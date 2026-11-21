import Fixpoint.DZeroCFA.Defs

import Fixpoint.Cache.Cache
import Fixpoint.Cache.Defs


-- Equation building

-- Used as part of the memoization key, to indentify which function is being called
inductive FnMarker where
  | evaluateMarker
  | exprResolveMarker
  | callResolveMarker
  deriving BEq, Hashable, Repr


-- Instantiate the parameters.
abbrev AbstractCursor := Std.HashSet Cursor

-- Interpreter monad
-- At the moment, it's just fixpoint (aka Cache), which subsumes the Nondeterminism monad, since it has Nondet effects already.
abbrev M := Cache.CacheM (FnMarker × Cursor) AbstractCursor

abbrev Selv := (FnMarker × Cursor) → M Cursor


-- Helpers

def assertApp (cursor : Cursor) : M Cursor := do
  match cursor.1 with
  | .appE _ _ => pure cursor
  | _ => Cache.fail


-- Meta-functions

def binder (x : Var) (cursor : Cursor) : Option Cursor :=
  let ⟨e, ctx⟩ := cursor
  match ctx with
  | .topC => none  -- Error: malformed program: failed to find a binder
  | .lamC y ctx =>
    if x = y then some ⟨.lamE y e, ctx⟩ else
    binder x ⟨.lamE y e, ctx⟩
  | .appC_operator ctx e1 => binder x ⟨.appE e e1, ctx⟩
  | .appC_operand e0 ctx => binder x ⟨.appE e0 e, ctx⟩
termination_by cursor.2


def find (x : Var) (cursor : Cursor) : M Cursor :=
  let ⟨e, ctx⟩ := cursor
  match e with
--
-- To find a variable within a reference:
  | .refE y =>
    -- Make sure it's the same variable. If so, return that reference.
    if x != y then Cache.fail else pure cursor
--
-- To find a variable within a lambda:
  | .lamE y bodyExpr =>
    -- If the lambda shadows the variable, then nothing.
    if y = x then Cache.fail else
    -- Otherwise, find within the lambda’s body.
    let bodyCursor: Cursor := ⟨bodyExpr, .lamC y ctx⟩  -- Step in
    find x bodyCursor
--
-- To find a variable within an application:
  | .appE e0 e1 =>
    -- Find within its operator.
    let operatorCursor : Cursor := ⟨e1, .appC_operand e0 ctx⟩  -- Step in
    let operatorRefs := find x operatorCursor
    -- Find within its operand.
    let operandCursor : Cursor := ⟨e0, .appC_operator ctx e1⟩  -- Step in
    let operandRefs := find x operandCursor
    -- Union the results.
    Cache.each [operatorRefs, operandRefs]
termination_by cursor.1
decreasing_by
  · simp
  · simp; omega
  · simp; omega


-- Relations

mutual  -- TODO! Add fixpoint or cache; otherwise recursion will diverge

  partial def evaluate (self : Selv) (cursor : Cursor) : M Cursor := do
    -- Overload all three open-recursive functions, for convencience and clarity.
    -- This means the signatures are the same as if they were normal recursive functions, so I can write like it's normal recursion, even though under the hood it uses `self` for open recursion.
    let evaluate c := self ⟨.evaluateMarker, c⟩
    let exprResolve c := self ⟨.exprResolveMarker, c⟩
    let _callResolve c := self ⟨.callResolveMarker, c⟩

    let ⟨e, ctx⟩ := cursor
    match e with
  --
  -- To evaluate a lambda: Return that lambda.
    | .lamE _ _ => pure cursor
  --
  -- To evaluate an application:
    | .appE e0 e1 =>
      -- Evaluate its operator to get some lambda.
      let operatorCursor : Cursor := ⟨e0, .appC_operator ctx e1⟩ -- Step into the operator
      let ⟨lam_expr, lam_ctx⟩ ← evaluate operatorCursor
      match lam_expr with  -- Asserting this is a lamE variant. Failure should be unreachable.
      | .lamE x ebody =>
        -- Evaluate the lambda’s body. Return the result.
        let bodyCursor : Cursor := ⟨ebody, .lamC x lam_ctx⟩  -- Step into the lambda body
        evaluate bodyCursor
      | _ => Cache.fail
  --
  -- To evaluate a reference:
    | .refE x =>
      -- Find its binding lambda.
      match binder x cursor with
      | none => Cache.fail
      | some binderCursor =>
      -- Expr-resolve the lambda to get an application.
      let ⟨app_expr, app_ctx⟩ ← exprResolve binderCursor
      match app_expr with  -- Asserting this is an appE variant. Failure should be unreachable.
      | .appE e0 e1 =>
        -- Evaluate the application’s operand, and return the result.
        let operandCursor : Cursor := ⟨e1, .appC_operand e0 app_ctx⟩
        evaluate operandCursor
      | _ => Cache.fail


  partial def exprResolve (self : Selv) (cursor : Cursor) : M Cursor := do
    -- Overload all three open-recursive functions, for convencience and clarity.
    -- This means the signatures are the same as if they were normal recursive functions, so I can write like it's normal recursion, even though under the hood it uses `self` for open recursion.
    let evaluate c := self ⟨.evaluateMarker, c⟩
    let exprResolve c := self ⟨.exprResolveMarker, c⟩
    let callResolve c := self ⟨.callResolveMarker, c⟩

    let ⟨e, ctx⟩ := cursor
    match ctx with
    | .topC => Cache.fail
  --
  -- To expr-resolve the body of a lambda:
    | .lamC _ _ =>
      -- Call-resolve that body to get an application B.
      let b ← callResolve cursor
      let b ← assertApp b  -- Failure should be unreachable.
      -- Expr-resolve that application to get another application A.
      let a ← exprResolve b
      let a ← assertApp a  -- Failure should be unreachable.
      -- Return A.
      pure a
  --
  -- To expr-resolve an operand:
    | .appC_operand e0 appCtx =>
      -- Evaluate the operator to get some lambda.
      let operatorCursor : Cursor := ⟨e0, .appC_operator appCtx e⟩
      let ⟨lam_expr, lam_ctx⟩ ← evaluate operatorCursor
      match lam_expr with  -- Asserting this is a lamE variant. Failure should be unreachable.
      | .lamE x ebody =>
        -- Find-resolve the lambda’s parameter with its body to get a reference to that parameter.
        let bodyCursor : Cursor := ⟨ebody, .lamC x lam_ctx⟩  -- Step into the lambda body
        let refCursor ← find x bodyCursor
        -- Expr-resolve that reference, and return the result.
        exprResolve refCursor
      | _ => Cache.fail
  --
  -- To expr-resolve an operator:
    | .appC_operator appCtx e1 =>
      -- Return its application.
      let appCursor : Cursor := ⟨.appE e e1, appCtx⟩  -- Step out
      pure appCursor

  partial def callResolve (self : Selv) (cursor : Cursor) : M Cursor := do
    -- Overload all three open-recursive functions, for convencience and clarity.
    -- This means the signatures are the same as if they were normal recursive functions, so I can write like it's normal recursion, even though under the hood it uses `self` for open recursion.
    let _evaluate c := self ⟨.evaluateMarker, c⟩
    let exprResolve c := self ⟨.exprResolveMarker, c⟩
    let _callResolve c := self ⟨.callResolveMarker, c⟩

    let ⟨e, ctx⟩ := cursor
    match ctx with
  --
  -- To call-resolve the body of a lambda:
    | .lamC x bodyCtx =>
      -- Expr-resolve the (entire) lambda to get an application, and return the result.
      let lamCursor : Cursor := ⟨.lamE x e, bodyCtx⟩  -- Step out
      let c ← exprResolve lamCursor
      assertApp c  -- Failure should be unreachable.
  --
    | _ => Cache.fail

end


def equation (self : Selv) : Selv
  | ⟨.evaluateMarker, c⟩ => evaluate self c
  | ⟨.exprResolveMarker, c⟩ => exprResolve self c
  | ⟨.callResolveMarker, c⟩ => callResolve self c

  -- (let f (lam x x) (let a (app f 1) (let b (app f 2) a)))
def prgm : SugExpr :=
  .letE "f" (.lamE "x" $ .refE "x") $
  .letE "a" (.appE (.refE "f") (.idE "1")) $
  .letE "b" (.appE (.refE "f") (.idE "2")) $
  .refE "a"  -- This ref to "a" is the expression to be queried.
def prgmCtx : RContext := .lamC "b" $ .appC_operator (.lamC "a" $ .appC_operator (.lamC "f" (.appC_operator (.topC) $ Expr.lamE "x" $ Expr.refE "x")) $ Expr.appE (Expr.refE "f") $ Expr.lamE "1" $ Expr.refE "1") $ Expr.appE (Expr.refE "f") $ Expr.lamE "2" $ Expr.refE "2"
def queryCursor : Cursor := ⟨.refE "a", prgmCtx⟩

def demo : IO Unit := do
  --   demo "multiple values"
  -- (let f (lam x x) (let a (app f 1) (let b (app f 2) a)))
  let query : FnMarker × Cursor := ⟨.evaluateMarker, queryCursor⟩

  -- FIXME! Cache.fix expects an AbstractCursor, but the interpreter is written over concrete Cursor.
  -- let tbl ← Cache.run (Cache.fix equation query)

  -- let f0_key : Fn × Input := ⟨Fn.f, (0 : Nat)⟩
  -- let f0_cell := tbl[f0_key]?
  -- let g0_key : Fn × Input := ⟨Fn.g, (0 : Nat)⟩
  -- let g0_cell := tbl[g0_key]?
  -- IO.println (showCell "f(0)" f0_cell)
  -- IO.println (showCell "g(0)" g0_cell)
  -- let hasBoth (entry : Option (Entry (HashSet Output))) : Bool :=
  --   match entry with
  --   | some (some vs, _) => vs.contains "fResult" && vs.contains "gResult"
  --   | _ => false
  -- if hasBoth f0_cell && hasBoth g0_cell then
  --   pure ()
  -- else
  --   throw <| IO.userError "expected both cells to contain f(0) and g(0)"

#eval demo
