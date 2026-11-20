import Fixpoint.DZeroCFA.Defs


-- Helpers

def assertApp (cursor : Cursor) : ND Cursor := do
  match cursor.1 with
  | .appE _ _ => pure cursor
  | _ => ND.fail


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


def find (x : Var) (cursor : Cursor) : List Cursor :=
  let ⟨e, ctx⟩ := cursor
  match e with
--
-- To find a variable within a reference:
  | .refE y =>
    -- Make sure it's the same variable. If so, return that reference.
    if x != y then [] else [cursor]
--
-- To find a variable within a lambda:
  | .lamE y bodyExpr =>
    -- If the lambda shadows the variable, then nothing.
    if y = x then [] else
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
    operatorRefs ++ operandRefs
termination_by cursor.1
decreasing_by
  · simp
  · simp; omega
  · simp; omega


-- Relations

mutual  -- TODO! Add fixpoint or cache; otherwise recursion will diverge

  partial def evaluate (cursor : Cursor) : ND Cursor := do
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
      | _ => ND.fail
  --
  -- To evaluate a reference:
    | .refE x =>
      -- Find its binding lambda.
      match binder x cursor with
      | none => ND.fail
      | some binderCursor =>
      -- Expr-resolve the lambda to get an application.
      let ⟨app_expr, app_ctx⟩ ← exprResolve binderCursor
      match app_expr with  -- Asserting this is an appE variant. Failure should be unreachable.
      | .appE e0 e1 =>
        -- Evaluate the application’s operand, and return the result.
        let operandCursor : Cursor := ⟨e1, .appC_operand e0 app_ctx⟩
        evaluate operandCursor
      | _ => ND.fail


  partial def exprResolve (cursor : Cursor) : ND Cursor := do
    let ⟨e, ctx⟩ := cursor
    match ctx with
    | .topC => ND.fail
  --
  -- To expr-resolve the body of a lambda:
     -- TODO! FIXME -- Claude identified an issue
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
      | _ => ND.fail
  --
  -- To expr-resolve an operator:
    | .appC_operator appCtx e1 =>
      -- Return its application.
      let appCursor : Cursor := ⟨.appE e e1, appCtx⟩  -- Step out
      pure appCursor


  partial def callResolve (cursor : Cursor) : ND Cursor := do
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
    | _ => ND.fail

end
