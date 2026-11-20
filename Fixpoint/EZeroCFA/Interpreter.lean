import Fixpoint.Cache.Cache
import Std.Data.HashMap
import Std.Data.HashSet
open Std

namespace ADI.Interp

/-! 0CFA interpreter over `ADI.Cache`.

    Answers are sets of abstract values, ordered by inclusion. The cache joins
    each published set into the cell and re-runs subscribers when the cell
    grows. Recursive calls go through `self`. `bindBang` publishes a set to a
    `.sigma` key, whose producer itself returns nothing. -/

open ADI.Cache

/-! ============================================================
    Syntax and abstract values
    ============================================================

  ANF Syntax (tiered):
    aexp ::= x | lit | (λ (x) exp)
    cexp ::= (app aexp aexp) | aexp
    exp  ::= (let ([x cexp]) exp) | (if aexp exp exp) | cexp
-/

inductive Exp where
  | var  (x : String)
  | bool (b : Bool)
  | num  (n : Nat)
  | lam  (x : String) (body : Exp)
  | app  (f a : Exp)
  | let_ (x : String) (rhs body : Exp)
  | if_  (c t e : Exp)
  deriving BEq, Hashable, Repr, Inhabited

/-- Abstract values. In 0CFA a closure is just its lambda (no environment). -/
inductive Val where
  | clo  (x : String) (body : Exp)
  | bool (b : Bool)
  | num  (n : Nat)
  deriving BEq, Hashable, Repr, Inhabited

/-- Memo-table keys. -/
inductive Key where
  | sigma (x : String)
  | ceval (e : Exp)
  | eval  (e : Exp)
  deriving BEq, Hashable, Repr, Inhabited

abbrev M := CacheM Key (HashSet Val)

def single (v : Val) : HashSet Val :=
  ({} : HashSet Val).insert v

/-- Publish `vs` at the address `x`, then continue with unit. -/
def bindBang (x : String) (vs : HashSet Val) : M Unit := fun cache κ => do
  publish cache (.sigma x) vs
  κ ()

/-- Evaluate an atomic expression. Variable lookup subscribes to the store and
    receives the whole set accumulated there. -/
def aeval (self : Key → M (HashSet Val)) : Exp → M (HashSet Val)
  | .var x   => self (.sigma x)
  | .lam x b => pure (single (.clo x b))
  | .bool b  => pure (single (.bool b))
  | .num n   => pure (single (.num n))
  | _        => fail

/-- Bind the operand set and evaluate the body of every closure in `fvs`. -/
def applyClo (self : Key → M (HashSet Val)) (fvs avs : HashSet Val) : M (HashSet Val) :=
  let branches : List (M (HashSet Val)) := fvs.toList.filterMap fun
    | .clo x b => some (bindBang x avs >>= fun _ => self (.eval b))
    | _ => none
  each branches

/-- One analysis step. `self` is the memoized recursion.
    A subscriber is re-run with the whole set when a cell grows. -/
def equation (self : Key → M (HashSet Val)) : Key → M (HashSet Val)
  | .sigma _ => fail
  | .ceval c =>
    match c with
    | .app f a =>
      aeval self f >>= fun fv =>
      aeval self a >>= fun av =>
      applyClo self fv av
    | _ => aeval self c
  | .eval e =>
    match e with
    | .let_ x r b =>
      self (.ceval r) >>= fun v =>
      bindBang x v >>= fun _ =>
      self (.eval b)
    | .if_ c t f =>
      aeval self c >>= fun cv =>
        let goElse := cv.toList.any (· == .bool false)
        let goThen := cv.toList.any (· != .bool false)
        let branches : List (M (HashSet Val)) :=
          (if goThen then [self (.eval t)] else []) ++
          (if goElse then [self (.eval f)] else [])
        each branches
    | _ => self (.ceval e)

/-- Evaluate `e`. Recursive demands go through the cache. -/
def eval (e : Exp) : M (HashSet Val) := fix equation (.eval e)

/-! ============================================================
    Pretty printing
    ============================================================ -/

def Exp.show : Exp → String
  | .var x      => x
  | .bool true  => "#t"
  | .bool false => "#f"
  | .num n      => toString n
  | .lam x b    => s!"(λ ({x}) {b.show})"
  | .app f a    => s!"(app {f.show} {a.show})"
  | .let_ x r b => s!"(let ([{x} {r.show}]) {b.show})"
  | .if_ c t e  => s!"(if {c.show} {t.show} {e.show})"

def Val.show : Val → String
  | .clo x b   => s!"(clo {(Exp.lam x b).show})"
  | .bool true => "#t"
  | .bool false => "#f"
  | .num n     => toString n

/-- The σ entries of the memo table, as `x ↦ {values}`. -/
def showStore (tbl : HashMap Key (Entry (HashSet Val))) : String :=
  let items : List String := tbl.toList.filterMap fun (k, vals, _) =>
    match k, vals with
    | .sigma x, some vs =>
      let shown := (vs.toList.map Val.show).toArray.qsort (· < ·) |>.toList
      some s!"{x} ↦ {"{" ++ ", ".intercalate shown ++ "}"}"
    | _, _ => none
  "  " ++ "\n  ".intercalate ((items.toArray.qsort (· < ·)).toList)


end ADI.Interp
