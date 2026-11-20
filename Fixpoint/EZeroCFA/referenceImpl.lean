import Std.Data.HashMap
import Std.Data.HashSet
open Std

namespace ADI

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

/-- Memo-table keys: the `(cons tag args)` keys of the Racket version. -/
inductive Key where
  | sigma (x : String)
  | ceval (e : Exp)
  | eval  (e : Exp)
  deriving BEq, Hashable, Repr, Inhabited

/-! ============================================================
    Monad (curried, multi-value)
    ============================================================

  The Racket version is a continuation monad composed with a state monad,
  where the state (the memo table) stores continuations, i.e. functions
  `List Val → State → State`.  In Lean such a type is not strictly positive,
  so the memo table is instead a mutable reference (`IO.Ref`) and the
  continuations live in `IO`.  The order in which continuations are run is the
  same as in the state-passing version.

    M = Tbl → (List Val → IO Unit) → IO Unit
-/

/-- A continuation receives the list of values produced. -/
abbrev K := List Val → IO Unit

/-- A memo entry: the set of values seen so far, and the waiting continuations
    (most recently registered first). -/
abbrev Entry := HashSet (List Val) × List K

abbrev Tbl := IO.Ref (HashMap Key Entry)

abbrev M := Tbl → K → IO Unit

/-- return: inject values into the monad -/
def ret (vs : List Val) : M := fun _ κ => κ vs

/-- >>=: sequence computations; the value list is passed to `f` -/
def bindM (c : M) (f : List Val → M) : M :=
  fun t κ => c t (fun vs => f vs t κ)

/-- Convenience: `f` expects exactly one value (Racket `(λ (v) ...)`). -/
def bind1 (c : M) (f : Val → M) : M :=
  bindM c fun
    | [v] => f v
    | _   => fun _ _ => pure ()

/-- Convenience: `f` expects no values (Racket `(λ () ...)`). -/
def bind0 (c : M) (f : M) : M :=
  bindM c fun
    | [] => f
    | _  => fun _ _ => pure ()

/-- each: nondeterministic choice — run all computations in order. -/
def each (cs : List M) : M :=
  fun t κ => cs.forM fun c => c t κ

/-- fail: no results (each with zero computations) -/
def fail : M := each []

/-- deliver: propagate a new value to all waiting continuations.
    If the value was already seen, do nothing (fixed point for this value). -/
def deliver (t : Tbl) (key : Key) : K := fun vs => do
  let s ← t.get
  let (vals, conts) := s.getD key ({}, [])
  if vals.contains vs then
    pure ()
  else
    t.set (s.insert key (vals.insert vs, conts))
    for κ in conts do
      κ vs

/-- memo: memoize a computation with demand-driven fixed-point computation.
    - First call: register continuation, compute, deliver results
    - Later calls: register continuation, deliver cached results
    The body is a thunk so it is only built when the key is first demanded. -/
def memo (key : Key) (body : Unit → M) : M := fun t κ => do
  let s ← t.get
  match s[key]? with
  | none =>
    t.set (s.insert key ({}, [κ]))
    body () t (deliver t key)
  | some (vals, conts) =>
    t.set (s.insert key (vals, κ :: conts))
    for vs in vals.toList do
      κ vs

/-- run: execute a computation, return the final memo table. -/
def run (c : M) : IO (HashMap Key Entry) := do
  let t ← IO.mkRef ({} : HashMap Key Entry)
  c t (fun _ => pure ())
  t.get

/-! ============================================================
    Interpreter (tiered ANF with 0CFA)
    ============================================================

  A monovariant control-flow analysis where all bindings to the same
  variable share one abstract address. -/

/-- Abstract store: calling `sigma x` registers demand for x's value;
    `bindBang` delivers values to that demand. -/
def sigma (x : String) : M := memo (.sigma x) fun _ => fail

/-- bind!: deliver a value to a variable's address in the store.
    Passes the empty value list on (just a side effect). -/
def bindBang (x : String) (v : Val) : M := fun t κ => do
  deliver t (.sigma x) [v]
  κ []

/-- aeval: evaluate atomic expressions. -/
def aeval : Exp → M
  | .var x    => sigma x
  | .lam x b  => ret [.clo x b]
  | .bool b   => ret [.bool b]
  | .num n    => ret [.num n]
  | _         => fail   -- not atomic

mutual

/-- ceval: evaluate complex expressions (memoized). -/
partial def ceval (c : Exp) : M :=
  memo (.ceval c) fun _ =>
    match c with
    | .app f a =>
      bind1 (aeval f) fun fv =>
      bind1 (aeval a) fun av =>
      applyClo fv av
    | _ => aeval c

/-- eval: evaluate general expressions (memoized). -/
partial def eval (e : Exp) : M :=
  memo (.eval e) fun _ =>
    match e with
    | .let_ x r b =>
      bind1 (ceval r) fun v =>
      bind0 (bindBang x v) (eval b)
    | .if_ c t f =>
      bind1 (aeval c) fun cv =>
        match cv with
        | .bool false => eval f
        | _           => eval t
    | _ => ceval e

/-- apply-clo: bind the argument to the parameter, evaluate the body.
    Non-closures fail. -/
partial def applyClo (fv av : Val) : M :=
  match fv with
  | .clo x b => bind0 (bindBang x av) (eval b)
  | _        => fail

end

/-! ============================================================
    Pretty printing
    ============================================================ -/

def Exp.show : Exp → String
  | .var x       => x
  | .bool true   => "#t"
  | .bool false  => "#f"
  | .num n       => toString n
  | .lam x b     => s!"(λ ({x}) {b.show})"
  | .app f a     => s!"(app {f.show} {a.show})"
  | .let_ x r b  => s!"(let ([{x} {r.show}]) {b.show})"
  | .if_ c t e   => s!"(if {c.show} {t.show} {e.show})"

def Val.show : Val → String
  | .clo x b      => s!"(clo {(Exp.lam x b).show})"
  | .bool true    => "#t"
  | .bool false   => "#f"
  | .num n        => toString n

/-- show-store: the σ entries of the memo table, as `x ↦ {values}`. -/
def showStore (tbl : HashMap Key Entry) : String :=
  let items : List String := tbl.toList.filterMap fun (k, vals, _) =>
    match k with
    | .sigma x =>
      let vs := vals.toList.map fun l => "(" ++ " ".intercalate (l.map Val.show) ++ ")"
      some s!"{x} ↦ {"{" ++ ", ".intercalate vs ++ "}"}"
    | _ => none
  "  " ++ "\n  ".intercalate ((items.toArray.qsort (· < ·)).toList)

/-! ============================================================
    Examples
    ============================================================ -/

private def V (x : String) := Exp.var x
private def N (n : Nat) := Exp.num n
private def B (b : Bool) := Exp.bool b
private def L (x : String) (b : Exp) := Exp.lam x b
private def A (f a : Exp) := Exp.app f a
private def Let (x : String) (r b : Exp) := Exp.let_ x r b
private def If (c t e : Exp) := Exp.if_ c t e

def demo (title : String) (e : Exp) : IO Unit := do
  IO.println s!"--- {title} ---"
  IO.println (showStore (← run (eval e)))
  IO.println ""

def examples : IO Unit := do
  demo "let binding"
    (Let "x" (N 1) (V "x"))

  demo "identity function"
    (Let "f" (L "y" (V "y"))
      (A (V "f") (N 42)))

  demo "multiple values"
    (Let "f" (L "x" (V "x"))
      (Let "a" (A (V "f") (N 1))
        (Let "b" (A (V "f") (N 2))
          (V "a"))))

  demo "conditional (true)"
    (If (B true)
      (Let "x" (N 1) (V "x"))
      (Let "x" (N 2) (V "x")))

  demo "conditional (unknown)"
    (Let "b" (L "x" (V "x"))
      (Let "c" (A (V "b") (B true))
        (Let "d" (A (V "b") (B false))
          (If (V "c")
            (Let "r" (N 1) (V "r"))
            (Let "r" (N 2) (V "r"))))))

  demo "higher-order"
    (Let "apply" (L "f" (A (V "f") (N 99)))
      (Let "g" (L "z" (V "z"))
        (A (V "apply") (V "g"))))

  demo "self-application"
    (Let "ω" (L "x" (A (V "x") (V "x")))
      (A (V "ω") (V "ω")))

end ADI

def main : IO Unit := ADI.examples
