import Fixpoint.EZeroCFA_claude.Ops

/-!
# Terms

* `Raw`  : named surface terms (what the macro / string parser produce).
* `Tm n` : **intrinsically scoped** terms with de Bruijn indices; `n` is the
           number of variables in scope and variables are `Fin n`.  An unbound
           variable is therefore unrepresentable.
* `Raw.scope` : the (only) place scoping errors can occur.

Labels (for lambdas, call sites and `let` binders) are assigned in post-order,
as before, so `λi#2`-style names in the output are unchanged.
-/

namespace AbsInt

inductive Raw where
  | num (k : Int)
  | var (x : String)
  | input
  | lam (x : String) (body : Raw)
  | app (f a : Raw)
  | arith (op : ArithOp) (l r : Raw)
  | branch (op : CmpOp) (l r t e : Raw)
  | letE (x : String) (rhs body : Raw)
  | letrec (x : String) (rhs body : Raw)
  deriving Repr, Inhabited

/-- Scoped term.  Binders (`lam`, `letE`, `letrec`) extend the scope by one;
index 0 is the innermost binder. -/
inductive Tm : Nat → Type where
  | num {n : Nat} (k : Int) : Tm n
  | var {n : Nat} (i : Fin n) : Tm n
  | input {n : Nat} : Tm n
  | lam {n : Nat} (label : Nat) (param : String) (body : Tm (n + 1)) : Tm n
  | app {n : Nat} (site : Nat) (fn arg : Tm n) : Tm n
  | arith {n : Nat} (op : ArithOp) (lhs rhs : Tm n) : Tm n
  | branch {n : Nat} (op : CmpOp) (lhs rhs thenT elseT : Tm n) : Tm n
  | letE {n : Nat} (label : Nat) (name : String) (rhs : Tm n) (body : Tm (n + 1)) : Tm n
  /-- `rhs` is in the scope of the bound name (recursion). -/
  | letrec {n : Nat} (label : Nat) (name : String) (rhs : Tm (n + 1)) (body : Tm (n + 1)) : Tm n

/-- Index of the innermost binding of `x` in `ctx`. -/
def lookupIdx : (ctx : List String) → String → Option (Fin ctx.length)
  | [], _ => none
  | y :: ys, x =>
    if x = y then some ⟨0, Nat.succ_pos _⟩
    else (lookupIdx ys x).map Fin.succ

/-- Scope-check and label.  The `Nat` is the label counter. -/
def Raw.scope : (ctx : List String) → Raw → Nat → Except String (Tm ctx.length × Nat)
  | _, .num k, c => .ok (.num k, c)
  | _, .input, c => .ok (.input, c)
  | ctx, .var x, c =>
    (match lookupIdx ctx x with
     | some i => .ok (.var i, c)
     | none => .error s!"unbound variable {x}")
  | ctx, .lam x body, c => do
    let (b, c₁) ← Raw.scope (x :: ctx) body c
    pure (.lam (c₁ + 1) x b, c₁ + 1)
  | ctx, .app f a, c => do
    let (f', c₁) ← Raw.scope ctx f c
    let (a', c₂) ← Raw.scope ctx a c₁
    pure (.app (c₂ + 1) f' a', c₂ + 1)
  | ctx, .arith op l r, c => do
    let (l', c₁) ← Raw.scope ctx l c
    let (r', c₂) ← Raw.scope ctx r c₁
    pure (.arith op l' r', c₂)
  | ctx, .branch op l r t e, c => do
    let (l', c₁) ← Raw.scope ctx l c
    let (r', c₂) ← Raw.scope ctx r c₁
    let (t', c₃) ← Raw.scope ctx t c₂
    let (e', c₄) ← Raw.scope ctx e c₃
    pure (.branch op l' r' t' e', c₄)
  | ctx, .letE x rhs body, c => do
    let (r', c₁) ← Raw.scope ctx rhs c
    let (b', c₂) ← Raw.scope (x :: ctx) body c₁
    pure (.letE (c₂ + 1) x r' b', c₂ + 1)
  | ctx, .letrec x rhs body, c => do
    let (r', c₁) ← Raw.scope (x :: ctx) rhs c
    let (b', c₂) ← Raw.scope (x :: ctx) body c₁
    pure (.letrec (c₂ + 1) x r' b', c₂ + 1)

/-- Closed term from a raw one. -/
def Raw.close (r : Raw) : Except String (Tm 0) :=
  (Raw.scope [] r 0).map (fun p => p.1)

end AbsInt
