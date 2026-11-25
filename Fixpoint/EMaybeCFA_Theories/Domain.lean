import Fixpoint.EZeroCFA_claude.Ops

/-!
# Abstract domains (operations + concretization)

A `Domain α` bundles the executable operations *and* the concretization
`γ : α → Int → Prop` (a predicate, so no `Set`/Mathlib needed).  The soundness
laws live in the separate `Domain.Lawful` predicate (`Laws.lean`), so the
executable part never depends on proofs.

Interval bounds are explicit `Bound`s (no floats).  Parity is a four-point
lattice.  `Domain.product` takes a proof-carrying `Reducer`, so a reduced
product is exact by construction.
-/

namespace AbsInt

structure Domain (α : Type) where
  bot : α
  top : α
  ofInt : Int → α
  isBot : α → Bool
  le : α → α → Bool
  join : α → α → α
  meet : α → α → α
  /-- `widen old new`, where `new ⊒ old`. -/
  widen : α → α → α
  /-- `narrow old new`, where `old` is a post-fixpoint and `new` a recomputation. -/
  narrow : α → α → α
  binop : ArithOp → α → α → α
  /-- Refine `(a, b)` under the assumption that `a op b` holds. -/
  filterCmp : CmpOp → α → α → α × α
  toStr : α → String
  /-- Concretization. -/
  γ : α → Int → Prop

/-! ## Extended integers -/

inductive Bound where
  | negInf
  | fin (n : Int)
  | posInf
  deriving DecidableEq, Repr

namespace Bound

def le : Bound → Bound → Bool
  | .negInf, _ => true
  | _, .posInf => true
  | .fin a, .fin b => decide (a ≤ b)
  | _, _ => false

def bmin (a b : Bound) : Bound := if le a b then a else b
def bmax (a b : Bound) : Bound := if le a b then b else a

/-- Saturating add; `-∞ + +∞` never arises (we only add lo+lo or hi+hi). -/
def add : Bound → Bound → Bound
  | .negInf, _ => .negInf
  | _, .negInf => .negInf
  | .posInf, _ => .posInf
  | _, .posInf => .posInf
  | .fin a, .fin b => .fin (a + b)

def addInt (b : Bound) (k : Int) : Bound :=
  match b with
  | .fin n => .fin (n + k)
  | other => other

def neg : Bound → Bound
  | .negInf => .posInf
  | .posInf => .negInf
  | .fin n => .fin (-n)

def sub (a b : Bound) : Bound := add a (neg b)

def sign : Bound → Int
  | .negInf => -1
  | .posInf => 1
  | .fin n => if n < 0 then -1 else if n = 0 then 0 else 1

/-- `0 * ∞ = 0`. -/
def mul : Bound → Bound → Bound
  | .fin a, .fin b => .fin (a * b)
  | a, b =>
    let s := sign a * sign b
    if s = 0 then .fin 0 else if s > 0 then .posInf else .negInf

def toStr : Bound → String
  | .negInf => "-inf"
  | .posInf => "+inf"
  | .fin n => s!"{n}"

end Bound

/-- A non-empty interval `[lo, hi]` (`lo ≤ hi` by convention; use `Itv.mk?`). -/
structure Itv where
  lo : Bound
  hi : Bound
  deriving DecidableEq, Repr

namespace Itv
def mk? (lo hi : Bound) : Option Itv :=
  if Bound.le lo hi then some ⟨lo, hi⟩ else none
def meet (a b : Itv) : Option Itv :=
  mk? (Bound.bmax a.lo b.lo) (Bound.bmin a.hi b.hi)
end Itv

/-! ## Intervals -/

namespace Interval

def meetO : Option Itv → Option Itv → Option Itv
  | some a, some b => Itv.meet a b
  | _, _ => none

def le : Option Itv → Option Itv → Bool
  | none, _ => true
  | some _, none => false
  | some a, some b => Bound.le b.lo a.lo && Bound.le a.hi b.hi

def join : Option Itv → Option Itv → Option Itv
  | none, b => b
  | a, none => a
  | some a, some b => some ⟨Bound.bmin a.lo b.lo, Bound.bmax a.hi b.hi⟩

/-- Widening with thresholds: a grown bound jumps to the nearest enclosing
threshold, else to infinity. -/
def widen (ts : List Int) : Option Itv → Option Itv → Option Itv
  | none, n => n
  | o, none => o
  | some o, some n =>
    let lo : Bound :=
      if Bound.le o.lo n.lo then o.lo
      else ts.foldl (fun acc t =>
             if Bound.le (Bound.fin t) n.lo then Bound.bmax acc (Bound.fin t) else acc) Bound.negInf
    let hi : Bound :=
      if Bound.le n.hi o.hi then o.hi
      else ts.foldl (fun acc t =>
             if Bound.le n.hi (Bound.fin t) then Bound.bmin acc (Bound.fin t) else acc) Bound.posInf
    some ⟨lo, hi⟩

/-- Narrowing only refines infinite bounds. -/
def narrow : Option Itv → Option Itv → Option Itv
  | some o, some n =>
    Itv.mk? (if o.lo = Bound.negInf then n.lo else o.lo)
            (if o.hi = Bound.posInf then n.hi else o.hi)
  | _, _ => none

def binop : ArithOp → Option Itv → Option Itv → Option Itv
  | .add, some a, some b => some ⟨Bound.add a.lo b.lo, Bound.add a.hi b.hi⟩
  | .sub, some a, some b => some ⟨Bound.sub a.lo b.hi, Bound.sub a.hi b.lo⟩
  | .mul, some a, some b =>
    let p1 := Bound.mul a.lo b.lo
    let p2 := Bound.mul a.lo b.hi
    let p3 := Bound.mul a.hi b.lo
    let p4 := Bound.mul a.hi b.hi
    some ⟨Bound.bmin (Bound.bmin p1 p2) (Bound.bmin p3 p4),
          Bound.bmax (Bound.bmax p1 p2) (Bound.bmax p3 p4)⟩
  | _, _, _ => none

/-- Assume `a < b`. -/
def filterLt (a b : Itv) : Option Itv × Option Itv :=
  (Itv.meet a ⟨Bound.negInf, Bound.addInt b.hi (-1)⟩,
   Itv.meet b ⟨Bound.addInt a.lo 1, Bound.posInf⟩)

/-- Assume `a ≤ b`. -/
def filterLe (a b : Itv) : Option Itv × Option Itv :=
  (Itv.meet a ⟨Bound.negInf, b.hi⟩,
   Itv.meet b ⟨a.lo, Bound.posInf⟩)

def filterCmp (op : CmpOp) : Option Itv → Option Itv → Option Itv × Option Itv
  | some a, some b =>
    (match op with
     | .lt => filterLt a b
     | .le => filterLe a b
     | .gt => let (b', a') := filterLt b a; (a', b')
     | .ge => let (b', a') := filterLe b a; (a', b')
     | .eq => let m := Itv.meet a b; (m, m)
     | .ne =>
       if a.lo = a.hi ∧ a.hi = b.lo ∧ b.lo = b.hi then (none, none)
       else (some a, some b))
  | _, _ => (none, none)

def showItv : Option Itv → String
  | none => "⊥"
  | some a => s!"[{a.lo.toStr},{a.hi.toStr}]"

def gamma : Option Itv → Int → Prop
  | none, _ => False
  | some a, x => Bound.le a.lo (Bound.fin x) = true ∧ Bound.le (Bound.fin x) a.hi = true

def domain (thresholds : List Int := []) : Domain (Option Itv) where
  bot := none
  top := some ⟨Bound.negInf, Bound.posInf⟩
  ofInt := fun n => some ⟨Bound.fin n, Bound.fin n⟩
  isBot := fun a => a.isNone
  le := Interval.le
  join := Interval.join
  meet := Interval.meetO
  widen := Interval.widen thresholds
  narrow := Interval.narrow
  binop := Interval.binop
  filterCmp := Interval.filterCmp
  toStr := Interval.showItv
  γ := Interval.gamma

end Interval

/-! ## Parity -/

/-- `bot < even, odd < top`. -/
inductive Par where
  | bot | even | odd | top
  deriving DecidableEq, Repr

namespace Parity

def le (a b : Par) : Bool := a == b || a == Par.bot || b == Par.top

def join (a b : Par) : Par :=
  if a = Par.bot then b else if b = Par.bot then a
  else if a = b then a else Par.top

def meet (a b : Par) : Par :=
  if a = Par.top then b else if b = Par.top then a
  else if a = b then a else Par.bot

def binop (op : ArithOp) (a b : Par) : Par :=
  if a = Par.bot ∨ b = Par.bot then Par.bot
  else match op with
    | .mul =>
      if a = Par.even ∨ b = Par.even then Par.even
      else if a = Par.odd ∧ b = Par.odd then Par.odd
      else Par.top
    | _ =>
      if a = Par.top ∨ b = Par.top then Par.top
      else if a = b then Par.even
      else Par.odd

def filterCmp (op : CmpOp) (a b : Par) : Par × Par :=
  if a = Par.bot ∨ b = Par.bot then (Par.bot, Par.bot)
  else match op with
    | .eq => let m := meet a b; (m, m)
    | _ => (a, b)

def toStr : Par → String
  | .bot => "bot" | .even => "even" | .odd => "odd" | .top => "top"

def gamma : Par → Int → Prop
  | .bot, _ => False
  | .even, x => x % 2 = 0
  | .odd, x => x % 2 = 1
  | .top, _ => True

def domain : Domain Par where
  bot := Par.bot
  top := Par.top
  ofInt := fun n => if n % 2 = 0 then Par.even else Par.odd
  isBot := fun a => a == Par.bot
  le := Parity.le
  join := Parity.join
  meet := Parity.meet
  widen := Parity.join
  narrow := fun old new => if old = Par.bot then Par.bot else new
  binop := Parity.binop
  filterCmp := Parity.filterCmp
  toStr := Parity.toStr
  γ := Parity.gamma

end Parity

/-! ## Reduced product -/

/-- A reduction ρ between two domains, **carrying the proof** that it does not
change the concretization.  (The product below is therefore exact by
construction.) -/
structure Reducer {α β : Type} (D1 : Domain α) (D2 : Domain β) where
  ρ : α × β → α × β
  exact : ∀ (p : α × β) (x : Int),
    (D1.γ (ρ p).1 x ∧ D2.γ (ρ p).2 x) ↔ (D1.γ p.1 x ∧ D2.γ p.2 x)

def Reducer.identity {α β : Type} (D1 : Domain α) (D2 : Domain β) : Reducer D1 D2 :=
  ⟨fun p => p, fun _ _ => Iff.rfl⟩

/-- ρ is applied after join / meet / transfer / guards, but NOT after
widen / narrow (reducing a widened value could undo the jump and break
termination). -/
def Domain.product {α β : Type} (D1 : Domain α) (D2 : Domain β)
    (r : Reducer D1 D2 := Reducer.identity D1 D2) : Domain (α × β) :=
  let isBot : α × β → Bool := fun a => D1.isBot a.1 || D2.isBot a.2
  { bot := (D1.bot, D2.bot)
    top := (D1.top, D2.top)
    ofInt := fun n => r.ρ (D1.ofInt n, D2.ofInt n)
    isBot := isBot
    le := fun a b => isBot a || (D1.le a.1 b.1 && D2.le a.2 b.2)
    join := fun a b =>
      if isBot a then b else if isBot b then a
      else r.ρ (D1.join a.1 b.1, D2.join a.2 b.2)
    meet := fun a b => r.ρ (D1.meet a.1 b.1, D2.meet a.2 b.2)
    widen := fun a b => (D1.widen a.1 b.1, D2.widen a.2 b.2)
    narrow := fun a b => (D1.narrow a.1 b.1, D2.narrow a.2 b.2)
    binop := fun op a b => r.ρ (D1.binop op a.1 b.1, D2.binop op a.2 b.2)
    filterCmp := fun op a b =>
      let (a1, b1) := D1.filterCmp op a.1 b.1
      let (a2, b2) := D2.filterCmp op a.2 b.2
      (r.ρ (a1, a2), r.ρ (b1, b2))
    toStr := fun a => s!"({D1.toStr a.1}, {D2.toStr a.2})"
    γ := fun a x => D1.γ a.1 x ∧ D2.γ a.2 x }

/-! ### The interval × parity reduction -/

/-- Round a lower bound up to the next integer of parity `w` (0 even, 1 odd). -/
def tightenLo (w : Int) : Bound → Bound
  | .fin n => if n % 2 ≠ w then .fin (n + 1) else .fin n
  | b => b

/-- Round an upper bound down to the previous integer of parity `w`. -/
def tightenHi (w : Int) : Bound → Bound
  | .fin n => if n % 2 ≠ w then .fin (n - 1) else .fin n
  | b => b

/-- Tighten bounds to the right parity, detect emptiness, and learn parity
from singleton intervals. -/
def intervalParity : Option Itv × Par → Option Itv × Par
  | (none, _) => (none, Par.bot)
  | (some iv, par) =>
    if par = Par.bot then (none, Par.bot)
    else
      let bounds : Bound × Bound :=
        (match par with
         | .even => (tightenLo 0 iv.lo, tightenHi 0 iv.hi)
         | .odd => (tightenLo 1 iv.lo, tightenHi 1 iv.hi)
         | _ => (iv.lo, iv.hi))
      let lo := bounds.1
      let hi := bounds.2
      if !Bound.le lo hi then (none, Par.bot)
      else
        match lo, hi with
        | .fin a, .fin b =>
          if a = b then (some ⟨lo, hi⟩, if a % 2 = 0 then Par.even else Par.odd)
          else (some ⟨lo, hi⟩, par)
        | _, _ => (some ⟨lo, hi⟩, par)

/-- The proof that `intervalParity` preserves γ is **deferred** (`sorry`): it is
a case analysis on `Bound` arithmetic.  Everything computational is unaffected. -/
def intervalParityReducer (ts : List Int) :
    Reducer (Interval.domain ts) Parity.domain :=
  ⟨intervalParity, by sorry⟩

end AbsInt
