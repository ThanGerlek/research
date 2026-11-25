import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int

import Fixpoint.EZeroCFA_claude.Domain

/-!
# Soundness laws for domains

Built separately from the executable, so a `sorry` here can never break it.

`Domain.Lawful D` says every operation of `D` is sound w.r.t. its
concretization `D.γ`.

Proof status (compiles):
* proved:  `Parity.lawful` and `Domain.product_lawful` in full;
* `sorry`: `Interval.lawful` only (arithmetic-heavy; see the comment there).
-/

namespace AbsInt

/-- All operations of `D` are sound w.r.t. `D.γ`. -/
structure Domain.Lawful {α : Type} (D : Domain α) : Prop where
  bot_empty : ∀ x, ¬ D.γ D.bot x
  top_full : ∀ x, D.γ D.top x
  ofInt_mem : ∀ n, D.γ (D.ofInt n) n
  isBot_empty : ∀ a, D.isBot a = true → ∀ x, ¬ D.γ a x
  le_sound : ∀ a b, D.le a b = true → ∀ x, D.γ a x → D.γ b x
  join_left : ∀ a b x, D.γ a x → D.γ (D.join a b) x
  join_right : ∀ a b x, D.γ b x → D.γ (D.join a b) x
  meet_sound : ∀ a b x, D.γ a x → D.γ b x → D.γ (D.meet a b) x
  widen_left : ∀ a b x, D.γ a x → D.γ (D.widen a b) x
  widen_right : ∀ a b x, D.γ b x → D.γ (D.widen a b) x
  /-- `b` is a sound recomputation below `a`; narrowing must not lose it.
  (The hypothesis `b ⊑ a` is necessary: without it `narrow ⊥ b` could drop `b`.) -/
  narrow_sound : ∀ a b x, D.le b a = true → D.γ b x → D.γ (D.narrow a b) x
  binop_sound : ∀ op a b x y, D.γ a x → D.γ b y → D.γ (D.binop op a b) (op.eval x y)
  filter_sound : ∀ op a b x y, D.γ a x → D.γ b y → op.holds x y →
    D.γ (D.filterCmp op a b).1 x ∧ D.γ (D.filterCmp op a b).2 y

theorem CmpOp.holds_neg (op : CmpOp) (x y : Int) :
    op.neg.holds x y ↔ ¬ op.holds x y := by
  cases op <;> simp [CmpOp.neg, CmpOp.holds]

/-! ## Parity -/

-- Exhaustive case-split over a finite lattice: `simp ... at *` is intentional.
set_option linter.flexible false in
theorem Parity.binop_sound (op : ArithOp) (a b : Par) (x y : Int)
    (ha : Parity.gamma a x) (hb : Parity.gamma b y) :
    Parity.gamma (Parity.binop op a b) (op.eval x y) := by
  cases a <;> cases b <;> cases op <;>
    simp [Parity.binop, Parity.gamma, ArithOp.eval] at * <;> (first
      | omega
      | exact Dvd.dvd.mul_right ha y
      | exact Dvd.dvd.mul_left hb x
      | (rw [Int.mul_emod, ha, hb]; rfl))

set_option linter.flexible false in
theorem Parity.filter_sound (op : CmpOp) (a b : Par) (x y : Int)
    (ha : Parity.gamma a x) (hb : Parity.gamma b y) (hh : op.holds x y) :
    Parity.gamma (Parity.filterCmp op a b).1 x ∧ Parity.gamma (Parity.filterCmp op a b).2 y := by
  cases a <;> cases b <;> cases op <;>
    simp [Parity.filterCmp, Parity.meet, Parity.gamma, CmpOp.holds] at * <;> omega

theorem Parity.lawful : Parity.domain.Lawful where
  bot_empty := fun _ h => h
  top_full := fun _ => trivial
  ofInt_mem := by
    intro n
    change Parity.gamma (if n % 2 = 0 then Par.even else Par.odd) n
    split <;> simp [Parity.gamma] <;> omega
  isBot_empty := by
    intro a h x hx
    have : a = Par.bot := by simpa [Parity.domain] using h
    subst this
    exact hx
  -- finite lattice: case-split both arguments and let `simp` decide
  le_sound := by
    intro a b h x hx
    cases a <;> cases b <;> simp_all [Parity.domain, Parity.le, Parity.gamma]
  join_left := by
    intro a b x hx
    cases a <;> cases b <;> simp_all [Parity.domain, Parity.join, Parity.gamma]
  join_right := by
    intro a b x hx
    cases a <;> cases b <;> simp_all [Parity.domain, Parity.join, Parity.gamma]
  meet_sound := by
    intro a b x ha hb
    cases a <;> cases b <;> simp_all [Parity.domain, Parity.meet, Parity.gamma]
    all_goals omega
  widen_left := by
    intro a b x hx
    cases a <;> cases b <;> simp_all [Parity.domain, Parity.join, Parity.gamma]
  widen_right := by
    intro a b x hx
    cases a <;> cases b <;> simp_all [Parity.domain, Parity.join, Parity.gamma]
  narrow_sound := by
    intro a b x hle hx
    cases a <;> cases b <;>
      simp_all [Parity.domain, Parity.le, Parity.gamma]
  -- sum/difference/product parity: `rcases Int.emod_two_eq_zero_or_one x/y`,
  -- then `simp [Int.add_emod, Int.sub_emod, Int.mul_emod, hx, hy]`
  binop_sound := Parity.binop_sound
  filter_sound := Parity.filter_sound

/-! ## Intervals -/

/-- Strategy: unfold `Bound.le` into integer inequalities by cases on the
bounds, then `omega`.  `mul` needs the four-corner argument (monotonicity of
`*` on each sign quadrant).

Left as `sorry` deliberately: this is a large, in-depth proof (every field of
`Lawful` over `Bound`/`Itv`, including the `widen` threshold folds, `narrow`,
`filterCmp`, and the four-corner `mul` argument).  It would want its own
auxiliary lemmas on `Bound.le`/`add`/`mul` (e.g. a `Bound.toInt?`-style
embedding), so it is not a quick fix. -/
theorem Interval.lawful (ts : List Int) : (Interval.domain ts).Lawful := sorry

/-! ## Reduced product -/

theorem Domain.product_lawful {α β : Type} {D1 : Domain α} {D2 : Domain β}
    (h1 : D1.Lawful) (h2 : D2.Lawful) (r : Reducer D1 D2) :
    (Domain.product D1 D2 r).Lawful where
  bot_empty := fun x h => h1.bot_empty x h.1
  top_full := fun x => ⟨h1.top_full x, h2.top_full x⟩
  ofInt_mem := fun n => (r.exact _ n).2 ⟨h1.ofInt_mem n, h2.ofInt_mem n⟩
  isBot_empty := by
    intro a h x hx
    simp only [product, Bool.or_eq_true] at h
    rcases h with h | h
    · exact h1.isBot_empty _ h x hx.1
    · exact h2.isBot_empty _ h x hx.2
  widen_left := fun a b x hx => ⟨h1.widen_left _ _ x hx.1, h2.widen_left _ _ x hx.2⟩
  widen_right := fun a b x hx => ⟨h1.widen_right _ _ x hx.1, h2.widen_right _ _ x hx.2⟩
  meet_sound := fun a b x ha hb =>
    (r.exact _ x).2 ⟨h1.meet_sound _ _ x ha.1 hb.1, h2.meet_sound _ _ x ha.2 hb.2⟩
  binop_sound := fun op a b x y ha hb =>
    (r.exact _ _).2 ⟨h1.binop_sound op _ _ x y ha.1 hb.1, h2.binop_sound op _ _ x y ha.2 hb.2⟩
  le_sound := by
    intro a b h x hx
    have hna : (D1.isBot a.1 || D2.isBot a.2) = false := by
      cases e : (D1.isBot a.1 || D2.isBot a.2)
      · rfl
      · simp only [Bool.or_eq_true] at e
        rcases e with e | e
        · exact absurd hx.1 (h1.isBot_empty _ e x)
        · exact absurd hx.2 (h2.isBot_empty _ e x)
    simp only [product, hna, Bool.false_or, Bool.and_eq_true] at h
    exact ⟨h1.le_sound _ _ h.1 x hx.1, h2.le_sound _ _ h.2 x hx.2⟩
  join_left := by
    intro a b x hx
    have hna : (D1.isBot a.1 || D2.isBot a.2) = false := by
      cases e : (D1.isBot a.1 || D2.isBot a.2)
      · rfl
      · simp only [Bool.or_eq_true] at e
        rcases e with e | e
        · exact absurd hx.1 (h1.isBot_empty _ e x)
        · exact absurd hx.2 (h2.isBot_empty _ e x)
    simp only [product, hna, Bool.false_eq_true, ite_false]
    split
    · exact hx
    · exact (r.exact _ x).2 ⟨h1.join_left _ _ x hx.1, h2.join_left _ _ x hx.2⟩
  join_right := by
    intro a b x hx
    have hnb : (D1.isBot b.1 || D2.isBot b.2) = false := by
      cases e : (D1.isBot b.1 || D2.isBot b.2)
      · rfl
      · simp only [Bool.or_eq_true] at e
        rcases e with e | e
        · exact absurd hx.1 (h1.isBot_empty _ e x)
        · exact absurd hx.2 (h2.isBot_empty _ e x)
    simp only [product, hnb, Bool.false_eq_true, ite_false]
    split
    · exact hx
    · exact (r.exact _ x).2 ⟨h1.join_right _ _ x hx.1, h2.join_right _ _ x hx.2⟩
  narrow_sound := by
    intro a b x hle hx
    have hnb : (D1.isBot b.1 || D2.isBot b.2) = false := by
      cases e : (D1.isBot b.1 || D2.isBot b.2)
      · rfl
      · simp only [Bool.or_eq_true] at e
        rcases e with e | e
        · exact absurd hx.1 (h1.isBot_empty _ e x)
        · exact absurd hx.2 (h2.isBot_empty _ e x)
    simp only [product, hnb, Bool.false_or, Bool.and_eq_true] at hle
    exact ⟨h1.narrow_sound _ _ x hle.1 hx.1, h2.narrow_sound _ _ x hle.2 hx.2⟩
  filter_sound := by
    intro op a b x y ha hb hh
    have f1 := h1.filter_sound op _ _ x y ha.1 hb.1 hh
    have f2 := h2.filter_sound op _ _ x y ha.2 hb.2 hh
    exact ⟨(r.exact _ x).2 ⟨f1.1, f2.1⟩, (r.exact _ y).2 ⟨f1.2, f2.2⟩⟩

end AbsInt

#min_imports
