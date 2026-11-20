
universe u

-- 1. Separate data from obligations. Structures carry no proofs. Every proof-shaped thing is a Prop that lives in the ledger.

structure Checker (α : Type u) where
  W      : Type
  verify : α → W → Bool            -- `W = Unit` for plain deciders

def Checker.Sound (C : Checker α) (P : α → Prop) : Prop :=
  ∀ a w, C.verify a w = true → P a


-- Analyzers have one semantic relation. Every mode is a relation `Produces a w` ("the program can output w on a") plus a refinement claim. Modes differ only in how Produces is defined and who discharges Refines.

inductive Mode (α) (W : Type)
  | none  -- formalization only
  | lean (run : α → Option W)
  | exe (cmd : String) (version hash : String)
  | cert (gen : String)  -- untrusted generator

structure Analyzer (C : Checker α) where
  mode : Mode α C.W
  Produces : α → C.W → Prop  -- `run a = some w` for .lean; opaque for .exe

def Analyzer.Refines (A : Analyzer C) : Prop :=
  ∀ a w, A.Produces a w → C.verify a w = true


-- A proved status carries a proof, so it can't lie. Because Assume computes to True for proved claims, the theorem's hypotheses shrink automatically as you discharge claims, with no edits to the theorem.

inductive Status (p : Prop)
  | proved   (h : p)
  | attested (tool version hash : String)
  | todo     (note : String)

def Status.Assume {p : Prop} : Status p → Prop
  | .proved _ => True
  | _         => p

theorem Status.get {p} (s : Status p) (h : s.Assume) : p := by
  cases s <;> first | exact ‹p› | exact h   -- adjust to taste

-- Then bundle per oracle and compute the outstanding assumptions:

structure Trust (C : Checker α) (P) (A : Analyzer C) (a : α) where
  sound    : Status (C.Sound P)
  refines  : Status A.Refines
  observed : Status (∃ w, A.Produces a w)    -- attested with tool/version/hash/input hash

def Trust.Assumptions (T : Trust C P A a) : Prop :=
  T.sound.Assume ∧ T.refines.Assume ∧ T.observed.Assume

-- `#reduce T.Assumptions` is now your machine-computed to-do list, derived from the data rather than from a free-form origin string.

-- 4. Prove the chain once, generically.

theorem Trust.conclude (T : Trust C P A a) (h : T.Assumptions) : P a := by
  obtain ⟨hs, hr, ho⟩ := h
  obtain ⟨w, hw⟩ := T.observed.get ho
  exact (T.sound.get hs) a w ((T.refines.get hr) a w hw)
