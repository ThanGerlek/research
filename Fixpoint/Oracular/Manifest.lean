import Mathlib.Data.Set.Basic


def Name := String

inductive Origin
  | proved (decl : Name)
  | attested (tool version hash : String)
  | open (note : String)

structure Claim where
  stmt : Prop
  origin : Origin

structure Manifest where
  claims : List Claim

def Manifest.Holds (M : Manifest) := ∀ c ∈ M.claims, c.stmt

-- Naive approach: axiomatically declare all manifests hold
axiom manifestsHold : ∀ (M : Manifest), M.Holds

-- Better approach: programmatically generate axioms?
