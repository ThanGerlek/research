import Std.Data.HashMap
import Std.Data.HashSet
import Fixpoint.Cache.Cache

open Std

open Cache

/-! Two functions, one `self`.

    `f` and `g` are keys. Each body publishes its own mark, then demands itself
    and the other through `self`. A demand for a key that is already running
    does not enter the body again: it subscribes and receives the element stored
    so far. Both calls happen in one `run`, so they share a table. -/

inductive Fn where
  | f
  | g
  deriving BEq, Hashable, Repr

def Output := String
  deriving BEq, Hashable, Repr

def Input := Nat
  deriving BEq, Hashable, Repr

abbrev M := CacheM (Fn × Input) (HashSet Output)

def single (m : Output) : HashSet Output :=
  ({} : HashSet Output).insert m


def fBody (self : Fn × Input → M (HashSet Output)) (x : Input) : M (HashSet Output) :=
  each [
    pure (single "fResult"), -- Base case
    self ⟨.f, x⟩,          -- call f(x); the open cell is replayed, the body is not re-entered
    self ⟨.g, x⟩           -- call g(x)
  ]

def gBody (self : Fn × Input → M (HashSet Output)) (x : Input) : M (HashSet Output) :=
  each [
    pure (single "gResult"),
    self ⟨.g, x⟩,
    self ⟨.f, x⟩
  ]

def equation (self : Fn × Input → M (HashSet Output)) : Fn × Input → M (HashSet Output)
  | ⟨.f, x⟩ => fBody self x
  | ⟨.g, x⟩ => gBody self x


-- Display logic

def showMarks (vs : HashSet Output) : String :=
  let xs := (vs.toList.map fun
    a => a)
    -- | .f => "f"
    -- | .g => "g").toArray.qsort (· < ·) |>.toList
  "{" ++ ", ".intercalate xs ++ "}"

def showCell (name : String) (entry : Option (Option (HashSet Output) × List (HashSet Output → IO Unit))) : String :=
  match entry with
  | some (some vs, _) => s!"{name} ↦ {showMarks vs}"
  | _ => s!"{name} ↦ ∅"

def demo : IO Unit := do
  let tbl ← run (fix equation ⟨Fn.f, (0 : Nat)⟩)
  let f0_key : Fn × Input := ⟨Fn.f, (0 : Nat)⟩
  let f0_cell := tbl[f0_key]?
  let g0_key : Fn × Input := ⟨Fn.g, (0 : Nat)⟩
  let g0_cell := tbl[g0_key]?
  IO.println (showCell "f(0)" f0_cell)
  IO.println (showCell "g(0)" g0_cell)
  let hasBoth (entry : Option (Entry (HashSet Output))) : Bool :=
    match entry with
    | some (some vs, _) => vs.contains "fResult" && vs.contains "gResult"
    | _ => false
  if hasBoth f0_cell && hasBoth g0_cell then
    pure ()
  else
    throw <| IO.userError "expected both cells to contain f(0) and g(0)"

#eval demo
