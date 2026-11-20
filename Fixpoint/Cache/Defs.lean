import Std.Data.HashMap
import Std.Data.HashSet
open Std


class Lattice (α : Type) where
  bot : α
  /-- `le a b = true` means `a` is known to be below `b`. -/
  le : α → α → Bool
  join : α → α → α
  /-- Inflationary. Finite domains use `widen a b = join a b`. -/
  widen : α → α → α

/-- Powerset lattice. `widen` is `join`, so finite sets reach a fixed point
    by saturation. -/
instance [BEq α] [Hashable α] : Lattice (HashSet α) where
  bot := {}
  le a b := a.toList.all fun x => b.contains x
  join a b := a.toList.foldl (fun s x => s.insert x) b
  widen a b := a.toList.foldl (fun s x => s.insert x) b
