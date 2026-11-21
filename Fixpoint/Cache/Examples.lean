import Fixpoint.Cache.Cache


open Cache

/-! Two caches the 0CFA powerset cannot show.

    * Intervals widen to `top` once their width exceeds 2. The equation keeps
      joining in the next integer, so without widening it would not terminate.
    * Keys are `Nat` and `normKey n = min n 3`. The equation demands `n + 1`,
      and the table contains only `0` through `3`. -/

inductive Iv where
  | bot
  | bounded (lo hi : Nat)
  | top
  deriving BEq, Repr

def Iv.join : Iv → Iv → Iv
  | .bot, b => b
  | a, .bot => a
  | .top, _ => .top
  | _, .top => .top
  | .bounded lo₁ hi₁, .bounded lo₂ hi₂ =>
    .bounded (min lo₁ lo₂) (max hi₁ hi₂)

/-- Collapse an interval once `hi - lo` exceeds 2. -/
def Iv.widen (a b : Iv) : Iv :=
  match Iv.join a b with
  | .bounded lo hi => if hi - lo > 2 then .top else .bounded lo hi
  | other => other

instance : Lattice Iv where
  bot := .bot
  le
    | .bot, _ => true
    | _, .top => true
    | .bounded lo₁ hi₁, .bounded lo₂ hi₂ => lo₂ ≤ lo₁ && hi₁ ≤ hi₂
    | _, _ => false
  join := Iv.join
  widen := Iv.widen

def Iv.show : Iv → String
  | .bot => "bot"
  | .bounded lo hi => s!"[{lo}, {hi}]"
  | .top => "top"

/-- Publish `[0, 0]`, then on each accumulated interval `[lo, hi]` publish
    `[hi, hi + 1]`. Widening turns `[0, 3]` into `top` and the chain stops. -/
def ivEquation (self : Unit → CacheM Unit Iv Iv) : Unit → CacheM Unit Iv Iv
  | _ =>
    each [
      pure (.bounded 0 0),
      self () >>= fun
        | .bounded _ hi => pure (.bounded hi (hi + 1))
        | .top => pure .top
        | .bot => fail
    ]

inductive Flag where
  | bot
  | top
  deriving BEq, Repr

instance : Lattice Flag where
  bot := .bot
  le a b := a == .bot || b == .top
  join
    | .bot, b => b
    | a, .bot => a
    | .top, .top => .top
  widen
    | .bot, b => b
    | a, .bot => a
    | .top, .top => .top

/-- Publish `top`, then demand the next key. `pure` runs first so the recursive
    demand is not waiting on its own unpublished cell. -/
def natEquation (self : Nat → CacheM Nat Flag Flag) (n : Nat) : CacheM Nat Flag Flag :=
  each [
    pure .top,
    self (n + 1)
  ]

def failWith (msg : String) : IO Unit :=
  throw <| IO.userError msg

def demos : IO Unit := do
  let ivTbl ← run (fix ivEquation ())
  match ivTbl[()]? with
  | some (some .top, _) => IO.println "ok interval"
  | some (some iv, _) => failWith s!"interval cell is {iv.show}, expected top"
  | _ => failWith "interval cell missing"

  let natTbl ← run (fix natEquation 0) (fun n => min n 3)
  let keys := (natTbl.toList.map (·.1)).toArray.qsort (· < ·) |>.toList
  if keys != [0, 1, 2, 3] then
    failWith s!"normKey keys {keys}, expected [0, 1, 2, 3]"
  for (k, v, _) in natTbl.toList do
    match v with
    | some .top => pure ()
    | _ => failWith s!"key {k} did not widen to top"
  IO.println "ok normKey"

#eval demos
