import Fixpoint.EZeroCFA_claude.AbsInt

/-!
    lake exe absint                      # run the demos
    lake exe absint --prog "<src>" --domain product --k 1
    options: --domain interval|parity|product|product-noreduce
             --k N  --delay N  --narrow N  --thresholds N N ...

`--prog` goes through the run-time parser (`parseRaw`); the demos use the
embedded syntax instead.
-/

open AbsInt

structure Cli where
  cfg : Config := {}
  prog : Option String := none
  /-- inside a `--thresholds` list -/
  collecting : Bool := false

def parseArgs : List String → Cli → Except String Cli
  | [], c => .ok c
  | "--prog" :: v :: rest, c => parseArgs rest { c with prog := some v, collecting := false }
  | "--domain" :: v :: rest, c => do
    let some d := DomainName.ofString? v | throw s!"unknown domain {v}"
    parseArgs rest { c with cfg := { c.cfg with domain := d }, collecting := false }
  | "--k" :: v :: rest, c => do
    let some n := v.toNat? | throw s!"bad number {v}"
    parseArgs rest { c with cfg := { c.cfg with k := n }, collecting := false }
  | "--delay" :: v :: rest, c => do
    let some n := v.toNat? | throw s!"bad number {v}"
    parseArgs rest { c with cfg := { c.cfg with delay := n }, collecting := false }
  | "--narrow" :: v :: rest, c => do
    let some n := v.toNat? | throw s!"bad number {v}"
    parseArgs rest { c with cfg := { c.cfg with narrow := n }, collecting := false }
  | "--thresholds" :: rest, c =>
    parseArgs rest { c with cfg := { c.cfg with thresholds := [] }, collecting := true }
  | a :: rest, c =>
    if c.collecting then
      (match a.toInt? with
       | some n => parseArgs rest { c with cfg := { c.cfg with thresholds := c.cfg.thresholds ++ [n] } }
       | none => .error s!"unexpected argument {a}")
    else .error s!"unexpected argument {a}"

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e =>
    IO.eprintln e
    return 1
  | .ok cli =>
    match cli.prog with
    | none =>
      runDemos
      return 0
    | some src =>
      match parseRaw src >>= fun r => runConfig r cli.cfg with
      | .ok rep =>
        IO.println s!"result: {rep.result}"
        IO.println s!"store:  {rep.store}"
        return 0
      | .error e =>
        IO.eprintln s!"error: {e}"
        return 1
