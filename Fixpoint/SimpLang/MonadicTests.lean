import Fixpoint.SimpLang.Tests
import Fixpoint.SimpLang.MonadicInterpreter

/-!
# Differential tests: `Monadic.interp` vs `interp`

Reuses the case tables of `Tests.lean`; every source program must print identically under both
interpreters (and at every fuel in `fuelCases`). A failing case makes this file fail to compile.
-/

def showV (v : Value) : String := toString (repr v)

/-- Programs on which the two interpreters disagree (at the given fuel). -/
def disagree (fuel : Nat) (srcs : List String) : List String :=
  srcs.filter fun s =>
    match parse s with
    | .ok e => showV (interpf fuel e) != showV (Monadic.interpf fuel e)
    | .error _ => false

def allSrcs : List String :=
  (basics ++ operators ++ errors ++ ifs ++ scoping ++ apps ++ malformed ++ cases).map (·.1)
    ++ fuelCases.map (·.2.1)
    ++ [countdown 0, countdown 100, countdown 1000]

#eval allSrcs.length
#eval disagree 10000 allSrcs
#guard (disagree 10000 allSrcs).isEmpty
#guard ([0, 1, 2, 3, 5, 10, 100].all fun n => (disagree n allSrcs).isEmpty)

-- The monadic interpreter satisfies the expected-output tables directly, too.
def failingMonadic (cs : List (String × String)) : List (String × String × String) :=
  cs.filterMap fun (s, exp) =>
    match parse s with
    | .ok e => if showV (Monadic.interp e) == exp then none else some (s, exp, showV (Monadic.interp e))
    | .error _ => none
#guard (failingMonadic (basics ++ operators ++ errors ++ ifs ++ scoping ++ apps ++ malformed ++ cases)).isEmpty
#guard fuelCases.all fun (n, s, exp) =>
  match parse s with
  | .ok e => showV (Monadic.interpf n e) == exp
  | .error _ => false
-- Combined error order is left-nested.
#guard showV (Monadic.interp (.con "A" [.ref "a", .ref "b", .ref "c"]))
  == showV (interp (.con "A" [.ref "a", .ref "b", .ref "c"]))
