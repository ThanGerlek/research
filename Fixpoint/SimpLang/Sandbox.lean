import Fixpoint.SimpLang.Parser
import Fixpoint.SimpLang.Interpreter


def tryInterp (src : String) : Std.Format :=
  match parse src with
  | .ok e => repr (interp e)
  | .error m => s!"ParseError: {m}"

def a := tryInterp "(let x 0 (+ x 1))"
#eval a
