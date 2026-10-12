import Fixpoint.SimpLang.Parser
import Fixpoint.SimpLang.Interpreter


def tryInterp (src : String) : Std.Format :=
  match parse src with
  | .ok e => repr (interp e)
  | .error m => s!"ParseError: {m}"

def a := tryInterp "(let x 0 (+ x 1))"
#eval a


-- Layout is irrelevant:
#eval tryInterp "(let x 0\n   (+ x 1))"
#eval tryInterp "(let x 0\n   (+ x 1))"
#eval tryInterp "  ( let   x\t0 (+\nx\n1 ) )  "
#eval tryInterp "(let f (fun x (+ x 1)) (app f 3))"
#eval tryInterp "(app (fun x (+ x 1)) 3)"
#eval tryInterp "(if (if #true #true #false) 1 0)"
#eval tryInterp "(rec f n (if (< n 1) 0 (app f (- n 1))))"
#eval tryInterp "(+ -3 4)"
#eval tryInterp "(fun 7)"
#eval tryInterp
  "(let x (con iibCon 1 0 #true)
     (case x
       (iiCon a b
         (+ a b))
       (biiCon thn els cnd
         (if cnd thn els))))"

-- Errors:
#eval tryInterp "(x + 1)"          -- unknown form 'x'
#eval tryInterp "(f 3)"            -- unknown form 'f'
#eval tryInterp "((fun x x) 3)"    -- head must be a keyword
#eval tryInterp "(if #true 1)"     -- 'if' takes exactly 3 subexpressions
#eval tryInterp "(+ 1 2 3)"        -- '+' takes exactly 2 arguments
#eval tryInterp "(let if 1 2)"     -- invalid name 'if'
#eval tryInterp "12abc"            -- malformed integer
#eval tryInterp "#maybe"           -- unknown '#' literal
#eval tryInterp "(+ 1 2"           -- missing ')'
#eval tryInterp "(+ 1 2))"         -- trailing input
#eval tryInterp "()"               -- empty list
#eval tryInterp "x y"              -- trailing input
