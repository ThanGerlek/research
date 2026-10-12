import Fixpoint.SimpLang.Parser
import Fixpoint.SimpLang.Interpreter

/-!
# Tests for the SimpLang parser and interpreter

Run with `lake env lean Fixpoint/SimpLang/Tests.lean`. Every table below is checked with
`#guard`, so a failing case makes this file fail to compile; the `#eval` of the failing list
beforehand prints exactly which cases failed. Expected strings follow `LangSpec.md`.
-/

/-! ## Helpers -/

/-- Parse and evaluate, printing the value (or the parse error). -/
def run (src : String) : String :=
  match parse src with
  | .ok e => toString (repr (interp e))
  | .error m => s!"ParseError: {m}"

/-- Same, with an explicit fuel. -/
def runf (fuel : Nat) (src : String) : String :=
  match parse src with
  | .ok e => toString (repr (interpf fuel e))
  | .error m => s!"ParseError: {m}"

def evalExpr (e : Expr) : String := toString (repr (interp e))
def evalExprF (fuel : Nat) (e : Expr) : String := toString (repr (interpf fuel e))

/-- `(source, expected)` pairs that fail. -/
def failingParse (cases : List (String × String)) : List (String × String × String) :=
  cases.filterMap fun (s, exp) => if tryParse s == exp then none else some (s, exp, tryParse s)

def failingRun (cases : List (String × String)) : List (String × String × String) :=
  cases.filterMap fun (s, exp) => if run s == exp then none else some (s, exp, run s)

/-! ## Tokenizer -/

def tokenizeCases : List (String × List String) := [
  ("", []),
  ("   \n\t ", []),
  ("x", ["x"]),
  ("(+ 1 2)", ["(", "+", "1", "2", ")"]),
  ("(+1 2)", ["(", "+1", "2", ")"]),
  ("((x))", ["(", "(", "x", ")", ")"]),
  ("(  +\n   1\n\t2 )", ["(", "+", "1", "2", ")"]),
  -- comments
  ("; only a comment", []),
  (";", []),
  ("x ; trailing", ["x"]),
  ("x;y", ["x"]),
  ("a;b\nc", ["a", "c"]),
  ("a ;c\n;d\ne", ["a", "e"]),
  ("(a ; x )\n)", ["(", "a", ")"]),
  ("a;c\r\nb", ["a", "b"]),
  ("(a;\n)", ["(", "a", ")"]),
  (";;;;\n;\nz", ["z"]),
  ("#true;#false", ["#true"])
]

#eval tokenizeCases.filter fun (s, exp) => tokenize s != exp
#guard (tokenizeCases.filter fun (s, exp) => tokenize s != exp).isEmpty

/-! ## Parser: successful parses (canonical printing) -/

def parseOk : List (String × String) := [
  -- atoms
  ("0", "0"), ("42", "42"), ("-7", "-7"), ("007", "7"), ("-0", "0"),
  ("123456789012345678901234567890", "123456789012345678901234567890"),
  ("#true", "#true"), ("#false", "#false"),
  ("x", "x"), ("_", "_"), ("_x", "_x"), ("x1", "x1"), ("X_Y2", "X_Y2"),
  ("let1", "let1"), ("Let", "Let"), ("IF", "IF"), ("rec", "rec"), ("funny", "funny"),
  -- operators
  ("(+ 1 2)", "(+ 1 2)"), ("(- 1 2)", "(- 1 2)"), ("(* 1 2)", "(* 1 2)"),
  ("(/ 1 2)", "(/ 1 2)"), ("(% 1 2)", "(% 1 2)"), ("(< 1 2)", "(< 1 2)"),
  ("(== 1 2)", "(== 1 2)"),
  ("(+ -3 4)", "(+ -3 4)"),
  ("(- -3 -4)", "(- -3 -4)"),
  ("(+ (+ 1 2) (* 3 4))", "(+ (+ 1 2) (* 3 4))"),
  -- forms
  ("(if #true 1 2)", "(if #true 1 2)"),
  ("(if (if #true #true #false) 1 0)", "(if (if #true #true #false) 1 0)"),
  ("(let x 0 (+ x 1))", "(let x 0 (+ x 1))"),
  ("(let x (let y 1 y) x)", "(let x (let y 1 y) x)"),
  ("(fun x (+ x 1))", "(fun x (+ x 1))"),
  ("(fun x y z (+ x y))", "(fun x y z (+ x y))"),
  ("(fun 7)", "(fun 7)"),                -- zero parameters parses (interpreter rejects)
  ("(fun x)", "(fun x)"),                -- parameters [] and body x
  ("(fun x x x)", "(fun x x x)"),        -- duplicate parameters parse
  ("(app f)", "(app f)"),
  ("(app f 1 2 3)", "(app f 1 2 3)"),
  ("(app (fun x x) 3)", "(app (fun x x) 3)"),
  ("(app (app f 1) 2)", "(app (app f 1) 2)"),
  ("(con None)", "(con None)"),
  ("(con Pair 1 (con Pair 2 3))", "(con Pair 1 (con Pair 2 3))"),
  ("(case x)", "(case x)"),              -- zero clauses parses
  ("(case x (A 0))", "(case x (A 0))"),
  ("(case x (A a b (+ a b)) (B 1))", "(case x (A a b (+ a b)) (B 1))"),
  ("(case x (A 0) (A 1))", "(case x (A 0) (A 1))"),            -- duplicate tags parse
  ("(case x (A a a 0))", "(case x (A a a 0))"),                 -- duplicate vars parse
  -- layout and comments
  ("  ( let   x\t0 (+\nx\n1 ) )  ", "(let x 0 (+ x 1))"),
  ("(let x 0\n   (+ x 1))", "(let x 0 (+ x 1))"),
  ("(+ 1 ; one\n 2)", "(+ 1 2)"),
  ("; leading\n(+ 1 2) ; trailing", "(+ 1 2)"),
  ("(+ 1 2 ; unfinished\n)", "(+ 1 2)"),
  ("(+ 1 2) ; x )", "(+ 1 2)"),
  ("(let x;y 1 x)", "ParseError: missing ')'"),
  ("x;y", "x"),
  -- the example from the Parser docs
  ("(let x (con iibCon 1 0 #true)\n (case x (iiCon a b (+ a b)) (iibCon thn els cnd (if cnd thn els))))",
   "(let x (con iibCon 1 0 #true) (case x (iiCon a b (+ a b)) (iibCon thn els cnd (if cnd thn els))))")
]

#eval failingParse parseOk
#guard (failingParse parseOk).isEmpty

/-! ## Parser: errors -/

def parseErr : List (String × String) := [
  -- structure
  ("", "ParseError: unexpected end of input"),
  ("   ; just a comment", "ParseError: unexpected end of input"),
  (")", "ParseError: unexpected ')'"),
  ("(", "ParseError: missing ')'"),
  ("(+ 1 2", "ParseError: missing ')'"),
  ("(+ 1 2))", "ParseError: unexpected trailing input starting at ')'"),
  ("(+ 1 2) 3", "ParseError: unexpected trailing input starting at '3'"),
  ("x y", "ParseError: unexpected trailing input starting at 'y'"),
  ("()", "ParseError: empty list '()'"),
  ("(())", "ParseError: the head of a list must be a keyword (use 'app' to apply)"),
  -- heads
  ("(x + 1)", "ParseError: unknown form 'x'"),
  ("(f 3)", "ParseError: unknown form 'f'"),
  ("(rec f n n)", "ParseError: unknown form 'rec'"),
  ("(1 2)", "ParseError: unknown form '1'"),
  ("(#true 1)", "ParseError: unknown form '#true'"),
  ("((fun x x) 3)", "ParseError: the head of a list must be a keyword (use 'app' to apply)"),
  -- arities
  ("(if #true 1)", "ParseError: 'if' takes exactly 3 subexpressions"),
  ("(if #true 1 2 3)", "ParseError: 'if' takes exactly 3 subexpressions"),
  ("(if)", "ParseError: 'if' takes exactly 3 subexpressions"),
  ("(let x 1)", "ParseError: 'let' takes a name, a right-hand side, and a body"),
  ("(let x 1 2 3)", "ParseError: 'let' takes a name, a right-hand side, and a body"),
  ("(+ 1)", "ParseError: '+' takes exactly 2 arguments"),
  ("(+ 1 2 3)", "ParseError: '+' takes exactly 2 arguments"),
  ("(+)", "ParseError: '+' takes exactly 2 arguments"),
  ("(== 1)", "ParseError: '==' takes exactly 2 arguments"),
  ("(< 1 2 3)", "ParseError: '<' takes exactly 2 arguments"),
  ("(fun)", "ParseError: 'fun' is missing its body"),
  ("(app)", "ParseError: 'app' needs a function"),
  ("(con)", "ParseError: 'con' needs a tag"),
  ("(case)", "ParseError: 'case' needs a scrutinee"),
  -- names
  ("(let if 1 2)", "ParseError: invalid name 'if'"),
  ("(let + 1 2)", "ParseError: invalid name '+'"),
  ("(let 1 2 3)", "ParseError: invalid name '1'"),
  ("(let x-y 1 2)", "ParseError: invalid name 'x-y'"),
  ("(let (x) 1 2)", "ParseError: expected a name, found a list"),
  ("(fun if 1)", "ParseError: invalid name 'if'"),
  ("(fun (x) 1)", "ParseError: expected a name, found a list"),
  ("(fun x 1 x)", "ParseError: invalid name '1'"),
  ("(con 1)", "ParseError: invalid name '1'"),
  ("(con let)", "ParseError: invalid name 'let'"),
  ("(con (A))", "ParseError: expected a name, found a list"),
  ("(case 1 (let 0))", "ParseError: invalid name 'let'"),
  ("(case 1 (A case 0))", "ParseError: invalid name 'case'"),
  ("(case 1 (A 1 2))", "ParseError: invalid name '1'"),
  ("(case 1 ())", "ParseError: a case clause must be a non-empty list '(Tag vars... body)'"),
  ("(case 1 x)", "ParseError: a case clause must be a non-empty list '(Tag vars... body)'"),
  ("(case 1 (A))", "ParseError: 'case clause' is missing its body"),
  -- reserved words as variables
  ("let", "ParseError: 'let' is reserved and can't be used as a variable"),
  ("if", "ParseError: 'if' is reserved and can't be used as a variable"),
  ("fun", "ParseError: 'fun' is reserved and can't be used as a variable"),
  ("app", "ParseError: 'app' is reserved and can't be used as a variable"),
  ("con", "ParseError: 'con' is reserved and can't be used as a variable"),
  ("case", "ParseError: 'case' is reserved and can't be used as a variable"),
  ("+", "ParseError: '+' is reserved and can't be used as a variable"),
  ("-", "ParseError: '-' is reserved and can't be used as a variable"),
  ("*", "ParseError: '*' is reserved and can't be used as a variable"),
  ("/", "ParseError: '/' is reserved and can't be used as a variable"),
  ("%", "ParseError: '%' is reserved and can't be used as a variable"),
  ("<", "ParseError: '<' is reserved and can't be used as a variable"),
  ("==", "ParseError: '==' is reserved and can't be used as a variable"),
  ("(+ 1 let)", "ParseError: 'let' is reserved and can't be used as a variable"),
  -- integers
  ("12abc", "ParseError: malformed integer '12abc'"),
  ("1x", "ParseError: malformed integer '1x'"),
  ("-5a", "ParseError: malformed integer '-5a'"),
  ("5-3", "ParseError: malformed integer '5-3'"),
  ("1_000", "ParseError: malformed integer '1_000'"),
  ("1.5", "ParseError: malformed integer '1.5'"),
  -- hash literals
  ("#maybe", "ParseError: unknown '#' literal '#maybe'"),
  ("#", "ParseError: unknown '#' literal '#'"),
  ("#True", "ParseError: unknown '#' literal '#True'"),
  ("#true1", "ParseError: unknown '#' literal '#true1'"),
  ("(let #x 1 2)", "ParseError: invalid name '#x'"),
  -- non-name characters
  ("+7", "ParseError: invalid name '+7'"),
  ("-x", "ParseError: invalid name '-x'"),
  ("--5", "ParseError: invalid name '--5'"),
  ("x-y", "ParseError: invalid name 'x-y'"),
  ("x?", "ParseError: invalid name 'x?'"),
  ("a.b", "ParseError: invalid name 'a.b'"),
  ("'q", "ParseError: invalid name ''q'"),
  ("é", "ParseError: invalid name 'é'"),
  ("[x]", "ParseError: invalid name '[x]'"),
  ("(let x[0] 1 2)", "ParseError: invalid name 'x[0]'")
]

#eval failingParse parseErr
#guard (failingParse parseErr).isEmpty

/-- Printing a parsed program and re-parsing it gives the same program. -/
def roundTrips (s : String) : Bool :=
  match parse s with
  | .ok e => match parse (showExpr e) with
    | .ok e' => showExpr e' == showExpr e
    | .error _ => false
  | .error _ => true

#guard (parseOk.all fun (s, _) => roundTrips s)

/-! ## Interpreter: basics -/

def basics : List (String × String) := [
  ("0", "INT 0"), ("42", "INT 42"), ("-7", "INT -7"), ("#true", "BOOL True"),
  ("#false", "BOOL False"),
  ("123456789012345678901234567890", "INT 123456789012345678901234567890"),
  ("(let x 0 (+ x 1))", "INT 1"),
  ("(let x 0\n   (+ x 1))", "INT 1"),
  ("(let f (fun x (+ x 1)) (app f 3))", "INT 4"),
  ("(app (fun x (+ x 1)) 3)", "INT 4"),
  ("(app (fun x y (- x y)) 10 3)", "INT 7"),
  ("(if (if #true #true #false) 1 0)", "INT 1"),
  ("(if #false 1 0)", "INT 0"),
  ("(+ 1 ; comment\n 2)", "INT 3"),
  -- a function value prints its parameters
  ("(fun x y 0)", "FUN [\"x\", \"y\"]"),
  ("(con A 1 2)", "CON A"),
  ("(con None)", "CON None")
]

#eval failingRun basics
#guard (failingRun basics).isEmpty

/-! ## Interpreter: operators -/

def operators : List (String × String) := [
  ("(+ 2 3)", "INT 5"), ("(+ -2 -3)", "INT -5"), ("(- 2 3)", "INT -1"), ("(- 0 5)", "INT -5"),
  ("(* 4 5)", "INT 20"), ("(* -4 5)", "INT -20"), ("(* 0 99)", "INT 0"),
  ("(* 123456789012345678901234567890 10)", "INT 1234567890123456789012345678900"),
  ("(< 1 2)", "BOOL True"), ("(< 2 2)", "BOOL False"), ("(< 3 2)", "BOOL False"),
  ("(< -3 -2)", "BOOL True"),
  ("(== 1 1)", "BOOL True"), ("(== 1 2)", "BOOL False"), ("(== -1 -1)", "BOOL True"),
  ("(== #true #true)", "BOOL True"), ("(== #false #false)", "BOOL True"),
  ("(== #true #false)", "BOOL False"),
  ("(== (+ 1 1) 2)", "BOOL True"),
  -- Euclidean division: remainder always in [0, |divisor|)
  ("(/ 7 2)", "INT 3"), ("(% 7 2)", "INT 1"),
  ("(/ -7 2)", "INT -4"), ("(% -7 2)", "INT 1"),
  ("(/ 7 -2)", "INT -3"), ("(% 7 -2)", "INT 1"),
  ("(/ -7 -2)", "INT 4"), ("(% -7 -2)", "INT 1"),
  ("(% -1 5)", "INT 4"), ("(/ -1 5)", "INT -1"),
  ("(% 6 3)", "INT 0"), ("(/ 6 3)", "INT 2"), ("(/ 0 5)", "INT 0"), ("(% 0 5)", "INT 0"),
  -- division by zero
  ("(/ 1 0)", "ERROR 'arith: division by zero'"),
  ("(% 1 0)", "ERROR 'arith: modulo by zero'"),
  ("(/ 0 0)", "ERROR 'arith: division by zero'"),
  ("(% 0 0)", "ERROR 'arith: modulo by zero'"),
  ("(/ 5 (- 3 3))", "ERROR 'arith: division by zero'"),
  -- type errors
  ("(+ 1 #true)", "ERROR 'type: expected int operands for '+''"),
  ("(+ #true 1)", "ERROR 'type: expected int operands for '+''"),
  ("(- #true #false)", "ERROR 'type: expected int operands for '-''"),
  ("(* (fun x x) 1)", "ERROR 'type: expected int operands for '*''"),
  ("(/ 1 (con A))", "ERROR 'type: expected int operands for '/''"),
  ("(% #true 2)", "ERROR 'type: expected int operands for '%''"),
  ("(< #true 1)", "ERROR 'type: expected int operands for '<''"),
  ("(< #true #false)", "ERROR 'type: expected int operands for '<''"),
  -- equality is an error for everything but two ints / two bools
  ("(== 1 #true)", "ERROR 'type: '==' needs two ints or two bools'"),
  ("(== #true 1)", "ERROR 'type: '==' needs two ints or two bools'"),
  ("(== (fun x x) (fun x x))", "ERROR 'type: '==' needs two ints or two bools'"),
  ("(let f (fun x x) (== f f))", "ERROR 'type: '==' needs two ints or two bools'"),
  ("(== (con A) (con A))", "ERROR 'type: '==' needs two ints or two bools'"),
  ("(== (con A) 1)", "ERROR 'type: '==' needs two ints or two bools'"),
  -- nested
  ("(+ (* 2 3) (- 10 (/ 9 3)))", "INT 13"),
  ("(== (% 10 3) (- 2 1))", "BOOL True")
]

#eval failingRun operators
#guard (failingRun operators).isEmpty

/-! ## Interpreter: error propagation and combination -/

def errors : List (String × String) := [
  -- unbound variables
  ("x", "ERROR 'scope: free variable 'x''"),
  ("(+ 1 y)", "ERROR 'scope: free variable 'y''"),
  -- errors dominate non-errors; the operator is not applied
  ("(+ #true (/ 1 0))", "ERROR 'arith: division by zero'"),
  ("(+ (/ 1 0) #true)", "ERROR 'arith: division by zero'"),
  ("(== (fun x x) (% 1 0))", "ERROR 'arith: modulo by zero'"),
  -- two errors are combined, left then right
  ("(+ y (app 1 2))", "ERROR '[ scope: free variable 'y' | type: expected a function ]'"),
  ("(+ y z)", "ERROR '[ scope: free variable 'y' | scope: free variable 'z' ]'"),
  ("(< (/ 1 0) (% 1 0))", "ERROR '[ arith: division by zero | arith: modulo by zero ]'"),
  ("(== (% 1 0) (/ 1 0))", "ERROR '[ arith: modulo by zero | arith: division by zero ]'"),
  -- more than two combine left to right
  ("(app g a b)",
   "ERROR '[ [ scope: free variable 'g' | scope: free variable 'a' ] | scope: free variable 'b' ]'"),
  ("(con T a b c)",
   "ERROR '[ [ scope: free variable 'a' | scope: free variable 'b' ] | scope: free variable 'c' ]'"),
  ("(+ (+ a b) (+ c d))",
   "ERROR '[ [ scope: free variable 'a' | scope: free variable 'b' ] | [ scope: free variable 'c' | scope: free variable 'd' ] ]'"),
  -- only the erroring arguments are combined
  ("(app (fun x y 0) 1 q)", "ERROR 'scope: free variable 'q''"),
  ("(app (fun x y 0) q 1)", "ERROR 'scope: free variable 'q''"),
  ("(con T 1 q 2 r 3)", "ERROR '[ scope: free variable 'q' | scope: free variable 'r' ]'"),
  -- errors in the function position / arguments win over the call's own checks
  ("(app 1 q)", "ERROR 'scope: free variable 'q''"),
  ("(app (fun x x) q 1)", "ERROR 'scope: free variable 'q''"),
  ("(app (fun 7) q)", "ERROR '[ malformed: function has no parameters | scope: free variable 'q' ]'"),
  -- strict: let rhs errors are not bound
  ("(let x (/ 1 0) 5)", "ERROR 'arith: division by zero'"),
  ("(let x (app 1 2) 5)", "ERROR 'type: expected a function'"),
  ("(let x (app 1 2) x)", "ERROR 'type: expected a function'"),
  ("(let x 1 (let y (+ x z) 0))", "ERROR 'scope: free variable 'z''"),
  -- strict: call arguments
  ("(app (fun x 1) (/ 1 0))", "ERROR 'arith: division by zero'"),
  ("(app (fun x 1) (app 1 2))", "ERROR 'type: expected a function'"),
  -- strict: constructor fields
  ("(con A (/ 1 0))", "ERROR 'arith: division by zero'"),
  ("(con A 1 (con B (% 1 0)))", "ERROR 'arith: modulo by zero'"),
  ("(case (con A (/ 1 0)) (A x 0))", "ERROR 'arith: division by zero'"),
  -- strict: scrutinee and if condition
  ("(case y (A 1))", "ERROR 'scope: free variable 'y''"),
  ("(case (/ 1 0) (A 1))", "ERROR 'arith: division by zero'"),
  ("(if y 1 2)", "ERROR 'scope: free variable 'y''"),
  ("(if (/ 1 0) 1 2)", "ERROR 'arith: division by zero'"),
  -- errors pass through branches / bodies unchanged
  ("(if #true (/ 1 0) 2)", "ERROR 'arith: division by zero'"),
  ("(app (fun x (/ x 0)) 1)", "ERROR 'arith: division by zero'"),
  ("(case (con A) (A (/ 1 0)))", "ERROR 'arith: division by zero'"),
  -- unchosen branches / unmatched clauses are never evaluated
  ("(if #true 1 (/ 1 0))", "INT 1"),
  ("(if #false (/ 1 0) 2)", "INT 2"),
  ("(if #true 1 y)", "INT 1"),
  ("(case (con A) (A 1) (B (/ 1 0)))", "INT 1"),
  ("(case (con B) (A y) (B 2))", "INT 2"),
  -- unused bindings are fine when not errors
  ("(let x 1 2)", "INT 2")
]

#eval failingRun errors
#guard (failingRun errors).isEmpty

/-! ## Interpreter: if -/

def ifs : List (String × String) := [
  ("(if 1 2 3)", "ERROR 'type: 'if' condition must be a bool'"),
  ("(if (fun x x) 2 3)", "ERROR 'type: 'if' condition must be a bool'"),
  ("(if (con A) 2 3)", "ERROR 'type: 'if' condition must be a bool'"),
  ("(if (< 1 2) 10 20)", "INT 10"),
  ("(if (== 1 2) 10 20)", "INT 20"),
  ("(if #true (if #false 1 2) 3)", "INT 2"),
  ("(if #false 1 (if #false 2 3))", "INT 3"),
  ("(if #true #false #true)", "BOOL False"),
  ("(if #true (fun x x) 0)", "FUN [\"x\"]")
]

#eval failingRun ifs
#guard (failingRun ifs).isEmpty

/-! ## Interpreter: let and lexical scoping -/

def scoping : List (String × String) := [
  ("(let x 1 (let x 2 x))", "INT 2"),
  ("(let x 1 (+ (let x 2 x) x))", "INT 3"),
  ("(let x 1 (let y x y))", "INT 1"),
  ("(let x 1 (let x (+ x 1) x))", "INT 2"),
  -- let is not recursive
  ("(let x x 0)", "ERROR 'scope: free variable 'x''"),
  ("(let f (fun n (app f n)) (app f 1))", "ERROR 'scope: free variable 'f''"),
  -- lexical, not dynamic, scope
  ("(let y 10 (let f (fun x (+ x y)) (let y 20 (app f 1))))", "INT 11"),
  ("(let g (fun y z) (let z 5 (app g 1)))", "ERROR 'scope: free variable 'z''"),
  ("(let x 1 (let f (fun y (+ x y)) (let x 100 (app f 1))))", "INT 2"),
  -- closures escape their defining call
  ("(let mk (fun a (fun b (+ a b))) (app (app mk 1) 2))", "INT 3"),
  ("(let mk (fun a (fun b (+ a b))) (let add5 (app mk 5) (+ (app add5 1) (app add5 2))))", "INT 13"),
  ("(let mk (fun a (fun b (fun c (+ a (+ b c))))) (app (app (app mk 1) 2) 3))", "INT 6"),
  ("(let twice (fun f (fun x (app f (app f x)))) (app (app twice (fun n (+ n 3))) 10))", "INT 16"),
  ("(let compose (fun f g (fun x (app f (app g x)))) (app (app compose (fun a (* a 2)) (fun b (+ b 1))) 5))", "INT 12"),
  -- parameters shadow captured variables
  ("(let x 1 (app (fun x x) 2))", "INT 2"),
  ("(let x 1 (app (fun y (+ y x)) (+ x 10)))", "INT 12"),
  ("(app (fun x (let x (+ x 1) x)) 1)", "INT 2"),
  ("(app (fun x (app (fun x x) 5)) 1)", "INT 5"),
  ("(app (fun x (+ x (app (fun x x) 5))) 1)", "INT 6"),
  -- arguments evaluate in the caller's environment
  ("(let x 1 (app (fun x y (+ x y)) 10 x))", "INT 11"),
  -- a closure keeps its own copy of a shadowed binding
  ("(let x 1 (let f (fun u x) (let x 2 (+ (app f 0) x))))", "INT 3"),
  -- functions are first-class values
  ("(let f (fun x x) (app f f))", "FUN [\"x\"]"),
  ("(app (app (fun f f) (fun x (+ x 1))) 1)", "INT 2"),
  ("(app (if #true (fun x (+ x 1)) (fun x (- x 1))) 5)", "INT 6"),
  -- recursion by self-application
  ("(let w (fun x (app x x)) (app w (fun x 7)))", "INT 7"),
  -- Z combinator: factorial
  ("(let z (fun f (app (fun x (app f (fun v (app (app x x) v)))) (fun x (app f (fun v (app (app x x) v))))))
      (let fact (app z (fun self (fun n (if (< n 1) 1 (* n (app self (- n 1)))))))
        (app fact 5)))", "INT 120"),
  ("(let z (fun f (app (fun x (app f (fun v (app (app x x) v)))) (fun x (app f (fun v (app (app x x) v))))))
      (let fib (app z (fun self (fun n (if (< n 2) n (+ (app self (- n 1)) (app self (- n 2)))))))
        (app fib 15)))", "INT 610")
]

#eval failingRun scoping
#guard (failingRun scoping).isEmpty

/-! ## Interpreter: application -/

def apps : List (String × String) := [
  ("(app 1 2)", "ERROR 'type: expected a function'"),
  ("(app #true 2)", "ERROR 'type: expected a function'"),
  ("(app (con A) 2)", "ERROR 'type: expected a function'"),
  ("(app (con A))", "ERROR 'type: expected a function'"),
  ("(app (fun x x))", "ERROR 'arity: function expects 1 arguments, got 0'"),
  ("(app (fun x x) 1 2)", "ERROR 'arity: function expects 1 arguments, got 2'"),
  ("(app (fun x y 0) 1)", "ERROR 'arity: function expects 2 arguments, got 1'"),
  ("(app (fun x y z 0))", "ERROR 'arity: function expects 3 arguments, got 0'"),
  ("(let f (fun x x) (app f))", "ERROR 'arity: function expects 1 arguments, got 0'"),
  ("(app (fun x y z (+ x (+ y z))) 1 2 3)", "INT 6"),
  -- the zero-argument call of a parameterless function does not exist: such functions are malformed
  ("(app (fun 7))", "ERROR 'malformed: function has no parameters'"),
  -- arguments of any kind
  ("(app (fun x x) (con A 1))", "CON A"),
  ("(app (fun f (app f 4)) (fun n (* n n)))", "INT 16"),
  ("(app (fun x y (if x y 0)) #true 9)", "INT 9")
]

#eval failingRun apps
#guard (failingRun apps).isEmpty

/-! ## Interpreter: malformed functions and case expressions -/

def malformed : List (String × String) := [
  -- functions
  ("(fun 7)", "ERROR 'malformed: function has no parameters'"),
  ("(fun x)", "ERROR 'malformed: function has no parameters'"),
  ("(fun x x x)", "ERROR 'malformed: duplicate parameter 'x''"),
  ("(fun x y x 1)", "ERROR 'malformed: duplicate parameter 'x''"),
  ("(fun a b c b 1)", "ERROR 'malformed: duplicate parameter 'b''"),
  -- the check fires when the fun expression is evaluated, even if never called
  ("(let f (fun 7) 1)", "ERROR 'malformed: function has no parameters'"),
  ("(let f (fun x x 0) 1)", "ERROR 'malformed: duplicate parameter 'x''"),
  ("(app (fun x x 0) 1 2)", "ERROR 'malformed: duplicate parameter 'x''"),
  ("(+ (fun 1) 2)", "ERROR 'malformed: function has no parameters'"),
  -- ... but not when the fun expression is never evaluated
  ("(if #false (fun 7) 1)", "INT 1"),
  ("(if #true 1 (fun x x 0))", "INT 1"),
  -- case: checked before the scrutinee is evaluated
  ("(case (con A))", "ERROR 'malformed: case has no clauses'"),
  ("(case y)", "ERROR 'malformed: case has no clauses'"),
  ("(case 1)", "ERROR 'malformed: case has no clauses'"),
  ("(case y (A 1) (A 2))", "ERROR 'malformed: duplicate case tag 'A''"),
  ("(case (con A) (A 1) (A 2))", "ERROR 'malformed: duplicate case tag 'A''"),
  ("(case (con A) (A 1) (B 2) (C 3) (B 4))", "ERROR 'malformed: duplicate case tag 'B''"),
  ("(case (con A 1 2) (A x x 1))", "ERROR 'malformed: duplicate variable 'x' in clause 'A''"),
  ("(case y (A x x 1))", "ERROR 'malformed: duplicate variable 'x' in clause 'A''"),
  -- duplicate variables are rejected even in clauses that wouldn't be selected
  ("(case (con A) (A 1) (B x x 2))", "ERROR 'malformed: duplicate variable 'x' in clause 'B''"),
  ("(case (con B 1 2) (A 1) (B x y 2) (C z z 3))", "ERROR 'malformed: duplicate variable 'z' in clause 'C''"),
  -- the same variable in different clauses, or same name as the tag, is fine
  ("(case (con A 1) (A x x) (B x x))", "INT 1"),
  ("(case (con A 1) (A A A))", "INT 1")
]

#eval failingRun malformed
#guard (failingRun malformed).isEmpty

/-! ## Interpreter: constructors and case -/

def cases : List (String × String) := [
  ("(case (con A 1 2) (A a b (+ a b)))", "INT 3"),
  ("(case (con None) (None 0) (Some v v))", "INT 0"),
  ("(case (con Some 7) (None 0) (Some v v))", "INT 7"),
  ("(case (con B) (A 1) (B 2) (C 3))", "INT 2"),
  ("(case (con C) (A 1) (B 2) (C 3))", "INT 3"),
  -- nested constructors
  ("(case (con P 1 (con P 2 3)) (P a b (case b (P c d (+ a (+ c d))))))", "INT 6"),
  ("(case (con L 1 (con L 2 (con Nil))) (L h t (case t (L h2 t2 (+ h h2)) (Nil 0))))", "INT 3"),
  -- fields may be any value
  ("(case (con F (fun x (+ x 1)) 5) (F f n (app f n)))", "INT 6"),
  ("(case (con B #true) (B b (if b 1 2)))", "INT 1"),
  ("(case (con Wrap (con Wrap 4)) (Wrap w w))", "CON Wrap"),
  -- tag is data, not a binding: variables and tags don't interfere
  ("(let A 5 (case (con A 1) (A x (+ x A))))", "INT 6"),
  ("(let None 1 (con None))", "CON None"),
  -- clause variables shadow outer variables; outer variables remain visible
  ("(let x 1 (case (con A 5) (A x x)))", "INT 5"),
  ("(let y 2 (case (con A 5) (A x (+ x y))))", "INT 7"),
  ("(let x 1 (+ (case (con A 5) (A x x)) x))", "INT 6"),
  -- computed scrutinee
  ("(case (if #true (con A) (con B)) (A 1) (B 2))", "INT 1"),
  ("(case (app (fun x (con Box x)) 9) (Box n n))", "INT 9"),
  -- fields are closures too (lexical scope inside con)
  ("(let k 10 (case (con F (fun x (+ x k))) (F f (let k 99 (app f 1)))))", "INT 11"),
  -- failures
  ("(case 1 (A 1))", "ERROR 'type: 'case' scrutinee must be a constructor'"),
  ("(case #true (A 1))", "ERROR 'type: 'case' scrutinee must be a constructor'"),
  ("(case (fun x x) (A 1))", "ERROR 'type: 'case' scrutinee must be a constructor'"),
  ("(case (con A) (B 0))", "ERROR 'match: no clause for tag 'A''"),
  ("(case (con Zed 1) (A 0) (B 1))", "ERROR 'match: no clause for tag 'Zed''"),
  ("(case (con A 1) (A x y 0))",
   "ERROR 'arity: clause 'A' binds 2 variables but the constructor has 1 fields'"),
  ("(case (con A 1 2) (A x 0))",
   "ERROR 'arity: clause 'A' binds 1 variables but the constructor has 2 fields'"),
  ("(case (con A) (A x 0))",
   "ERROR 'arity: clause 'A' binds 1 variables but the constructor has 0 fields'"),
  ("(case (con A 1) (A 0))",
   "ERROR 'arity: clause 'A' binds 0 variables but the constructor has 1 fields'"),
  -- case-sensitive tags
  ("(case (con a) (A 1))", "ERROR 'match: no clause for tag 'a''"),
  -- the example from the Parser docs now matches a clause
  ("(let x (con iibCon 1 0 #true)
      (case x
        (iiCon a b (+ a b))
        (iibCon thn els cnd (if cnd thn els))))", "INT 1")
]

#eval failingRun cases
#guard (failingRun cases).isEmpty

/-! ## Interpreter: parse errors surface through `run` -/

#guard run "(f 3)" == "ParseError: unknown form 'f'"
#guard run "(+ 1 2" == "ParseError: missing ')'"
#guard run "(rec f n n)" == "ParseError: unknown form 'rec'"

/-! ## Fuel: only `app` consumes it, and it bounds call depth -/

def fuelCases : List (Nat × String × String) := [
  -- no calls: fuel is irrelevant, however deep the syntax is
  (0, "(+ (+ (+ (+ 1 2) 3) 4) 5)", "INT 15"),
  (0, "(let x 1 (let y 2 (if #true (+ x y) 0)))", "INT 3"),
  (0, "x", "ERROR 'scope: free variable 'x''"),
  (0, "(case (con A 1) (A x x))", "INT 1"),
  (0, "(fun x x)", "FUN [\"x\"]"),
  -- one call needs fuel 1
  (0, "(app (fun x x) 1)", "ERROR 'fuel: out of fuel'"),
  (1, "(app (fun x x) 1)", "INT 1"),
  (5, "(app (fun x x) 1)", "INT 1"),
  -- call depth 2
  (1, "(app (fun x (app (fun y y) x)) 1)", "ERROR 'fuel: out of fuel'"),
  (2, "(app (fun x (app (fun y y) x)) 1)", "INT 1"),
  -- call depth 3
  (2, "(app (fun a (app (fun b (app (fun c c) b)) a)) 1)", "ERROR 'fuel: out of fuel'"),
  (3, "(app (fun a (app (fun b (app (fun c c) b)) a)) 1)", "INT 1"),
  -- sequential calls do not accumulate: depth 1 however many
  (1, "(+ (app (fun x x) 1) (+ (app (fun x x) 2) (app (fun x x) 3)))", "INT 6"),
  (1, "(let a (app (fun x x) 1) (let b (app (fun x x) 2) (+ a b)))", "INT 3"),
  (1, "(con P (app (fun x x) 1) (app (fun x x) 2))", "CON P"),
  -- arguments are evaluated at the caller's fuel, the body at fuel - 1
  (1, "(app (fun x x) (app (fun y y) 1))", "INT 1"),
  (2, "(app (fun x (app (fun y y) x)) (app (fun z z) 1))", "INT 1"),
  -- a call in an unchosen branch costs nothing
  (0, "(if #true 1 (app (fun x x) 1))", "INT 1"),
  -- the callee's body is where fuel is spent
  (1, "(let f (fun x x) (app f 1))", "INT 1"),
  (1, "(let f (fun x (app (fun y y) x)) (app f 1))", "ERROR 'fuel: out of fuel'"),
  -- fuel checks come after the type and arity checks
  (0, "(app 1 2)", "ERROR 'type: expected a function'"),
  (0, "(app (fun x x))", "ERROR 'arity: function expects 1 arguments, got 0'"),
  -- error arguments are reported before the fuel check
  (0, "(app (fun x x) y)", "ERROR 'scope: free variable 'y''"),
  -- a diverging program ends with the fuel error
  (10, "(let w (fun x (app x x)) (app w w))", "ERROR 'fuel: out of fuel'"),
  (10000, "(let w (fun x (app x x)) (app w w))", "ERROR 'fuel: out of fuel'"),
  (0, "(let w (fun x (app x x)) w)", "FUN [\"x\"]")
]

#eval fuelCases.filter fun (n, s, exp) => runf n s != exp
#guard (fuelCases.filter fun (n, s, exp) => runf n s != exp).isEmpty

/-- `run` uses the default fuel (10000): a ~1000-deep recursion fits, runaway recursion doesn't. -/
def countdown (n : Nat) : String :=
  s!"(let z (fun f (app (fun x (app f (fun v (app (app x x) v)))) (fun x (app f (fun v (app (app x x) v))))))
      (let down (app z (fun self (fun n (if (< n 1) 0 (+ 1 (app self (- n 1)))))))
        (app down {n})))"

#guard run (countdown 0) == "INT 0"
#guard run (countdown 100) == "INT 100"
#guard run (countdown 1000) == "INT 1000"
#guard runf 100 (countdown 1000) == "ERROR 'fuel: out of fuel'"
#guard runf 100000 (countdown 5000) == "INT 5000"

/-! ## Hand-built `Expr`s: any `Expr` is a meaningful program -/

-- Reserved words and arbitrary strings are accepted as names by the interpreter.
#guard evalExpr (.lett "let" (.int 1) (.ref "let")) == "INT 1"
#guard evalExpr (.lett "x y" (.int 1) (.ref "x y")) == "INT 1"
#guard evalExpr (.ref "if") == "ERROR 'scope: free variable 'if''"
#guard evalExpr (.app (.fn ["+"] (.ref "+")) [.int 4]) == "INT 4"
#guard evalExpr (.case (.con "fun" [.int 1]) [⟨"fun", ["+"], .ref "+"⟩]) == "INT 1"
-- Malformed hand-built forms are errors, not crashes.
#guard evalExpr (.fn [] (.int 1)) == "ERROR 'malformed: function has no parameters'"
#guard evalExpr (.fn ["x", "x"] (.int 1)) == "ERROR 'malformed: duplicate parameter 'x''"
#guard evalExpr (.case (.int 1) []) == "ERROR 'malformed: case has no clauses'"
#guard evalExpr (.case (.int 1) [⟨"A", [], .int 1⟩, ⟨"A", [], .int 2⟩])
  == "ERROR 'malformed: duplicate case tag 'A''"
#guard evalExpr (.case (.con "A" []) [⟨"A", ["x", "x"], .int 1⟩])
  == "ERROR 'malformed: duplicate variable 'x' in clause 'A''"
#guard evalExpr (.app (.fn ["x"] (.ref "x")) []) == "ERROR 'arity: function expects 1 arguments, got 0'"
#guard evalExpr (.app (.fn ["x"] (.ref "x")) [.int 1, .int 2])
  == "ERROR 'arity: function expects 1 arguments, got 2'"
#guard evalExpr (.binop .div (.int 1) (.int 0)) == "ERROR 'arith: division by zero'"
#guard evalExpr (.binop .eq (.con "A" []) (.con "A" [])) == "ERROR 'type: '==' needs two ints or two bools'"
-- The fuel parameter of `interpf`.
#guard evalExprF 0 (.app (.fn ["x"] (.ref "x")) [.int 1]) == "ERROR 'fuel: out of fuel'"
#guard evalExprF 1 (.app (.fn ["x"] (.ref "x")) [.int 1]) == "INT 1"

/-! ## Environments (closures hold only non-error values) -/

#guard (env_insert [] "x" (.int 1)).isSome
#guard (env_insert [] "x" (.error "boom")).isNone
#guard (env_extend [] ["x", "y"] [.int 1, .int 2]).isSome
#guard (env_extend [] ["x"] [.int 1, .int 2]).isNone
#guard (env_extend [] ["x", "y"] [.int 1]).isNone
#guard (env_extend [] ["x"] [.error "e"]).isNone
#guard match env_extend [("x", .int 1)] ["x"] [.int 2] with
  | some env => match env_lookup env "x" with
    | some (.int 2) => true
    | _ => false
  | none => false
#guard (env_lookup [] "x").isNone

/-! ## combine helpers -/

#guard (combineErrs []).isNone
#guard (combineErrs [.int 1, .bool true]).isNone
#guard match combineErrs [.int 1, .error "a", .int 2] with | some (.error "a") => true | _ => false
#guard match combineErrs [.error "a", .error "b"] with | some (.error "[ a | b ]") => true | _ => false
#guard match combineErrs [.error "a", .int 0, .error "b", .error "c"] with
  | some (.error "[ [ a | b ] | c ]") => true | _ => false
#guard firstDuplicate ["a", "b", "c"] == none
#guard firstDuplicate ["a", "b", "a"] == some "a"
#guard firstDuplicate ["a", "b", "b", "a"] == some "a"
#guard firstDuplicate [] == none
