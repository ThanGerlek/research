import Fixpoint.EZeroCFA_claude.Term

/-!
# Run-time string parser (for the CLI's `--prog`)

String → tokens → `SExp` (Lisp-style cons cells, explicit stack) → `Raw`.
Everything is structurally recursive.  The embedded syntax in `Notation.lean`
is preferred for programs known at build time; this exists only for programs
supplied at run time.
-/

namespace AbsInt

inductive SExp where
  | atom (s : String)
  | nil
  | cons (hd tl : SExp)
  deriving Repr, Inhabited

def SExp.ofList (xs : List SExp) : SExp := xs.foldr SExp.cons SExp.nil

def tokenize (src : String) : List String :=
  go src.toList [] []
where
  flush (cur : List Char) (acc : List String) : List String :=
    if cur.isEmpty then acc else String.ofList cur.reverse :: acc
  go : List Char → List Char → List String → List String
    | [], cur, acc => (flush cur acc).reverse
    | c :: rest, cur, acc =>
      if c = '(' ∨ c = ')' then go rest [] (c.toString :: flush cur acc)
      else if c.isWhitespace then go rest [] (flush cur acc)
      else go rest (c :: cur) acc

/-- `cur`: reversed items of the list being built; `stack`: enclosing lists. -/
def parseTokens : List String → List SExp → List (List SExp) → Except String SExp
  | [], cur, [] =>
    (match cur with
     | [x] => .ok x
     | _ => .error "expected exactly one expression")
  | [], _, _ :: _ => .error "missing ')'"
  | t :: ts, cur, stack =>
    if t = "(" then parseTokens ts [] (cur :: stack)
    else if t = ")" then
      (match stack with
       | [] => .error "unexpected ')'"
       | parent :: rest => parseTokens ts (SExp.ofList cur.reverse :: parent) rest)
    else parseTokens ts (SExp.atom t :: cur) stack

def reserved : List String := ["lambda", "let", "letrec", "if", "input", "+", "-", "*"]

def ArithOp.ofString? : String → Option ArithOp
  | "+" => some .add | "-" => some .sub | "*" => some .mul | _ => none

def SExp.toRaw : SExp → Except String Raw
  | .atom t =>
    (match t.toInt? with
     | some k => .ok (.num k)
     | none => .ok (.var t))
  | .nil => .error "empty application ()"
  | .cons (.atom "lambda") (.cons (.cons (.atom p) .nil) (.cons body .nil)) => do
    pure (.lam p (← body.toRaw))
  | .cons (.atom h) (.cons (.cons (.cons (.atom x) (.cons rhs .nil)) .nil) (.cons body .nil)) => do
    unless h = "let" ∨ h = "letrec" do throw s!"unknown binding form {h}"
    let r ← rhs.toRaw
    let b ← body.toRaw
    pure (if h = "letrec" then .letrec x r b else .letE x r b)
  | .cons (.atom "if") (.cons (.cons (.atom o) (.cons a (.cons b .nil))) (.cons t (.cons e .nil))) => do
    let some cop := CmpOp.ofString? o | throw s!"bad comparison {o}"
    pure (.branch cop (← a.toRaw) (← b.toRaw) (← t.toRaw) (← e.toRaw))
  | .cons (.atom "input") .nil => .ok .input
  | .cons (.atom o) (.cons a (.cons b .nil)) => do
    let some aop := ArithOp.ofString? o | throw s!"unknown operator {o}"
    pure (.arith aop (← a.toRaw) (← b.toRaw))
  | .cons f (.cons a .nil) => do
    if let .atom h := f then
      if reserved.contains h then throw s!"malformed {h} form"
    pure (.app (← f.toRaw) (← a.toRaw))
  | _ => .error "malformed expression"

def parseRaw (src : String) : Except String Raw := do
  let sx ← parseTokens (tokenize src) [] []
  sx.toRaw

end AbsInt
