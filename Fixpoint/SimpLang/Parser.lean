import Fixpoint.SimpLang.Defs

/-!
# S-expression parser for SimpLang

Pipeline: `String` → (tokenize) → `List String` → (parseSExpr) → `SExpr` → (toExpr) → `Expr`

The parser checks *syntax only*; everything else (arity of functions, duplicate names, empty
`case`, types, scoping) is the interpreter's job. See `LangSpec.md` for the full language
specification; the concrete syntax is summarized here.

## Concrete syntax

1. **Whitespace is insignificant** and only separates tokens.
2. **Comments**: `;` starts a comment running to the end of the line (even mid-atom: `x;y` is `x`).
3. **Parentheses are mandatory** and are tokens on their own. No implicit grouping, infix,
   implicit application, or bracket variants.
4. **Atoms** are maximal runs of characters that are not whitespace, parentheses, or `;`.
   An atom is read as the first of these that matches:
   * `#true` / `#false` → `Expr.bool`;
   * an integer `-? digit+` → `Expr.int`. Anything else starting with a digit, or with `-`
     followed by a digit, is a "malformed integer" error;
   * any other atom starting with `#` is an error;
   * a reserved word is an error (it is not a variable);
   * a **name** `[A-Za-z_][A-Za-z0-9_]*` → `Expr.ref`;
   * anything else is an "invalid name" error (e.g. `+7`, `-x`, `a-b`).
5. **Reserved words**: `let if fun app con case + - * / % < ==`. They can't be variable,
   parameter, or tag names.
6. **A list's first element selects the form** and must be a bare reserved atom; `()` is an error.
   Application is always `(app f 3)`, never `(f 3)`.

### Forms

| Syntax                           | Produces                                   |
|----------------------------------|--------------------------------------------|
| `n`, `#true`, `#false`, `x`      | `int`, `bool`, `ref`                       |
| `(op a b)`, op ∈ `+ - * / % < ==`| `binop add/sub/mul/div/mod/lt/eq a b`      |
| `(if c t e)`                     | `iff`; exactly three subexpressions        |
| `(let x rhs body)`               | `lett`; `x` a name                         |
| `(fun p1 ... pn body)`           | `fn [p1..pn] body`; n ≥ 0 parses           |
| `(app f a1 ... an)`              | `app f [a1..an]`; n ≥ 0                    |
| `(con Tag a1 ... an)`            | `con Tag [a1..an]`; n ≥ 0                  |
| `(case s clause ...)`            | `case s [clauses]`; zero clauses parses    |
| clause: `(Tag v1 ... vn body)`   | `Clause Tag [v1..vn] body`                 |

In `fun` and clauses, the **last** element is the body and everything before it (after the head
or tag) is a parameter. A form with no body is an error. Zero-parameter functions, empty `case`,
duplicate parameters / clause variables / tags, and `(app f)` all parse; the interpreter rejects
them. Errors are `Except.error msg`; the parser never panics. Trailing input after the first
complete expression is an error.
-/
/-- Raw S-expression: either an atom or a (possibly empty) list. Stage 2 output. -/
inductive SExpr
  | atom (s : String)
  | list (xs : List SExpr)

/-! ## Stage 1: tokenizer -/

/-- `(` and `)` are always tokens by themselves; whitespace only separates tokens; `;` starts a
comment that runs to the end of the line (`inComment` is true while skipping it). -/
private def tokenizeGo : List Char → List Char → List String → Bool → List String
  | [], cur, acc, _ => (flush cur acc).reverse
  | c :: cs, _, acc, true =>
    tokenizeGo cs [] acc (c != '\n')
  | c :: cs, cur, acc, false =>
    if c == ';' then
      tokenizeGo cs [] (flush cur acc) true
    else if c == '(' || c == ')' then
      tokenizeGo cs [] (c.toString :: flush cur acc) false
    else if c.isWhitespace then
      tokenizeGo cs [] (flush cur acc) false
    else
      tokenizeGo cs (c :: cur) acc false
where
  /-- Finish the atom being accumulated (stored reversed), if any. -/
  flush (cur : List Char) (acc : List String) : List String :=
    if cur.isEmpty then acc else String.ofList cur.reverse :: acc

/-- `tokenize "(+ 1  2) ; hi" = ["(", "+", "1", "2", ")"]` -/
def tokenize (s : String) : List String := tokenizeGo s.toList [] [] false

/-! ## Stage 2: tokens → `SExpr` -/

mutual
  /-- Parse one S-expression, returning it and the unconsumed tokens.
  The subtype records that at least one token is consumed, which is what makes
  the recursion terminate. -/
  def parseSExpr : (toks : List String) →
      Except String {r : SExpr × List String // r.2.length < toks.length}
    | [] => .error "unexpected end of input"
    | ")" :: _ => .error "unexpected ')'"
    | "(" :: rest => do
      let ⟨r, h⟩ ← parseItems rest []
      pure ⟨r, by simp only [List.length_cons]; omega⟩
    | a :: rest => .ok ⟨(.atom a, rest), by simp⟩
  termination_by toks => (toks.length, 0)

  /-- Parse list elements until the matching `)`. `acc` holds elements so far, reversed. -/
  def parseItems : (toks : List String) → (acc : List SExpr) →
      Except String {r : SExpr × List String // r.2.length < toks.length}
    | [], _ => .error "missing ')'"
    | ")" :: rest, acc => .ok ⟨(.list acc.reverse, rest), by simp⟩
    | t :: ts, acc => do
      let ⟨(x, rest), h⟩ ← parseSExpr (t :: ts)
      let ⟨r, h'⟩ ← parseItems rest (x :: acc)
      pure ⟨r, by simp only [List.length_cons] at h ⊢; omega⟩
  termination_by toks _ => (toks.length, 1)
end

/-! ## Stage 3: `SExpr` → `Expr` -/

/-- Words that can't be used as names. -/
def reserved : List String :=
  ["let", "if", "fun", "app", "con", "case", "+", "-", "*", "/", "%", "<", "=="]

/-- Does this atom look like it was meant to be an integer? -/
def numLike (a : String) : Bool :=
  match a.toList with
  | c :: _ => c.isDigit || (c == '-' && (a.toList.drop 1).head?.any Char.isDigit)
  | [] => false

/-- `-? digit+` -/
def isIntLit (a : String) : Bool :=
  let ds := if a.startsWith "-" then a.toList.drop 1 else a.toList
  !ds.isEmpty && ds.all Char.isDigit

/-- `[A-Za-z_][A-Za-z0-9_]*` -/
def isNameShape (a : String) : Bool :=
  match a.toList with
  | c :: cs => (c.isAlpha || c == '_') && cs.all (fun d => d.isAlphanum || d == '_')
  | [] => false

/-- A legal name: well-shaped and not reserved. -/
def isSymbol (a : String) : Bool := isNameShape a && !reserved.contains a

def asSymbol : SExpr → Except String Symbol
  | .atom a => if isSymbol a then .ok a else .error s!"invalid name '{a}'"
  | .list _ => .error "expected a name, found a list"

/-- Split off the last element: `[a, b, c] ↦ ([a, b], c)`; `none` for `[]`. -/
def splitLast {α} (xs : List α) : Option (List α × α) :=
  match xs.reverse with
  | [] => none
  | l :: r => some (r.reverse, l)

theorem splitLast_snd_mem {α} {xs : List α} {r : List α × α}
    (h : splitLast xs = some r) : r.2 ∈ xs := by
  unfold splitLast at h
  cases hr : xs.reverse with
  | nil => simp [hr] at h
  | cons l r' =>
    simp [hr] at h
    subst h
    have : l ∈ xs.reverse := by simp [hr]
    simpa using this

def primOf : String → Option Prim
  | "+" => some .add
  | "-" => some .sub
  | "*" => some .mul
  | "/" => some .div
  | "%" => some .mod
  | "<" => some .lt
  | "==" => some .eq
  | _ => none

/-- Parse a bare atom: boolean, integer, or variable reference. -/
def atomToExpr (a : String) : Except String Expr :=
  if a == "#true" then .ok (.bool true)
  else if a == "#false" then .ok (.bool false)
  else if isIntLit a then
    match a.toInt? with
    | some n => .ok (.int n)
    | none => .error s!"malformed integer '{a}'"
  else if numLike a then .error s!"malformed integer '{a}'"
  else if a.startsWith "#" then .error s!"unknown '#' literal '{a}'"
  else if reserved.contains a then .error s!"'{a}' is reserved and can't be used as a variable"
  else if isNameShape a then .ok (.ref a)
  else .error s!"invalid name '{a}'"

mutual
  def toExpr : SExpr → Except String Expr
    | .atom a => atomToExpr a
    | .list [] => .error "empty list '()'"
    | .list (.list _ :: _) => .error "the head of a list must be a keyword (use 'app' to apply)"
    | .list (.atom h :: args) =>
      match h, args with
      | "if", [c, t, e] => do return .iff (← toExpr c) (← toExpr t) (← toExpr e)
      | "if", _ => .error "'if' takes exactly 3 subexpressions"
      | "let", [x, rhs, body] => do return .lett (← asSymbol x) (← toExpr rhs) (← toExpr body)
      | "let", _ => .error "'let' takes a name, a right-hand side, and a body"
      | "fun", as => do
        let ⟨(params, body), _hb⟩ ← bodyAfter "fun" as
        return .fn (← params.mapM asSymbol) (← toExpr body)
      | "app", f :: as => do return .app (← toExpr f) (← as.mapM toExpr)
      | "app", [] => .error "'app' needs a function"
      | "con", tag :: as => do return .con (← asSymbol tag) (← as.mapM toExpr)
      | "con", [] => .error "'con' needs a tag"
      | "case", s :: cs => do return .case (← toExpr s) (← cs.mapM toClause)
      | "case", [] => .error "'case' needs a scrutinee"
      | op, as =>
        match primOf op with
        | none => .error s!"unknown form '{op}'"
        | some p =>
          match as with
          | [a, b] => do return .binop p (← toExpr a) (← toExpr b)
          | _ => .error s!"'{op}' takes exactly 2 arguments"
  termination_by x => sizeOf x
  decreasing_by
    all_goals
      simp_wf
      first
      | omega
      | (have := List.sizeOf_lt_of_mem (by assumption); (try simp only at *); omega)

  /-- `(Tag v1 ... vn body)` -/
  def toClause : SExpr → Except String Clause
    | .list (tag :: rest) => do
      let ⟨(vars, body), _hb⟩ ← bodyAfter "case clause" rest
      return ⟨← asSymbol tag, ← vars.mapM asSymbol, ← toExpr body⟩
    | _ => .error "a case clause must be a non-empty list '(Tag vars... body)'"
  termination_by x => sizeOf x
  decreasing_by
    all_goals
      simp_wf
      first
      | omega
      | (have := List.sizeOf_lt_of_mem (by assumption); (try simp only at *); omega)

  /-- Split `xs` into leading parameters and the final body. The subtype records that the body
  is an element of `xs`, which is what makes the recursion on it terminate. -/
  def bodyAfter (what : String) (xs : List SExpr)
      : Except String {r : List SExpr × SExpr // r.2 ∈ xs} :=
    match h : splitLast xs with
    | some r => .ok ⟨r, splitLast_snd_mem h⟩
    | none => .error s!"'{what}' is missing its body"
end

/-- Parse a whole program: exactly one expression, nothing after it. -/
def parse (src : String) : Except String Expr := do
  let ⟨(sx, rest), _⟩ ← parseSExpr (tokenize src)
  unless rest.isEmpty do
    throw s!"unexpected trailing input starting at '{rest.head!}'"
  toExpr sx

/-! ## Printing and examples -/

/-- Print an `Expr` back in canonical single-line syntax (used to check the parser). -/
partial def showExpr : Expr → String
  | .int n => toString n
  | .bool b => if b then "#true" else "#false"
  | .ref x => x
  | .binop op l r => s!"({op.sym} {showExpr l} {showExpr r})"
  | .iff c t e => s!"(if {showExpr c} {showExpr t} {showExpr e})"
  | .lett x r b => s!"(let {x} {showExpr r} {showExpr b})"
  | .fn ps b => s!"(fun {" ".intercalate (ps ++ [showExpr b])})"
  | .app f as => s!"(app {" ".intercalate (showExpr f :: as.map showExpr)})"
  | .con t as => s!"(con {" ".intercalate (t :: as.map showExpr)})"
  | .case s cs =>
    let cl := cs.map fun c => s!"({" ".intercalate (c.tag :: c.vars ++ [showExpr c.body])})"
    s!"(case {" ".intercalate (showExpr s :: cl)})"

def tryParse (src : String) : String :=
  match parse src with
  | .ok e => showExpr e
  | .error m => s!"ParseError: {m}"

-- Layout is irrelevant:
#eval tryParse "(let x 0\n   (+ x 1))"             -- (let x 0 (+ x 1))
#eval tryParse "  ( let   x\t0 (+\nx\n1 ) )  "      -- (let x 0 (+ x 1))
#eval tryParse "(let f (fun x (+ x 1)) (app f 3))"  -- (let f (fun x (+ x 1)) (app f 3))
#eval tryParse "(app (fun x (+ x 1)) 3)"
#eval tryParse "(if (if #true #true #false) 1 0)"
#eval tryParse "(+ -3 4)"                           -- negative literal vs. `-` operator
#eval tryParse "(fun 7)"                            -- parses; the interpreter rejects it
#eval tryParse "(+ 1 ; one\n 2)"                    -- comment
#eval tryParse
  "(let x (con iibCon 1 0 #true)
     (case x
       (iiCon a b
         (+ a b))
       (iibCon thn els cnd
         (if cnd thn els))))"

-- Errors:
#eval tryParse "(x + 1)"          -- unknown form 'x'
#eval tryParse "(f 3)"            -- unknown form 'f'
#eval tryParse "((fun x x) 3)"    -- head must be a keyword
#eval tryParse "(if #true 1)"     -- 'if' takes exactly 3 subexpressions
#eval tryParse "(+ 1 2 3)"        -- '+' takes exactly 2 arguments
#eval tryParse "(let if 1 2)"     -- invalid name 'if'
#eval tryParse "12abc"            -- malformed integer
#eval tryParse "+7"               -- invalid name
#eval tryParse "#maybe"           -- unknown '#' literal
#eval tryParse "(+ 1 2"           -- missing ')'
#eval tryParse "(+ 1 2))"         -- trailing input
#eval tryParse "()"               -- empty list
#eval tryParse "x y"              -- trailing input
