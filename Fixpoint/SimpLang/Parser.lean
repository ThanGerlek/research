import Fixpoint.SimpLang.Defs

/-!
# S-expression parser for SimpLang

Pipeline: `String` → (tokenize) → `List String` → (parseSExpr) → `SExpr` → (toExpr) → `Expr`

Splitting into three stages keeps each decision small and independently testable.

## Concrete syntax (every decision, with examples)

1. **Whitespace is insignificant.** Spaces, tabs, and newlines all just separate tokens, and any
   amount of them is the same as one space. Indent however you like.
   `"(+ 1 2)"` = `"(  +\n   1\n\t2 )"`.

2. **Parentheses are mandatory** and are the only structure. `(` and `)` are tokens on their own,
   so no whitespace is needed around them: `"(+ (+ 1 2) 3)"`. There is no implicit grouping,
   no infix, no implicit application, and no bracket variants like `[ ]`.

3. **Atoms** are maximal runs of characters that are not whitespace or parentheses.
   An atom is read as the first of these that matches:
   * `#true` / `#false`  → `Expr.bool`. (The `#` prefix means a user variable can never clash
     with them; any other atom beginning with `#` is an error.)
   * an integer: optional leading `-`, then digits (`0`, `42`, `-7`) → `Expr.int`.
     Anything starting with a digit, or with `-` followed by a digit, must be a valid integer
     (so `12abc` is an error, not a variable name). `+7` is not an integer.
   * otherwise a **symbol** → `Expr.ref`. Symbols may not be keywords or operators (below).

4. **Keywords and operators are reserved** and can't be used as variable, parameter, tag, or
   self names: `let if fun rec app con case + - * / % < ==`.
   This is so that `(let ...)` is never ambiguous with a variable called `let`.

5. **A list's first element selects the form** and must be a bare reserved atom.
   Any other head (including a list, or a plain variable) is an error. In particular you must
   write `(app f 3)`, never `(f 3)`. The empty list `()` is an error.

6. **No comments** are supported (the lexer has no comment syntax; `;` would just be an atom).

### Forms

| Syntax                           | Produces                                   |
|----------------------------------|--------------------------------------------|
| `n`, `#true`, `#false`, `x`      | `int`, `bool`, `ref`                       |
| `(+ a b)` `(- a b)` `(* a b)`    | `prim add/sub/mul`                         |
| `(/ a b)` `(% a b)`              | `prim div/mod`                             |
| `(< a b)` `(== a b)`             | `prim lt/eq`                               |
| `(if c t e)`                     | `iff`; exactly three subexpressions        |
| `(let x rhs body)`               | `lett`; `x` a symbol                       |
| `(fun p1 ... pn body)`           | `fn none [p1..pn] body`; n ≥ 0             |
| `(rec self p1 ... pn body)`      | `fn (some self) [p1..pn] body`; n ≥ 0      |
| `(app f a1 ... an)`              | `app f [a1..an]`; n ≥ 0                    |
| `(con Tag a1 ... an)`            | `con Tag [a1..an]`; n ≥ 0                  |
| `(case s clause ...)`            | `case s [clauses]`; zero clauses allowed   |
| clause: `(Tag v1 ... vn body)`   | `Clause Tag [v1..vn] body`                 |

Decisions behind the table:
* Primitives are written in prefix form like everything else, and always take exactly two
  arguments (matching what the interpreter's `req_len_2` demands). Equality is `==`, not `=`.
* In `fun`, `rec`, and clauses, the **last** element is the body and everything before it
  (after the head/self/tag) is a parameter. That is why parameters are written flat
  (`(fun x y body)`) rather than in a sub-list; it matches your example `(fun x (+ x 1))`.
  A form with no body (e.g. `(fun)`) is an error.
* `fun` has no self name; the separate `rec` form fills `Expr.fn`'s `self` field. The interpreter
  currently ignores `self`, but the AST has it so the parser can produce it.
* `app` and `con` are explicit keywords (as in your examples) instead of overloading plain lists.
* Duplicate parameters are *not* rejected here: the interpreter already reports them at runtime.
  The parser only checks syntax.
* Errors are `Except.error msg` with a human-readable message; the parser never panics.
  Trailing input after the first complete expression is an error.

### Examples (from the original notes)

```
(let x 0
  (+ x 1))

(let f (fun x (+ x 1))
  (app f 3))

(app (fun x (+ x 1)) 3)

(if (if #true #true #false) 1 0)

(let x (con iibCon 1 0 #true)
  (case x
    (iiCon a b
      (+ a b))
    (biiCon thn els cnd
      (if cnd thn els))))
```
-/

/-- Raw S-expression: either an atom or a (possibly empty) list. Stage 2 output. -/
inductive SExpr
  | atom (s : String)
  | list (xs : List SExpr)

/-! ## Stage 1: tokenizer -/

/-- `(` and `)` are always tokens by themselves; whitespace only separates tokens. -/
private def tokenizeGo : List Char → List Char → List String → List String
  | [], cur, acc => (flush cur acc).reverse
  | c :: cs, cur, acc =>
    if c == '(' || c == ')' then
      tokenizeGo cs [] (c.toString :: flush cur acc)
    else if c.isWhitespace then
      tokenizeGo cs [] (flush cur acc)
    else
      tokenizeGo cs (c :: cur) acc
where
  /-- Finish the atom being accumulated (stored reversed), if any. -/
  flush (cur : List Char) (acc : List String) : List String :=
    if cur.isEmpty then acc else String.ofList cur.reverse :: acc

/-- `tokenize "(+ 1  2)" = ["(", "+", "1", "2", ")"]` -/
def tokenize (s : String) : List String := tokenizeGo s.toList [] []

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

/-- Words that can't be used as names (rule 4). -/
def reserved : List String :=
  ["let", "if", "fun", "rec", "app", "con", "case", "+", "-", "*", "/", "%", "<", "=="]

/-- Does this atom look like it was meant to be an integer (rule 3)? -/
def numLike (a : String) : Bool :=
  match a.toList with
  | c :: _ => c.isDigit || (c == '-' && (a.toList.drop 1).head?.any Char.isDigit)
  | [] => false

/-- A legal name: not reserved, not integer-like, and not a `#...` literal. -/
def isSymbol (a : String) : Bool :=
  !a.isEmpty && !reserved.contains a && !numLike a && !a.startsWith "#"

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
  else if numLike a then
    match a.toInt? with
    | some n => .ok (.int n)
    | none => .error s!"malformed integer '{a}'"
  else if a.startsWith "#" then .error s!"unknown '#' literal '{a}'"
  else if reserved.contains a then .error s!"'{a}' is reserved and can't be used as a variable"
  else .ok (.ref a)

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
        return .fn none (← params.mapM asSymbol) (← toExpr body)
      | "rec", self :: rest => do
        let ⟨(params, body), _hb⟩ ← bodyAfter "rec" rest
        return .fn (some (← asSymbol self)) (← params.mapM asSymbol) (← toExpr body)
      | "rec", [] => .error "'rec' needs a self name"
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
          | [a, b] => do return .prim p [← toExpr a, ← toExpr b]
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

def Prim.sym : Prim → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"
  | .mod => "%" | .lt => "<" | .eq => "=="

/-- Print an `Expr` back in canonical single-line syntax (used to check the parser). -/
partial def showExpr : Expr → String
  | .int n => toString n
  | .bool b => if b then "#true" else "#false"
  | .ref x => x
  | .prim op as => s!"({op.sym} {" ".intercalate (as.map showExpr)})"
  | .iff c t e => s!"(if {showExpr c} {showExpr t} {showExpr e})"
  | .lett x r b => s!"(let {x} {showExpr r} {showExpr b})"
  | .fn none ps b => s!"(fun {" ".intercalate (ps ++ [showExpr b])})"
  | .fn (some s) ps b => s!"(rec {s} {" ".intercalate (ps ++ [showExpr b])})"
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
#eval tryParse "(let x 0\n   (+ x 1))"             -- (let x 0 (+ x 1))
#eval tryParse "  ( let   x\t0 (+\nx\n1 ) )  "      -- (let x 0 (+ x 1))
#eval tryParse "(let f (fun x (+ x 1)) (app f 3))"  -- (let f (fun x (+ x 1)) (app f 3))
#eval tryParse "(app (fun x (+ x 1)) 3)"
#eval tryParse "(if (if #true #true #false) 1 0)"
#eval tryParse "(rec f n (if (< n 1) 0 (app f (- n 1))))"
#eval tryParse "(+ -3 4)"                           -- negative literal vs. `-` operator
#eval tryParse "(fun 7)"                            -- thunk: zero params
#eval tryParse
  "(let x (con iibCon 1 0 #true)
     (case x
       (iiCon a b
         (+ a b))
       (biiCon thn els cnd
         (if cnd thn els))))"

-- Errors:
#eval tryParse "(x + 1)"          -- unknown form 'x'
#eval tryParse "(f 3)"            -- unknown form 'f'
#eval tryParse "((fun x x) 3)"    -- head must be a keyword
#eval tryParse "(if #true 1)"     -- 'if' takes exactly 3 subexpressions
#eval tryParse "(+ 1 2 3)"        -- '+' takes exactly 2 arguments
#eval tryParse "(let if 1 2)"     -- invalid name 'if'
#eval tryParse "12abc"            -- malformed integer
#eval tryParse "#maybe"           -- unknown '#' literal
#eval tryParse "(+ 1 2"           -- missing ')'
#eval tryParse "(+ 1 2))"         -- trailing input
#eval tryParse "()"               -- empty list
#eval tryParse "x y"              -- trailing input
