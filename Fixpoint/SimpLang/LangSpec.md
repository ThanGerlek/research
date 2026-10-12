# SimpLang Language Specification

SimpLang is a small, expression-only, dynamically typed functional language with integers,
booleans, first-class functions with lexical scope, tagged data, and pattern matching on tags.
A program is a single expression.

Implementation layout: `Parser.lean` (text → `Expr`), `Interpreter.lean` (`Expr` → `Value`),
`Defs.lean` (AST, values, environments), `Helpers.lean`.

**Division of labour.** The parser checks _syntax only_. Everything else — arity, duplicate
names, empty forms, types, scoping — is checked by the interpreter, as runtime error values.
Every `Expr` that typechecks in Lean is a meaningful program: the interpreter gives it either a
value or an error value and never gets stuck or panics. The interpreter does not check names
against the reserved-word list (§1), so a hand-built `Expr` may use names the parser could never
produce; printing such an `Expr` with `showExpr` need not round-trip through `parse`.

---

## 1. Lexical structure

- **Whitespace** (space, tab, newline, CR) only separates tokens; amount and kind are irrelevant.
- `(` and `)` are tokens on their own and need no surrounding whitespace.
- **Comments**: a `;` starts a comment that runs to the end of the line. This applies wherever
  the `;` appears, including in the middle of what would otherwise be an atom (`x;y` reads as `x`).
- **Atom**: a maximal run of characters that are not whitespace, parentheses, or `;`.
- There are no strings and no bracket variants (`[ ]`, `{ }`).

### Atom classification

An atom in expression position is classified by the first matching rule:

| Rule                                                                         | Result                                         |
| ---------------------------------------------------------------------------- | ---------------------------------------------- |
| `#true`, `#false`                                                            | boolean literal                                |
| matches `-? digit+`                                                          | integer literal                                |
| starts with a digit, or with `-` followed by a digit (but is not an integer) | parse error "malformed integer"                |
| starts with `#` (anything else)                                              | parse error "unknown '#' literal"              |
| is a reserved word                                                           | parse error (reserved words are not variables) |
| matches `name` (below)                                                       | variable reference                             |
| otherwise                                                                    | parse error "invalid name"                     |

So `12abc` and `-7x` are errors; `-7` is an integer; `-` alone is the subtraction operator;
`+7`, `-x`, `a-b`, and `x?` are errors (not names).

### Names

A **name** matches `[A-Za-z_][A-Za-z0-9_]*` and is not a reserved word. Names are case sensitive.
The same rule applies to variables, parameters, and constructor tags.

### Reserved words

`let if fun app con case + - * / % < ==`

They cannot be used as variable, parameter, or tag names (checked by the parser).

Variables and constructor tags are separate namespaces: tags are never looked up in the
environment, tags are not values (they cannot be bound, passed, or applied), and a variable and a
tag may share a spelling without interfering. A misspelled tag is not a scope error; it surfaces
as a failed case match.

---

## 2. Grammar

```txt
program  ::= expr                      -- exactly one expression, no trailing input

expr     ::= int | bool | name
           | "(" binop expr expr ")"
           | "(" "if"  expr expr expr ")"
           | "(" "let" name expr expr ")"
           | "(" "fun" name* expr ")"            -- last element is the body
           | "(" "app" expr expr* ")"
           | "(" "con" name expr* ")"
           | "(" "case" expr clause* ")"

clause   ::= "(" name name* expr ")"             -- tag, variables, body (last element)

binop    ::= "+" | "-" | "*" | "/" | "%" | "<" | "=="
int      ::= "-"? digit+
bool     ::= "#true" | "#false"
name     ::= [A-Za-z_][A-Za-z0-9_]*   (not a reserved word)
```

Structural rules:

- The head of every list must be a bare reserved atom. `(f 3)`, `((fun x x) 3)`, `()` and
  `(x + 1)` are all parse errors; application is always written `(app f 3)`.
- Binary operators take exactly two operands; `if` takes exactly three; `let` takes exactly a name, a
  right-hand side, and a body.
- In `fun` and in case clauses, the final element is the body and everything between the head
  (or tag) and the body is a parameter/variable. A form with no body is a parse error.
- A case clause must be a non-empty list.
- The following **parse** but are rejected at runtime by the interpreter (§4): `(fun body)` with
  no parameters, `case` with no clauses, duplicate parameters, duplicate clause variables,
  duplicate clause tags, `(app f)` with no arguments (see §4.6).
- `con` with no fields (a nullary constructor) and a clause with no variables are valid.
- Parse errors are reported as `Except.error msg`; the parser never panics.

### Abstract syntax (`Defs.lean`)

```txt
Expr ::= int n | bool b | binop op lhs rhs | iff c t e | ref x | lett x rhs body
       | fn [params] body | app f [args] | con tag [args] | case scrut [Clause]
Clause ::= { tag, vars, body }
Prim ::= add | sub | mul | div | mod | lt | eq
```

Parser mapping: `+ - * / % < ==` → `binop` with `add sub mul div mod lt eq`; `if` → `iff`;
`let` → `lett`; `fun` → `fn`. Fixed arities (binary operators, `if`, `let`) are enforced by the
shape of `Expr`; variable arities (`fn`, `app`, `con`, `case`, clauses) are lists.

---

## 3. Values and environments

```txt
Value ::= int n | bool b | fn params body env | con tag [Value] | error desc
```

- `fn` is a **closure**: parameters, body, and the environment in which the `fn` expression was
  evaluated.
- `con` is a tag plus a list of field values.
- `error` is an ordinary `Value` constructor, not an exception. There is no syntax to create,
  inspect, or catch one. Errors are strict and absorbing (§4.9): a value that contains an error
  is never constructed, so no environment, closure, or constructor field ever holds an error.

An **environment** is a finite map from names to non-error values. The initial environment is
empty. Binding a name that already exists shadows it.

Values print as `INT n`, `BOOL True`/`BOOL False`, `CON tag`, `FUN ["p1", "p2"]` (closures' bodies,
environments, and constructor fields are not printed), and `ERROR 'desc'`.

---

## 4. Evaluation semantics

Evaluation is strict (call-by-value) and lexically scoped. There is no recursive binding form
(`let` is non-recursive and functions have no self name), so recursion is only possible by
self-application.

`interpf fuel e` evaluates `e` in the empty environment with the given fuel; `interp` is
`interpf 10000`.

### 4.1 Fuel

Fuel bounds the **call depth** of a program, so that evaluation is total.

- Only `app` consumes fuel. A call needs fuel ≥ 1; the callee's body is evaluated with fuel − 1.
  All other forms pass their fuel unchanged to their subexpressions, and sibling subexpressions
  each receive the same fuel.
- Calling with fuel 0 yields `fuel: out of fuel`.
- Fuel is independent of how deeply an expression is nested syntactically.
- A program that would diverge (e.g. via self-application) ends with the fuel error.

### 4.2 Literals and variables

- `int n` ⇒ `int n`; `bool b` ⇒ `bool b`.
- `ref x` ⇒ the binding of `x`, or `scope: free variable 'x'` if unbound.

### 4.3 Binary operators

Evaluate both operands, then:

1. If either operand is an error, the result is an error: with one error, that error; with two,
   `combine_err` of the left and right errors (`[ d1 | d2 ]`). The operator is not applied.
2. Otherwise by operator:

| Operator      | Operands                                             | Result                                              |
| ------------- | ---------------------------------------------------- | --------------------------------------------------- |
| `+ - *`       | two `int`                                            | `int`                                               |
| `/` `%`       | two `int`, divisor ≠ 0                               | `int`                                               |
| `/` `%`       | divisor = 0                                          | `arith: division by zero` / `arith: modulo by zero` |
| `<`           | two `int`                                            | `bool`                                              |
| `==`          | two `int` or two `bool`                              | `bool`                                              |
| `+ - * / % <` | anything else                                        | `type: expected int operands for 'op'`              |
| `==`          | anything else (mixed types, functions, constructors) | `type: '==' needs two ints or two bools`            |

Division and modulo use the Euclidean convention (Lean's `Int` `/` and `%`): the remainder is
always in `0 ≤ r < |divisor|` and `a = b * (a / b) + (a % b)`. E.g. `(% -1 5)` = `4`,
`(/ -7 2)` = `-4`, `(% -7 2)` = `1`, `(/ 7 -2)` = `-3`, `(% 7 -2)` = `1`.

### 4.4 `if`

Evaluate the condition. Error ⇒ that error. `bool b` ⇒ evaluate only the chosen branch (its
result is the result of the `if`). Anything else ⇒ `type: 'if' condition must be a bool`.

### 4.5 `let`

`(let x rhs body)`: evaluate `rhs` in the current environment (`x` is **not** in scope in `rhs`).
If it is an error, that error is the result and `body` is not evaluated. Otherwise evaluate `body`
in the current environment extended with `x` bound to the result.

### 4.6 Functions and application

- `(fun p1 … pn body)` is checked, then yields a closure over the current environment:
  - `n = 0` ⇒ `malformed: function has no parameters`;
  - duplicate parameters ⇒ `malformed: duplicate parameter 'p'`.

  The check happens when the `fun` expression is evaluated, not when the function is called.

- `(app f a1 … an)`:
  1. evaluate `f` and every `ai` (all of them, left to right, in the caller's environment);
  2. if any of them is an error, the result is those errors combined left to right with
     `combine_err`; no call is made;
  3. `f` not a closure ⇒ `type: expected a function`;
  4. parameter count ≠ `n` ⇒ `arity: function expects N arguments, got M`
     (so `(app f)` is always an error, since every closure has at least one parameter);
  5. if fuel is 0 ⇒ `fuel: out of fuel`;
  6. evaluate the closure's body in the **closure's** environment extended with the parameters
     bound to the argument values (shadowing), with fuel − 1.

```txt
(let y 10 (let f (fun x (+ x y)) (let y 20 (app f 1))))   ⇒ 11
(let mk (fun a (fun b (+ a b))) (app (app mk 1) 2))       ⇒ 3
```

### 4.7 Constructors

`(con Tag a1 … an)` evaluates every `ai`. If any is an error, the result is those errors
combined left to right with `combine_err`. Otherwise the result is `con Tag [v1 … vn]`.

### 4.8 `case`

`(case s clause…)` — checks first, before `s` is evaluated:

- no clauses ⇒ `malformed: case has no clauses`;
- two clauses with the same tag ⇒ `malformed: duplicate case tag 'T'`;
- duplicate variables in any one clause ⇒ `malformed: duplicate variable 'x' in clause 'T'`.

Then:

1. evaluate `s`; an error is the result; a non-`con` ⇒ `type: 'case' scrutinee must be a constructor`;
2. find the clause whose tag equals the constructor's tag; none ⇒ `match: no clause for tag 'T'`;
3. if the clause's variable count ≠ the constructor's field count ⇒
   `arity: clause 'T' binds N variables but the constructor has M fields`;
4. evaluate the clause body in the current environment extended with the clause variables bound
   to the fields.

Clauses need not be exhaustive (a missed tag is the runtime error above). There is no default or
wildcard clause.

### 4.9 Errors

Errors are strict and absorbing: any construct with an error-valued subexpression whose value
it needs (operands, `let` right-hand side, call function/arguments, constructor fields, `if`
condition, `case` scrutinee) returns that error rather than binding or storing it. When several
independent subexpressions of one construct are errors (operands, call function and arguments,
constructor fields), all are evaluated and their errors are combined left to right with
`combine_err`, preserving all error information. Only the unchosen branch of an `if` and the
unmatched clauses of a `case` are never evaluated.

Every error message has the form `<category>: <detail>`:

| Category    | Messages                                                                                                                                                               |
| ----------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `fuel`      | `out of fuel`                                                                                                                                                          |
| `scope`     | `free variable 'x'`                                                                                                                                                    |
| `type`      | `expected int operands for 'op'`; `'==' needs two ints or two bools`; `'if' condition must be a bool`; `expected a function`; `'case' scrutinee must be a constructor` |
| `arith`     | `division by zero`; `modulo by zero`                                                                                                                                   |
| `arity`     | `function expects N arguments, got M`; `clause 'T' binds N variables but the constructor has M fields`                                                                 |
| `match`     | `no clause for tag 'T'`                                                                                                                                                |
| `malformed` | `function has no parameters`; `duplicate parameter 'p'`; `case has no clauses`; `duplicate case tag 'T'`; `duplicate variable 'x' in clause 'T'`                       |

Combined errors have the form `[ d1 | d2 ]` where `d1`, `d2` are full messages.

---

## 5. Examples

| Program                                                   | Result                                                              |
| --------------------------------------------------------- | ------------------------------------------------------------------- |
| `(let x 0 (+ x 1))`                                       | `INT 1`                                                             |
| `(let f (fun x (+ x 1)) (app f 3))`                       | `INT 4`                                                             |
| `(app (fun x (+ x 1)) 3)`                                 | `INT 4`                                                             |
| `(if (if #true #true #false) 1 0)`                        | `INT 1`                                                             |
| `(+ -3 4)`                                                | `INT 1`                                                             |
| `(% -1 5)`                                                | `INT 4`                                                             |
| `(case (con A 1 2) (A a b (+ a b)))`                      | `INT 3`                                                             |
| `(case (con None) (None 0) (Some v v))`                   | `INT 0`                                                             |
| `(let y 10 (let f (fun x (+ x y)) (let y 20 (app f 1))))` | `INT 11`                                                            |
| `(/ 1 0)`                                                 | `ERROR 'arith: division by zero'`                                   |
| `(== 1 #true)`                                            | `ERROR "type: '==' needs two ints or two bools"`                    |
| `(let x (app 1 2) 5)`                                     | `ERROR 'type: expected a function'`                                 |
| `(case (con A) (B 0))`                                    | `ERROR "match: no clause for tag 'A'"`                              |
| `(case (con A))`                                          | `ERROR 'malformed: case has no clauses'`                            |
| `(app (fun x x))`                                         | `ERROR 'arity: function expects 1 arguments, got 0'`                |
| `(fun 7)`                                                 | `ERROR 'malformed: function has no parameters'`                     |
| `(fun x x x)`                                             | `ERROR "malformed: duplicate parameter 'x'"`                        |
| `(+ y (app 1 2))`                                         | `ERROR "[ scope: free variable 'y' \| type: expected a function ]"` |

Comments: `(+ 1 ; one` followed on the next line by `2)` evaluates to `INT 3`.

Parse errors: `(f 3)`, `(+ 1 2 3)`, `(if #true 1)`, `(let if 1 2)`, `12abc`, `#maybe`, `+7`,
`(+ 1 2`, `(+ 1 2))`, `()`, `x y`.
