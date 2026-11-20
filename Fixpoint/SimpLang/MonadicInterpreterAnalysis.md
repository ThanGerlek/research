# Converting the SimpLang interpreter to monadic style

Companion to `MonadicInterpreter.lean` (the implementation) and `MonadicTests.lean` (differential
tests against `Interpreter.lean`). No existing file was modified.

## 1. What the current interpreter does, as effects

`eval : Nat → Env → Expr → Value` threads three things by hand. Reading them as effects:

| Concern                                | Current encoding                                          | Effect it really is                                                                             |
| -------------------------------------- | --------------------------------------------------------- | ----------------------------------------------------------------------------------------------- |
| Environment `env`                      | extra argument, extended at `let`/call/clause             | **Reader** (with `local`); a call _replaces_ the env with the closure's                         |
| Fuel                                   | extra argument, `k` passed to callee body only on `app`   | Looks like Reader/State, but is really the **termination measure**, decreasing along calls only |
| Errors                                 | `Value.error` returned in-band, matched at every use site | **Exception** — but with a twist (below)                                                        |
| Static checks (`checkFn`, `checkCase`) | `Option Value`, matched                                   | Exception, raised before evaluating anything                                                    |
| Evaluation order                       | `evalList`, left to right                                 | trivial: no state, so order only matters for _which errors_ are collected                       |

There is no mutable state, no I/O, no non-determinism. So the natural stack is small:
**`ReaderT Env (Except Value)`**.

### The twist: error accumulation is _not_ monadic bind

Two kinds of error propagation coexist (LangSpec §4.9):

1. **Short-circuiting / absorbing** — `if` condition, `let` rhs, `case` scrutinee: an error
   stops the construct. This is exactly `Except`'s `>>=`.
2. **Accumulating** — binary operands, call function + arguments, constructor fields: _all_
   siblings are evaluated and all errors combined with `combine_err`, left-nested
   (`[ [ a | b ] | c ]`).

A monad cannot express (2): `bind` of a failed computation never runs the continuation, so the
second sibling's error is never seen. (2) is the **Validation applicative** pattern
(`Validation ε` is an `Applicative` but provably not a lawful `Monad` consistent with its `<*>`).
Any faithful monadic interpreter must therefore mix monadic sequencing (1) with an
applicative/accumulating combinator (2). This is the single most important design point.

## 2. Design chosen

```lean
abbrev Eval := ReaderT Env (Except Value)   -- thrown value is always a Value.error
```

- `Value.error` stays as the _payload_ of `throw` (so `combine_err`, `err` and the printing are
  reused unchanged), but `Eval Value` results are never `.error` — which is the invariant the spec
  states ("no value ever contains an error") and now holds by construction rather than by
  convention.
- `attempt : Eval α → Eval (Except Value α)` runs a sub-evaluation and captures the outcome
  (never throws). `collect2` / `collect` then fold captured outcomes, combining errors left to
  right. Accumulating constructs are "attempt every sibling, then collect"; absorbing constructs
  are plain `do`.
- `withReader` implements scoping. A call uses `withReader (fun _ => env')` (replace, since the
  closure's env, not the caller's, is in scope); `let` uses `fun env => (x,v) :: env`.
- Fuel remains an explicit `Nat` argument (see 3.2).
- The pure helpers (`evalBinop`, `checkFn`, `checkCase`, `env_extend`) are reused; they are
  lifted with `ofValue` / `orThrow` / `extend`.

Resulting size/readability: `eval` loses all `.error d => .error d` boilerplate and the
`env` parameter; the cost is the explicit `attempt`/`collect` in the three accumulating cases.

## 3. Alternatives considered

### 3.1 Error handling

| Option                                                                                      | Verdict                                                                                                                                                                                                                                                                                       |
| ------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **`Except Value`** (chosen)                                                                 | Faithful, simplest, reuses the pure code. Short-circuit semantics for free.                                                                                                                                                                                                                   |
| `Except String` / dedicated `Err` type, convert to `Value.error` at the end                 | Cleaner typing (an `Err` structure with category + detail would stop stringly-typed `"cat: detail"` and make `combine_err` a real `Semigroup`). `combine_err` would need re-expressing; output strings identical if rendered the same. Good follow-up refactor, but changes `Defs`-level API. |
| **A `Validation`-style applicative** as a _separate_ type, `Eval := ReaderT Env Validation` | Gives `<*>` accumulation for free (`(f <$> a <*> b)`), but `bind` then cannot be lawful, and `do`-notation would silently be the wrong thing for `let`/`if`. Hazardous; we keep accumulation explicit instead.                                                                                |
| `ExceptT Value (Reader Env)` (`ExceptT` over `Reader`)                                      | Equivalent here (no state to roll back). Same observable semantics; the order only matters once state exists.                                                                                                                                                                                 |
| Keep errors in-band (`Value.error`) and make `Eval := Reader Env`                           | Minimal change, but retains all the manual matching, which is what we want to get rid of.                                                                                                                                                                                                     |

### 3.2 Fuel

| Option                                               | Verdict                                                                                                                                                                                         |
| ---------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Explicit `Nat` argument** (chosen)                 | Fuel is the termination argument: `termination_by (fuel, sizeOf e)`. Lean sees `k < k+1` structurally. Zero friction.                                                                           |
| Reader of fuel (`ReaderT (Nat × Env)`)               | Reads nicely (`withReader` decrements), but then fuel is invisible to the termination checker: `eval` is no longer provably terminating without `partial` or a fuel-indexed type like `Eval n`. |
| `StateT Nat` fuel as a _step_ counter                | Changes semantics: spec fuel bounds call **depth**, siblings share the same fuel; a state counter would bound total calls. Would be a language change.                                          |
| `partial def` + fuel check at runtime                | Gives up termination and, importantly, the ability to _prove_ things about the interpreter.                                                                                                     |
| Fuel-indexed monad `Eval (n : Nat)` (indexed/graded) | The "correct" typed solution, but needs a custom indexed monad; heavy for little benefit.                                                                                                       |

Implication: because fuel stays a parameter, the interpreter is "monadic in env/errors only."

### 3.3 Environment

- **ReaderT** (chosen): mirrors lexical scope exactly (`local` = scope extension).
- `StateT Env`: wrong — scoping would need manual save/restore and would invite dynamic-scope
  bugs; the spec requires lexical closures.
- Keep env as an explicit argument: possible, but then the monad only handles errors.

### 3.4 Mutual recursion over lists

`List.mapM`/`traverse` would be the idiomatic way to evaluate argument lists, but inside a
`mutual` block with well-founded recursion it makes termination awkward (needs `List.attach`
and a lemma on `sizeOf`). A tiny hand-rolled `evalList` is structural on the list and passes
the termination checker with no obligations. It returns `List (Except Value Value)` (captured
results) rather than failing, because accumulation must see every sibling.

### 3.5 Other monads one _could_ add (not used; semantics don't call for them)

- **`WriterT`/trace**: logging of calls, or collecting _warnings_, for debugging. Free to add
  on top without touching the semantics.
- **`StateT Nat`** (call counter / profiling), as discussed above — a different semantics.
- **`StateT` heap / `IO`**: relevant only if mutable references or I/O are added to the language.
- **CPS / `ContT`**: for `callcc`/exceptions as first-class; unnecessary now (errors are not
  catchable, per spec).
- **Free monad / effect handlers**: the semantic modularity is nice (interpret errors,
  fuel, env separately) but overkill; they also complicate termination proofs.

## 4. Implications

- **Behavioural equality.** Verified by `MonadicTests.lean`: 242 programs from `Tests.lean`
  (all tables + `countdown`), at fuels 0,1,2,3,5,10,100,10000, produce identical printed
  results, and the monadic one also passes the expected-output tables directly.
  Not a proof, but covers every error category and error-combination order.
- **Proof story.** `Eval` is a concrete `def`, so `simp [Eval, ReaderT.run, ...]` can unfold
  it; the simulation lemma `runEval (eval k e) env = Interpreter.eval k env e` (by induction on
  `(fuel, e)`) is feasible. The main work is the `collect` ↔ `combineErrs` correspondence (left
  fold on both sides, so it should be a direct induction). Not done here.
- **Invariant by construction.** Previously, "no `.error` value in an environment" was
  enforced by `env_insert` returning `none`. Now `Eval Value` results only come from `pure`,
  so `lett`'s binding can never be an error; `env_insert`'s "internal" branch becomes
  unreachable. (It is retained via `extend` for fidelity; it could be dropped if `Env` were
  retyped as a subtype of non-error values.)
- **Performance.** `ReaderT` over `Except` compiles to closures; `attempt` allocates an
  `Except` per sibling. Negligible next to the interpretive overhead here; the
  deep-recursion tests (`countdown 1000`) pass. `collect` uses `++ [v]` (quadratic in
  list length) — fine for argument lists, replaceable with an `Array` if lists grow.
- **Stack depth.** Every `bind` is a call frame; deep recursion (fuel 10000) is as deep as
  before, plus a few frames per level. No stack problems observed at the test depths.
- **Extensibility.** New short-circuiting forms are a plain `do`; new accumulating forms use
  `attempt`/`collect`. New effects (trace, state) are `StateT`/`WriterT` layers added to `Eval`
  — the call sites using `read`, `throw`, `withReader` keep working via the `Monad*` classes.
- **Pitfall: `<*>`/`mapM` on `Eval`.** Using them on `Eval` gives _short-circuit_ behaviour,
  not accumulation, and would silently drop errors (the first test with two errors catches it).
  Hence the explicit `collect`.

## 5. Suggested follow-ups

1. Replace string errors with a structure `{cat, detail}` plus a `Semigroup`-like `combine`;
   render to `Value.error` only at the boundary.
2. Prove the simulation lemma above.
3. If accumulating constructs multiply, introduce a small `Validation` applicative locally
   (a `structure`, _not_ a `Monad` instance) to replace `attempt`/`collect2`.
