import Fixpoint.SimpLang.Interpreter

/-!
# Monadic interpreter for SimpLang

A monadic rewrite of `Interpreter.lean`, observationally equal to it (see `MonadicTests.lean`).
The analysis and rationale are in `MonadicInterpreterAnalysis.md`. In short:

* `Env` is the environment of a `ReaderT`; `let`, clause binding and calls use `withReader`.
* Errors are thrown in `Except Value` (the thrown value is always a `Value.error`), so the
  absorbing, short-circuiting constructs (`let`, `if`, `case`, ...) are plain `do` sequencing.
* The constructs whose siblings are *all* evaluated and whose errors are combined
  (operands, call, constructor) are not monadic sequencing, they are error *accumulation*;
  see `attempt` / `collect`.
* Fuel stays an explicit argument: it is the termination measure, and it must be *decreased*
  across calls, which is not something a reader/state hides from the termination checker.

Everything in `Interpreter.lean` that is already pure (`err`, `checkFn`, `checkCase`,
`evalBinop`, ...) is reused unchanged.
-/

namespace Monadic

/-- The evaluation monad: read the environment, or throw an error `Value`. -/
abbrev Eval := ReaderT Env (Except Value)

/-- Throw `"<cat>: <detail>"`. -/
def throwErr (cat detail : String) : Eval α := throw (err cat detail)

/-- Re-enter a pure `Value` that may be an error: errors are thrown, others returned. -/
def ofValue : Value → Eval Value
  | .error d => throw (.error d)
  | v => pure v

/-- Throw the error of a static check, if it failed. -/
def orThrow : Option Value → Eval Unit
  | some e => throw e
  | none => pure ()

/-- Run `m` without letting its error escape: capture the result. Never throws. -/
def attempt (m : Eval α) : Eval (Except Value α) := fun env => pure (m.run env)

/-- Pair two captured results, combining both errors if both failed. -/
def collect2 : Except Value α → Except Value β → Except Value (α × β)
  | .ok a, .ok b => .ok (a, b)
  | .error e, .ok _ => .error e
  | .ok _, .error e => .error e
  | .error e₁, .error e₂ => .error (combine_err e₁ e₂)

/-- Collect captured results: the values, or all errors combined left to right
(`combine_err` is left-nested, matching `combineErrs`). -/
def collect (rs : List (Except Value α)) : Except Value (List α) :=
  rs.foldl (fun acc r => (collect2 acc r).map fun (vs, v) => vs ++ [v]) (.ok [])

/-- Look up a variable. -/
def lookup (x : Symbol) : Eval Value := do
  match env_lookup (← read) x with
  | none => throwErr "scope" s!"free variable '{x}'"
  | some v => pure v

/-- Extend an environment, as in the original interpreter. -/
def extend (env : Env) (xs : List Symbol) (vs : List Value) : Eval Env :=
  match env_extend env xs vs with
  | none => throwErr "internal" "invalid environment extension"
  | some env' => pure env'

mutual
  /-- Evaluate `e`. Fuel is consumed only by applications. -/
  def eval (fuel : Nat) (e : Expr) : Eval Value :=
    match e with
    | .int n => pure (.int n)
    | .bool b => pure (.bool b)
    | .ref x => lookup x
    | .binop op l r => do
      let lr ← attempt (eval fuel l)
      let rr ← attempt (eval fuel r)
      let (lv, rv) ← liftM (collect2 lr rr)
      ofValue (evalBinop op lv rv)
    | .iff c t el => do
      match ← eval fuel c with
      | .bool true => eval fuel t
      | .bool false => eval fuel el
      | _ => throwErr "type" "'if' condition must be a bool"
    | .lett x rhs body => do
      let v ← eval fuel rhs
      withReader (fun env => (x, v) :: env) (eval fuel body)
    | .fn params body => do
      orThrow (checkFn params)
      return .fn params body (← read)
    | .app f args => do
      let fr ← attempt (eval fuel f)
      let ars ← evalList fuel args
      match ← liftM (collect (fr :: ars)) with
      | .fn params body cenv :: avs =>
        if params.length != avs.length then
          throwErr "arity" s!"function expects {params.length} arguments, got {avs.length}"
        else
          match fuel with
          | 0 => throwErr "fuel" "out of fuel"
          | k + 1 => do
            let env' ← extend cenv params avs
            withReader (fun _ => env') (eval k body)
      | _ => throwErr "type" "expected a function"
    | .con tag args => do
      let vs ← liftM (collect (← evalList fuel args))
      return .con tag vs
    | .case scrut clauses => do
      orThrow (checkCase clauses)
      match ← eval fuel scrut with
      | .con tag fields => evalClauses fuel tag fields clauses
      | _ => throwErr "type" "'case' scrutinee must be a constructor"
  termination_by (fuel, sizeOf e)

  /-- Evaluate a list of expressions left to right, capturing each result (never throws). -/
  def evalList (fuel : Nat) (es : List Expr) : Eval (List (Except Value Value)) :=
    match es with
    | [] => pure []
    | e :: es => do
      let r ← attempt (eval fuel e)
      let rs ← evalList fuel es
      pure (r :: rs)
  termination_by (fuel, sizeOf es)

  /-- Select the clause for `tag` and evaluate its body with the fields bound. -/
  def evalClauses (fuel : Nat) (tag : Symbol) (fields : List Value)
      (cs : List Clause) : Eval Value :=
    match cs with
    | [] => throwErr "match" s!"no clause for tag '{tag}'"
    | ⟨ctag, vars, body⟩ :: cs =>
      if ctag == tag then
        if vars.length != fields.length then
          throwErr "arity" s!"clause '{ctag}' binds {vars.length} variables but the constructor has {fields.length} fields"
        else do
          let env' ← extend (← read) vars fields
          withReader (fun _ => env') (eval fuel body)
      else evalClauses fuel tag fields cs
  termination_by (fuel, sizeOf cs)
end

/-- Run an evaluation: the final value, or the (error) value that was thrown. -/
def runEval (m : Eval Value) (env : Env := []) : Value :=
  match m.run env with
  | .ok v => v
  | .error d => d

/-- Evaluate in the empty environment with the given call-depth fuel. -/
def interpf (fuel : Nat) (e : Expr) : Value := runEval (eval fuel e)
def interp := interpf 10000

end Monadic
