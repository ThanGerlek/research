import Fixpoint.SimpLang.Helpers
import Fixpoint.SimpLang.Defs

/-!
# Interpreter for SimpLang

See `LangSpec.md` for the language semantics. Summary of the design:

* Every error is a `Value.error` whose message has the form `"<category>: <detail>"`.
* Errors are strict and absorbing; when several independent subexpressions fail, the errors are
  combined left to right with `combine_err`.
* Scoping is lexical: `fn` evaluates to a closure over the current environment.
* Fuel is consumed by function application only; it bounds call depth.
-/

/-- An error value `"<cat>: <detail>"`. -/
def err (cat detail : String) : Value := .error s!"{cat}: {detail}"

/-- Combine the errors among `vs`, left to right; `none` if there are none. -/
def combineErrs (vs : List Value) : Option Value :=
  vs.foldl
    (fun acc v =>
      match v with
      | .error _ =>
        match acc with
        | none => some v
        | some a => some (combine_err a v)
      | _ => acc)
    none

/-- The first element that occurs again later in the list. -/
def firstDuplicate : List Symbol → Option Symbol
  | [] => none
  | x :: xs => if xs.contains x then some x else firstDuplicate xs

/-- Static well-formedness of a `fn`. Returns `some error` if malformed. -/
def checkFn (params : List Symbol) : Option Value :=
  if params.isEmpty then some (err "malformed" "function has no parameters")
  else match firstDuplicate params with
    | some p => some (err "malformed" s!"duplicate parameter '{p}'")
    | none => none

/-- Static well-formedness of a `case`. Returns `some error` if malformed. -/
def checkCase (clauses : List Clause) : Option Value :=
  if clauses.isEmpty then some (err "malformed" "case has no clauses")
  else match firstDuplicate (clauses.map (·.tag)) with
    | some t => some (err "malformed" s!"duplicate case tag '{t}'")
    | none =>
      clauses.findSome? fun c =>
        (firstDuplicate c.vars).map fun x =>
          err "malformed" s!"duplicate variable '{x}' in clause '{c.tag}'"

/-- Apply a binary operator to two already-evaluated operands. -/
def evalBinop (op : Prim) (l r : Value) : Value :=
  match combineErrs [l, r] with
  | some e => e
  | none =>
    match op, l, r with
    | .add, .int n, .int m => .int (n + m)
    | .sub, .int n, .int m => .int (n - m)
    | .mul, .int n, .int m => .int (n * m)
    | .div, .int n, .int m =>
      if m == 0 then err "arith" "division by zero" else .int (n / m)
    | .mod, .int n, .int m =>
      if m == 0 then err "arith" "modulo by zero" else .int (n % m)
    | .lt, .int n, .int m => .bool (n < m)
    | .eq, .int n, .int m => .bool (n == m)
    | .eq, .bool p, .bool q => .bool (p == q)
    | .eq, _, _ => err "type" "'==' needs two ints or two bools"
    | op, _, _ => err "type" s!"expected int operands for '{op.sym}'"

theorem Expr.sizeOf_pos' (e : Expr) : 0 < sizeOf e := by cases e <;> simp +arith

theorem List.sizeOf_pos' {α} [SizeOf α] (l : List α) : 0 < sizeOf l := by cases l <;> simp +arith

mutual
  /-- Interpret `e`. Fuel is consumed only by applications. -/
  def interp_env (fuel : Nat) (env : Env) (e : Expr) : Value :=
    match e with
    | .int n => .int n
    | .bool b => .bool b
    | .binop op l r => evalBinop op (interp_env fuel env l) (interp_env fuel env r)
    | .iff c t el => interp_iff_env fuel env c t el
    | .ref x => interp_ref_env env x
    | .lett x rhs body => interp_lett_env fuel env x rhs body
    | .fn params body => interp_fn_env env params body
    | .app f args => interp_app_env fuel env f args
    | .con tag args => interp_con_env fuel env tag (args)
    | .case scrut clauses => interp_case_env fuel env scrut clauses
  termination_by (fuel, sizeOf e + 1)

  def interp_iff_env (fuel : Nat) (env : Env) (cnd : Expr) (thn : Expr) (els : Expr) : Value :=
    let cnd_v := interp_env fuel env cnd
    match cnd_v with
    | .error d => .error d
    | .bool true => interp_env fuel env thn
    | .bool false => interp_env fuel env els
    | _ => err "type" "'if' condition must be a bool"
  termination_by (fuel, sizeOf cnd + sizeOf thn + sizeOf els + 1)
  decreasing_by
    all_goals simp_wf
    all_goals (have := Expr.sizeOf_pos' cnd; have := Expr.sizeOf_pos' thn; have := Expr.sizeOf_pos' els)
    all_goals omega

  def interp_ref_env (env : Env) (x : Symbol) : Value :=
    match env_lookup env x with
    | none => err "scope" s!"free variable '{x}'"
    | some v => v

  def interp_lett_env (fuel : Nat) (env : Env) (x : Symbol) (rhs : Expr) (body : Expr) : Value :=
    match interp_env fuel env rhs with
    | .error d => .error d
    | v => interp_env fuel ((x, v) :: env) body
  termination_by (fuel, sizeOf rhs + sizeOf body + 1)
  decreasing_by
    all_goals simp_wf
    all_goals (have := Expr.sizeOf_pos' rhs; have := Expr.sizeOf_pos' body)
    all_goals omega

  def interp_fn_env (env : Env) (params : List Symbol) (body : Expr) : Value :=
    match checkFn params with
    | some e => e
    | none => .fn params body env

  def interp_app_env (fuel : Nat) (env : Env) (fn : Expr) (args : List Expr) : Value :=
    let fv := interp_env fuel env fn
    let avs := interp_env_list fuel env args
    match combineErrs (fv :: avs) with
    | some e => e
    | none =>
      match fv with
      | .fn params body cenv =>
        if params.length != avs.length then
          err "arity" s!"function expects {params.length} arguments, got {avs.length}"
        else
          match fuel with
          | 0 => err "fuel" "out of fuel"
          | k + 1 =>
            match env_extend cenv params avs with
            | none => err "internal" "invalid environment extension"
            | some env' => interp_env k env' body
      | _ => err "type" "expected a function"
  termination_by (fuel, sizeOf fn + sizeOf args + 1)
  decreasing_by
    all_goals simp_wf
    all_goals (have := List.sizeOf_pos' args; have := Expr.sizeOf_pos' fn)
    all_goals omega

  def interp_con_env (fuel : Nat) (env : Env) (tag : Symbol) (args : List Expr) : Value :=
    let vs := interp_env_list fuel env args
    match combineErrs vs with
    | some e => e
    | none => .con tag (vs)
  termination_by (fuel, sizeOf args + 1)

  def interp_case_env (fuel : Nat) (env : Env) (scrut : Expr) (clauses : List Clause) : Value :=
    match checkCase clauses with
    | some e => e
    | none =>
      match interp_env fuel env scrut with  -- (fuel, sizeOf scrut)
      | .error d => .error d
      | .con tag fields => interp_clauses fuel env tag fields clauses  -- (fuel, sizeOf clauses)
      | _ => err "type" "'case' scrutinee must be a constructor"
  termination_by (fuel, sizeOf scrut + sizeOf clauses + 1)
  decreasing_by
    all_goals simp_wf
    all_goals (have := Expr.sizeOf_pos' scrut; have := List.sizeOf_pos' clauses)
    all_goals omega

  /-- Evaluate a list of expressions (left to right). -/
  def interp_env_list (fuel : Nat) (env : Env) (es : List Expr) : List Value :=
    match es with
    | [] => []
    | e :: es => interp_env fuel env e :: interp_env_list fuel env es
  termination_by (fuel, sizeOf es)
  decreasing_by
    all_goals simp_wf
    all_goals (have := List.sizeOf_pos' es)
    all_goals omega

  /-- Select the clause for `tag` and evaluate its body with the fields bound. -/
  def interp_clauses (fuel : Nat) (env : Env) (tag : Symbol) (fields : List Value)
  (cs : List Clause) : Value :=
    match cs with
    | [] => err "match" s!"no clause for tag '{tag}'"
    | ⟨ctag, vars, body⟩ :: cs =>
      if ctag == tag then
        if vars.length != fields.length then
          err "arity" s!"clause '{ctag}' binds {vars.length} variables but the constructor has {fields.length} fields"
        else
          match env_extend env vars fields with
          | none => err "internal" "invalid environment extension"
          | some env' => interp_env fuel env' body
      else interp_clauses fuel env tag fields cs
  termination_by (fuel, sizeOf cs)
end

/-- Evaluate in the empty environment with the given call-depth fuel. -/
def interpf (fuel : Nat) (e : Expr) : Value := interp_env fuel [] e
def interp := interpf 10000
