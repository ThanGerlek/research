import Fixpoint.SimpLang.Helpers
import Fixpoint.SimpLang.Defs


def find_clause (tag : Symbol) (clauses : List Clause) : Option Clause :=
  match clauses with
  | [] => none
  | c::cs =>
    if c.tag = tag then c else find_clause tag cs  -- !Warning: no error if more than one clause matches; it just uses the first one


--    The program is stuck: no rule applies. The message begins "stuck: <kind>:"
--    and the kind says WHAT WENT WRONG not which construct it happened in.
def stuck desc := Value.error desc
--    A syntax error: the program has no Expr. The message begins
--    "syntax: <kind>:" and the kind is one of those the page lists.
-- fun bad_syntax(kind : Symbol detail : String):
--   error(#'syntax string_append(to_string(kind) string_append(": " detail)))

def req_len_1 (arr : List Value) : Value :=
  match arr with
  | [x0] => x0
  | _ => stuck "Required len 1"

def req_len_2 (arr : List Value) : Value × Value :=
  match arr with
  | [x, y] => ⟨x, y⟩
  | _ => ⟨stuck "Required len 2", stuck "Required len 2"⟩

def req_len_3 (arr : List Value) : Value × Value × Value :=
  match arr with
  | [x, y, z] => ⟨x, y, z⟩
  | _ => ⟨stuck "Required len 3", stuck "Required len 3", stuck "Required len 3"⟩




mutual
  def interp_env (fuel : Nat) (env : Env) (e : Expr) : Value :=
    match fuel with
    | 0 => .error "Ran out of fuel"
    | fuel + 1 =>
    match e with
    | Expr.int n => .int n
    | Expr.bool b => .bool b
    | Expr.prim op args => interp_prim_env fuel env op args
    | Expr.iff cnd thn els => interp_iff_env fuel env cnd thn els
    | Expr.ref x => interp_ref_env env x
    | Expr.lett x rhs body => interp_lett_env fuel env x rhs body
    | Expr.fn self params body => interp_fn_env env self params body
    | Expr.app fn args => interp_app_env fuel env fn args
    | Expr.con tag args => interp_con_env fuel env tag args
    | Expr.case scrut clauses => interp_case_env fuel env scrut clauses
    termination_by fuel
    decreasing_by
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp


  def interp_prim_env (fuel : Nat) (env : Env) (op : Prim) (args : List Expr) : Value :=
    match fuel with
    | 0 => .error "Ran out of fuel"
    | fuel + 1 =>
    match op with
    | Prim.add =>
      let ⟨x, y⟩ : Value × Value := req_len_2 $ args.map $ interp_env fuel env
      match x,y with
      | .error _, .error _ => combine_err x y
      | .error _, _ => x
      | _, .error _ => y
      | .int n, .int m => .int (n + m)
      | _, _ => stuck "Required integer"
    | Prim.sub =>
      let ⟨x, y⟩ : Value × Value := req_len_2 $ args.map $ interp_env fuel env
      match x,y with
      | .error _, .error _ => combine_err x y
      | .error _, _ => x
      | _, .error _ => y
      | .int n, .int m => .int (n - m)
      | _, _ => stuck "Required integer"
    | Prim.mul =>
      let ⟨x, y⟩ : Value × Value := req_len_2 $ args.map $ interp_env fuel env
      match x,y with
      | .error _, .error _ => combine_err x y
      | .error _, _ => x
      | _, .error _ => y
      | .int n, .int m => .int (n * m)
      | _, _ => stuck "Required integer"
    | Prim.div =>
      let ⟨x, y⟩ : Value × Value := req_len_2 $ args.map $ interp_env fuel env
      match x,y with
      | .error _, .error _ => combine_err x y
      | .error _, _ => x
      | _, .error _ => y
      | .int n, .int m => .int (n / m)
      | _, _ => stuck "Required integer"
    | Prim.mod =>
      let ⟨x, y⟩ : Value × Value := req_len_2 $ args.map $ interp_env fuel env
      match x,y with
      | .error _, .error _ => combine_err x y
      | .error _, _ => x
      | _, .error _ => y
      | .int n, .int m => .int (n % m)
      | _, _ => stuck "Required integer"
    | Prim.lt =>
      let ⟨x, y⟩ : Value × Value := req_len_2 $ args.map $ interp_env fuel env
      match x,y with
      | .error _, .error _ => combine_err x y
      | .error _, _ => x
      | _, .error _ => y
      | .int n, .int m => .bool (n < m)
      | _, _ => stuck "Required integer"
    | Prim.eq =>
      let ⟨x, y⟩ : Value × Value := req_len_2 $ args.map $ interp_env fuel env
      match x,y with
      | .error _, .error _ => combine_err x y
      | .error _, _ => x
      | _, .error _ => y
      | .int n, .int m => .bool (n == m)
      | .bool p, .bool q => .bool (p == q)
      | _, _ => .bool False
    termination_by fuel
    decreasing_by
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp


  def interp_iff_env (fuel : Nat) (env : Env) (cnd : Expr) (thn : Expr) (els : Expr) :=
    match fuel with
    | 0 => .error "Ran out of fuel"
    | fuel + 1 =>
    let cnd_v := interp_env fuel env cnd
    match cnd_v with
    | .error _ => cnd_v
    | .bool b =>
      if b
      then interp_env fuel env thn
      else interp_env fuel env els
    | _ => stuck "Condition wasn't a boolean value"
    termination_by fuel
    decreasing_by
      · simp
      · simp
      · simp

  def interp_ref_env (env : Env) (x : Symbol) : Value :=
    match env[x]? with
    | none => stuck "Free variable reference"
    | some bound_val => bound_val

  def interp_lett_env (fuel : Nat) (env : Env) (x : Symbol) (rhs : Expr) (body : Expr) : Value :=
    match fuel with
    | 0 => .error "Ran out of fuel"
    | fuel + 1 =>
    let bound_val := interp_env fuel env rhs
    let env' := env.insert x bound_val
    interp_env fuel env' body
    termination_by fuel
    decreasing_by
      · simp
      · simp

  def interp_fn_env (_ : Env) (_self : Option Symbol) (params : List Symbol) (body : Expr) : Value :=
    if contains_duplicates params then .error "Duplicate param" else
    .fn params body

  def interp_app_env (fuel : Nat) (env : Env) (fn : Expr) (args : List Expr) : Value :=
    match fuel with
    | 0 => .error "Ran out of fuel"
    | fuel + 1 =>
    let fn_v := interp_env fuel env fn
    match fn_v with
    | .error _ => fn_v
    | .fn params body =>
      let arg_vals := args.map (interp_env fuel env)
      let opt_env := env_extend env params arg_vals  -- !Warning: potentially hidden error values?
      match opt_env with
      | none => .error "Mismatched numbers of parameters and arguments"
      | some env =>
        interp_env fuel env body
    | _ => .error "Required fn"
    termination_by fuel
    decreasing_by
      · simp
      · simp
      · simp

  def interp_con_env (fuel : Nat) (env : Env) (tag : Symbol) (args : List Expr) : Value :=
    match fuel with
    | 0 => .error "Ran out of fuel"
    | fuel + 1 =>
    let field_vals := args.map (interp_env fuel env)
    .con tag field_vals
    termination_by fuel
    decreasing_by
      · simp

  def interp_case_env (fuel : Nat) (env : Env) (scrut : Expr) (clauses : List Clause) : Value :=
    match fuel with
    | 0 => .error "Ran out of fuel"
    | fuel + 1 =>
    let scrut_v := interp_env fuel env scrut
    match scrut_v with
    | .con tag fields =>
      let opt_clause := find_clause tag clauses
      match opt_clause with
      | none => .error "No matching clause found"
      | some clause =>
        let opt_env := env_extend env clause.vars fields
        match opt_env with
        | none => .error "Invalid env write in interp_case_env"
        | some env => interp_env fuel env clause.body
    | _ => .error "Required a .con"
    termination_by fuel
    decreasing_by
      · simp
      · simp

end

def interp (e : Expr) : Value := interp_env 100 ∅ e
