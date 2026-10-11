import Std.Data.HashMap

abbrev Symbol := String


-- Primops

inductive Prim
  | add : Prim
  | sub : Prim
  | mul : Prim
  | div : Prim
  | mod : Prim
  | lt : Prim
  | eq : Prim
deriving Repr


-- Expr and Clause

mutual
  structure Clause where
    tag : Symbol
    vars : List Symbol
    body : Expr

  inductive Expr
    | int (n : Int)
    | bool (b : Bool)
    | prim (op : Prim) (args : List Expr)
    | iff (test : Expr) (thn : Expr) (els : Expr)
    | ref (x : Symbol)
    | lett (x : Symbol) (rhs : Expr) (body : Expr)
    | fn (self : Option Symbol) (params : List Symbol) (body : Expr)
    | app (fn : Expr) (args : List Expr)
    | con (tag : Symbol) (args : List Expr)
    | case (scrut : Expr) (clauses : List Clause)
end


-- Value

inductive Value
| int (n : Int)
| bool (b : Bool)
| fn (params : List Symbol) (body : Expr)
| con (tag : Symbol) (fields : List Value)
| error (desc : String)
instance : Inhabited Value := ⟨.int 0⟩

def combine_err (err1 : Value) (err2 : Value) : Value :=
  match err1, err2 with
  | .error d1, .error d2 => .error ("[ " ++ d1 ++ " | " ++ d2 ++ " ]")
  | _, _ => .error "Tried to combine_err with non-error value(s)"

instance reprValue : Repr Value where
  reprPrec v p := match v with
    | Value.bool b => f!"BOOL {if b then "True" else "False"}"
    | Value.con tag _fields => f!"CON {tag}"
    | Value.fn params _ => f!"FUN {params.repr p}"
    | Value.int n => f!"INT {n.repr}"
    | Value.error desc => f!"ERROR '{desc}'"


-- Env

abbrev Env := @Std.HashMap Symbol Value (inferInstance) (inferInstance)

def env_insert (env : Env) (x : Symbol) (v : Value) : Option Env :=
  match v with
  | .error _ => none  -- !Warning: error info (whatever the error was) is lost!
  | _ => env.insert x v

def env_extend (env : Env) (xs : List Symbol) (vs : List Value) : Option Env :=
  match xs, vs with
  | [], [] => env
  | x::xs, v::vs =>
    let env := env_insert env x v
    match env with
    | none => none
    | some env => env_extend env xs vs
  | _, _ => none  -- !Warning: error info ("invalid env write") is lost!
