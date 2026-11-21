-- Types

def Var := String
deriving DecidableEq, Hashable, Repr

inductive Expr where
  | lamE (x : Var) (e : Expr) : Expr
  | appE (e0 e1 : Expr) : Expr
  | refE (x : Var) : Expr
  deriving BEq, Hashable, Repr

inductive Value where  -- Demand 0CFA: no environments
  | lamV (x : Var) (e : Expr) : Value

inductive RContext where
  | topC : RContext
  | lamC (x : Var) (ctx : RContext) : RContext
  | appC_operand (e0 : Expr) (ctx : RContext) : RContext
  | appC_operator (ctx : RContext) (e1 : Expr) : RContext
  deriving BEq, Hashable, Repr
  -- NOTE: appC_X indicates that *the hole* is X, not that the
  --  structure contains X. So appC_operand contains the operator.

def Cursor := Expr × RContext
  deriving BEq, Hashable, Repr


-- Sugaring

inductive SugExpr where
  | lamE (x : Var) (e : SugExpr) : SugExpr
  | appE (e0 e1 : SugExpr) : SugExpr
  | refE (x : Var) : SugExpr
  | letE (x : Var) (e ebody : SugExpr) : SugExpr
  | idE (n : Var) : SugExpr
  deriving BEq, Hashable, Repr

def desugar (e : SugExpr) : Expr :=
  match e with
  | .lamE x e => .lamE x (desugar e)
  | .appE e0 e1 => .appE (desugar e0) (desugar e1)
  | .refE x => .refE x
  | .letE x e ebody => .appE (.lamE x (desugar ebody)) (desugar e)
  | .idE n => .lamE n (.refE n)


-- Nondet Monad

abbrev ND := List

namespace ND

instance monadND : Monad ND where
  pure a := [a]
  bind a f := a.flatMap f

instance : EmptyCollection (ND α) where
  emptyCollection := []

def choose (a b : α) : ND α := [a, b]

def chooseFrom (a b : ND α) : ND α := a ++ b

def fail : ND α := []

end ND
