import Fixpoint.DZeroCFA.Interpreter

-- Compact pretty-printers
def Var.str (x : Var) : String := x

def Expr.pp : Expr → String
  | .lamE x e => s!"(λ.{x.str} {e.pp})"
  | .appE a b => s!"(app {a.pp} {b.pp})"
  | .refE x => x.str

-- Renders the context as a hole-filled expression: `e` is plugged into `[]`.
def RContext.pp (hole : String) : RContext → String
  | .topC => hole
  | .lamC x ctx => ctx.pp s!"(λ.{x.str} {hole})"
  | .appC_operand e0 ctx => ctx.pp s!"(app {e0.pp} {hole})"
  | .appC_operator ctx e1 => ctx.pp s!"(app {hole} {e1.pp})"

def ppCursor (c : Cursor) : String := c.2.pp s!"⟦{c.1.pp}⟧"


-- Compact pretty-printers
def ppMarker : FnMarker → String
  | .evaluateMarker => "evaluate"
  | .exprResolveMarker => "exprResolve"
  | .callResolveMarker => "callResolve"


  -- (let f (lam x x) (let a (app f 1) (let b (app f 2) a)))
def prgm : SugExpr :=
  .letE "f" (.lamE "x" $ .refE "x") $
  .letE "a" (.appE (.refE "f") (.idE "1")) $
  .letE "b" (.appE (.refE "f") (.idE "2")) $
  .refE "a"  -- This ref to "a" is the expression to be queried.
def prgmCtx : RContext := .lamC "b" $ .appC_operator (.lamC "a" $ .appC_operator (.lamC "f" (.appC_operator (.topC) $ Expr.lamE "x" $ Expr.refE "x")) $ Expr.appE (Expr.refE "f") $ Expr.lamE "1" $ Expr.refE "1") $ Expr.appE (Expr.refE "f") $ Expr.lamE "2" $ Expr.refE "2"
def queryCursor : Cursor := ⟨.refE "a", prgmCtx⟩


def demo : IO Unit := do
  -- demo "multiple values"
  -- (let f (lam x x) (let a (app f 1) (let b (app f 2) a)))
  let query : FnMarker × Cursor := ⟨.evaluateMarker, queryCursor⟩

  let tbl ← Cache.run (Cache.gfix equation query)
  IO.println s!"Table ({tbl.size} entries):"
  for (⟨marker, cursor⟩, (val, _)) in tbl.toList do
    IO.println s!"{ppMarker marker}\n\t    {ppCursor cursor}"
    match val with
    | none => IO.println "\t  ↦ (no value)"
    | some cs =>
      for c in cs.toList do
        IO.println s!"\t  ↦ {ppCursor c}"

#eval demo
