import Fixpoint.adi.Interpreter


open ADI.Cache

namespace ADI.Interp


/-! ============================================================
    Interpreter Examples
    ============================================================ -/

private def V (x : String) := Exp.var x
private def N (n : Nat) := Exp.num n
private def B (b : Bool) := Exp.bool b
private def L (x : String) (b : Exp) := Exp.lam x b
private def A (f a : Exp) := Exp.app f a
private def Let (x : String) (r b : Exp) := Exp.let_ x r b
private def If (c t e : Exp) := Exp.if_ c t e

def demo (title : String) (e : Exp) : IO Unit := do
  IO.println s!"--- {title} ---"
  IO.println (showStore (← run (eval e)))
  IO.println ""

def examples : IO Unit := do
  demo "let binding"
    (Let "x" (N 1) (V "x"))  -- let x 1 x

  demo "identity function"
    (Let "f" (L "y" (V "y"))  -- let f(y)=y $ f(42)
      (A (V "f") (N 42)))

  demo "multiple values"
    (Let "f" (L "x" (V "x"))
      (Let "a" (A (V "f") (N 1))
        (Let "b" (A (V "f") (N 2))
          (V "a"))))

  demo "conditional (true)"
    (If (B true)
      (Let "x" (N 1) (V "x"))
      (Let "x" (N 2) (V "x")))

  demo "conditional (unknown)"
    (Let "b" (L "x" (V "x"))
      (Let "c" (A (V "b") (B true))
        (Let "d" (A (V "b") (B false))
          (If (V "c")
            (Let "r" (N 1) (V "r"))
            (Let "r" (N 2) (V "r"))))))

  demo "higher-order"
    (Let "apply" (L "f" (A (V "f") (N 99)))
      (Let "g" (L "z" (V "z"))
        (A (V "apply") (V "g"))))

  demo "self-application"
    (Let "ω" (L "x" (A (V "x") (V "x")))
      (A (V "ω") (V "ω")))

#eval examples

end ADI.Interp
