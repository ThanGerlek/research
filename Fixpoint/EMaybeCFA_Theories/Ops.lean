/-!
# Operators

Comparison / arithmetic operators as real inductives (Python used `Literal`
string types).  Core Lean only; no Mathlib.
-/

namespace AbsInt

inductive CmpOp where
  | lt | le | gt | ge | eq | ne
  deriving DecidableEq, Repr

inductive ArithOp where
  | add | sub | mul
  deriving DecidableEq, Repr

namespace CmpOp

/-- Concrete meaning of `x op y`. -/
def holds : CmpOp → Int → Int → Prop
  | .lt, x, y => x < y
  | .le, x, y => x ≤ y
  | .gt, x, y => x > y
  | .ge, x, y => x ≥ y
  | .eq, x, y => x = y
  | .ne, x, y => x ≠ y

/-- Python: `NEG`. Negation of a guard (used for the `else` branch). -/
def neg : CmpOp → CmpOp
  | .lt => .ge
  | .le => .gt
  | .gt => .le
  | .ge => .lt
  | .eq => .ne
  | .ne => .eq

def ofString? : String → Option CmpOp
  | "<"  => some .lt
  | "<=" => some .le
  | ">"  => some .gt
  | ">=" => some .ge
  | "==" => some .eq
  | "!=" => some .ne
  | _    => none

end CmpOp

namespace ArithOp

/-- Concrete meaning of `x op y`. -/
def eval : ArithOp → Int → Int → Int
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y

end ArithOp

end AbsInt
