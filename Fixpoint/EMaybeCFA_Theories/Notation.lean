import Fixpoint.EZeroCFA_claude.Term

/-!
# Embedded syntax

Programs are written inline in the original s-expression syntax and parsed by
Lean itself (positions in error messages, editor highlighting):

    def loopProg : Raw :=
      [absexp| (letrec ((loop (lambda (i) (if (< i 100) (loop (+ i 1)) i)))) (loop 0))]

Notes
* The macro yields an unlabelled, *named* `Raw` tree; `Raw.close` does scope
  checking and labelling (a macro cannot number nodes in post-order).
* No negative literals: write `(- 0 5)`.  (`(- 3 4)` would otherwise be
  ambiguous with applying `-3` to `4`.)
* `lambda`, `letrec`, `input` become global keywords once this file is
  imported.  If that is a problem, wrap the declarations in a `scoped`
  namespace.
-/

namespace AbsInt

declare_syntax_cat absexp
declare_syntax_cat abscmp

syntax "<"  : abscmp
syntax "<=" : abscmp
syntax ">"  : abscmp
syntax ">=" : abscmp
syntax "==" : abscmp
syntax "!=" : abscmp

syntax num                                                      : absexp
syntax ident                                                    : absexp
syntax "(" "input" ")"                                          : absexp
syntax "(" "lambda" "(" ident ")" absexp ")"                    : absexp
syntax "(" "let" "(" "(" ident absexp ")" ")" absexp ")"        : absexp
syntax "(" "letrec" "(" "(" ident absexp ")" ")" absexp ")"     : absexp
syntax "(" "if" "(" abscmp absexp absexp ")" absexp absexp ")"  : absexp
syntax "(" "+" absexp absexp ")"                                : absexp
syntax "(" "-" absexp absexp ")"                                : absexp
syntax "(" "*" absexp absexp ")"                                : absexp
syntax "(" absexp absexp ")"                                    : absexp

/-- Bridge from the embedded syntax back into ordinary Lean terms. -/
syntax "[absexp|" absexp "]" : term
syntax "[abscmp|" abscmp "]" : term

macro_rules
  | `([abscmp| <])  => `(CmpOp.lt)
  | `([abscmp| <=]) => `(CmpOp.le)
  | `([abscmp| >])  => `(CmpOp.gt)
  | `([abscmp| >=]) => `(CmpOp.ge)
  | `([abscmp| ==]) => `(CmpOp.eq)
  | `([abscmp| !=]) => `(CmpOp.ne)

macro_rules
  | `([absexp| $n:num]) => `(Raw.num $n)
  | `([absexp| $x:ident]) => `(Raw.var $(Lean.quote x.getId.toString))
  | `([absexp| (input)]) => `(Raw.input)
  | `([absexp| (lambda ($x:ident) $b:absexp)]) =>
    `(Raw.lam $(Lean.quote x.getId.toString) [absexp| $b])
  | `([absexp| (let (($x:ident $rhs:absexp)) $b:absexp)]) =>
    `(Raw.letE $(Lean.quote x.getId.toString) [absexp| $rhs] [absexp| $b])
  | `([absexp| (letrec (($x:ident $rhs:absexp)) $b:absexp)]) =>
    `(Raw.letrec $(Lean.quote x.getId.toString) [absexp| $rhs] [absexp| $b])
  | `([absexp| (if ($c:abscmp $a:absexp $b:absexp) $t:absexp $e:absexp)]) =>
    `(Raw.branch [abscmp| $c] [absexp| $a] [absexp| $b] [absexp| $t] [absexp| $e])
  | `([absexp| (+ $a:absexp $b:absexp)]) => `(Raw.arith ArithOp.add [absexp| $a] [absexp| $b])
  | `([absexp| (- $a:absexp $b:absexp)]) => `(Raw.arith ArithOp.sub [absexp| $a] [absexp| $b])
  | `([absexp| (* $a:absexp $b:absexp)]) => `(Raw.arith ArithOp.mul [absexp| $a] [absexp| $b])
  | `([absexp| ($f:absexp $a:absexp)]) => `(Raw.app [absexp| $f] [absexp| $a])

end AbsInt
