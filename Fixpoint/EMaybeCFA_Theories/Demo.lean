import Fixpoint.EZeroCFA_claude.Analyzer
import Fixpoint.EZeroCFA_claude.Notation

/-!
# Configuration, domain dispatch, demos, and build-time regression tests

The `#guard`s at the bottom replace "run and eyeball the output": they are
checked when the file is compiled.  Expected values are the outputs of the
original Python implementation (and of a Python model of this pure-step
formulation, which agrees on every demo).
-/

namespace AbsInt

inductive DomainName where
  | interval | parity | product | productNoReduce
  deriving DecidableEq, Repr

namespace DomainName
def toString : DomainName → String
  | .interval => "interval" | .parity => "parity"
  | .product => "product" | .productNoReduce => "product-noreduce"
instance : ToString DomainName := ⟨DomainName.toString⟩
def ofString? : String → Option DomainName
  | "interval" => some .interval | "parity" => some .parity
  | "product" => some .product | "product-noreduce" => some .productNoReduce
  | _ => none
end DomainName

structure Config where
  domain : DomainName := .interval
  k : Nat := 0
  delay : Nat := 2
  narrow : Nat := 2
  thresholds : List Int := []

def Config.label (c : Config) : String :=
  s!"{c.domain} k={c.k} delay={c.delay} narrow={c.narrow} thresholds={c.thresholds}"

structure Report where
  result : String
  store : String

def reportOf {α : Type} (dom : Domain α) (p : Params) (r : Raw) : Except String Report := do
  let A ← Analyzer.ofRaw dom p r
  match A.run with
  | none => throw "no fixpoint within maxIter"
  | some (v, st) => pure ⟨A.showValue v, A.showStore st⟩

/-- Dispatch on the domain name, one precisely-typed branch per domain. -/
def runConfig (r : Raw) (cfg : Config) : Except String Report :=
  let p : Params := { k := cfg.k, delay := cfg.delay, narrowPasses := cfg.narrow }
  match cfg.domain with
  | .interval => reportOf (Interval.domain cfg.thresholds) p r
  | .parity => reportOf Parity.domain p r
  | .product =>
    reportOf (Domain.product (Interval.domain cfg.thresholds) Parity.domain
      (intervalParityReducer cfg.thresholds)) p r
  | .productNoReduce =>
    reportOf (Domain.product (Interval.domain cfg.thresholds) Parity.domain) p r

/-! ## Programs (embedded syntax, checked by Lean's parser) -/

def loopProg : Raw :=
  [absexp| (letrec ((loop (lambda (i) (if (< i 100) (loop (+ i 1)) i)))) (loop 0))]

def joinProg : Raw :=
  [absexp| (let ((f (if (< (input) 0) (lambda (x) (+ x 1)) (lambda (y) (- y 1))))) (f 10))]

def twiceProg : Raw :=
  [absexp| (let ((twice (lambda (f) (lambda (x) (f (f x))))))
              (let ((inc (lambda (n) (+ n 1)))) ((twice inc) 0)))]

def evenProg : Raw :=
  [absexp| (let ((x (* (input) 2))) (if (< x 4) (if (> x 2) 1 2) 3))]

structure Demo where
  title : String
  prog : Raw
  configs : List Config

def demos : List Demo := [
  { title := "Loop via recursion: widening, narrowing, thresholds"
    prog := loopProg
    configs := [{ narrow := 0 }, { narrow := 2 }, { narrow := 0, thresholds := [100] }] },
  { title := "Join of closure sets (control-flow analysis)"
    prog := joinProg
    configs := [{}] },
  { title := "Context sensitivity: apply the same function twice"
    prog := twiceProg
    configs := [{ k := 0 }, { k := 1 }] },
  { title := "Reduction: x is even, so  2 < x < 4  is impossible"
    prog := evenProg
    configs := [{ domain := .interval }, { domain := .productNoReduce }, { domain := .product }] }
]

def runDemos : IO Unit := do
  for d in demos do
    IO.println s!"\n== {d.title}"
    for cfg in d.configs do
      match runConfig d.prog cfg with
      | .ok rep =>
        IO.println s!"   [{cfg.label}]\n      result: {rep.result}\n      store:  {rep.store}"
      | .error e =>
        IO.println s!"   [{cfg.label}]\n      error: {e}"

/-! ## Regression tests (checked at build time) -/

def expect (r : Except String Report) (res sto : String) : Bool :=
  match r with
  | .ok rep => rep.result == res && rep.store == sto
  | .error _ => false

-- loop: widening only / + narrowing / + threshold
#guard expect (runConfig loopProg { narrow := 0 }) "[100,+inf]" "i=[0,+inf], loop={λi#2}"
#guard expect (runConfig loopProg { narrow := 2 }) "[100,+inf]" "i=[0,100], loop={λi#2}"
#guard expect (runConfig loopProg { narrow := 0, thresholds := [100] }) "[100,100]" "i=[0,100], loop={λi#2}"

-- closure-set join
#guard expect (runConfig joinProg {}) "[9,11]" "f={λx#1, λy#2}, x=[10,10], y=[10,10]"

-- context sensitivity
#guard expect (runConfig twiceProg { k := 0 }) "[1,+inf]"
  "f={λn#5}, inc={λn#5}, n=[0,+inf], twice={λf#4}, x=[0,0]"
#guard expect (runConfig twiceProg { k := 1 }) "[2,2]"
  "f@6={λn#5}, inc={λn#5}, n@1=[0,0], n@2=[1,1], twice={λf#4}, x@7=[0,0]"

-- reduction
#guard expect (runConfig evenProg { domain := .interval }) "[1,3]" "x=[-inf,+inf]"
#guard expect (runConfig evenProg { domain := .productNoReduce }) "([1,3], top)" "x=([-inf,+inf], even)"
#guard expect (runConfig evenProg { domain := .product }) "([2,3], top)" "x=([-inf,+inf], even)"

end AbsInt
