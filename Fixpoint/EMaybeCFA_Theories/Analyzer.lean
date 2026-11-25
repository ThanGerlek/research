import Fixpoint.EZeroCFA_claude.Domain
import Fixpoint.EZeroCFA_claude.Term

/-!
# The analyzer, as a pure monotone step

State of the analysis: `AbsState α` = abstract store σ plus a table of function
summaries.  A summary key is a (closure, call-context) pair; **a key is in the
table iff some call site demanded it.**

    F σ  : one pass.  Evaluates the program, and the body of every demanded
           key, *reading* σ and *writing* a fresh accumulator.

    ascend :  σ' = σ ∇ (σ ⊔ F σ)      (plain join during the first `delay` rounds)
    narrow :  σ' = σ Δ F σ

There is no `visited` set, no `changed` flag, no narrowing-mode flag, no
`out*` tables and no oracle for callee bodies: calls read the summary table
and only record demand, so `ev` is plainly structural on the term.  Errors are
gone too (scoping is intrinsic), so nothing is in `Except`.

Positivity: closures hold addresses (`Env`) rather than values, so `Value` is
not recursive.

Termination: the only remaining non-structural loop is `ascend`, bounded by
`Params.maxIter` fuel.  Replace it by a well-founded argument when ready
(see `ascend`).
-/

namespace AbsInt

/-- Last `k` call-site labels (k-CFA context). -/
abbrev Ctx := List Nat

/-- Abstract address: binding site + context (display name only for printing). -/
structure Addr where
  label : Nat
  name : String
  ctx : Ctx
  deriving DecidableEq, Repr

/-- Length-indexed environment of addresses; `Env.get` is total. -/
inductive Env : Nat → Type where
  | nil : Env 0
  | cons {n : Nat} (a : Addr) (rest : Env n) : Env (n + 1)

namespace Env

def get : {n : Nat} → Env n → Fin n → Addr
  | _, .cons a _, ⟨0, _⟩ => a
  | _, .cons _ rest, ⟨i + 1, h⟩ => rest.get ⟨i, Nat.lt_of_succ_lt_succ h⟩
  | _, .nil, i => i.elim0

def toList : {n : Nat} → Env n → List Addr
  | _, .nil => []
  | _, .cons a rest => a :: rest.toList

end Env

/-- A closure carries its own body, so no lambda table is needed.  Lambda
labels are unique, so equality is label + environment contents. -/
structure Closure where
  n : Nat
  label : Nat
  param : String
  body : Tm (n + 1)
  env : Env n

instance : BEq Closure :=
  ⟨fun a b => a.label == b.label && a.env.toList == b.env.toList⟩

/-- Function-summary key. -/
abbrev RetKey := Closure × Ctx

namespace Clos
def union (a b : List Closure) : List Closure := b.foldl (fun acc c => List.insert c acc) a
def inter (a b : List Closure) : List Closure := a.filter (fun c => b.contains c)
def subset (a b : List Closure) : Bool := a.all (fun c => b.contains c)
end Clos

/-- Abstract value: base element plus the set of possible closures. -/
structure Value (α : Type) where
  num : α
  clos : List Closure

/-! ## Association-list tables -/

abbrev Table (κ ν : Type) := List (κ × ν)

namespace Table
variable {κ ν : Type} [BEq κ]

def get? (t : Table κ ν) (k : κ) : Option ν :=
  (List.find? (fun p => p.1 == k) t).map (fun p => p.2)

def getD (t : Table κ ν) (k : κ) (d : ν) : ν := (Table.get? t k).getD d

def put (t : Table κ ν) (k : κ) (v : ν) : Table κ ν :=
  if List.any t (fun p => p.1 == k) then
    List.map (fun p => if p.1 == k then (k, v) else p) t
  else t ++ [(k, v)]

end Table

/-! ## Analysis state -/

structure AbsState (α : Type) where
  store : Table Addr (Value α) := []
  ret : Table RetKey (Value α) := []

structure Params where
  /-- call-string depth (0 = 0-CFA) -/
  k : Nat := 0
  /-- rounds of plain join before widening kicks in -/
  delay : Nat := 2
  narrowPasses : Nat := 2
  /-- fuel for the ascending phase -/
  maxIter : Nat := 1000

structure Analyzer (α : Type) where
  dom : Domain α
  params : Params := {}
  prog : Tm 0

namespace Analyzer
variable {α : Type}

/-! ### Lattice operations lifted to `Value` -/

def bot (A : Analyzer α) : Value α := ⟨A.dom.bot, []⟩
def vjoin (A : Analyzer α) (a b : Value α) : Value α :=
  ⟨A.dom.join a.num b.num, Clos.union a.clos b.clos⟩
def vmeet (A : Analyzer α) (a b : Value α) : Value α :=
  ⟨A.dom.meet a.num b.num, Clos.inter a.clos b.clos⟩
def vwiden (A : Analyzer α) (a b : Value α) : Value α :=
  ⟨A.dom.widen a.num b.num, Clos.union a.clos b.clos⟩
def vnarrow (A : Analyzer α) (a b : Value α) : Value α :=
  ⟨A.dom.narrow a.num b.num, b.clos⟩
def vle (A : Analyzer α) (a b : Value α) : Bool :=
  A.dom.le a.num b.num && Clos.subset a.clos b.clos

/-! ### Writes into the accumulator (always a weak update: join) -/

def writeStore (A : Analyzer α) (d : AbsState α) (a : Addr) (v : Value α) : AbsState α :=
  { d with store := Table.put d.store a (A.vjoin (Table.getD d.store a A.bot) v) }

/-- Also used with `v = ⊥` to record *demand* for a summary. -/
def writeRet (A : Analyzer α) (d : AbsState α) (k : RetKey) (v : Value α) : AbsState α :=
  { d with ret := Table.put d.ret k (A.vjoin (Table.getD d.ret k A.bot) v) }

/-! ### Reading, refinement, guards -/

/-- Read from the *old* store, met with guard information. -/
def lookup (A : Analyzer α) (σ : AbsState α) (a : Addr) (ref : Table Addr (Value α)) : Value α :=
  let v := Table.getD σ.store a A.bot
  match Table.get? ref a with
  | some r => A.vmeet v r
  | none => v

/-- Record a refined value for the variable tested by a guard (if it is one). -/
def refine (A : Analyzer α) {n : Nat} (ref : Table Addr (Value α)) (e : Tm n) (env : Env n)
    (v : Value α) (num : α) : Table Addr (Value α) :=
  match e with
  | .var i =>
    let a := env.get i
    let new : Value α := ⟨num, v.clos⟩
    Table.put ref a
      (match Table.get? ref a with
       | some r => A.vmeet r new
       | none => new)
  | _ => ref

/-- The refinement map for the branch where `lhs op rhs` holds, or `none` if
that branch is infeasible. -/
def guardRef (A : Analyzer α) {n : Nat} (ref : Table Addr (Value α)) (env : Env n)
    (lhs rhs : Tm n) (va vb : Value α) (op : CmpOp) : Option (Table Addr (Value α)) :=
  let (na, nb) := A.dom.filterCmp op va.num vb.num
  if A.dom.isBot na || A.dom.isBot nb then none
  else some (A.refine (A.refine ref lhs env va na) rhs env vb nb)

/-! ### Abstract evaluation

Reads the old state `σ`; writes the accumulator (the monad's state). -/

def ev (A : Analyzer α) (σ : AbsState α) :
    (n : Nat) → Tm n → Env n → Ctx → Table Addr (Value α) → StateM (AbsState α) (Value α)
  | _, .num k, _, _, _ => pure ⟨A.dom.ofInt k, []⟩
  | _, .input, _, _, _ => pure ⟨A.dom.top, []⟩
  | _, .var i, env, _, ref => pure (A.lookup σ (env.get i) ref)
  | n, .lam label param body, env, _, _ =>
    pure ⟨A.dom.bot, [{ n := n, label := label, param := param, body := body, env := env }]⟩
  | n, .arith op l r, env, ctx, ref => do
    let a ← A.ev σ n l env ctx ref
    let b ← A.ev σ n r env ctx ref
    pure ⟨A.dom.binop op a.num b.num, []⟩
  | n, .letE label name rhs body, env, ctx, ref => do
    let v ← A.ev σ n rhs env ctx ref
    let addr : Addr := ⟨label, name, ctx⟩
    modify fun d => A.writeStore d addr v
    let ref2 := ref.filter (fun p => p.1 != addr)
    A.ev σ (n + 1) body (Env.cons addr env) ctx ref2
  | n, .letrec label name rhs body, env, ctx, ref => do
    let addr : Addr := ⟨label, name, ctx⟩
    let env2 := Env.cons addr env
    let v ← A.ev σ (n + 1) rhs env2 ctx ref
    modify fun d => A.writeStore d addr v
    let ref2 := ref.filter (fun p => p.1 != addr)
    A.ev σ (n + 1) body env2 ctx ref2
  | n, .branch op l r t f, env, ctx, ref => do
    let va ← A.ev σ n l env ctx ref
    let vb ← A.ev σ n r env ctx ref
    -- written out twice: a local helper would hide `t`/`f` from the
    -- structural-recursion check
    let o1 ← match A.guardRef ref env l r va vb op with
      | some ref' => A.ev σ n t env ctx ref'
      | none => pure A.bot
    let o2 ← match A.guardRef ref env l r va vb op.neg with
      | some ref' => A.ev σ n f env ctx ref'
      | none => pure A.bot
    pure (A.vjoin o1 o2)
  | n, .app site fe ae, env, ctx, ref => do
    let fv ← A.ev σ n fe env ctx ref
    let av ← A.ev σ n ae env ctx ref
    let mut out := A.bot
    for cl in fv.clos do                                    -- every possible callee
      let c := ctx ++ [site]
      let ctx2 : Ctx := c.drop (c.length - A.params.k)      -- last k call sites
      let paddr : Addr := ⟨cl.label, cl.param, ctx2⟩
      let key : RetKey := (cl, ctx2)
      modify fun d => A.writeRet (A.writeStore d paddr av) key A.bot   -- bind arg, record demand
      out := A.vjoin out (Table.getD σ.ret key A.bot)       -- read the summary
    pure out

/-! ### One pass: `F` -/

/-- Evaluate the program and the body of every previously demanded key. -/
def step (A : Analyzer α) (σ : AbsState α) : Value α × AbsState α :=
  let pass : StateM (AbsState α) (Value α) := do
    let v ← A.ev σ 0 A.prog Env.nil [] []
    for p in σ.ret do
      let (cl, ctx2) := p.1
      let paddr : Addr := ⟨cl.label, cl.param, ctx2⟩
      let r ← A.ev σ (cl.n + 1) cl.body (Env.cons paddr cl.env) ctx2 []
      modify fun d => A.writeRet d (cl, ctx2) r
    pure v
  Id.run (pass.run {})

/-! ### Pointwise operations on states -/

section Tables
variable {κ : Type} [BEq κ]

/-- union of keys, join of values -/
def joinTbl (A : Analyzer α) (a b : Table κ (Value α)) : Table κ (Value α) :=
  List.foldl (fun acc p => Table.put acc p.1 (A.vjoin (Table.getD acc p.1 A.bot) p.2)) a b

/-- `new` must contain every key of `old` (it is `old ⊔ _`). -/
def widenTbl (A : Analyzer α) (old new : Table κ (Value α)) : Table κ (Value α) :=
  new.map (fun p => (p.1, A.vwiden (Table.getD old p.1 A.bot) p.2))

/-- Only keys already in `old` are narrowed. -/
def narrowTbl (A : Analyzer α) (old new : Table κ (Value α)) : Table κ (Value α) :=
  old.map (fun p =>
    (p.1, match Table.get? new p.1 with
          | some nv => A.vnarrow p.2 nv
          | none => p.2))

/-- `new ⊑ old`, keys included (a new key means a new demand). -/
def leTbl (A : Analyzer α) (new old : Table κ (Value α)) : Bool :=
  new.all (fun p =>
    match Table.get? old p.1 with
    | some ov => A.vle p.2 ov
    | none => false)

end Tables

def joinSt (A : Analyzer α) (a b : AbsState α) : AbsState α :=
  ⟨A.joinTbl a.store b.store, A.joinTbl a.ret b.ret⟩
def widenSt (A : Analyzer α) (old new : AbsState α) : AbsState α :=
  ⟨A.widenTbl old.store new.store, A.widenTbl old.ret new.ret⟩
def narrowSt (A : Analyzer α) (old new : AbsState α) : AbsState α :=
  ⟨A.narrowTbl old.store new.store, A.narrowTbl old.ret new.ret⟩
def leSt (A : Analyzer α) (new old : AbsState α) : Bool :=
  A.leTbl new.store old.store && A.leTbl new.ret old.ret

/-! ### The fixpoint (interface for the termination argument) -/

/-- Ascending phase: `σ' = σ ∇ (σ ⊔ F σ)` (plain `σ ⊔ F σ` during the first
`delay` rounds).  Returns the program value and the stable state, or `none`
if `fuel` ran out.

**TODO (termination).**  `fuel` is the placeholder.  The real argument: the
state lives in a finite-height lattice once widening is applied (finitely many
`Addr`/`RetKey`s because contexts are bounded by `k`, and the base domain's
widening has finite ascending chains), so `σ ↦ σ ∇ (σ ⊔ F σ)` reaches a
post-fixpoint.  Replace this by `termination_by`/`WellFounded.fix` over
that measure. -/
def ascend (A : Analyzer α) : Nat → Nat → AbsState α → Option (Value α × AbsState α)
  | 0, _, _ => none
  | fuel + 1, it, σ =>
    let (v, δ) := A.step σ
    let joined := A.joinSt σ δ
    if A.leSt joined σ then some (v, σ)
    else
      let σ' := if it ≥ A.params.delay then A.widenSt σ joined else joined
      A.ascend fuel (it + 1) σ'

/-- Descending phase: `σ' = σ Δ F σ`, `n` times.  Returns the value of the last
pass (or the supplied one if `n = 0`). -/
def descend (A : Analyzer α) : Nat → Value α → AbsState α → Value α × AbsState α
  | 0, v, σ => (v, σ)
  | n + 1, _, σ =>
    let (v, δ) := A.step σ
    A.descend n v (A.narrowSt σ δ)

def run (A : Analyzer α) : Option (Value α × AbsState α) :=
  match A.ascend A.params.maxIter 0 {} with
  | none => none
  | some (v, σ) => some (A.descend A.params.narrowPasses v σ)

/-! ### Construction and printing -/

def ofRaw (dom : Domain α) (params : Params) (r : Raw) : Except String (Analyzer α) := do
  let t ← r.close
  pure { dom := dom, params := params, prog := t }

def showValue (A : Analyzer α) (v : Value α) : String :=
  let numPart : List String :=
    if !A.dom.isBot v.num || v.clos.isEmpty then [A.dom.toStr v.num] else []
  let names := (v.clos.map (fun c => s!"λ{c.param}#{c.label}")).toArray.qsort
    (fun a b => decide (a < b))
  let closPart : List String :=
    if v.clos.isEmpty then [] else ["{" ++ String.intercalate ", " names.toList ++ "}"]
  String.intercalate " + " (numPart ++ closPart)

def showAddr (a : Addr) : String :=
  a.name ++ (if a.ctx.isEmpty then "" else "@" ++ String.intercalate "." (a.ctx.map toString))

def showStore (A : Analyzer α) (st : AbsState α) : String :=
  let items := st.store.map (fun p => (showAddr p.1, A.showValue p.2))
  let sorted := (items.toArray.qsort (fun x y => decide (x.1 < y.1))).toList
  String.intercalate ", " (sorted.map (fun p => s!"{p.1}={p.2}"))

end Analyzer

end AbsInt
