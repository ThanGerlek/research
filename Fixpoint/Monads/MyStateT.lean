import Mathlib.Algebra.Group.Monoid


-- Reader

def Reader.{u,v} (r : Type u) (α : Type v) := r → α

instance monadReader : Monad (Reader r) where
  pure a := fun _ => a
  -- bind (ma : r→α) (mf : α → (r→β)) : r→β
  bind {α β} (ma : r→α) (mf : α → (r→β)) := fun x => mf (ma x) x

def read : Reader r r := id  -- Is this even useful...?


-- Writer

def Writer.{v} (w : Type u) (α : Type v) := w × α

instance monadWriter [mndW : Monoid w] : Monad (Writer w) where
  pure a := ⟨mndW.one, a⟩
  bind {α β} (ma : Writer w α) (famb : α → Writer w β) : Writer w β :=
    let ⟨wa,a⟩ := ma
    let mb := famb a
    let ⟨wf,b⟩ := mb
    ⟨mndW.mul wa wf, b⟩

def tell (log : w) : Writer w Unit := ⟨log, ()⟩
def execWriter (wa : Writer w α) : w := wa.1


-- MyState (Reader composed with Writer)

-- Reader σ (Writer σ α) -- σ → (σ × α) The state monad
-- Writer σ (Reader σ α) -- σ × (σ → α) Not useful. The outer σ isn't a function of the
--                                      state transformation, so it can't depend on it,
--                                      and thus must be entirely independent of it.


def MyState σ α := Reader σ (Writer σ α) -- σ → (σ × α)

instance : Monad (MyState σ) where
  pure a := fun s => ⟨s, a⟩
  -- bind {α β} (ma : σ→(σ×α)) (famb : α → (σ→(σ×β))) : σ→(σ×β)
  bind {α β} (ma : MyState σ α) (famb : α → MyState σ β) : MyState σ β :=
    fun (s:σ) =>
      let ⟨sa,a⟩ := ma s
      let mb := famb a
      let ⟨sab,b⟩ := mb sa
      ⟨sab, b⟩

def get : MyState σ σ := fun s => ⟨s, s⟩
def put (s : σ) : MyState σ Unit := fun _ => ⟨s, ()⟩
def update (f : σ → σ) : MyState σ Unit := fun s => ⟨f s, ()⟩

def execState (m : MyState σ α) (s : σ) : σ := execWriter (m s)

def example1 : MyState String Nat := do
  let x ← (pure 3)
  let _ ← put "3"
  let x ← pure (x + 6)
  let s ← get
  let s ← pure (s ++ "+6")
  let _ ← put s
  return x
def result1 := execState example1 ""
-- #eval result1

-- MyStateT

def MyStateT.{u,v} (M) [Monad M] (σ : Type u) (α : Type v) :=
  Reader σ (M (Writer σ α))  -- σ → M (σ × α)
  -- Placement matters:
  -- σ → M (σ × α)    M's effects apply to the state (ex. nondeterminism means multiple envs)
  --                      Take in state, and return a computation that produces a state and a value
  -- σ → (σ × M α)    State is independent of M's effects (ex. global env, despite nondeterminism)
  --                      Take in state, and return state and a computation that produces a value
  -- M (σ → (σ × α))  Not useful. M runs once, then its result never changes.
  --                    A computation that produces a state transformer. (This isn't even a monad.)

instance monadStateT [minst : Monad M] : Monad (MyStateT M σ) where
  pure a := fun s => minst.pure ⟨s, a⟩
  bind {α β} (ma : MyStateT M σ α) (famb : α → MyStateT M σ β) : MyStateT M σ β :=
--bind {α β} (ma : σ → W (σ×α)) (famb : α → (σ → W (σ×β))) : σ → W (σ×β) :=
    fun (s:σ) =>
      let Mpa := ma s
      minst.bind Mpa (fun (pa : σ×α) =>
        let ⟨sa, a⟩ := pa
        let mb := famb a
        let Mpb := mb sa
        Mpb)

def getT [minst : Monad M] : MyStateT M σ σ := fun s => minst.pure ⟨s, s⟩
def putT [minst : Monad M] (s : σ) : MyStateT M σ Unit := fun _ => minst.pure ⟨s, ()⟩
def updateT [minst : Monad M] (f : σ → σ) : MyStateT M σ Unit := fun s => minst.pure ⟨f s, ()⟩

-- Don't touch the state, but do this M-specific action
def lift (σ) {α β M} [minst : Monad M] (f : α → M β) : α → MyStateT M σ β := fun a => fun s =>
  let Mb := f a
  minst.bind Mb (fun (b:β) =>
    minst.pure ⟨s, b⟩)

def execStateT [minst : Monad M] (ma : MyStateT M σ α) (s : σ) : M σ := minst.map Prod.fst (ma s)
