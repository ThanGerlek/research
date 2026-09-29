-- MyState

def MyState (σ : Type u) (α : Type v) := σ → (σ × α)

instance : Monad (MyState σ) where
  pure a := λs => ⟨s, a⟩
  -- app {α β} (mf : σ → (σ×(α→β))) (ma : σ→(σ×α)) : σ→(σ×β)
  -- bind {α β} (ma : σ→(σ×α)) (famb : α → (σ→(σ×β))) : σ→(σ×β)
  bind {α β} (ma : MyState σ α) (famb : α → MyState σ β) : MyState σ β :=
    λ(s:σ) =>
      let ⟨sa,a⟩ := ma s
      let mb := famb a
      let ⟨sab,b⟩ := mb sa
      ⟨sab, b⟩

def get : MyState σ σ := λs => ⟨s, s⟩
def put (s : σ) : MyState σ Unit := λ_ => ⟨s, ()⟩
def update (f : σ → σ) : MyState σ Unit := λs => ⟨f s, ()⟩


-- Writer

def Writer.{v} (α : Type v) := (List String) × α
instance monadWriter : Monad Writer where
  pure a := ⟨[], a⟩
  bind {α β} (ma : Writer α) (famb : α → Writer β) : Writer β :=
    let ⟨wa,a⟩ := ma
    let mb := famb a
    let ⟨wf,b⟩ := mb
    ⟨wa ++ wf, b⟩

def tell (log : List String) : Writer Unit := ⟨log, ()⟩
def execWriter (w : Writer α) : List String := w.1


-- MyStateT

def MyStateT.{u,v} (M) [Monad M] (σ : Type u) (α : Type v) := σ → M (σ × α)
instance monadStateT [minst : Monad M] : Monad (MyStateT M σ) where
  pure a := λs => minst.pure ⟨s, a⟩
  bind {α β} (ma : MyStateT M σ α) (famb : α → MyStateT M σ β) : MyStateT M σ β :=
--bind {α β} (ma : σ → W (σ×α)) (famb : α → (σ → W (σ×β))) : σ → W (σ×β) :=
    λ(s:σ) =>
      let Mpa := ma s
      minst.bind Mpa (λ (pa : σ×α) =>
        let ⟨sa, a⟩ := pa
        let mb := famb a
        let Mpb := mb sa
        Mpb)

def getT [minst : Monad M] : MyStateT M σ σ := λs => minst.pure ⟨s, s⟩
def putT [minst : Monad M] (s : σ) : MyStateT M σ Unit := λ_ => minst.pure ⟨s, ()⟩
def updateT [minst : Monad M] (f : σ → σ) : MyStateT M σ Unit := λs => minst.pure ⟨f s, ()⟩

-- Don't touch the state, but do this M-specific action
def lift (σ) {α β M} [minst : Monad M] (f : α → M β) : α → MyStateT M σ β := λa => λs =>
  let Mb := f a
  minst.bind Mb (λ (b:β) =>
    minst.pure ⟨s, b⟩)

def execStateT [minst : Monad M] (ma : MyStateT M σ α) (s : σ) : M σ := minst.map Prod.fst (ma s)
