import Std.Data.HashMap
import Std.Data.HashSet

import Fixpoint.Cache.Defs

open Std


namespace Cache

/-! A demand-driven fixed-point cache.

    Each key holds one element of a lattice. `publish` replaces it with
    `widen old (join old v)` and wakes subscribers with the stored element.
    Subscribers are re-run when the element grows; a value that is already
    below the stored element is dropped.

    Expected laws (not proved):

    * `le bot a`
    * `le a (join a b)` and `le b (join a b)`
    * `le a b = true` and `le b c = true` implies `le a c = true`
    * `le a (widen a b)` and `le (join a b) (widen a b)`
    * ascending chains `aᵢ₊₁ = widen aᵢ bᵢ` stabilize

    `le a b = true` means `a` is known to be below `b`. An uncertain comparison
    must return `false`, so a growth is never missed.

    `normKey` is applied to every lookup. It must be idempotent. -/

/-- One cell: the element published so far, if any, and the waiting
    continuations (newest first). `none` means nothing has been published. -/
abbrev Entry (V : Type) := Option V × List (V → IO Unit)

/-- The memo table. Continuations live in `IO` because a state monad whose
    state contains `V → State → State` is not strictly positive. -/
structure Cache (K V : Type) [BEq K] [Hashable K] [Lattice V] where
  ref : IO.Ref (HashMap K (Entry V))
  normKey : K → K
  flushing : IO.Ref Bool
  dirty : IO.Ref (HashSet K)

/-- A computation receives the cache and a continuation, and calls that
    continuation once for each answer. -/
abbrev CacheM (K V : Type) [BEq K] [Hashable K] [Lattice V] (α : Type) :=
  Cache K V → (α → IO Unit) → IO Unit

def pureM {K V α} [BEq K] [Hashable K] [Lattice V] (a : α) : CacheM K V α :=
  fun _ κ => κ a

def bindM {K V α β} [BEq K] [Hashable K] [Lattice V]
    (c : CacheM K V α) (f : α → CacheM K V β) : CacheM K V β :=
  fun t κ => c t (fun a => f a t κ)

instance {K V} [BEq K] [Hashable K] [Lattice V] : Monad (CacheM K V) where
  pure := pureM
  bind := bindM
  map f c := bindM c (fun a => pureM (f a))
  seq f c := bindM f fun g => bindM (c ()) fun a => pureM (g a)

/-- Nondeterministic choice: run every computation against the same continuation. -/
def each {K V α} [BEq K] [Hashable K] [Lattice V]
    (cs : List (CacheM K V α)) : CacheM K V α :=
  fun t κ => cs.forM fun c => c t κ

/-- No answers. -/
def fail {K V α} [BEq K] [Hashable K] [Lattice V] : CacheM K V α :=
  each []

/-- Deliver the current element of every dirty key. A nested call, made from a
    subscriber, only records growth; the outer call loops until the dirty set
    stays empty. Each wave reads the element it sends, so a subscriber observes
    an ascending chain. -/
partial def flush {K V} [BEq K] [Hashable K] [Lattice V] (cache : Cache K V) : IO Unit := do
  if ← cache.flushing.get then
    pure ()
  else
    cache.flushing.set true
    let rec loop : IO Unit := do
      let dirty ← cache.dirty.get
      if dirty.isEmpty then
        pure ()
      else
        cache.dirty.set {}
        for key in dirty.toList do
          let s ← cache.ref.get
          match s[key]? with
          | some (some cur, conts) =>
            for κ in conts do
              κ cur
          | _ => pure ()
        loop
    loop
    cache.flushing.set false

/-- Publish `v` at `key`. The stored element becomes `widen old (join old v)`.
    A result already below the stored element is dropped. Otherwise subscribers
    are woken with the stored element. -/
def publish {K V} [BEq K] [Hashable K] [Lattice V]
    (cache : Cache K V) (key : K) (v : V) : IO Unit := do
  let key := cache.normKey key
  let s ← cache.ref.get
  let (cur, conts) := s.getD key (none, [])
  let old := cur.getD Lattice.bot
  let next := Lattice.widen old (Lattice.join old v)
  if Lattice.le next old then
    pure ()
  else
    cache.ref.set (s.insert key (some next, conts))
    let dirty ← cache.dirty.get
    cache.dirty.set (dirty.insert key)
    flush cache

/-- Demand the element at `key`.

    The first demand registers `κ`, then runs `body`. The body's continuation
    is `publish`, so every answer it returns is joined into the cell.
    A later demand registers `κ` and, if an element is present, delivers it
    once. -/
def demand {K V} [BEq K] [Hashable K] [Lattice V]
    (key : K) (body : Unit → CacheM K V V) : CacheM K V V := fun cache κ => do
  let key := cache.normKey key
  let s ← cache.ref.get
  match s[key]? with
  | none =>
    cache.ref.set (s.insert key (none, [κ]))
    body () cache (publish cache key)
  | some (cur, conts) =>
    cache.ref.set (s.insert key (cur, κ :: conts))
    match cur with
    | none => pure ()
    | some v => κ v

/-- Open recursion. `equation` receives the recursive function and must call it
    instead of recursing itself. `self k` demands `k`, producing answers by
    running `equation self k`. -/
partial def fix {K V} [BEq K] [Hashable K] [Lattice V]
    (equation : (K → CacheM K V V) → K → CacheM K V V) (k : K) : CacheM K V V :=
  demand k fun _ => equation (fix equation) k

/-- Run `c` against an empty table and return the table.
    `normKey` collapses keys before lookup; it defaults to the identity and
    must be idempotent. -/
def run {K V α} [BEq K] [Hashable K] [Lattice V]
    (c : CacheM K V α) (normKey : K → K := fun k => k) : IO (HashMap K (Entry V)) := do
  let ref ← IO.mkRef ({} : HashMap K (Entry V))
  let flushing ← IO.mkRef false
  let dirty ← IO.mkRef ({} : HashSet K)
  c { ref, normKey, flushing, dirty } (fun _ => pure ())
  ref.get


/-- Like `fix`, but the equation is written over a concrete answer type `C` with
    a Galois connection to the cache's abstract answer type.

    Normal `fix` requires the interpreter to be written over the same type as
    what the cache returns, so we get `K → CacheM K V V`. `gfix` generalizes that
    to `K → CacheM K V C`. But it still needs some way of converting between
    abstract cache-results and concrete interpreter-values. Hence, we need a
    Galois connection (encoded by the Abstraction typeclass): `elems` (aka γ),
    which concretizes a cell, and `inj` (aka α), which abstracts one answer.-/
partial def gfix {K V C} [BEq K] [Hashable K] [Lattice V] [Abstraction V C]
    (equation : (K → CacheM K V C) → K → CacheM K V C) (k : K) : CacheM K V C :=
  fun t κ =>
    demand k (fun _ t' κ' =>
        equation (gfix equation) k t' (fun c => κ' (Abstraction.inj c)))
      t (fun v => (Abstraction.elems v).forM κ)


end Cache
