import Mathlib.Algebra.Group.Defs


-- Type constructors (needed for type inference)

def Reader (r : Type u) (a : Type u) := r → a


-- Monad

-- Failure Monad
instance : Monad Option where
  pure := some
  bind ma f := match ma with
    | none => none
    | some a => f a

-- Exception Monad
instance : Monad (Except e) where
  pure := .ok
  bind ma f := match ma with
    | .error e => .error e
    | .ok a => f a

-- Nondeterminism Monad
def listBind {α β : Type} (as : List α) (f : α → List β) : List β := match as with
  | [] => []
  | a :: rest_as => List.append (f a) (listBind rest_as f)
instance : Monad List where
  pure a := [a]
  bind := listBind

-- Reader Monad: r → α
instance {r : Type u} : Monad (Reader r) where
  pure a := fun _ => a
  bind ma mf := fun x:r => mf (ma x) x

-- Writer Monad: w × α
instance {w} [winst : Monoid w] : Monad (fun α => w × α) where
  pure a := ⟨winst.one, a⟩
  bind ma mf :=
    let a := ma.2
    let mb := mf a
    ⟨winst.mul ma.1 mb.1, mb.2⟩

-- Backtracking Monad ???
-- instance : Monad (Arrow r) where
--   pure a := λ_ => a
--   bind ma mf := fun x:r => mf (ma x) x

-- Continuation Monad
-- (k : a → r) → r
instance {r : Type u} : Monad (fun (α : Type v) => (α → r) → r) where
  pure a := fun k => k a
  bind {α β} (ma : (α → r) → r) (mf : α → (β → r) → r) := fun k => ma (fun a => (mf a) k)

-- Functor

instance myFunctorOption : Functor Option where
  map f optA := match optA with
    | none => none
    | some a => some (f a)

instance myFunctorList : Functor List where
  map := List.map

instance myFunctorReader : Functor (Reader r) where
  -- fmap : (α → β) → (r→α) → (r→β)
  map g f := fun x => g (f x)


-- Applicative

instance myApplicativeOption : Applicative Option where
  pure := some
  seq ff u_fa := match ff with
    | none => none
    | some f => match (u_fa ()) with
    | none => none
    | some a => some (f a)

def listAppOne (f : α → β) (as : List α) : List β :=
  match as with
  | [] => []
  | a :: rest_as => (f a) :: (listAppOne f rest_as)
def listApp (fs : List (α → β)) (as : List α) : List β :=
  match fs with
  | [] => []
  | f :: rest_fs => (listAppOne f as) ++ (listApp rest_fs as)
instance : Applicative List where
  pure a := [a]
  seq ff u_fa := listApp ff (u_fa ())

instance myApplicativeReader : Applicative (Reader r) where
  pure a := fun _ => a
  -- app := {α β : Type} : (r → (α→β)) → (r→α) → (r→β)
  seq ff u_fa := fun x => ff x (u_fa () x)

#min_imports
