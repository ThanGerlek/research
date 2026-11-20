abbrev Arrow.{u,v} (α : Type u) (β : Type v) := α → β


-- Monad

instance : Monad Option where
  pure := some
  bind ma f := match ma with
    | none => none
    | some a => f a

def listBind {α β : Type} (as : List α) (f : α → List β) : List β := match as with
  | [] => []
  | a :: rest_as => List.append (f a) (listBind rest_as f)

instance : Monad List where
  -- Non-determinism
  pure a := [a]
  bind := listBind

instance : Monad (Arrow r) where
  pure a := λ_ => a
  -- bind {α β : Type u} : (r→α) → (α → (r→β)) → (r→β)
  bind ma mf := fun x:r => mf (ma x) x


-- Functor

instance myFunctorOption : Functor Option where
  map f optA := match optA with
    | none => none
    | some a => some (f a)

instance myFunctorList : Functor List where
  map := List.map

instance myFunctorArrowR : Functor (Arrow r) where
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

instance myApplicativeArrowR : Applicative (Arrow r) where
  pure a := fun _ => a
  -- app := {α β : Type} : (r → (α→β)) → (r→α) → (r→β)
  seq ff u_fa := fun x => ff x (u_fa () x)
