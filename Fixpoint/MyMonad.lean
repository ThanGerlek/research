-- Monad

class MyMonad.{u,v} (m : Type u → Type v) where
  pur : α → m α
  bind : m α → (α → m β) → m β

class MyLawfulMonad.{u,v} m extends MyMonad.{u,v} m where
  -- Left identity
  -- The "minimally contextualize" fn, composed with another ctx'ing fn, is that other ctx'ing fn.
  h_bind_lid : bind (pur x) f = f x
  -- Right identity
  -- A ctx'ing fn, composed with the "minimally contextualize" fn, is that first ctx'ing fn.
  h_bind_rid {ma : m α} : bind ma pur = ma
  -- Associativity
  -- Composing ctx'ing fns is associative.
  h_bind_assoc {ma} : bind ma (fun x => bind (f x) g) = bind (bind ma f) g


-- Functor

class MyFunctor (f : Type u → Type v) where
  fmap : (α → β) → (f α) → (f β)

class MyLawfulFunctor f extends MyFunctor f where
  -- Mapping the id function over a ctx leaves that ctx unchanged.
  h_fmap_id : fmap (id : α → α) a = id a

-- Applicative

class MyApplicative.{u,v} (f : Type u → Type v) extends MyFunctor f where
  pur : α → f α
  app : f (α → β) → f α → f β

class MyLawfulApplicative f extends MyApplicative f where
  -- identity: (pure id) * v = v
  -- Ctx'd id, applied to a ctx'd val, leaves the ctx'd val unchanged.
  h_app_id : app (pur id) v = v
  -- composition: (pure (.) * f * g) * x = f * (g * x)
  -- A ctx'd "composition operator", being applied to two ctx'd fns and then a ctx'd val,
  -- is the same as applying the first ctx'd fn to (the second ctx'd fn applied to the ctx'd val).
  h_app_comp : app (app (app (pur (fun a b x => a (b x))) u) v) w = app u (app v w)
  -- homomorphism: (pure f) * (pure x) = pure (f x)
  -- A ctx'd fn, applied to a ctx'd val, is a ctx'd version of (the fn applied to the val).
  h_mrph {g : α → β} {x : α} : app (pur g) (pur x) = pur (g x)
  -- interchange: u * pure y = pure (· y) * u
  -- A ctx'd fn applied to a ctx'd val, is the same as
  -- a ctx'd "operate-on-the-value" fn applied to the ctx'd fn.
  -- Effectively, (f ·) x = (· x) f
  h_intr : app u (pur y) = app (pur (· y)) u
  -- fmap: fmap g x = pure g * x
  -- Mapping a fn over a ctx'd val is the same as a ctx'd version of the fn applied to the ctx'd val.
  h_app_fmap : fmap g x = app (pur g) x


-- Equivalence

instance monadMyMonad [minst : MyMonad m] : Monad m where
  pure := minst.pur
  bind := minst.bind
instance myMonadMonad [Monad m] : MyMonad m where
  pur := pure
  bind := bind

instance functorMyFunctor [minst : MyFunctor m] : Functor m where
  map := minst.fmap
instance myFunctorFunctor [minst : Functor m] : MyFunctor m where
  fmap := minst.map

instance applicativeMyApplicative [minst : MyApplicative m] : Applicative m where
  pure := minst.pur
  seq mf fma := minst.app mf (fma ())
instance myApplicativeApplicative [minst : Applicative m] : MyApplicative m where
  pur := pure
  app mf ma := minst.seq mf (λ_ => ma)
