{-# LANGUAGE GADTs, RankNTypes #-}
import RecComb

data ExpF r t where
  Lam :: (r a -> r b) -> ExpF r (a -> b)
  App :: r (a -> b) -> r a -> ExpF r b
type Exp' a t = Rec1 ExpF a t
type Exp t = forall a . Exp' a t
lam e    = Roll1 (Lam e)
app f e  = Roll1 (App f e)

newtype Id a = MkId { unId :: a }

type Phi f a = forall r . (forall i. a i -> r a i)
                       -> (forall i. r a i -> a i)   
                       -> (forall i. f (r a) i -> a i)

eval :: Exp t -> Id t
eval e = msfcata1 phi e where
  phi :: Phi ExpF Id
  phi inv ev (Lam f) = MkId(\v -> unId(ev (f (inv (MkId v)))))
  phi inv ev (App f x) = MkId(unId(ev f) (unId(ev x)))

