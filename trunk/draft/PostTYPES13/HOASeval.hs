{-# LANGUAGE GADTs, RankNTypes #-}
import RecComb

data ExpF r t where
  Lam :: (r a -> r b) -> ExpF r (a -> b)
  App :: r (a -> b) -> r a -> ExpF r b
type Exp' a t = Rec1 ExpF a t
type Exp t = forall a . Exp' a t
-- lam :: (Exp' a t1 -> Exp' a t2) -> Exp' a (t1 -> t2)
lam e    = Roll1 (Lam e)
-- app :: Exp (t1 -> t2) -> Exp t1 -> Exp t2
app f e  = Roll1 (App f e)

data Id a = MkId {unId :: a}

eval :: Exp t -> Id t
eval e = msfcata1 phi e where
  phi :: Phi1' ExpF Id
  phi inv ev (Lam f)   = MkId(\v -> unId(ev (f (inv (MkId v)))))
  phi inv ev (App f x) = MkId(unId(ev f) (unId(ev x)))
