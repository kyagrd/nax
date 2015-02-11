\begin{comment}
\begin{code}
{-# LANGUAGE GADTs, RankNTypes #-}
import RecComb
\end{code}
\end{comment}
\begin{code}
data ExpF r t where
  Lam :: (r t1 -> r t2) -> ExpF r (t1 -> t2)
  App :: r (t1 -> t2) -> r t1 -> ExpF r t2
type Exp' a t = Rec1 ExpF a t
type Exp t = forall a . Exp' a t
lam :: (forall a . Exp' a t1 -> Exp' a t2) -> Exp (t1 -> t2)
lam e    = Roll1 (Lam e)
app :: Exp (t1 -> t2) -> Exp t1 -> Exp t2
app e1 e2  = Roll1 (App e1 e2)
{-""-}
newtype Id a = MkId { unId :: a }
type Phi f a = forall r. (forall i. a i -> r a i) -> (forall i. r a i -> a i) -> (forall i. f (r a) i -> a i)
{-""-}
evalHOAS :: Exp t -> Id t
evalHOAS e = msfcata1 phi e where
  phi :: Phi ExpF Id
  phi inv ev (Lam f) = MkId(\v -> unId(ev (f (inv (MkId v)))))
  phi inv ev (App e1 e2) = MkId(unId(ev e1) (unId(ev e2)))
\end{code}
