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
data V r t where V :: (r t1 -> r t2) -> V r (t1 -> t2)
type Val t = Mu1 V t
val f = In1 (V f) 
{-""-}
type Phi f a = forall r. (forall i. a i -> r a i) -> (forall i. r a i -> a i) -> (forall i. f (r a) i -> a i)
{-""-}
evalHOAS :: Exp t -> Val t
evalHOAS e = msfcata1 phi e where
  phi :: Phi ExpF (Mu1 V)
  phi inv ev (Lam f) = val(\v -> ev (f (inv v)))
  phi inv ev (App e1 e2) = unVal(ev e1) (ev e2)
{-""-}
unVal :: Val (t1 -> t2) -> (Val t1 -> Val t2)
unVal (In1(V f)) = f
\end{code}
