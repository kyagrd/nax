\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes, KindSignatures, NoMonoLocalBinds #-}
import RecComb
\end{code}
\end{comment}
\begin{code}
mopenit0 :: (forall r. (a -> r a) -> (r a -> a) -> f (r a) -> a)
          -> (forall a. Rec0 f a -> Rec0 f a) -> (a -> a)
mopenit0 phi x v  =  msfcata phi (x (Inverse0 v))
  where
  msfcata :: (forall r. (a -> r a) -> (r a -> a) -> f (r a) -> a) -> Rec0 f a -> a
  msfcata phi (Roll0 x)     = phi Inverse0 (msfcata phi)  x
  msfcata phi (Inverse0 z)  = z

{-""-}
data E r = A r r | L (r -> r) -- base structure for HOAS
type Exp a = Rec0 E a
lam g      = Roll0 (L g)
app e1 e2  = Roll0 (A e1 e2)
{-""-}
-- |False| for |(\x->lam(\y->y))|, |True| for |(\x->lam(\y->x))|
freevarused :: (forall a. Exp a -> Exp a) -> Bool
freevarused e = mopenit0 phi e True
  where
  phi :: forall r. (Bool -> r Bool) -> (r Bool -> Bool) -> E(r Bool) -> Bool
  phi inv fvused (L g)      = fvused (g(inv False))
  phi inv fvused (A e1 e2)  = fvused e1 || fvused e2
\end{code}
