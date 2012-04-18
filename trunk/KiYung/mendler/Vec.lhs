\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes, GADTs, EmptyDataDecls #-}
import RecComb

data Z
data S i
\end{code}
\end{comment}

\begin{code}
data V p r i where
  NV  :: V p r Z
  CV  :: p -> r i -> V p r (S i)

type Vec p i = Mu1 (V p) i

nilv        = In1 NV
consv x xs  = In1 (CV x xs)

copy :: Vec p i -> Vec p i
copy = mcata1 phi where
  phi :: (forall i . r i -> Vec p i) -> V p r i -> Vec p i
  phi cp NV         = nilv
  phi cp (CV x xs)  = consv x (cp xs)

switch2 :: Vec p i -> Vec p i
switch2 = mhist1 phi where
  phi  ::  (forall i . r i -> V p r i) ->
           (forall i . r i -> Vec p i) -> V p r i -> Vec p i
  phi out sw2  NV          =   nilv
  phi out sw2  (CV x xs)   =
                case out xs of
                  NV       ->  consv x nilv
                  CV y ys  ->  consv y (consv x (sw2 ys))
\end{code}
