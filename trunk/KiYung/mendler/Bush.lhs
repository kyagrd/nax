\comment{
\begin{code}
{-# LANGUAGE RankNTypes, NoMonoLocalBinds, ScopedTypeVariables #-}
import RecComb

newtype Ret  i = Ret  { unRet  :: (i -> Int) -> Int }
\end{code}
}
\newcommand{\BushSum}{
\begin{code}
data BushF r i  = NB  | CB i (r (r i))
type Bush i = Mu1 BushF i
nilb        = In1 NB
consb x xs  = In1 (CB x xs)

bsum :: Bush i -> (i -> Int) -> Int
bsum = unRet . bsumm

bsumm :: Bush i -> Ret i
bsumm = mcata1 phi where
  phi :: forall r i' . (forall i . r i -> Ret i) -> BushF r i' -> Ret i'
  phi bsum'  NB         = Ret (\ f -> 0)
  phi bsum'  (CB x xs)  = Ret (\ f ->
                        f x + bsum'' xs (\ ys -> bsum'' ys f))
               where  bsum'' :: r i -> (i -> Int) -> Int
                      bsum'' = unRet . bsum'
\end{code}
}
