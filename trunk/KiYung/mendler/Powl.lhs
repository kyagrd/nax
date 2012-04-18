\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes, NoMonoLocalBinds, ScopedTypeVariables #-}
import RecComb
import Control.Arrow ( (***) )

newtype Ret  i = Ret  { unRet  :: (i -> Int) -> Int }
\end{code}
\end{comment}
\newcommand{\PowlSum}{
\begin{code}
data PowlF r i  = NP  | CP i (r (i,i))
type Powl i = Mu1 PowlF i
nilp        = In1 NP
consp x xs  = In1 (CP x xs)

psum :: Powl i -> (i -> Int) -> Int
psum = unRet . psumm

psumm :: Powl i -> Ret i
psumm = mcata1 phi where
  phi :: forall r i' . (forall i . r i -> Ret i) -> PowlF r i' -> Ret i'
  phi psum'  NP         = Ret (\ f -> 0)
  phi psum'  (CP x xs)  = Ret (\ f ->
                 f x + psum'' xs (\(x,y)->f x+f y))
             where  psum'' :: r i -> (i -> Int) -> Int
                    psum'' = unRet . psum'
\end{code}
}
