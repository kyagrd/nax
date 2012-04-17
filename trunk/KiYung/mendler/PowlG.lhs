\comment{
\begin{code}
{-# LANGUAGE RankNTypes, NoMonoLocalBinds #-}
\end{code}
}




\newcommand{\PowlSumG}{
\vspace*{1em}
\begin{code}
data Powl i = NP | CP i (Powl (i,i))
{-""-}

psum :: Powl i -> (i -> Int) -> Int
psum  NP         = \ f -> 0
psum  (CP x xs)  = \ f ->
          f x + psum xs (\(x,y)->f x+f y)

newtype Ret i = Ret { unRet :: (i -> Int) -> Int }

psum' :: Powl i -> Ret i
psum'  NP         = Ret (\ f -> 0)
psum'  (CP x xs)  = Ret (\ f ->
           f x + psum'' xs (\(x,y)->f x+f y))
       where  psum'' :: Powl i -> (i -> Int) -> Int
              psum'' = unRet . psum'
\end{code}
}

\comment{
\begin{code}
ps    = CP 1 ps'             :: Powl Int
ps'   = CP (2,3) ps''        :: Powl (Int,Int)
ps''  = CP ((4,5),(6,7)) NP  :: Powl ((Int,Int),(Int,Int))
\end{code}
}
