\comment{
\begin{code}
{-# LANGUAGE RankNTypes, NoMonoLocalBinds, ScopedTypeVariables #-}
import RecComb

-- sumB :: Bush Int -> Int
-- sumB NB         = 0
-- sumB (CB b bs)  = b + sumB (reduceB sumB bs)

-- bsum :: (a -> Int) -> Bush a -> Int
-- bsum f NB         = 0
-- bsum f (CB x xs)  = f x + bsum (bsum f) xs
-- 
-- sumB :: Bush Int -> Int
-- sumB = bsum id
\end{code}
}

\newcommand{\BushSumG}{
\vspace*{1em}
\begin{code}
data Bush i  = NB  | CB i (Bush (Bush i))
{-""-}

bsum :: Bush i -> (i -> Int) -> Int
bsum NB         = (\ f -> 0)
bsum (CB x xs)  = (\ f ->
                f x + bsum xs (\ ys -> bsum ys f))

newtype Ret i = Ret { unRet :: (i -> Int) -> Int }

bsum' :: Bush i -> Ret i
bsum'  NB         = Ret (\ f -> 0)
bsum'  (CB x xs)  = Ret (\ f ->
                  f x + bsum'' xs (\ ys -> bsum'' ys f))
        where  bsum'' :: Bush i -> (i -> Int) -> Int                
               bsum'' = unRet . bsum'       
\end{code}
}

\comment{
phi::(forall i . r i -> f i),  x::BushF r i 
----------------------------------------------
mcata1 (f i = typ) phi x : f i

mcata1 (f i = (i -> Int) -> Int) phi xs
}

\comment{
\begin{code}
bs    = CB 1 bs'           :: Bush Int
bs'   = CB (CB 2 NB) bs''  :: Bush (Bush Int)
bs''                       :: Bush (Bush (Bush Int))
bs''  = CB (CB (CB 3 NB) (CB (CB (CB 4 NB) NB) NB)) NB
\end{code}
}
