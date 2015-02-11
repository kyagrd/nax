\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes, KindSignatures, NoMonoLocalBinds #-}

import RecComb hiding (mcata0, mcata1, msfcata0, msfcata1)


mcata0     :: (forall r . (r -> a) -> (f r -> a)) -> Mu0 f -> a

mcata1     :: (forall r i. (forall i. r i -> a i) -> (f r i -> a i))
           -> Mu1 f i -> a i

msfcata0   :: (forall r . (a -> r a) -> (r a -> a) -> (f (r a) -> a))
           -> (forall a . Rec0 f a) -> a

msfcata1   :: (forall r i .   (forall i. a i -> r (a i) i) ->
                               (forall i. r (a i) i -> a i) ->
                               (f (r (a i)) i -> a i) )
            -> (forall a. Rec1 f (a i) i) -> a i
\end{code}
\end{comment}

\newcommand{\CataViaHisto}{
\begin{code}
mcata0    phi r = mhist0 (const phi) r
mcata1    phi r = mhist1 (const phi) r

msfcata0  phi r = msfhist0 (\inv _ -> phi inv) r
msfcata1  phi r = msfhist1 (\inv _ -> phi inv) r
\end{code}
}

