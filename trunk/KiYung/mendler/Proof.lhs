\comment{
\begin{code}
{-# LANGUAGE RankNTypes, ImpredicativeTypes, StandaloneDeriving
           , TypeSynonymInstances #-}
{- F <=^{vec k -> *} G := forall vec x: vec k . F vec x -> G vec x -}
\end{code}
}

%format in0
\newcommand{\ProofCata}{
\begin{code}
type Mu0 f = forall a . (forall r . (r -> a) -> f r -> a) -> a

mcata0 :: (forall r . (r -> a) -> f r -> a) -> Mu0 f -> a
mcata0 phi r = r phi

in0 :: f (Mu0 f) -> Mu0 f
in0 r phi = phi (mcata0 phi) r
\end{code}
}

\newcommand{\ProofCataEx}{
\begin{tabular}{l||l}
$\!\!\!\!\!\!\!\!\!\!$
\begin{minipage}{.45\linewidth}
\begin{code}
data N c = Z | S c
type Nat = Mu0 N

zer = in0 Z
suc = in0 . S
\end{code}
\end{minipage} &
\begin{minipage}{.54\linewidth}
\begin{code}
n2i :: Nat -> Int
n2i = mcata0 phi where
  phi n2i' Z     = 0
  phi n2i' (S n) = 1 + n2i' n
\end{code}
\end{minipage}
\end{tabular}
}
