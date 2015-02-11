\begin{comment}
\begin{code}
import RecComb
\end{code}
\end{comment}
%format lenm = len"_{\!m}"
\begin{code}
data L p r = N | C p r
type List p = Mu0 (L p)
nil        = In0 N
cons x xs  = In0 (C x xs)

lenm :: List p -> Int
lenm = mcata0 phi where
  phi len N         = 0
  phi len (C x xs)  = 1 + len xs
\end{code}

\begin{comment}
\begin{code}
lenc = cata s where
  s N = 0
  s (C x xslen) = 1 + xslen

instance Functor (L p) where
  fmap s N        = N
  fmap s (C x xs) = C x (s xs)
\end{code}
\end{comment}
