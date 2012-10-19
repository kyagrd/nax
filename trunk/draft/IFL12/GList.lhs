%include lhs2TeX.fmt
%include includelhs2tex.lhs

\begin{code}
{-"\underline{\textsc{Haskell}_{\phantom{g}}
   \textcolor{gray}{\texttt{+}\;\texttt{GADTs},\;\texttt{DataKind},\;\texttt{PolyKind}} }"-}

{-""-}
{-""-}
data GList x i j where
  GNil   :: GList x i i
  GCons  :: x i j  -> GList x j k
                   -> GList x i k

{-""-}
append :: GList x i j  -> GList x j k
                       -> GList x i k
append GNil            ys  = ys
append (  GCons x xs)  ys  =
          GCons x (append xs ys)
\end{code}
