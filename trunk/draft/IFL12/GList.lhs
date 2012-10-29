%include lhs2TeX.fmt
%include includelhs2tex.lhs

\begin{code}
{-"\underline{\textsc{Haskell}_{\phantom{g}}
   \textcolor{gray}{\texttt{+}\;\texttt{GADTs},\;\texttt{DataKind},\;\texttt{PolyKind}} }"-}

{-""-}
{-""-}
data Path x i j where
  PNil   :: Path x i i
  PCons  :: x i j  -> Path x j k
                   -> Path x i k

{-""-}
append :: Path x i j  -> Path x j k
                      -> Path x i k
append PNil            ys  = ys
append (  PCons x xs)  ys  =
          PCons x (append xs ys)
\end{code}
