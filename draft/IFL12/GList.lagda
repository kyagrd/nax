%include lhs2TeX.fmt
%include agda.fmt
%include includelhs2tex.lhs
\begin{code}
data GList {I : Set} (X : I -> I -> Set) : I -> I -> Set
  where
    GNil   : {i : Ix} -> GList X i i
    GCons  : {i j k : Ix} ->
             X i j -> GList X j k -> GList X i k

{-""-}

append  : {Ix : Set} ->
          {X : Ix -> Ix -> Set} -> {i j k : Ix} ->
          GList X i j -> GList X j k -> GList X i k
append GNil ys            = ys
append  (GCons x xs)  ys  =
        {-"~"-}GCons x (append xs ys) 
\end{code}