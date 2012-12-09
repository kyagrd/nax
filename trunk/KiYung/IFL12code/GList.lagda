\begin{code}
{-"\underline{\textsc{Agda}_{\phantom{g}}^{\phantom{A^k}}
              \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\quad~~} "-}
{-""-}
data Path {Ix : Set} (X : Ix -> Ix -> Set) : Ix -> Ix -> Set
  where
    PNil   : {i : Ix} -> Path X i i
    PCons  : {i j k : Ix} ->
             X i j -> Path X j k -> Path X i k

{-""-}

append : {Ix : Set} -> {X : Ix -> Ix -> Set} -> {i j k : Ix}
  {-"~~"-} -> Path X i j -> Path X j k -> Path X i k
append  PNil          ys  = ys
append  (PCons x xs)  ys  =
        {-"~"-}PCons x (append xs ys) 
\end{code}
