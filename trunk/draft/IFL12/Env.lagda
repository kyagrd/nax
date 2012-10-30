\textsf{Agda}$\phantom{_{g_g}}$\hrule ~

\begin{code}
data Vec (a : Set) : ℕ -> Set where
  VNil  : {n : ℕ} -> Vec a n
  VCons : {n : ℕ} -> a -> Vec a n -> Vec a (suc n)

data Env {st} (res : st -> Set) : {n : ℕ} -> Vec st n -> Set where
   Empty  : Env res {0} VNil
   Extend : {n : ℕ} {x : st} {xs : Vec st n} ->
            res x -> Env res xs -> Env res {suc n} (VCons x xs)
\end{code}
