%include lhs2TeX.fmt
%include agda.fmt
%include includelhs2tex.lhs
\begin{code}
-- instantiating to a plain list 

record Unit : Set where constructor <>

List' : Set -> Set
List' a = GList (λ i j -> a) <> <>
 
nil : {a : Set} -> List' a
nil = GNil

cons : {a : Set} -> a -> List' a -> List' a
cons = GCons

-- instantiating to a length indexed list

Vec : Set -> ℕ -> Set
Vec a n = GList (λ i j -> a) n 0

vNil : {a : Set} -> Vec a 0
vNil = GNil

vCons  : {a : Set} {n : ℕ} ->
         a -> Vec a n -> Vec a (1 + n)
vCons = GCons
\end{code}
