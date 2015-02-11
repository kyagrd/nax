%include lhs2TeX.fmt
%include agda.fmt
%include includelhs2tex.lhs
\begin{code}
-- instantiating to a plain regular list 

record Unit : Set where constructor <>

List' : Set -> Set
List' a = Path (λ i j -> a) <> <>
 
nil' : {a : Set} -> List' a
nil' = PNil

cons' : {a : Set} -> a -> List' a -> List' a
cons' = PCons

-- instantiating to a length indexed list

Vec : Set -> ℕ -> Set
Vec a n = Path (λ i j -> a) n zero

vNil : {a : Set} -> Vec a zero
vNil = PNil

vCons  : {a : Set} {n : ℕ} ->
         a -> Vec a n -> Vec a (suc n)
vCons = PCons
\end{code}
