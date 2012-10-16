%include lhs2TeX.fmt
%include includelhs2tex.lhs
%format cons = "\textit{cons}\,"
\begin{code}
-- instantiating to a plain list

data Elem a i j where
  MkElem :: a -> Elem a () ()

type List a = GList (Elem a) () ()

nil = GNil {-"~"-} :: List a

cons :: a -> List a -> List a
cons = GCons . MkElem

-- instantiating to a length indexed list

data Nat = Z | S Nat

data ElemV a i j where
  MkElemV :: a -> ElemV a (S n) n

type Vec a n = GList (ElemV a) n Z

vNil = GNil {-"~"-} :: Vec a Z

vCons :: a -> Vec a n -> Vec a (S n)
vCons = GCons . MkElemV
\end{code}
