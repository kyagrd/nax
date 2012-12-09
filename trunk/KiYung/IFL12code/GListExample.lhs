%format cons = "\textit{cons}\,"
\begin{code}
-- instantiating to a plain regular list

data Elem a i j where
  MkElem :: a -> Elem a () ()

type List' a = Path (Elem a) () ()

nil' = PNil {-"~"-} :: List' a

cons' :: a -> List' a -> List' a
cons' = PCons . MkElem

-- instantiating to a length indexed list

data Nat = Z | S Nat

data ElemV a i j where
  MkElemV :: a -> ElemV a (S n) n

type Vec a n = Path (ElemV a) n Z

vNil = PNil {-"~"-} :: Vec a Z

vCons :: a -> Vec a n -> Vec a (S n)
vCons = PCons . MkElemV
\end{code}
