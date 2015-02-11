\begin{code}
{-"\underline{\textsc{Agda}_{\phantom{g}}
              \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad}"-}

data Inst : List Ty -> List Ty -> Set where
  PUSH   : {t : Ty} {ts : List Ty} ->
           Val t -> Inst ts (t ∷ ts) 
  ADD    : {ts : List Ty } ->
           Inst (I ∷ I ∷ ts) (I ∷ ts)
  IFPOP  : {ts ts' : List Ty} ->
           Path Inst ts ts' ->
           Path Inst ts ts' ->
           Inst (B ∷ ts) ts'

Code : List Ty -> List Ty -> Set
Code sc sc' = Path Inst sc sc'

compile  : {t : Ty} -> {ts : List Ty} ->
           Expr t -> Code ts (t ∷ ts)
compile (VAL v)       =
  PCons (PUSH v) PNil
compile (PLUS e1 e2)  =
  append  (append  (compile e1) (compile e2)) 
          (PCons ADD PNil)
compile (IF e0 e1 e2)  =
  append  (compile e0)
          (PCons  (IFPOP  (compile e1)
                          (compile e2))
                  PNil)
\end{code}
