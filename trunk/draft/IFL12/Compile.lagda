%include lhs2TeX.fmt
%include agda.fmt
%include includelhs2tex.lhs

\begin{code}
data Inst : List Ty -> List Ty -> Set where
  PUSH   : {t : Ty} {ts : List Ty} ->
           Val t -> Inst ts (t ∷ ts) 
  ADD    : {ts : List Ty } ->
           Inst (I ∷ I ∷ ts) (I ∷ ts)
  IFPOP  : {ts ts' : List Ty} ->
           GList Inst ts ts' ->
           GList Inst ts ts' ->
           Inst (B ∷ ts) ts'

Code : List Ty -> List Ty -> Set
Code sc sc' = GList Inst sc sc'

compile  : {t : Ty} -> {ts : List Ty} ->
           Expr t -> Code ts (t ∷ ts)
compile (VAL v)       =
  GCons (PUSH v) GNil
compile (PLUS e1 e2)  =
  append  (append  (compile e1) (compile e2)) 
          (GCons ADD GNil)
compile (IF e e1 e2)  =
  append  (compile e)
          (GCons  (IFPOP  (compile e1)
                          (compile e2))
                  GNil)
\end{code}
