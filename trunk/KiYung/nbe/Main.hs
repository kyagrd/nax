{-# LANGUAGE TypeOperators #-}
data Ty = B | Ty :-> Ty | Ty :*: Ty
    deriving Show
data Exp = Var String | Lam String Exp | App Exp Exp
         | Pair Exp Exp | Fst Exp | Snd Exp
    deriving Show

data Val = LAM (Val -> Val) | PAIR Val Val | SYN Exp

type Ctx = [(String,Val)]

reflect :: Ty -> Exp -> Val
reflect B           e = SYN e
reflect (t1 :-> t2) e = LAM (\v -> reflect t2 (App e (reify t1 v)))
reflect (t1 :*: t2) e = PAIR (reflect t1 (Fst e)) (reflect t2 (Snd e))

reify :: Ty -> Val -> Exp
reify B           (SYN t) = t
reify (t1 :-> t2) (LAM v) = Lam x (reify t2 (v (reflect t1 (Var x)))) where x = undefined
reify (t1 :*: t2) (PAIR v1 v2) = Pair (reify t1 v1) (reify t2 v2)

true  = SYN (Var "T")
false = SYN (Var "F")
