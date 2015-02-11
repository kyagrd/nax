{-# LANGUAGE GADTs, DataKinds, PolyKinds, TypeOperators, KindSignatures #-}

-- import Control.Monad
-- import Data.Maybe

data Nat = Z | S Nat

infixr :->
infixr :*:

data Ty :: * where
  Iota :: Ty
  (:->) :: Ty  -> Ty -> Ty
  (:*:) :: Ty -> Ty -> Ty
    deriving Show

data Tm = Var String | Lam String Tm | App Tm Tm
        | Pair Tm Tm | Fst Tm | Snd Tm
    deriving Show

data Val = LAM (Val -> Val) | PAIR (Val,Val) | SYN Tm

type Ctx = [(String,Val)]

vars = map (:[]) cs ++ [c:show n | c<-cs, n<-[0..]] where cs="xyz"

reflect :: Ty -> Tm -> Val
reflect Iota        e = SYN e
reflect (t1 :-> t2) e = LAM (\v -> reflect t2 (App e (reify t1 v vars)))
reflect (t1 :*: t2) e = PAIR (reflect t1 (Fst e), reflect t2 (Snd e))

reify :: Ty -> Val -> [String] -> Tm
reify Iota        (SYN t) _      = t
reify (t1 :-> t2) (LAM v) (x:xs) = Lam x (reify t2 (v (reflect t1 (Var x))) xs)
reify (t1 :*: t2) (PAIR(v1,v2)) ss = Pair (reify t1 v1 ss) (reify t2 v2 ss)

meaning :: Ctx -> Tm -> Val
meaning ctx (Var x)      = case lookup x ctx of Just v -> v
                                                Nothing -> undefined
meaning ctx (Lam x e)    = LAM (\v -> meaning ((x,v):ctx) e)
meaning ctx (App e1 e2)  = case meaning ctx e1 of
                             LAM v1 -> v1 (meaning ctx e2)
                             _ -> undefined
meaning ctx (Pair e1 e2) = PAIR (meaning ctx e1, meaning ctx e2)
meaning ctx (Fst e)      = case meaning ctx e of PAIR p -> fst p
                                                 _ -> undefined
meaning ctx (Snd e)      = case meaning ctx e of PAIR p -> snd p
                                                 _ -> undefined

nbe :: Ty -> Tm -> Tm
nbe t e = reify t (meaning [] e) vars

_x, _y, _z :: Tm
_x = Var "x"
_y = Var "y"
_z = Var "z"

k, s, skk :: Tm
k = Lam "x" $ Lam "y" $ _x
s = Lam "x" $ Lam "y" $ Lam "z" $ App (_x `App` _z) (_y `App` _z)
skk = App (App s k) k

tmSKK = nbe (Iota :-> Iota) skk

tmSKK' = nbe ((Iota :-> Iota) :-> (Iota :-> Iota)) skk

tmK = nbe (Iota :-> Iota :-> Iota) k

tmK' = nbe (Iota :-> (Iota :-> Iota) :-> Iota) k

tmK'' = nbe ((Iota :-> Iota) :-> Iota :-> (Iota :-> Iota)) k

tmS = nbe ((Iota :-> Iota :-> Iota) :-> (Iota :-> Iota) :-> Iota :-> Iota) s

