{-# LANGUAGE GADTs, DataKinds, PolyKinds, TypeOperators, KindSignatures #-}

-- import Control.Monad
-- import Data.Maybe

data Nat = Z | S Nat

infixr :>
infixr :->
-- infixr :*:

data T = I | T :> T

data Ty :: T -> * where
  Iota :: Ty I
  (:->) :: Ty a -> Ty b -> Ty (a:>b)

data Tm :: T -> * where
  Var :: String -> Tm a
  Lam :: String -> Tm b -> Tm (a:>b)
  App :: Tm (a:>b) -> Tm a -> Tm b

data Val :: T -> * where
  Fun :: (Val a -> Val b) -> Val (a:>b)
  Syn :: Tm I -> Val I

vars = map (:[]) cs ++ [c:show n | c<-cs, n<-[0..]] where cs="xyz"

reflect :: Ty t -> Tm t -> Val t
reflect Iota        e = Syn e
reflect (t1 :-> t2) e = Fun (\v -> reflect t2 (App e (reify t1 vars v)))

reify :: Ty t -> [String] -> Val t -> Tm t
reify Iota        _      (Syn t) = t
reify (t1 :-> t2) (x:xs) (Fun v) = Lam x (reify t2 xs (v (reflect t1 (Var x))))

{-
type Ctx = [(String,Val)]

meaning :: Ctx -> Tm -> Val
meaning ctx (Var x)      = case lookup x ctx of Just v -> v
                                                Nothing -> undefined
meaning ctx (Lam x e)    = Fun (\v -> meaning ((x,v):ctx) e)
meaning ctx (App e1 e2)  = case meaning ctx e1 of
                             Fun v1 -> v1 (meaning ctx e2)
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
-}
