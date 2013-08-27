{-# LANGUAGE RankNTypes #-}
import RecComb

data ExpF r = Lam (r -> r) | App r r

type Expr = Mu0 ExpF
-- lam :: (Exp' a -> Exp' a) -> Exp' a
lam e    = Roll0 (Lam e)
-- app :: Exp -> Exp -> Exp
app f e  = Roll0 (App f e)

type Exp' a = Rec0 ExpF a
type Exp = (forall a. Exp' a)  -- (forall a. Rec0 E a)

exp2expr :: Exp -> Expr   -- (forall a. Rec0 E a) -> Mu0 E
exp2expr = msfcata0 phi where
  phi inv p2r (Lam f)   = In0(Lam(\x -> p2r (f (inv x))))
  phi inv p2r (App e1 e2) = In0(App (p2r e1) (p2r e2))
