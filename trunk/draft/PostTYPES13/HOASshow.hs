{-# LANGUAGE RankNTypes #-}
import RecComb
vars = [ [i] | i <- ['a'..'z'] ] ++ [ i:show j | j<-[1..], i<-['a'..'z'] ] :: [String] -- k    = lam(\x -> lam(\y -> x))

data ExpF r = Lam (r -> r) | App r r
type Exp' a = Rec0 ExpF a
type Exp = forall a . Exp' a
-- lam :: (Exp' a -> Exp' a) -> Exp' a
lam e    = Roll0 (Lam e)
-- app :: Exp -> Exp -> Exp
app f e  = Roll0 (App f e)

showExp :: Exp -> String
showExp e = msfcata0 phi e vars where
  phi :: Phi0' ExpF ([String] -> String)
  phi inv show' (App x y) = \vs    -> "("++ show' x vs ++" "
                                      ++ show' y vs ++")"
  phi inv show' (Lam z)   = \(v:vs)-> "(\\"++v++"."++
                                show' (z(inv(const v))) vs ++")"

