{-# LANGUAGE RankNTypes, GADTs #-}
import RecComb
vars = [ [i] | i <- ['a'..'z'] ] ++ [ i:show j | j<-[1..], i<-['a'..'z'] ] :: [String]

data ExpF r where
  Lam :: (r -> r) -> ExpF r
  App :: r -> r -> ExpF r
type Exp' a = Rec0 ExpF a
type Exp = forall a . Exp' a

lam :: (forall a . Exp' a -> Exp' a) -> Exp
lam e = lam' e      where lam' e    = Roll0 (Lam e)
app :: Exp -> Exp -> Exp
app f e = app' f e  where app' f e  = Roll0 (App f e)

{-
showExp :: Exp -> String
showExp e = msfcata0  phi e vars where
                       phi :: (([String] -> String) -> r) -> (r -> ([String] -> String)) -> ExpF r -> ([String] -> String)
                       phi inv show' (App x y)  = \vs      -> "("++ show' x vs ++" "++ show' y vs ++")"
                       phi inv show' (Lam z)    = \(v:vs)  -> "(\\"++v++"->"++ show' (z (inv (const v))) vs ++")"
-}
