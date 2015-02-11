{-# LANGUAGE RankNTypes, GADTs #-}
import RecComb
vars = [ [i] | i <- ['a'..'z'] ] ++ [ i:show j | j<-[1..], i<-['a'..'z'] ] :: [String]

data ExpF r t where
  Lam :: (r () -> r ()) -> ExpF r ()
  App :: r () -> r () -> ExpF r ()
type Expr' a t = Rec1 ExpF a t
type Expr t = forall a . Expr' a t

type Exp' a = Expr' a ()
type Exp = Expr ()

lam :: (forall a . Exp' a -> Exp' a) -> Exp
lam e    = Roll1 (Lam e)
app :: Exp -> Exp -> Exp
app f e  = Roll1 (App f e)

{-
showExp :: Exp -> String
showExp e = msfcata0  phi e vars where
                       phi :: (([String] -> String) -> r) -> (r -> ([String] -> String)) -> ExpF r -> ([String] -> String)
                       phi inv show' (App x y)  = \vs      -> "("++ show' x vs ++" "++ show' y vs ++")"
                       phi inv show' (Lam z)    = \(v:vs)  -> "(\\"++v++"->"++ show' (z (inv (const v))) vs ++")"
-}
