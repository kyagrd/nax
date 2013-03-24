{-# LANGUAGE GADTs, RankNTypes, NoMonoLocalBinds,
             NoMonomorphismRestriction, KindSignatures #-}

data     Rec0  (f :: *         -> *         )  a     = Roll0  { unRoll0  :: f (Rec0 f a)     }  | Inverse0 a
data     Rec1  (f :: (* -> *)  -> (* -> *)  )  a  i  where
  Roll1 :: f (Rec1 f a)  i  -> Rec1 f a i
  Inverse1 :: a i -> Rec1 f a i

unRoll1 (Roll1 x) = x

msfcata0  :: (forall r . (a   -> r a) ->  
                         (r a -> a  ) ->
                         (f (r a) -> a) ) -> (forall a . Rec0 f a)  ->  a
msfcata0  phi r = msfcata phi r where
  msfcata ::  (forall r . (a   -> r a) ->  
                          (r a -> a  ) ->
                          (f (r a) -> a) ) -> Rec0 f a  ->  a
  msfcata phi (Roll0 x)     = phi Inverse0  (msfcata phi)  x
  msfcata phi (Inverse0 z)  = z

msfcata1  :: (forall r . (forall i. a i  -> r a i  ) ->
                         (forall i. r a i  -> a i  ) ->
                         (forall i. f (r a) i  -> a i  ) )
          -> (forall a.  Rec1 f a i  )  ->  a i
msfcata1  phi r = msfcata phi r  where
  msfcata  :: (forall  r.  (forall i. a i -> r a i)
                       ->  (forall i. r a i -> a i)   
                       ->  (forall i. f (r a) i -> a i) )
           ->  Rec1 f a i  -> a i
  msfcata phi    (Roll1 x)       = phi Inverse1           (msfcata phi)  x



{-
data ExpF r = Lam (r -> r) | App r r
type Exp' a = Rec0 ExpF a
type Exp = forall a . Exp' a
lam e    = Roll0 (Lam e)
app f e  = Roll0 (App f e)

showExp :: Exp -> String
showExp e = msfcata0  phi e vars where
                       phi :: (([String] -> String) -> r) -> (r -> ([String] -> String)) -> ExpF r -> ([String] -> String)
                       phi inv show' (App x y)  = \vs      -> "("++ show' x vs ++" "++ show' y vs ++")"
                       phi inv show' (Lam z)    = \(v:vs)  -> "(\\"++v++"->"++ show' (z (inv (const v))) vs ++")"


vars = [ [i] | i <- ['a'..'z'] ] ++ [ i:show j | j<-[1..], i<-['a'..'z'] ] :: [String]
-}

data ExpF r t where
  Lam :: (r a -> r b) -> ExpF r (a -> b)
  App :: r (a -> b) -> r a -> ExpF r b
type Exp' a t = Rec1 ExpF a t
type Exp t = forall a . Exp' a t
lam e    = Roll1 (Lam e)
app f e  = Roll1 (App f e)

newtype Id a = MkId { unId :: a }

type Phi f a = forall r . (forall i. a i -> r a i)
                       -> (forall i. r a i -> a i)   
                       -> (forall i. f (r a) i -> a i)

eval :: Exp t -> Id t
eval e = msfcata1 phi e where
  phi :: Phi ExpF Id
  phi inv ev (Lam f) = MkId(\v -> unId(ev (f (inv (MkId v)))))
  phi inv ev (App f x) = MkId(unId(ev f) (unId(ev x)))

