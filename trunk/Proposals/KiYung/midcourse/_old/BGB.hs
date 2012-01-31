{-# Language RankNTypes, ScopedTypeVariables #-}
data Rec f a = Roll (f (Rec f a)) | Inverse a

msfiter0 :: (forall r . (a -> r a) -> (r a -> a) -> f (r a) -> a)
         -> (forall a . Rec f a) -> a
msfiter0 phi x = msfiter phi x

msfiter :: (forall r . (a -> r a) -> (r a -> a) -> f (r a) -> a)
        -> Rec f a -> a
msfiter phi (Roll x)    = phi Inverse (msfiter phi) x
msfiter phi (Inverse z) = z


-- one free variable
mopeniter1 :: (forall r . (a -> r a) -> (r a -> a) -> f (r a) -> a)
           -> (forall a . Rec f a -> Rec f a) -> (a -> a)
mopeniter1 phi x1 a1 = mopeniter phi x1 a1

mopeniter :: (forall r . (a -> r a) -> (r a -> a) -> f (r a) -> a)
          -> (Rec f a -> Rec f a) -> (a -> a)
mopeniter phi x1 a1 = msfiter phi (x1 (Inverse a1))

data E r = A r r | L (r -> r)
type Exp a = Rec E a

freevarused :: (forall a . Exp a -> Exp a) -> Bool
freevarused e = mopeniter1 phi e True
  where
  phi inv fvused (A e1 e2) = fvused e1 || fvused e2
  phi inv fvused (L f)     = fvused (f (inv False))
{-
*Main> freevarused (\y -> Roll (L (\x -> x)))
False
*Main> freevarused (\y -> Roll (L (\x -> y)))
True
-}

-- msfprec0
msfprec0 :: (forall r . (r a -> Rec f a) -> (a -> r a) -> (r a -> a) -> f (r a) -> a)
         -> (forall a . Rec f a) -> a
msfprec0 phi x = msfprec phi x

msfprec :: (forall r . (r a -> Rec f a) -> (a -> r a) -> (r a -> a) -> f (r a) -> a)
        -> Rec f a -> a
msfprec phi (Roll x)    = phi id Inverse (msfprec phi) x
msfprec phi (Inverse z) = z

{-
app :: (forall a . Exp a) -> (forall a . Exp a) -> (forall a . Exp a)
app x y = Roll (A x y)
lam :: (forall a . Exp a -> Exp a) -> (forall a . Exp a)
lam g = Roll (L g)

-- data PAR a = PAR { par :: Exp a , apply :: Exp a -> Exp a }

parred :: (forall a . Exp a) -> (forall a . Exp a)
parred = msfprec0 phi where
  phi cast inv pred (L g)     = Roll (L (\x -> pred (g (inv x))))
  phi cast inv pred (A e1 e2) = Roll (A e1' e2')
                                where e1' = pred e1
                                      e2' = pred e2


msfprec0' :: (forall r . (r a -> (forall a . Rec f a)) -> (a -> r a) -> (r a -> a) -> f (r a) -> a)
         -> (forall a . Rec f a) -> a
msfprec0' = undefined

-- apply :: (forall a . Exp a) -> a -> (forall a . Exp a)
apply = msfprec0' phi where
  -- phi cast inv ap (L g)     = undefined
  phi cast inv ap (A e1 e2) = (app (cast e1) (cast e2))
-}
