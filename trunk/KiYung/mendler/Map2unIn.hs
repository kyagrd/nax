{-# LANGUAGE RankNTypes, KindSignatures, NoMonoLocalBinds #-}
{-# LANGUAGE StandaloneDeriving, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
import Data.List

data Mu f = In { unIn :: f(Mu f) }
instance Show (f(Mu f)) => Show (Mu f)
data Nu f = UnOut { out :: f(Nu f) }

iter :: (forall r. (r -> a) -> f r -> a) -> Mu f ->  a
iter s = s (iter s) . unIn

prim :: (forall r. (r -> Mu f) -> (r -> a) -> f r -> a) -> Mu f ->  a
prim s = s id (iter s) . unIn


coit :: (forall r. (a -> r) -> a -> f r) -> a -> Nu f
coit s = UnOut . s (coit s)

data L a r = N | C a r

type List a = Mu (L a)
nil :: List a
nil = In N
cons :: a -> List a -> List a
cons x xs = In (C x xs)

data S a r = SC a r
type Stream a = Nu (S a)
-- scons x xs = UnOut (SC x xs)
headS :: Stream a -> a
headS xs = case out xs of SC x _ -> x
tailS :: Stream a -> Stream a
tailS xs = case out xs of SC _ t -> t

upfrom = coit phi where
   phi upf n = n `SC` upf (n+1)

-- fibs = unfoldr (\(a,b) -> Just (a,(b,a+b))) (0,1)

fibs = coit phi (0,1) where
  phi f (a,b) = (a,b) `SC` f (b,a+b)

data N r = S r | Z deriving Show
type Nat = Mu N
instance Show Nat
z :: Nat
z = In Z
s :: Nat -> Nat
s = In . S

fibo n = iter phi n fibs where
  phi f Z     = fst . headS
  phi f (S n) = f n . tailS

mon2unIn :: (forall a b. (a -> b) -> f a ->  f b) -> Mu f -> f(Mu f)
mon2unIn m = prim phi where phi cast f x = m cast x


