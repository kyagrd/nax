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
prim s = s id (prim s) . unIn


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


newtype Mu1 f i = In1 { unIn1 :: f(Mu1 f)i }

mcvpr1 :: Functor1 f =>
          (forall r i. Functor r =>
                       (forall i. r i -> f r i) ->
                       (forall i. r i -> Mu1 f i) ->
                       (forall i.r i -> a i) ->
                       (f r i -> a i) )
       -> Mu1 f i -> a i
mcvpr1 phi = phi unIn1 id (mcvpr1 phi) . unIn1

-- Mu1 P are not exactly functor but we can do things somehow like this

data P r i = PC i (r(i,i)) | PN

class Functor1 h where
  fmap1   :: Functor f => (forall i. f i -> g i)
          -> h f i -> h g i
  fmap1'  :: Functor f => (forall i. f i -> g i) -> (a -> b)
          -> h f a -> h g b
  fmap1' h f = fmap1 h . fmap f
  fmap1'' :: Functor f => (forall i j. (i -> j) -> f i -> g j) -> (a -> b)
          -> h f a -> h g b
  fmap1'' h f = fmap1' (h id) f

instance (Functor1 h, Functor f) => Functor (h f) where
   fmap f = fmap1' id f

instance Functor1 P where
  fmap1 h (PC x a) = PC x (h a)
  fmap1 _ PN = PN

instance Functor1 B where
  fmap1 h (BC x a) = BC x (h $ fmap h a)
  fmap1 _ BN = BN

-- instance Functor1 f => Functor (f (Mu1 f)) where
--   fmap f = fmap1' id f

instance Functor (f (Mu1 f)) => Functor (Mu1 f) where
  fmap f = In1 . fmap f . unIn1
 
unInP :: Mu1 P i -> P (Mu1 P) i
unInP = mcvpr1 phi where
  phi :: forall r i'. Functor r =>
                      (forall i. r i -> P r i) ->
                      (forall i. r i -> Mu1 P i) ->
                      (forall i. r i -> P (Mu1 P) i) ->
                      (P r i' -> P (Mu1 P) i')
  phi _ cast _ (PC x xs) = PC x (cast xs)
  phi _ _    _ PN = PN
  
data B r a = BC a (r(r a)) | BN

{-
bmap' :: Functor f =>
         (forall i j.(i -> j) -> f i -> g j) -> (a -> b) -> B f a -> B g b
bmap' _ _ BN = BN
bmap' h f (BC x xs) = BC (f x) (h id $ fmap (h f) xs)

bmap :: Functor f =>
        (forall i. f i -> g i) -> (a -> b) -> B f a -> B g b
bmap _ _ BN = BN
bmap h f (BC x xs) = BC (f x) (h $ fmap (h . fmap f) xs)
-}

unInB :: Mu1 B i -> B (Mu1 B) i
unInB = mcvpr1 phi where
  phi :: forall r i'. Functor r =>
                      (forall i. r i -> B r i) ->
                      (forall i. r i -> Mu1 B i) ->
                      (forall i. r i -> B (Mu1 B) i) ->
                      (B r i' -> B (Mu1 B) i')
  phi _ cast _ (BC x xs) = BC x (cast (fmap cast xs))
  phi _ _    _ BN = BN

