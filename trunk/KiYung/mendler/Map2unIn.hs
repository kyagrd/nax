{-# LANGUAGE TypeFamilies, PolyKinds, KindSignatures, TypeOperators #-}
{-# LANGUAGE RankNTypes, NoMonoLocalBinds, GADTs #-}
{-# LANGUAGE StandaloneDeriving, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, DeriveFunctor #-}

newtype Mu0 f = In0 { unIn0 :: f(Mu0 f) }

mcvpr0 :: Functor f => (forall r. (r -> f r) ->
                              (r -> Mu0 f) ->
                              (r -> a) ->
                              (f r -> a) )
       -> Mu0 f -> a
mcvpr0 phi = phi unIn0 id (mcvpr0 phi) . unIn0

data N r   = S r   | Z  deriving Functor
type Nat = Mu0 N
data L a r = C a r | N  deriving Functor
type List a = Mu0 (L a)
data R a r = F a [r]    deriving Functor
type Rose a = Mu0 (R a)

unInN :: Mu0 N -> N(Mu0 N)
unInN = mcvpr0 (\ _ cast _ ->  fmap cast)
unInL :: Mu0(L a) -> (L a) (Mu0(L a))
unInL = mcvpr0 (\ _ cast _ ->  fmap cast)
unInR :: Mu0(R a) -> (R a) (Mu0(R a))
unInR = mcvpr0 (\ _ cast _ ->  fmap cast)

{-
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
mon2unIn m = prim (\ cast _ x -> m cast x)
-}
newtype Mu1 f i = In1 { unIn1 :: f(Mu1 f)i }

mcvpr1 :: Functor1 f =>
          (forall r j. Functor r =>
                       (forall i. r i -> f r i) ->
                       (forall i. r i -> Mu1 f i) ->
                       (forall i.r i -> a i) ->
                       (f r j -> a j) )
       -> Mu1 f i' -> a i'
mcvpr1 phi = phi unIn1 id (mcvpr1 phi) . unIn1

class Functor1 h where
  fmap1  :: Functor f => (forall i j. (i -> j) -> f i -> g j) -> (a -> b)
        -> h f a -> h g b
  -- fmap1 h = fmap1' (h id)

  fmap1' :: Functor f => (forall i. f i -> g i) -> (a -> b)
          -> h f a -> h g b
  fmap1' h = fmap1 (\f -> h . fmap f)

instance (Functor1 h, Functor f) => Functor (h f) where
   fmap = fmap1' id
       -- fmap1 (\f -> id . fmap f)

instance Functor (f (Mu1 f)) => Functor (Mu1 f) where
  fmap f = In1 . fmap f . unIn1

data P r i = PC i (r(i,i)) | PN

instance Functor1 P where
  fmap1 h f (PC x a) = PC (f x) (h (\(i,j) -> (f i,f j)) a)
  fmap1 _ _ PN = PN
--  fmap1' h f (PC x a) = PC (f x) (h $ fmap (\(a1,a2) -> (f a1,f a2)) a)
--  fmap1' _ _ PN = PN

 
unInP :: Mu1 P i -> P (Mu1 P) i
unInP = mcvpr1 (\ _ cast _ -> fmap1' cast id) {- phi where
  phi :: forall r i'. Functor r =>
                      (forall i. r i -> P r i) ->
                      (forall i. r i -> Mu1 P i) ->
                      (forall i. r i -> P (Mu1 P) i) ->
                      (P r i' -> P (Mu1 P) i')
  phi _ cast _ x = fmap1' cast id x
--  phi _ cast _ (PC x xs) = PC x (cast xs)
--  phi _ _    _ PN = PN
-} 
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

instance Functor1 B where
  fmap1 h f (BC x a) = BC (f x) (h (h f) a)
  fmap1 _ _ BN = BN
  -- fmap1' h f (BC x a) = BC (f x) (h $ fmap (h . fmap f) a)
  -- fmap1' _ _ BN = BN

unInB :: Mu1 B i -> B (Mu1 B) i
unInB = mcvpr1 (\ _ cast _ -> fmap1' cast id) {- phi where
  phi :: forall r i'. Functor r =>
                      (forall i. r i -> B r i) ->
                      (forall i. r i -> Mu1 B i) ->
                      (forall i. r i -> B (Mu1 B) i) ->
                      (B r i' -> B (Mu1 B) i')
  phi _ cast _ x = fmap1' cast id x
--  phi _ cast _ (BC x xs) = BC x (cast (fmap cast xs))
--  phi _ _    _ BN = BN
-}

{-
data X r = MkX ((r -> ()) -> r)

instance Functor X where
  fmap f (MkX h) = MkX (f . \g -> h (g . f))
-}
