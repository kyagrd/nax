{-# LANGUAGE DeriveFunctor, RankNTypes, StandaloneDeriving #-}
data F x = C (([x] -> Bool) -> Maybe x) deriving Functor

data F1 x = C1 ((forall y . [(y,x)] -> y) -> Maybe x) deriving Functor

data F2 x = C2 (forall y . ([x] -> y) -> [(y,x)]) -- deriving Functor

data F3 x = C3 (forall y . ([x] -> y) -> Maybe y) deriving Functor

data F4 x = C4 (forall y . ([x] -> y) -> (y,x)) deriving Functor

deriving instance Functor ((,) y)

-- instance Functor F where
--   fmap f (C g) = C (\h -> fmap f (g (h . fmap f)))

-- instance Functor F1 where
--   fmap f (C1 g) = C1 (\h -> fmap f (g (h . fmap (fmap f))))

instance Functor F2 where
  fmap f (C2 g) = C2 (\h -> fmap (fmap f) (g (h . fmap f)))

-- instance Functor F3 where
--   fmap f (C3 g) = C3 (\h -> (g (h . fmap f)))


data F' x = C' (([x] -> Bool) -> Maybe x) -- deriving Functor

unC' (C' g) = g

instance Functor F' where
--  fmap f (C' g) = C' (\h -> fmap f (g (h . fmap f)))
--  fmap f = C' . (\g h -> fmap f (g (h . fmap f))) . unC'
  fmap f = C' . (\g h -> (fmap f . g) (h . fmap f)) . unC'


data F'' x = C'' (([x] -> ([x] -> Bool)) -> Maybe x) -- deriving Functor
unC'' (C'' g) = g
instance Functor F'' where
  fmap f (C'' g) = C'' (\h -> fmap f (g (\x1 x2 -> h (fmap f x1) (fmap f x2))))
