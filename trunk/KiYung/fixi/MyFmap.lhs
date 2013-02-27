\begin{code}
{-# LANGUAGE RankNTypes #-}

data F1 x = C1 (Int -> Bool)

instance Functor F1 where
  fmap f (C1 z) = C1 z

data F2 x = C2 x

instance Functor F2 where
  fmap f (C2 z) = C2 (f z)

data F3 x = C3 (([x] -> Bool) -> Maybe x)

instance Functor F3 where
  fmap z (C3 y) = C3 (\x -> fmap z (y (\x1-> x (fmap z x1))))

data F4 x = C4 ((forall y . [x] -> y) -> Maybe x)

instance Functor F4 where
  fmap z (C4 y) = C4 (\x -> fmap z (y (\x1-> x (fmap z x1))))

data F5 x = C5 (forall y . ([x] -> y) -> Maybe x)

instance Functor F5 where
  fmap z (C5 y) = C5 (\x -> fmap z (y (\x1-> x (fmap z x1))))

data F6 x = C6 (([x] -> ([x] -> Bool)) -> Maybe x)

instance Functor F6 where
  fmap z (C6 y) = C6 (\x -> fmap z (y (\x1 x2 -> x (fmap z x1) (fmap z x2))))
\end{code}
