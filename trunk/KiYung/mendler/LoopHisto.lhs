\comment{
\begin{code}
{-# LANGUAGE RankNTypes, KindSignatures, NoMonoLocalBinds #-}
import RecComb
\end{code}
}

%format coo0
%format coo1
\begin{code}
data FooF r = Noo | Coo (r -> r) r
type Foo = Mu0 FooF
noo       = In0 Noo
coo f xs  = In0 (Coo f xs)

lenFoo :: Foo -> Int
lenFoo = mcata0 phi where
  phi len Noo         =  0
  phi len (Coo f xs)  =  1 + len (f xs)

loopFoo :: Foo -> Int
loopFoo = mhist0 phi where
  phi out len Noo         =  0
  phi out len (Coo f xs)  =  case out xs of
                               Noo       -> 1 + len (f   xs)
                               Coo f' _  -> 1 + len (f'  xs)

foo :: Foo -- loops for |loopFoo|
foo = coo0 (coo1 noo) where   coo0 = coo id
                              coo1 = coo coo0
\end{code}

