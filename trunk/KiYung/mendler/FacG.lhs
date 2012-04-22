\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes, KindSignatures, NoMonoLocalBinds #-}

plus :: Nat -> Nat -> Nat
plus Zero     m = m
plus (Succ n) m = Succ (plus n m)

times :: Nat -> Nat -> Nat
times Zero     _ = Zero
times (Succ n) m = plus m (times n m)
\end{code}
\end{comment}

\newcommand{\ExFacG}{
\begin{code}
{-""-}
data Nat
  =  Zero
  |  Succ Nat

{-""-}
fac Zero      = Succ Zero
fac (Succ n)  = times (Succ n) (fac n)
\end{code}
}

\newcommand{\ExPredG}{
\begin{code}
{-""-}
pred Zero      = Zero
pred (Succ n)  = n
\end{code}
}

\newcommand{\ExTailG}{
\begin{code}
{-""-}
data List a
  =  Nil
  |  Cons a (List a)
{-""-}
tail Nil          = Nil
tail (Cons x xs)  = xs
\end{code}
}

\newcommand{\ExLucasG}{
\begin{code}
{-""-}
luc Zero      =   Zero
luc (Succ n)  =
   case n of
     Zero     ->  Succ Zero
     Succ n'  ->  plus  (plus (luc n) (luc n'))
                        n'
\end{code}
}
