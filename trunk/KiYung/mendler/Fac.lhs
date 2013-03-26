\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes, KindSignatures, NoMonoLocalBinds #-}

module Fac where
import RecComb hiding (mcata0, mcata1, mhist0, mhist1)
import Prelude hiding (succ, pred, tail)

plus :: Nat -> Nat -> Nat
plus = mcata0 phi where
  phi (+.) Z     m = m
  phi (+.) (S n) m = succ (n +. m)

times :: Nat -> Nat -> Nat
times = mcata0 phi where
  phi (*.) Z     _ = zero
  phi (*.) (S n) m = plus m (n *. m) 
\end{code}
\end{comment}

\newcommand{\mprimDef}{
\begin{code}
                        {-"~~~~~~~\textrm{out}"-}          {-"~~~~~~\textrm{cast}"-}          {-"~~~\begin{smallmatrix}\text{abstract}\\\text{recursive call}\end{smallmatrix}"-}
mcata0  :: (forall r    .                                                                     (           r    -> a    ) -> (f r    -> a    )) -> (Mu0 f    -> a    )
mcata1  :: (forall r i  .                                                                     (forall i.  r i  -> a i  ) -> (f r i  -> a i  )) -> (Mu1 f i  -> a i  )
mprim0  :: (forall r    .                                  (           r    -> Mu0 f    ) ->  (           r    -> a    ) -> (f r    -> a    )) -> (Mu0 f    -> a    )
mprim1  :: (forall r i  .                                  (forall i.  r i  -> Mu1 f i  ) ->  (forall i.  r i  -> a i  ) -> (f r i  -> a i  )) -> (Mu1 f i  -> a i  )
mhist0  :: (forall r    . (           r    -> f r    ) ->                                     (           r    -> a    ) -> (f r    -> a    )) -> (Mu0 f    -> a    )
mhist1  :: (forall r i  . (forall i. r i   -> f r i  ) ->                                     (forall i.  r i  -> a i  ) -> (f r i  -> a i  )) -> (Mu1 f i  -> a i  )
mcvpr0  :: (forall r    . (           r    -> f r    ) ->  (           r    -> Mu0 f    ) ->  (           r    -> a    ) -> (f r    -> a    )) -> (Mu0 f    -> a    )
mcvpr1  :: (forall r i  . (forall i.  r i  -> f r i  ) ->  (forall i.  r i  -> Mu1 f i  ) ->  (forall i.  r i  -> a i  ) -> (f r i  -> a i  )) -> (Mu1 f i  -> a i  )

{-""-}

mcata0  phi (In0  x)  = phi            (mcata0  phi) x
mcata1  phi (In1  x)  = phi            (mcata1  phi) x
mprim0  phi (In0  x)  = phi       id   (mprim0  phi) x
mprim1  phi (In1  x)  = phi       id   (mprim1  phi) x
mhist0  phi (In0  x)  = phi out0       (mhist0  phi) x
mhist1  phi (In1  x)  = phi out1       (mhist1  phi) x
mcvpr0  phi (In0  x)  = phi out0  id   (mcvpr0  phi) x
mcvpr1  phi (In1  x)  = phi out1  id   (mcvpr1  phi) x
\end{code}
}

\newcommand{\ExFac}{
\begin{code}
data N r = Z | S r
type Nat = Mu0 N
zero     = In0 Z
succ n   = In0 (S n)

{-""-}
factorial = mprim0 phi where
    phi cast fac Z      = succ zero
    phi cast fac (S n)  = times (succ (cast n)) (fac n)
\end{code}
}

\newcommand{\ExConstPred}{
\begin{code}
pred = mprim0 phi where
  phi cast pr Z      = zero
  phi cast pr (S n)  = cast n
\end{code}
}

\newcommand{\ExConstTail}{
\begin{code}
data L a r = N | C a r
type List a = Mu0 (L a)
nil        = In0 N
cons x xs  = In0 (C x xs)

tail = mprim0 phi where
  phi cast tl N         = nil
  phi cast tl (C x xs)  = cast xs
\end{code}
}

\newcommand{\ExLucas}{
\begin{code}
lucas = mcvpr0 phi where
  phi out cast luc Z      =   zero
  phi out cast luc (S n)  =
    case out n of
      Z     ->  succ zero
      S n'  ->  plus  (plus (luc n) (luc n'))
                      (cast n')
\end{code}
}
