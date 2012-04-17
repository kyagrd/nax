\begin{comment}
\begin{code}
import RecComb
import Prelude hiding(succ)
\end{code}
\end{comment}
%format fibm = fib"_{\!m}"
\begin{code}
data N r = Z | S r
type Nat = Mu0 N
zero     = In0 Z
succ n   = In0 (S n)

fibm = mhist0 phi where
  phi  out fib Z      = 0
  phi  out fib (S n)  =
         case out n of
           Z     -> 1
           S n'  -> fib n + fib n'
\end{code}
\begin{comment}
\begin{code}
data N' r = N' (r -> N r) (N r)
type Nat' = Mu0 N'

dropNat = mcata0 phi where
  phi dropN (N' _ Z)      = zero
  phi dropN (N' _ (S n))  = succ (dropN n)

liftNat p = mcata0 phi where
  phi liftN Z      = In0 (N' p Z)
  phi liftN (S n)  = In0 (N' p (S (liftN n)))


-- outNat :: Nat -> N Nat
outNat = mcata0 phi where
  phi outN Z     = Z
  phi outN (S n) = case outN n of
                     Z      -> S zero
                     (S n') -> S (succ n')

eqZer = mcata0 phi where
  phi eqZ Z     = True
  phi eqZ (S n) = False

predNat n = case outNat n of
              Z   -> zero
              S n -> succ n

outNNat' p n' = case outNat (dropNat n') of
                  Z   -> Z
                  S n -> S (liftNat p n)

predNat'OfNat :: Nat -> Nat' -> N Nat'
predNat'OfNat n = case outNat n of
                    Z   -> const Z
                    S m -> predNat'OfNat m

predNat' = undefined

z' = In0 ( N' (const Z) Z )
s' = In0 . N' predNat' . S

fibC = mcata0 phi where
  phi fib (N' _ Z)      = 1
  phi fib (N' p (S n))  =
    case p n of
      Z     -> fib n
      S n'  -> fib n + fib n'
\end{code}
\end{comment}
