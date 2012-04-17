\begin{code}
{-""-}
data Nat
   =  Z
   |  S Nat

{-""-}
fib Z      = 0
fib (S n)  =
  case n of
    Z     -> 1
    S n'  -> fib n + fib n'
\end{code}

