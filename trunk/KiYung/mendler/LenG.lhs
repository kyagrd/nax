\begin{code}
{-""-}
data List p
   =  N
   |  C p (List p)

{-""-}
len :: List p -> Int
len N         = 0
len (C x xs)  = 1 + len xs
\end{code}
