\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes, GADTs, EmptyDataDecls #-}
\end{code}
\end{comment}

\begin{code}
data Z
data S i

data Vec p i where
  NV  :: Vec p Z
  CV  :: p -> Vec p i -> Vec p (S i)

{-""-}
{-""-}
{-""-}

copy :: Vec p i -> Vec p i
copy NV         = NV
copy (CV x xs)  = CV x (copy xs)
{-""-}
{-""-}
{-""-}

switch2 :: Vec p i -> Vec p i
switch2  NV          =   NV
switch2  (CV x xs)   =
          case xs of
            NV       ->  CV x NV
            CV y ys  ->  CV y (CV x (switch2 ys))
\end{code}

