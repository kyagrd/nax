\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes, ImpredicativeTypes, ScopedTypeVariables #-}
import RecComb
\end{code}
\end{comment}
\begin{figure}
\begin{code}
data G p r =  N p [r] |  R (r -> r) |  S (r -> r) r 
type Graph p = forall a . Rec0 (G p) a
node v gs  = Roll0 (N v gs)
rec f      = Roll0 (R f)
share f g  = Roll0 (S f g)

flatG :: Graph a -> [a]
flatG = msfcata0 phi where
  phi inv flat (N v gs)  = v : concatMap flat gs
  phi inv flat (R f)     = flat (f (inv []))
  phi inv flat (S f g)   = flat (f g)

sumG :: Graph Int -> Int
sumG = msfcata0 phi where
  phi inv sumg (N n gs)  = n + sum (map sumg gs)
  phi inv sumg (R f)     = sumg (f (inv 0))
  phi inv sumg (S f g)   = sumg (f g)

g0 :: Graph Int -- \xy \xymatrix{ *++[o][F-]{0} \ar[r] \ar[dr] & *++[o][F-]{1} \ar[d] \ar@@(ur,dr) \\ & *++[o][F-]{2} \ar@@<1ex>[ul] } \POS(-3,+3)\xymatrix{x &   \\ & } \POS( 0,+3)\xymatrix{  & y \\ & } \POS( 6,-6)\xymatrix{  &  \\ & z} \POS(10,-6)\xymatrix{& |flatG g0 ~> [0,2,1,2]|}\POS(10,-10)\xymatrix{& |sumG g0 ~> 5|}\endxy
g0 =  rec(\x->
       share  (\z-> node 0  [z, rec(\y-> node 1 [y,z])])
              (node 2 [x]))
\end{code}
\caption{A graph datatype with cycles and sharing \cite{FegShe96}}
\label{fig:graph}
\end{figure}

\begin{comment}
-- newtype Ret a b = Ret { unRet :: (a -> b) -> Graph b }
{- -- mapG is not trivial to implement
mapG :: forall a b . Graph a -> Ret a b
mapG = msfcata0 phi where
  phi :: forall r . (Ret a b -> r (Ret a b)) -> (r (Ret a b) -> Ret a b)
      -> G a (r (Ret a b)) -> Ret a b
  phi inv mapg (N v gs)  = Ret$ \h-> node (h v) (map (flip(unRet.mapg) h) gs)
  phi inv mapg (R f)     = Ret$ \h-> rec (flip(unRet.mapg) h . f . inv )
--  phi inv mapg (S f g)   = Ret$ \h-> share (flip(unRet.mapg) h . f . undefined) ((unRet.mapg) g h)
-}
\end{comment}

