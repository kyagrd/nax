%format :+: = +
%format inL = "\textit{in}_{\!"L"}"
%format inR = "\textit{in}_{\!"R"}"
%format caseSum = "\textit{case}_{"+"}"
\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes, ImpredicativeTypes, ScopedTypeVariables
           , TypeOperators #-}
import Prelude hiding (succ)
\end{code}
\end{comment}
\newcommand{\ProofSFCata}{
\begin{code}
type Rec0 f r a = (r a) :+: (((r a -> a) -> f (r a) -> a) -> a)

newtype Id x = Id { unId :: x }

msfcata  ::  (forall r . (a -> r a) -> (r a -> a) -> f (r a) -> a)
         ->  (forall a . Rec0 f Id a) -> a
msfcata phi x = caseSum x unId (\ f -> f (phi Id))

lift :: ((Id a -> a) -> f (Id a) -> a) -> Rec0 f Id a -> Id a
lift h x = caseSum x id (\ x -> Id(x h))
\end{code}
}

\newcommand{\SumDef}{
\begin{code}
type a :+: b =  forall c . (a ->  c) ->  (b -> c) ->  c
inL :: a -> (a:+:b) 
inL a = \ f g -> f a
inR :: b -> (a:+:b) 
inR b = \ f g -> g b
caseSum :: (a:+:b) -> (a -> c) -> (b -> c) -> c
caseSum x f g = x f g
\end{code}
}

\newcommand{\HOASshowFw}{
\begin{code}       
data ExpF x = App x x | Lam (x -> x)
type Exp' a = Rec0 ExpF Id a
type Exp = forall a . Exp' a
app :: Exp' a -> Exp' a -> Exp' a
app x y = inR (\h -> h unId (App (lift h x) (lift h y)))
lam :: (Exp' a -> Exp' a) -> Exp' a
lam f = inR (\h -> h unId (Lam (\x -> lift h(f(inL x))) ))

showExp:: Exp -> String
showExp e = msfcata phi e vars where 
  phi inv show' (App x y)  = \vs      ->
                "("++ show' x vs ++" "++ show' y vs ++")"
  phi inv show' (Lam z)    = \(v:vs)  ->
                "(\\"++v++"->"++ show'(z (inv (const v))) vs ++")"
\end{code}
}

\begin{comment}
\begin{code}
k = lam (\ x -> lam (\ y -> x))

vars =  [ [i] | i <- ['a'..'z'] ] ++
        [ i:show j | j<-[1..], i<-['a'..'z'] ]

data N r = Z | S r
type Nat' a = Rec0 N Id a
type Nat = forall a . Nat' a
zero:: Nat' a
zero = inR (\h -> h unId Z)
succ:: Nat' a -> Nat' a
succ x = inR (\h -> h unId (S (lift h x)))

n2i :: Nat -> Int
n2i = msfcata phi
  where phi _ n2i' Z      = 0
        phi _ n2i' (S n)  = 1 + n2i' n
\end{code}
\end{comment}
