\begin{comment}
\begin{code}
{-# LANGUAGE GADTs, RankNTypes, EmptyDataDecls, TypeFamilies, KindSignatures
           , NoMonoLocalBinds #-}

import RecComb
import Data.Maybe
type Name = String
type Env = [(Name, Int)]

{-
data Ret i where
  RetE :: (Env -> Int) -> Ret E
  RetD :: (Env -> Env) -> Ret D
-}
\end{code}
\end{comment}

\begin{code}
data D
data E

data DecExpF (r :: * -> *) (i :: *) where
  Def  :: Name -> r E  -> DecExpF r D
  Var  :: Name         -> DecExpF r E
  Val  :: Int          -> DecExpF r E
  Add  :: r E -> r E   -> DecExpF r E
  Let  :: r D -> r E   -> DecExpF r E

type Dec  = Mu1 DecExpF D
type Exp  = Mu1 DecExpF E

data family Ret i :: *
newtype instance Ret D  = RetD  (Env -> Env)
newtype instance Ret E  = RetE  (Env -> Int)

proj_D  f = \x -> case f x of RetD  f_D  -> f_D
proj_E  f = \x -> case f x of RetE  f_E  -> f_E

extev :: Mu1 DecExpF i -> Ret i
extev = mcata1 phi where
  phi :: (forall i . r i -> Ret i) -> DecExpF r i -> Ret i
  phi f (Def x e)    =
        RetD $ \env -> (x, ev e env) : env
                     where ev = proj_E f
  phi f (Var x)      =
        RetE $\env -> fromJust (lookup x env)
  phi f (Val v)      =
        RetE $\env -> v
  phi f (Add e1 e2)  =
        RetE $\env -> ev e1 env + ev e2 env
                     where ev = proj_E f

extend  :: Dec  -> Env -> Env
extend  = proj_D  extev

eval    :: Exp  -> Env -> Int
eval    = proj_E  extev
\end{code}

\begin{comment}
\begin{code}
names = mcata1' phi
  where
  phi :: (forall i . r i -> [Name]) -> DecExpF r i -> [Name]
  phi names' (Def x e)   = x : names' e
  phi names' (Var x)     = [x]
  phi names' (Val _)     = []
  phi names' (Add e1 e2) = names' e1 ++ names' e2
  phi names' (Let d e)   = names' d ++ names' e

evalh :: Exp -> Env -> Int
evalh = mhist1_ phi
  where
  phi :: (forall i . r i -> DecExpF r i) -> (r E -> Env -> Int)
       -> DecExpF r E -> Env -> Int
  phi out ev (Var x)     = \env -> fromJust (lookup x env)
  phi out ev (Val v)     = \env -> v
  phi out ev (Add e1 e2) = \env -> ev e1 env + ev e2 env
  phi out ev (Let d e)   = \env -> case out d of
                                      Def x e -> ev e $ (x, ev e env) : env
\end{code}
\end{comment}
