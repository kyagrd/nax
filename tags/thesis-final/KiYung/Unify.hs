module Unify where

import Data.List (find)

type Var = String

data Type = V Var | Iota | Type :-> Type deriving (Eq,Show)

type Subst = [(Var,Type)]
emptySubst :: Subst
emptySubst = []

type Query = (Type,Type)

uinfy :: [Query] -> Subst
uinfy qs = u emptySubst qs

-- u terminates since for each recursive call
-- either the flollwing quadruple measure reduces in the usual tuple ordering
--   ( # of variables in (unzip snd s) and qs,
--     # of :-> in qs,
--     # of q s.t. (V x,V y) where x>y or (t,V y) where t is not var in qs,
--     length qs )
-- or an error may be raised
u :: Subst -> [Query] -> Subst
u _ ((Iota,t@(_:->_)):_) = error("cannot unify Iota with "++show t)
u _ ((t@(_:->_),Iota):_) = error("cannot unify "++show t++" with Iota")
u s ((Iota,Iota):qs)         = u s qs -- remove trival query
u s ((V x,V y):qs) | x == y  = u s qs -- remove trival query
                   | x >  y  = u s ((V y,V x):qs) -- smaller vars to left
u s ((t1,V y):qs)            = u s ((V y,t1):qs)  -- vars to left
u s ((t1:->t1',t2:->t2'):qs) = u s ((t1,t2):(t1',t2'):qs) -- decompose
u s ((V x,t):qs) = case find (uncurry occurs) s' of
                     Just (x',t')  -> error(x'++" occurs in "++show t')
                     Nothing       -> u s' q'
                 where
                 s' = (x,t):substS x t s
                 q' = substQs x t qs
u s [] = s

-- soundness of unification
theorem :: Type -> Type -> Bool
theorem t1 t2 = t1' == t2'
	where
	s = uinfy [(t1,t2)]
	t1' = applySubst s t1
	t2' = applySubst s t2

-- helper functions (obviously terminates)
occurs :: Var -> Type -> Bool
occurs x (V y)      = x == y
occurs _ Iota       = False
occurs x (t1:->t2)  = occurs x t1 && occurs x t2

occursQ :: Var -> Query  -> Bool
occursQ x (t1,t2) = occurs x t1 && occurs x t2

occursQs :: Var -> [Query] -> Bool
occursQs x = all (occursQ x)

subst :: Var -> Type -> Type -> Type
subst _ _ Iota = Iota
subst x ty t@(V y) = if x == y then ty else t
subst x ty (t1 :-> t2) = subst x ty t1 :-> subst x ty t2

substS :: Var -> Type -> Subst -> Subst
substS x ty s = [(y,subst x ty t) | (y,t) <- s]

substQ :: Var -> Type -> Query -> Query
substQ x ty (ty1,ty2) = (subst x ty ty1,subst x ty ty2)

substQs :: Var -> Type -> [Query] -> [Query]
substQs x ty = map (substQ x ty)

applySubst :: Subst -> Type -> Type
applySubst = foldr (.) id . map (uncurry subst)

