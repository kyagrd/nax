\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes, KindSignatures, NoMonoLocalBinds #-}

module RecComb where
\end{code}
\end{comment}

\newcommand{\DataFix}{
\begin{code}
newtype  Mu0   (f :: *         -> *         )                    {-"~"-} = {-"~"-} In0    { out0     :: f (Mu0 f)        }
newtype  Mu1   (f :: (* -> *)  -> (* -> *)  )                 i  {-"~"-} = {-"~"-} In1    { out1     :: f (Mu1 f)     i  }
                                                              
data     Rec0  (f :: *         -> *         )  (a :: *)          {-"~"-} = {-"~"-} Roll0  { unRoll0  :: f (Rec0 f a)     }  | Inverse0 a
data     Rec1  (f :: (* -> *)  -> (* -> *)  )  (a :: * -> *)  i  {-"~"-} = {-"~"-} Roll1  { unRoll1  :: f (Rec1 f a)  i  }  | Inverse1 (a i)
\end{code}
}

\newcommand{\tti}{\begin{smallmatrix}\\\text{abstract inverse}\end{smallmatrix}}
\newcommand{\ttii}{\begin{smallmatrix}\\\text{abstract unroll}\end{smallmatrix}}
\newcommand{\ttiii}{\begin{smallmatrix}\\\text{abstract recursive call}\end{smallmatrix}}
\newcommand{\ttiiii}{\begin{smallmatrix}\\\text{combining function}\end{smallmatrix}}
\newcommand{\ttm}{\begin{smallmatrix}\\\text{input value}\end{smallmatrix}}
\newcommand{\tta}{$\!\!\!\!\!\!$\begin{smallmatrix}\\\text{answer}\end{smallmatrix}}

\newcommand{\TypesOfRecursiveCombinators}{
\begin{code}
                          {-"\tti"-}                         {-"\ttii"-}                              {-"\ttiii"-}                     {-"\ttiiii"-}              {-"\ttm"-}                     {-"\tta"-}
cata      :: Functor f => (                                                                                                            (f a        -> a    )) ->              Mu0 f          ->  a

mcata0    :: (forall r .  {-""-}                             {-""-}                                   (           r      -> a    ) ->  (f r        -> a    )) ->              Mu0 f          ->  a
mcata1    :: (forall r i.                                                                             (forall i.  r i    -> a i  ) ->  (f r i      -> a i  )) ->              Mu1 f i        ->  a i
mhist0    :: (forall r .                                     (             r      -> f r        ) ->  (           r      -> a    ) ->  (f r        -> a    )) ->              Mu0 f          ->  a
mhist1    :: (forall r i.                                    (forall i.    r i    -> f r i      ) ->  (forall i.  r i    -> a i  ) ->  (f r i      -> a i  )) ->              Mu1 f i        ->  a i
msfcata0  :: (forall r .    (           a    -> r a    ) ->  {-""-}                                   (           r a    -> a    ) ->  (f (r a)    -> a    )) ->  (forall a.  Rec0 f a    )  ->  a
msfcata1  :: (forall r i.   (forall i.  a i  -> r a i  ) ->  {-""-}                                   (forall i.  r a i  -> a i  ) ->  (f (r a) i  -> a i  )) ->  (forall a.  Rec1 f a i  )  ->  a i
msfhist0  :: (forall r .    (           a    -> r a    ) ->  (forall a .   r a    -> f (r a)    ) ->  (           r a    -> a    ) ->  (f (r a)    -> a    )) ->  (forall a.  Rec0 f a    )  ->  a
msfhist1  :: (forall r i.   (forall i.  a i  -> r a i  ) ->  (forall a i.  r a i  -> f (r a) i  ) ->  (forall i.  r a i  -> a i  ) ->  (f (r a) i  -> a i  )) ->  (forall a.  Rec1 f a i  )  ->  a i
\end{code}
}

\newcommand{\DefsOfRecursiveCombinators}{
$\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!$
\begin{minipage}{.55\linewidth}
\begin{code}
cata    s    (In0 x)             = s (fmap (cata s) x)
                               
mcata0  phi  (In0 x)             = phi                    (mcata0 phi)   x
mcata1  phi  (In1 x)             = phi                    (mcata1 phi)   x
                                                                   
mhist0  phi  (In0 x)             = phi           out0     (mhist0 phi)   x
mhist1  phi  (In1 x)             = phi           out1     (mhist1 phi)   x
                                                                   
msfcata0  phi r = msfcata phi r where
  msfcata phi (Roll0 x)          = phi Inverse0           (msfcata phi)  x
  msfcata phi (Inverse0 z)       = z

msfcata1  phi r = msfcata phi r  where
  msfcata  :: (forall  r i.  (forall i. a i -> r a i)
                       ->    (forall i. r a i -> a i)   
                       ->    (f (r a) i -> a i)        ) -> Rec1 f a i -> a i
  msfcata phi    (Roll1 x)       = phi Inverse1           (msfcata phi)  x
  msfcata phi    (Inverse1 z)    = z
\end{code}
\end{minipage}
\begin{minipage}{.5\linewidth}
\begin{code}
msfhist0  phi r = msfhist phi r  where
  msfhist  :: (forall r.  (a -> r a)
                      ->  (forall a . r a -> f (r a))  {-""-}
                      ->  (r a -> a)
                      ->  (f (r a) -> a)               ) ->  Rec0 f a        -> a
  msfhist phi    (Roll0 x)       = phi Inverse0  unRoll0  (msfhist phi)  x
  msfhist phi    (Inverse0 z)    = z

msfhist1  phi r = msfhist phi r  where
  msfhist  :: (forall  r i.  (forall i. a i -> r a i)
                       ->    (forall a i. r a i -> f (r a) i)  {-""-}
                       ->    (forall i. r a i -> a i)
                       ->    (f (r a) i -> a i)                ) ->  Rec1 f a i  -> a i
  msfhist phi    (Roll1 x)       = phi Inverse1  unRoll1  (msfhist phi)  x
  msfhist phi    (Inverse1 z)    = z
\end{code}
\end{minipage}
}

\begin{comment}
\begin{code}
mcata1'   :: (forall r i.                                                                                        (forall i.  r i        -> a) ->  (f r i          -> a)) ->              Mu1 f i            ->  a
mcata1' phi (In1 x)              = phi                    (mcata1' phi)  x

mhist1'   :: (forall r i.  (forall i.    r i        -> f r i          ) ->                                       (forall i.  r i        -> a  ) ->  (f r i          -> a  )) ->              Mu1 f i            ->  a
mhist1' phi (In1 x)              = phi           out1    (mhist1' phi)   x

mhist1_  :: (forall r  .  (forall i.    r i        -> f r i          ) ->                                       (r i        -> a  ) ->  (f r i          -> a  )) ->              Mu1 f i            ->  a
mhist1_ phi (In1 x)              = phi           out1    (mhist1_ phi)   x



type Phi0   f a = forall r . (    r   -> a  ) -> (f r   -> a  )
type Phi1 f a = forall r i.(forall i.r i -> a i) -> (f r i -> a i)

type Phi0'   f a = forall r . (     a  -> r a  ) ->
                         (     r a  -> a  ) -> (f (r a)   -> a  )
type Phi1' f a = forall r i.(forall i.a i -> r a i) ->
                         (forall i.r a i -> a i) -> (f (r a) i -> a i)

\end{code}
\end{comment}
