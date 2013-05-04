\begin{comment}
\begin{code}
{-# LANGUAGE RankNTypes #-}
import RecComb
\end{code}
\end{comment}
\newcommand{\varsDef}{
\begin{code}
vars = [ [i] | i <- ['a'..'z'] ] ++ [ i:show j | j<-[1..], i<-['a'..'z'] ] :: [String]
\end{code}
}
%format Exp_g = Exp"_{\!g}"
%format Var_g = Var"_{\!g}"
%format Lam_g = Lam"_{  g}"
%format App_g = App"_{\!g}"
%format showExp_g = showExp"_{\!g}"
\newcommand{\ExpGFig}{
\begin{code}
data Exp_g = Lam_g (Exp_g -> Exp_g) | App_g Exp_g Exp_g | Var_g String

showExp_g :: Exp_g -> String
showExp_g e = show' e vars where  show' (App_g x y)  = \vs      -> "("++ show' x vs ++" "++ show' y vs ++")"
                                  show' (Lam_g z)    = \(v:vs)  -> "(\\"++v++"->"++ show' (z (Var_g v)) vs ++")"
                                  show' (Var_g v)    = \vs      -> v
\end{code}
}
%format ExpF_m = ExpF"\!_m"
%format Exp_m = Exp"_{\!m}"
%format Var_m = Var"_{\!m}"
%format Lam_m = Lam"_{  m}"
%format App_m = App"_{\!m}"
%format var_m = var"_{\!m}"
%format lam_m = lam"_{  m}"
%format app_m = app"_{\!m}"
%format showExp_m = showExp"_{\!m}"
\newcommand{\ExpMFig}{
\begin{code}
data ExpF_m r =  Var_m String | Lam_m (String -> r) (r -> r) | App_m r r
type Exp_m = Mu0 ExpF_m
var_m x    = In0 (Var_m x)
lam_m e    = In0 (Lam_m var_m e)
app_m f e  = In0 (App_m f e)

showExp_m :: Exp_m -> String
showExp_m e = mcata0 phi e vars
  where  phi :: (r -> ([String] -> String)) -> ExpF_m r -> ([String] -> String)
         phi show' (App_m x y)   = \vs      -> "("++ show' x vs ++" "++ show' y vs ++")"
         phi show' (Lam_m mk z)  = \(v:vs)  -> "(\\"++v++"->"++ show' (z (mk v)) vs ++")"
         phi show' (Var_m x)     = \vs      -> x
\end{code}
}
\newcommand{\ExpFig}{
\begin{code}
data ExpF r = Lam (r -> r) | App r r
type Exp' a = Rec0 ExpF a
type Exp = forall a . Exp' a
-- lam :: (forall Exp' a -> Exp' a) -> Exp
lam e    = Roll0 (Lam e)
-- app :: Exp -> Exp -> Exp
app f e  = Roll0 (App f e)

showExp :: Exp -> String
showExp e = msfcata0  phi e vars where
                       phi :: (([String] -> String) -> r) -> (r -> ([String] -> String)) -> ExpF r -> ([String] -> String)
                       phi inv show' (App x y)  = \vs      -> "("++ show' x vs ++" "++ show' y vs ++")"
                       phi inv show' (Lam z)    = \(v:vs)  -> "(\\"++v++"->"++ show' (z (inv (const v))) vs ++")"
\end{code}
}
%format k_g = k"_g"
%format s_g = s"_g"
%format skk_g = skk"_g"
%format w_g = w"_g"
\newcommand{\ExpGExamples}{
\begin{code}
k_g    = Lam_g  (\x -> Lam_g (\y -> x))
s_g    = Lam_g  (\x -> Lam_g (\y -> Lam_g (\z ->
                    App_g (App_g x z) (App_g y z))))
w_g    = Lam_g  (\x -> App_g x x)
skk_g  = App_g (App_g s_g k_g) k_g
\end{code}
}
%format k_m = k"_m"
%format s_m = s"_m"
%format skk_m = skk"_m"
%format w_m = w"_m"
\newcommand{\ExpMExamples}{
\begin{code}
k_m    = lam_m  (\x -> lam_m (\y -> x))
s_m    = lam_m  (\x -> lam_m (\y -> lam_m (\z ->
                    app_m (app_m x z) (app_m y z))))
w_m    = lam_m  (\x -> app_m x x)
skk_m  = app_m (app_m s_m k_m) k_m
\end{code}
}
\newcommand{\ExpExamples}{
\begin{code}
k    = lam  (\x -> lam (\y -> x))
s    = lam  (\x -> lam (\y -> lam (\z ->
                app (app x z) (app y z))))
w    = lam  (\x -> app x x)
skk  = app (app s k) k
\end{code}
}
