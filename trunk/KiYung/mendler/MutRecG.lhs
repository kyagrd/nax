\begin{comment}
\begin{code}
import Data.Maybe (fromJust)
\end{code}
\end{comment}
\begin{code}
type Name = String

type Env = [(Name, Int)]
{-""-}
data Dec  =  Def Name Exp
data Exp  =  Var Name
          |  Val Int
          |  Add Exp Exp
          |  Let Dec Exp
{-""-}

{-""-}
{-""-}

{-""-}
{-""-}
{-""-}

{-""-}
{-""-}

{-""-}
extend :: Dec -> Env -> Env
extend  (Def x e)  =
        \env -> (x, eval e env) : env

eval :: Exp -> Env -> Int
eval    (Var x)      =
        \env -> fromJust (lookup x env)
eval    (Val v)      =
        \env -> v
eval    (Add e1 e2)  =
        \env -> eval e1 env + eval e2 env
{-""-}

{-""-}
{-""-}

{-""-}
{-""-}
\end{code}
