\begin{figure*}
%format e1
%format e2
%format env = "\sigma"
%format proj_D = "\pi_{\!"D"}"
%format proj_E = "\pi_{\!"E"}"
%format f_D = f"_{"D"}"
%format f_E = f"_{"E"}"
%format RetD = Ret"_{\!"D"}"
%format RetE = Ret"_{\!"E"}"
\begin{minipage}{.5\textwidth}
%include MutRecG.lhs
\end{minipage}
\begin{minipage}{.5\textwidth}
%include MutRec.lhs
\end{minipage}
\caption{Mutual recursion (|extend| and |eval| over |Dec| and |Exp|)
         expressed in terms of |mcata1| over an indexed datatype |DecExpF|}
\label{fig:mutrec}
\end{figure*}

\subsection{Mutually recursive datatypes} \label{ssec:tourMutRec}

We can express mutual recursion over mutually recursive datatypes
in Mendler style using an indexed base dataype.
The context extension function |extend| and
the expression evaluation function |eval| in Figure \ref{fig:mutrec}
are mutually recursive functions over the mutually recursive datatypes of
declaration |Dec| and expression |Exp|.
%% A declaration (|Dec|) binds a name to an expression.
%% %% \footnote{For simplicity, we have only one constructor for |Def|.
%% %% There would be more than one ways to declare bindings in a more realistic
%% %% programming language syntax tree.}
%% Expressions (|Expr|) include variables, integer values, additions, and
%% let-bindings, which contain a declaration.
The general recursive version on left-hand side of Figure \ref{fig:mutrec}
is a self-explanatory standard evaluator implementation for the expression.

To express this in Mender-style (right), we first define the common base
|DecExpF| which is indexed by |D| and |E|.  Note, the data constructors of
|DecExpF| include both the data constructors of declarations (|Def|) and
expressions (|Var|, |Val|, |Add|, and |Let|).  The data constructor for
declaration is indexed by |D|, and the other data constructors for
expressions are indexed by |E| in their result types.
Then, we can define |Dec| as |Mu1 DecExpF D| and |Exp| as |Mu1 DecExpF E|.
We wrap up the return types of the |eval| and |extend| functions with the
data family |Ret|, for reasons similar to the return types of
the summation functions in \S\ref{ssec:tourNested}.
%% The datatype family |Ret| is basically a GADT indexed by |E| and |D| as follows:
%% \begin{code}
%% data Ret (i :: *) where
%%   RetD  :: (Env->Env)  -> Ret D
%%   RetE  :: (Env->Int)  -> Ret E
%% \end{code}
%% The data family and newtype instance extensions enables GHC to optimize the
%% GADT datatype above by compiling away |RetD| and |RetE| at compile time.
We also define the projection functions |proj_D :: Ret D -> (Env->Env)| and
|proj_E :: Ret E -> (Env->Int)| to open up the return type.
Then, we can express the mutually recursive functions, both |eval| and |extend|,
combined in one function definition |extev| using |mcata1|.
You can observe that the definition of |phi| is very close to the
definitions of the general recursive version of |extend| and |eval| on the left.
The difference is that we project out |ev| from |f|, which is the handle for
combined mutually recursive function, when we need to call the evaluation
function for the recursion.  Once we have defined the combined function |extev|,
we can project out |extend| and |eval| using |proj_D| and |proj_E|.

