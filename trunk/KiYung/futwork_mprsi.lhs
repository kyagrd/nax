%include includelhs2tex.lhs

\section{Another Mendler-style recursion scheme for mixed-variant datatypes}
\label{sec:futwork:mprsi}
%% This section is an extended and revised version of our extended abstract
%% (without the introduction section) in the TYPES 2013 workshop.

In \S\ref{sec:msf}, we discussed the Mendler-style iteration with
a syntactic inverse, |msfcata|, which is particularly useful for
negative (or mixed-variant) datatypes.
We demonstrated the usefulness of |msfcata| by defining functions over HOAS:
the string formatting function |showHOAS| for the untyped HOAS using |msfcata0|
(Figure\ref{fig:HOASshow} on p\pageref{fig:HOASshow}) and
the type preserving evaluator |evalHOAS| for the simply-typed HOAS
using |msfcata1| (Figure\ref{fig:HOASeval} on p\pageref{fig:HOASeval}).
In this section, we introduce another Mendler-style recursion scheme,
|mprsi|, motivated by an example similar to the |evalHOAS| function.
The name of |mprsi| stands for
Mendler-style primitive recursion with sized index.


\begin{figure}
\begin{singlespace}
%include mendler/HOASevalV.lhs
\end{singlespace}
\caption{evaluators for simply-typed HOAS,
         via the native value domain (|evalHOAS|)
         and via a user-defined value domain (|vevalHOAS|)}
\label{fig:HOASevalV}
\end{figure}

Let us first review the |evalHOAS| example before we discuss
the motivating example |vevalHOAS| for |mprsi|. Both |evalHOAS|
and |vevalHOAS| are illustrated in In Figure\;\ref{fig:HOASevalV}.
The function |evalHOAS :: Exp t -> Id t| is a type preserving evaluator
that evaluates an HOAS expression of type |t| to the Haskell's native
value of type |t|. The |evalHOAS| function always terminates because
|msfcata1| always terminates. Recall that |msfcata1| and |Rec1|
can be embedded into System \Fw\ (or System \Fi, considering term indices).

The next example |vevalHOAS :: Exp t -> Val t| is a type preserving evaluator
for the simply-typed HOAS. The function |vevalHOAS :: Exp t -> Val t| is
a type preserving evaluator that evaluates an HOAS expression of type |t|
to a user-defined value domain |Val| of type |t|. The definition of |vevalHOAS|
is similar to |evalHOAS| -- both of them are defined using |msfcata1|.
The first equation of |phi| for evaluating the |Lam|-expression is essentially
the same as the corresponding equation in the definition of |evalHOAS|.
The second equation of |phi| for evaluating the |Lam|-expression is also similar
in structure to the corresponding equation of in the definition of |evalHOAS|,
but the use of |unVal| is problematic. Note, the definition of |unVal|
relies on pattern matching against |In1|. Recall that one cannot freely
pattern match against a recursive value in Mendler style. In Mendler style,
recursive values must be analyzed (or, eliminated) by using Mendler-style
recursion schemes. It is not a problem to use |unId| in the definition of
|evalHOAS| because |Id| is non-recursive.

It is not likely that |unVal| can be defined using any of the existing
Mendler-style recursion scheme we know of. So, we design a new Mendler-style
recursion scheme that can express |unVal|. The new recursion scheme |mprsi|
extends |mpr| with the additional uncast operation. Recall that |mpr| has
two abstract operations, call and cast. So, |mprsi| has three abstract
operations, call, cast, and uncast. In the following paragraphs,
we explain the design of |mprsi| step-by-set.

Let us try to define |unVal| using |mprim1|, and see where it falls short.
|mpr1| provides two abstract operations, |cast| and |call|, as you can
see from its type sigaure:
\begin{singlespace}
\begin{code}
mprim1 :: (forall r i.  (forall i. r i -> Mu1 f i)  -- cast
                    ->  (forall i. r i -> a i)      -- call
                    ->  f r i -> a i) ) -> Mu f i -> a i
\end{code}~\vspace{-1em}
\end{singlespace}
\noindent
We attempt to define |unVal| using |mprim1| as follows:\vspace{.5em}
\begin{singlespace}
\begin{code}
unVal :: Mu1 V (t1 -> t2) -> (Mu1 V t1 -> Mu1 V t2)
unVal = mprim1 phi where
  phi cast call (VFun f) = ...
\end{code}~\vspace{-1em}
\end{singlespace}\noindent
Inside the |phi| function, we a function |f :: (r t1 -> r t2)| over
abstract recursive values. We need to somehow cast |f| into
a function over concrete recursive values with type |(Mu V t1 -> Mu V t2)|.
We would not need to use |call|, since we do not expect
any recursive computation to define |unVal|.
So, |cast :: (forall i. r i -> Mu f i)| is what is left for us to work with.
Composing |cast| with |f|, we can get |(cast . f) :: (r t1 -> Mu V t2)|,
whose domain type (|Mu V t2|) is exactly what we want. But, the codomain type
is still abstract |(r t1)| rather than being concrete |(Mu V t1)|.
We are stuck here.

What additional abstract operation would help us complete the definition of
|unVal|? We need an abstract operation to cast from |(r t1)| to |(Mu V t1)|
in a contravariant position.
If we had an inverse of cast, |uncast :: (forall i. Mu f i -> r i)|, we can
complete the definition of |unVal| by compsoing |uncast|, |f|, and |cast|.
Observe that |(uncast . f . cast) :: (Mu1 V t1 -> Mu1 V t2)|.

existing
So, we design a new recursion scheme |mprsi|

not erasable

\begin{singlespace}
\begin{code}
-- a naive type signature for mprsi1
mprsi1 :: (forall r  i.  (forall i. r i -> Mu1 f i)  -- cast
                     ->  (forall i. Mu1 f i -> r i)  -- uncast
                     ->  (forall i. r i -> a i)      -- call
                     ->  f r i -> a i) ) -> Mu f i -> a i

mprsi1 phi (In1 x) = phi id id (mprsi1 phi) x
\end{code}~\vspace{-1em}
\end{singlespace}

%% \texttt{unfun\;:\;Val\,(a\,->\,b)\;->\;Val\;a\,->\,Val\;b},
%% this would be admitted in Nax.

\begin{singlespace}
\begin{code}
-- candidate 1
mprsi1 :: (forall r  j.  (forall i. (i<j) =>  r i -> Mu1 f i)  -- cast
                     ->  (forall i. (i<j) =>  Mu1 f i -> r i)  -- uncast
                     ->  (forall i.           r i -> a i)      -- call
                     ->  f r j -> a j) ) -> Mu f i -> a i
-- candidate 2
mprsi1 :: (forall r  j.  (forall i.           r i -> Mu1 f i)  -- cast
                     ->  (forall i. (i<j) =>  Mu1 f i -> r i)  -- uncast
                     ->  (forall i.           r i -> a i)      -- call
                     ->  f r j -> a j) ) -> Mu f i -> a i
\end{code}~\vspace{-1em}
\end{singlespace}




motivates
a new recursion scheme, The |vevalHOAS| function.

%% If the datatype \texttt{Exp} had indexes to assert invariants of
%% well-formed expressions, we could rely on these invariants to write
%% even more expressive programs, such as a terminating well-typed evaluator.
%% Discussion around this idea will constitute the latter parts of the paper.
%% \vspace*{-2ex}
%% \paragraph{A simply-typed HOAS evaluator\!\!\!} can be defined
%% using \MsfIt\ at kind \texttt{*\,->\,*}.  Since \MsfIt\ terminates
%% for any datatype, we are also proving that the evaluation of
%% the simply-typed $\lambda$-calculus always terminates
%% just by defining \texttt{eval\,:\,Exp\;t\;->\;Id\;t\,} in Nax, as below.
%% We wonder \texttt{eval} has similarities to other normalization strategies
%% like NbE \cite{BerSch91}.
%% \vspace*{-1ex}
%% {\small
%% \begin{verbatim}
%%   data E : (* -> *) -> (* -> *) where      -- the "deriving fixpoint Exp" defines
%%     Abs : (r a -> r b) -> E r (a -> b)     --   abs f   = In[* -> *] (Abs f)
%%     App : E r (a -> b) -> E r a -> E r b   --   app f e = In[* -> *] (App f e)
%%       deriving fixpoint Exp                --   synonym Exp t = Mu[* -> *] E t
%% 
%%   data Id a = MkId a -- the identity type
%%   unId (MkId x) = x  -- destructor of Id
%%   
%%   eval e = msfit { t . Id t } e with
%%              call inv (App f x) = MkId (unId(call f) (unId(call x)))
%%              call inv (Abs f) = MkId (\v -> unId(call (f (inv (MkId v)))))
%% \end{verbatim} }
%% \vspace*{-.5ex}\noindent
%% The type of \texttt{eval\,:\,Exp\;t\;->\;Id\;t\,} is inferred from
%% \texttt{\{\,t\,.\;Id t\,\}}, which specifies the answer type in relation
%% to the input type's index.
%% Conceptually, \texttt{msfit} at kind \texttt{*\,->\,*} has the following type.\vspace*{-.5ex}
%% % Note the types of \texttt{msfit}'s two abstract operations
%% % \texttt{call} and \texttt{inv}.
%% {\small
%% \begin{verbatim}
%%   msfit : (forall r . (forall i . r i -> ans i) -- call
%%                    -> (forall i . ans i -> r i) -- inv
%%                    -> (forall i . f r i -> ans i)      ) -> Mu[* -> *] f j -> ans j
%% \end{verbatim} }
%% \vspace*{-2.5ex}
%% \paragraph{Evaluation via user-defined value domain\!\!\!\!\!}, instead of
%% the native value space of Nax, motivates a new recursion scheme,
%% \mprsi, standing for Mendler-style primitive recursion with sized index.
%% %% A user-defined value domain is particularly useful for evaluating expressions
%% %% of first-order syntax. Here, we stick to HOAS to avoid introducing a new datatype.
%% Consider writing an evaluator \texttt{\,veval\;:\;Exp\;t\,->\,Val\;t\,}
%% via the value domain \texttt{Val\;:\;*\,->\,*\,}.\vspace*{-.5ex}
%% {\small
%% \begin{verbatim}
%%   data V : (* -> *) -> * -> * where      -- the "deriving fixpoint Val" defines
%%     Fun : (r a -> r b) -> V r (a -> b)   -- fun f = In [* -> *] (Fun f)
%%       deriving fixpoint Val              -- synonym Val t = Mu[* -> *] V t
%% \end{verbatim}\vspace*{-1.5ex}
%% \begin{verbatim}
%%   veval e = msfit { t . V t } e with
%%               call inv (App f x) = unfun (call f) (call x)  -- how do we define unfun?
%%               call inv (Abs f) = fun (\v -> (call (f (inv v))))
%% \end{verbatim} }
%% \noindent
%% Only if we were able to define
%% \texttt{unfun\;:\;Val\,(a\,->\,b)\;->\;Val\;a\,->\,Val\;b},
%% this would be admitted in Nax.
%% However, it is not likely that \texttt{unfun} can be defined using
%% recursion schemes currently available in Nax. Thereby, we propose
%% a new recursion scheme \mprsi, which extends the Mendler-style primitive recursion
%% (\texttt{mpr}) with the uncasting operation.\vspace*{-.5ex}
%% {\small
%% \begin{verbatim}
%%   mprsi : (forall r . (forall i. r i -> ans i)                      -- call
%%                    -> (forall i. (i < j) => r i -> Mu[* -> *] f i)  -- cast   
%%                    -> (forall i. (i < j) => Mu[* -> *] f i -> r i)  -- uncast 
%%                    -> (forall i. f r i -> ans i) ) -> Mu[* -> *] f j -> ans j
%% \end{verbatim}\vspace*{-1.5ex}
%% \begin{verbatim}
%%   unfun v = mprsi { (a -> b) . V a -> V b } v with
%%               call cast (Fun f) = cast . f . uncast   -- dot (.) is function composition
%% \end{verbatim} }\vspace*{-.5ex}
%% \noindent
%% Note the size constraints \texttt{(i\;<\;j)} on both \texttt{cast} and \texttt{uncast} operations
%% (FYI, \texttt{mpr}'s \texttt{cast} does not have size constraints).
%% These constraints prevent writing evaluator-like functions on strange expressions
%% that have constructors like below, which may cause non-termination.\vspace*{-.5ex}
%% {\small
%% \begin{verbatim}
%%  app1 : (Exp1 (a->b) -> Exp1 b) -> Exp1 (a->b)  -- prevented by constraint on uncast
%%  app2 : (Exp2 a -> Exp2 (a->b)) -> Exp2 (a->b)  -- prevented by constraint on cast
%% \end{verbatim} }\vspace*{-.5ex}
%% \noindent
%% Our examples in this abstract only involve type indices, but similar
%% formulation is possible for term indices as well.\vspace*{-1.5ex}
%% This is still a fresh proposal awaiting proof of termination.


