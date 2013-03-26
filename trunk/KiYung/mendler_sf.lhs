%include includelhs2tex.lhs
\section{Mendler-style iteration with a syntactic inverse (|msfcata|)}
\label{sec:msf}
While it is known that iteration and primitive recursion terminate for all types
\cite{AbeMatUus05,AbeMat04}, they are not particularly expressive over negative
recursive types. Identifying additional Mendler-style operators that work
naturally, and are more expressive than iteration, is one of the important
result of this dissertation.

Interesting examples of Mendler-style operators over negative recursive types
have been neglected in the literature. One of the reasons, I think, is because
it is possible to encode negative recursive types into positive recursive ones.
Because conventional iteration and primitive recursion normalize for
positive recursive types we can use standard techniques on these encodings
of translating negative recursive types into positive recursive types.
What we gain by using such encodings must be traded against the loss in
transparency that such encodings force upon the implementation. The natural
structure, which were evident in the negative data type, become obscured by
the encoding.

A series of papers \cite{Pat93,MeiHut95,FegShe96,DesPfeSch97,bgb} studied 
techniques that define recursion schemes over negative recursive types in
the conventional setting. In our recent work \cite{AhnShe11}, we discovered
that this work can be naturally captured as a kind-indexed family of Mendler
style combinator. The \textit{msfit} combinator (\aka\ \textit{msfcata})
corresponds to the conventional recursion combinator discovered
by \citet{FegShe96} and later refined by \citet{bgb}.
With this new family, we were able to write many interesting programs,
involving negative recursive types, that may be impossible, or very unnatural,
to write with the ordinary Mendler-style iteration family (\textit{mit},
\aka, \textit{mcata}).

\subsection{Formatting Higher-Order Abstract Syntax}\label{sec:showHOAS}
To lead up to the Mendler-style solution to formatting HOAS, we first review
some earlier work on turning expressions, expressed in 
Higher-Order Abstract Syntax (HOAS)\cite{Church40,PfeEll88}, into strings.
This solution was suggested by \citet{FegShe96}. They were studying
yet another abstract recursion scheme described
by \citet{Pat93} and \citet{MeiHut95} that could only be used
if the combining function had a true inverse. This seemed a bit limiting,
so Fegaras and Sheard introduced the idea of a syntactic inverse.
The syntactic inverse was realized by augmenting the |Mu0| type with a second
constructor. This augmented |Mu0| had the same structure as |Rec0|
in Figure \ref{fig:datafix}, but with a different type.

The algorithm worked, but, the augmentation introduces junk.
\citet{bgb} eliminated the junk by exploiting parametricity.
It is a coincidence that Mendler-style recursion combinators also use the same
technique, parametricity, for a different purpose, to guarantee termination.
Fortunately, these two approaches work together
without getting in each other's way.  

%include mendler/HOASshow.lhs
\afterpage{
\begin{landscape}
\begin{figure*}
\ExpGFig
%% \ExpMFig
\ExpFig
\varsDef
\caption{|msfcata0| example: String formatting function for Higher-Order Abstract Syntax (HOAS)}
\label{fig:HOASshow}
\end{figure*}
\end{landscape}
}

\subsubsection{A general recursive implementation for open HOAS}
\label{ssec:showHOASrecursive}

The recursive datatype |Exp_g| in Figure \ref{fig:HOASshow} is an open HOAS.
By \emph{open}, we express that |Exp_g| has a data constructor |Var_g|,
which enables us to introduce free variables.
The constructor |Lam_g| holds an embedded function of type |(Exp_g -> Exp_g)|.
This is called a shallow embedding, since we use functions in the host language,
Haskell, to represent lambda abstractions in the object language |Exp_g|.
For example, using the Haskell lambda expressions,
we can construct some |Exp_g| representing lambda expressions as follows:
\vspace*{.5em}\ExpGExamples\vspace*{-.5em}\\
Since we can build any untyped lambda expressions with |Exp_g|, 
even the problematic self application expression |w_g|, it is not possible to write a terminating
evaluation function for |Exp_g|.  However, there are many 
functions that recurse over the structure of |Exp_g|, and when they
terminate produce something useful.  One of them is
the string formatting function |showExp_g| defined in Figure \ref{fig:HOASshow}.

Given an expression (|Exp_g|) and a list of fresh variable names (|[String]|),
the function |show'| (defined in the |where| clause of |showExp_g|)
returns a string (|String|) that represents
the given expression.  To format an application expression |(App_g x y)|,
we simply recurse over each of the subexpressions |x| and |y|.
To format a lambda expression, we take a fresh name |v| to represent the binder
and we recurse over |(z (Var_g v))|, which is the application of
the embedded function |(z :: Exp_g -> Exp_g)| to a variable expression
|(Var_g v :: Exp_g)| constructed from the fresh name.
Note, we had to create a new variable expression to format the function body
since we cannot look inside the function values of Haskell.
To format a variable expression |(Var_g v)|,
we only need to return its name |v|.  The local function |show'|
(and hence also |showExp_g|), are total as long as
the function values embedded in the |Lam_g| constructors are total.

We can use |showExp_g| to print out the terms as follows: %% |k_g|, %% |s_g|,
%% |skk_g| and |w_g| as follows:
\vspace*{-1em}
\begin{quote}\noindent
$>$ |putStrLn (showExp_g k_g)|\\
\verb|(\a->(\b->a))| \\
$>$ |putStrLn (showExp_g s_g)|\\
\verb|(\a->(\b->(\c->((a c) (b c)))))| \\
%% $>$ |putStrLn (showExp_g skk_g)| \\
%% \verb|(((\a->(\b->(\c->((a c) (b c))))) (\a->(\b->a)))|
%% \verb|(\a->(\b->a)))| \\
$>$ |putStrLn (showExp_g w_g)|\\
\verb|(\a->(a a))|
\end{quote}
\vspace*{-.1em}

Note that |show'| is not structurally inductive in the |Lam_g| case.
The recursive argument (|z (Var_g v)|), in particular |Var_g v|, is not
a subexpression of (|Lam_g z|).  Thus the recursive call to |show'|
may not terminate. This function terminated only
because the embedded function |z| was well behaved, and the argument
we passed to |z|, (|Var_g v|), was well behaved.
If we had applied |z| to the expression (|Lam_g (\x->x)|) in place of |Var_g v|,
or |z| itself had been divergent, the recursive call would have diverged.
If |z| is divergent, then obviously |show' (z x)| diverges for all |x|.
More interestingly, suppose |z| is not divergent
(perhaps something as simple as the identity function)
and |show'| was written to recurse on (|Lam_g (\x->x)|), 
then what happens?
\vspace*{.5em}
\begin{code}
show' (Lam_g z) (v:  vs) = "(\\"++v++"->"++
                     show' (z (Lam_g (\x->x)) vs ++")"
\end{code}\vspace*{-.5em}\\
The function is no longer total.  To format (|z (Lam_g (\x->x))|)
in the recursive call, it loops back to the |Lam_g| case again,
unless |z| is a function that ignores its argument.
This will form an infinite recursion, since this altered |show'| forms
yet another new |Lam_g (\x->x)| expression and keeps on recursing.


%% \subsection{An ad-hoc solution for open HOAS using $\pmb{ |mcata0| }$}
%% We can write the formatting function using the Mendler catamorphism combinator
%% |mcata0|, with a slight change to the datatype definition.  As usual, we define
%% the base datatype |ExpF_m| and define the expression type |Exp_m| as
%% a fixpoint of |ExpF_m| as in Figure \ref{fig:HOASshow}.  The change we make is
%% on the data constructor |Lam_m| for lambda expressions.  We add an additional
%% argument to the |Lam_m| constructor.  Note, the type of the additional argument
%% |(String -> r)| is intensionally similar to the type of the |Var_m| constructor
%% |(String -> ExpF_m r)|.  As we shall see shortly, we expect this additional
%% argument to always be |var_m| in the definition of the formatting function.
%% Then, we define shorthand constructor functions |var_m|, |lam_m| and |app_m|
%% for the |Exp_m| type.  We would normally define the shorthand constructor
%% function for lambda expressions as |lam_m mk e = In0 (Lam mk e)|, but here
%% we choose to always apply |Lam_g| to |var_m| since that is what we expect
%% to use in the definition of the formatting function.
%% Using these shorthand constructor functions we can construct some expressions
%% of |Exp_m| analogous to the ones we constructed for |Exp_g| as follows:
%% \vspace*{.5em}\ExpMExamples\vspace*{-.5em}\\
%% We can define the formatting function |showExp_m| using
%% the Mendler catamorphism |mcata0| as in Figure \ref{fig:HOASshow}.
%% The definition of the local function |phi| inside |showExp_m| is
%% very similar to |show'| in the definition of |showExp_g|.
%% The only difference is in the lambda expression case where we use use |mk|
%% to construct a new variable expression from a fresh name |v|
%% to pass as an argument to |z|, instead of using the constructor |Var_m|
%% or the shorthand constructor function |var_g| directly.
%% In fact, we can use neither |Var_m :: String -> ExpF_m r|
%% nor |var_m :: String -> Exp_m| here in |phi|
%% since we need to construct a new value of parametric type |r|
%% to pass it as an argument of |z :: r -> r|.
%% This is the very kind of action Mendler-style combinators prevent.
%% Recall, |mk :: String -> r| has the right type and its value is always
%% |var_m| when we consistently use |lam_m| to construct expressions.
%% Thus, it has the same effect of using |var_m| to construct a new variable
%% expression while respecting the parametricity of the type variable |r|.
%% In other words, the additional argument |mk| gives a safe local handle of
%% the constructor function |var_m| inside second equation of |phi| defined
%% for the |Lam_m| case.
%% 
%% Let us contemplate on whether |mcata0| does really guarantee termination
%% while writing functions over negative inductive types, such as |showExp_m|.
%% One may wonder why we cannot play the same adversary strategy for
%% non-termination by passing |lam_m| instead of |var_m| into |mk|,
%% the first argument of the |Lam_m| constructor, just as we did for |show'|
%% in the general recursive version.  To play that adversary strategy,
%% we would have to define the shorthand constructor |lam_m| as follows:
%% |lam_m e = In0 (Lam_m lam_m e)|.  Although this is a valid Haskell code,
%% we have already violated the rule of the game by using unrestricted
%% general recursion to define |lam_m| in terms of |lam_m| itself.
%% 
%% With |showExp_m| we can format and print out the expressions
%% |k_m|, |s_m|, |skk_m| and |w_m| as follows:
%% \begin{quote}\noindent
%% $>$ |putStrLn (showExp_m k_m)|\\
%% \verb|(\a->(\b->a))|
%% \end{quote}\vspace*{-1em}
%% \begin{quote}\noindent
%% $>$ |putStrLn (showExp_m s_m)|\\
%% \verb|(\a->(\b->(\c->((a c) (b c)))))|
%% \end{quote}\vspace*{-1em}
%% \begin{quote}\noindent
%% $>$ |putStrLn (showExp_m skk_m)|\\
%% \verb|(((\a->(\b->(\c->((a c) (b c))))) (\a->(\b->a)))|\\
%% \verb|(\a->(\b->a)))|
%% \end{quote}\vspace*{-1em}
%% \begin{quote}\noindent
%% $>$ |putStrLn (showExp_m w_m)|\\
%% \verb|(\a->(a a))|
%% \end{quote}
%% 
%% Although |mcata0| allows us to define total functions over recursive datatypes
%% with embedded functions, it is not quite satisfactory. It is not general enough
%% since we have to make change to the datatype definition to meet the goal of
%% the specific function we intend to define.  And, we need to consistently apply
%% |Lam_m| to only |var_m| when we construct expressions in order to make
%% |showExp_m| work as we intend to.  In addition, the change we make
%% to the datatype definition is specific to function definition.
%% The definition of |Exp_m|, in particular the |Lam_m| data constructor,
%% is only intended to work with the formatting function |showExp_m|,
%% but it may not work for functions over HOAS other than
%% the string formatting function.  We would need to define
%% yet another variation of HOAS datatype to define other total functions.
%% Moreover, we cannot cover certain class of datatypes even with this rather
%% ad-hoc approach of defining multiple variations specific for each function.
%% More standard definition of HOAS without the variable constructor,
%% that is |data Exp = Lam (Exp -> Exp) || App Exp Exp|, is a typical example.
%% As in \citet{Pat93} and \citet{MeiHut95}, we typically need anamorphism
%% in addition to catamorphism. 
%% \TODO{some refined writing needed here to close the subsection maybe
%% we should note up front that there is a differnce?? that we start with
%% an example of HOAS with variable constructor}

\subsubsection{A Mendler-style solution for closed HOAS}
\label{ssec:showHOASmsfcata}

Our exploration of the code in Figure \ref{fig:HOASshow} illustrates
three potential problems with the general recursive approach.
\vspace*{-.3em}
\begin{itemize}
\item The embedded functions may not terminate.
\item In a recursive call, the arguments to an embedded function
may introduce a constructor with another embedded function, leading to
a non terminating cycle.
\item We got lucky, in that the answer we required was a |String|, and we
happened to have a constructor |Var_g :: String -> Exp_g|. In general
we may not be so lucky.
\end{itemize}\vspace*{-.3em}

In Figure \ref{fig:HOASshow}, we defined |Exp_g| in anticipation of our need
to write a function |showExp_g :: Exp_g -> String|, by including a constructor
|Var_g :: String -> Exp_g|.  Had we anticipated another function
|f:: Exp_g -> Int| we would have needed another constructor |C :: Int -> Exp_g|.
Clearly we need a better solution.  The solution is to generalize the kind of
the datatype from |Exp_g :: *| to |Exp :: * -> *|, and add a universal inverse.
\vspace*{.5em}
\begin{code}
data Exp a   =  App (Exp a) (Exp a)
             |  Lam (Exp a -> Exp a)
             |  Inv a

countLam:: Exp Int -> Int   
countLam (Inv n) = n
countLam (App x y) = countLam x + countLam y
countLam (Lam f) = countLam(f (Inv 1))
\end{code}\vspace*{-.5em}\\
Generalizing from |countLam| we can define a function from |Exp| to any
type. How do we lift this kind of solution to the Mendler style?
\citet{FegShe96} proposed moving the general inverse from the Base type
to the datatype fixpoint. Later this approach was refined by \citet{bgb}
to remove the junk introduced by that augmentation (i.e. things like
|App (Inv 1) (Inv 1)|).

We use the same inverse augmented datatype fixpoint appearing in \citet{bgb}.
Here, we call it |Rec0| (see Figure \ref{fig:datafix}).
The inverse augmented datatype fixpoint |Rec0| is similar to
the standard datatype fixpoint |Mu0|.
The difference is that |Rec0| has an additional type index |a|
and an additional data constructor |Inverse0 :: a -> Rec0 a i|,
corresponding to the universal inverse.
The data constructor |Roll0| and the projection function |unRoll0|
correspond to |In0| and |out0| of the normal fixpoint |Mu0|.
As usual we restrict the use of |unRoll0|, or pattern matching against |Roll0|.
%% to terms in the programatic fragment of the language.

We illustrate this in the second part of Figure \ref{fig:HOASshow}.
As usual, we define |Exp' a| as a fixpoint of the base datatype |ExpF|
and define shorthand constructors |lam| and |app|.
Using the shorthand constructor functions,
we can define some lambda expressions: %% as follows:
\vspace*{.3em}\ExpExamples\vspace*{-1em}\\
However, there is another way to construct |Exp'| values that is
problematic. Using the constructor |Inverse0|, we can turn values of
arbitrary type |t| into values of |Exp' t|.  For example, 
|Inverse0 True :: Exp' Bool|. This value is junk, since it does 
not coorespond to any lambda term. By design, we wish to hide |Inverse0|
behind an abstraction boundary. We should never allow the user to construct
expressions such as |Inverse0 True|, except for using them as callers
for intermediate results during computation.


We can distinguish pure expressions that are inverse-free
from expressions that contain inverse values by exploiting parametricity.
The expressions that do not contain inverses have a fully polymorphic type.
For instance, |k|, |s| and |w| are of type (|Exp' a|).
The expressions that contain |Inverse0| have more specific type
(e.g., |(Inverse0 True) :: (Exp' Bool)|).
Therefore, we define the type of |Exp| to be |forall a . Exp' a|.
Then, expressions of type |Exp| are guaranteed to be be inverse-free.
Using parametricity to sort out junk introduced by the inverse is the key idea
of \citet{bgb}, and the inverse augmented fixpoint |Mu0| is the key idea
of \citet{FegShe96}.  The contribution we make in this work is putting
together these ideas in Mender-style setting.  By doing so, we are able
define recursion combinators over types with negative occurrences,
which have well understood termination properties enforced by parametricity. We define
4 such combinators: |msfcata0|, |msfhist0|, |msfcata1|, and |msfhist1|. 
The combinator |msfcata0| is the simplest, to define it
we generalize over |mcata0| by using the same device we used earlier,
we abstract the combining function over an additional argument,
this time an abstract inverse.
\begin{itemize}
  \item The combining function |phi| becomes a function of 3 arguments.
        An abstract inverse, an 
        recursive caller, and a base structure.
\begin{code}
  msfcata phi (Roll0 x)          = phi Inverse0           (msfcata phi)  x
  msfcata phi (Inverse0 z)       = z
\end{code}
  \item For inverse values, return the value inside |Inverse0| as it is.
  \item We use higher-rank polymorphism to insist that 
        the abstract inverse function, with type (|a -> r a|),
        the recursive caller function, with type (|r a -> a|), and
        the base structure, with type (|f (r a)|), only work
        over an abstract type constructor, denoted by (|r|).
\begin{code}
msfcata0  ::  (forall r .  (a -> r a)  ->
                           (r a -> a)  ->
                           (f (r a)    -> a)) ->  (forall a . Rec0 f a) -> a
\end{code}
  \item Note, the abstract recursive type |r| is parameterized by
        the answer type |a| because the augmented datatype fixpoint |Rec0|
        is parameterized by the answer type |a|.

        Also, note, the second argument of |msfcata0|, the object being
        operated on, has the higher-rank type
        |(forall a . Rec0 f a)|, insisting the input value to be inverse-free
        by enforcing |a| to be abstract.
\end{itemize}  

In Figure \ref{fig:HOASshow}, using |msfcata0|, it is easy to define |showExp|,
the string formatting function for |Exp|, as in Figure \ref{fig:HOASshow}.
The |App| case is similar to the general recursive implementation.
The body of |phi| is almost textually identical to the body of |show'|
in the general recursive solution, except we use the inverse expression
|inv (const v)| to create an abstract |r| value to pass to
the embedded function |z|.  Note, |const v| plays exactly
the same roll as |(Var_g v)| in |show'|.

Does |msfcata0| really guarantee termination?  To prove this we need to
address the first two of the three potential problems described at
the beginning of Section \ref{ssec:showHOASmsfcata}.  The first problem
(embedded functions may be partial) is addressed using logicality analysis.
The second problem (cyclic use of constructors as arguments to
embedded functions) is addressed by the same argument we used
in Section \ref{ssec:tourNegative}.  The abstract type of the inverse
doesn't allow it to be applied to constructors, they're not abstract enough. 
Just as we couldn't define |p_m| (in Section \ref{ssec:tourNegative}) we can't
apply |z| to things like {\small (|Lam (\ x -> x)|)}.
In \S\ref{App:Fomega} we provide an embedding
of |msfcata|, along with several examples (including
the HOAS formatting example), into the strongly normalizing language $F_\omega$.
This constitutes a proof that |msfcata| terminates for all
inductive datatypes, even those with negative occurrences.

%%Parallel reduction of lambda
%%terms is an example of the use of |msfhist0|, which we have
%%elided for space reasons. 

%% The extra type parameter |a| to the type constructors |r|
%% in the type of |msfcata0| (and the other |msf*| operators as well)
%% \begin{code}
%% (forall r.(a -> r a) -> (r a -> a) -> f (r a) -> a) ->  
%% (forall a . Rec0 f a) -> a
%% \end{code}
%% is an artifact of the Haskell implementation that uses the device
%% |Exp = forall a . Exp' f a| to ensure that inverse operator is truly abstract.
%% In fact |msfcata0| is defined in terms of a local function |msfcata|
%% that is less abstract (see Figure \ref{fig:rcombdef} for the details). 
%% 
%% In a language where we could use other kinds of abstraction boundaries to
%% completely hide |Inverse0|, we could get away with the simpler type:
%% \TODO{I doubt whether this is exactly correct}
%% \begin{code}
%% (forall r. (a -> r) -> (r -> a) -> f r -> a) -> (Rec0 f) -> a
%% \end{code}
%% If no programmer can access |Inverse0|, then every |Exp| will be abstract on
%% |a|, so why bother to track |a| at all?  Of course, while the programmer can't
%% get his hands on |Inverse0|, by using |mcata0|, he can get his hands on
%% |Inverse0|'s effect, but this version has an abstract type that sanitizes
%% its use.  Similar properties hold for |mhist0|, |mcata1|, and |mhist1|.


\subsection{A graph datatype with cycles and sharing}
%include mendler/Graph.lhs
Another example of negative datatype is a graph with cycles and sharing.
Due to the space limitation, we only give its implementation
in Figure \ref{fig:graph}. For further details, see \citet{FegShe96}.

\subsection{$F_\omega$ encoding of |Rec0| and |msfcata0|}\label{App:Fomega}

%include mendler/Proof2.lhs

\begin{figure}
\ProofSFCata
\SumDef
\caption{$F_\omega$ encoding of |Rec0|, |msfcata0|, and the sum type (+).}
\label{fig:proofsf}
\end{figure}
 
%% \begin{figure}
%% \SumDef
%% \caption{$F_\omega$ encoding of the sum type}
%% \label{fig:sumdef}
%% \end{figure}

\begin{figure}
\HOASshowFw
\caption{HOAS string formatting example in $F_\omega$.}
\label{fig:HOASshowFw}
\end{figure}

Figure \ref{fig:proofsf} is the $F_\omega$ encoding of
the inverse augmented datatype |Rec0| and its iteration |msfcata0|.
We use the sum type to encode |Rec0| since it consists of two constructors,
one for the inverse and the other for the recursion.  The newtype |Id| wraps
answer values inside the inverse. The iteration combinator |msfcata0| unwraps
the result (|unIn|) when |x| is an inverse.  Otherwise, |msfcata0| runs the
combining function |phi| over the recursive structure |(\f->f(phi Id))|.
The utility function |lift| abstracts a common pattern, useful
when we define the shorthand constructors (|lam| and |app|).

Figure \ref{fig:proofsf} also contains the $F_\omega$ encoding of the sum type
|(+)| and its constructors (or injection functions) |inL| and |inR|.
The case expression |caseSum| for the sum type is just binary function
application. In the $F_\omega$ encoding, they could be omitted
(i.e., |caseSum x f g| simplifies to |x f g|).  But, we choose to write
in terms of |caseSum| to make the definitions easier to read.

In Figure \ref{fig:HOASshowFw}, we define both an recursive datatype
for HOAS (|Exp|), and the string formatting function (|showExp|), 
with these $F_\omega$ encodings, just as we did in \S\ref{ssec:showHOASmsfcata}.
We can define simple expressions using the shorthand constructors and print out
those expressions using |showExp|.  For example,
\begin{quote}\noindent
$>$ |putStrLn (showExp (lam(\x->lam(\y->x))))|\\
\verb|(\a->(\b->a))|
\end{quote}

\newpage
\subsection{Evaluating Simply-Typed Higher-Order Abstract Syntax}
\label{sec:evalHOAS}
\begin{figure}
%include mendler/HOASeval.lhs
\caption{|msfcata1| example: an evaluator for simply-typed HOAS}
\label{fig:HOASeval}
\end{figure}
Surprisingly, we can write an evaluator for a simply-typed HOAS
in a surprisingly simple manner. In Figure \ref{fig:HOASeval}
is a Haskell program illustrating the technique.

We first define the simply-typed HOAS as a recursive indexed datatype
|Exp :: * -> *|. We take the fixpoint using |Rec1| (the fixpoint 
operation that supports a syntactic inverse). This fixpoint is taken over
a non recursive base structure (|ExpF :: (* -> *) -> (* -> *)|).
Note that |ExpF| is an indexed type. So expressions will be
indexed by their type. Using |Rec1| the fixpoint of any structure is
also parameterized by the type of the answer.

The use of the |msfcata| requires
that |Exp| should be parametric in this answer type
(by defining |type Exp t = forall a. Exp' a|) just as we did in the
untyped HOAS formatting example in Figure \ref{fig:HOASshow}.

Using general recursion, one would have defined
the datatype |Exp_g :: * -> *| that corresponds to |Exp|
as follows, using Haskell's native recursive datatype definition.
\begin{code}
data Exp_g t where
  Lam_g :: (Exp_g a -> Exp_g b) -> Exp_g (a -> b)
  App_g :: Exp_g (a -> b) -> Exp_g a -> Exp_g b
\end{code}

The definition of |evalHOAS| specifies how to evaluate an HOAS expression
to a host-language value (i.e. Haskell or Nax) wrapped by the identity newtype (|Id|).
In the description below, we ignore the wrapping (|MkId|) and unwrapping (unId) of |Id|
by completely dropping them from the description. See the Figure \ref{fig:HOASeval}
(where they are not omitted) if you care about these details. We discuss the
evaluation for each of the constructors of |Exp|,


\begin{itemize}
\item Evaluating an HOAS abstraction |(Lam f)| lifts an object-language function
(|f|) over |Exp| into a host-language function over values:
|(\v -> ev (f(inv v)))|. In the body of this host-language lambda abstraction
the inverse of the (host-language) argument value $v$ is passed to
the object-language function $f$. The resulting HOAS expression
|(f(inv v))| is evaluated by the recursive caller (|ev|) to obtain a host-language value.

\item Evaluating an HOAS application |(App f x)| lifts the function
  |f| and argument |x| to host-language values
        |(ev f)| and |(ev x)|, and uses host-language application
        to compute the resulting value. Note that the host-language application
        |((ev f) (ev x))| is type correct since
	|ev f :: a -> b| and |ev x ::  a|,
	thus the resulting value has type |b|.
\end{itemize}
We can be confident that |evalHOAS| indeed terminates
since |Rec1| and |msfcata1| can be embedded into \Fw\ in manner  
similar to the embedding of |Rec0| and |msfcata0| into \Fw\ in Figure \ref{fig:proofsf}.

Figure \ref{fig:HOASeval} highlights two advantages 
of the Mendler style over conventional style in one example.
This example shows that the Mendler-style Sheard--Fegaras iteration is
useful for both \textit{negative} and \textit{indexed} datatypes.
|Exp| in Figure \ref{fig:HOASeval} has both negative recursive occurrences
and type indices.

The |showHOAS| example in Figure \ref{fig:HOASshow}, which we discussed
in the previous subsection, has appeared in other work \cite{FegShe96},
written in conventional style.
So the |showHOAS| example, only shows that the Mendler style is
as expressive as the conventional style (although it is
perhaps syntactically more pleasant than the conventional style).
However, it is not obvious how one extends
the conventional-style Sheard--Fegaras iteration over indexed datatypes.

In contrast, the Mendler-style Sheard--Fegaras iteration is naturally
defined over indexed datatypes of arbitrary kinds. In fact, both the
the |msfcata1|, used in the |evalHOAS|, 
and |msfcata0|, used in the |showHOAS|,
have exactly the same syntatctic definition. They differ only
in their type signatures. This is illustrated
in Figures \ref{fig:rcombty} and \ref{fig:rcombdef}
on pages \pageref{fig:rcombty}-\pageref{fig:rcombdef}.

\subsection{Additional Mendler-style combinators}
The combinator |msfhist0| generalizes |mhist0| by the addition of an
abstract inverse to a combinator that already has an abstract unroller.
The combining function |phi| becomes a function of 4 arguments:
an abstract inverse, an abstract unroller,
a recursive caller, and a base structure.

The combinators |msfcata1| and |msfhist1| (at kind $* -> *$) generalize
the combinators |msfcata0| and |msfhist0| (at kind $*$) to combinators 
on types with a type index. The pattern of generalization is quite evident
in Figures \ref{fig:rcombty} (p\pageref{fig:rcombty}),
and \ref{fig:rcombdef} (p\pageref{fig:rcombdef}), and the reader is
encouraged to study those Figures for a complete understanding of
the results of this chapter.

We believe |msfcata1| might be useful for writing functions over
negative datatypes with type indices.  The combinator, |msfhist1|,
like its kind $*$ counterpart |msfhist0|, may not terminate given
ill-behaved |phi| functions. Such functions
use the unroller to {\it reach down inside a tree} to extract an 
embedded function, and then applies that function to an ancestor that
contains that function. Yet, they may be nevertheless useful 
for well-behaved |phi| functions. 

\begin{figure}
%{
%format e1
%format e2
%include mendler/OpenIt.lhs
%}
\caption{The Mender-style open-iteration |mopenit0|,
        which allows one free variable,
        and the |freevarused| function defined using |mopenit0|.}
\label{fig:openiter}
\end{figure}
\paragraph{}
In a HOAS, a meta-level function from expressions to expressions, represents
an expression with a single free variable. For example,
|\ x -> app (lam (\ f -> app f x))| represents |\ f -> f x|, where
|x| is free. The Mendler-style open-iterator (|mopenit0|) supports
computation over terms with one free variable represented in this fashion.
We write |mopenit0 (\x->e) v| for the open-iteration over an expression |e|
with a free variable |x|, the iteration should compute |v|,
when the computation reaches |x|.  For instance, the function
|freevarused| defined using |mopenit0| in Figure \ref{fig:openiter}
checks whether |x| appears in |e|, or is simply never mentioned.
There there is an open-iteration combinator at each kind (\eg, |mopenit1|
at kind |* -> *|), just like other combinators.
\citet{bgb} have studied open-iterations that support
more than one free variable, although not in Mendler style.

