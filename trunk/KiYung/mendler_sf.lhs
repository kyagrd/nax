%include includelhs2tex.lhs
\subsection{Negative datatypes, a second look} \label{ssec:tourNegative}

Let us revisit the negative inductive datatype |T|
(from \S\ref{sec:motiv}) from which we constructed a diverging computation.
%format T_m = T"_{\!m}"
%format C_m = C"_{\!m}"
%format p_m = p"_{\!m}"
%format w_m = w"_{\!m}"
We can define a Mendler style version of |T|, called |T_m|, as follows:
\begin{code}
data TBase r = C_m (r -> ())
type T_m = Mu0 TBase
\end{code}
If we can write two functions |p_m :: T_m -> (T_m -> ())|, 
and |w_m :: T_m -> ()|, corresponding to |p| and |w| from
\S\ref{sec:motiv}, we can reconstruct the same diverging computation.
The function
\begin{code}
w_m x = (p_m x) x
\end{code} 
is easy. The function
|p_m| is problematic. By the rules of the game,
we cannot pattern match on |In0|
(or use |out0|) so we must resort to using one of the
combinators, such as |mcata0|.
However, it is not possible to write |p_m|
in terms of |mcata0|.
Here is an attempt (seemingly the only one possible) that fails:
\begin{code}
p_m :: T_m -> (T_m -> ())
p_m =  mcata0 phi where
         phi :: (r -> (T_m -> ())) -> TBase r -> (T_m -> ())
         phi _ (C_m f) = f
\end{code}
We write the explicit type signature for the combining function |phi|
(even though the type can be inferred from the type of |mcata0|),
to make it clear why this attempt fails to type check. The combining
function |phi| take two arguments. The recursive placeholder (for which we
have used the pattern |_|, since we don't intend to call it) and the
base structure |(Cm f)|, from which we can extract
the function |f :: r -> ()|. Note that |r| is an abstract
(universally quantified) type, and the result type of |phi| requires
|f :: T_m -> ()|. The types |r| and |T_m| can never match, if |r|
is to remain abstract. Thus, |p_m| fails to type check.

There is a function, with the right type, that you can define:
\begin{code}
pconst :: T_m -> (T_m -> ())
pconst = mcata0 phi where phi g (C f) = const ()
\end{code}
Not surprisingly, given the abstract pieces composed of
the recursive placeholder |g :: r -> ()|, the base structure |(C f) :: TBase r|,
and the function we can extract from the base structure |f :: r -> ()|,
the only function that returns a unit value (modulo extensional
equivalence) is, in fact, the constant function returning the unit value.

This illustrates the essence of how Mendler catamorphism guarantees
normalization even in the presence of negative occurrences in the
recursive datatype definition. By quantifying over the recursive type
parameter of the base datatype (e.g. |r| in |TBase r|), it prevents an
embedded function with a negative occurrence from flowing into any
outside terms (especially terms embedding that function).

Given these restrictions, the astute reader may ask, are types with
embedded function with negative occurrences good for anything at all?
Can we ever call such functions?  A simple example which uses an
embedded function inside a negative recursive datatype is illustrated
in Figure \ref{fig:LoopHisto}.  The datatype |Foo| (defined as a fixpoint
of |FooF|) is a list-like data structure with two data constructors |Noo|
and |Coo|.  The data constructor |Noo| is like the nil and |Coo| is like
the cons.  Interestingly, the element (with type |Foo->Foo|) contained in |Coo|
is a function that transforms a |Foo| value into another |Foo| value.
The function |lenFoo|, defined with |mcata0|, is a length like function,
but it recurses on the transformed tail, |(f xs)|,
instead of the original tail |xs|.
The intuition behind the termination of |mcata0| for this negative datatype
|Foo| is similar to the intuition for positive dataypes.  The embedded function
|f::r->r| can only apply to the direct subcomponent of its parent, or to its
sibling, |xs| and its transformed values (e.g. |f xs|, |f (f xs)|, $\ldots$),
but no larger values that contains |f| itself.  We illustrate a general proof
on termination of |mcata0| in Figure \ref{fig:proof}. %% \S\ref{sec:proof}.

\begin{figure}
%include mendler/LoopHisto.lhs
\caption{An example of a total function |lenFoo|
         over a negative datatype |Foo| defined with |mcata0|,
     and a counter-example |loopFoo| illustrating that |mhist0|
         can diverge for negative datatypes.}
\label{fig:LoopHisto}
\end{figure}

While all functions written in terms of |mcata0| are total, the
same cannot be said of function written in terms of |mhist0|.
The function |loopFoo| defined with |mhist0| is a counter-example to totality, which
shows that Mendler style histomorphisms do not always terminate.
Try evaluating |loopFoo foo|.  It will loop.  This function |loopFoo| is
similar to |lenFoo|, but has an additional twist.  At the very end of the
function definition, we recurse on the transformed tail |(f' xs)|,
when we have more than two elements where the first and second elements
are named |f| and |f'|, respectively.  Note, |f'| is an element embedded
inside the tail |xs|.  Thus, |(f' xs)| is dangerous since it applies |f'|
to a larger value |xs|, which contains |f'|.
The abstract type of the unrolling function (|out::r->f r|),
prevents the recursive placeholder from being applied to a larger value, but it
does not preclude the risk of embedded functions, with negative domains,
being applied to larger values which contain the embedded function
itself.

%% One should not be punished just by defining negative recursive types as long
%% as one uses them in a safe way.  We know from functional programming examples
%% that negative occurrences have real constructive uses, how do we generalize
%% the Mendler Hierarchy to express these useful examples?  If you guessed that
%% we will make the combining function |phi| abstract over yet another argument
%% you are correct.

\section{Formatting Higher-Order Abstract Syntax}\label{sec:showHOAS}

To lead up to the Mendler style solution
to formatting HOAS, we first review
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
It is a coincidence that Mendler style recursion combinators also use the same
technique, parametricity, for a different purpose, to guarantee termination.
Fortunately, these two approaches work together
without getting in each other's way.  

%include mendler/HOASshow.lhs
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

\subsection{A general recursive implementation for open HOAS}
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
%% This is the very kind of action Mendler style combinators prevent.
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

\subsection{A Mendler style solution for closed HOAS}
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
expressions such as |Inverse0 True|, except for using them as placeholders
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
        recursive placeholder, and a base structure.
\begin{code}
  msfcata phi (Roll0 x)          = phi Inverse0           (msfcata phi)  x
  msfcata phi (Inverse0 z)       = z
\end{code}
  \item For inverse values, return the value inside |Inverse0| as it is.
  \item We use higher-rank polymorphism to insist that 
        the abstract inverse function, with type (|a -> r a|),
        the recursive placeholder function, with type (|r a -> a|), and
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

\subsection{Additional generalization}
The combinator |msfhist0| generalizes |mhist0| by adding an abstract inverse to
a combinator that already has an abstract unroller.
The combining function |phi| becomes a function of 4 arguments:
an abstract inverse, an abstract unroll,
a recursive placeholder, and a base structure.

The rank 1 combinators |msfcata1| and |msfhist1| generalize
the rank 0 combinators |msfcata0| and |msfhist0| to combinators 
on types with an index. The pattern of generalization is
quite evident in Figures \ref{fig:rcombty}, and \ref{fig:rcombdef},
and the reader is encouraged to study those Figures for
a complete understanding of the results of this paper.

We believe |msfcata1| would be useful for writing functions over negative datatypes with
type indices.  The combinator, |msfhist1|, like its rank 0 counterpart
|msfhist0|, may not terminate given ill-behaved |phi| functions
that extract embedded functions, and then apply them to
parts of the tree which contain those functions. Yet, they
are nevertheless useful functions. 


