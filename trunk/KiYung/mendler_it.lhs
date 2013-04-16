%include includelhs2tex.lhs
\section{Defining recursive regular datatypes} \label{ssec:tourRegular}
In the Mendler-style approach, we define recursive datatypes
as fixpoints of non-recursive base datatypes.  For example, the following
are definitions of the natural number type in the general recursion style (left)
and in the Mendler style (right).
\begin{center}
\begin{minipage}{.49\linewidth}
\begin{code}
{-""-}
data Nat
   =  Z
   |  S Nat
\end{code}
\end{minipage}
\begin{minipage}{.49\linewidth}
\begin{code}
data N r = Z | S r
type Nat = Mu0 N
zero     = In0 Z
succ n   = In0 (S n)
\end{code}
\end{minipage}
\end{center}
Note, in Mendler style, we define |Nat| by applying the fixpoint |Mu0| to
the base |N|.  The type argument |r| in the base |N| is intended to denote
the points of recursion in the recursive datatype.  Here, we have only
one point of recursion at |S|, the successor data constructor.
Then, we define the shorthand constructors |zero| and |succ| (on the right),
which correspond to the data constructors |Z| and |S| of
the natural number datatype in the general recursive encoding (on the left).  
We can express the number 2 as |S (S Z)| in the general recursive encoding,
and |succ (succ zero)| or |In0 (S (In0 (S (In0 Z))))| in the Mendler-style
encoding.

We can also define parameterized datatypes, such as lists, in the Mendler style,
using the same datatype fixpoint |Mu0|, provided that we consistently order
the parameter arguments (|p|) to come before the type argument that denotes
the recursion points (|r|) in the base datatype definition (|L p r|):
\vspace*{-1em}
\begin{center}
\begin{minipage}{.49\linewidth}
\begin{code}
{-""-}
data List p 
   =  N
   |  C p (List p)
\end{code}
\end{minipage}
\begin{minipage}{.49\linewidth}
\begin{code}
data L p r = N | C p r
type List p = Mu0 (L p)
nil        = In0 N
cons x xs  = In0 (C x xs)
\end{code}
\end{minipage}
\end{center}
Note, we define |List p| as |Mu0 (L p)|, which is the fixpoint of
the partial application of the base |L| to the parameter |p|.
%% Then,
%% we define the shorthand constructors |nil| and |cons|, which correspond to
%% the data constructors |N| and |C| of list type in the general recursive encoding.
We can express the integer list with two elements 1 and 2 as |C 1 (C 2 N)|
in the general recursive encoding, and |cons 1 (cons 2 nil)| or
|In0 (C 1 (In0 (C 2 (In0 N))))| in the Mendler-style encoding.


\section{Conventional iteration for regular datatypes} \label{ssec:convCata}
The conventional iteration\footnote{Also known as catamorphism.
In Haskell-ish words, |foldr| on lists generalized to other dataypes}
is defined on the very same fixpoint, |Mu0|, as is used in the Mendler style,
provided that the base datatype |f| is a functor.
This, more widely known approach \cite{hagino87phd}, was developed independently,
and at about the same time, as the Mendler style.

The additional requirement, that the base datatype (|f|) is a functor, shows up
as a type class constraint (|Functor f|) in the type signature of
the conventional iteration combinator |cata|:\\
\hspace*{.1in} |cata :: Functor f => (f a -> a) -> Mu0 f -> a| \hspace*{.1in} (Figure \ref{fig:rcombty}).\\
This is necessary because |cata| is defined in terms of |fmap| (a method of the |Functor| class):\\
\hspace*{.1in} |cata phi (In0 x) = phi (fmap (cata phi) x)| \hspace*{.1in}  (Figure \ref{fig:rcombdef}).\\
The combinator |cata| takes a combining function |phi :: f a -> a|, which
assumes the recursive subcomponents (\eg, tail of the list) have already been
turned into a value of answer type (|a|) and combines the overall result.

%format lenc = len"_{\!c}"
A typical example of iteration is the list length function.  We can define
the list length function |lenc| in conventional style, as
 in Figure \ref{fig:lenc}, which corresponds to
the list length function |len| in the general recursion style
in the left-hand side of Figure \ref{fig:len}.
\begin{figure}
\begin{minipage}{.45\linewidth}
\begin{code}
lenc :: List p -> Int
lenc = cata phi where  
   phi N            = 0
   phi (C x xslen)  = 1 + xslen
\end{code}
\end{minipage}
\begin{minipage}{.5\linewidth}
\begin{code}
instance Functor (L p) where
   fmap f N         = N
   fmap f (C x xs)  = C x (f xs)
\end{code}
\end{minipage}
\caption{|cata| example: list length function}
\label{fig:lenc}
\end{figure}
Of course, we need the functor instance for the base |L p|,
which properly defines |fmap|, to complete the definition.

The conventional iteration is widely known, especially on the list type,
as |foldr|. The conventional iteration is more often used than
the Mendler-style iteration, but it does not generalize easily to more
exotic datatypes such as nested datatypes and GADTs.
%format lenm = len"_{\!m}"
\begin{figure}
\begin{minipage}{.49\linewidth}
%include mendler/LenG.lhs
\end{minipage}
\begin{minipage}{.49\linewidth}
%include mendler/Len.lhs
\end{minipage}
\caption{|mcata0| example: list length function}
\label{fig:len}
\end{figure}




\section{Mendler-style iteration (|mcata|) for regular datatypes}
\label{ssec:tourCata0}
The Mendler-style iteration combinator |mcata0| lifts the restriction that the
base type be a functor, but still maintains the strict termination behavior of
|cata|. This restriction is lifted by using two devices.
\vspace*{-.5em}
\begin{itemize}
  \item The combining function |phi| becomes a function of two arguments
        rather than one. The first argument is a function that represents a
        recursive caller, and the second is the base structure
        that must be combined into an answer. The recursive caller 
        allows the programmer to direct where recursive calls must be made.
        The Functor class requirement is lifted, because the definition of
	|mcata0| does not rely on |fmap|:
\begin{code}
mcata0 phi (In0 x) = phi (mcata0 phi) x
\end{code}
  \item The second device is the use of higher-rank polymorphism to insist
        that the recursive caller, with type (|r -> a|), and
        the base structure, with type (|f r|),
        work over an abstract type, denoted by (|r|). 
\begin{code}
mcata0:: (forall r. (r -> a) -> (f r -> a)) -> Mu0 f -> a
\end{code}
\end{itemize}
\vspace*{-.2em}

Under what conditions do |mcata0| calls always terminate? Although we defined
|Mu0| as a newtype and |mcata0| as a function in Haskell, you should consider
them as an information hiding abstraction. The rules of the game (which will be enforced in Trellys)
require programmers to construct values using the |In0| constructor (as in
|zero|, |succ|, |nil| and |cons|), but forbid programmers from deconstructing those
values by pattern matching against |In0| (or, by using the selector function
|out0|). These operations are hidden by the abstraction boundary (or in the case
of Trellys' logicality inference, lead to classifying a term as programatic,
rather than as logical). To remain in the logical (terminating) classification,
whenever you need to decompose values of recursive datatypes you must do it via
|mcata0| (or, any of the other terminating Mendler-style combinators).
To conform to these rules, all functions over positive recursive datatypes,
except the trivial ones such as identity and constant functions (which don't
inspect their structure), need to be implemented in terms of the combinators
described in Figure \ref{fig:rcombty}. For negative recursive datatypes
only the combinators in the iteration family ensure termination.

The intuitive reasoning behind the termination property of |mcata0| for
all positive recursive datatypes is that (1) |mcata0| strips off one |In0|
constructor each time it is called, and (2) |mcata0| only recurses on the
direct subcomponents (\eg, tail of a list) of its argument (because the type
of the recursive caller won't allow it to be applied to anything else).
Once we observe these two properties, it is obvious that |mcata0| always
terminates since those properties imply that every recursive call to |mcata0|
decreases the number of |In0| constructors in its argument.\footnote{We assume
that the values of recursive types are always finite. We can construct infinite
values (or, co-recursive values) in Haskell exploiting lazyness, but we exclude
such infinite values from our discussion in this work, and this property is
a fundamental design decision in Trellys.} 

The first property is easy to observe from the definition of |mcata0|
in Figure \ref{fig:rcombdef}, in particular, the pattern matching of
the second argument with |(In0 x)|.  The second property is enforced
by the parametricity in the type of the combining function |phi| of
the |mcata0| combinator as shown in Figure \ref{fig:rcombty},

In Figure \ref{fig:len}, we redefine the length function (|lenm| on the right),
this time, using a Mendler-style iteration.  In the definition of |lenm|,
we name the first argument of |phi|, the recursive caller, to be |len|.
We use this |len| exactly where we would recursively call the recursive function
in the general recursion style (|len| on the left).

However, unlike the general recursion style, it is not possible to call
|len::r->Int| on anything other than the tail |xs::r|.
Using general recursion, we could easily err (by mistake or by design)
causing length to diverge, if we wrote its second equation as follows: 
|len (C x xs) = 1 + len (C x xs)|. 

We cannot encode such diverging recursion in the Mendler style because
|len::r->Int| requires its argument to have the parametric type |r|,
while |(C x xs) :: L p r| has more specific type than |r|.
The parametricity enforces weak structural induction.

The scheme of having the combining function |phi| abstract over the
recursive caller |len| is a powerful one.  We will reuse
this strategy, generalizing |phi| to abstract over
additional arguments, in order to generalize |mcata0| to become more expressive.


