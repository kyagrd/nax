%include includelhs2tex.lhs

%format NP = N"_{\!P}"
%format CP = C"_{\!P}"
%format nilp = nil"_{\!"P"}"
%format consp = cons"_{\!"P"}"
%format psumm = psum"_{\!m}"
%format NB = N"_{\!B}"
%format CB = C"_{\!B}"
%format nilb  = nil"_{\!B}"
%format consb = cons"_{\!B}"
%format bsumm = bsum"_{\!m}"

\subsection{Nested datatypes} \label{ssec:tourNested}
The datatypes |Nat| and |List|, defined in \S\ref{ssec:tourRegular}, 
are regular datatypes.  Non-recursive datatypes (e.g., |Bool|) and
recursive datatypes without any type arguments (e.g., |Nat|)
are always regular.  Among the recursive datatypes with type arguments,
those datatypes where all of the recursive occurrence on the right-hand side
have exactly the same type argument as the left-hand side (in the same order)
are considered regular.  For example, the list datatype
%% \begin{code}
$\,$ |data List p = N || C p (List p)| $\,$
%% \end{code}
is regular since |(List p)| appearing on right-hand side takes exactly the same
argument |p| as the |(List p)| in the left-hand side (|data List p = |$\,\ldots$).

Note, every concrete {\em instantiation} of the list datatype has an equivalent
non-parameterized datatype definition.
For instance, |List Bool| is equivalent to the following datatype:
%format ListBool = List"_{"Bool"}"
%format NBool = N"_{"Bool"}"
%format CBool = C"_{"Bool"}"
\begin{code}
data ListBool = NBool | CBool Bool ListBool
\end{code}
This {em instantiation} property does {\em not} hold for nested datatypes.

Type arguments that never change in any recursive occurrences
in a datatype definition are called \emph{type parameters}.
Type arguments that do change are called \emph{type indices}.
Datatypes with only type parameters are always regular.
Nested datatypes \cite{BirMee98} are non-regular datatypes where
type arguments in some of the recursive occurrences in the recursive
datatype equation differ from the left-hand side of the datatype equation.

Such types can be expressed in Haskell and ML without using GADT extensions.
%% We introduce two well-known examples, powerlists and bushes.
We introduce a well-known example of the bush datatype, and
%% We illustrate the Mendler style by writing
a function that sums up the elements of bush (Figure \ref{fig:bsum}).
Nested datatypes require us to move from rank 0 Mendler combinators
to rank 1 Mendler combinators.\footnote{The rank of a kined is defined by
the equations $\textrm{rank}(*)=0$ and
$\textrm{rank}(\kappa -> \kappa')=
   \textrm{max}(1+\textrm{rank}(\kappa),\textrm{rank}(\kappa'))$.
Rank 0 Mendler combinators work on recursive types of kind $*$, whose rank 0,
constructed from rank 1 base structure of kind $* -> *$.
Rank 1 Mendler combinators work on recursive type constructors of kind $* -> *$,
whose rank is 1, constructed from rank 1 base structure of kind
$(* -> *) -> (* -> *)$. We could have called them Rank 1 Mendler combinator
and Rank 2 Mendler combinator, matching the rank of the base structure
instead of the rank of the recursive type constructor, but just happen to
prefer counting from 0.}

The powerlist datatype is defined as follows:
\begin{code}
data Powl i = NP  | CP i (Powl (i,i))
\end{code}
The type argument |(i,i)| for |Powl| occurring on the right-hand side is
different from |i| appearing on the left-hand side.  Type arguments that
occur in variation on the right-hand side, like |i|, are type indices.

This single datatype equation for |Powl| relates a family of datatypes:
the tail of an |i|-powerlist is a |(i,i)|-powerlist,
its tail is a |((i,i),(i,i))|-powerlist, and so on.
More concretely,
\begin{code}
ps    = CP 1 ps'             :: Powl Int
ps'   = CP (2,3) ps''        :: Powl (Int,Int)
ps''  = CP ((4,5),(6,7)) NP  :: Powl ((Int,Int),(Int,Int))
\end{code}
The tail of |ps| is |ps'|, and the tail of |ps'| is |ps''|.
We can observe that the shape of elements includes deeper nested pairs
as the type indices become more deeply nested.

The bush datatype is defined as follows (also in Figure \ref{fig:bsum}):
\begin{code}
data Bush  i = NB  | CB i (Bush (Bush i))
\end{code}
The type argument |i| for |Bush| is a type index, since
the type argument |(Bush i)| occurring on the right-hand side is
different from |i| appearing on the left-hand side.  What is intriguing
about |Bush| is that the variation on the type index involves itself.
\citet{Mat09} calls such datatypes, like |Bush|, \emph{truly nested datatypes}.
Here are some examples of bush values:
\begin{code}
bs    = CB 1 bs'           :: Bush Int
bs'   = CB (CB 2 NB) bs''  :: Bush (Bush Int)
bs''                       :: Bush (Bush (Bush Int))
bs''  = CB (CB (CB 3 NB) (CB (CB (CB 4 NB) NB) NB)) NB
\end{code}
The tail of |bs| is |bs'|, and the tail of |bs'| is |bs''|.
We can observe that the shape of the elements becomes more deeply nested as we
move towards latter elements.
Note, the element type of bushes becomes nested by bushes themselves.

%% On the left-hand side of Figure \ref{fig:psum}
%% we define a function that sums up all the nested elements in a powerlist
%% using the general recursion style. This function takes 2 parameters:
%% a function that turns elements into integers, and the powerlist itself.
%% The key part in the definition of |psum| is constructing the function
%% |(\(x,y)->f x+f y) :: (i,i) -> Int|. We must
%% construct this function, on the fly, in order
%% to make the recursive call of |psum| on its tail |xs :: Powl (i,i)|.
%% Without this function, the recursive call wouldn't know how to sum up paired elements.
%% Note this kind of recursive call is an instance of polymorphic recursion.
%% 
%% We can specialize |psum|, for instance, for integer powerlists as follows
%% by supplying the identity function:
%% \begin{code}
%% sumP :: Powl Int -> Int
%% sumP xs = psum xs id
%% \end{code}
%% Using |sumP|, we can sum up |ps| defined above: |sumP ps ~> 28|.

%% On the left-hand side of Figure \ref{fig:bsum}, we similarly define a
%% function that sums up all the nested elements in a bush using general
%% recursion. As we did with |psum|, |bsum| can sum up any powerlist |(Bush i)|,
%% once we supply a function |f :: i->Int| that maps elements to integers. The
%% key part in the definition of |bsum| is constructing the function |(\ys->bsum
%% ys f) :: Bush i -> Int| on the fly.  Without this function the recursive call
%% of |bsum| on the tail |xs :: Bush (Bush i)| would be incomplete. As before,
%% we can specialize |bsum|, for integer bushes as follows by
%% supplying the identity function:

\begin{landscape}
\begin{figure*}
%include mendler/PowlG.lhs
%include mendler/Powl.lhs
\begin{minipage}{.49\linewidth}
\PowlSumG
\end{minipage}
\begin{minipage}{.49\linewidth}
\PowlSum
\end{minipage}
\caption{Summing up a powerlist (|Powl|), a nested datatype,
         expressed in terms of |mcata1|.}
\label{fig:psum}
\end{figure*}
\end{landscape}

\begin{landscape}
\begin{figure*}
%include mendler/BushG.lhs
%include mendler/Bush.lhs
\begin{minipage}{.49\linewidth}
\BushSumG
\end{minipage}
\begin{minipage}{.49\linewidth}
\BushSum
\end{minipage}
\caption{Summing up a bush (|Bush|), a recursively nested datatype,
         expressed in terms of |mcata1|.}
\label{fig:bsum}
\end{figure*}
\end{landscape}

We can define a function that sums up all the nested elements in a bush.
Let us first take a look at the function |bsum| in the general recursion style,
on the left-hand side of Figure \ref{fig:bsum}.
This function takes 2 parameters: a bush to sum up and a function that
turns elements into integers.  The key part in the definition of |bsum| is
constructing the function |(\ys->bsum ys f) :: Bush i -> Int|.  We must
construct this function, on the fly, in order to make the recursive call of
|bsum| on its tail |xs :: Bush (Bush i)|.  Without this function,
the recursive call wouldn't know how to sum up bushed elements.
%% Note this kind of recursive call is an instance of polymorphic recursion.

We can specialize |bsum|, for instance, for integer bushes as follows
by supplying the identity function:
\begin{code}
sumB :: Bush Int -> Int
sumB xs = bsum xs id
\end{code}
Using |sumB|, we can sum up |bs| defined above: |sumB bs ~> 10|.

Before discussing the Mendler style version, let us take a look at yet another
general recursive version of the function |bsum'|, which explicitly wraps up
the answer values of type |(i->Int) -> Int| inside the newtype |Ret i|.
The relations between the plain vanilla version and the wrapped up version
are simply:
\begin{code}
       bsum  = unRet .  bsum'
Ret .  bsum  =          bsum'
\end{code}
The wrapped up version |bsum'| has the same structure as the Mendler style
version |bsumm| found on the right-hand side of Figure \ref{fig:bsum}.
The wrapping of the answer type is for purely technical reasons:
to avoid the need for higher-order unification.
If we were to work with the unwrapped answer type in the Mendler style,
the type system would need to unify (|a i|) with (|(i->Int) -> Int|),
which is a higher-order unification, whereas unifying (|a i|) with
the wrapped answer type (|Ret i|) is first-order.
The type inference algorithm of Haskell (and most other languages)
does not support higher-order unification.\footnote{We may avoid higher-order
unification, either by making the Mendler-style combinators language constructs
(rather than functions) so that the type system treats them with specialized
typing rules; or by providing a version of the combinators with syntactic
Kan-extension as in \cite{AbeMatUus05}.}

Finally, let us discuss the summation function for bushes using
the Mendler style, found on the right-hand side in Figure \ref{fig:bsum}.
First, we give Mendler style datatype definitions for bushes.  As usual,
we define the datatype |Bush| as a fixpoint of the base |BushF|.
However, an important difference that readers should notice is the use of
fixpoint |Mu1| at kind $* -> *$ bases, instead of |Mu0|, for the kind $*$ bases
inducing regular datatypes.

That the type argument |i| in |Powl i| and |Bush i| is a type index that
forces us to choose the fixpoint on kind $* -> *$ (and its related recursion
combinators). Note, in the definition of the base types |PowlF| and 
type |BushF|, we place the index |i| after the type argument |r| for
the recursion points. This is the convention we use. We always write
parameters (|p|), before the recursion point arugment (|r|), followed by
indices (|i|).  Figure \ref{fig:vec}, which we will shortly discuss
in \S\ref{ssec:tourIndexed}, contains an example where there are both
type parameters and type indices in a datype (|Vec p i|). 

Getting back to the right-hand side of Figure \ref{fig:bsum},
since we used |Mu1| to define the recursive datatypes, we use |mcata1|,
the Mendler style iteration combinator at kind $* -> *$, to define
the functions. The beauty of the Mendler style approach is that
the implementation of the recursion combinators for higher-ranks
(or, higher-kinds) are \emph{exactly the same} as their kind $*$ counterparts.
The definitions differ only in their type signatures. As you can see in Figures 
\ref{fig:rcombty} and \ref{fig:rcombdef}, |mcata1| has a richer type than
|mcata0|, but their implementations are \emph{exactly the same}!
This is not the case for the conventional approach.
The definition of |cata| won't generalize to nested datatypes in a trivial way.
There has been several approaches \cite{BirPat99,MarGibBay04,Hin00}
to extend folds or catamorphisms for nested datatypes
in the conventional setting.

