%include includelhs2tex.lhs
\section{Mendler-style course-of-values iteration (|mhist|) for regular datatypes}
\label{ssec:tourHist0}
Some computations are not easily expressible by iteration,
since iteration only recurses on the direct subcomponents (\eg, tail
of a list). Terminating recursion shcemes on deeper subcomponents
(\eg, tail of tail of a list) requires rather complex encodings
in the conventional setting. Unfortunately, functional programmers often
write simple recursive functions using nested pattern matching that
recurse on deep subcomponents exposed by the nested patterns.
A typical example is the Fibonacci function:
\vspace*{.5em}
\begin{code}
fib Z          = 0
fib (S Z)      = 1
fib (S (S m))  = fib (S m) + fib m
\end{code}\vspace*{-.5em}\\
Note, in the third equation |fib| recurses on both the predecessor |(S m)|,
which is a direct subcomponent of the argument, and the predecessor of
the predecessor |m|, which is a deeper subcomponent of the argument.
The Histomorphism \cite{UusVen99histo} captures such patterns of recursion.
The Histomorphism is also known as the course-of-values iteration.

In the conventional style, course-of-values iteration are defined through
co-algebraic construction of an intermediate stream data structure that
pairs up the current argument and the results from the previous steps.
There are two ways of implementing this.  One is a memoizing bottom-up version,
and the other is a non-memoizing version that repeats the computation of
the previous steps.  We are not going to show or discuss those implementations
here, but the point we want to make is that both versions need to be
implemented through co-algebraic construction \cite{UusVen00,vene00phd}.
Course-of-values iteration expressed in terms of this co-algebraic style will
look very different from its equivalent in general recursion style. One needs
to extract both the original arguments and the deep result values from the
stream explicitly calling on stream-head and stream-tail operations.
However, in the Mendler style, we do not need such co-algebraic construction
at least for the non-memoizing version.\footnote{The Mendler-style
histormophism combinators implemented here are the non-memoizing ones.
\citet{vene00phd} suggests how to implement a memoizing 
Mendler-style histomorphism, which uses co-algebraic construction.}.

In the Mendler-style course-of-values iteration (|mhist|),
we play the same trick we played in the Mendler-style iteration (|mit|).
We arrange for the combining function to take additional arguments
(Figures \ref{fig:rcombty} and \ref{fig:rcombdef}).
\begin{itemize}
  \item The combining function |phi| now becomes a function of 3 arguments. 
        The first argument is a function that represents an
        abstract unrolling function that projects out the value
        embedded inside the data constructor |In0| by accessing
        the projection function |out0| given in the definition.
        As in |mcata0|,
        the next argument represents a recursive caller, and
        the last argument represents the base structure
        that must be combined into an answer.

  |mhist0 phi (In0 x) = phi out0 (mhist0 phi) x|

  \item Again we use higher-rank polymorphism to insist that 
        the abstract unrolling function, with type (|r -> f r|),
        the recursive caller function, with type (|r -> a|), and
%%%%%%% the recursion points, with type (|r|), in
        the base structure, with type (|f r|), only work
        over an abstract type, denoted by (|r|).
        
  |mhist0 :: (forall r . (a -> f a) -> (r -> a) -> (f r -> a)) -> {-"\cdots"-}|
\end{itemize}  

The Mendler-style course-of-values iteration is much handier
than the conventional course-of-values iteration \cite{UusVen00}. For example,
in Figure \ref{fig:fib}, the definition for the Fibonacci function in the
general recursion style (left) and the definition in the Mendler style (right)
look almost identical.  Particularly, when we have unrolled the nested pattern
matching in the general recursive definition into a case expression.
The only difference between the two, is that in the Mendler style (left),
we pattern match over |out n| in the case expression, in the gerneral recursion
style (right) we pattern match over |n|.  

\begin{figure}
\begin{minipage}{.49\linewidth}
%include mendler/FibG.lhs
\end{minipage}
\begin{minipage}{.49\linewidth}
%include mendler/Fib.lhs
\end{minipage}
\caption{|mhist0| example: Fibonacci function}
\label{fig:fib}
\end{figure}

Let us visually relate the definition of |mhist0| with the second equation of
|phi| in the definition of the Fibonocci function as follows:
\begin{code}
mhist0 phi (In0 x) =  phi  out0            (mhist0 phi)         {-"~~"-}x
                           {-"~~\vdots"-}  {-"~~~~~\vdots"-}    {-"~~~\vdots"-}
                      phi  out             {-"~~~"-}fib         (S n)  =
                          case out n of
                            Z     -> 1
                            S n'  -> fib n + fib n'
\end{code}      
The abstract unrolling function |out| and the recursive caller |fib|
stand for the actual arguments |out0| and |(mhist0 phi)|, but the higher-rank
type of the combining function |phi| ensures that they are only used in a safe
manner.  The abstract unrolling function |out| enables us to discharge |In0|
as many times as we want inside |phi|. 

From the programmers perspective, |out0| is a hidden primitive,
hidden by the |mhist0| abstraction (\ie, only used within the definition of
combinators like |mhist0| but not in the user-defined functions).
But, inside the definition of the combining function |phi|,
the programmer can actually access the functionality of |out0|
through the abstract unrolling function |out|. The higher-rank types limit
the use of this abstract unrolling function |out| to values of type |r|.

In a positive recursive datatype, the only functions with domain |r|
are the abstract unroller, and the recursive caller.
The programmer can only
{\em whittle down} the |r| values inside the base structure,
of type (|f r|), into smaller structures, of type (|f r|). The programmer can
then decompose these into even smaller |r| values by pattern matching against
the data constructors of the base |f|. However, there is no way to combine
any of these decomposed |r| values to build up larger |r| values.
The only possible use of the decomposed |r| values is to call
the recursive caller, with type (|r -> a|).

For example, in Figure \ref{fig:fib}, we pattern match over (|out n|),
discharging the hidden |In0| constructor of |n|.  Note the types inside
the |(S n')| pattern matching branch: |n :: r|; |(out n) :: (N r)|;
and |n' :: r|.  What can we possibly do with |n| and |n'|, of type |r|?
The only possible computation is to call
 |fib :: r -> Int| on |n| and |n'|,  as we do in |fib n + fib n'|.
It is a type error to call |fib :: r -> Int| on either |(S n) :: N r|
or |(S n') :: N r|. This is why the termination property of |mhist0|
continues to hold for positive datatypes. In \S\ref{sec:fixi:cv}
We discuss further on when Mendler-style course-of-values recursion is
guaranteed to terminate.

For negative datatypes, however, we have additional functions with domain |r|.
Inside the |phi| function passed to |mhist0|, the embedded functions with
negative occurrences, will have type |r| as their domain.
These can be problematic, as shown in Figure \ref{fig:LoopHisto},
which conatins the counter-example to termination of |mhist0|.
In the following section (\S\ref{ssec:tourNegative}), we will discuss
why |mhist| family fails to guarantee termination for negative datatypes
while |mcata| family guarantees termination for arbitrary datatypes
including negative datatypes.

\section{Properties of |mcata| and |mhist| for negative datatypes}
\label{ssec:tourNegative}

Let us revisit the negative inductive datatype |T|
(from \S\ref{sec:mendler:motiv}) from which we constructed a diverging computation.
%format T_m = T"_{\!m}"
%format C_m = C"_{\!m}"
%format p_m = p"_{\!m}"
%format w_m = w"_{\!m}"
We can define a Mendler-style version of |T|, called |T_m|, as follows:
\begin{code}
data TBase r = C_m (r -> ())
type T_m = Mu0 TBase
\end{code}
If we can write two functions |p_m :: T_m -> (T_m -> ())|, 
and |w_m :: T_m -> ()|, corresponding to |p| and |w| from
\S\ref{sec:mendler:motiv}, we can reconstruct the same diverging computation.
The function
\begin{code}
w_m x = (p_m x) x
\end{code} 
is easy. The function |p_m| is problematic. By the rules of the game, we cannot
pattern match on |In0| (or use |out0|) so we must resort to using one of
the combinators, such as |mcata0|. However, it is not possible to write |p_m|
in terms of |mcata0|. Here is an attempt (seemingly the only one possible)
that fails:
\begin{code}
p_m :: T_m -> (T_m -> ())
p_m =  mcata0 phi where
         phi :: (r -> (T_m -> ())) -> TBase r -> (T_m -> ())
         phi _ (C_m f) = f
\end{code}
We write the explicit type signature for the combining function |phi|
(even though the type can be inferred from the type of |mcata0|),
to make it clear why this attempt fails to type check. The combining
function |phi| take two arguments. The recursive caller (for which we
have used the pattern |_|, since we don't intend to call it) and the
base structure |(Cm f)|, from which we can extract the function |f :: r -> ()|.
Note that |r| is an abstract type (since it is universally quantified
in the function argument), and the result type of |phi| requires
|f :: T_m -> ()|. The types |r| and |T_m| can never match, if |r|
is to remain abstract. Thus, |p_m| fails to type check.

There is a function, with the right type, that you can define:
\begin{code}
pconst :: T_m -> (T_m -> ())
pconst = mcata0 phi where phi g (C f) = const ()
\end{code}
Not surprisingly, given the abstract pieces composed of
the recursive caller |g :: r -> ()|, the base structure |(C f) :: TBase r|,
and the function we can extract from the base structure |f :: r -> ()|,
the only function that returns a unit value (modulo extensional
equivalence) is, in fact, the constant function returning the unit value.

This illustrates the essence of how the Mendler-style iteration guarantees
normalization even in the presence of negative occurrences in the
recursive datatype definition. By quantifying over the recursive type
parameter of the base datatype (\eg, |r| in |TBase r|), it prevents an
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
sibling, |xs| and its transformed values (\eg, |f xs|, |f (f xs)|, $\ldots$),
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
shows that the Mendler-style course-of-values iteration do not always terminate.
Try evaluating |loopFoo foo|.  It will loop.  This function |loopFoo| is
similar to |lenFoo|, but has an additional twist.  At the very end of the
function definition, we recurse on the transformed tail |(f' xs)|,
when we have more than two elements where the first and second elements
are named |f| and |f'|, respectively.  Note, |f'| is an element embedded
inside the tail |xs|.  Thus, |(f' xs)| is dangerous since it applies |f'|
to a larger value |xs|, which contains |f'|.
The abstract type of the unrolling function (|out::r->f r|),
prevents the recursive caller from being applied to a larger value, but it
does not preclude the risk of embedded functions, with negative domains,
being applied to larger values which contain the embedded function itself.

%% One should not be punished just by defining negative recursive types as long
%% as one uses them in a safe way.  We know from functional programming examples
%% that negative occurrences have real constructive uses, how do we generalize
%% the Mendler Hierarchy to express these useful examples?  If you guessed that
%% we will make the combining function |phi| abstract over yet another argument
%% you are correct.



