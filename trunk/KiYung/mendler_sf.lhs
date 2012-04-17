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
inductive type definition. By quantifying over the recursive type
parameter of the base datatype (e.g. |r| in |TBase r|), it prevents an
embedded function with a negative occurrence from flowing into any
outside terms (especially terms embedding that function).

Given these restrictions, the astute reader may ask, are types with
embedded function with negative occurrences good for anything at all?
Can we ever call such functions?  A simple example which uses an
embedded function inside a negative inductive datatype is illustrated
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
%include LoopHisto.lhs
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

%% One should not be punished just by defining negative inductive types as long
%% as one uses them in a safe way.  We know from functional programming examples
%% that negative occurrences have real constructive uses, how do we generalize
%% the Mendler Hierarchy to express these useful examples?  If you guessed that
%% we will make the combining function |phi| abstract over yet another argument
%% you are correct.

