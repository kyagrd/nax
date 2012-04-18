%include includelhs2tex.lhs
\section{A Tour of the Mendler style Approach}\label{sec:tour}
%include mendler/RecComb.lhs
%include mendler/CataViaHisto.lhs
%include mendler/Proof.lhs

In this section we give a tour of the Mendler style approach,
to orient the reader, before diving into
our case study on HOAS formatting in \S\ref{sec:showHOAS}.
First, we introduce both the catamorphism (\S\ref{ssec:tourCata0}) and
histomorpism (\S\ref{ssec:tourHist0}) combinators of rank 0 for
regular datatypes.
Second, we provide intuition why Mendler style recursion combinators ensure termination
for positive datatypes.  Third, we move our focus from regular datatypes 
to more expressive datatypes which need rank 1 recursion combinators. These include
nested datatypes (\S\ref{ssec:tourNested}),
indexed datatypes(GADTs) (\S\ref{ssec:tourIndexed}), and
mutually recursive datatypes (\S\ref{ssec:tourMutRec}).
Fourth, we give intuition why the Mendler style catamorphism ensures
termination even for negative datatypes (\S\ref{ssec:tourNegative}).
Finally, we present the case study focusing on HOAS in \S\ref{sec:showHOAS}.


\begin{landscape}
\begin{figure}
\DataFix
\caption{Standard (|Mu|) and inverse augmented (|Rec|) datatype fixpoints
 for kind $*$ and kind $* -> *$}
\label{fig:datafix}
\end{figure}

\begin{figure}
{\small\TypesOfRecursiveCombinators }
\caption{Type signatures of recursive combinators.
         Note the heavy use of higher-rank types.}
\label{fig:rcombty}
\end{figure}

\begin{figure}
{\small \DefsOfRecursiveCombinators }
\caption{Definitions of recursive combinators.
  Note identical textual definitions for the same operators at different ranks,
  but with types specialized for that rank.}
\label{fig:rcombdef}
\end{figure}
\end{landscape}

\begin{figure}
\CataViaHisto
\caption{\normalsize Alternative definition of catamorphism via histomorphism.}
\label{fig:cataviahisto}
\end{figure}

\begin{figure}
\ProofCata
\caption{\normalsize $F_{\omega}$ encoding of |Mu0| and |mcata0| in Haskell}
\label{fig:proof}
\end{figure}

All of our results are summarized in Figures \ref{fig:datafix},
\ref{fig:rcombty}, and \ref{fig:rcombdef}. In Figure \ref{fig:datafix},
we define the Mendler style datatype fixpoint operators (i.e. |Mu0| and |Mu1|).
These are datatype definitions in Haskell that take type constructors
as arguments. They are used to tie the recursive knot
through the generating functor (or base datatype) that they take as an argument.

In Figure \ref{fig:rcombty}, we provide the types of 8 Mendler style
combinators distributed over the two ranks that we consider,
along with the type of a conventional catamorphism for comparison.
The combinators can be organized into a hierarchy of increasing generality, and
juxtaposing the types of the combinators makes it clear where in the hierarchy
each combinator appears, and how each is related to the others.

In Figure \ref{fig:rcombdef}, we define the combinators themselves,
again distributed over two ranks. The definition of the corresponding
combinators in the two ranks are textually identical, although they
must be given different types in each rank.

In Figures \ref{fig:len}, \ref{fig:fib}, and \ref{fig:bsum}, \ref{fig:vec}, and
\ref{fig:mutrec}, we provide examples\footnote{Some of the examples
(Figures \ref{fig:len}, \ref{fig:fib}, and \ref{fig:bsum}) are
adopted from \cite{UusVen00,vene00phd,AbeMatUus03,AbeMatUus05}.}
selected for each of the combinators |mcata0|, |mhist0|, |mcata1|, and |mhist1|.
We discuss the remaining combinators of the inverse augmented fixpoints
in \S\ref{sec:showHOAS}, where we culminate with the HOAS formatting example.
We have structured each of the examples into two, side by side, parts.
On the left, we provide a general recursive encoding, and
on the right, a Mendler style encoding.


%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% %%%%%%% Catamorphism for regular datatypes      %%%%%%% ssec:tourCata0
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%% %include tourCata0.lhs
%% 
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% %%%%%%% Histomorphism for regular datatypes     %%%%%%% ssec:tourHist0
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%% %include tourHist0.lhs
%% 
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% %%%%%%% Nested datatypes                        %%%%%%% ssec:tourNested
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%% %include tourNested.lhs
%% 
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% %%%%%%% Indexed datatypes (GADTs)               %%%%%%% ssec:tourIndexed
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%% %include tourIndexed.lhs
%% 
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% %%%%%%% Mutrually recursive datatypes           %%%%%%% ssec:tourMutRec
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%% %include tourMutRec.lhs
%% 
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% %%%%%%% Negative datatypes, a short look        %%%%%%% ssec:tourNegative
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%% %include tourNegative.lhs

