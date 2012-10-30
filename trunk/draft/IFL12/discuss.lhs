%include lhs2TeX.fmt
%include includelhs2tex.lhs

\section{TODO discussion}

\subsection{deeply indexed datatypes and datatypes containing types}
Examples in Sect.\;\ref{sec:example} consisted of rather simple
indexed datatypes, where the terms indices are of datatypes
without any term indices (\eg, |Unit|, |Nat|, |Bool|).
One can imagine more complex indexed datatypes, where some term indices
are themselves of indexed datatypes. Such deeply indexed datatypes are
often useful in dependently typed programming. For instance, \citet{BraHam10}
defines a datatype for environments that contain stateful resources in order
to implement their embedded domain specific language (EDSL) for verified
resource usage protocols. Figure \label{fig:env} is a transcription of
their environment datatype (|Env|) in Idris into Agda an Nax.  Note that
the datatype |Env| is indexed by a term of a length indexed list datatype,
which is again indexed by a natural number term. There is no Haskell
transcription because promotion of datatypes \cite{YorgeyWCJVM12} is
limited to datatypes without any term indices. That is, Nax supports
deeply nested datatypes while Haskell's datatype promotion does not.

\begin{figure}
%include Env.lagda
~\\
%include Env.lnax
\caption{Environments of stateful resources
	indexed by the length indexed list of states}
\label{fig:env}
\end{figure}

On the contrary, Haskell supports datatypes that hold types,
although limited to elements of non-indexed types, but Nax does not.
Heterogeneous lists indexed by the list of element types in Figure 3
is well-known example of 

\begin{figure}
\begin{code}
data List a = Nil | a :. List a{-"~"-};{-"~"-}infixr :.

data HList :: List {-"\;"-} * -> * where
  HNil  :: HList Nil
  HCons :: t -> HList ts -> HList (t :. ts)

hlist :: HList (Int :. Bool :. List Int :.  Nil)
hlist = HCons 3 (HCons True (HCons (1 :. 2 :. Nil) HNil))
\end{code}
\caption{Heterogeneous lists (|HList|) indexed by
	 the list of element types (|List{-"\;"-}*|).}
\label{fig:hlist}
\end{figure}
