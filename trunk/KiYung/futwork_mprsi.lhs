%include includelhs2tex.lhs

\section[Another Mendler-style recursion scheme for mixed-variant datatypes]{
	 Another Mendler-style recursion scheme for mixed-variant datatypes
	\footnotemark{} }
\footnotetext{
	This section is an extended and revised version of our extended abstract
	(without the introduction section) in the TYPES 2013 workshop.}
\label{sec:futwork:mprsi}


In \S\ref{sec:msf}, we discussed Mendler-style iteration with
a syntactic inverse, |msfcata|, which is particularly useful for
defining functions over negative (or mixed-variant) datatypes.
We demonstrated the usefulness of |msfcata| by defining functions over HOAS:
\index{datatype!negative}
\index{datatype!mixed-variant}
\begin{itemize}
\item the string formatting function |showHOAS| for the untyped HOAS using |msfcata0|
(Figure \ref{fig:HOASshow} on p.\pageref{fig:HOASshow}) and
\item the type-preserving evaluator |evalHOAS| for the simply-typed HOAS
using |msfcata1| (Figure \ref{fig:HOASeval} on p.\pageref{fig:HOASeval}).
\end{itemize}
In this section, we speculate about another Mendler-style recursion scheme,
|mprsi|, motivated by an example similar to the |evalHOAS| function.
The name |mprsi| stands for
Mendler-style primitive recursion with a sized index.
\index{Mendler-style!primitive recursion with a sized index}

%format t1
%format t2
%format e1
%format e2
\begin{figure}
\begin{singlespace}\small
%include mendler/HOASevalV.lhs
\end{singlespace}
\caption{Two evaluators for the simply-typed $\lambda$-calculus in HOAS.
         One uses a native (Haskell) value domain (|evalHOAS|), the
         other uses a user-defined value domain (|vevalHOAS|).}
\label{fig:HOASevalV}
\end{figure}

We review the |evalHOAS| example and then compare
it to our motivating example |vevalHOAS| for |mprsi|. Both |evalHOAS|
and |vevalHOAS| are illustrated in Figure\;\ref{fig:HOASevalV}. Recall
that this code is written in Haskell, following the Mendler-style conventions.
The function |evalHOAS :: Exp t -> Id t| is a type-preserving evaluator
that evaluates an HOAS expression of type |t| to a (Haskell)
value of type |t|. The |evalHOAS| function always terminates because
|msfcata1| always terminates. Recall that |msfcata1| and |Rec1|
can be embedded into System \Fw\ (or System \Fi, if we need term indices).

The motivating example |vevalHOAS :: Exp t -> Val t| is also 
a type-preserving evaluator. Unlike |evalHOAS|, it evaluates to 
a user-defined value domain |Val| of type |t| (rather than a Haskell value).
The definition of |vevalHOAS| is similar to |evalHOAS|; both of them are
defined using |msfcata1|. The first equation of |phi| for evaluating
the |Lam|-expression is essentially
the same as the corresponding equation in the definition of |evalHOAS|.
The second equation of |phi| for evaluating the |App|-expression is also similar
in structure to the corresponding equation in the definition of |evalHOAS|.
However, the use of |unVal| is problematic. In particular, the definition of
|unVal| relies on pattern matching against |In1|. Recall that one cannot
freely pattern match against a recursive value in Mendler style.
Recursive values must be analyzed (or eliminated) by using Mendler-style
recursion schemes. It is not a problem to use |unId| in the definition of
|evalHOAS| because |Id| is non-recursive.

It is not likely that |unVal| can be defined using any of the existing
Mendler-style recursion schemes discussed earlier.
So, we designed a new Mendler-style recursion scheme that can express |unVal|.
The new recursion scheme |mprsi| extends |mprim| with an additional
uncast operation. Recall that |mprim| has two abstract operations,
call and cast. So, |mprsi| has three abstract operations,
call, cast, and uncast. In the following paragraphs,
we explain the design of |mprsi| step-by-step.

Let us try to define |unVal| using |mprim1| and examine where it falls short.
|mprim1| provides two abstract operations, |cast| and |call|, as it can be
seen from the type signature below:
\begin{singlespace}
\begin{code}
mprim1 :: (forall r i.  (forall i. r i -> Mu1 f i)  -- cast
                    ->  (forall i. r i -> a i)      -- call
                    ->  (f r i -> a i)              ) -> Mu f i -> a i
\end{code}
\end{singlespace}
\noindent
We attempt to define |unVal| using |mprim1| as follows:\vspace{.5em}
\begin{singlespace}
\begin{code}
unVal :: Mu1 V (t1 -> t2) -> (Mu1 V t1 -> Mu1 V t2)
unVal = mprim1 phi where
  phi cast call (VFun f) = ...
\end{code}
\end{singlespace}
\noindent
Inside the |phi| function, we have a function |f :: (r t1 -> r t2)| over
abstract recursive values. We need to cast |f| into a function over
concrete recursive values |(Mu V t1 -> Mu V t2)|.
We should not need to use |call|, since we do not expect
to use any recursion to define |unVal|.
So, the only available operation is |cast :: (forall i. r i -> Mu f i)|.
Composing |cast| with |f|, we can get |(cast . f) :: (r t1 -> Mu V t2)|,
whose codomain (|Mu V t2|) is exactly what we want. But, the domain
is still abstract |(r t1)| rather than being concrete |(Mu V t1)|.
We are stuck.

\index{abstract operation!cast}
\index{abstract operation!uncast}
What additional abstract operation would help us complete the definition of
|unVal|? We need an abstract operation to cast from |(r t1)| to |(Mu V t1)|
in a contravariant position.
If we had an inverse of cast, |uncast :: (forall i. Mu f i -> r i)|, we could
complete the definition of |unVal| by composing |uncast|, |f|, and |cast|.
That is, |(uncast . f . cast) :: (Mu1 V t1 -> Mu1 V t2)|. Thus, we can
formulate |mprsi1| with a naive type signature as follows:
\begin{singlespace}
\begin{code}
mprsi1 :: (forall r  i.  (forall i. r i -> Mu1 f i)  -- cast
                     ->  (forall i. Mu1 f i -> r i)  -- uncast
                     ->  (forall i. r i -> a i)      -- call
                     ->  (f r i -> a i)              ) -> Mu f i -> a i

mprsi1 phi (In1 x) = phi id id (mprsi1 phi) x
\end{code}
\end{singlespace}
\indent
Although the type signature above is type-correct, it is too powerful.
The Mendler-style approach uses types to forbid, as ill-typed,
non-terminating computations. Having both |cast| and |uncast| supports
the same ability as freely pattern matching over recursive values,
which can lead to non-termination. To recover the guarantee of termination,
we need to restrict the use of either |cast| or |uncast|, or both.

Let us see how this non-termination might occur. If we allowed |mprsi1| with
the naive type signature above, we would be able to write an evaluator
(similar to |vevalHOAS| but for an untyped HOAS) that does not always terminate.
This evaluator would diverge for terms with self application. Here,
we walk through the process of defining an untyped HOAS with a dummy index.
The base structures for the untyped HOAS and its value domain can be defined
as follows:
%format ExpF_u = ExpF"_u"
%format Lam_u = Lam"_u"
%format App_u = App"_u"
%format V_u = V"_u"
%format VFun_u = VFun"_u"
\begin{code}
data ExpF_u r t = Lam_u (r t -> r t) | App_u (r t) (r t)

data V_u r t = VFun_u (r t -> r t)
\end{code}
Fixpoints of the structures above represent the untyped HOAS and
its value domain. 
Here, the index |t| is bogus; that is, it does not track the type of
an HOAS expression but remains constant everywhere. Using the naive version
of |mprsi1| above, we can write an evaluator similar to |vevalHOAS| for
the untyped HOAS (|Mu1 ExpF_u ()|) via the value domain (|Mu1 V_u  ()|),
which would obviously not terminate for some input.

Why did we believe that |vevalHOAS| always terminates?
Because it evaluates a well-typed HOAS, whose type is encoded as
an index |t| in the recursive datatype |(Exp t)|. That is,
the use of indices as types is the key to the termination property.
Therefore, our idea is to restrict the use of the abstract operations
in |mprsi1| by enforcing constraints over their indices; in that way,
we would still be able write |vevalHOAS| for the typed HOAS,
but would get a type error when we try to write an evaluator for
the untyped HOAS.

We suggest that some of the abstract operations of |mprsi1| should only be
applied to the abstract values whose indices are smaller in size compared to
the size of the argument index. For the |vevalHOAS| example, we define
being smaller as the structural ordering over types, that is,
|t1 < (t1 -> t2)| and |t2 < (t2 -> t1)|. We have two candidates for
the type signature of |mprsi1|:\vspace{-2em}\newpage
\begin{singlespace}
\begin{itemize}
\item Candidate 1: restrict uses of both |cast| and |uncast|
\begin{code}
mprsi1 :: (forall r  j.  (forall i. (i<j) =>  r i -> Mu1 f i)  --  cast
                     ->  (forall i. (i<j) =>  Mu1 f i -> r i)  --  uncast
                     ->  (forall i.           r i -> a i)      --  call
                     ->  (f r j -> a j)                        ) -> Mu f i -> a i
\end{code}
\item Candidate 2: restrict the use of |uncast| only
\begin{code}
mprsi1 :: (forall r  j.  (forall i.           r i -> Mu1 f i)  --  cast
                     ->  (forall i. (i<j) =>  Mu1 f i -> r i)  --  uncast
                     ->  (forall i.           r i -> a i)      --  call
                     ->  (f r j -> a j)                        ) -> Mu f i -> a i
\end{code}
\end{itemize}
\end{singlespace}\noindent
We strongly believe that the first candidate always terminates,
but it might be overly restrictive. Maybe the second candidate is
enough to guarantee termination? Both candidates allow defining |vevalHOAS|,
because one can define |unVal| using |mprsi1| with either one of
the candidates, but both forbid the evaluator over the untyped HOAS, because
neither supports extracting functions from the untyped value domain.

We need further studies to prove the termination properties of |mprsi|.
The sized-type approach, discussed in \S\ref{sec:relwork:sized},
seems to be relevant for showing the termination of |mprsi|. However,
existing theories on sized-types are not directly applicable to |mprsi|
because they are focused on positive datatypes, but not negative datatypes.

%% |Exp| and |Val| in this section are chosen to be minimal for simplicity,
%% kbut it does not well motivate why one might need a user-defined value domain.
%% kThe normalization by evaluation based on HOAS in Appendix \ref{app:nbeHOAS}
%% kgives a clear motivation why one would need a user-defined value domain.

