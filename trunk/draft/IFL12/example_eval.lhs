\subsection{Type preserving evaluator for an expression language}
\afterpage{
\begin{landscape}
\begin{figure}
~~\qquad\qquad\,\textcolor{gray}{\texttt{GADTs},}
\\\vskip-5ex
\hspace*{-6ex}
\begin{minipage}{.31\linewidth}\input{exEvalHs}\end{minipage}
\begin{minipage}{.35\linewidth}\input{exEvalNax}\end{minipage}
\begin{minipage}{.33\linewidth}\input{exEvalAgda}\end{minipage}
\caption{A type preserving evaluator (|eval|) that evaluates
	an expression (|Expr|) to a value (|Val|).}
\label{fig:eval}
\end{figure}
\end{landscape}
} % end afterpage

In this section we will write similar
programs in Nax, Haskell, and Agda.
What we really want to focus on is the use of term indices
to enforce invariants of programs, we hope the use of several host-languages
makes this idea accessbile to a larger audience.
One of our goals is to distinguish the Nax
approach from other approaches, and to illustrate why this approach 
has certain advantages.

In a language that supports term-indices, one writes a type preserving
evaluator as follows: (1) define a datatype Universe which encodes
types of the object language; (2) define a datatype Value (the range of object language evaluation)
indexed by terms of the type Universe; (3) define a datatype ObjectLanguage 
indexed by the same type Universe; and (4) write
the evaluator (from expressions to values) that preserves the term indices
representing the type of the object language. Once the evaluator type checks,
we can be confident that the evaluator is type preserving, relying on
type preservation of the host-language type system.
In Fig.\,\ref{fig:eval}, we provide a concrete example of such
a type preserving evaluator for a very simple expression language (|Expr|).

Our Universe (|Ty|) for the expression language consists of numbers and
booleans, represented by the constants |I| and |B|. We want to evaluate an
expression, to get a value, which may be either numeric (|IV n|) or boolean (|BV b|).
Note that the both the |Expr| and |Val| datatypes are indexed by constant terms (|I| and |B|)
of Universe (|Ty|).

An expression (|Expr|) is either a value (|VAL v|), a numeric addition (|PLUS e1 e2|),
or a conditional (|IF e0 e1 e2|).  Note that the term indices of |Expr| ensure
that expressions are type correct by construction.
For instance, a conditional expression |IF e0 e1 e2| can only be constructed
when |e0| is a boolean expression (\ie, indexed by |B|) and
|e1| and |e2| are expressions of the same type (\ie, both indexed by |t|).

Then, we can write an evaluator (|eval|) (from expressions to values) which
preserves the index that represents the object language type. The definition
of |eval| is fairly straightforward, since our expression language is a very
simple one. What we really want to focus on is the use of term indices
to enforce invariants of programs. 

\subsubsection{Universes, kinds, and well-sortedness}
~\\ \vskip-5ex
In all three languages, the datatype |Val| has the kind annotation |Ty -> *|,
which means that |Val| is a unary type constructor that expects a term of
type |Ty|, rather than a type (c.f., a unary type constructor that expects
a type has kind |* -> *|). Although the textual form of the kind, (|Ty -> *|),
coincides in the three languages, each language has its own
universe structure, kind syntax, and justifications for well-sortedness
(\aka\ kind validity) as illustrated in Table\;\ref{tbl:sorting}.

In a nutshell, the mechanism that allow types at kind level in Nax
is closely related to \emph{universe subtyping} in Agda, and,
the datatype promotion in Haskell is closely related to
\emph{universe polymorphism} in Agda.


Term index types mean that we have to extend how we form both types and kinds.
Several approaches. a typer like (List Int Zero) will not be well formed.
we can lift Zero to a type (Haskell), Extend what is a type and kind (Nax),
unify terms and types and kinds, and use a hierarchy of universes. Nax is
particularly simple.

Haskell Types are promoted (T: * -> *) promoted to (T : box -> box)
limits the promotion of types with term-indexes, unless *::*

Nax, add an additional constructor for kinds, a specail kind of kind-arrow
to Nat => * is a kind. Everything else follows logically from this.

Agda. A hieracrhy of universers allows types and kinds to be prom ....


\begin{table}
\hspace*{-3ex}
\begin{tabular}{ccc}
\textsc{Haskell} \textcolor{gray}{\texttt{+ DataKind}}
&
\textsc{Nax}
&
\textsc{Agda} 
\\
|* : BOX| &
|* : BOX| &
$\star_0 : \star_1 : \star_2 : \star_3 : \cdots$
\\ & &
$\stackrel{\parallel}{|*|}~\,\stackrel{\parallel}{|BOX|}~~\quad\qquad\qquad$
\\
|kappa ::= * || kappa -> kappa | $\mid$
  \textcolor{magenta}{$T\,$}$\overline{\kappa}$
&
|kappa ::= * || kappa -> kappa | $\mid$
   \textcolor{magenta}{$A\,$}|-> kappa|
&
\begin{minipage}{.37\linewidth}\small\centering
term/type/kind/sort syntax are\\ merged into one pseudo-term
\end{minipage}
\\ \\
{ \inference{ \inference{\Jty |Ty : *|}{\Jki |Ty : BOX|} & \Jki |* : BOX| }{
    \Jki |Ty -> * : BOX| }
} & ~~
{ \inference{ \Jty |Ty : *| & \Jki |* : BOX| }{ \Jki |Ty -> * : BOX| }
}
& \qquad
{ \inference{ \!\!\!\!\!\!\!\!\!\!\!\!\!\!\!\!
              \inference{||- |Ty : *| & |* <= BOX|}{||- |Ty : BOX|}
            & ||- |* : BOX| }{
    ||- |Ty -> * : BOX| }
}
\end{tabular} \vskip2ex
\caption{The universe structure, kind syntax, and justifications for
	well-sortedness of the kind |Ty -> *| in three different languages.}
\label{tbl:sorting}
\end{table}

The datatype promotion extension ({\small\texttt{DataKind}}) for Haskell
works as follows:
(1) check if a type constructor |T| is well-kinded
    ($\Jty T : \overline{\star} -> \star$),
(2) promote |T| to the kind level
    (note $T\,\overline{\kappa}\,$ in the kind syntax), and
(3) check well-sortedness of the promoted |T| used in kinds
    ($\Jki T\,\overline{\kappa} : |BOX|$).
In our example, we need not worry about the arguments to the type constructor
since |Ty| is a just a type (\ie, nullary type constructor).
The justification for $\Jki |Ty -> * : BOX|$ in Haskell is illustrated at
the left bottom corner of Table\;\ref{tbl:sorting}.
Note the promotion of |Ty|, from $\Jty |Ty : *|$ to $\Jki |Ty : BOX|$.
We can also view that |Ty| is a polymorphic definition across the type universe,
since |Ty| can be used at type level (|*|) as well as at kind level (|BOX|).

Types can appear in kinds in Nax as well as in Haskell. However, the mechanism
that allows types at kind level in Nax is quite different from the promotion of
type constructors in Haskell. Nax has a simple universe structure (|* : BOX|)
just like Haskell. But, unlike the promotion in Haskell, Nax provides a direct
way of forming arrow from types to kinds (note the |A -> kappa| syntax). There
are two ways of forming arrows at kind level in Nax:\vspace*{-1ex}
\begin{itemize}
\item[(1)] from a kind to another kind
   $\inference{\Jki |kappa1:BOX| & \Jki |kappa2:BOX|}{
        \Jki |kappa1 -> kappa2|}$,
and\vskip1ex
\item[(2)] from a type to a kind
   $\inference{\Jty |A : *| & \Jki |kappa : BOX|}{
        \Jki |A -> kappa|}$.
\end{itemize}
Note that types can only appear in the domain (\ie, left-hand-side of the arrow)
but not the range (\ie, right-hand-side of the arrow).
Modulo right associativity of arrows (\ie, |kappa1 -> kappa2 -> kappa3|
means |kappa1 -> (kappa2 -> kappa3)|), kinds in Nax always end up in |*|
(\eg, |* -> * -> *|, |Nat -> Nat -> *|, |(Nat -> *) -> Nat -> *|).
Note that we do not promote types or type constructors to kind level.
Type constructors must be fully applied to their type level arguments
to form a type of kind |*| before being used at kind level, which is
in opposite order from the promotion of type constructor in Haskell
where we first promote type constructors to kind level and then
apply kind level arguments. The second formation rule (2) could be
understood as a specific use of universe subtyping (|* <= BOX|) hard-wired
with arrow formation. Nax only needs to use universe subtyping in this rule
since the universe structure is simple and there is no full-fledged
dependent types. Agda needs a more general notion of universe subtyping
since Agda is a dependently typed language with stratified universes, which
we will shortly explain.

Agda has stratified type universes. That is, there are countably many stars
$\star_0,\star_1,\dots$ such that $||- \star_n : \star_{1+n}$. When we
from an arrow in Agda, that is, $||- |kappa1 -> kappa2| : \star_n$,
its well-formedness condition is when $||- |kappa1| : \star_n$ and
$||- |kappa2| : \star_n$. However, requiring |kappa1|, |kappa2|, and
|kappa1 -> kappa2| to be in exactly the same universe can cause a lot of
code duplication. For example, if we have $||- |Ty| : \star_0$ and
we want to construct $|Ty| -> \star_0$, we cannot do this since
$||- \star_0:\star_1$. To work around the universe difference, we
would need to duplicate another datatype $||- |Ty'| : \star_1$,
which is isomorphic to |Ty| but at one higher level. Only then,
we can construct $|Ty'| -> \star_0$. Then, if one needs
$|Ty| -> \star_1$, we would need yet another duplicate |Ty''|
at yet another higher level. Universe subtyping provides a remedy
to this duplication problem by allowing objects at lower universe
to be considered as objects at higher universe -- in other words,
it is `promoted' to upper level. This gives us a notion of subtyping
such that $\star_i \leq \star_j$ where $i \leq j$.\footnote{
	This is not the only rule for subtyping in Agda.
 	Another important rule is subtyping between arrows.
	See Ulf Norell's thesis [TODO cite] (\S 1.4) for details.}
With universe subtyping, we can form arrows from |Ty| to any level of universe
(\eg, $|Ty| -> \star_0$, $|Ty| -> \star_1$, $\dots$). Relating back to
the datatype promotion in Haskell, $\star_0$ and $\star_1$ corresponds to |*|
and |BOX| in Haskell. So, we wrote |*| and |BOX| instead of $\star_0$ and
$\star_1$ in the justification of well-formedness of |Ty -> *| in Agda
(at right bottom corner of Table\;\ref{tbl:sorting}) to make the comparison
more apparent. In addition to universe subtyping, Agda also supports
universe polymorphism,\footnote{
\url{http://wiki.portal.chalmers.se/agda/agda.php?n=Main.UniversePolymorphism}}
which can be viewed as a generalization of the datatype promotion in Haskell.
But, we only rely on universe subtyping but not universe polymorphism in
our Agda example codes in Figs.\;\ref{fig:eval}, \ref{fig:glist}, and
\ref{fig:compile}.

\subsubsection{Use of term indices in types:}
TODO


