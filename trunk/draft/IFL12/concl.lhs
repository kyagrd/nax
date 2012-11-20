%include lhs2TeX.fmt
%include includelhs2tex.lhs

\section{Summary and Future Work}
In Nax, programmers can enforce program invariants using indexed types,
without excessive annotations (like functional programming languages)
while enjoying logical consistency (like dependently typed proof assistants).

There are two approaches that allow term-indices without code duplication at
every universe. \emph{Universe subtyping} is independent of the number of
universes. Even scaled down to two universes (|*, BOX|), it adds no additional
restrictions -- term indices can appear at arbitrary depth.
\emph{Universe polymorphism} is sensitive to the number of universes.
Unless you have countably infinite universes, nested term indices are
restricted to depth $n-1$ where $n$ is the number of universes.

On the other hand, universe polymorphism can reuse datatypes at term level
(|List a| where |a: *|) at type-level to contain type elements
(\eg, |List| |*|), which is beyond universe subtyping. We envision that
Nax extended with first-class datatype descriptions \cite{DagMcb12} would
be able express the same concept reflected at term level, so that we would
have no need for type level datatypes.

