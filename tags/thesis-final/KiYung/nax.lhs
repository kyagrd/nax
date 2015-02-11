%include lhs2TeX.fmt
%include greek.fmt
%include forall.fmt
%include agda.fmt
%include IFL12code/includelhs2tex.lhs

\newcommand{\Jtag}[1]{\mathop{\vdash_{\!\!\mathsf{#1}}}}
\newcommand{\Jty}[0]{\Jtag{ty}}
\newcommand{\Jki}[0]{\Jtag{k}}

%% chapter
%include nax_features.lhs

\chapter{Design Principles of Nax's Type System}\label{ch:nax}
%include nax_intro.lhs
%include nax_examples.lhs
%include nax_discuss.lhs

%% chapter
%%% %include nax_tyinfer.lhs

\input{naxtyinfer}
