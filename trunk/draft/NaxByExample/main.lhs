%\documentclass[preliminary,copyright,creativecommons]{eptcs}
%\documentclass[submission,copyright,creativecommons]{eptcs}
\documentclass[adraft,copyright,creativecommons]{eptcs}
\providecommand{\event}{FICS or MSFP 2012} % Name of the event to submit
\usepackage{breakurl}              % Not needed if you use pdflatex only.
\usepackage{amssymb}
\usepackage[fleqn]{amsmath}
\usepackage{amsthm}
\usepackage{semantic}
\usepackage{color}
\usepackage{fancybox}
\usepackage{framed}
\usepackage{comment}

\definecolor{grey}{rgb}{0.8,0.8,0.8}

%include lhs2TeX.fmt
%include greek.fmt
%% %include forall.fmt

%format kappa1
%format kappa2
%format kappa3

%format forall = "\forall"
%format synonym = "\mathbf{synonym}"
%format with = "\mathbin{\mathbf{with}}"
%format where = "\;\mathbf{where}"
%format fixpoint = "\,\mathbf{fixpoint}"
%format Mu (k) = "\mu^{" k "}"
%format In (k) = "\In^{" k "}"
%format MIt (a) = "\mathsf{MIt}^{" a "}"
%format MPr (a) = "\mathsf{MPr}^{" a "}"
%format MsfIt (a) = "\mathsf{MsfIt}^{" a "}"
%format McvIt (a) = "\mathsf{McvIt}^{" a "}"
%format . = "\mathbin{.}\,"

%format phi = "\varphi"

%%%% workaround since lhs2TeX does not allow redefining formats for keywords

%format casei (a) = "\mathbf{case}^{" a "}"

%format (NEWFI (x)) = "{\newFi{" x "}\;}"

\title{Nax theory}

\author{Ki Yung Ahn \qquad Tim Sheard
\institute{Portland State University\thanks{This paper is based upon work supported by the National Science Foundation under Grant No. 0613969.}\\
           Portland, Oergon, USA}
\email{kya@@cs.pdx.edu \qquad sheard@@cs.pdx.edu}
\and
Marcelo P. Fiore \quad\qquad Andrew M. Pitts
\institute{University of Cambridge\thanks{Another thanks here if needed}\\
           Cambridge, UK}
\email{\{Marcelo.Fiore,Andrew.Pitts\}@@cl.cam.ac.uk}
}
\def\titlerunning{title running}
\def\authorrunning{KY. Ahn, T. Sheard \& M. P. Fiore, A. M. Pitts}

%%%%% commands for comments
\newcommand{\KYA}[1]{\textcolor{magenta}{#1 --KYA}}

\theoremstyle{plain}
\newtheorem{proposition}{Proposition}
\newtheorem*{proposition*}{Proposition}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}
\newtheorem{corollary}{Corollary}

\theoremstyle{remark}
\newtheorem{remark}{Remark}

\theoremstyle{definition}
\newtheorem{definition}{Definition}


\newcommand{\Fig}[1]{Figure\,\ref{fig:#1}}
\newcommand{\newFi}[1]{\colorbox{grey}{\ensuremath{#1}}}

\newcommand{\eg}{{e.g.}}
\newcommand{\ie}{{i.e.}}

\newcommand{\Fi}{\ensuremath{\mathsf{F}_i}}
\newcommand{\Fw}{\ensuremath{\mathsf{F}_\omega}}
\newcommand{\fix}{\mathsf{fix}}
\newcommand{\Fix}{\mathsf{Fix}}
\newcommand{\Fixw}{\ensuremath{\Fix_{\omega}}}
\newcommand{\Fixi}{\ensuremath{\Fix_{i}}}

\newcommand{\Nat}{\ensuremath{\mathsf{Nat}}}
\newcommand{\Bool}{\ensuremath{\mathsf{Bool}}}
\newcommand{\sfList}{\ensuremath{\mathsf{List}}}
\newcommand{\sfVec}{\ensuremath{\mathsf{Vec}}}
\newcommand{\SAT}{\ensuremath{\mathsf{SAT}}}

\newcommand{\oz}{\oldstylenums{0}}
\newcommand{\ka}{{\check\kappa}}

\newcommand{\calS}{\mathcal{S}}
\newcommand{\calA}{\mathcal{A}}
\newcommand{\calR}{\mathcal{R}}
\newcommand{\dom}{\mathop{\mathsf{dom}}}
\newcommand{\FV}{\mathop{\mathrm{FV}}}
\newcommand{\In}{\mathsf{In}}

\newcommand{\defeq}{\stackrel{\mathrm{def}}{=}}
\newcommand{\tyinf}{\mathrel{\triangleright}}

%%%%% semantic package commands
\reservestyle[\mathinner]{\command}{\mathsf}
\command{MIt[MIt\;]}
\reservestyle[\mathinner]{\cmd}{\mathbf}
\cmd{let[let\;],in[\;in\;],data[data~],where[~where~]}


\begin{document}
\maketitle

\begin{abstract}
This is a sentence in the abstract.
This is another sentence in the abstract.
This is yet another sentence in the abstract.
This is the final sentence in the abstract.
\end{abstract}

\input{intro}

%include example.lhs

%%\input{nax}

%% \section{TODO}
%% let's write a paper for maybe one of the following venues?
%% \begin{itemize}
%% \item FICS \url{http://www.inf.u-szeged.hu/fics2012/}\\
%% Abstract submission:         4 Dec 2011\\
%% Paper submission:    11 Dec 2011\\
%% 8 pages using eptcs style
%% \item MSFP \url{http://cs.ioc.ee/msfp/msfp2012/}\\
%% Submission of papers 16 December\\
%% There is no specific page limit but authors should strive for brevity.
%% \end{itemize}

~\\~\\
\cite{article,bookA} just dummy citation %% \nocite{*}
\bibliographystyle{eptcs}
\bibliography{main}

\end{document}
