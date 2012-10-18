.PHONY: all pdf ps dvi touch ListLike

TEXSRC=main.tex mylhs2tex.sty \
       exEvalHs.tex exEvalAgda.tex exEvalNax.tex \
       exCmplHs.tex exCmplAgda.tex exCmplNax.tex \
       exGListHs.tex exGListAgda.tex exGListNax.tex \
       exGListHsEx.tex exGListAgdaEx.tex exGListNaxEx.tex \

UNLIT = /usr/lib/ghc/unlit

##########################################################################
#
# How Haskell, Nax, Agda source files work
#
# Orignal souce files are
#	Eval.lhs   GList.lhs   GListExample.lhs   Compile.lhs  
#	Eval.lnax  GList.lnax  GListExample.lnax  Compile.lnax 
#	Eval.lagda GList.lagda GListExample.lagda Compile.lagda
#
# From Eval.l* files the figure for evaluator is generated via Lhs2TeX.
# From GList*.l* files the figure for glist is generated via Lhs2TeX.
# From GList*.l* files the figure for glist is generated via Lhs2TeX.
#
# To run (or type check) the code you should run "make ListLike"
# in order to generate ListLike.hs, ListLike.nax, and ListLike.agda.
# The "make ListLike" command will automatically generate ListLike.hs,
# ListLike.nax, and ListLike.agda from all the original source files above
# by unliterating and some preprocessing (sed, cat). Since ListLike.* files
# are automatically generated, manually edited versions of ListLike.* must
# not be commited to the repository. You can experiment in your sandbox,
# but save corresponding changes into the original source files and then
# run "make ListLike" to generated updated ListLike.* files automatically.
#
# All.lhs, All.lnax, and All.lagda are manually cut/pasted/modifed from
# the generated ListLike.* files except the content of GListExample.l*.
# All.l* files are just fist phase excercise to experiment formatting
# before I have splitted them into differenet files of Eval, GList,
# Compile, and GListExample. So, I may remove it from the repository
# and also take out from the LaTeX document at some point.
#
##########################################################################


all: pdf

pdf: main.pdf

ps: main.ps

dvi: main.dvi

touch:
	touch main.tex
	touch main.bib
	touch *.lhs
	touch *.lagda
	touch *.lnax


main.pdf: ${TEXSRC} main.bbl
	pdflatex main

main.ps: main.dvi
	dvips main

main.dvi: ${TEXSRC} main.bbl
	latex main

main.aux: main.tex
	latex main

main.bbl: main.aux main.bib
	bibtex main
	latex main


exEvalNax.tex: Eval.lnax includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

exEvalHs.tex: Eval.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

exEvalAgda.tex: Eval.lagda includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<


exCmplNax.tex: Compile.lnax includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

exCmplHs.tex: Compile.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

exCmplAgda.tex: Compile.lagda includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<


exGListNax.tex: GList.lnax includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

exGListHs.tex: GList.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

exGListAgda.tex: GList.lagda includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<


exGListNaxEx.tex: GListExample.lnax includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

exGListHsEx.tex: GListExample.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

exGListAgdaEx.tex: GListExample.lagda includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<




ListLike: ListLike.agda ListLike.nax ListLike.hs

ListLike.agda: Header.agda _Eval.agda _GList.agda _Compile.agda _GListExample.agda
	cat $+ > $@

_Eval.agda: Eval.lagda
	$(UNLIT) $< $@

_GList.agda: GList.lagda
	$(UNLIT) $< $@

_Compile.agda: Compile.lagda
	$(UNLIT) $< $@

_GListExample.agda: GListExample.lagda
	$(UNLIT) $< $@


ListLike.hs: Header.hs _Eval.hs _GList.hs _Compile.hs _GListExample.hs
	cat $+ > $@ && sed -i "s/\.:/':/g" $@

_Eval.hs: Eval.lhs
	$(UNLIT) $< $@

_GList.hs: GList.lhs
	$(UNLIT) $< $@

_Compile.hs: Compile.lhs
	$(UNLIT) $< $@

_GListExample.hs: GListExample.lhs
	$(UNLIT) $< $@


# the generated nax file won't type check since it cannot type check apppend
ListLike.nax: Header.nax _Eval.nax _GList.nax _Compile.nax _GListExample.nax
	cat $+ > $@ && sed -i 's/^{-"\\hs.*"-} //g' $@

_Eval.nax: Eval.lnax
	$(UNLIT) $< $@

_GList.nax: GList.lnax
	$(UNLIT) $< $@

_Compile.nax: Compile.lnax
	$(UNLIT) $< $@

_GListExample.nax: GListExample.lnax
	$(UNLIT) $< $@




