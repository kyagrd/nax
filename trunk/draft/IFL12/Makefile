.PHONY: all pdf ps dvi touch

TEXSRC=main.tex \
       exEvalHs.tex exEvalAgda.tex exEvalNax.tex \
       exCmplHs.tex exCmplAgda.tex exCmplNax.tex \
       exGListHs.tex exGListAgda.tex exGListNax.tex \
       exGListHsEx.tex exGListAgdaEx.tex exGListNaxEx.tex \
       exHaskell.tex exAgda.tex exNax.tex

all: pdf

pdf: main.pdf

ps: main.ps

dvi: main.dvi

touch:
	touch main.tex
	touch main.bib
	touch *.lhs

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

mylhs2tex.sty: mylhs2tex.lhs
	lhs2TeX --poly -o $@ $<

exNax.tex: CompileExpr2Code.lnax includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

exHaskell.tex: CompileExpr2Code.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

exAgda.tex: CompileExpr2Code.lagda includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<



exEvalNax.tex: Expr2Val.lnax includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

exEvalHs.tex: Expr2Val.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

exEvalAgda.tex: Expr2Val.lagda includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<


exCmplNax.tex: Expr2Code.lnax includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

exCmplHs.tex: Expr2Code.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

exCmplAgda.tex: Expr2Code.lagda includelhs2tex.lhs
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

