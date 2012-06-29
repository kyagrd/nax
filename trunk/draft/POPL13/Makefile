.PHONY: all pdf ps dvi

LHSSRC=main.lhs \
       example.lhs

TEXSRC=main.tex \
       intro.tex fi.tex theory.tex relwork.tex concl.tex

all: pdf Abstract.pdf

pdf: main.pdf

ps: main.ps

dvi: main.dvi

# main.tex: ${LHSSRC}
# 	lhs2TeX --poly -v -o main.tex main.lhs

main.pdf: ${TEXSRC} main.bbl
	pdflatex main

main.ps: main.dvi
	dvips main

main.dvi: ${TEXSRC} main.bbl
	latex main

main.aux:
	latex main

main.bbl: main.aux main.bib
	bibtex main
	latex main

Abstract.pdf: Abstract.tex Abstract.bbl
	pdflatex Abstract

Abstract.bbl: Abstract.aux main.bib
	bibtex Abstract 
	latex Abstract


