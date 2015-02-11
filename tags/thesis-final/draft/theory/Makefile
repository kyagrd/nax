.PHONY: pdf ps dvi

LHSSRC=main.lhs \
       example.lhs

TEXSRC=main.tex \
       intro.tex nax.tex fi.tex embed.tex related.tex future.tex concl.tex

pdf: main.pdf

ps: main.ps

dvi: main.dvi

main.tex: ${LHSSRC}
	lhs2TeX --poly -v -o main.tex main.lhs

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

