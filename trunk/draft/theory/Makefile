.PHONY: pdf ps dvi

TEXSRC=main.tex intro.tex fi.tex

pdf: main.pdf

ps: main.ps

dvi: main.dvi

main.pdf: ${TEXSRC} main.bbl
	pdflatex main

main.ps: main.dvi

main.dvi: ${TEXSRC} main.bbl
	latex main

main.aux:
	latex main

main.bbl: main.aux main.bib
	bibtex main
	latex main

