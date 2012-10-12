.PHONY: all pdf ps dvi touch

TEXSRC=main.tex

all: pdf

pdf: main.pdf

ps: main.ps

dvi: main.dvi

touch:
	touch main.tex
	touch main.bib

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

