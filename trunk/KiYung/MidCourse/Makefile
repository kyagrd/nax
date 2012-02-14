.PHONY: pdf ps dvi clean

pdf: main.pdf

ps: main.ps

dvi: main.dvi

INCSRC = intro.tex relwork.tex mendler.tex fi.tex nax.tex ext.tex summary.tex

main.pdf: main.tex main.aux main.bbl $(INCSRC)
	pdflatex main

main.ps: main.dvi
	dvips -o $@ $<

main.dvi: main.tex main.aux main.bbl $(INCSRC)
	latex main

main.aux:
	latex main 

main.bbl: main.aux main.bib
	bibtex main
	pdflatex main

