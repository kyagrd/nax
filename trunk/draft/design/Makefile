.PHONY: all pdf ps dvi touch

TEXSRC=main.tex mylhs2tex.sty \
       intro.tex example.tex nax.tex summary.tex

all: pdf

pdf: main.pdf

ps: main.ps

dvi: main.dvi

touch:
	touch main.tex
	touch main.bib
	touch mylhs2tex.lhs

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


mylhs2tex.sty: mylhs2tex.lhs
	lhs2TeX --poly -o $@ $<

example.tex: example.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<


