.PHONY: all pdf ps dvi

TEXSRC=main.tex mylhs2tex.sty \
       intro.tex example.tex
#       fi.tex data.tex theory.tex relwork.tex concl.tex

all: pdf

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


mylhs2tex.sty: mylhs2tex.lhs
	lhs2TeX --poly -o $@ $<

example.tex: example.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<


