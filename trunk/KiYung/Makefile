.PHONY: pdf ps dvi

## LHSSRC=main.lhs \
##        example.lhs

TEXSRC=mylhs2tex.sty main.tex \
       intro.tex \
       poly.tex poly_stlc.tex poly_f.tex poly_fw.tex poly_hm.tex \
       mendler.tex \
       fi.tex fixi.tex nax.tex casestd.tex \
       relwork.tex futwork.tex concl.tex

pdf: main.pdf

ps: main.ps

dvi: main.dvi

## main.tex: ${LHSSRC}
## 	lhs2TeX --poly -v -o main.tex main.lhs

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





############ style file for using multiple lhs files

mylhs2tex.sty: mylhs2tex.lhs
	lhs2TeX --poly -o $@ $<
