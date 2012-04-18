.PHONY: pdf ps dvi

## LHSSRC=main.lhs \
##        example.lhs

TEXSRC=mylhs2tex.sty main.tex \
       intro.tex \
       poly.tex poly_stlc.tex poly_f.tex poly_fw.tex poly_hm.tex \
       mendler.tex \
       mendler_intro.tex mendler_it.tex mendler_cv.tex mendler_sf.tex \
       mendler_nest.tex mendler_gadt.tex mendler_mutrec.tex mendler_proof.tex \
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

mendler_intro.tex: mendler_intro.lhs
	lhs2TeX --poly -o $@ $<

mendler_it.tex: mendler_it.lhs
	lhs2TeX --poly -o $@ $<

mendler_cv.tex: mendler_cv.lhs
	lhs2TeX --poly -o $@ $<

mendler_sf.tex: mendler_sf.lhs
	lhs2TeX --poly -o $@ $<

mendler_nest.tex: mendler_nest.lhs
	lhs2TeX --poly -o $@ $<

mendler_gadt.tex: mendler_gadt.lhs
	lhs2TeX --poly -o $@ $<

mendler_mutrec.tex: mendler_mutrec.lhs
	lhs2TeX --poly -o $@ $<

mendler_proof.tex: mendler_proof.lhs
	lhs2TeX --poly -o $@ $<

