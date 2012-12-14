.PHONY: pdf ps dvi

## LHSSRC=main.lhs \
##        example.lhs

TEXSRC=mylhs2tex.sty main.tex \
       intro.tex \
       poly.tex poly_stlc.tex poly_f.tex poly_fw.tex poly_hm.tex \
       mendler.tex \
       mendler_intro.tex mendler_it.tex mendler_cv.tex mendler_sf.tex \
       mendler_nonreg.tex mendler_nest.tex mendler_gadt.tex mendler_mutrec.tex \
       mendler_proof.tex \
       mendler_prim.tex \
       fi.tex fi_fi.tex fi_theory.tex fi_data.tex \
       fixi.tex nax.tex casestd.tex \
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

mendler_intro.tex: mendler_intro.lhs includelhs2tex.lhs \
	mendler/RecComb.lhs mendler/CataViaHisto.lhs mendler/Proof.lhs
	lhs2TeX --poly -o $@ $<

mendler_it.tex: mendler_it.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

mendler_cv.tex: mendler_cv.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

mendler_sf.tex: mendler_sf.lhs includelhs2tex.lhs \
	mendler/HOASshow.lhs mendler/Graph.lhs
	lhs2TeX --poly -o $@ $<

mendler_nonreg.tex: mendler_nonreg.lhs includelhs2tex.lhs \
	mendler_nest.lhs mendler_gadt.lhs mendler_mutrec.lhs
	lhs2TeX --poly -o $@ $<

mendler_nest.tex: mendler_nest.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

mendler_gadt.tex: mendler_gadt.lhs includelhs2tex.lhs \
	mendler/Vec.lhs  mendler/VecG.lhs
	lhs2TeX --poly -o $@ $<

mendler_mutrec.tex: mendler_mutrec.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

mendler_proof.tex: mendler_proof.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

mendler_prim.tex: mendler_prim.lhs includelhs2tex.lhs \
	mendler/Fac.lhs mendler/FacG.lhs
	lhs2TeX --poly -o $@ $<

nax.tex: nax.lhs nax_examples.lhs nax_discuss.lhs IFL12code/includelhs2tex.lhs \
	IFL12code/Eval.lhs IFL12code/Eval.lnax IFL12code/Eval.lagda \
	IFL12code/GList.lhs IFL12code/GListExample.lhs \
       	IFL12code/GList.lnax IFL12code/GListExample.lnax \
	IFL12code/GListExample.lagda IFL12code/GList.lagda \
	IFL12code/Compile.lhs IFL12code/Compile.lnax IFL12code/Compile.lagda \
	IFL12code/Env.lnax IFL12code/Env.lagda
	lhs2TeX --poly -o $@ $<

