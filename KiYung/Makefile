.PHONY: pdf ps dvi drop

## LHSSRC=main.lhs \
##        example.lhs

TEXSRC=mylhs2tex.sty main.tex \
       intro.tex intro_figoverview.tex \
       poly.tex poly_stlc.tex poly_f.tex poly_fw.tex poly_hm.tex \
       mendler.tex \
       mendler_intro.tex mendler_it.tex mendler_cv.tex mendler_sf.tex \
       mendler_nonreg.tex mendler_nest.tex mendler_gadt.tex mendler_mutrec.tex \
       mendler_proof.tex \
       mendler_prim.tex \
       fi.tex fi_fi.tex fi_theory.tex fi_data.tex \
       fixi_fixi.tex fixi_prim.tex fixi_cvpr.tex fixi_theory.tex \
       nax.tex naxtyinfer.tex casestd.tex \
       relwork.tex relwork_mcoit.tex relwork_mmult.tex \
       futwork.tex futwork_mprsi.tex futwork_mu.tex \
       concl.tex \
       appendix.tex

pdf: main.pdf

ps: main.ps

dvi: main.dvi

drop: main.pdf
	cp $< ~/Dropbox/Public/thesis/Nax_KiYungAhn_thesis_singlespace.pdf

## main.tex: ${LHSSRC}
## 	lhs2TeX --poly -v -o main.tex main.lhs

main.pdf: main.bbl ${TEXSRC}
	makeindex main
	pdflatex main

main.ps: main.dvi
	dvips main

main.dvi: main.bbl ${TEXSRC}
	makeindex main
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
	mendler/HOASshow.lhs mendler/Graph.lhs \
	mendler/HOASeval.lhs mendler/Proof2.lhs
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

####	nax_tyinfer.lhs
nax.tex: nax.lhs IFL12code/includelhs2tex.lhs \
	nax_features.lhs \
	nax_intro.lhs nax_examples.lhs nax_discuss.lhs \
	IFL12code/Eval.lhs IFL12code/Eval.lnax IFL12code/Eval.lagda \
	IFL12code/GList.lhs IFL12code/GListExample.lhs \
       	IFL12code/GList.lnax IFL12code/GListExample.lnax \
	IFL12code/GListExample.lagda IFL12code/GList.lagda \
	IFL12code/Compile.lhs IFL12code/Compile.lnax IFL12code/Compile.lagda \
	IFL12code/Env.lnax IFL12code/Env.lagda
	lhs2TeX --poly -o $@ $<

relwork_mcoit.tex: relwork_mcoit.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

relwork_mmult.tex: relwork_mmult.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

futwork_mprsi.tex: futwork_mprsi.lhs includelhs2tex.lhs mendler/HOASevalV.lhs
	lhs2TeX --poly -o $@ $<

futwork_mu.tex: futwork_mu.lhs includelhs2tex.lhs
	lhs2TeX --poly -o $@ $<

