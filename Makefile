OTT_FILES = grammar.ott rules.ott
OTT_FILES_MOD = grammar.ott rules_mod.ott
OTT_OPTS = -tex_show_meta true -tex_wrap false -picky_multiple_parses false -tex_suppress_ntr Q
OTT_TEX = destination_calculus_ott.tex
OTT_COQ = ott_coq/destination_calculus_ott.v

all: destination_calculus.pdf

# Manual steps to submit to Arxiv:
# - the no-editing-mark trick isn't used on Arxiv submission. Make
#   sure that the editing marks are deactivated. Or that there is no
#   mark left in the pdf.
arxiv:
	$(MAKE) clean
	$(MAKE) destination_calculus.tar.gz

arxiv-nix:
	nix-shell --pure --run "make arxiv"

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf
	rm -f ott_coq/destination_calculus_ott.v
	rm -f *.aux *.bbl *.ptb *.pdf *.toc *.out *.run.xml
	rm -f *.log *.bcf *.fdb_latexmk *.fls *.blg
	rm -f destination_calculus.pdf
	rm -f destination_calculus.lhs
	rm -f destination_calculus.tex
	rm -f destination_calculus.*.gz
	rm -f destination_calculus_ott.tex

rules_mod.ott : rules.ott
	python patch_rules.py rules.ott rules_mod.ott

%.tex: %.mng $(OTT_FILES_MOD)
	ott $(OTT_OPTS) -tex_filter $< $@ $(OTT_FILES_MOD)

$(OTT_TEX): $(OTT_FILES_MOD)
	ott $(OTT_OPTS) -o $@ $^

$(OTT_COQ): $(OTT_FILES)
	ott $(OTT_OPTS) -o $@ $^
	sed -i 's/: Set/: Type/g' $@

# %.tex: %.lhs
# 	lhs2TeX -o $@ $<

destination_calculus.tar.gz: destination_calculus.tex destination_calculus.bbl destination_calculus_ott.tex ottstyling.sty listproc.sty ottalt.sty
	tar -cvzf $@ $^

%.pdf %.bbl : %.tex bibliography.bib ottstyling.sty $(OTT_TEX)
	cd $(dir $<) && latexmk $(notdir $*)

nix::
	nix-shell --pure --run make

continous-nix:: nix
	nix-shell --pure --run "ls destination_calculus.mng bibliography.bib $(OTT_FILES) ottstyling.sty | entr make"

coq: Makefile.coq $(OTT_COQ)
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

# .SECONDARY:
# the line above prevents deletion of temporary files, which can be helpful for debugging build problems