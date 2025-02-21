OTT_OPTS = -tex_show_meta true -tex_wrap false -picky_multiple_parses false -tex_suppress_ntr Q
PDF_ARXIV_DEPENDENCIES = *.sty *.tikzstyles schemas/*
PDF_OTHER_DEPENDENCIES = *.bib *.py flake.nix
MAIN_END_PAGE = 28
APPENDIX_FIRST_PAGE = $(shell echo $$(($(MAIN_END_PAGE) + 1)))

all: destination_calculus.pdf

# Manual steps to submit to Arxiv:
# - the no-editing-mark trick isn't used on Arxiv submission. Make
#   sure that the editing marks are deactivated. Or that there is no
#   mark left in the pdf.
arxiv:
	$(MAKE) clean
	$(MAKE) destination_calculus.tar.gz

destination_calculus.tar.gz: destination_calculus.tex destination_calculus_ott.tex destination_calculus.bbl $(PDF_ARXIV_DEPENDENCIES)
	tar -cvzf $@ $^

arxiv-nix:
	nix develop --command make arxiv

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf
	rm -f ott_coq/destination_calculus_ott.v
	rm -f *.aux *.bbl *.ptb *.toc *.out *.run.xml
	rm -f *.log *.bcf *.fdb_latexmk *.fls *.blg
	rm -f destination_calculus.tex
	rm -f destination_calculus_ott.tex
	rm -f destination_calculus*.pdf
	rm -f destination_calculus.tar.gz
	rm -f no-editing-marks
	rm -f short-version
	rm -f temp.pdf

rules_mod.ott: patch_rules.py rules.ott
	python patch_rules.py rules.ott rules_mod.ott

destination_calculus_ott.tex: grammar.ott rules_mod.ott
	ott $(OTT_OPTS) -o $@ $^

%.tex: %.mng grammar.ott rules_mod.ott
	ott $(OTT_OPTS) -tex_filter $< $@ grammar.ott rules_mod.ott

destination_calculus.pdf destination_calculus.bbl : destination_calculus.tex destination_calculus_ott.tex $(PDF_ARXIV_DEPENDENCIES) $(PDF_OTHER_DEPENDENCIES)
	latexmk destination_calculus.tex

submission:
	$(MAKE) clean
	touch no-editing-marks
	touch short-version
	$(MAKE) destination_calculus-submission.pdf
	rm -f no-editing-marks
	rm -f short-version

# pdftk $< cat 1-$(MAIN_END_PAGE) output temp.pdf
# pdftk $< dump_data_utf8 | pdftk temp.pdf update_info_utf8 - output $@
# rm -f temp.pdf
destination_calculus-submission.pdf: destination_calculus.pdf
	cp destination_calculus.pdf destination_calculus-submission.pdf

destination_calculus-supplementary.pdf: destination_calculus.pdf
	pdftk $< cat $(APPENDIX_FIRST_PAGE)-end output $@

nix::
	nix develop --command make

continuous::
	ls destination_calculus.mng *.ott $(PDF_ARXIV_DEPENDENCIES) $(PDF_OTHER_DEPENDENCIES) Makefile no-editing-marks short-version | entr make

continuous-nix:: nix
	nix develop --command make continuous

ott_coq/destination_calculus_ott.v: grammar.ott rules.ott
	ott $(OTT_OPTS) -o $@ $^
	sed -i 's/: Set/: Type/g' $@

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

coq: Makefile.coq ott_coq/destination_calculus_ott.v
	$(MAKE) TIMED=1 -j -f Makefile.coq

# .SECONDARY:
# the line above prevents deletion of temporary files, which can be helpful for debugging build problems
