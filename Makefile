OTT_FILES = grammar.ott rules.ott
OTT_OPTS = -tex_show_meta false -tex_wrap false -picky_multiple_parses false -tex_suppress_ntr Q
OTT_TEX = destination-calculus-ott.tex
OTT_COQ = destination-calculus-ott.v

all: destination-calculus.pdf

# Manual steps to submit to Arxiv:
# - the no-editing-mark trick isn't used on Arxiv submission. Make
#   sure that the editing marks are deactivated. Or that there is no
#   mark left in the pdf.
arxiv:
	$(MAKE) clean
	$(MAKE) destination-calculus.tar.gz

arxiv-nix:
	nix-shell --pure --run "make arxiv"

clean:
	rm -f *.aux *.bbl *.ptb *.pdf *.toc *.out *.run.xml
	rm -f *.log *.bcf *.fdb_latexmk *.fls *.blg
	rm -f destination-calculus.pdf
	rm -f destination-calculus.lhs
	rm -f destination-calculus.tex
	rm -f destination-calculus.*.gz
	rm -f destination-calculus-ott.tex

%.tex: %.mng $(OTT_FILES)
	ott $(OTT_OPTS) -tex_filter $< $@ $(OTT_FILES)

$(OTT_TEX): $(OTT_FILES)
	ott $(OTT_OPTS) -o $@ $^

$(OTT_COQ): $(OTT_FILES)
	ott $(OTT_OPTS) -o $@ $^

# %.tex: %.lhs
# 	lhs2TeX -o $@ $<

destination-calculus.tar.gz: destination-calculus.tex destination-calculus.bbl destination-calculus-ott.tex ottstyling.sty listproc.sty ottalt.sty
	tar -cvzf $@ $^

%.pdf %.bbl : %.tex bibliography.bib $(OTT_TEX)
	cd $(dir $<) && latexmk $(notdir $*)

nix::
	nix-shell --pure --run make

continous-nix:: nix
	nix-shell --pure --run "ls destination-calculus.mng bibliography.bib $(OTT_FILES) ottstyling.sty | entr make"

# .SECONDARY:
# the line above prevents deletion of temporary files, which can be helpful for debugging build problems