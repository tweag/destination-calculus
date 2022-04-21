##
## Makefile for the document, based on:
##
## https://tex.stackexchange.com/questions/40738/how-to-properly-make-a-latex-project
##

# Document name
DOCNAME=phd-research

PDFLATEX="pdflatex -interaction=nonstopmode -synctex=1"

# You want latexmk to *always* run, because make does not have all the info.
# Also, include non-file targets in .PHONY so they are run regardless of any
# file of the given name existing.
.PHONY: $(DOCNAME).pdf all clean

# The first rule in a Makefile is the one executed by default ("make"). It
# should always be the "all" rule, so that "make" and "make all" are identical.
all: $(DOCNAME).pdf

##
## CUSTOM BUILD RULES
##

##
## MAIN LATEXMK RULE
##

# -pdf tells latexmk to generate PDF directly (instead of DVI).

# -pdflatex="" tells latexmk to call a specific backend with specific options.

# -use-make tells latexmk to call make for generating missing files.

# -interaction=nonstopmode keeps the pdflatex backend from stopping at a
# missing file reference and interactively asking you for an alternative.

# -synctex=1 enables syncronization between the LaTeX sources and the generated
# PDF so that it is possible to jump to the source file when clicking on the
# PDF, and vice-versa. Note that this option requires that the viewer and the
# editor are properly configured.

%.pdf: %.tex
	latexmk -pdf -pdflatex=$(PDFLATEX) -use-make $<

watch: $(DOCNAME).tex
	latexmk -pvc -pdf -pdflatex=$(PDFLATEX) -use-make $(DOCNAME).tex

clean:
	latexmk -CA

%-ott.tex: %-ott.ott
	ott -i $< -o $@
