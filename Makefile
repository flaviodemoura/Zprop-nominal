# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _RocqProject

# Directories for documentation generation
SRC_DIR = src
LATEX_DIR = latex

# Tools
ROQC = rocq
PDFLATEX = pdflatex
BIBTEX = bibtex

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _RocqProject
	$(ROQC) makefile -f _RocqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

$(KNOWNFILES): ;

####################################################################
##                      Your targets here                         ##
####################################################################

# Find all .v files in src directory
V_FILES := $(wildcard $(SRC_DIR)/*.v)
# Get just the filenames without path or extension
V_NAMES := $(notdir $(V_FILES:.v=))
# Generate corresponding .v.tex filenames in latex directory
TEX_FILES := $(addprefix $(LATEX_DIR)/, $(addsuffix .v.tex, $(V_NAMES)))

# Create latex directory if it doesn't exist
$(LATEX_DIR):
	mkdir -p $(LATEX_DIR)

# Prevent the catch-all "%: invoke-coqmakefile" rule below from being used
# to (re)build the .v source files: without this, make treats them as
# reachable via that pattern too and forwards the top-level goal to
# CoqMakefile, which breaks targets like `doc` that CoqMakefile doesn't know.
$(SRC_DIR)/%.v: ;
tools/%.py: ;

# Logical path of src/ (must match _RocqProject) and the repository URL that
# identifiers in the PDF link to. REV pins the links to a commit so that line
# numbers stay valid; override it with e.g. `make doc REV=v1.0`.
LOGICAL = LXConfl
REPO_URL = https://github.com/flaviodemoura/Zprop-nominal
REV ?= $(shell git rev-parse HEAD)

# The .glob files (needed for hyperlinks) are produced by compiling the .v files
$(SRC_DIR)/%.glob: $(SRC_DIR)/%.v CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(SRC_DIR)/$*.vo

# Generate all .v.tex files in a single rocq doc run, so that identifiers
# defined in one file are linked where they are used in another.
# --body-only ensures only the body content is included
$(TEX_FILES) &: $(V_FILES) $(V_FILES:.v=.glob) tools/tidy_coqdoc.py | $(LATEX_DIR)
	cd $(LATEX_DIR) && $(ROQC) doc --latex --body-only -l -s \
	  -R ../$(SRC_DIR) $(LOGICAL) $(addprefix ../,$(V_FILES))
	@# rocq doc names the files after their logical path; rename them to <name>.v.tex
	cd $(LATEX_DIR) && for f in $(V_NAMES); do mv $(LOGICAL).$$f.tex $$f.v.tex; done
	@# drop empty code blocks, which would otherwise show up as empty boxes
	python3 tools/tidy_coqdoc.py $(TEX_FILES)

# Line number of every definition, used to link identifiers to the repository
$(LATEX_DIR)/coqsrclinks.tex: tools/glob2links.py $(V_FILES:.v=.glob) | $(LATEX_DIR)
	python3 tools/glob2links.py $(SRC_DIR) $(LOGICAL) $(V_NAMES) > $@

$(LATEX_DIR)/coqsrcbase.tex: FORCE | $(LATEX_DIR)
	@echo '\newcommand{\coqsrcbase}{$(REPO_URL)/blob/$(REV)/$(SRC_DIR)/}' > $@.tmp
	@cmp -s $@.tmp $@ && rm $@.tmp || mv $@.tmp $@
	@git diff --quiet HEAD -- $(SRC_DIR) || echo "Warning: $(SRC_DIR) has uncommitted changes; links point to $(REV)"

.PHONY: FORCE
FORCE:

# Target to generate all .v.tex files
.PHONY: tex-fragments
tex-fragments: $(TEX_FILES)
	@echo "All documentation files generated in $(LATEX_DIR)/"
	@ls -la $(LATEX_DIR)/*.v.tex 2>/dev/null || echo "No .v.tex files found"

# Debug target to see what rocq doc actually generates
.PHONY: debug-rocq-doc
debug-rocq-doc: | $(LATEX_DIR)
	@echo "Testing rocq doc on first .v file with -l -s option..."
	@cd $(LATEX_DIR) && $(ROQC) doc --latex -l -s ../$(firstword $(V_FILES))
	@echo "Files generated in $(LATEX_DIR):"
	@ls -la $(LATEX_DIR)/*
	@echo ""
	@echo "First 10 lines of generated .tex file (should start at line 7 of original):"
	@head -10 $(LATEX_DIR)/$(firstword $(V_NAMES)).tex 2>/dev/null || echo "No .tex file found"

# Individual file target (kept for backward compatibility)
.PHONY: tex-fragment-%
tex-fragment-%: $(LATEX_DIR)/%.v.tex
	@echo "Generated $<"

# Main documentation target
.PHONY: doc
doc: $(LATEX_DIR)/sbmf2026.pdf

$(LATEX_DIR)/sbmf2026.pdf: $(LATEX_DIR)/sbmf2026.tex $(TEX_FILES) $(LATEX_DIR)/coqsrclinks.tex $(LATEX_DIR)/coqsrcbase.tex | $(LATEX_DIR)
	cd $(LATEX_DIR) && $(PDFLATEX) sbmf2026
	cd $(LATEX_DIR) && $(PDFLATEX) sbmf2026 && $(BIBTEX) sbmf2026
	cd $(LATEX_DIR) && $(PDFLATEX) sbmf2026
	cd $(LATEX_DIR) && $(PDFLATEX) sbmf2026

# Clean documentation files
.PHONY: clean-doc
clean-doc:
	rm -rf $(LATEX_DIR)/*.aux $(LATEX_DIR)/*.log $(LATEX_DIR)/*.out
	rm -f $(LATEX_DIR)/*.v.tex $(LATEX_DIR)/coqsrclinks.tex $(LATEX_DIR)/coqsrcbase.tex

# Add doc cleaning to the main clean target
.PHONY: clean
clean: clean-doc
	-$(MAKE) --no-print-directory -f CoqMakefile clean
	rm -f CoqMakefile*

# Show debug information
.PHONY: debug-doc
debug-doc:
	@echo "SRC_DIR = $(SRC_DIR)"
	@echo "LATEX_DIR = $(LATEX_DIR)"
	@echo "V_FILES = $(V_FILES)"
	@echo "V_NAMES = $(V_NAMES)"
	@echo "TEX_FILES = $(TEX_FILES)"
	@echo "ROQC = $(ROQC)"
	@echo "PDFLATEX = $(PDFLATEX)"
	@echo ""
	@echo "Files in $(SRC_DIR):"
	@ls -la $(SRC_DIR)/*.v 2>/dev/null || echo "No .v files found"

# Open pdf with evince
.PHONY: pdf
pdf:
	zathura latex/sbmf2026.pdf&

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
