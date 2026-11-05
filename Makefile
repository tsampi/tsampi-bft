SHELL := /bin/bash
.SHELLFLAGS := -eu -o pipefail -c
PYTHON ?= python3
.DEFAULT_GOAL := verify
BUILD_DIR := build
PAPER_NAME := tsampi-bft
PAPER_BUILD_DIR := $(BUILD_DIR)/paper

.PHONY: lean bend rocq python paper verify clean help

lean bend rocq python:
	$(MAKE) -C $@ verify

paper:
	command -v pdflatex >/dev/null
	command -v bibtex >/dev/null
	rm -rf $(PAPER_BUILD_DIR)
	mkdir -p $(PAPER_BUILD_DIR)
	cp paper/$(PAPER_NAME).tex $(PAPER_BUILD_DIR)/
	cd $(PAPER_BUILD_DIR) && pdflatex -interaction=nonstopmode -halt-on-error $(PAPER_NAME).tex
	cd $(PAPER_BUILD_DIR) && bibtex $(PAPER_NAME)
	cd $(PAPER_BUILD_DIR) && pdflatex -interaction=nonstopmode -halt-on-error $(PAPER_NAME).tex
	cd $(PAPER_BUILD_DIR) && pdflatex -interaction=nonstopmode -halt-on-error $(PAPER_NAME).tex
	cd $(PAPER_BUILD_DIR) && pdflatex -interaction=nonstopmode -halt-on-error $(PAPER_NAME).tex
	! grep -Eq 'undefined citations|undefined references|There were undefined citations|Label\(s\) may have changed' $(PAPER_BUILD_DIR)/$(PAPER_NAME).log
	cp $(PAPER_BUILD_DIR)/$(PAPER_NAME).pdf $(PAPER_NAME).pdf

verify: lean bend rocq python paper
	@printf 'BFT_PUBLIC_VERIFY_OK\n'

clean:
	$(MAKE) -C lean clean
	$(MAKE) -C rocq clean
	rm -rf -- $(BUILD_DIR)

help:
	@printf '%s\n' \
		'lean    Check the Lean definitions and proofs.' \
		'bend    Check the Bend definitions and kernel verdicts.' \
		'rocq    Compile and kernel-check the Rocq proofs.' \
		'python  Run the Python simulation tests.' \
		'paper   Build tsampi-bft.pdf.' \
		'verify  Run all checks and build the paper (default).' \
		'clean   Remove generated build files.' \
		'help    Show these targets.'
