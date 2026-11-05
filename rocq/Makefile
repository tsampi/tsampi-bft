SHELL := /bin/bash
.SHELLFLAGS := -eu -o pipefail -c
COQC ?= coqc
COQCHK ?= coqchk
SOURCES := $(shell sed -n '/\.v$$/p' _CoqProject)

.PHONY: build verify clean help

build:
	for source in $(SOURCES); do $(COQC) -q -Q . BFT "$$source"; done

verify: build
	$(COQCHK) -silent -Q . BFT BFT.Proofs

clean:
	rm -f -- *.vo *.vok *.vos *.glob .*.aux .lia.cache

help:
	@printf '%s\n' 'build   Compile the public Rocq project.' 'verify  Compile and kernel-check the public proofs.' 'clean   Remove Rocq build output.'
