SHELL := /bin/bash
.SHELLFLAGS := -eu -o pipefail -c
BUN ?= bun
BEND_COMPILER ?=
export ELAN_TOOLCHAIN := $(shell cat lean-toolchain)
SOURCES := model/kernel.bend $(sort $(wildcard proofs/*.bend))

.PHONY: build verify help

build:
	@test -n "$(BEND_COMPILER)" || { printf '%s\n' 'Set BEND_COMPILER to the main.ts pinned in TOOLCHAIN.toml.' >&2; exit 1; }
	for source in $(SOURCES); do BEND_NO_TELEMETRY=1 $(BUN) "$(BEND_COMPILER)" "$$source" --check-only; done
	BEND_NO_TELEMETRY=1 $(BUN) "$(BEND_COMPILER)" proofs/network_execution.bend --verdict
	BEND_NO_TELEMETRY=1 $(BUN) "$(BEND_COMPILER)" proofs/conditional_liveness.bend --verdict

verify: build

help:
	@printf '%s\n' 'build   Check the model and proofs with the pinned Bend compiler.' 'verify  Check every public Bend source and the execution and progress proofs.'
