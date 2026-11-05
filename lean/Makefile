SHELL := /bin/bash
.SHELLFLAGS := -eu -o pipefail -c

.PHONY: build verify clean help

build:
	env -u ELAN_TOOLCHAIN lake build

verify: build

clean:
	lake clean

help:
	@printf '%s\n' 'build   Compile the protocol definitions and proofs.' 'verify  Compile all public Lean roots.' 'clean   Remove Lean build output.'
