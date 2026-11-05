PYTHON ?= python3

.PHONY: build test verify help

build:
	$(PYTHON) -B -c 'import consensus, network, owner, codec, event_delivery'

test:
	PYTHONHASHSEED=0 $(PYTHON) -B -m unittest discover -s . -p 'test_*.py'

verify: build test

help:
	@printf '%s\n' 'build   Import the standalone Python model.' \
		'test    Run the basic simulation tests.' 'verify  Import the model and run the simulations.'
