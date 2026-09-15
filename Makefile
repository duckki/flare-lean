.PHONY: all build check lint fmt fmt-check

all: check

build:
	lake build

lint:
	lake lint

fmt:
	python3 scripts/fmt.py

fmt-check:
	python3 scripts/fmt.py --check

check: lint
	python3 -m unittest discover -s scripts -p 'test_*.py'
	python3 scripts/fmt.py --check
