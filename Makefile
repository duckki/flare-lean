.PHONY: all build check lint fmt fmt-check

all: build check

build:
	time lake build

b: build

lint:
	time lake lint

fmt:
	time python3 scripts/fmt.py

fmt-check:
	time python3 scripts/fmt.py --check

check: lint
	time python3 -m unittest discover -s scripts -p 'test_*.py'
	time python3 scripts/fmt.py --check

c: check
