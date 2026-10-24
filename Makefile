.PHONY: all build check docs-check lint fmt fmt-check numerics-check numerics-bench numerics-scale

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

docs-check:
	python3 scripts/check_docs.py

check: docs-check lint
	time python3 -m unittest discover -s provider/tests -t provider -p 'test_*.py'
	time python3 scripts/fmt.py --check

c: check

numerics-check:
	env FLARE_NUMERICS_INTEGRATION=1 python3 -m unittest discover -s provider/tests -t provider -p 'test_numerics*.py'

numerics-bench:
	python3 scripts/benchmark_numerics.py --out .cache/numerics-generated/bench-$$(date +%Y%m%d-%H%M%S)

numerics-scale:
	python3 scripts/benchmark_numerics.py --suite scale --out .cache/numerics-generated/scale-$$(date +%Y%m%d-%H%M%S)
