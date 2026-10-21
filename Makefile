.PHONY: all build check lint fmt fmt-check numerics-check numerics-bench numerics-scale

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

numerics-check:
	env FLARE_NUMERICS_INTEGRATION=1 python3 -m unittest discover -s scripts -p 'test_numerics*.py'

numerics-bench:
	python3 scripts/benchmark_numerics.py --out .cache/numerics-generated/bench-$$(date +%Y%m%d-%H%M%S)

numerics-scale:
	python3 scripts/benchmark_numerics.py --suite scale --out .cache/numerics-generated/scale-$$(date +%Y%m%d-%H%M%S)
