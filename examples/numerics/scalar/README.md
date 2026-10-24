# Scalar numerical examples

These examples retain original Python, Julia, MATLAB-compatible and Rust scalar
source with complete verification requests. Start with `scalar_kalman.json` or
`mean_update.json`; the other requests vary the source form, producer, budget or
delivery target.

From the provider repository root:

```sh
python3 scripts/certify_numerics.py run \
  --request examples/numerics/scalar/mean_update.json \
  --out .cache/numerics-generated/scalar-example
```

The output directory must be new. These are provider regression paths;
application verification follows the skill's agreed artifact destinations.
Optional runtime, external-producer and Rust routes need their selected tools.
See the [workflow guide](../../../docs/numerical-verification.md),
[tool integration](../../../docs/integration/tool-integration.md) and
[benchmarks](../../../benchmarks/numerics/README.md) for scope and expected results.
