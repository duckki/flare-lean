# Checked scalar failure witnesses

| Request | Original requirement | Checked witness |
| --- | --- | --- |
| `naive_covariance.json` | Strictly positive variance on the stated positive domain | `p = 1`, `r = 2^-54`: native zero, exact `1/(2^54+1) > 0` |
| `cancellation.json` | Absolute residual error at most `2^-55` | `x = 1`, `y = 2^-54`: native zero, exact `y`, attained error `2^-54` |

The first request uses the original [README snippet](naive_covariance.py).
Both use ordinary source admission, a separate independent reference, a generated
Lean root and cold replay. They are concrete violations, not upper allowances
above budget. See [the guide](../../../docs/integration/counterexamples.md).
