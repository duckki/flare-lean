# Retained public application checks

These cases were selected before adding their admission support. Each directory
keeps the unmodified full upstream source and license, pinned revision/hashes,
`initial-request.json`, original first-attempt result, supported `request.json`
and `assistance.json`. Initial domains, independent references and error limits
are unchanged. The only request additions select the new closed source bridge.

| Case | Domain | Checked scope | Assistance |
| --- | --- | --- | --- |
| Chemicals `API_to_SG` | Petroleum density conversion; API 10–80 | Specific gravity against `283/(2*API+263)`, error ≤ 1e-12 | Closed module selection and generic total-field equality checking |
| NumPy `_compute_virtual_index` | Scientific quantile helper; four quantiles 0–1, binary64 sample count 1–1000, α/β 0–1 | Four index values against independent collection algebra, error ≤ 1e-10 | Module selection, exact integer-literal promotion, polynomial reference checking |
| ROS `angles::from_degrees` | Robotics; degrees −360–360 | Radians using the configured **binary64** π constant, error ≤ 1e-12 | Closed C++ header selection and actual-header constant checks |

These certify selected admitted source models with explicit parser/runtime trust.
Python functions execute as the original definitions in isolation; unrelated
module initialization and dynamic dispatch require caller review. NumPy's full
quantile algorithm, integer-index safety and statistical properties are excluded.
The ROS reference does not establish accuracy against mathematical π.

`first-attempt.json` retains the original invocation and provider revision. Its
request hash identifies `initial-request.json`; its old scratch path is provenance,
not a prerequisite for reproduction. No authored application proofs or source,
reference, domain or budget edits were needed. Provider extensions are assistance;
these are now regression cases, not new held-out evaluations on every run.

From a built provider with NumPy 2.4.0 and pycparser 3.0:

```sh
python3 scripts/release_numerics.py --out .cache/numerics-generated/release
```

This also checks the covariance and separate ROS underflow failures, relocates portable bundles, replays
without producers/source runtimes, and rechecks unchanged contracts. It records
per-stage time, replay/recheck wall time, completed-child peak RSS and bundle size.
`--tools <JSON>` additionally exercises retained Rust delivery when its explicit
`rust_tools` selection is available. Use
[the delivery guide](../../../docs/automated-delivery.md) for setup, search,
rechecking and independent engineer reproduction. Agent-operated runs do not
satisfy the independent engineer criterion.

The ROS positivity requests are separate contracts, with an original CBMC trace
and an ordinary supplied-witness regression. They leave `initial-request.json`
and the positive accuracy request unchanged.
