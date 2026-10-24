# Deliver a checked numerical counterexample

For a finite scalar witness in the supported separate-binary64 profile, use the
provider's `counterexample` request path. Keep the user's original domain,
reference and requirement; a large allowance or a rejected proof is not a failure
witness. Search, sampling and foreign tools may propose inputs, but only Lean
establishes the violation.

In `numerics-request-v1`, add:

```json
"counterexample": {
  "inputs": {"p": "0x3ff0000000000000", "r": "0x3c90000000000000"},
  "output": 0
}
```

Use one `0x` + 16 lowercase hexadecimal digits word per original input. For
strict positivity the selected output is
`{"name":"variance","unit":"m²","property":"strict_positive"}`; the root
also requires a positive independent exact reference. For an attained absolute
error violation, keep the ordinary output `limit` unchanged. Other outputs still
need names, units and requirements. The provider validates a supplied witness;
it currently has no automatic witness search or CBMC adapter.

Run `certify_numerics.py run`, then `replay` into a new directory beneath the
agreed verification destination. Require status `counterexample` and entry
`Workflow.Counterexample.counterexample`. The root checks finite input/domain
conditions, actual native outputs, the independent exact value and a violation
of the selected requirement. The provider regenerates its independent root-type
and axiom check during replay. Replay needs the Lean library but no source runtime,
analyzer, witness finder, translator or LLM.

A nonviolating or out-of-domain witness is unresolved. Keep missing tools,
resource limits and rejected proof attempts separate; do not label them numerical
bugs. Deliver the decoded inputs, exact native/reference results, violated
requirement, trust boundaries and replay command. For unsupported properties or
profiles, use the authored-refutation guidance in
[lean-conversion.md](lean-conversion.md) and report authored coverage explicitly.

Read the provider's
[counterexample guide](https://github.com/duckki/flare-lean/blob/main/docs/counterexamples.md)
for the complete request, current profile limits and rejection controls.
