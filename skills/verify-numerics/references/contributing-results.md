# Contribute reusable verification results

Use this follow-up only after delivering a successfully completed verification
task: the requested guarantee has an audited, replayed Lean proof, the report and
artifacts are delivered, and any requested Rust port is complete. A delivered,
audited and replayed Lean counterexample can also complete a verification task;
an analyzer candidate, rejection, timeout or missing bridge cannot. Finish the
engineer's task before proposing library work.

The destination is [duckki/flare-lean](https://github.com/duckki/flare-lean).
Scope all PR overlap searches and submissions to this repository. This optional
contribution lets later verification tasks reuse checked results.

## Identify a useful result and check overlap

- Review the helpers actually proved during the task. Select a theorem or small
  connected group with an independent use: a composable error contract, invariant,
  source-semantics bridge or reusable inference rule. A generated certificate for
  one input domain or fixed horizon alone is usually application evidence.
  Prefer reusable machinery over accumulating specialized bound instances. Do not
  invent extra lemmas or broaden assumptions just to generate a contribution.
- Search the provider's FLARE and pinned Mathlib declarations, then current FLARE
  upstream. Compare definitions, hypotheses and conclusions, including equivalent
  formulations with different names. Reuse an existing result when it suffices.
  Read the target checkout's `AGENTS.md`, `CONTRIBUTING.md` and organization guide.
  The Mathlib check concerns existing declarations; the PR workflow targets FLARE.
- Search [FLARE pull requests](https://github.com/duckki/flare-lean/pulls) using
  GitHub tools, `gh` or the web. Cover open PRs and merged/closed PRs, using both
  theorem/definition names and mathematical concepts. Read relevant descriptions
  and diffs; titles alone do not establish overlap. Record the search terms,
  relevant links, and any remaining gap in the contribution proposal.
- If an open PR covers the result, report its link and avoid a duplicate. If a
  merged PR already supplies it, reuse it on a compatible dependency revision;
  keep the completed application's frozen proof unchanged. For a closed,
  unmerged proposal, read its disposition before deciding whether a distinct
  contribution is warranted. A small new gap can warrant a separate PR when its
  relationship to the existing work is clear.

If no reusable gap remains, finish without a contribution prompt. An unavailable
search is not evidence of novelty: report the search limitation and keep the
contribution unpublished. This does not change the completed verification result.

## Prepare a reviewable contribution

Prepare a minimal local diff against FLARE's current default branch, in an
isolated checkout or worktree. Reuse an existing suitable location, or announce
a checkout under the shared user cache. Keep application artifacts and the
provider revision used for frozen replay intact.

Extract statements and proofs with their existing assumptions. Keep new
generalizations, tighter bounds and changed operation orders separate. Use the
library's established definitions and subject modules: `Flare/Analysis`,
`Flare/Binary64` or `Flare/Matrix`, respecting their import boundaries. Preserve
attribution and applicable source licenses. Include only reusable definitions,
proofs, focused checks and documentation in the proposed public diff; application
reports, frozen runs, local paths and tool downloads stay outside it.

Follow the checkout's validation rules: format with `make fmt` at width 100 and
run `make check`, including the proof audit. If changing workflow integration,
also run `make numerics-check` and relevant smoke/scale benchmarks. A theorem
must compile with no admitted proofs or additional axioms; its transitive axiom
closure may use only `propext`, `Classical.choice` and `Quot.sound`. Explain how
its statement follows from the application proof and how another caller can
reuse it. Update exports, proof coverage, documentation and the source manifest
when required by the contribution guide.

## Ask once, then publish if authorized

Present the prepared diff, theorem names and assumptions, intended reuse, check
results, and overlap findings. After the completed verification report, ask one
concise question, for example:

> Verification is complete. The checked helper `…` also applies to `…`. Searches
> of existing declarations and FLARE PRs found no equivalent result. The proposed
> diff contains `…`; `make check` passed. May I commit this change and open a
> public PR to `duckki/flare-lean`?

Use the actual findings, including related PR links, instead of assuming that
the search is empty. This question authorizes publishing the specific reviewed
diff. Reuse explicit authorization already given for this contribution; do not
ask again. A decline or no reply leaves the verified deliverable complete and
the contribution unpublished. Do not repeat the offer in the same task.

After authorization, refresh the default branch and overlap search before
publishing, and rerun affected checks if the base changed. If the result is still
warranted, create a focused branch, commit the reviewed diff, push to an
authorized remote or fork, and open one PR targeting `duckki/flare-lean`.
Describe the theorem's useful behavior, exact hypotheses, provenance, relevant
existing PRs and validation. Return the PR link, and attach it to the current
task if an attachment tool is available. Do not comment on or modify someone
else's PR as a substitute without authorization. If authentication, permissions
or checks block publication, retain the local patch and report that limitation;
do not claim a PR was created or retry publication indefinitely.
