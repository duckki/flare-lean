# FLARE development

- Official name: FLARE. Repository: flare-lean. Lake package: flare.
  Lean namespace: Flare. Keep one Lake project and one library.
- FLARE is a proof library. Prioritize reusable definitions, theorem statements,
  and composable proofs; use Mathlib as the primary design reference. Include
  executable algorithms where they are the subjects of theorems.
- Keep pure mathematics in Flare/Analysis, native binary64 reasoning in
  Flare/Binary64, and matrix correctness proofs with their algorithms in
  Flare/Matrix.
  Analysis must not depend on Binary64, Matrix, or application projects.
- Keep shared IEEE format/packing/rounding inference in Flare/FloatFormat and
  binary32 storage conversions in Flare/Binary32. Binary32 may use Binary64 for
  exact promotion and mixed-storage numerical bounds; Binary64 uses the shared
  FloatFormat foundation. Analysis remains independent of all floating modules.
- Use content-specific module names and match declaration namespaces to file
  paths. Shared type methods may use their type namespace. Do not add
  per-directory import aggregators; keep Flare.lean as the public entry point.
- Follow docs/organization.md and CONTRIBUTING.md. Track potential Mathlib
  work in docs/upstream/mathlib.md. Name another contribution destination only
  for a concrete result that fits its definitions and scope. Keep theorem
  sources organized by subject, with one authoritative copy.
- Keep source interpretations distinct from implementation adaptations. Cite
  external definitions and state numeric domains, exceptional values, and bounds.
- Extract statements and proofs with their existing assumptions first. Treat
  generalization, tighter bounds, or changed operation order as separate changes.
  Check Mathlib for existing results before adding alternative formulations.
- No admitted proofs or additional axioms. Review definitions, statements,
  assumptions, and proof dependencies; Lean checks proof scripts.
- Do not add application-specific dependencies. Any interoperability claim
  needs a proved bridge, isolated from the core module trees.
- Maintain one engineer-facing skill in skills/verify-numerics and the provider
  CLI in scripts/certify_numerics.py. Keep external analyzers and optional Rust
  translators outside core Lake dependencies. Finish certification at one Lean
  entry theorem with numerical premises discharged and its axiom closure checked.
  Distinguish candidate bounds, checked allowances, sampled runtime diagnostics,
  and physical premises. Preserve frozen-source replay without producers or LLMs.
- Maintain reusable workflow scenarios in benchmarks/numerics and examples/numerics.
  Run make numerics-check and relevant smoke/scale benchmarks after changing the pipeline.
  Tool absence and proof rejection are different outcomes; negative controls
  must fail for the intended reason. Keep provider regression runs under
  .cache/numerics-generated/. Application artifacts and tool downloads follow
  skills/verify-numerics/SKILL.md and its confirmed destinations.
- Run relevant checks and present a reviewable slice. Commit only when requested.
  After committing, stop unless the user authorized continuing.
- Keep documentation consistent with actual exported results and proof status.
  Use doc-gen4 and importGraph/Graphviz for generated documentation when needed;
  keep generated artifacts under ignored docs-generated/.
- Format Lean with make fmt (pinned leanfmt, width 100). Run make check for
  formatting, linters, build, proof audit, and layout/import checks.
  Keep formatter exceptions limited to the affected syntax and explain why.
  Keep docs/extraction-manifest.json
  accurate when importing additional source results. Never change a source
  project as a side effect of extracting into FLARE.
- Keep public docs focused on the current library. Retain durable attribution
  in docs/organization.md and the source manifest; omit session logs and inherited
  application roadmaps.
