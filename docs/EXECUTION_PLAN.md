# Execution plan

This is the compact, current-state ledger for sustained autonomous work. It is
updated at milestone boundaries; [`AGENT_ACTIVITY.md`](AGENT_ACTIVITY.md)
holds the append-only narrative.

## Active milestone

**Prove spectral-projector algebra in the SGT center.** The persistence
chain is assembled end-to-end in the derived layer. The remaining inner
obligation named by the architecture is projector idempotence and
eigenbasis orthonormality behind `spectralProjector`, currently consumed
through the admitted perturbation interfaces rather than proved.

**Design (2026-08-17, in progress):** the pinned Mathlib
`OrthonormalBasis` API supplies both structural facts, so no new axioms
are needed:

1. `eigvecOf_inner` (proved) — pairwise orthonormality
   `∑ k, v i k * v j k = δᵢⱼ`, from `OrthonormalBasis.orthonormal` and
   `PiLp.inner_apply` (both definitional `rfl` computations in this
   snapshot).
2. `eigvecOf_complete` (proved) — completeness
   `∑ i, v i a * v i b = δₐᵦ`, from `OrthonormalBasis.sum_repr'` at
   `EuclideanSpace.single a 1`.
3. `spectralProjector_idempotent` (proved) — `P_c * P_c = P_c` by
   entrywise expansion (`Finset.sum_mul_sum`, two `Finset.sum_comm`s,
   orthonormality, `Finset.sum_ite_eq'` collapse).
4. Extreme-threshold theorems (proved, hypothesis-gated):
   `spectralProjector_eq_zero` below the spectrum (filter empty),
   `spectralProjector_eq_one` above it (filter univ + completeness);
   plus `initialProjector_idempotent` as consumer corollary.
5. New QA file `Scaffold/QA/SpectralGraph/Projector_QA.lean` composing the
   extreme cases with idempotence (0 and 1 are idempotent through the
   gated theorems); thin-QA rationale documented since these are theorems,
   not axioms.

**Leverage:** converts implicit structural trust (every projector-based
statement in Cheeger/persistence/drift assumes `P² = P`) into hard crust
via the Mathlib spectral-theorem API, and unblocks tightening
Davis–Kahan/persistence assumptions later.

**Next action:** implement steps 1–5, build `GraphTheory.Spectral` and the
QA directly, update the architecture debt list and scoreboard, rerun all
hygiene scripts.

## Ready queue

1. Projector algebra (active milestone above).
2. Review page-level locators for Horn--Johnson and Chung; tighten explicit
   projector/eigenbasis assumptions where possible.
3. Fold or deprecate the unconsumed per-step `spectral_persistence` axiom
   in favor of the two-endpoint derived chain.
4. Specify the x90 observable against the completed persistence chain
   (application ring).
5. Re-admit removed subgaussian statements (moment growth, linear
   combinations, centering, sums) only when a consumer names them.

## Last verified state

- 2026-08-17 (derived layer, step 2): `lake build` passes with the full
  umbrella including `Scaffold.Derived.{EventStream,ProjectorDrift}`;
  all seventeen public modules and all twelve QA modules (70 declarations)
  compile directly with no `sorry`/`admit`; 19 explicit cited axioms;
  `lint_axioms`, `check_citations`, and `check_markdown_links` all pass.
- Same run: `eventStreamProjectorDrift` derived from
  `matrix_azuma_hoeffding` + `weyl_inequality` + `davis_kahan_sin_theta`
  with no new axioms; proved center theorem `initialProjector_congr` added.

## Blockers

- The native Mathlib cache executable fails on this macOS environment with a
  dyld segment error. Cached artifacts were obtained through the recorded Lean
  interpreter workaround; this is environment debt, not an SGT source failure.
