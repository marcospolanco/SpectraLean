# QA Scoreboard and Repository Health

**Status:** Canonical verification record  
**Last reviewed:** August 17, 2026

This document separates source-derived counts from commands that have actually been run. A QA declaration is counted syntactically; it is considered verified only when its module check passes. QA proves selected consequences relative to Scaffold’s axioms and does not prove those axioms.

## Source metrics

Run `python3 scripts/generate_qa_scoreboard.py` after changing Lean source.

<!-- BEGIN GENERATED SOURCE METRICS -->
_Generated from Lean source on 2026-08-17._

| Metric | Count |
| --- | ---: |
| QA theorem/lemma declarations | 107 |
| `sorry`/`admit` tokens in QA code | 0 |
| Explicit axioms in `Scaffold/Mathlib` | 18 |
| `sorry`/`admit` tokens in `Scaffold/Mathlib` code | 0 |

### QA declarations by domain

| Domain | Declarations |
| --- | ---: |
| Concentration | 12 |
| Derived | 11 |
| Perturbation | 5 |
| SpectralGraph | 79 |

### QA files

| File | Declarations | Placeholder tokens |
| --- | ---: | ---: |
| `Scaffold/QA/Concentration/Matrix_QA.lean` | 6 | 0 |
| `Scaffold/QA/Concentration/Scalar_QA.lean` | 6 | 0 |
| `Scaffold/QA/Derived/EventStream_QA.lean` | 7 | 0 |
| `Scaffold/QA/Derived/ProjectorDrift_QA.lean` | 4 | 0 |
| `Scaffold/QA/Perturbation/DavisKahan_QA.lean` | 1 | 0 |
| `Scaffold/QA/Perturbation/Weyl_QA.lean` | 4 | 0 |
| `Scaffold/QA/SpectralGraph/BasicProperties_QA.lean` | 5 | 0 |
| `Scaffold/QA/SpectralGraph/Basic_QA.lean` | 14 | 0 |
| `Scaffold/QA/SpectralGraph/Cheeger_QA.lean` | 7 | 0 |
| `Scaffold/QA/SpectralGraph/Cuts_QA.lean` | 11 | 0 |
| `Scaffold/QA/SpectralGraph/Dynamics_QA.lean` | 6 | 0 |
| `Scaffold/QA/SpectralGraph/Interlacing_QA.lean` | 5 | 0 |
| `Scaffold/QA/SpectralGraph/Normalized_QA.lean` | 14 | 0 |
| `Scaffold/QA/SpectralGraph/Projector_QA.lean` | 5 | 0 |
| `Scaffold/QA/SpectralGraph/RandomWalk_QA.lean` | 7 | 0 |
| `Scaffold/QA/SpectralGraph/Variational_QA.lean` | 5 | 0 |
<!-- END GENERATED SOURCE METRICS -->

## Verification record

| Check | Result | Date | Scope and limitation |
| --- | --- | --- | --- |
| `lake build` | Pass | 2026-08-17 | Default target is the library root `Scaffold.lean`; its umbrella certifies `Core.{RandomVariable,Norms,MatrixUpdates}`, `GraphTheory.{Spectral,Cheeger,RandomWalk,Normalized,Dynamics}`, `Analysis.OperatorTheory.Perturbation.{Weyl,DavisKahan}`, `Probability.Concentration.{Scalar.*,Matrix.*}`, and the derived layer `Derived.{EventStream,ProjectorDrift}`. |
| Direct QA module targets | Pass | 2026-08-17 | All sixteen QA modules compiled individually (`lake build Scaffold.QA.…`) with no `sorry`/`admit`, including `SpectralGraph/{Normalized,Cuts}_QA.lean`. |
| Direct public module targets | Pass | 2026-08-17 | All nineteen public modules (the prior eighteen plus `Scaffold.Mathlib.GraphTheory.Normalized`) compile individually. |
| Mathlib cache provenance | Note | 2026-08-17 | The local `lake exe cache` binary crashes under the current macOS dyld (`__DATA_CONST segment missing SG_READ_ONLY flag`); the cache was fetched by running the same Cache tool logic interpreted via `lake env lean --run`, unpacking 5685 Mathlib oleans. |
| `scripts/lint_axioms.py` | Pass | 2026-08-17 | All 18 explicit axioms are covered by `index/sources/` and `index/map/`. |
| `scripts/check_citations.py` | Pass | 2026-08-17 | Every axiom carries a `Source:` citation in its doc comment. |
| `scripts/check_markdown_links.py` | Pass | 2026-08-17 | No broken repository-relative targets in active docs; excludes the historical archive, the dependency checkout, and the local `.opencode/` tooling directory (including its vendored `node_modules`). |

## Interpretation

- **Explicit axiom:** an intentional trust boundary declared with Lean's `axiom` command. QA lemmas and derived theorems using these axioms are conditional on them.
- **Admitted proof:** a `sorry` or `admit` accepted by Lean; this is different from an explicit axiom and remains technical debt in public modules. As of this scoreboard there are no `sorry`/`admit` tokens anywhere under `Scaffold/`.
- **QA declaration:** a theorem or lemma under `Scaffold/QA`; all 107 declarations have compiled against the current public API.
- **Default build:** the umbrella reaches every public module listed above; no public module is excluded from `lake build`.
- **Cut duality (2026-08-17):** the first expansion/cut slice delivered in the center — `vol_compl`, `boundary_compl`, `conductance_compl` (cuts are partition-valued: boundary and conductance invariant under complementation for symmetric weights, via volume complementarity and `Finset.sum_comm`), and the degenerate-cut guards `boundary_empty`/`boundary_univ`. These are the structural facts sweep-cut and sparsest-cut consumers assume; no axioms admitted.
- **Random-walk and normalized-Laplacian interfaces (2026-08-17):** the first two broad-SGT backlog items delivered — `GraphTheory.RandomWalk` (transition matrix, row-stochasticity for `d`-regular graphs, walk-Laplacian bridges to both existing worlds) and `GraphTheory.Normalized` (the *irregular* symmetric normalized Laplacian through a diagonal `Real.sqrt` square root — no matrix square root needed — with the congruence `√D L_sym √D = laplacian`, regular-cone agreement, the general walk form `D⁻¹A` with irregular row-stochasticity, and the similarity identity `√D · L_walk · (1/√D) = L_sym`; the eigenvalue-list transfer is the named residual gap — the walk form is not symmetric, so `evals` does not apply, and the pinned Mathlib has no charpoly-roots interface for non-symmetric matrices). No axioms admitted in either module.
- **Citation and assumption review (2026-08-17):** `spectral_gap_stability` was converted from an admitted axiom into a theorem proved from `weyl_inequality` (four Weyl facts plus arithmetic), reducing the explicit axiom count from 19 to 18 at no trust cost; `weyl_inequality`'s doc now records that its Lean form is the spectral-norm corollary of the cited general theorem; `davis_kahan_sin_theta`'s separation hypothesis was tightened from a pairwise quantification to the binding single-pair two-cluster form `λ_{k+1}(A+E) − λ_k(A) ≥ δ` (the form used by the cited Yu–Wang–Samworth Theorem 2), with the derived wrapper simplified accordingly (Weyl at the gap index only). The Chung index's provenance note was corrected: git history shows no earlier page-level locators ever recorded (the initial commit cited "Theorem 2.2" without a page); theorem and page numbering remain explicitly unconfirmed rather than invented.
- **Projector algebra (2026-08-17):** eigenbasis orthonormality (`eigvecOf_inner`) and completeness (`eigvecOf_complete`) are proved from the Mathlib spectral-theorem API, yielding proved `spectralProjector_idempotent` / `initialProjector_idempotent` and the extreme-threshold theorems `spectralProjector_eq_zero` / `spectralProjector_eq_one`. These structural facts were previously consumed implicitly through the admitted perturbation interfaces.
- **Derived layer:** `Derived.EventStream.eventStreamTail` is proved from `matrix_azuma_hoeffding`; `Derived.ProjectorDrift.davisKahanTwoPoint` is proved from `davis_kahan_sin_theta` and `weyl_inequality`; `Derived.ProjectorDrift.eventStreamProjectorDrift` combines them with `eventStreamTail`. All three are checked deductions relative to the trust base (three concentration/perturbation axioms), not foundationally proved results.
- **`spectral_persistence` deprecation (2026-08-17):** the per-step persistence axiom was deprecated with a migration note after a consumer inventory showed zero non-QA consumers and the derived two-endpoint chain covering the motivating use. The axiom is retained through the compatibility window (its QA deliberately exercises the deprecated surface with the linter silenced for that use only); removal is a later release decision. The explicit axiom count remains 18 until removal.
- **Azuma statement repair (2026-08-17, same day as the axiom's introduction):** preparing the derivation exposed that `matrix_azuma_hoeffding` lacked the summand-count factor `m` in the exponent denominator, which made the statement false for `m ≥ 2` (Rademacher-sum counterexample). The denominator is now `8 m R²`, the uniform-bound specialization of Tropp's variance statistic `σ² = ‖∑ Yₖ²‖ ≤ m R²`. The axiom had no downstream consumers before the repair.

## Active priorities

1. Fold or deprecate the unconsumed per-step `spectral_persistence` axiom
   in favor of the two-endpoint derived chain.
2. Confirm Horn–Johnson section-level and Chung chapter-level locators
   against physical or publisher copies (no local copy available; numbers
   must not be invented).
3. Specify the x90 observable against the completed persistence chain
   (application ring; the inner chain is now credible end-to-end).
4. Add QA based on risk and composability rather than targeting a cosmetic one-to-one ratio.

## Historical reports

Earlier scoreboards and build reports are preserved under [`research/archive/status/`](../research/archive/status/). They are historical snapshots and may contradict current generated metrics.
