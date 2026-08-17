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
| QA theorem/lemma declarations | 70 |
| `sorry`/`admit` tokens in QA code | 0 |
| Explicit axioms in `Scaffold/Mathlib` | 19 |
| `sorry`/`admit` tokens in `Scaffold/Mathlib` code | 0 |

### QA declarations by domain

| Domain | Declarations |
| --- | ---: |
| Concentration | 12 |
| Derived | 11 |
| Perturbation | 5 |
| SpectralGraph | 42 |

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
| `Scaffold/QA/SpectralGraph/Dynamics_QA.lean` | 6 | 0 |
| `Scaffold/QA/SpectralGraph/Interlacing_QA.lean` | 5 | 0 |
| `Scaffold/QA/SpectralGraph/Variational_QA.lean` | 5 | 0 |
<!-- END GENERATED SOURCE METRICS -->

## Verification record

| Check | Result | Date | Scope and limitation |
| --- | --- | --- | --- |
| `lake build` | Pass | 2026-08-17 | Default target is the library root `Scaffold.lean`; its umbrella certifies `Core.{RandomVariable,Norms,MatrixUpdates}`, `GraphTheory.{Spectral,Cheeger,Dynamics}`, `Analysis.OperatorTheory.Perturbation.{Weyl,DavisKahan}`, `Probability.Concentration.{Scalar.*,Matrix.*}`, and the derived layer `Derived.{EventStream,ProjectorDrift}`. |
| Direct QA module targets | Pass | 2026-08-17 | All twelve QA modules compiled individually (`lake build Scaffold.QA.…`) with no `sorry`/`admit`, including `Derived/{EventStream,ProjectorDrift}_QA.lean`. |
| Direct public module targets | Pass | 2026-08-17 | All seventeen public modules (the prior sixteen plus `Scaffold.Derived.ProjectorDrift`) compile individually. |
| Mathlib cache provenance | Note | 2026-08-17 | The local `lake exe cache` binary crashes under the current macOS dyld (`__DATA_CONST segment missing SG_READ_ONLY flag`); the cache was fetched by running the same Cache tool logic interpreted via `lake env lean --run`, unpacking 5685 Mathlib oleans. |
| `scripts/lint_axioms.py` | Pass | 2026-08-17 | All 19 explicit axioms are covered by `index/sources/` and `index/map/`. |
| `scripts/check_citations.py` | Pass | 2026-08-17 | Every axiom carries a `Source:` citation in its doc comment. |
| `scripts/check_markdown_links.py` | Pass | 2026-08-17 | No broken repository-relative targets in active docs; excludes the historical archive, the dependency checkout, and the local `.opencode/` tooling directory (including its vendored `node_modules`). |

## Interpretation

- **Explicit axiom:** an intentional trust boundary declared with Lean's `axiom` command. QA lemmas and derived theorems using these axioms are conditional on them.
- **Admitted proof:** a `sorry` or `admit` accepted by Lean; this is different from an explicit axiom and remains technical debt in public modules. As of this scoreboard there are no `sorry`/`admit` tokens anywhere under `Scaffold/`.
- **QA declaration:** a theorem or lemma under `Scaffold/QA`; all 70 declarations have compiled against the current public API.
- **Default build:** the umbrella reaches every public module listed above; no public module is excluded from `lake build`.
- **Derived layer:** `Derived.EventStream.eventStreamTail` is proved from `matrix_azuma_hoeffding`; `Derived.ProjectorDrift.davisKahanTwoPoint` is proved from `davis_kahan_sin_theta` and `weyl_inequality`; `Derived.ProjectorDrift.eventStreamProjectorDrift` combines them with `eventStreamTail`. All three are checked deductions relative to the trust base (three concentration/perturbation axioms), not foundationally proved results. No new axioms were introduced for the projector-drift milestone; one proved center theorem (`initialProjector_congr`) was added.
- **Azuma statement repair (2026-08-17, same day as the axiom's introduction):** preparing the derivation exposed that `matrix_azuma_hoeffding` lacked the summand-count factor `m` in the exponent denominator, which made the statement false for `m ≥ 2` (Rademacher-sum counterexample). The denominator is now `8 m R²`, the uniform-bound specialization of Tropp's variance statistic `σ² = ‖∑ Yₖ²‖ ≤ m R²`. The axiom had no downstream consumers before the repair.

## Active priorities

1. Prove spectral-projector idempotence and eigenbasis orthonormality
   behind `spectralProjector` in the SGT center, replacing facts currently
   consumed through the admitted perturbation interfaces.
2. Review page-level locators for Horn--Johnson and Chung; tighten explicit
   projector/eigenbasis assumptions where possible.
3. Specify the x90 observable against the completed persistence chain
   (application ring; only now that concentration → perturbation →
   persistence is credible end-to-end).
4. Add QA based on risk and composability rather than targeting a cosmetic one-to-one ratio.

## Historical reports

Earlier scoreboards and build reports are preserved under [`research/archive/status/`](../research/archive/status/). They are historical snapshots and may contradict current generated metrics.
