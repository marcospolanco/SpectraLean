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
| QA theorem/lemma declarations | 48 |
| `sorry`/`admit` tokens in QA code | 0 |
| Explicit axioms in `Scaffold/Mathlib` | 26 |
| `sorry`/`admit` tokens in `Scaffold/Mathlib` code | 0 |

### QA declarations by domain

| Domain | Declarations |
| --- | ---: |
| Concentration | 1 |
| Perturbation | 5 |
| SpectralGraph | 42 |

### QA files

| File | Declarations | Placeholder tokens |
| --- | ---: | ---: |
| `Scaffold/QA/Concentration/Matrix_QA.lean` | 1 | 0 |
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
| `lake build` | Pass | 2026-08-17 | Default target is the library root `Scaffold.lean`; its umbrella certifies `Core.{RandomVariable,Norms,MatrixUpdates}`, `GraphTheory.{Spectral,Cheeger,Dynamics}`, and `Analysis.OperatorTheory.Perturbation.{Weyl,DavisKahan}`. The probability concentration subtree is not reachable through the umbrella. |
| Direct QA module targets | Pass | 2026-08-17 | All SpectralGraph and Perturbation QA modules compiled individually (`lake build Scaffold.QA.…`) with no `sorry`/`admit`. `Scaffold/QA/Concentration/Matrix_QA.lean` is **not** certified: its imports (`Probability.Concentration.Matrix.*`) do not elaborate. |
| Public Mathlib-mirror module targets | Pass | 2026-08-17 | All eight umbrella modules compile directly. `Scaffold.Mathlib.Probability.Concentration.*` (six modules) still fails to elaborate: invalid binder annotations, `expected token` parse errors, and undefined `RV`/`Independent` references. |
| Mathlib cache provenance | Note | 2026-08-17 | The local `lake exe cache` binary crashes under the current macOS dyld (`__DATA_CONST segment missing SG_READ_ONLY flag`); the cache was fetched by running the same Cache tool logic interpreted via `lake env lean --run`, unpacking 5685 Mathlib oleans. |
| `scripts/lint_axioms.py` | Pass with 1 warning | 2026-08-17 | `matrix_azuma_hoeffding` (uncertified concentration module) is absent from the index. The ten axioms of the certified modules are covered by `index/sources/` and `index/map/`. |
| `scripts/check_citations.py` | Fail: 1 issue | 2026-08-17 | `matrix_azuma_hoeffding` lacks a `Source:` citation in its doc comment (uncertified concentration module). Down from 28 issues; the checker's `Source:` matcher was also repaired to accept citations anywhere in the doc comment rather than only at its start. |
| `scripts/check_markdown_links.py` | Pass | 2026-08-17 | No broken repository-relative targets in active docs; excludes the historical archive, the dependency checkout, and the local `.opencode/` tooling directory (including its vendored `node_modules`). |

## Interpretation

- **Explicit axiom:** an intentional trust boundary declared with Lean's `axiom` command. QA lemmas and derived theorems using these axioms are conditional on them.
- **Admitted proof:** a `sorry` or `admit` accepted by Lean; this is different from an explicit axiom and remains technical debt in public modules. As of this scoreboard there are no `sorry`/`admit` tokens anywhere under `Scaffold/`.
- **QA declaration:** a theorem or lemma under `Scaffold/QA`; the 47 declarations in the certified modules have compiled against the current public API, while the one concentration declaration has not.
- **Default build:** whatever the current Lake targets reach; the umbrella does not reach the concentration subtree, so `lake build` passing must not be read as certifying that subtree.

## Active priorities

1. Repair or quarantine the six `Probability.Concentration` modules (malformed syntax and undefined interfaces) and then certify `Concentration/Matrix_QA.lean`.
2. Replace admitted Cheeger/Weyl/Davis–Kahan statements by proved versions where feasible, or refine their citations (page-level locators pending review).
3. Prove projector idempotence and eigenbasis properties behind `spectralProjector`, which are currently consumed through the admitted perturbation interfaces.
4. Add QA based on risk and composability rather than targeting a cosmetic one-to-one ratio.

## Historical reports

Earlier scoreboards and build reports are preserved under [`research/archive/status/`](../research/archive/status/). They are historical snapshots and may contradict current generated metrics.
