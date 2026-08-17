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
| QA theorem/lemma declarations | 33 |
| `sorry`/`admit` tokens in QA code | 0 |
| Explicit axioms in `Scaffold/Mathlib` | 28 |
| `sorry`/`admit` tokens in `Scaffold/Mathlib` code | 33 |

### QA declarations by domain

| Domain | Declarations |
| --- | ---: |
| Concentration | 1 |
| Perturbation | 2 |
| SpectralGraph | 30 |

### QA files

| File | Declarations | Placeholder tokens |
| --- | ---: | ---: |
| `Scaffold/QA/Concentration/Matrix_QA.lean` | 1 | 0 |
| `Scaffold/QA/Perturbation/DavisKahan_QA.lean` | 1 | 0 |
| `Scaffold/QA/Perturbation/Weyl_QA.lean` | 1 | 0 |
| `Scaffold/QA/SpectralGraph/BasicProperties_QA.lean` | 5 | 0 |
| `Scaffold/QA/SpectralGraph/Basic_QA.lean` | 12 | 0 |
| `Scaffold/QA/SpectralGraph/Cheeger_QA.lean` | 3 | 0 |
| `Scaffold/QA/SpectralGraph/Dynamics_QA.lean` | 3 | 0 |
| `Scaffold/QA/SpectralGraph/Interlacing_QA.lean` | 4 | 0 |
| `Scaffold/QA/SpectralGraph/Variational_QA.lean` | 3 | 0 |
<!-- END GENERATED SOURCE METRICS -->

## Verification record

| Check | Result | Date | Scope and limitation |
| --- | --- | --- | --- |
| `lake build` | Fail | 2026-08-17 | The configured executable target references missing `Main.lean`; the library umbrella also reaches only `Scaffold.Mathlib.Core`. |
| Direct QA module targets | Fail | 2026-08-17 | Spectral and perturbation targets encounter obsolete or misplaced imports before QA can be certified. |
| Public Mathlib-mirror module targets | Fail | 2026-08-17 | Examples include missing Mathlib 4.14 import paths in `Spectral.lean`/`DavisKahan.lean` and imports after declarations in `Weyl.lean`. |
| `scripts/lint_axioms.py` | Pass with 12 warnings | 2026-08-17 | Twelve public axioms are absent from the index. The script treats coverage findings as warnings. |
| `scripts/check_citations.py` | Fail: 28 issues | 2026-08-17 | Every source-detected public axiom lacks the checker’s required doc-comment or `Source:` form. |
| `scripts/check_markdown_links.py` | Pass | 2026-08-17 | No broken repository-relative targets in active docs; excludes the historical archive and dependency checkout. |

## Interpretation

- **Explicit axiom:** an intentional trust boundary declared with Lean’s `axiom` command.
- **Admitted proof:** a `sorry` or `admit` accepted by Lean; this is different from an explicit axiom and remains technical debt in public modules.
- **QA declaration:** a theorem or lemma under `Scaffold/QA`; source counting alone does not show that every module was compiled in the latest run.
- **Default build:** whatever the current Lake targets reach; it must not be described as a full repository verification unless all modules are reachable.

## Active priorities

1. Make the umbrella library or CI compile every intended public and QA module.
2. Remove admitted proofs and constant placeholder definitions from public APIs, or quarantine them with explicit status.
3. Complete citation mappings for every admitted axiom.
4. Add QA based on risk and composability rather than targeting a cosmetic one-to-one ratio.

## Historical reports

Earlier scoreboards and build reports are preserved under [`research/archive/status/`](../research/archive/status/). They are historical snapshots and may contradict current generated metrics.
