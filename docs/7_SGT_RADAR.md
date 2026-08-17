# SGT Coverage Radar

**Status:** Canonical coverage assessment  
**Last reviewed:** August 17, 2026

Two radars, per the operator's axes definition
([`cdx-sgt-radar-axes.md`](../cdx-sgt-radar-axes.md)): a *subject*
radar over the eight spectral-graph-theory neighborhoods, and a separate
*assurance-quality* radar. Scores reflect usable, verified coverage —
what a downstream consumer can import and rely on — not declaration
counts. Scale 0–5; every score cites the declarations that justify it,
with their status (proved / admitted / absent). Re-score at milestone
boundaries against the [QA scoreboard](5_QA_SCOREBOARD.md).

## Subject radar

| # | Axis | Score | Evidence |
|---|------|------:|----------|
| 1 | Graph and Laplacian models | 2.5 | Weighted arbitrary graphs (`WAdj`), combinatorial Laplacian with symmetry/kernel/Dirichlet/PSD **proved**; normalized Laplacian both regular (`Cheeger.regularNormalizedLaplacian`) and general/irregular (`Normalized.normalizedLaplacian`, congruence + similarity **proved**). Absent: directed graphs, signed-graph theory, `SimpleGraph` adapters. |
| 2 | Spectral linear algebra | 3.5 | Sorted spectrum `evals` + monotonicity **proved**; eigenbasis orthonormality/completeness and projector algebra (idempotence, extremes, transport) **proved**; interlacing **admitted** (`eigen_interlacing_principal_submatrix`); Weyl **admitted** with gap stability **proved from it**; Davis–Kahan **admitted** with a **derived** two-point wrapper. |
| 3 | Variational and functional methods | 2.5 | `quadForm`/Dirichlet identity and PSD **proved**; `rayleigh` defined; λ₂ variational characterization **admitted** (`lambda2_variational`). Absent: Poincaré, log-Sobolev, generic min–max. |
| 4 | Cuts, expansion, clustering | 2.5 | `vol`/`boundary`/`conductance`/`cheegerConstant` with nonnegativity, GLB, and full cut duality (**proved**, run 10); Cheeger bounds **admitted**, regular graphs only. Absent: multiway expansion, spectral partitioning driver. |
| 5 | Random walks and diffusion | 2.5 | Regular and irregular transition matrices with row-stochasticity **proved**; walk↔normalized similarity and both Laplacian bridges **proved**. Absent: mixing-time statements, heat kernels, reversibility; walk-spectrum transfer is the named Mathlib gap. |
| 6 | Combinatorial and electrical structure | 0.5 | Only Laplacian basics touch this axis. Absent: effective resistance, spanning-tree enumeration (Matrix–Tree), Kirchhoff identities. |
| 7 | Perturbation, randomness, algorithms | 3.0 | Weyl/Davis–Kahan **admitted** with the **derived** two-endpoint drift chain; scalar + matrix concentration **admitted** with the **derived** event-stream tail. Absent: random-graph models, numerical/spectral algorithm drivers. |
| 8 | Adjacent systems interfaces | 1.0 | Dynamics exist only as the retained compatibility example (`Derived.{EventStream,ProjectorDrift}`, conditional on three axioms; per-step axiom deprecated). Thermodynamics/statistical mechanics gated, absent. |

**Weakest axes:** 6 (combinatorial/electrical — entirely absent) and 8
(adjacent systems — deliberately gated). Axis 4's admitted half and axis
5's transfer gap are the nearest load-bearing completions.

## Assurance radar

| Axis | Score | Evidence |
|------|------:|----------|
| Proved depth | 3.5 | Interfaces and algebra are hard crust (projector algebra, cut duality, all Laplacian/normalized/walk bridges, gap stability); the inequality *engines* (interlacing, variational, Cheeger, Weyl, DK, concentration) remain admitted with documented statement differences. |
| Axiom minimization | 3.5 | 18 explicit axioms, all cited and indexed; `spectral_gap_stability`, `hoeffding_iid`, `bernstein_iid` converted from admitted to proved; `spectral_persistence` deprecated with migration note (count drops at its removal release). Net trend 26 → 19 → 18. |
| Mathlib interoperability | 3.5 | Native `Matrix`, `IsSymm`, `Matrix.L2OpNorm`, `Matrix.PosSemidef`, `ProbabilityTheory.IndepFun`, `OrthonormalBasis`; documented deviations: matrix-first graph representation (no `SimpleGraph` adapters yet) and `MatrixMDS` pending a Mathlib filtration API. |
| QA | 3.0 | 107 declarations across 16 modules, zero `sorry`/`admit`, all modules individually compiled; coverage skews to degenerate/zero instantiations — no property-based or negative (falsification) QA yet. |
| Citation fidelity | 3.5 | Every axiom carries author/title/locator + statement-differences; false Chung provenance corrected against git history; Horn–Johnson/Chung page-level locators explicitly unconfirmed rather than invented. |
| Downstream reuse | 3.5 | The derived layer consumes the concentration and perturbation bridges end-to-end; `GraphTheory.Stationary` (2026-08-17, runs 2–3) consumes both interface modules: `Normalized` (kernel `L_sym √deg = 0`, stationary degree measure) and `RandomWalk` (conservation of mass `L_rw 1 = 0`, regular case). Scores raised 2.5 → 3.0 → 3.5 with those milestones; remaining gap: `Stationary` is the sole consumer — breadth of reuse, not existence, is now the constraint. |

**Weakest assurance axis:** QA (3.0) — coverage skews to degenerate-case
instantiations; property-based or falsification QA is the next
assurance lever. Downstream reuse improved to 3.5 on 2026-08-17
(`Stationary` now consumes both walk/normalized interface modules).

## Re-scoring protocol

1. Regenerate the [QA scoreboard](5_QA_SCOREBOARD.md); scores must cite
   declarations that exist in the current tree.
2. A score may rise only for *usable, verified* coverage: proved
   statements, or admitted statements with QA-exercised interfaces and
   named consumers.
3. Record score changes with the milestone that caused them in
   [AGENT_ACTIVITY.md](AGENT_ACTIVITY.md); do not silently re-score.

## Source provenance

Axes defined by the operator in
[`cdx-sgt-radar-axes.md`](../cdx-sgt-radar-axes.md) (2026-08-17);
scores assessed from repository evidence on the same date.
