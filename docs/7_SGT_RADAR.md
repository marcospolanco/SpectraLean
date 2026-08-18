# SGT Coverage Radar

**Status:** Canonical coverage assessment  
**Last reviewed:** August 18, 2026

This document maintains two radars: a *subject* radar over eight
spectral-graph-theory neighborhoods, and a separate *assurance-quality*
radar. Scores reflect usable, verified coverage — what a downstream consumer
can import and rely on — not declaration counts. Scale 0–5; every score cites
the declarations that justify it, with their status (proved / admitted /
absent). Re-score at milestone boundaries against the
[QA scoreboard](5_QA_SCOREBOARD.md). For *why* a given axis's ceiling sits
where it does, see the [Mathlib Coverage Map](8_MATHLIB_COVERAGE_MAP.md) —
this radar scores what Scaffold built; that document surveys what the
pinned Mathlib itself provides to build from.

## Subject axes

1. **Graph and Laplacian models** — weighted, normalized, directed, signed,
   and graph-native adapters.
2. **Spectral linear algebra** — eigenvalues, eigenspaces, projectors, and
   interlacing.
3. **Variational and functional methods** — Rayleigh/min--max principles,
   Dirichlet forms, Poincaré and log-Sobolev inequalities.
4. **Cuts, expansion, and clustering** — conductance, Cheeger theory,
   multiway expansion, and spectral partitioning.
5. **Random walks and diffusion** — transition operators, mixing, heat
   kernels, Markov structure, and reversibility.
6. **Combinatorial and electrical structure** — effective resistance,
   spanning trees, and Kirchhoff identities.
7. **Perturbation, randomness, and algorithms** — matrix concentration,
   random graphs, stability, and numerical/spectral algorithms.
8. **Adjacent systems interfaces** — dynamical-systems and
   thermodynamics/statistical-mechanics connections.

The assurance radar remains separate from subject coverage. Its axes are
proved depth, axiom minimization, Mathlib interoperability, QA, citation
fidelity, and downstream reuse.

## Subject radar

| # | Axis | Score | Evidence |
|---|------|------:|----------|
| 1 | Graph and Laplacian models | 3.5 | Weighted arbitrary graphs (`WAdj`), combinatorial Laplacian with symmetry/kernel/Dirichlet/PSD **proved**; normalized Laplacian both regular (`Cheeger.regularNormalizedLaplacian`) and general/irregular (`Normalized.normalizedLaplacian`, congruence + similarity **proved**); both `SimpleGraph` adapter directions landed — `supportGraph : WAdj → SimpleGraph` (2026-08-18, consumed by the kernel characterization) and `SimpleGraph.toWAdj` (2026-08-18, `GraphTheory.SimpleGraphAdapter`, with the proved agreement family `laplacian G.toWAdj = G.lapMatrix ℝ`, degree/volume/boundary agreement, handshake, and the roundtrip `supportGraph (toWAdj G) = G`). Absent: directed graphs, signed-graph theory. |
| 2 | Spectral linear algebra | 3.5 | Sorted spectrum `evals` + monotonicity + `evals_mem_eigvalOf` (**proved**); `secondEval` (matrix-facing λ₂ API) and the trace/Rayleigh pinning tools `eigvalOf_sum_eq_trace`, `eigvalOf_le_of_quadForm_nonpos` **proved** (2026-08-18); eigenbasis orthonormality/completeness and projector algebra **proved**; interlacing **admitted** (`eigen_interlacing_principal_submatrix`); Weyl **admitted** with gap stability **proved from it**; Davis–Kahan **admitted** with a **derived** two-point wrapper. |
| 3 | Variational and functional methods | 3.5 | `quadForm`/Dirichlet identity and PSD **proved**; `rayleigh` defined; normalized↔combinatorial transfer **proved** (2026-08-17, `VariationalTransfer`: congruence lemma, degree-weighted Rayleigh quotient `rayleigh L_sym (√D y) = (yᵀ L y)/∑ deg·y²`, `normalizedLaplacian_psd`); **λ₂ variational characterization (Courant–Fischer) now proved** (2026-08-18, `lambda2_variational`: `λ₂ = sInf` of the Rayleigh quotient over nonzero vectors ⊥ `onesVec`, for symmetric nonnegative weights — retired from axiom, whose symmetry-only shape was false and is refuted in QA; matrix-world proof through eigenbasis expansion, Parseval, the spectral resolution of `quadForm`, and two sorted-multiset multiplicity pins; the semidefinite Cauchy–Schwarz `laplacian_cauchy_schwarz` is also proved). Re-scored 3.0 → 3.5 with this milestone (the row's named admitted gap closed by a proved theorem). Absent: Poincaré, log-Sobolev, generic min–max. |
| 4 | Cuts, expansion, clustering | 3.0 | `vol`/`boundary`/`conductance`/`cheegerConstant` with nonnegativity, GLB, and full cut duality (**proved**, run 10); **the Cheeger *upper* bound (easy direction, `λ₂(L_sym) ≤ 2φ`) is proved** (2026-08-18, `cheeger_upper_bound` retired from axiom) — the volume-centered cut-indicator interface (`cutTestVector`: orthogonality, the general weighted-graph cut-energy identity `xᵀLx = boundary·vol V²`, the norm identity, and the Rayleigh value `boundary·vol V/(vol S·vol Sᶜ)`), instantiated in QA on `K₂` (bound attained: `λ₂ = 2φ = 2`) and on `C₄` (`λ₂ ≤ 1` through the exhaustively computed conductance `1/2`); the Cheeger *lower* bound (hard direction) remains **admitted** (regular graphs; spectral side restated 2026-08-18 at the source-faithful `secondEval (L_sym)` shape after QA refuted the previous `lambda2`-composed side, and pinned to the classical value `2` on `K₂`). Absent: multiway expansion, spectral partitioning driver, the irregular Cheeger statement shape. Re-scored 2.5 → 3.0 with this milestone (the axis's first inequality engine proved rather than admitted). |
| 5 | Random walks and diffusion | 2.5 | Regular and irregular transition matrices with row-stochasticity **proved**; walk↔normalized similarity and both Laplacian bridges **proved**. Absent: mixing-time statements, heat kernels, reversibility; walk-spectrum transfer is the named Mathlib gap. |
| 6 | Combinatorial and electrical structure | 3.0 | The connectivity/kernel hinge is **proved** (2026-08-18, proposal `electrical-structure-crust.md` step 2 after the re-sequencing): for connected symmetric nonnegative weights, `ker (laplacian A) = span ℝ {onesVec}` (`laplacian_kernel_eq_span_onesVec`, built on `supportGraph` + `SimpleGraph.Walk` induction), with connected and disconnected QA witnesses. **Component structure is complete for weighted graphs** (2026-08-18, proposal step 3): the component-form kernel characterization `L *ᵥ f = 0 ↔ f` constant on each support-graph component (`laplacian_mulVec_eq_zero_iff_forall_reachable`), the kernel-equality bridge `ker (laplacian A) = ker ((supportGraph A).lapMatrix ℝ)`, kernel dimension = component count, and the component-indicator basis (Mathlib's `lapMatrix_ker_basis`/rank theorem inherited through the bridge; QA computes the count to `2` and the basis to `![1,1,0,0]`/`![0,0,1,1]` on the disconnected fixture). **The potential equation is completely characterized on connected graphs** (2026-08-18, proposal step 4): every zero-sum demand is solvable (`exists_laplacian_mulVec_eq_of_sum_eq_zero`, constructive eigenbasis witness `f = ∑_{λᵢ ≠ 0} (vᵢ ⬝ᵥ b/λᵢ)•vᵢ` — the load-bearing consumer of the proved eigenbasis algebra and the step-2 kernel theorem), the unit demand `e u − e v` is solvable (`exists_laplacian_mulVec_eq_single_sub_single`), and the reciprocity identity `w ⬝ᵥ (L *ᵥ f) = (L *ᵥ w) ⬝ᵥ f` (`laplacian_dotProduct_mulVec`) certifies in proved QA form that non-zero-sum demands are unsolvable and that zero-sum does not suffice without connectivity. **Effective resistance is a defined, well-determined quantity** (2026-08-18, proposal step 5, `GraphTheory.Electrical`; Mathlib surveyed: no resistance declaration, no pseudoinverse): `IsEffectiveResistance A u v r` by the potential equation, existence from step 4, uniqueness of `r` at reachability-pair strength, the total function `effectiveResistance` with proved agreement theorems and an honestly QA-witnessed junk fallback, the energy identity at solution and function level (`quadForm L f = f u − f v`; `R = energy`), nonnegativity from PSD, hypothesis-free relation symmetry, and `R u u = 0` unconditional; QA computes `R = 1` on the unit edge, `R = 2` on the 3-vertex path (series edges add), and cross-checks the energy identity against an independently computed energy. **The one-sided Dirichlet bound is proved** (2026-08-18, proposal step 6, program complete): `(f u − f v)² / quadForm L f ≤ R u v` for every test potential of positive energy (`effectiveResistance_ge_sq_div_quadForm`), via the semidefinite Cauchy–Schwarz `laplacian_cauchy_schwarz` (no connectivity hypothesis; the pin's only C–S is the definite inner-product one — polarization route recorded); QA attains equality at both harmonic potentials (`1/1 = 1`, `4/2 = 2`), shows strictness at a non-harmonic potential, refutes the reverse inequality numerically, and witnesses the energy guard. Absent: full Rayleigh monotonicity (needs the attained-supremum Dirichlet principle), the resistance metric's triangle inequality and definiteness residual, spanning-tree enumeration (Matrix–Tree), Kirchhoff identities. |
| 7 | Perturbation, randomness, algorithms | 3.0 | Weyl/Davis–Kahan **admitted** with the **derived** two-endpoint drift chain; scalar + matrix concentration **admitted** with the **derived** event-stream tail. Absent: random-graph models, numerical/spectral algorithm drivers. |
| 8 | Adjacent systems interfaces | 1.0 | Dynamics exist only as the retained compatibility example (`Derived.{EventStream,ProjectorDrift}`, conditional on three axioms; per-step axiom deprecated). Thermodynamics/statistical mechanics gated, absent. |

**Weakest axes:** 6 (combinatorial/electrical — the connectivity
hinge, the full weighted component structure, the solvability
characterization, effective resistance as a well-determined quantity
with its energy identity, and the one-sided Dirichlet bound are
proved, but full Rayleigh monotonicity, the resistance metric, and
Matrix–Tree/Kirchhoff remain absent) and 8 (adjacent systems —
deliberately gated). Axis 4's admitted *hard* direction and axis
5's transfer gap are the nearest load-bearing completions.

## Assurance radar

| Axis | Score | Evidence |
|------|------:|----------|
| Proved depth | 3.5 | Interfaces and algebra are hard crust (projector algebra, cut duality, all Laplacian/normalized/walk bridges, gap stability, electrical structure through the one-sided Dirichlet bound); the *variational* engine is proved (`lambda2_variational` + its general-operator form `secondEval_variational`, 2026-08-18) and the *Cheeger easy direction* is proved on top of it (`cheeger_upper_bound`, retired the same day), so the remaining admitted engines are interlacing, the Cheeger hard direction, Weyl, DK, concentration — each with documented statement differences. |
| Axiom minimization | 4.0 | 16 explicit axioms, all cited and indexed; `spectral_gap_stability`, `hoeffding_iid`, `bernstein_iid` converted from admitted to proved; **`lambda2_variational` retired from axiom to proved theorem (2026-08-18) — the first axiom removed by proof rather than deprecation — and `cheeger_upper_bound` retired the same way one milestone later** (the Cheeger easy direction, proved from the generalized `secondEval_variational`; both false pre-repair shapes refuted in QA); `spectral_persistence` deprecated with migration note (count drops at its removal release). Net trend 26 → 19 → 18 → 17 → 16. Score 4.0 (re-scored 3.5 → 4.0 with the λ₂ retirement; the Cheeger retirement continues the trend without crossing a new threshold). |
| Mathlib interoperability | 4.5 | Native `Matrix`, `IsSymm`, `Matrix.L2OpNorm`, `Matrix.PosSemidef`, `ProbabilityTheory.IndepFun`, `OrthonormalBasis`; the matrix-first representation is bridged in **both** directions and mutually consistently — `supportGraph : WAdj → SimpleGraph` (2026-08-18, consumed by the proved kernel characterization) and `SimpleGraph.toWAdj` (2026-08-18, `GraphTheory.SimpleGraphAdapter`), tied by the proved roundtrip `supportGraph (toWAdj G) = G`; through the agreement `laplacian G.toWAdj = G.lapMatrix ℝ`, Mathlib's unweighted kernel/reachable and component-count results are transferred onto the Scaffold side (`laplacian_toWAdj_mulVec_eq_zero_iff_reachable`, `finrank_ker_laplacian_toWAdj`), and every center theorem becomes callable on Mathlib graphs. Remaining documented deviation: `MatrixMDS` pending a Mathlib filtration API. |
| QA | 4.0 | 378 declarations across 24 modules, zero `sorry`/`admit`, all modules individually compiled; coverage no longer degenerate-skewed (2026-08-17, `Exhaustive_QA`): exhaustive kernel-checked sweeps over **all** cuts of the 3-vertex path and the 4-cycle, negative witnesses, and walk row sums computed independently of their theorem. **Computational eigenvalue checks now exist (2026-08-18, `Cheeger_QA`)**: the corrected Cheeger spectral side is pinned to its classical value on the two-vertex edge (`edge_normLap_secondEval_eq_two_QA`: trace + determinant + sortedness, no axiom), and the pre-repair axiom shape is **refuted in proved form** (`old_cheeger_lower_bound_refuted_QA`: the old side evaluated to `1/2 ≤ 0` on `K₂`) — the QA program caught a materially false admitted statement. **Load-bearingness witnesses for hypothesis structure (2026-08-18, `Connectivity_QA`)**: the disconnected `Fin 4` fixture shows the kernel-characterization conclusion failing when connectivity is dropped (component indicator in the kernel, not constant; support graph proved not connected). **Adapter agreement computed, not rewritten (2026-08-18, `SimpleGraphAdapter_QA`)**: weights, degrees, both Laplacian sides, boundary, handshake, and kernel membership evaluated against hand-expected numbers, plus a disconnected witness where the kernel is proved ≠ `span {onesVec}` through the adapter. **Cross-representation coherence computed (2026-08-18, `KernelBridge_QA`)**: on the connected path, the bridge's dimension count and the connected span theorem hold simultaneously (dimension `1`, basis vector constantly `1`); on the disconnected fixture the component count is computed to `2` **independently of the transferred theorem** (block classification + `Nat.card_eq_two_iff`), the transferred dimension reads `2`, and the two basis vectors are computed to the component indicators `![1,1,0,0]`/`![0,0,1,1]`. **Unsolvability certified, not just solvability (2026-08-18, `PotentialSolvability_QA`)**: potentials are computed to hand values on the edge and the 3-path (`![1,0]` carrying `L *ᵥ ![1,0] = e₀ − e₁`, `![1,0,−1]` fixed by the path Laplacian), and the negative witnesses use the reciprocity identity with kernel certificates (all-ones on the connected edge; component indicator on the disconnected fixture) to prove *in Lean* that a non-zero-sum demand and a cross-component zero-sum demand have no solution — both hypotheses of the solvability theorem are shown load-bearing. **A second materially false admitted statement refuted in proved form (2026-08-18, `Variational_QA`)**: the pre-repair `lambda2_variational` shape (symmetry hypotheses only) is refuted on a negative-weight two-vertex graph (`λ₂ = 0` while the constraint set's infimum is `-2`, every element computed parametrically), and the proved theorem is instantiated exactly on `K₂` — `λ₂ = 2` computed twice, once from trace/determinant/sortedness and once *through* the theorem from the independently computed Rayleigh side — plus the disconnected instantiation `λ₂ = 0` and the path bound `λ₂(P₃) ≤ 1`. **The proved Cheeger upper bound exercised on computed data (2026-08-18, `Cheeger_QA`)**: the cut test vector pinned to `![1,-1]` on `K₂`, its Rayleigh value computed to `2` (exactly the pinned `λ₂(L_sym)` — the test-vector bound attained), the theorem itself instantiated on `K₂` as `λ₂ = 2φ` from independently computed values, and on `C₄` as `λ₂ ≤ 1` through the exhaustively computed adjacent-pair conductance `1/2`, whose test-vector Rayleigh value computes to exactly `1`. Remaining gap: no parametric (randomized) property QA; eigenvalue pinning beyond two-point fixtures is limited to the transferred `K₂` value and the path bound. |
| Citation fidelity | 3.5 | Every axiom carries author/title/locator + statement-differences; false Chung provenance corrected against git history; Horn–Johnson/Chung page-level locators explicitly unconfirmed rather than invented; the Cheeger axioms' Lean statements now match their cited source after the 2026-08-18 shape repair. |
| Downstream reuse | 4.0 | The derived layer consumes the concentration and perturbation bridges end-to-end; the walk/normalized interfaces now have **two** consuming modules: `GraphTheory.Stationary` (2026-08-17, runs 2–3: kernel `L_sym √deg = 0`, stationary degree measure, conservation of mass) and `GraphTheory.VariationalTransfer` (2026-08-17, run 2: quadratic-form/Rayleigh transfer through the congruence, `normalizedLaplacian_psd`). Scores raised 2.5 → 3.0 → 3.5 → 4.0 with those milestones; the proved `cheeger_upper_bound` (2026-08-18) additionally consumes the variational engine (`secondEval_variational`/`secondEval_le_rayleigh`) as the first axiom-retirement proof built on a locally proved engine; remaining gap: the remaining admitted axioms (interlacing, Cheeger hard direction, Weyl, DK, concentration) have derived consumers but no proof-level consumer yet. |

**Weakest assurance axes:** three axes sit at 3.5 (proved depth, axiom
minimization, citation fidelity) — the
inequality engines remain admitted by design. QA was re-scored
3.0 → 3.5 on 2026-08-17 (`Exhaustive_QA`) and 3.5 → 4.0 on
2026-08-18 (`Cheeger_QA`: the tree's first computational eigenvalue
checks plus a proved refutation of the pre-repair Cheeger axiom shape —
the QA program caught a materially false admitted statement);
its remaining gap is parametric property QA and eigenvalue pinning
beyond two-point fixtures. Mathlib interoperability was re-scored
3.5 → 4.0 on 2026-08-18 (`supportGraph`: the first
matrix-first ↔ `SimpleGraph` bridge, consumed by the proved kernel
characterization) and 4.0 → 4.5 on 2026-08-18
(`SimpleGraphAdapter`: the reverse direction delivered, tied by the
proved roundtrip, with Mathlib's kernel/component results transferred
onto the Scaffold side and the center callable on Mathlib graphs).
Subject axis 1 (models) was re-scored 3.0 → 3.5 with the same
milestone (both adapter directions landed with proved agreement).
Subject axis 6 (combinatorial/electrical) was re-scored 1.0 → 1.5 on
2026-08-18 (proposal step 3: the kernel-equality bridge plus the
inherited component count and indicator basis — weighted component
structure is now complete) and 1.5 → 2.0 on 2026-08-18 (proposal
step 4: the potential equation is now *completely characterized* on
connected graphs — zero-sum demands are solvable by a proved
constructive witness, and QA proves the converse direction through
kernel-certificate unsolvability in both hypothesis regimes; no
electrical quantity is defined yet, which keeps the axis from rising
further until step 5's `effectiveResistance` lands) and 2.0 → 2.5 on
2026-08-18 (proposal step 5: effective resistance is now a *defined,
well-determined quantity* — the potential-equation relation with
existence, reachability-strength uniqueness, a total function with
proved agreement and an honestly witnessed junk fallback, the energy
identity at both levels, nonnegativity, symmetry, and `R u u = 0`,
QA-pinned to the classical values `1` (edge) and `2` (path); the axis
stays below 3.0 because the variational Dirichlet bound, Rayleigh
monotonicity, the resistance-metric inequality, and Matrix–Tree/
Kirchhoff are still absent). It was re-scored 2.5 → 3.0 on
2026-08-18 (proposal step 6, the program's final step: the one-sided
Dirichlet bound — every test potential of positive energy lower-bounds
the resistance, the first *variational/electrical inequality* on the
axis, proved through a reusable semidefinite Cauchy–Schwarz with QA
attainment, strictness, reverse refutation, and guard witnesses; the
axis stays below 3.5 because full Rayleigh monotonicity, the
resistance metric, and Matrix–Tree/Kirchhoff are still absent).
Downstream reuse was re-scored 3.5 → 4.0 on
2026-08-17 (`VariationalTransfer`, the second consuming module); the
remaining gap is consumption by an admitted-axiom consumer.

## Re-scoring protocol

1. Regenerate the [QA scoreboard](5_QA_SCOREBOARD.md); scores must cite
   declarations that exist in the current tree.
2. A score may rise only for *usable, verified* coverage: proved
   statements, or admitted statements with QA-exercised interfaces and
   named consumers.
3. Record score changes with the milestone that caused them in
   [AGENT_ACTIVITY.md](AGENT_ACTIVITY.md); do not silently re-score.

## Source provenance

Axes and scores are maintained from repository evidence at the stated review
date.
