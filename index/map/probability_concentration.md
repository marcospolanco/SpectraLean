# Probability Concentration Inequalities

This index maps Lean modules and axioms for concentration inequalities by topic area.

## Scalar Concentration

### Subgaussian Random Variables

**Module**: `Scaffold.Mathlib.Probability.Concentration.Scalar.Subgaussian`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `subgaussianNorm` | definition | Ψ₂ norm via the MGF characterization; junk behavior documented (empty set → 0 via `Real.sInf_empty`; non-integrable MGFs → junk-zero integrals make the set *full*, also 0) | Vershynin Def 2.5.1 / Prop 2.5.2 |
| `subgaussianNorm_nonneg` | proved | `0 ≤ subgaussianNorm X μ` | — |
| `hoeffding_lemma` | axiom (**repaired 2026-08-28**; the pre-repair `subgaussianNorm ≤ a` shape with no measure constraint was materially false in two ways — the constant `1` refuted at the fair-coin Rademacher fixture, and *every* constant `≤ 4` refuted at the mass-19/10 rescaling, both with genuinely-satisfied hypotheses; see `proposals/audit-scalar-concentration-integrability-hazard.md`) | Bounded and centered on a **probability measure** ⇒ `subgaussianNorm ≤ √6·a` | Vershynin Lem 2.6.2 (λ-form; the `√6` derived via two-sided tail + layer-cake integration) |
| `subgaussian_tail_bound` | **proved** (2026-08-22; retired from axiom with repaired hypotheses `0 < K`, MGF integrable, MGF integral ≤ 2 — the old `subgaussianNorm ≤ K` shape was materially false via `sInf ∅ = 0` and junk-zero integrals, refuted in QA at `3 • δ₀`) | μ{\|X\| ≥ t} ≤ 2exp(−t²/(2K²)) | Vershynin Prop 2.5.2 (ii) |

Formerly admitted subgaussian statements without a current consumer
(`subgaussian_moment_growth`, `subgaussian_linear_combination`,
`subgaussian_centering`, `subgaussian_sum_bound`) were removed from the
axiom boundary in the 2026-08-17 concentration repair.

### Hoeffding's Inequality

**Module**: `Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `hoeffding_inequality` | axiom (audited safe 2026-08-28: `IsProbabilityMeasure` + bounded + measurable rule out the junk-integral hazard; **repaired 2026-08-29**: the independence clause, pairwise `IndepFun` in the pre-repair shape, is `iIndepFun` — mutual independence — matching the cited source; the old shape refuted by the Walsh-character fixture, Errata §6) | Sums of bounded independent variables | Vershynin Thm 2.2.2 |
| `integrable_of_bounded_measurable` | proved | The audit's safety lemma: measurable + `|X| ≤ a` + probability measure ⇒ `Integrable X` | — |
| `hoeffding_iid` | proved | Uniform-bound specialization | Vershynin Cor 2.2.3 |
| `hoeffding_empirical` | axiom (**repaired 2026-08-29**: pairwise → `iIndepFun`, Errata §6) | Empirical averages of [0,1] variables | Boucheron-Lugosi-Massart Thm 2.8 |

### Bernstein's Inequality

**Module**: `Scaffold.Mathlib.Probability.Concentration.Scalar.Bernstein`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `bernstein_inequality` | axiom (audited safe 2026-08-28: same guard set as `hoeffding_inequality`; **repaired 2026-08-29**: pairwise → `iIndepFun`, Errata §6) | Tail bound with variance | Vershynin Thm 2.8.1 |
| `bernstein_bounded_variance` | axiom (audited safe 2026-08-28; **repaired 2026-08-29**: pairwise → `iIndepFun`, Errata §6) | Bounded variance form | Wainwright Thm 2.15 |
| `integrable_sq_sub_mean` | proved | The audit's centered-square safety lemma: both Bernstein axioms' variance statistics are honest integrals | — |
| `bernstein_iid` | proved | Common-variance specialization | Vershynin Cor 2.8.3 |

## Sampling Spaces

### Bernoulli Product Space

**Module**: `Scaffold.Mathlib.Probability.BernoulliProduct` (delivered
2026-08-27, `proposals/spectral-sparsification-via-leverage-scores.md`
Step 1 Slice 1; all proved, zero axioms — the shelf's first concrete
probability space, and the i.i.d.-sampling prerequisite the
empirical-stationary-distribution proposal names)

| Declaration | Kind | Description |
|-------------|------|-------------|
| `bern` | definition | Per-coordinate Bernoulli mass; junk outside `[0,1]` via the `ofReal` clamp |
| `jointMass` | definition | The joint product mass |
| `bernPMF` | definition | The product-Bernoulli PMF on `ι → Bool`; `[0,1]` hypotheses load-bearing (fenced in QA) |
| `sum_coord_mul` | proved | The one-coordinate marginal (the product structure's arithmetic core) |
| `sum_coord2_mul` | proved | The two-coordinate marginal (independence's arithmetic core) |
| `indepFun_coord` | proved | Pairwise `IndepFun` of coordinate projections — the two-point consequence of the mutual engine (kept as the refutation records' interface) |
| `toMeasure_cyl_inter` | proved | Finite coordinate-cylinder intersections (2026-08-29) — the engine for mutual independence |
| `iIndepFun_coord` | proved | **Mutual independence of the coordinate projections** (2026-08-29) — the repaired `h_indep` clause shape |
| `iIndepFun_of_injective` | proved | Mutual independence inherited by injective reindexing (2026-08-29, generic) |
| `iIndepFun_coord_apply` | proved | The mutual clause at an arbitrary measurable codomain, single-coordinate factors (2026-08-29) — the scalar designs' `h_indep` |
| `iIndepFun_coord_matrix` | proved | The mutual clause at the matrix codomain (2026-08-29) — the sparsification and edge-perturbation designs' `h_indep` |
| `toMeasure_cyl` | proved | Coordinate-cylinder measures are Bernoulli masses |
| `integral_delta` | proved | `∫ δ_e ∂μ = p e` — the scalar `h_mean` core |
| `stronglyMeasurable_coord_matrix` | proved | The `h_meas` clause at the L2OpNorm topology (topology-only route) |
| `measurable_coord_matrix` | proved | The `h_meas` clause at the shelf's matrix product σ-algebra |
| `indepFun_coord_matrix` | proved | The `h_indep` clause at the matrix codomain |
| `integral_coord_smul` | proved | `∫ (δ_e) • M = p e • M` — the matrix centering building block |
| `integral_coord_center_smul` | proved | `∫ ((δ_e / p e) − 1) • M = 0` at `p e ≠ 0` — the `h_mean` clause shape |

### IID Product Space (V-valued)

**Module**: `Scaffold.Mathlib.Probability.IIDProduct`

| Declaration | Kind | Description |
|-------------|------|-------------|
| `iidMass` / `iidPMF` | definition | The i.i.d. product PMF on `ι → V` at a normalized factor `q : V → ℝ`; the mass hypotheses load-bearing (fenced in QA) |
| `sum_mass_eq_one` / `sum_iidMass_eq_one` | proved | The factor and joint masses sum to one |
| `sum_coord_mul` / `sum_coord2_mul` | proved | The one-/two-coordinate factorized marginals (independence's arithmetic core) |
| `measurable_coord` | proved | Measurability of coordinate projections at the product σ-algebra |
| `toMeasure_cyl` | proved | Coordinate-cylinder measures are factor masses |
| `indepFun_coord` | proved | Pairwise `IndepFun` of the V-valued projections (the two-point consequence of the mutual engine) |
| `measurable_indicator_coord` | proved | The `h_meas` clause shape of `hoeffding_empirical` at coordinate indicators |
| `integral_indicator` | proved | `∫ 1_{ω e = i} ∂μ = q i` — the mean-clause constant the empirical form's centering collapses to |
| `indepFun_indicator_coord` | proved | The pairwise clause at coordinate indicators (the two-point consequence; refutation records' interface) |
| `iIndepFun_coord` / `iIndepFun_coord_apply` / `iIndepFun_indicator_coord` | proved | The `iidPMF` mutual-independence engine (2026-08-29) — `iIndepFun_indicator_coord` is the repaired `h_indep` clause shape of `hoeffding_empirical` at this sampling space |

## Matrix Concentration

All statements are over the spectral norm (`Matrix.L2OpNorm`), the
semidefinite order (`Matrix.PosSemidef`), and the product σ-algebra on
matrices defined in `Matrix/Basic.lean`.

### Matrix Hoeffding

**Module**: `Scaffold.Mathlib.Probability.Concentration.Matrix.Hoeffding`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `matrix_hoeffding` | axiom | Mutually independent Hermitian, PSD-dominated squares; `[Nonempty V]` guard (repaired 2026-08-28 — the guard-free shape was inconsistent at `card V = 0`, `t = 0`; **repaired 2026-08-29**: pairwise → `iIndepFun`, Errata §6) | Tropp Thm 1.4 |

### Matrix Bernstein

**Module**: `Scaffold.Mathlib.Probability.Concentration.Matrix.Bernstein`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `matrix_bernstein` | axiom | Mutually independent centered uniformly bounded; `[Nonempty V]` guard (repaired 2026-08-28 — same degenerate-dimension corner; **repaired 2026-08-29**: pairwise → `iIndepFun`, Errata §6) | Tropp Thm 1.1 |

### Matrix Azuma–Hoeffding

**Module**: `Scaffold.Mathlib.Probability.Concentration.Matrix.Azuma`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `mdsFiltration` | definition | Natural past σ-algebra of a matrix sequence | — |
| `MatrixMDS` | definition | Martingale-difference structure with uniform bound (**repaired 2026-08-29** — the `adapted` field was content-free and nothing forced ambient strong measurability, making the `cond_mean_zero` integrals junk zeros; replaced by `measurable : ∀ k, StronglyMeasurable (X k)`, Errata §7) | — |
| `matrix_azuma_hoeffding` | axiom | Dependent-event tail bound `2d exp(-t²/(8mR²))`; `[Nonempty V]` guard (repaired 2026-08-28 — same corner; **hypothesis repair 2026-08-29** via the `MatrixMDS` field, Errata §7) | Tropp Thm 7.1 |

### Derived consumers

**Module**: `Scaffold.Derived.EdgePerturbationTail` (derived layer, not axioms — 2026-08-28; the irregular normalized window added 2026-08-29)

`matrix_hoeffding`'s first theorem consumer, on the centered Bernoulli
edge-perturbation design of `GraphTheory.EdgePerturbation` (every axiom
clause proved hard crust; the design is sign-free — no hypothesis on the
weight matrix, the only load-bearing clause hypothesis `p ∈ [0, 1]`).

| Declaration | Kind | Description | Consumes |
|-------------|------|-------------|----------|
| `matrix_hoeffding_quadForm` | theorem (axiom-conditional) | Fixed-nonzero-vector quadratic-form pullback of the axiom (`x ≠ 0` load-bearing: at `x = 0` the event is all of `Ω`) | `matrix_hoeffding` |
| `edgePerturbation_norm_tail` | theorem (axiom-conditional) | `μ {‖∑_e (δ_e − p_e) • L_e‖ ≥ t} ≤ 2 d exp(−t²/(2 ‖∑_e L_e²‖))` | `matrix_hoeffding` |
| `edgePerturbation_quadForm_tail` | theorem (axiom-conditional) | The same bound at `t (x ⬝ᵥ x) ≤ |xᵀ S(ω) x|` for a fixed nonzero `x` | `matrix_hoeffding` |
| `edgePerturbation_eval_tail` | theorem (axiom-conditional) | The eigenvalue-level packaging (2026-08-28, the follow-on delivery): `μ {t ≤ |λᵢ(L(A+E_ω)) − λᵢ(L A)|} ≤ 2 d exp(−t²/(2 ‖∑_e L_e²‖))` at every sorted index — the norm tail joined to the *proved* Weyl inequality | `matrix_hoeffding` |
| `edgePerturbation_eval_lower_tail` | theorem (axiom-conditional) | The one-sided gap-survival form `μ {λᵢ(L(A+E_ω)) ≤ λᵢ(L A) − t} ≤ …` | `matrix_hoeffding` |
| `edgePerturbation_lambda2_lower_tail` | theorem (axiom-conditional) | The λ₂ spelling at the `lambda2` interface (`2 ≤ card V`) — the Fiedler-facing robustness statement | `matrix_hoeffding` |
| `edgePerturbation_quadForm_uniform_tail` | theorem (axiom-conditional) | The uniform/existential-x packaging: outside the bound's failure set, `|xᵀ L(E_ω) x| < t (x ⬝ᵥ x)` for *every* nonzero `x` simultaneously (`x ≠ 0` guard load-bearing — the un-guarded event is all of `Ω`) | `matrix_hoeffding` |
| `edgePerturbation_lambda2_cheeger_floor` | theorem (axiom-conditional) | The Cheeger-driven connectivity floor (2026-08-28, the Cheeger-window follow-on): `μ {λ₂(L(A+E_ω)) ≤ d·φ(A)²/2 − t} ≤ 2 d exp(−t²/(2 ‖∑_e L_e²‖))` on `d`-regular input — the proved `cheeger_lower_bound_laplacian` composed with the λ₂ lower tail by `measure_mono` | `matrix_hoeffding` |
| `edgePerturbation_connectivity_bracket` | theorem (axiom-conditional) | The two-sided window (2026-08-28): `μ {λ₂(L(A+E_ω)) ≤ d·φ²/2 − t ∨ 2dφ + t ≤ λ₂(L(A+E_ω))} ≤ 2 d exp(…)` at the same constant as the one-sided tail — both Cheeger directions (the engine pair) load-bearing on the inclusion into the two-sided eigenvalue tail | `matrix_hoeffding` |
| `edgePerturbation_degree_tail` | theorem (axiom-conditional) | **`hoeffding_inequality`'s first theorem consumer** (2026-08-29, the degree-concentration delivery): `μ {t ≤ \|deg G_ω v − deg A v\|} ≤ 2 exp(−t²/(2 S_v))` at `S_v = ∑ₑ w_v(e)²` — the per-vertex degree-deviation tail, the complementary concentration the window family's admissibility story was missing (the λ₂/norm tails carry zero degree information, `L(E_ω)·1 = 0` identically) | `hoeffding_inequality` |
| `edgePerturbation_degree_tail_all` | theorem (axiom-conditional) | The all-vertices union bound (2026-08-29), stated at the exact per-vertex sum — the first step toward *deriving* the admissibility window rather than hypothesizing it (the collapse to a uniform exponent needs per-vertex `0 < S_v`, demonstrated numerically in QA) | `hoeffding_inequality` |
| `edgePerturbation_degree_tail_bernstein` | theorem (axiom-conditional) | **`bernstein_inequality`'s first theorem consumer** (2026-08-29, the Bernstein twin): `μ {t ≤ \|deg dev\|} ≤ 2 exp(−t²/(2 σ²_v + 2Mt/3))` at the *true* variance statistic `σ²_v = ∑ₑ w_v(e)² p e (1 − p e)` and magnitude budget `M ≥ \|w_v(e)\|` — the variance-adaptive degree tail, strictly sharper than the Hoeffding twin at interior `p` (`σ²_v ≤ S_v/4`, the strict improvement `2 exp(−3/5) < 2 exp(−1/4)` proved in QA) | `bernstein_inequality` |
| `edgePerturbation_degree_tail_bernstein_budget` | theorem (axiom-conditional) | **`bernstein_bounded_variance`'s first theorem consumer** (2026-08-29, the Bernstein twin): the budget form at any supplied `σ²_v ≤ Vbud` (the relaxation honest by exponent monotonicity, pinned in QA) | `bernstein_bounded_variance` |
| `perturbAdmissible` | definition | The admissibility window of the irregular design (2026-08-29): outcomes whose resampled graph stays nonnegative with degrees in the base window `[dmin, dmax]` — event-internal because the centered design's degrees are random and the norm tail carries zero degree information (`L(E_ω)·1 = 0` identically) | — |
| `edgePerturbation_normalized_cheeger_floor` | theorem (axiom-conditional) | The *normalized* Cheeger floor (2026-08-29, the irregular window): `μ {ω admissible ∧ λ₂(L_sym G_ω) ≤ (dmin·φ(A)²/2 − t)/dmax} ≤ 2 d exp(−t²/(2 ‖∑_e L_e²‖))` on arbitrary symmetric nonnegative positive-degree base graphs — the sandwich's lower side on the perturbed graph plus the window-Cheeger floor engine, a `measure_mono` into the λ₂ lower tail | `matrix_hoeffding` |
| `edgePerturbation_normalized_connectivity_bracket` | theorem (axiom-conditional) | The two-sided *normalized* window (2026-08-29, the irregular window): leaving `[(dminφ²/2 − t)/dmax, (2·dmax·φ + t)/dmin]` implies leaving the two-sided eigenvalue tail at the same constant — the floor consumes the sandwich's lower side at the perturbed degree ceiling, the ceiling the upper side at the degree floor; both engine constants load-bearing | `matrix_hoeffding` |
| `edgePerturbation_fiedler_sweep_cut_tail` | theorem (axiom-conditional) | The swept-Fiedler-cut consumer of the normalized window (2026-08-29, the family's algorithm-facing capstone): at the floor-positivity guard `0 < dmin·φ²/2 − t`, `μ {ω admissible ∧ ¬(connected G_ω ∧ ∃ swept S, conductance G_ω S² ≤ 2·(2·dmax·φ + t)/dmin)} ≤ 2 d exp(−t²/(2 ‖∑_e L_e²‖))` — the floor's positivity feeding the connectivity transfer (`0 < λ₂(L_sym) ↔ connected`), the ceiling capping `fiedler_sweep_cut_normalized` on the resampled graph; three delivered families load-bearing on one statement | `matrix_hoeffding` |
| `perturbAdmissible_of_degDev_lt` | theorem (proved) | **The degree-window transfer** (2026-08-29, the admissibility dissolution): base degrees in the shrunk window `[dmin + s, dmax − s]` plus per-vertex deviations strictly below `s` put the outcome inside the admissibility window — nonnegativity from the pair design condition (`perturbWeight_entry_nonneg`), degrees from the shrunk window; no `0 ≤ s` hypothesis (the strictness carries it) | — |
| `edgePerturbation_normalized_connectivity_bracket_unconditional` | theorem (axiom-conditional) | **The admissibility dissolution — the window family's first unconditional measured event** (2026-08-29): at the shrunk base window and the pair design condition, leaving the two-sided normalized-connectivity window — an *unconditioned* event — is bounded by `2 d exp(−t²/(2 ‖∑_e L_e²‖)) + ∑_v 2 exp(−s²/(2 S_v))`, by the decomposition "some deviation ≥ s, or all < s and then admissible" — the first composition of the degree-tail and window families, dissolving the recorded admissibility honesty note on its degree half | `matrix_hoeffding`, `hoeffding_inequality` |
| `edgePerturbation_normalized_cheeger_floor_unconditional` | theorem (axiom-conditional) | **The dissolution's floor member** (2026-08-29, the completion): the *unconditioned* floor event `μ {λ₂(L_sym G_ω) ≤ (dmin·φ²/2 − t)/dmax} ≤ 2 d exp(−t²/(2 ‖∑_e L_e²‖)) + ∑_v 2 exp(−s²/(2 S_v))` at the same decomposition — the family's second two-axiom member | `matrix_hoeffding`, `hoeffding_inequality` |
| `edgePerturbation_fiedler_sweep_cut_tail_unconditional` | theorem (axiom-conditional) | **The dissolution's capstone member — the family completed** (2026-08-29): the failure of "connected with a swept Fiedler cut at `conductance² ≤ 2·(2·dmax·φ + t)/dmin`" bounded the same way with **no conditioning event** — an unconditioned high-probability algorithmic output under random edge resampling; the floor-positivity guard remains (it feeds the connectivity transfer, not the window — its C₄ dropped-guard refutation fixture carries over verbatim); the **strict-containment witness** in QA proves the dissolution genuinely enlarged the measured event (the all-false outcome in the unconditional bad event while provably not admissible) | `matrix_hoeffding`, `hoeffding_inequality` |

**Module**: `Scaffold.Derived.EventStream` (derived layer, not axioms)

| Declaration | Kind | Description | Consumes |
|-------------|------|-------------|----------|
| `sum_range_telescope` | proved | `∑_{k<m} (f_{k+1} - f_k) = f_m - f_0` | — |
| `randomLaplacianIncrement` | definition | Laplacian increment process of a random stream | — |
| `randomLaplacianIncrement_bounded_iff` | proved | Uniform bound ↔ pointwise `IsEventDriven` | — |
| `eventStreamTail` | axiom-backed derived | Tail of cumulative Laplacian perturbation `‖L_m - L_0‖` | `matrix_azuma_hoeffding` |

**Module**: `Scaffold.Derived.ProjectorDrift` (derived layer, not axioms)

| Declaration | Kind | Description | Consumes |
|-------------|------|-------------|----------|
| `davisKahanTwoPoint` | axiom-backed derived | `‖P_C - P_B‖ ≤ ‖C-B‖/δ` from a base-gap hypothesis | `davis_kahan_sin_theta` (plus the *proved* `weyl_inequality` since the 2026-08-20 retirement) |
| `eventStreamProjectorDrift` | axiom-backed derived | `μ{‖P_{L_m} - P_{L_0}‖ ≥ s/(γ-s)} ≤ 2 d exp(-s²/(8 m R²))` | the above plus `eventStreamTail` |

### Planned (no module yet)

| Axiom | Description | Source |
|-------|-------------|--------|
| `freedman_inequality` | Martingale with variance process | Freedman (1975) |
| `gaussian_matrix_concentration` | Gaussian matrix spectral norm | Vershynin Thm 5.3.1 |

**Module**: `Scaffold.Derived.EmpiricalStationary` (derived layer; the two theorems below are axiom-backed, honestly reported by `#print axioms`)

| Declaration | Kind | Description | Consumes |
|-------------|------|-------------|----------|
| `hoeffding_empirical_iid` | axiom-backed derived | The empirical visit frequency of `i` in `n` i.i.d. `q`-samples concentrates around `q i` at `2 exp(−2nt²)`; `n ≠ 0` load-bearing at the centering collapse | `hoeffding_empirical` |
| `empiricalWalkDistribution_tail` | axiom-backed derived | The graph instance at `q = walkDistribution A t₀ x`: `P{\|p̂_i(n) − ν_{t₀} i\| ≥ t} ≤ 2 exp(−2nt²)`; no symmetry/connectivity/mixing hypothesis | `hoeffding_empirical` |

## Usage Patterns

### For Bounded Variables

1. Use `hoeffding_lemma` (probability measure; conclusion `≤ √6·a`) to show subgaussian
2. Apply `hoeffding_inequality` (integrability of the clause set certified by `integrable_of_bounded_measurable`)

### For Variance-Dependent Bounds

1. Use `bernstein_inequality` when variance is small
2. Provides tighter bounds than Hoeffding when Var(X) ≪ bound²

### For Martingales

1. Azuma for bounded differences
2. Freedman when variance process is available

## See Also

- [Sources Index](../sources/) for detailed bibliographic information
- [Load-bearing Axioms](../load_bearing_axioms.md) for critical dependencies
