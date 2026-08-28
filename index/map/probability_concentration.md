# Probability Concentration Inequalities

This index maps Lean modules and axioms for concentration inequalities by topic area.

## Scalar Concentration

### Subgaussian Random Variables

**Module**: `Scaffold.Mathlib.Probability.Concentration.Scalar.Subgaussian`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `subgaussianNorm` | definition | Ψ₂ norm via the MGF characterization; junk behavior documented (empty set → 0 via `Real.sInf_empty`; non-integrable MGFs → junk-zero integrals make the set *full*, also 0) | Vershynin Def 2.5.1 / Prop 2.5.2 |
| `subgaussianNorm_nonneg` | proved | `0 ≤ subgaussianNorm X μ` | — |
| `hoeffding_lemma` | axiom | Bounded and centered ⇒ subgaussian | Vershynin Lem 2.6.2 |
| `subgaussian_tail_bound` | **proved** (2026-08-22; retired from axiom with repaired hypotheses `0 < K`, MGF integrable, MGF integral ≤ 2 — the old `subgaussianNorm ≤ K` shape was materially false via `sInf ∅ = 0` and junk-zero integrals, refuted in QA at `3 • δ₀`) | μ{\|X\| ≥ t} ≤ 2exp(−t²/(2K²)) | Vershynin Prop 2.5.2 (ii) |

Formerly admitted subgaussian statements without a current consumer
(`subgaussian_moment_growth`, `subgaussian_linear_combination`,
`subgaussian_centering`, `subgaussian_sum_bound`) were removed from the
axiom boundary in the 2026-08-17 concentration repair.

### Hoeffding's Inequality

**Module**: `Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `hoeffding_inequality` | axiom | Sums of bounded independent variables | Vershynin Thm 2.2.2 |
| `hoeffding_iid` | proved | Uniform-bound specialization | Vershynin Cor 2.2.3 |
| `hoeffding_empirical` | axiom | Empirical averages of [0,1] variables | Boucheron-Lugosi-Massart Thm 2.8 |

### Bernstein's Inequality

**Module**: `Scaffold.Mathlib.Probability.Concentration.Scalar.Bernstein`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `bernstein_inequality` | axiom | Tail bound with variance | Vershynin Thm 2.8.1 |
| `bernstein_bounded_variance` | axiom | Bounded variance form | Wainwright Thm 2.15 |
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
| `indepFun_coord` | proved | Pairwise `IndepFun` of coordinate projections — the `h_indep` clause shape |
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
| `indepFun_coord` | proved | Pairwise `IndepFun` of the V-valued projections |
| `measurable_indicator_coord` | proved | The `h_meas` clause shape of `hoeffding_empirical` at coordinate indicators |
| `integral_indicator` | proved | `∫ 1_{ω e = i} ∂μ = q i` — the mean-clause constant the empirical form's centering collapses to |
| `indepFun_indicator_coord` | proved | The `h_indep` clause shape of `hoeffding_empirical` at coordinate indicators |

## Matrix Concentration

All statements are over the spectral norm (`Matrix.L2OpNorm`), the
semidefinite order (`Matrix.PosSemidef`), and the product σ-algebra on
matrices defined in `Matrix/Basic.lean`.

### Matrix Hoeffding

**Module**: `Scaffold.Mathlib.Probability.Concentration.Matrix.Hoeffding`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `matrix_hoeffding` | axiom | Independent Hermitian, PSD-dominated squares | Tropp Thm 1.4 |

### Matrix Bernstein

**Module**: `Scaffold.Mathlib.Probability.Concentration.Matrix.Bernstein`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `matrix_bernstein` | axiom | Independent centered uniformly bounded | Tropp Thm 1.1 |

### Matrix Azuma–Hoeffding

**Module**: `Scaffold.Mathlib.Probability.Concentration.Matrix.Azuma`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `mdsFiltration` | definition | Natural past σ-algebra of a matrix sequence | — |
| `MatrixMDS` | definition | Martingale-difference structure with uniform bound | — |
| `matrix_azuma_hoeffding` | axiom | Dependent-event tail bound `2d exp(-t²/(8mR²))` | Tropp Thm 7.1 |

### Derived consumers

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

1. Use `hoeffding_lemma` to show subgaussian
2. Apply `subgaussian_sum_bound` or `hoeffding_inequality`

### For Variance-Dependent Bounds

1. Use `bernstein_inequality` when variance is small
2. Provides tighter bounds than Hoeffding when Var(X) ≪ bound²

### For Martingales

1. Azuma for bounded differences
2. Freedman when variance process is available

## See Also

- [Sources Index](../sources/) for detailed bibliographic information
- [Load-bearing Axioms](../load_bearing_axioms.md) for critical dependencies
