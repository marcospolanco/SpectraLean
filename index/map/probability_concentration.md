# Probability Concentration Inequalities

This index maps Lean modules and axioms for concentration inequalities by topic area.

## Scalar Concentration

### Subgaussian Random Variables

**Module**: `Scaffold.Mathlib.Probability.Concentration.Scalar.Subgaussian`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `subgaussianNorm` | definition | Ψ₂ norm via the MGF characterization; junk behavior documented (empty set → 0 via `Real.sInf_empty`; non-integrable MGFs → junk-zero integrals make the set *full*, also 0) | Vershynin Def 2.5.1 / Prop 2.5.2 |
| `subgaussianNorm_nonneg` | proved | `0 ≤ subgaussianNorm X μ` | — |
| `subgaussianNorm_eq_zero_of_forall_eq_zero` | proved | A pointwise-zero variable has norm exactly `0` (every positive `K` admissible on a probability measure — the `a = 0` corner of the bounded-variable bound) | — |
| `subgaussianNorm_le_of_bounded` | proved (2026-08-30, `proposals/retire-hoeffding-lemma-pointwise-collapse.md`) | The sharp boundedness-only collapse: `subgaussianNorm ≤ a/√(log 2)` with **no mean-zero, no measurability hypothesis, no numeric pins** — the defining set sees only the bound and the mass; the constant is exact (attained at `|X| ≡ a`, QA `rademacher_norm_eq_QA`); the probability-measure instance load-bearing (QA mass-guard fence at the mass-19/10 fixture) | — (pointwise `exp (X²·log 2/a²) ≤ exp (log 2) = 2`) |
| `hoeffding_lemma` | **proved (retired from axiom 2026-08-30, `proposals/retire-hoeffding-lemma-pointwise-collapse.md`)** — at the unchanged `√6·a` shape through `subgaussianNorm_le_of_bounded` + `1/√(log 2) ≤ √6` (`log 2 ≥ 1/2`); the mean-zero hypothesis retained for statement stability, unused by the proof (earlier history: repaired 2026-08-28 — the pre-repair `subgaussianNorm ≤ a` shape with no measure constraint was materially false in two ways, the constant `1` refuted at the fair-coin Rademacher fixture and *every* constant `≤ 4` refuted at the mass-19/10 rescaling, both with genuinely-satisfied hypotheses, `proposals/audit-scalar-concentration-integrability-hazard.md`; the source's actual λ-form content is the proved `hoeffding_lemma_mgf`) | Bounded and centered on a **probability measure** ⇒ `subgaussianNorm ≤ √6·a` | Vershynin Lem 2.6.2 (λ-form; the `√6` derived via two-sided tail + layer-cake integration) |
| `subgaussian_tail_bound` | **proved** (2026-08-22; retired from axiom with repaired hypotheses `0 < K`, MGF integrable, MGF integral ≤ 2 — the old `subgaussianNorm ≤ K` shape was materially false via `sInf ∅ = 0` and junk-zero integrals, refuted in QA at `3 • δ₀`) | μ{\|X\| ≥ t} ≤ 2exp(−t²/(2K²)) | Vershynin Prop 2.5.2 (ii) |

Formerly admitted subgaussian statements without a current consumer
(`subgaussian_moment_growth`, `subgaussian_linear_combination`,
`subgaussian_centering`, `subgaussian_sum_bound`) were removed from the
axiom boundary in the 2026-08-17 concentration repair.

### Hoeffding's Inequality

**Module**: `Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `hoeffding_inequality` | **proved (retired from axiom 2026-08-30, `proposals/prove-hoeffding-inequality-mgf.md`)** — the Chernoff assembly from `hoeffding_lemma_mgf` (earlier history: audited safe 2026-08-28, pairwise→`iIndepFun` repair 2026-08-28/29, Errata §6; QA: the denominator fence + the first genuinely-random instantiation in `Scalar_QA.lean`) | Sums of bounded independent variables | Vershynin Thm 2.2.2 |
| `integrable_of_bounded_measurable` | proved | The audit's safety lemma: measurable + `|X| ≤ a` + probability measure ⇒ `Integrable X` | — |
| `hoeffding_iid` | proved | Uniform-bound specialization | Vershynin Cor 2.2.3 |
| `hoeffding_inequality_interval` / `hoeffding_lemma_mgf` / `mgf_sum_le_of_iIndepFun` / `phiComb_le_exp` | proved (2026-08-30 retirement) | The retirement's proved core: the MGF interval engine `E exp(λX) ≤ exp(λ²(b−a)²/8)` (secant bound + the sharp two-point `φ(u) ≤ e^{u²/8}` by the perfect-square identity), the independence factorization, and the interval-form tail | Hoeffding 1963, Lemma 2; Vershynin Prop 2.2.1 |
| `hoeffding_empirical` | **proved (retired from axiom 2026-08-30)** — the centered `[0,1]` specialization of the interval engine (earlier: pairwise→`iIndepFun` repair 2026-08-29, Errata §6; QA: the closed-form instance with the exact `1/2` deviation-event measure in `Scalar_QA.lean`) | Empirical averages of [0,1] variables | Boucheron-Lugosi-Massart Thm 2.8 |

Adversarial-fence coverage (2026-09-05,
`proposals/adversarial-fences-scalar-concentration-family.md`): the
`h_indep` clauses of the Hoeffding tail/MGF theorems and the `ht`
backward-time clause fenced at the perfectly-correlated two-coin
fixture `scCorrX` (`Scalar_QA.lean`'s `AdversarialFences` section) —
the product-integral identity refuted by the algebraic
`cosh 2 ≠ cosh²1`, the MGF bound by `cosh 2 > e`, the tails by
event-degeneration (`1 > 2e⁻¹`) — and the `h_mean` centering clauses
of `mgf_sum_le_of_iIndepFun`, `hoeffding_inequality_interval`,
`hoeffding_inequality`, `hoeffding_iid` fenced at the
genuinely-independent biased product (the `DeferralFences` section:
independence genuine, centering broken at `4/5`; the `t = 2` tail at
`41/50 > 2e⁻¹`, the `λ = 1` MGF over `e`). The measurability layer
(the proposal's follow-up record, same day): the `h_meas` clauses of
`hoeffding_inequality_interval` and `hoeffding_empirical` and the
`hf` clauses of the `measurable_finset_prod'`/`sum'` engines fenced at
the biased two-point `⊥`-σ-algebra space (`Scalar_QA.lean`'s
`MeasurabilityFences` section — non-measurable breakers, junk-zero
means, heavy-atom mass `9/10 > 2e⁻²`); `hoeffding_inequality`'s and
`hoeffding_iid`'s own `h_meas` carry the priced trim-saturation
deferral. Both deferrals were closed the same day (the
proposal's deferral-closure record): the saturation lemma
(`scM_dirac_bot_eq_one`) and the saturated-independence lemma in
`Scalar_QA.lean`'s `SaturationFences` section fence both theorems'
`h_meas` at the four-cell family on `(Fin 4, ⊥, δ₀)` — the
repository's first genuinely-independent non-measurable family.

### Bernstein's Inequality

**Module**: `Scaffold.Mathlib.Probability.Concentration.Scalar.Bernstein`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `bernstein_inequality` | **proved theorem since 2026-08-30** (Errata §8 repair-and-retirement: the admitted form hypothesized the *uncentered* bound `\|X i ω\| ≤ a` — materially understating the Bennett price, MGF-separation witness in QA — repaired to the source-faithful centered bound and proved by the local Bennett MGF engine; repaired 2026-08-29 pairwise → `iIndepFun`, Errata §6; audited safe 2026-08-28) | Tail bound with variance | Vershynin Thm 2.8.1 |
| `bernstein_bounded_variance` | **proved theorem since 2026-08-30** (Errata §8 repair-and-retirement, same centered-bound repair and Bennett engine; the dead `0 ≤ v` clause dropped — strictly stronger statement; repaired 2026-08-29 pairwise → `iIndepFun`, Errata §6) | Bounded variance form | Wainwright Thm 2.15 |
| `integrable_sq_sub_mean` | proved | The audit's centered-square safety lemma: both Bernstein statements' variance statistics are honest integrals | — |
| `bennettQ`, `bennettQ_eq_integral`, `bennettQ_le`, `hasSum_bennettQ`, `bennettQ_le_inv` | proved (2026-08-30) | The Bennett ratio `(e^u−1−u)/u²`: integral representation `∫₀¹(1−s)e^{us}ds`, whole-line monotonicity, the series representation, and the series bound `q(v) ≤ 1/(2(1−v/3))` on `(0,3)` | — |
| `exp_le_add_sq_mul`, `bennett_mgf`, `mgf_sum_le_bernstein` | proved (2026-08-30) | The MGF engine retiring the pair: the pointwise Bennett bound, the per-variable MGF bound `E e^{λY} ≤ exp(λ²σ²/(2(1−λa/3)))`, and the sum bound through the Hoeffding retirement's `iIndepFun` factorization | — |
| `bernstein_iid` | proved | Common-variance specialization | Vershynin Cor 2.8.3 |

## Sampling Spaces

Adversarial-fence coverage (2026-09-05): the `h_indep` clauses of the
Bernstein tail theorems fenced at `scCorrX` (event-degeneration kills,
`1 > 2e^{-3/4}`) and the `ht` clause at `scRadX` (`t = -2`,
`1 > 2e^{-3/2}`).

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

Adversarial-fence coverage (2026-09-05,
`proposals/adversarial-fences-bernoulli-product-family.md`): fifteen
hypothesis-form fences in `BernoulliProduct_QA.lean`'s `AdversarialFences`
section — the four ∑-theorems' `hp0`/`hp1` bounds clauses (out-of-bounds
fixtures keeping the other bound genuine; a marginal-identity bounds fence
needs a breaker coordinate outside the statement's consumed coordinates),
the `hee` distinctness clauses (Cauchy–Schwarz strictness at the double
marginal; `μ(A ∩ A) ≠ μ(A)²` for both independence statements, the matrix
kill at the measurable entry cylinder), the `he` injectivity clauses of the
mutual-independence transfer trio, and the `hpne` centering clause (the
file's pre-discipline free-form fences reconciled as the wrappers' proof
engines). The `bernPMF`-consuming theorems' bounds clauses are
signature-entangled: the sampling measure does not exist out of bounds.

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

The family's falsification surface is fully fenced (2026-09-05,
`proposals/adversarial-fences-iid-product-family.md`): every priceable
named clause has a negative witness in `IIDProduct_QA.lean`'s
`AdversarialFences` section — the `hq0`/`hq1` bounds clauses of the
three ∑-theorems at `ofReal`-clamp fixtures keeping the other clause
genuine, `sum_coord2_mul`'s pair at the three-coordinate breaker
(on `Fin 2` Fubini makes the dropped identity true),
the three signature-free `hee` clauses at the all-genuine `q23`
(`2/3 ≠ 4/9`), and `iIndepFun_coord_apply`'s `he` at the constant
reindexing; `iIndepFun_coord_apply`'s `hF` is decorative at the
shelf's own generality (the proved hF-free twin
`iIndepFun_coord_apply_strict`), and the nine `iidPMF`-consumers'
mass clauses are signature-entangled (the sampling measure does not
exist out of bounds — the mass-level fences are that entanglement's
visible boundary).

## Matrix Concentration

The matrix axioms' hypothesis surfaces are fully fenced (2026-09-05,
`proposals/adversarial-fences-matrix-concentration-family.md`):
beyond the repair-era refutations (the `Fin 0` corner ×3, the
uncentered family, the caterpillar), twelve hypothesis-form
`-- @refutes`-tagged fences in `Matrix_QA.lean`'s `AdversarialFences`
section close every remaining named clause — `matrix_hoeffding`'s
`h_herm`/`h_indep`/`h_bound`/`ht`, `matrix_bernstein`'s
`h_mean`/`h_herm`/`h_bound`/`h_meas`/`ht` (with `h_meas` the
headline: the variance statistic is itself a junk integral — Errata
§7's mechanism class reaching the sibling axiom through `Σ`), and
`matrix_azuma_hoeffding`'s `cond_mean_zero`/`norm_bound`/`ht` — the
repository's mechanically-independence-checked tag count 12 → 24.

All statements are over the spectral norm (`Matrix.L2OpNorm`), the
semidefinite order (`Matrix.PosSemidef`), and the product σ-algebra on
matrices defined in `Matrix/Basic.lean`.

### Master Bound (retirement-route engine)

**Module**: `Scaffold.Mathlib.Probability.Concentration.Matrix.MasterBound`
(delivered 2026-08-30, `proposals/matrix-master-bound-first-slice.md` —
all proved, zero axioms: the first slice of the admitted matrix trio's
retirement route, the Laplace-transform engine every matrix
concentration proof consumes)

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `trace_exp_smul_eq_sum_exp_eigvalOf` | proved (2026-08-30) | The trace-exponential spectral identity `tr (exp (θ•M)) = ∑ i, exp (θ·λᵢ(M))` for real-symmetric `M`, any scale `θ` — the identity the pinned Mathlib's `MatrixExponential.lean` lists as an open TODO; conjugation through the spectral theorem's unitary diagonalization (`exp_conj` + `exp_diagonal`), the exp-carrying extension of `eigvalOf_sum_eq_trace`'s route | — |
| `trace_exp_nonneg` / `exp_smul_eigvalOf_le_trace_exp` | proved (2026-08-30) | The trace-exponential is a sum of exponentials (nonnegative), and every eigenvalue's exponential is a single summand of it — the deterministic half of the master bound's inclusion step | — |
| `continuous_trace_exp` / `stronglyMeasurable_trace_exp` | proved (2026-08-30) | The trace-exponential is continuous in the matrix argument (at the `l∞`-instance topology, the canonical product topology) and hence strongly measurable after any strongly measurable matrix-valued function — the hypothesis under which the Markov step applies | — |
| `measure_mul_le_lintegral` | proved (2026-08-30) | Markov's inequality on the lower integral (`c · μ {c ≤ f} ≤ ∫⁻ f`), no integrability hypothesis, `c = 0` allowed — honest for unbounded summands | — |
| `exists_abs_eigvalOf_ge` | proved (2026-08-30) | The norm–eigenvalue attainment bridge: on a nonempty index type every threshold below the operator norm is attained by some eigenvalue in absolute value (`[Nonempty V]` load-bearing — fails at `V = ∅`, `t = 0`, fenced by `master_bound_fin0_unguarded_refuted_QA`) | — |
| `matrix_master_bound` | **proved** (2026-08-30) | Tropp's Proposition 3.1, the two-sided spectral-norm form: `μ {t ≤ ‖Y‖} ≤ e^{−θt} (E tr e^{θY} + E tr e^{−θY})` for strongly measurable symmetric-matrix-valued `Y`, `θ ≥ 0` — the expectations as `ℝ≥0∞` lower integrals (no integrability hypothesis); `[Nonempty V]` guard at birth; the `inf_θ` left to the consumer; the still-admitted trio rides it together with the (future, gated) sum-MGF step | Tropp Prop 3.1 |

### Matrix Hoeffding

**Module**: `Scaffold.Mathlib.Probability.Concentration.Matrix.Hoeffding`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `matrix_hoeffding` | axiom | Mutually independent, **centered** (`h_mean : ∀ i, ∫ X i ∂μ = 0`, added by the 2026-08-30 Errata §9 repair — the uncentered pre-repair shape was refuted by the deterministic constant-ones family, `old_matrix_hoeffding_refuted_uncentered_QA`) Hermitian, PSD-dominated squares; `[Nonempty V]` guard (repaired 2026-08-28 — the guard-free shape was inconsistent at `card V = 0`, `t = 0`; **repaired 2026-08-29**: pairwise → `iIndepFun`, Errata §6) | Tropp Thm 1.4 |

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
| `matrix_hoeffding_quadForm` | theorem (axiom-conditional) | Fixed-nonzero-vector quadratic-form pullback of the axiom (`x ≠ 0` load-bearing: at `x = 0` the event is all of `Ω`; statement gains the axiom's `h_mean` centering hypothesis at the 2026-08-30 Errata §9 repair) | `matrix_hoeffding` |
| `edgePerturbation_norm_tail` | theorem (axiom-conditional) | `μ {‖∑_e (δ_e − p_e) • L_e‖ ≥ t} ≤ 2 d exp(−t²/(2 ‖∑_e L_e²‖))` | `matrix_hoeffding` |
| `edgePerturbation_quadForm_tail` | theorem (axiom-conditional) | The same bound at `t (x ⬝ᵥ x) ≤ |xᵀ S(ω) x|` for a fixed nonzero `x` | `matrix_hoeffding` |
| `edgePerturbation_eval_tail` | theorem (axiom-conditional) | The eigenvalue-level packaging (2026-08-28, the follow-on delivery): `μ {t ≤ |λᵢ(L(A+E_ω)) − λᵢ(L A)|} ≤ 2 d exp(−t²/(2 ‖∑_e L_e²‖))` at every sorted index — the norm tail joined to the *proved* Weyl inequality | `matrix_hoeffding` |
| `edgePerturbation_eval_lower_tail` | theorem (axiom-conditional) | The one-sided gap-survival form `μ {λᵢ(L(A+E_ω)) ≤ λᵢ(L A) − t} ≤ …` | `matrix_hoeffding` |
| `edgePerturbation_lambda2_lower_tail` | theorem (axiom-conditional) | The λ₂ spelling at the `lambda2` interface (`2 ≤ card V`) — the Fiedler-facing robustness statement | `matrix_hoeffding` |
| `edgePerturbation_quadForm_uniform_tail` | theorem (axiom-conditional) | The uniform/existential-x packaging: outside the bound's failure set, `|xᵀ L(E_ω) x| < t (x ⬝ᵥ x)` for *every* nonzero `x` simultaneously (`x ≠ 0` guard load-bearing — the un-guarded event is all of `Ω`) | `matrix_hoeffding` |
| `edgePerturbation_lambda2_cheeger_floor` | theorem (axiom-conditional) | The Cheeger-driven connectivity floor (2026-08-28, the Cheeger-window follow-on): `μ {λ₂(L(A+E_ω)) ≤ d·φ(A)²/2 − t} ≤ 2 d exp(−t²/(2 ‖∑_e L_e²‖))` on `d`-regular input — the proved `cheeger_lower_bound_laplacian` composed with the λ₂ lower tail by `measure_mono` | `matrix_hoeffding` |
| `edgePerturbation_connectivity_bracket` | theorem (axiom-conditional) | The two-sided window (2026-08-28): `μ {λ₂(L(A+E_ω)) ≤ d·φ²/2 − t ∨ 2dφ + t ≤ λ₂(L(A+E_ω))} ≤ 2 d exp(…)` at the same constant as the one-sided tail — both Cheeger directions (the engine pair) load-bearing on the inclusion into the two-sided eigenvalue tail | `matrix_hoeffding` |
| `edgePerturbation_degree_tail` | theorem (**hard crust since the 2026-08-30 retirement**; `#print axioms`-verified) | **`hoeffding_inequality`'s first theorem consumer** (2026-08-29, the degree-concentration delivery): `μ {t ≤ \|deg G_ω v − deg A v\|} ≤ 2 exp(−t²/(2 S_v))` at `S_v = ∑ₑ w_v(e)²` — the per-vertex degree-deviation tail, the complementary concentration the window family's admissibility story was missing (the λ₂/norm tails carry zero degree information, `L(E_ω)·1 = 0` identically) | — (proved) |
| `edgePerturbation_degree_tail_all` | theorem (**hard crust since the 2026-08-30 retirement**; `#print axioms`-verified) | The all-vertices union bound (2026-08-29), stated at the exact per-vertex sum — the first step toward *deriving* the admissibility window rather than hypothesizing it (the collapse to a uniform exponent needs per-vertex `0 < S_v`, demonstrated numerically in QA) | — (proved) |
| `edgePerturbation_degree_tail_bernstein` | theorem (**hard crust since 2026-08-30**: `bernstein_inequality` proved by the repair-and-retirement, `#print axioms` standard-three) | **`bernstein_inequality`'s first theorem consumer** (2026-08-29, the Bernstein twin): `μ {t ≤ \|deg dev\|} ≤ 2 exp(−t²/(2 σ²_v + 2Mt/3))` at the *true* variance statistic `σ²_v = ∑ₑ w_v(e)² p e (1 − p e)` and magnitude budget `M ≥ \|w_v(e)\|` — the variance-adaptive degree tail, strictly sharper than the Hoeffding twin at interior `p` (`σ²_v ≤ S_v/4`, the strict improvement `2 exp(−3/5) < 2 exp(−1/4)` proved in QA) | `bernstein_inequality` (proved 2026-08-30) |
| `edgePerturbation_degree_tail_bernstein_budget` | theorem (**hard crust since 2026-08-30**: `bernstein_bounded_variance` proved by the repair-and-retirement, `#print axioms` standard-three) | **`bernstein_bounded_variance`'s first theorem consumer** (2026-08-29, the Bernstein twin): the budget form at any supplied `σ²_v ≤ Vbud` (the relaxation honest by exponent monotonicity, pinned in QA) | `bernstein_bounded_variance` (proved 2026-08-30) |
| `perturbAdmissible` | definition | The admissibility window of the irregular design (2026-08-29): outcomes whose resampled graph stays nonnegative with degrees in the base window `[dmin, dmax]` — event-internal because the centered design's degrees are random and the norm tail carries zero degree information (`L(E_ω)·1 = 0` identically) | — |
| `edgePerturbation_normalized_cheeger_floor` | theorem (axiom-conditional) | The *normalized* Cheeger floor (2026-08-29, the irregular window): `μ {ω admissible ∧ λ₂(L_sym G_ω) ≤ (dmin·φ(A)²/2 − t)/dmax} ≤ 2 d exp(−t²/(2 ‖∑_e L_e²‖))` on arbitrary symmetric nonnegative positive-degree base graphs — the sandwich's lower side on the perturbed graph plus the window-Cheeger floor engine, a `measure_mono` into the λ₂ lower tail | `matrix_hoeffding` |
| `edgePerturbation_normalized_connectivity_bracket` | theorem (axiom-conditional) | The two-sided *normalized* window (2026-08-29, the irregular window): leaving `[(dminφ²/2 − t)/dmax, (2·dmax·φ + t)/dmin]` implies leaving the two-sided eigenvalue tail at the same constant — the floor consumes the sandwich's lower side at the perturbed degree ceiling, the ceiling the upper side at the degree floor; both engine constants load-bearing | `matrix_hoeffding` |
| `edgePerturbation_fiedler_sweep_cut_tail` | theorem (axiom-conditional) | The swept-Fiedler-cut consumer of the normalized window (2026-08-29, the family's algorithm-facing capstone): at the floor-positivity guard `0 < dmin·φ²/2 − t`, `μ {ω admissible ∧ ¬(connected G_ω ∧ ∃ swept S, conductance G_ω S² ≤ 2·(2·dmax·φ + t)/dmin)} ≤ 2 d exp(−t²/(2 ‖∑_e L_e²‖))` — the floor's positivity feeding the connectivity transfer (`0 < λ₂(L_sym) ↔ connected`), the ceiling capping `fiedler_sweep_cut_normalized` on the resampled graph; three delivered families load-bearing on one statement | `matrix_hoeffding` |
| `perturbAdmissible_of_degDev_lt` | theorem (proved) | **The degree-window transfer** (2026-08-29, the admissibility dissolution): base degrees in the shrunk window `[dmin + s, dmax − s]` plus per-vertex deviations strictly below `s` put the outcome inside the admissibility window — nonnegativity from the pair design condition (`perturbWeight_entry_nonneg`), degrees from the shrunk window; no `0 ≤ s` hypothesis (the strictness carries it) | — |
| `edgePerturbation_normalized_connectivity_bracket_unconditional` | theorem (conditional on `matrix_hoeffding` alone since the 2026-08-30 retirement) | **The admissibility dissolution — the window family's first unconditional measured event** (2026-08-29): at the shrunk base window and the pair design condition, leaving the two-sided normalized-connectivity window — an *unconditioned* event — is bounded by `2 d exp(−t²/(2 ‖∑_e L_e²‖)) + ∑_v 2 exp(−s²/(2 S_v))`, by the decomposition "some deviation ≥ s, or all < s and then admissible" — the first composition of the degree-tail and window families, dissolving the recorded admissibility honesty note on its degree half | `matrix_hoeffding` (the `hoeffding_inequality` half retired to proved 2026-08-30) |
| `edgePerturbation_normalized_cheeger_floor_unconditional` | theorem (conditional on `matrix_hoeffding` alone since the 2026-08-30 retirement) | **The dissolution's floor member** (2026-08-29, the completion): the *unconditioned* floor event `μ {λ₂(L_sym G_ω) ≤ (dmin·φ²/2 − t)/dmax} ≤ 2 d exp(−t²/(2 ‖∑_e L_e²‖)) + ∑_v 2 exp(−s²/(2 S_v))` at the same decomposition — the family's second two-axiom member | `matrix_hoeffding` (the `hoeffding_inequality` half retired to proved 2026-08-30) |
| `edgePerturbation_fiedler_sweep_cut_tail_unconditional` | theorem (conditional on `matrix_hoeffding` alone since the 2026-08-30 retirement) | **The dissolution's capstone member — the family completed** (2026-08-29): the failure of "connected with a swept Fiedler cut at `conductance² ≤ 2·(2·dmax·φ + t)/dmin`" bounded the same way with **no conditioning event** — an unconditioned high-probability algorithmic output under random edge resampling; the floor-positivity guard remains (it feeds the connectivity transfer, not the window — its C₄ dropped-guard refutation fixture carries over verbatim); the **strict-containment witness** in QA proves the dissolution genuinely enlarged the measured event (the all-false outcome in the unconditional bad event while provably not admissible) | `matrix_hoeffding` (the `hoeffding_inequality` half retired to proved 2026-08-30) |

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

**Module**: `Scaffold.Derived.EmpiricalStationary` (derived layer; every theorem below **hard crust** — the tail engine was an admitted axiom until the 2026-08-30 retirement of `hoeffding_empirical`, verified by `#print axioms` at the standard three)

| Declaration | Kind | Description | Consumes |
|-------------|------|-------------|----------|
| `hoeffding_empirical_iid` | derived (**hard crust since the 2026-08-30 retirement**; `#print axioms`-verified) | The empirical visit frequency of `i` in `n` i.i.d. `q`-samples concentrates around `q i` at `2 exp(−2nt²)`; `n ≠ 0` load-bearing at the centering collapse | — (proved) |
| `empiricalWalkDistribution_tail` | derived (**hard crust since the 2026-08-30 retirement**; `#print axioms`-verified) | The graph instance at `q = walkDistribution A t₀ x`: `P{\|p̂_i(n) − ν_{t₀} i\| ≥ t} ≤ 2 exp(−2nt²)`; no symmetry/connectivity/mixing hypothesis | — (proved) |
| `empiricalWalkDistribution_stationary_tail` | derived (hard crust; `#print axioms`-verified 2026-08-31, `wip/empstat2_axcheck.lean`) | The stationarity-limit form (the proposal's Step 2): at threshold strictly above the oversmoothing entrywise bias `r ^ t₀ √(π i ((π x)⁻¹ − 1))`, `P{\|p̂_i(n) − π i\| ≥ t} ≤ 2 exp(−2n(t − bias)²)` — the proved `walkDistribution_sub_stationaryVec_abs_le` folded in by the triangle-route event inclusion | — (proved) |
| `empiricalWalkDistribution_stationary_tail_of_depth` | derived (hard crust; `#print axioms`-verified 2026-08-31, `wip/empstat2_axcheck.lean`) | The depth-form capstone — the oversmoothing ceiling's empirical counterpart: past the ceiling's own threshold at `ε/2`, `n` simulated trajectories estimate `π i` to `ε` at `2 exp(−nε²/2)` | — (proved) |
| `empiricalLazyWalkDistribution_tail` | derived (hard crust; `#print axioms`-verified 2026-09-02, `wip/lazystat_axcheck.lean`, `proposals/empirical-lazy-stationary-sampling.md`) | The fixed-time form at the lazy law: `P{\|p̂_i(n) − ν^L_{t₀} i\| ≥ t} ≤ 2 exp(−2nt²)` — the lazy law certified a probability vector by the proved `lazyWalkDistribution_nonneg`/`sum_lazyWalkDistribution` | — (proved) |
| `empiricalLazyWalkDistribution_stationary_tail` | derived (hard crust; `#print axioms`-verified 2026-09-02) | **The bias-term form at the computed intrinsic rate**: at threshold strictly above `(1 − λ₂/2)^t₀ √(π i ((π x)⁻¹ − 1))`, `P{\|p̂_i(n) − π i\| ≥ t} ≤ 2 exp(−2n(t − bias)²)` — connectivity the only graph hypothesis, no caller-supplied rate certificate (the plain twin's certificate provably unsatisfiable on every connected bipartite graph, fenced in QA) | — (proved) |
| `empiricalLazyWalkDistribution_stationary_tail_of_depth` | derived (hard crust; `#print axioms`-verified 2026-09-02) | **The lazy capstone — the sampling guarantee on the bipartite class**: past the lazy ceiling's own threshold at `ε/2` (honest visible `λ₂ < 2`, K₂'s rate-0 corner excluded), `n` simulated lazy trajectories estimate `π i` to `ε` at `2 exp(−nε²/2)` | — (proved) |
| `empiricalPageRank_tail` | derived (hard crust; `#print axioms`-verified 2026-09-02) | **The fixed-time empirical PageRank tail**: `n` i.i.d. samples of the `t₀`-step Google-walk law concentrate around the law at `2 exp(−2nt²)` — the probability certification proved, no symmetry anywhere | — (proved) |
| `empiricalPageRank_stationary_tail` | derived (hard crust; `#print axioms`-verified 2026-09-02) | **The PageRank bias-term form**: concentration around the stationary value with the quoted bias `α^{t₀}·TV(δ_x, π)` folded in — the rate theorem's own entrywise extraction through `abs_sub_le_tvDistance` | — (proved) |
| `empiricalPageRank_stationary_tail_of_depth` | derived (hard crust; `#print axioms`-verified 2026-09-02) | **The directed `t_mix` object's named consumer**: past the object's threshold at `ε/2`, `n` simulated random-surfer trajectories estimate `π i` to `ε` at `2 exp(−nε²/2)` — on directed input the entire symmetric mixing toolkit is unavailable, the α-rate Doeblin certificate the only route; the object's `_spec` attainment is load-bearing in the hypothesis | — (proved) |
| `empiricalPageRank_uniform_tail_of_depth` | derived (hard crust; `#print axioms`-verified 2026-09-02) | **The uniform `t_mix` object's named consumer** (2026-09-02, `proposals/directed-uniform-mixing-time.md`): past *one* start-independent threshold (the uniform object's attainment at `ε/2`), `n` simulated random-surfer trajectories estimate `π i` to `ε` at `2 exp(−nε²/2)` **for every start simultaneously** — the per-start capstone needs a per-start threshold; the agent that cannot control the surfer's start gets a single certificate, composed from the uniform `_spec` + the witness supplier + the delivered per-start capstone | — (proved) |
| `empiricalPageRank_tail_selfcontained_of_depth` | derived (hard crust; `#print axioms`-verified 2026-09-02) | **The self-contained capstone** (2026-09-02, `proposals/selfcontained-empirical-pagerank.md`): the sampling program's target *produced by the theorem itself* — `∃ π` (strictly positive, mass one, stationary at the Google walk, supplied by the re-proved `exists_pageRankVec`) such that past the single `(α, ε)`-computable display threshold `⌈log(2/ε)/log(1/α)⌉`, `n` simulated trajectories estimate `π i` to `ε` for every start — no caller-supplied stationarity anywhere; QA identifies the produced vector with the hand value through the proved `∃!`'s uniqueness clause | — (proved) |
| `empiricalWalkDistribution_stationary_tail_of_pos_power` | derived (hard crust; `#print axioms`-verified 2026-09-02) | **The stationarity-limit concentration at the Doeblin rate** (2026-09-02, `proposals/primitivity-supplier-plain-walk.md`): at a strictly-positive-power certificate, the empirical visit frequency of `i` in `n` i.i.d. samples of the `t₀`-step walk law concentrates around the stationary value with the walk law's own TV distance folded in as the deterministic bias `ρ^{t₀/m}·TV(δ_x, π)` — the same triangle route as the spectral form, the bias supplied by the primitivity rate instead of a caller certificate | — (proved) |
| `empiricalWalkDistribution_tail_selfcontained_of_depth` | derived (hard crust; `#print axioms`-verified 2026-09-02) | **The plain family's self-contained twin** (2026-09-02, `proposals/primitivity-supplier-plain-walk.md`): on a connected support graph with a single odd closed walk, `∃ t₀` past which, for every start simultaneously, `n` i.i.d. simulated walk trajectories of length `s` estimate `stationaryVec A i` to `ε` at `2 exp(−nε²/2)` — no caller-supplied rate certificate anywhere; the PageRank twin's `(α, ε)`-computable display threshold is honestly existential here (the produced `(m, δ)` are witnesses, not functions of the visible parameters) | — (proved) |

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
