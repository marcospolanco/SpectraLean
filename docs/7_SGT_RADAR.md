# SGT Coverage Radar

**Status:** Canonical coverage assessment  
**Last reviewed:** August 23, 2026

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
| 2 | Spectral linear algebra | 4.5 | Sorted spectrum `evals` + monotonicity + `evals_mem_eigvalOf` (**proved**); `secondEval` (matrix-facing λ₂ API) and the trace/Rayleigh pinning tools `eigvalOf_sum_eq_trace`, `eigvalOf_le_of_quadForm_nonpos` **proved** (2026-08-18); eigenbasis orthonormality/completeness and projector algebra **proved**; interlacing **proved** (2026-08-18: `eigen_interlacing_principal_submatrix` retired from axiom, derived from the Courant–Fischer engine through the extend-by-zero padding bridge and the subspace-intersection dimension count; QA pins the window to `0 ≤ 1 ≤ 2` on `K₂` with a singleton submatrix, with both collapsed one-sided bounds refuted); Weyl **proved** (retired from axiom 2026-08-20, `proposals/discharge-perturbation-axioms.md`: the additive bounds `weyl_additive_upper`/`weyl_additive_lower` from this axis's min–max engine plus the bottom-domination mirror `evals_first_mul_dotProduct_le_quadForm`, composed with the operator-norm bridge — gap stability fully hard crust) with Davis–Kahan **proved** (retired 2026-08-21 — see axis 7) and the two-point wrapper **fully hard crust**. **The operator-norm ↔ spectrum bridge is proved** (2026-08-19, `Analysis.OperatorTheory.Resolvent`, proposal `resolvent-calculus-psd.md` Step 0): for every real symmetric matrix, `|λ| ≤ ‖M‖` for all eigenvalues and conversely `‖M‖ ≤ c` when all `|λ| ≤ c`, packaged as `l2OpNorm_eq_max_abs_evals` (`‖M‖ = max |evals hM 0| |evals hM last|`) — the axis's first operator-norm identity, and the finite-dimensional spectral-radius fact for real symmetric matrices; route recorded after the C*-algebra thread `IsSelfAdjoint.spectralRadius_eq_nnnorm` was elaboration-verified **structurally inapplicable** to real matrices (`CStarAlgebra` requires `NormedAlgebra ℂ`), the fallback proved from the eigenbasis machinery (Parseval + eigenaction + `cstar_norm_def` transport). Step 1 added shifted-PSD invertibility (`M + t•1`, `t > 0`, no symmetry needed) and the resolvent identity `(A+1)⁻¹ − (B+1)⁻¹ = (A+1)⁻¹(B−A)(B+1)⁻¹`. Step 2 (2026-08-19) completed the family with the operator-norm bounds — `‖(M + t•1)⁻¹‖ ≤ t⁻¹` for any quadForm-nonneg matrix (no symmetry; the energy route: `t‖y‖² ≤ quadForm M y + t‖y‖² = y ⬝ᵥ x ≤ ‖y‖‖x‖`, a recorded deviation from the sketched eigenvalue transfer) and the `1`-Lipschitz stability `‖(A+1)⁻¹ − (B+1)⁻¹‖ ≤ ‖A−B‖` (Step-1 identity + `norm_mul_le` + the norm bound; QA shows both attained with equality at `K₂`, the energy and spectral routes agreeing at `1`, and the shift/hypothesis guards refuted-on-omission). Step 3 (2026-08-20) completed the program with **injectivity of the resolvent map** — `A ≠ B → (A+1)⁻¹ ≠ (B+1)⁻¹` on quadForm-nonneg matrices (contrapose the Step-1 identity, cancel both invertible outer factors), with the packaged iff `inv_add_one_eq_inv_add_one_iff_of_quadForm_nonneg` stating resolvent equality as a certificate of matrix equality; QA instantiates it at two distinct PSD pairs with both resolvents left-inverse-pinned (`lap2` vs `0`, `lap2` vs `mat2`), and **refutes the hypothesis-free implication** at `A = -1` vs `-1 + nilpotent` (both `+1` shifts singular, both resolvents the junk `0`). Score held at 3.5 at Step 3 (the resolvent family completed within the operator-norm interface already counted at Step 0 — completion, not a new capability family). **Tikhonov regularization in the Laplacian eigenbasis is proved** (2026-08-20, `GraphTheory.Tikhonov`, proposal `tikhonov-shrinkage-filter.md`, zero new axioms): the axis's first *constructed application-facing operator family* — the smoothing filter minimizing `‖x−y‖² + (1/π)·xᵀLx`, defined by the eigenbasis formula with the closed-form eigencoefficient shrinkage identity, the normal equation `(L+π•1) *ᵥ x* = π•y` and its converse characterization, minimality/uniqueness through the strict-convexity decomposition `obj(x)−obj(x*) = ∑_k (1+λ_k/π)(d_k−d*_k)²`, mean preservation (symmetry + `π ≠ 0` only), and the not-a-projection idempotence-failure theorem distinguishing it from `spectralProjector`; the attenuation factor's endpoint behavior corrected against the proposal's sketch (`= 1` exactly at `λ = 0` — the kernel mode untouched — and `< 1` iff `λ > 0`). Re-scored 3.5 → 4.0 with this milestone (a new capability family — a constructed spectral filter with a variational characterization, not packaging and not a completion of the counted resolvent interface; QA pins the minimizer against a hand-solved linear system through the converse characterization). **The two-sided spectral band projectors are proved** (2026-08-20, `GraphTheory.Band`, proposal `spectral-band-projectors.md` Step 1, zero new axioms): the `(a, b]` band as the difference of two `spectralProjector` calls with idempotence through the **nestedness cross-law** `P_{c₁} * P_{c₂} = P_{min c₁ c₂}` (added to `GraphTheory.Spectral` with its ordered forms; the old `spectralProjector_idempotent` re-derived from it at unchanged statement), the complete projector-eigenvector action description (`P_c *ᵥ vᵢ = if λᵢ ≤ c then vᵢ else 0`), and the band mode-selection interface — in-band modes fixed, out-of-band modes annihilated — plus the below-spectrum special case and the covering band. Step 2 (2026-08-20, same proposal) added the **orthogonality layer for disjoint bands**: the two band projectors compose to zero in both orders (the four-term cross-law expansion collapsing under `b ≤ c` — exactly interval disjointness, load-bearing), their images are dot-orthogonal (`bandProjector_inner_eq_zero`), and no nonzero vector is fixed by both (`eq_zero_of_bandProjector_mulVec_eq_self`, the subspace-level reading of "they share no eigenvector"); score held at 4.0 (completion within the band family already counted at Step 1; Steps 3–4 — partition completeness and the Hilbert projection specialization — remain the natural re-score triggers). Step 3 (2026-08-20, same proposal) added **completeness under a partition**: the unconditional telescoping law `∑_{k<n} B(t_k, t_{k+1}) = P_{t_n} − P_{t_0}` for *any* threshold sequence (ordered or not — load-bearing on the band definition's exact difference shape), the covering-family resolution of the identity `∑ B_k = 1` from exactly the two endpoint hypotheses (`t₀` below every eigenvalue, `tₙ` covering them all — both refutable-on-omission), distinct members of a **monotone** family composing to zero (monotonicity deliberately not a hypothesis of the sum identity — it is exactly what the orthogonality statement consumes, making the family a partition), and the consumer's vector decomposition `x = ∑ B_k *ᵥ x`; score held at 4.0 (the same-family completion the Step-1 re-score named as a trigger — the genuinely new capability dimension, consuming Mathlib's Hilbert projection theorem, is Step 4). Step 4 (2026-08-21, same proposal, program complete) added **the Hilbert-projection specialization**: the residual-orthogonality engine `(x − B*ᵥx) ⬝ᵥ (B*ᵥz) = 0` (load-bearing on exactly the two Step-1 facts — symmetry and idempotence), the identification `bandProjector_toEuclidean_apply_eq_orthogonalProjection` (Mathlib's `orthogonalProjection` at the transported band range *is* the band-filtered signal — the SGT center's first consumption of `Analysis/InnerProductSpace/Projection.lean`, through the `toEuclideanLin` transport the resolvent Step-0 record named as precedent), and the closest-point property `norm_sub_bandProjector_apply_le` (`‖e x − e (B*ᵥx)‖ ≤ ‖e x − e y‖` for every fixed point `y` — equivalently every range member — from `orthogonalProjection_minimal` + `ciInf_le`; stated at `EuclideanSpace ℝ V` because the bare `V → ℝ` default norm is the sup norm). QA pins attainment (`= 4` exactly), strict improvement over the zero signal (`4 ≤ 5`, the 3-4-5 triangle), the whole range line `4 ≤ √((3−t)²+16)` with an independent raw-arithmetic cross-check, and refutes the hypothesis-free form at the unfiltered signal. Re-scored 4.0 → 4.5 with this milestone (the capability dimension the two prior records explicitly reserved as the trigger: the spectral-operator layer gains a *characterized closest-point/projection interface* into Mathlib's inner-product-space machinery — every downstream distance-to-band and best-band-approximation claim is now derivable — not another member of the counted band family). Davis–Kahan remains admitted. |
| 3 | Variational and functional methods | 4.0 | `quadForm`/Dirichlet identity and PSD **proved**; `rayleigh` defined; normalized↔combinatorial transfer **proved** (2026-08-17, `VariationalTransfer`: congruence lemma, degree-weighted Rayleigh quotient `rayleigh L_sym (√D y) = (yᵀ L y)/∑ deg·y²`, `normalizedLaplacian_psd`); **λ₂ variational characterization (Courant–Fischer) now proved** (2026-08-18, `lambda2_variational`: `λ₂ = sInf` of the Rayleigh quotient over nonzero vectors ⊥ `onesVec`, for symmetric nonnegative weights — retired from axiom, whose symmetry-only shape was false and is refuted in QA; matrix-world proof through eigenbasis expansion, Parseval, the spectral resolution of `quadForm`, and two sorted-multiset multiplicity pins; the semidefinite Cauchy–Schwarz `laplacian_cauchy_schwarz` is also proved); **general Courant–Fischer min–max proved at every index** (2026-08-18, proposal `prove-courant-fischer.md`: `evals_min_max` with the two witness directions `exists_submodule_forall_rayleigh_le` / `exists_ne_mem_rayleigh_ge_of_finrank_eq` — only symmetry assumed, no positivity or graph structure; the general-`k` multiplicity pins and component-form Rayleigh bounds are new public center API; QA pins both directions on a spectrum-`[1,3]` fixture, derives the top-eigenvalue domination universal through the theorem, and refutes wrong and under-dimensional subspaces plus an interior-index wrong two-dimensional subspace on the path Laplacian). Re-scored 3.5 → 4.0 with this milestone (the fixed-index engine generalized to the full subspace min–max; the axis's remaining named gaps are functional inequalities). Absent: Poincaré, log-Sobolev. |
| 4 | Cuts, expansion, clustering | 4.5 | `vol`/`boundary`/`conductance`/`cheegerConstant` with nonnegativity, GLB, and full cut duality (**proved**, run 10); **the Cheeger *upper* bound (easy direction, `λ₂(L_sym) ≤ 2φ`) is proved** (2026-08-18, `cheeger_upper_bound` retired from axiom) — the volume-centered cut-indicator interface (`cutTestVector`: orthogonality, the general weighted-graph cut-energy identity `xᵀLx = boundary·vol V²`, the norm identity, and the Rayleigh value `boundary·vol V/(vol S·vol Sᶜ)`), instantiated in QA on `K₂` (bound attained: `λ₂ = 2φ = 2`) and on `C₄` (`λ₂ ≤ 1` through the exhaustively computed conductance `1/2`); **the Cheeger *lower* bound (hard direction) is proved** (2026-08-23, `cheeger_lower_bound` retired from axiom at the unchanged statement by the median-split route of `proposals/discharge-perturbation-axioms.md` Steps 1a/1b/1c — the Cauchy–Schwarz core and fused median-part contraction, the interval-integral co-area core `coarea_core`, and the median/level-set/assembly layer: `exists_median` by pure Finset arithmetic, the per-part bound `φ²·d·‖y‖² ≤ E'(y)`, the norm split, the sweep lemma `φ²/2 ≤ R_{L_sym}(x)` for every nonzero `x ⊥ 1`, closed through `secondEval_variational`; explicit axioms 10 → 9; the spectral side had been restated 2026-08-18 at the source-faithful `secondEval (L_sym)` shape after QA refuted the previous `lambda2`-composed side, and is pinned to the classical value `2` on `K₂`). Re-scored 4.0 → 4.5 with this milestone (both directions of the axis's central isoperimetric–spectral family now proved — a new theorem family, the hard direction, not packaging). **The Fiedler-vector interface exists and the sign partition is proved sane (2026-08-18, `GraphTheory.Fiedler`, proposal `fiedler-partitioning.md` Phase A — no new axioms):** `fiedlerVector` (the eigenbasis vector at `lambda2`) with the eigenvector equation, unit norm, and `fiedlerVector_quadForm`; the algebraic-connectivity certificate `lambda2_pos_of_connected` (connected ⇒ `0 < λ₂`, consuming the kernel characterization and both multiplicity pins); and `fiedlerPartition` proved nonempty and proper on connected graphs through the zero-sum identity (QA on the `P₄` barbell — two `K₂` near-cliques joined by a bridge — derives the sign pattern from the eigen equations and computes the partition to be exactly the known good cut `{0,1}` or its complement: boundary `1`, volume `3`, conductance `1/3`). **The Expander Mixing Lemma is proved** (2026-08-19, proposal `decidable-spectral-certificates.md` Step 2, `GraphTheory.Expander` + two generic additions to `GraphTheory.Spectral`; zero new axioms): for symmetric, nonnegative, `d`-regular networks with Laplacian-spectrum hypothesis `μ ≥ max |d − λ₂(L)| |d − λ_max(L)|`, the `(S,T)` cut weight deviates from the population main term `d•|S|•|T|/|V|` by at most `μ • √(|S||T|(|V|−|S|)(|V|−|T|))/|V|` — the axis's first discrepancy/pseudorandomness result, i.e. the quantitative form of "spectral gap ⇒ cut pseudorandomness". Route: a Rayleigh sandwich on `1⊥` (the `d`-regular identity `xᵀAx + xᵀLx = d•‖x‖²` trading the proved `λ₂•‖x‖² ≤ xᵀLx` against the new generic top domination `xᵀLx ≤ λ_max•‖x‖²`), then the sharp bilinear form by the polarization/scaling trick (`a² = Y, b² = X` attains AM–GM equality — no slack), then the variance identity for the geometric factor; no eigenspace split, no kernel case analysis, no affine spectrum transfer. QA (+19 declarations): the spectral hypothesis **derived on the fixture** (test vector, sum-of-squares, PSD) and the bound **attained exactly** on `C₄`'s opposite cut and on the alternating vector — the derived `μ` is tight. Re-scored 3.5 → 4.0 with this milestone (a new theorem family — spectral–combinatorial discrepancy — not packaging; the certified partition-quality guarantee remains Phase B, and multiway/irregular variants remain absent). Step 4 (2026-08-19, QA-only) made the fixture evidence exact: `lambda2 (C₄) = 2` and `λ_max(C₄) = 4` pinned (Poincaré through the lower half of `lambda2_variational`; the alternating vector through `quadForm_le_evals_last`), so `μ(C₄) = 2` *exactly* — the Ramanujan bound `2√(d−1)` attained with equality; `K₃` pinned (`λ₂ = λ_max = 3`, `μ = 1`, strictly Ramanujan, EML attained exactly on both cuts tested) and the `C₆` EML instantiated with derived `μ ≤ 2`, attained on the alternating cut — the Step 0 scope decision's `Kₙ`/`Cₙ` Ramanujan fixture family delivered. Score held at 4.0 (QA strengthening, no new theorem family). > **The certified partition-quality guarantee is delivered** (2026-08-23, `fiedler-partitioning.md` Phase B, pure hard crust, zero new axioms): `cheeger_cut_existence` — on every connected `d`-regular graph, `∃ S` nonempty proper with `conductance S ^ 2 ≤ 2 · lambda2 / d` — the axis's first application-ring certificate (an algorithmically consumable existence guarantee, not just an inequality about an infimum), assembled from the proved sweep lemma at the Fiedler vector, the Rayleigh transfer `R_{L_sym}(f) = lambda2 / d`, and the new `cheegerConstant_attained` (the conductance minimum realized by `Finset.exists_min_image` over the filtered powerset). The proposal's operator gate dissolved with the 2026-08-23 hard-direction retirement, so this is composition of proved pieces, and the score **held at 4.5** per protocol: the certificate's mathematical content is the (already counted) Cheeger family plus a finiteness attainment lemma — completion within the counted family, not a new theorem family; the honest statement-shape deviation is recorded (the sign cut is not certifiable from λ₂ alone; the certified object is the minimizer, and the sweep-level-set extraction is the named strengthening follow-on). QA is load-bearing on the retirement (the Rayleigh transfer cross-checked against the pinned `lambda2 (K₂) = 2`; the regularity hypothesis refuted-on-omission at `d = 100`). **The swept-level-set certified cut is delivered** (2026-08-24, `proposals/sweep-cut-extraction.md`, Phase C in `GraphTheory.Fiedler` + the `SweepExtraction` section of `GraphTheory.Cheeger`; zero new axioms): `fiedler_sweep_cut` — on every connected `d`-regular graph, a *closed superlevel or sublevel set of the Fiedler vector itself* (the object the spectral-partitioning sweep returns, not the non-constructive conductance minimizer of Phase B) satisfies `conductance S² ≤ 2λ₂/d` — through the per-part `sweep_level_extract` (attainment over the finitely many positive values of `y²`, the covering fact that every closed superlevel set equals one at an attained value, a non-strict layer-cake integration cloned from `coarea_core`, Component A) and the median assembly `cheeger_sweep_cut` (same constant 2 as `cheeger_sweep`, witness explicit — a strengthening of the sweep lemma itself, load-bearing on the whole Step-1a/1b/1c chain). **The irregular (volume-weighted) easy direction is proved** (2026-08-25, `proposals/irregular-cheeger-variational-transfer.md` Steps 0+1: `cheeger_upper_bound_normalized` — `secondEval (normalizedLaplacian A) ≤ 2 * cheegerConstant A` on arbitrary symmetric nonnegative positive-degree graphs, no regularity, no connectivity — through the degree-stretched cut indicator `√D · cutTestVector` (orthogonality to the true kernel vector `√D · 1` by the volume identity, no regularity), the new general-kernel `secondEval_le_rayleigh_of_ker`, and the `VariationalTransfer` congruence engine; the same Rayleigh quotient as the regular family, closing arithmetic verbatim; QA on `P₃` with the eigenpair-independent spectral bound and both fences). Held at 4.5 per protocol: the irregular hard direction (`φ²/2 ≤ λ₂` in the volume-weighted measure) remains regular-only — half the irregular statement delivered. Absent: multiway expansion, the irregular Cheeger *hard*-direction statement shape. |
| 5 | Random walks and diffusion | 4.0 | Regular and irregular transition matrices with row-stochasticity **proved**; walk↔normalized similarity and both Laplacian bridges **proved**; the walk-matrix **eigenpair transfer proved** (2026-08-22, `proposals/mixing-time-bound.md` Step 1: eigenpairs conjugate through the similarity in both directions, `walkEvals` certifying each transferred entry a genuine eigenvalue of the non-symmetric walk matrix with explicit nonzero eigenvector witnesses, and `walk_eigvec_expansion` the diagonalizability interface — the axis's named walk-spectrum gap, closed as QA'd hard crust; re-scored 2.5 → 3.0); **reversibility (detailed balance) proved** (2026-08-22, `proposals/reversibility-and-heat-semigroup.md` Phase A: `deg i * P i j = deg j * P j i` with both forms — degree measure and stationary measure `π = deg/vol` — plus the symmetrizability packaging `D * P` symmetric and the regular uniform-measure corollary, zero new axioms, in `GraphTheory.Stationary`); **the ℓ²-mixing proxy defined with its evolution interface** (2026-08-22, `proposals/mixing-time-bound.md` Step 2, the new `GraphTheory.Mixing`: `stationaryVec`/`walkDistribution`/`walkDensity`/`chiSquareDistance` all proved-interface hard crust, `walkDensity_succ` consuming the detailed-balance interface — the density-coordinate evolution `h_{t+1} = P *ᵥ h_t` that the transferred eigenbasis diagonalizes); **the geometric decay engine proved** (2026-08-22, Step 3 component 1: the conjugated-power transfer `√D *ᵥ (Pᵗ *ᵥ g) = (1 − L_sym)ᵗ *ᵥ (√D *ᵥ g)`, eigencoordinate evolution, the Parseval-exact decay identity, and the ℓ²(π) contraction under value-based mode exclusion); and **the χ² mixing statement itself proved — the program's closing theorem** (2026-08-22, Step 3 component 2: `chiSquareDistance_le_of_connected` — `χ²(t, x) ≤ r ^ (2t) · ((π x)⁻¹ − 1)` on connected symmetric-nonnegative positive-degree networks under the rate hypothesis — assembled from the centered density evolution `h_t − 1 = Pᵗ *ᵥ (h₀ − 1)`, the connectivity kernel characterization of `L_sym` (the shelf's `laplacian_kernel_eq_span_onesVec` transferred through the proved congruence `√D L_sym √D = L`, composed with mass conservation), and the delivered contraction; zero new axioms; QA pins the bound **attained exactly** on K₃ at `t = 1, 2` (`1/2 ≤ (1/4)·2`, `1/8 ≤ (1/16)·2` — equalities), the λ* = 1 no-decay behavior on P₃ (rate derived basis-independently from two sum-of-squares certificates pinning the spectrum into `[0, 2]`), and refutes the connectivity-dropped form on a triangle⊕self-loop fixture where the rate hypothesis provably holds at `r = 1/2` yet `χ²(3) = 3/8 > 3/64` — the loop's `μ = 0` mode being exactly the hole connectivity plugs; re-scored 3.0 → 3.5). Heat semigroup **in delivery** (2026-08-23, `proposals/reversibility-and-heat-semigroup.md` Phase B Steps 0–3, the Active table's single High row — its gate resolved by the real external consumer `sgt-gaps.md`: the new `GraphTheory.Heat` defines the matrix-level `heatKernel A t = e^{-tL}` on `laplacian A` with symmetry under `A.IsSymm` through the pin's `Matrix.IsSymm.exp`, the hypothesis-free time-zero identity, the square-zero exponential collapse, **the semigroup law** `heatKernel A s * heatKernel A t = heatKernel A (s + t)` (Step 2, delivered 2026-08-23: hypothesis-free, via `Matrix.exp_add_of_commute` at the commuting negated scalar multiples, QA witnessing the law by two independent routes — hand multiplication of the fixture's closed forms vs. the theorem), and **mass conservation** `heatKernel A t *ᵥ onesVec = onesVec` (Step 3, delivered 2026-08-23: hypothesis-free, through the entrywise-built exponential-series convergence `expSeries_hasSum_exp` — the summability content constructed from scratch because the pin's normed `expSeries_summable'` cannot be applied at matrix type and the pin has no Pi-HasSum lemmas at all — and the kernel-vector engine `exp_mulVec_eq_of_mulVec_eq_zero`, whose per-kernel-vector generality the QA consumes for the per-component no-leakage witness on a disconnected fixture; the raw-vs-theorem two-route conservation check and the non-kernel-vector guard complete the witness set) — zero new axioms; held at 3.5 pending Step 4); and **the heat-kernel *statements* themselves — eigenmode decay and the DC limit — proved, closing the heat family** (Step 4, delivered 2026-08-23: the eigenmode engine `exp_mulVec_eq_smul_of_mulVec_eq_smul` (`M *ᵥ v = μ • v → exp ℝ M *ᵥ v = e^μ • v`, Step 3's convergence consumed at an eigenvector, the kernel engine its `μ = 0` case), `heatKernel_mulVec_eigvecOf` (every eigenbasis vector an eigenvector of `heatKernel A t` at every time, eigenvalue `e^{−t·λᵢ}`), the sorted-spectrum decay monotonicity with the PSD `≤ 1` dissipation bound, the eigenbasis expansion `heatKernel_mulVec_eq_sum` (the spectral-calculus identity in action form), and the payoff **DC limit** `heatKernel_mulVec_tendsto_atTop` (on connected graphs the heat flow of any vector converges to its mean `((∑ j, x j)/|V|) • onesVec` — assembled from PSD, `det L = 0` + `det_eq_prod_eigenvalues`, the kernel characterization, uniqueness-by-orthogonality, and finite-sum limit passage; zero new axioms; QA: two independent routes to the mode-decay statement and to the DC limit on K₂, the new rank-one-idempotent closed form `heatKernel K₂ t = 1 + ((e^{−2t}−1)/2) • L`, the K₂ spectrum pinned `[0,2]` from trace/determinant, and the engine⇄collapse cross-validation at a nonzero eigenvalue; re-scored 3.5 → 4.0 — the named trigger fired, and the continuous-time side of the axis is now a closed capability family: definition, identity, semigroup, conservation, mode decay, convergence). Absent: the ℓ² → total-variation conversion (the mixing proposal's own optional Step 4 — a separate proposal-scale decision) — the axis's only remaining absent category. |
| 6 | Combinatorial and electrical structure | 4.5 | The connectivity/kernel hinge is **proved** (2026-08-18, proposal `electrical-structure-crust.md` step 2 after the re-sequencing): for connected symmetric nonnegative weights, `ker (laplacian A) = span ℝ {onesVec}` (`laplacian_kernel_eq_span_onesVec`, built on `supportGraph` + `SimpleGraph.Walk` induction), with connected and disconnected QA witnesses. **Component structure is complete for weighted graphs** (2026-08-18, proposal step 3): the component-form kernel characterization `L *ᵥ f = 0 ↔ f` constant on each support-graph component (`laplacian_mulVec_eq_zero_iff_forall_reachable`), the kernel-equality bridge `ker (laplacian A) = ker ((supportGraph A).lapMatrix ℝ)`, kernel dimension = component count, and the component-indicator basis (Mathlib's `lapMatrix_ker_basis`/rank theorem inherited through the bridge; QA computes the count to `2` and the basis to `![1,1,0,0]`/`![0,0,1,1]` on the disconnected fixture). **The potential equation is completely characterized on connected graphs** (2026-08-18, proposal step 4): every zero-sum demand is solvable (`exists_laplacian_mulVec_eq_of_sum_eq_zero`, constructive eigenbasis witness `f = ∑_{λᵢ ≠ 0} (vᵢ ⬝ᵥ b/λᵢ)•vᵢ` — the load-bearing consumer of the proved eigenbasis algebra and the step-2 kernel theorem), the unit demand `e u − e v` is solvable (`exists_laplacian_mulVec_eq_single_sub_single`), and the reciprocity identity `w ⬝ᵥ (L *ᵥ f) = (L *ᵥ w) ⬝ᵥ f` (`laplacian_dotProduct_mulVec`) certifies in proved QA form that non-zero-sum demands are unsolvable and that zero-sum does not suffice without connectivity. **Effective resistance is a defined, well-determined quantity** (2026-08-18, proposal step 5, `GraphTheory.Electrical`; Mathlib surveyed: no resistance declaration, no pseudoinverse): `IsEffectiveResistance A u v r` by the potential equation, existence from step 4, uniqueness of `r` at reachability-pair strength, the total function `effectiveResistance` with proved agreement theorems and an honestly QA-witnessed junk fallback, the energy identity at solution and function level (`quadForm L f = f u − f v`; `R = energy`), nonnegativity from PSD, hypothesis-free relation symmetry, and `R u u = 0` unconditional; QA computes `R = 1` on the unit edge, `R = 2` on the 3-vertex path (series edges add), and cross-checks the energy identity against an independently computed energy. **The one-sided Dirichlet bound is proved** (2026-08-18, proposal step 6, program complete): `(f u − f v)² / quadForm L f ≤ R u v` for every test potential of positive energy (`effectiveResistance_ge_sq_div_quadForm`), via the semidefinite Cauchy–Schwarz `laplacian_cauchy_schwarz` (no connectivity hypothesis; the pin's only C–S is the definite inner-product one — polarization route recorded); QA attains equality at both harmonic potentials (`1/1 = 1`, `4/2 = 2`), shows strictness at a non-harmonic potential, refutes the reverse inequality numerically, and witnesses the energy guard. **The potential API is now a routing object** (2026-08-19, proposal `electrical-flow-routing.md` steps 0–1, `GraphTheory.ElectricalFlow`; Mathlib re-surveyed: no flow/circulation/divergence API anywhere in the pin): `electricalCurrent` (Ohm's law on ordered pairs, conductance convention), `flowDivergence`, the predicates `IsFlowOn` (antisymmetry + zero-conductance support — the support conjunct QA-witnessed load-bearing by an edgeless-network phantom that satisfies every other unit-flow condition) and `IsUnitFlow`, and the Kirchhoff bridge `flowDivergence_electricalCurrent` + headline `isUnitFlow_electricalCurrent`: every unit-demand potential induces a valid unit flow (load-bearing on the center's exact Laplacian sign convention through `laplacian_mulVec_apply`); QA computes the `K₂` and 3-path currents and divergences from the definitions with internal-vertex conservation `0`, and refutes current antisymmetry on an asymmetric network (`2 ≠ 1`). **Flow energy agrees with the Dirichlet energy and the resistance it routes** (2026-08-19, proposal step 2): `flowEnergy` with the explicit zero branch and the mandatory `1/2` ordered-pair factor; `flowEnergy_electricalCurrent` (symmetry-only — the entrywise Ohm's-law algebra needs no nonnegativity, QA-witnessed both ways), `flowEnergy_nonneg` (nonnegativity load-bearing, QA exhibits energy `-1` on a symmetric negative-weight network), and `flowEnergy_electricalCurrent_eq_effectiveResistance`; QA pins energies `1`/`2` from the raw definitions against independently computed Dirichlet energies and pinned resistances, guards the `1/2` factor numerically (raw ordered-pair sum `2 ≠ 1`), pins the step-1 phantom's zero energy, and exhibits the zero-energy competitor — an antisymmetric unit-divergence flow through zero-conductance pairs with energy `0 < 1` = the real resistance, excluded by the support conjunct alone. **Thomson's principle is proved** (2026-08-19, proposal step 3): `effectiveResistance A u v ≤ flowEnergy A θ` for every valid unit flow (`effectiveResistance_le_flowEnergy`) — the electrical current is the energy minimizer — via the divergence-free superposition lemma `flowEnergy_add_of_flowDivergence_eq_zero` (discrete integration by parts; stated with **no hypotheses on `A`**, only the perturbation's flow properties), `isFlowOn_sub`/`flowDivergence_sub` linearity, and `flowEnergy_nonneg`; QA witnesses attainment at the split current on the triangle (`K₃`, `R = 2/3` = the current's energy, computed from the raw definitions), a **strict competitor** (the detour flow around the two-edge path: valid `IsUnitFlow`, energy `2`, `2/3 < 2`), and the superposition decomposition `2 = 2/3 + 4/3` with all three values computed independently. **Rayleigh monotonicity in conductance form is proved** (2026-08-19, proposal step 4): entrywise `A ≤ B` on connected symmetric nonnegative networks gives `effectiveResistance B u v ≤ effectiveResistance A u v` (`effectiveResistance_le_of_le`) — the first *network-comparison* theorem on the axis (it relates two graphs, not two objects of one graph) and the ICP-facing fact that adding capacity cannot worsen the certified energy cost of electrical routing — via the two new reusable interfaces `isFlowOn_of_le` (flow-space growth: a flow supported on `A` is a flow on every `B ≥ A ≥ 0`, support load-bearing) and `flowEnergy_le_of_le` (raising conductances lowers dissipated energy, termwise; support load-bearing again on the `A i j = 0 < B i j` branch), composed with Thomson on `B` at the transferred `A`-current and the step-2 energy identity; QA certifies the proposal's capacity-increase fixture `1 → 1/2` strict with the **orientation guard** (the reverse inequality `1 ≤ 1/2` refuted numerically — weights are conductances), the competitor transfer instantiated on computed objects, and a partial increase on the triangle (`2/3 → 2/5`, new value pinned by an independent potential). **The program is complete (2026-08-19, step 5)**: `increaseConductance` raises one undirected pair's conductance (both ordered entries together), and the one-hypothesis headline `effectiveResistance_le_increaseConductance` packages the monotonicity as the ICP-facing capacity-reinforcement theorem — only the original network's connectivity is hypothesized, the reinforced network's derived by `supportGraph_connected_of_le` (support graphs grow along entrywise domination — `supportGraph_le_of_le`, no nonnegativity needed — and Mathlib's `SimpleGraph.Connected.mono` lifts connectedness); QA is the release example: the Mathlib `Fin 3` path graph through `toWAdj`, the reinforcement computed to the concrete doubled-path matrix, the reinforced resistance `3/2` pinned by an independent potential witness, and the decrease certified strict `3/2 < 2`. Re-scored 3.5 → 4.0 per the step-3 recorded reservation (the axis rises when Thomson/Rayleigh land; both have now landed); held at 4.0 at step 5 (packaging, not new mathematics). **Foster's theorem is proved** (2026-08-19, proposal `spectral-graph-sparsification.md` Phase A, `GraphTheory.Foster`; zero new axioms — `#print axioms` reads only the three standard axioms): `(∑ i, ∑ j, A i j * R i j) / 2 = card V − 1` on every connected symmetric-nonnegative network, via the proposal's pseudoinverse-free eigenbasis route (the per-pair spectral sum `effectiveResistance_eq_sum_eigbasis` = energy identity + `quadForm_eigvalOf` + self-adjointness; the double-sum swap with per-eigenvector Dirichlet evaluation `∑_{i,j} A i j (v_k i − v_k j)² = 2 λ_k`; and the one-kernel-index count `card_filter_eigvalOf_laplacian_eq_zero` against `laplacian_kernel_eq_span_onesVec`) — the first **global network identity** on the axis, tying the electrical quantities to the combinatorial spanning-tree count; the sparsification-facing leverage scores are defined with their probability normalization proved (`sum_leverageScore_eq_two`; QA pins the `K₃` edge leverage `1/3` and the `K₄` edge `1/6`). Re-scored 4.0 → 4.5 with this milestone (a new theorem family — global identities — not packaging; QA witnesses the ordered-pair double-counting factor on both cliques, `4 ≠ 2` on `K₃` and `6 ≠ 3` on `K₄`, so a statement shape dropping the `/ 2` would be refuted). **The resistance metric is proved** (2026-08-24, proposal `resistance-metric.md`, backlog item 7's two named non-gated residuals, `GraphTheory.Electrical`; zero new axioms): the **maximum principle** for unit-demand potentials (`min (f u) (f v) ≤ f x ≤ max (f u) (f v)`, by diffusion-form propagation — `laplacian_mulVec_apply` + nonneg-termwise-zero + walk induction, the kernel-characterization argument run at an inequality), the definiteness residual `effectiveResistance A u v = 0 ↔ u = v` (positivity off-diagonal via the one-sided Dirichlet bound at the indicator `e u`, whose energy `∑_{j≠u} A u j` is positive by connectivity), and the **triangle inequality** `R u w ≤ R u v + R v w` (the polarization cross term `f v − f w ≤ 0` of the `f + g` assembly — the Step-0 survey records that the eigenbasis route yields only the *root*-triangle, so the maximum principle is the mathematical crux, not a convenience); with the earlier nonnegativity/symmetry/self-distance laws this makes `effectiveResistance` a genuine metric on every connected network (the classical resistance distance). Held at 4.5 (the metric's named gaps close, but the axis's absent list still holds Matrix–Tree and Kirchhoff; QA fences `hnonneg` across all three new theorems on one signed fixture). Absent: spanning-tree enumeration (Matrix–Tree), and the Kirchhoff loop/cut-space theorems. |
| 7 | Perturbation, randomness, algorithms | 4.0 | Weyl **proved** (retired 2026-08-20); **Davis–Kahan proved** (retired from axiom 2026-08-21, `proposals/discharge-perturbation-axioms.md` Step 1 complete — explicit axioms 11 → 10: the Duhamel/exponential-integral route, components `Analysis.OperatorTheory.Perturbation.{ProjectionGap,Duhamel}` — the equal-rank projector identity `‖P − Q‖ = ‖(I−Q)P‖` and the Duhamel bound `‖(I−Q)P‖ ≤ ‖E‖/(b−a)` from the vector-level heat semigroup, scalar pairing FTC, and cluster-filtered Parseval damping, with the eigenvalue-tie cases collapsed through the proved Weyl additive bound; `davis_kahan_sin_theta` at its unchanged statement now reads only `propext, Classical.choice, Quot.sound`; the derived chain's `davisKahanTwoPoint` **fully hard crust** and `eventStreamProjectorDrift` conditional on `matrix_azuma_hoeffding` alone — the axis's first calculus-based (FTC/integral) proof technique, re-scored 3.5 → 4.0); scalar + matrix concentration **admitted** with the **derived** event-stream tail. **A verified numerical/spectral algorithm driver now exists (2026-08-19, decidable-certificates Step 3, `GraphTheory.SpectralCertificates`):** proof-carrying λ₂ upper-bound certificates — a ℚ specification checker with a proved soundness theorem consuming `lambda2_variational`, a kernel-`decide`able integer cross-multiplied twin (fractional variant included), and proved cross-multiplication bridges making the specification reachable from kernel-verifiable arithmetic — with C₄ QA demonstrating the full chain (`decide`d integer data → verified `lambda2 ≤ 2`, `≤ 5/2`). Re-scored 3.0 → 3.5 with this milestone (the axis's named absent category "numerical/spectral algorithm drivers" gains its first verified occupant — a new capability family, not packaging; random-graph models remain absent). Step 4 (2026-08-19, QA-only) completed the demonstration: the certificate chain kernel-decided at the second required size (`C₆`: `lambda2 ≤ 1` end-to-end from `decide`d integer data) and, on `C₄`, witnessed **exactly tight** — the checker accepts precisely at the true `lambda2 = 2` (pinned by a Poincaré inequality) and rejects every integer bound below it. Score held at 3.5 (verification strengthening of the existing occupant, no new capability family). |
| 8 | Adjacent systems interfaces | 1.0 | Dynamics exist only as the retained compatibility example (`Derived.{EventStream,ProjectorDrift}`, conditional on three axioms; per-step axiom deprecated). Thermodynamics/statistical mechanics gated, absent. |

**Weakest axes:** 8 (adjacent systems — deliberately gated) and 5
(random walks — now at 4.0: the full mixing-time program (eigenpair
transfer, ℓ²-mixing proxy, geometric decay engine, the closing χ²
mixing bound) *and* the complete continuous-time heat-kernel family
(`e^{-tL}` with identity, semigroup law, mass conservation, eigenmode
decay, and the connected-graph DC limit — the reversibility proposal's
Phase B, closed 2026-08-23 as hard crust with two-route QA) are
delivered as proved hard crust; the axis's only remaining absent
category is the ℓ² → TV conversion, a separate proposal-scale
decision).
Axis 6's electrical program is complete and now carries a global
network identity (4.5, 2026-08-19; Thomson, Rayleigh, the step-5 ICP
capacity-reinforcement packaging, and Foster's theorem all landed per
the recorded reservations); the resistance metric and
Matrix–Tree/Kirchhoff remain there. Axis 4 now carries the Expander
Mixing Lemma (2026-08-19, with tightness witnessed in QA) and, as of
2026-08-23, **both Cheeger inequalities proved** (4.5) — the hard
direction's retirement completes the axis's central
isoperimetric–spectral family — **and, later the same day, the
certified partition-quality guarantee** (`cheeger_cut_existence`, the
Fiedler Phase B cut-existence certificate at hard-crust trust level;
held at 4.5 per protocol as composition within the counted family);
multiway expansion, the swept-level-set certified cut, and the
irregular statement shape remain its nearest completions.

## Assurance radar

| Axis | Score | Evidence |
|------|------:|----------|
| Proved depth | 3.5 | Interfaces and algebra are hard crust (projector algebra, cut duality, all Laplacian/normalized/walk bridges, gap stability, electrical structure through the one-sided Dirichlet bound and the flow/Kirchhoff-conservation interface (`isUnitFlow_electricalCurrent`, 2026-08-19) with its flow-energy agreement (`flowEnergy_electricalCurrent` and the unit-demand identity `flowEnergy_electricalCurrent_eq_effectiveResistance`, 2026-08-19) **and Thomson's principle** (`effectiveResistance_le_flowEnergy` over every valid unit flow via the divergence-free superposition lemma `flowEnergy_add_of_flowDivergence_eq_zero` — hypothesis-free on `A` — plus flow-space linearity; QA: attainment, strict competitor, decomposition, 2026-08-19) **and Rayleigh monotonicity** (`effectiveResistance_le_of_le`, 2026-08-19 — the conductance-form network comparison `A ≤ B ⇒ R_B ≤ R_A`, via flow-space growth `isFlowOn_of_le` and the energy comparison `flowEnergy_le_of_le`, composed with Thomson on `B`; QA: capacity increase `1 → 1/2` certified strict with the orientation guard, partial increase `2/3 → 2/5` on the triangle), plus the one-hypothesis capacity-reinforcement packaging `effectiveResistance_le_increaseConductance` with the `supportGraph_connected_of_le` connectivity adapter (2026-08-19, completing the flow program), the Fiedler-vector/sign-partition interface of Phase A incl. the algebraic-connectivity certificate `lambda2_pos_of_connected`, 2026-08-18, and the Woodbury matrix-update identity proved from Mathlib, 2026-08-18; **the Expander Mixing Lemma and its Rayleigh-sandwich bridge are hard crust** (2026-08-19, `expander_mixing_lemma` with the operator bound on `1⊥`, the sharp bilinear form, the generic top Rayleigh domination `quadForm_le_evals_last`, and the `d`-regular identity `quadForm_add_quadForm_laplacian`)); **Weyl's inequality is hard crust** (retired 2026-08-20, `proposals/discharge-perturbation-axioms.md`: `weyl_inequality` proved at its unchanged axiom statement from the additive window via the min–max engine's two witness forms plus both Rayleigh domination bounds, composed with the operator-norm bridge — with the public additive interfaces `weyl_additive_upper`/`weyl_additive_lower`); the operator-norm bridge and the resolvent calculus are hard crust too (2026-08-19, `Analysis.OperatorTheory.Resolvent`: `l2OpNorm_eq_max_abs_evals` with both directions, shifted-PSD invertibility `isUnit_det_add_smul_one_of_quadForm_nonneg`, `resolvent_identity_sub`, and — Step 2, same day — the resolvent norm bound `l2OpNorm_inv_add_smul_one_le_inv_of_quadForm_nonneg` (general `t`, no symmetry, energy route) and the Lipschitz bound `l2OpNorm_resolvent_sub_le_of_quadForm_nonneg`; and — Step 3, 2026-08-20, completing the program — the resolvent-map injectivity `resolvent_map_injective_of_quadForm_nonneg` with its core form `eq_of_inv_add_one_eq_inv_add_one` and the certificate iff `inv_add_one_eq_inv_add_one_iff_of_quadForm_nonneg`); the *variational* engine is proved in full generality (`lambda2_variational` + its general-operator form `secondEval_variational`, 2026-08-18, and the general Courant–Fischer min–max at every index — `evals_min_max` with both witness directions — later the same day, no positivity or graph hypotheses), the *Cheeger easy direction* is proved on top of it (`cheeger_upper_bound`, retired the same day), and **Cauchy interlacing is proved on top of the min–max engine** (`eigen_interlacing_principal_submatrix`, retired 2026-08-18 — the engine's first named consumer, consuming both witness directions through the extend-by-zero padding bridge), so the remaining admitted engines are the Cheeger hard direction and concentration — each with documented statement differences (Weyl left this list 2026-08-20; **Davis–Kahan left it 2026-08-21** — `davis_kahan_sin_theta` proved by the Duhamel/exponential-integral route, the equal-rank projector identity plus the heat-semigroup FTC assembly, with the equal-rank identity itself a new hard-crust gap-metric theorem). |
| Axiom minimization | 4.5 | 9 explicit axioms, all cited and indexed (the row-head count had drifted stale at 9 across the 2026-08-22 Perron–Frobenius admission — repaired with this sync; the count reached 10 on 2026-08-20 with the Weyl retirement — `weyl_inequality` proved at its unchanged statement from the Courant–Fischer engine plus the operator-norm bridge, `proposals/discharge-perturbation-axioms.md`; the perturbation bridge's admitted set is now Davis–Kahan alone, and the derived projector-drift chain is conditional on two axioms instead of three); `spectral_gap_stability`, `hoeffding_iid`, `bernstein_iid` converted from admitted to proved; **`lambda2_variational` retired from axiom to proved theorem (2026-08-18) — the first axiom removed by proof rather than deprecation — and `cheeger_upper_bound` retired the same way one milestone later** (the Cheeger easy direction, proved from the generalized `secondEval_variational`; both false pre-repair shapes refuted in QA); **`woodbury_identity` retired 2026-08-18 as an emergency correctness repair — the first retirement motivated by the axiom being verified *false* rather than merely unproved, proved from Mathlib's `Matrix.invOf_add_mul_mul` at zero local proof cost**; **`sherman_morrison` retired 2026-08-18 as the `k = Fin 1` specialization of the proved Woodbury theorem — a pure proof task at unchanged name/hypotheses (the statement had been verified correct against the repaired Woodbury shape first), completing the matrix-update bridge at zero axiom cost**; **`eigen_interlacing_principal_submatrix` retired 2026-08-18 — Cauchy interlacing proved from the locally proved Courant–Fischer engine, the engine's first named consumer and the first SGT-center retirement (all prior retirees were variational, update-identity, or derived statements)**; `spectral_persistence` deprecated 2026-08-17 with a migration note and removed 2026-08-20 (zero non-QA consumers throughout; the derived two-endpoint chain covers the motivating use). Net trend 26 → 19 → 18 → 17 → 16 → 15 → 14 → 13 → 12 → 11 → 10 → 9 → 10 → 9 (the 2026-08-21 step is `davis_kahan_sin_theta`, proved by the Duhamel route of `proposals/discharge-perturbation-axioms.md`; the 2026-08-22 down-step is `subgaussian_tail_bound`, the **second false-axiom repair retirement** after Woodbury — the mandated Step 0 spike proved the old `subgaussianNorm ≤ K`-shaped axiom materially false through two independent junk mechanisms (`Real.sInf_empty` vacuity; `integral_undef` junk-zero MGF integrals making the defining set full for heavy tails), refuted in QA with the old hypotheses satisfied, and the theorem restated at the same name/conclusion with the moment integrable — the falseness category is empty again among checked statements, and the first measure-theoretic retirement landed; the 2026-08-22 up-step is the Perron–Frobenius admission (the directed axis' second spectral toolkit — a deliberate admission, not drift); the 2026-08-23 down-step is `cheeger_lower_bound`, the Cheeger hard direction proved at the unchanged statement by the median-split route of `proposals/discharge-perturbation-axioms.md` — the discharge program complete: Weyl, Davis–Kahan, and both Cheeger directions all proved; the count also passed through 11 on 2026-08-20 with the operator-directed `spectral_persistence` removal, an editorial deletion rather than a proof retirement). Score held at 4.5 (a retirement within the already-cited-and-QA'd admitted set; the falseness category stays empty). Score 4.5 (re-scored 4.0 → 4.5 at the Woodbury repair: the false-axiom category is now empty among statements whose truth has been checked, and the false Woodbury shape was removed rather than merely replaced; the Sherman–Morrison and interlacing retirements continue the trend without crossing a new threshold — the Core update-identity bridge and the interlacing window are now axiom-free; the Weyl retirement likewise continues the trend — the first *perturbation-bridge* retirement, but within the same cited-and-QA'd admitted set rather than a new threshold; the subgaussian repair holds the score — the second false-axiom repair confirms the falsification discipline works, but the discovered falseness itself is not minimization progress to score). |
| Mathlib interoperability | 4.5 | Native `Matrix`, `IsSymm`, `Matrix.L2OpNorm`, `Matrix.PosSemidef`, `ProbabilityTheory.IndepFun`, `OrthonormalBasis`; the matrix-first representation is bridged in **both** directions and mutually consistently — `supportGraph : WAdj → SimpleGraph` (2026-08-18, consumed by the proved kernel characterization) and `SimpleGraph.toWAdj` (2026-08-18, `GraphTheory.SimpleGraphAdapter`), tied by the proved roundtrip `supportGraph (toWAdj G) = G`; through the agreement `laplacian G.toWAdj = G.lapMatrix ℝ`, Mathlib's unweighted kernel/reachable and component-count results are transferred onto the Scaffold side (`laplacian_toWAdj_mulVec_eq_zero_iff_reachable`, `finrank_ker_laplacian_toWAdj`), and every center theorem becomes callable on Mathlib graphs. Remaining documented deviation: `MatrixMDS` pending a Mathlib filtration API. |
| QA | 4.0 | 2152 declarations across 54 modules (count synced 2026-08-25 with the irregular-Cheeger delivery, `IrregularCheeger_QA` a new file at 85 — the first volume-weighted Cheeger statement witnessed at every level on genuinely irregular input: the `P₃` fixture (degrees `1, 2, 1`) with the conductance side computed by hand (every cut's conductance `1`, `cheegerConstant = 1`), the test-vector layer verified entrywise (the stretched cut indicator `![3, -√2, -1]`, its kernel orthogonality by both the new theorem and raw arithmetic, its norm `12` raw and as `vol S · vol Sᶜ · vol V`, its energy `16` by **three independent routes** — raw combinatorial arithmetic, the congruence engine, and the delivered cut energy identity); the spectral side bounded **independently of the theorem** through the eigenpair witness `![1, 0, -1]` at eigenvalue `1` (a route through the new general-kernel lemma at a vector *not* orthogonal to `onesVec` — the discrimination witness `2 - √2 ≠ 0` pinning why the onesVec engine cannot express the irregular route); the **regular-recovery tight check** on `K₂` (`2 ≤ 2 · 1` through the cone agreement and the delivered pin); and two proved-form fences — the PSD drop on the general-kernel engine (`diag(-1, 0)`, sorted spectrum `[-1, 0]` and Rayleigh `-1` both pinned, conclusion `0 ≤ -1` false, exactly `hpsd` isolated) and the degree drop on the headline (all-zero adjacency: every conductance junk-zero, `λ₂ (normalizedLaplacian 0) = λ₂ (1) = 1` pinned by trace/determinant, conclusion `1 ≤ 0` false, exactly `hd` isolated); held 4.0 per protocol — quantitative strengthening within the already-counted cuts/expansion QA pillar). Earlier: 2067 declarations across 53 modules (count synced 2026-08-25 with the magnetic-Laplacian delivery, `Magnetic_QA` a new file at 16 — the shelf's first complex-valued object witnessed at every level: the asymmetric-flux fixture with the raw phase-weighted entries (`W 0 1 = -2`, `W 1 0 = I`), the operator's genuinely complex conjugate-pair off-diagonal entries (`1 ± I/2`) with Hermitian verified on directed input, the energy identity pinned numerically at `5` by the theorem route, and the zero-phase/symmetric-cone agreements pinned entrywise; the **frustrated-vs-consistent kernel pair** — the triangle with one `π`-flux edge forces the kernel *trivial* (positive definiteness at form level, no eigenvalue machinery) while the same flux on `K₂` leaves the antipodal phase potential in the kernel through the gauge iff, cross-checked by the raw vanishing energy (the pair together exhibiting that the characterization discriminates); the classical bridge (constants in the zero-phase kernel, the antipodal vector provably outside it at energy exactly `4` — the flux is what moved the kernel); and the **nonnegativity fence** (symmetric signed input refutes PSD in proved form at `-1 < 0` with every other hypothesis vacuous — exactly `hA` isolated, the signed-graph surface marked); held 4.0 per protocol — quantitative strengthening within the already-counted directed-axis QA pillar). Earlier: 2051 declarations across 52 modules (count synced 2026-08-24 with the primitive-power-convergence delivery, `DirectedMixing_QA` a new file at 30 — the admission's mandated fence witnessed at every level: the reducible-fixture positive witness with the power-iteration limit pinned to the raw-verified uniform PageRank value `1/4` and the second iterate computed completely raw at `3/16 < 1/4` (the sequence visibly in motion toward its limit); the **2-cycle periodicity refutation** — nonnegative, row-stochastic, *irreducible*, with the uniform stationary distribution verified raw, primitivity proved to fail, and the power action proved to have *no limit at all* (even/odd subsequences at `e₀`/`e₁` through `Tendsto.comp` subsequence extraction), `P2_fence_isolation` collecting every other axiom hypothesis as verified — exactly `hprim` isolated, the convergence-form mirror of `strict_dominance_refuted_QA`; the irreducibility transfer cross-checked against the delivered single-arc route; and the `onesVec` coherence join *deriving* the mass fact `π ⬝ᵥ 1 = 1` from the axiom against the raw sum; held 4.0 per protocol — quantitative strengthening within the already-counted directed-axis QA pillar). Earlier: 2021 declarations across 51 modules (count synced 2026-08-24 with the sweep-cut-extraction delivery, QA +22 across `Cheeger_QA` (+18: four `C₄` conductance pins, the two sweep-family characterizations pinning exactly which sets the theorem's family constraint admits, three theorem instantiations with numeric companions, the orthogonality fence refuted in proved form on the constant vector whose sweep family has no nonempty proper member at all, and the `cycPos` layer forcing the per-part extracted set through its level-membership iff) and `Fiedler_QA` (+4: the identified swept cut on `K₂`, the sweep-family characterization through the Fiedler antisymmetry pins — on an eigenvector with equal entries the family would be *empty* — and the optimality tie `conductance S = cheegerConstant = 1`); held 4.0 per protocol — quantitative strengthening within the already-counted cuts/expansion QA pillar). Earlier: 1999 declarations across 51 modules (count synced 2026-08-24 with the resistance-metric delivery, `ResistanceMetric_QA` a new file at 28 — the resistance-metric residuals witnessed at every level: the triangle's **equality case** pinned on the 3-path (`2 = 1 + 1` — any proof route with a slack constant dies there, series resistances adding exactly) with the degenerate `v = u` instantiation exercising the theorem's self-distance branch; the **strict case** on the reused `K₃` pins (`2/3 < 4/3`); the confinement/definiteness positive witnesses at the actual unit-current potential `![2,1,0]` (voltage difference the pinned `R = 2`, interior value pinned strictly between the boundary values, both confinement halves instantiated at every vertex); and **one signed fixture fencing `hnonneg` across all three theorems** (`![0,1,1;1,0,−1;1,−1,0]`: symmetric, support graph connected, NOT nonnegative — in-file solution-shape analysis pins `R(0,1) = 0` at distinct vertices with definiteness **refuted in proved form**, `R(0,2) = 0`, `R(2,1) = −2` with the triangle **refuted** at `¬(0 ≤ 0 + (−2))`, and confinement **refuted** for every solution at the interior vertex) — the nonnegativity hypothesis load-bearing everywhere, exactly that hypothesis isolated; held 4.0 per protocol — quantitative strengthening within the already-counted electrical QA pillar). Earlier: 1971 declarations across 50 modules (count synced 2026-08-24 with the cluster-projector-*symmetric* delivery, `ClusterProjector_QA` 28 → 46 — the two-sided rank-free constant-2 set-form difference theorem witnessed at every level: the **unequal-rank non-interval witness** `S = {0,5}` rank 2 on `clusterA` vs `T = {5}` rank 1 on `bm` with both flank separations discharged at two-pair center/radius data (the delivered equal-rank family's hypothesis exhibited failing on the very fixture the new theorem covers, ranks pinned 2 ≠ 1 through the supplier, theorem bound `≤ 4` via the imported perturbation norm against the independent raw lower `1` at `e₀` from entrywise projector pins); the ε = 0 attainment through the new theorem with both flanks genuinely discharged; the **two-sided fence** on the interior-gap configuration where *each* `hfar` flank is refuted in proved form at its own interior eigenvalue while both `hnear` sides hold and the hypothesis-free conclusion dies at norm `≥ 1` — the two-sidedness itself exercised; and the ring-identity coherence witness (the composition's identity pinned entrywise on the witness projectors); held 4.0 per protocol — quantitative strengthening within the already-counted perturbation QA pillar). Earlier: 1953 declarations across 50 modules (count synced 2026-08-24 with the cluster-projector delivery, `ClusterProjector_QA` a new Perturbation-domain file at 28 — the set-valued spectral projector and its Davis–Kahan pair witnessed at every level: the **non-interval pin** `P_{{0,11}} = diag(1,0,1)` on the imported `diag(0,5,11)` fixture — a subspace no window expresses, reached through a four-lemma composition (capture at sets, the complement law, the band agreement, the imported threshold pin), with the idempotence/action/disjointness interface witnesses and the rank counts (2/1/2/2) through the trace route; the **non-interval difference instance** at exact-fit `c = 11/2, r = 11/2, δ = 1` (both in-`S` eigenvalues at distance exactly `r`, the single out-of-`T` eigenvalue at exactly `r + δ`) with the theorem bound `≤ 1` joined against the independent raw lower `1 ≤ ‖P − Q‖` at `e₀` (the difference pinned entrywise to `diag(1,−1,0)`); the ε = 0 attainment at singleton clusters with the out-of-`T` separation genuinely discharged (distances 5 and 6 at δ = 1/2); and the **`hfar` fence on the interior-gap configuration** — the proposal's recorded obstruction itself (an out-of-`T` eigenvalue inside A's cluster range at distance `11/2 < 6`) exercised as a hypothesis fence with ranks equal 2 = 2, `hnear` verified, and the hypothesis-free conclusion refuted at norm ≥ 1; held 4.0 per protocol — quantitative strengthening within the already-counted perturbation QA pillar. Earlier: 1925 declarations across 49 modules (count synced 2026-08-24 with the band-Davis–Kahan *symmetric*-form delivery, `BandDavisKahanSymm_QA` a new Perturbation-domain file at 17 on the **public** cluster fixtures — no new Fin 3 machinery needed: the **unequal-rank witness** with ranks pinned 2 ≠ 1 through the delivered supplier (the delivered difference family's hypothesis exhibited failing on the very fixture the new theorem covers; raw norm ≥ 1 through an in-file eigen-equation support pin plus the component action; bound `≤ 2·7/(1/2) = 28`), the constant-2 cost exhibited numerically on the equal-rank rotated fixture (delivered `≤ 1`, new `≤ 2`, raw `√(1/10)`), the ε = 0 attainment at genuinely distinct windows cross-checked by the imported raw zero pin, the **`hsepAB`-isolated fence** (the mirror separation provably vacuous-holding, `Q = 1` through `bandProjector_eq_one`, the hypothesis-free conclusion refuted at `‖P − 1‖ ≥ 1` — the mirror of the cluster QA's fence, so both separation sides are now isolated across the QA family), and the decomposition-coherence witness (the consumed ring identity's action-level content on rotated input, both composite parts computed from imported pins); held 4.0 per protocol — quantitative strengthening within the already-counted perturbation QA pillar. Earlier: 1908 declarations across 48 modules (count synced 2026-08-24 with the band-Davis–Kahan *cluster*-form delivery, `BandDavisKahanCluster_QA` a new Perturbation-domain file at 35 — the pairwise/YWS-literal separation witnessed at every level, with an in-file Fin 3 spectral layer (distinct-entry diagonals force eigenvector support onto single coordinates, orthonormality forces eigenvalue classes to be singletons): the **interior witness** on `diag(0,5,11)` vs `diag(1,2,4)` where the closure-separation shape of the delivered theorem is *refuted in proved form* (`7 ≤ 4` false at the interior 4-mode) while the pairwise hypothesis discharges and both band projectors pin entrywise to `diag(1,1,0)` (the delivered form's unreachable configuration covered, distance exactly `0` against the bound `≤ ‖A−B‖ ≤ 7`); the rotated two-route witness (bound `≤ 1` vs the imported raw `√(1/10)`); the ε = 0 attainment at genuinely distinct windows `(-1,2]` vs `(-1/2,5/2]` through the new capture-equality lemma; and the **separation fence refuted in proved form** with ranks equal and every guard verified — exactly `hsep` isolated, the mirror of the sibling's rank fence; held 4.0 per protocol — quantitative strengthening within the already-counted perturbation QA pillar. Earlier: 1873 across 47 modules, synced with the band-Davis–Kahan *difference*-form delivery, `BandDavisKahanDiff_QA` a new Perturbation-domain file at 21 — the sin-Θ (subspace-distance) form witnessed at every level: the rotated positive witness with the rank equality supplied through the new public rank supplier and the distance pinned from below by `1/√10` completely independently (the sign-independent eigenbasis resolution `Q *ᵥ e₀ = ![9/10, −3/10]`) against the theorem's `1` upper bound, the **identity-coherence witness** (`(I−Q)·P` and `P−Q` actions pinned equal by two independent raw routes — the consumed equal-rank identity's content exhibited numerically), the ε = 0 attainment with separation genuinely holding, the margin-corollary instance at δ = 1, and the **rank fence refuted in proved form** (A = B = diag13, windows empty vs occupied, ranks 0 ≠ 1 through the supplier, every other hypothesis verified — exactly `hrank` isolated); held 4.0 per protocol — quantitative strengthening within the already-counted perturbation QA pillar. Earlier: `BandDavisKahan_QA` a new Perturbation-domain file at 20 — the bounded-window Davis–Kahan product bound witnessed at every level: the rotated 2×2 positive witness with `‖Q * P‖` pinned from below by `1/√10` completely independently of the theorem (eigenbasis resolution with eigen-equation direction constraints, no `eigvecOf` value assumed) against the delivered `3/4` upper bound, the ε = 0 commuting case attained exactly, the overlapping-window fence refuted in proved form with every `hsep`-shaped hypothesis exhibited impossible, and the mirror orientation instantiated at δ = 1/2; held 4.0 per protocol — quantitative strengthening within the already-counted perturbation QA pillar. Earlier: `PolyFilter_QA` a new file at 28 — the Chebyshev layer's second consumer's witnesses: the affine exact filter driving the transfer engine to ε = 0 with both sides pinned raw (two routes to one statement), the power and Chebyshev ε constants *attained* at the out-mode (`(1/3)^d` and `1/3`/`1/17` — no smaller ε can hold for these designs at this fixture), the power-vs-Chebyshev rate comparison `1/17 < 4/9` proved at one gap, and the out-of-band filter-quality hypothesis **refuted in proved form** (a filter perfect in-band whose conclusion fails, the difference's operator norm lower-bounded at `1 > 1/2` through the fixed unit vector — the `abs_eigvalOf_le_l2OpNorm` technique at a literal eigenvector); `#print axioms` on all 37 declarations reads only the standard three — held). Earlier: 1804 declarations across 44 modules (count synced 2026-08-24 with the PageRank delivery, `PageRank_QA` a new file at 89 — the second Perron–Frobenius consumer's witnesses: the reducible two-edge fixture's uniform PageRank `(1/4,1/4,1/4,1/4)` verified **completely raw** against pinned entries (all 16 Google entries pinned) with the `∃!` join identifying every stationary distribution with the hand value — on the very fixture whose raw walk has two stationary distributions (the imported reducibility fence); the asymmetric star's PageRank `(4/9, 5/18, 5/18)` verified raw and provably **distinct** from the raw stationary `(1/2, 1/4, 1/4)` — teleportation shifting mass to the leaves being the construction's observable content; the teleportation floor, row sums, the row-stochasticity bridge, and irreducibility each pinned raw and by theorem route (two independent paths); and *both* endpoint fences refuted in proved form with complementary fixtures — at `α = 1` the Google matrix pinned entrywise equal to the raw walk and the `∃!` refuted through the imported witnesses with degrees/row sums intact (exactly `hα2` isolated), at `α = -1` the mixture pinned to the identity on `K₂` and the `∃!` refuted by two distinct stationary point masses with row stochasticity provably surviving (exactly `hα` isolated); `#print axioms` split-verified, the six axiom-route QA theorems carrying `perron_frobenius` and the raw/fence lemmas not — held). Earlier: 1715 declarations across 43 modules (count synced 2026-08-24 with the irreducible-stationary delivery, `IrreducibleStationary_QA` a new file at 94 — the first Perron–Frobenius consumer's witnesses: the asymmetric directed star with all four hypotheses hand-verified, the walk entries pinned, the hand value `(1/2, 1/4, 1/4)` verified completely raw, and the `∃!`'s uniqueness clause *identifying* every stationary distribution of the fixture with the hand value; the symmetric-cone `K₂` agreement pinning the PF-unique distribution *equal* to `stationaryVec` through the shelf's detailed-balance chain (two independent API paths to one value — a disagreement falsifies one route); and the reducibility fence on two disjoint edges refuting the hypothesis-free `∃!` and scale-uniqueness conclusions in proved form with `hnn`/`hdeg` verified intact; `#print axioms` split-verified, the axiom-route QA theorems carrying `perron_frobenius` and the raw lemmas not — the axiom-conditional theorems held to their conditional status, so the QA axis adds witnesses without converting conditional coverage into unconditional; held). Earlier: 1621 declarations across 42 modules (count synced 2026-08-24 with the approximate-spectral-projection Step-1c delivery, `Krylov_QA` 35 → 50 — the final `kanielPaige` statement's four proposal-mandated witnesses: the final-form bound **proved expression-equal** to the 1b composite's `16/75` on `diag(3,1,0)` with the raw true gap `32/241` strictly inside, the `k = 1` degenerate case (`T₀ ≡ 1`, bound reduced to the plain Rayleigh-gap value `16/3` against the raw `R(b) = 43/25`), the `b = u` tightness (bound `= 0`, the delivered witness pinned to Rayleigh value exactly `Ltop` from both sides), and the simple-top guard **refuted in proved form** on the top-multiplicity `diag(3,3,0)` fixture (`hpar` itself false by orthonormality, and the hypothesis-free conclusion refuted with every other hypothesis verified — the `k = 1` Krylov line's Rayleigh value computed raw to `8/3`) — witness kinds that strengthen existing coverage without touching the parametric gap; held). Earlier: 1606 declarations across 42 modules (count synced 2026-08-23 with the approximate-spectral-projection Step-1b delivery, `Krylov_QA` 19 → 35 — the composite `kanielPaigeChebyshev` instantiated end-to-end on `diag(3,1,0)` with the band hypothesis derived from the eigen-equation alone and the delivered bound pinned `= 16/75`, an independent raw route proving the actual Krylov witness's gap `32/241` strictly inside it (membership by the span's own generators, Rayleigh value computed by hand), the transfer engines and band-map pins each two-route, and the unit decomposition instantiated with both content pins forced — witness kinds that strengthen existing coverage without touching the parametric gap; held). Earlier: 1590 declarations across 42 modules (count synced 2026-08-23 with the approximate-spectral-projection Step-1a delivery, `Krylov_QA` a new file at 19 — the polynomial action and Krylov membership each witnessed by **two independent routes to one statement** (the transfer theorem vs. hand-computed `aeval diagM (X²+1) = diagM² + 1`; the polynomial interface vs. generator-direct membership), the **degree guard refuted in proved form** (`M e₁ = e₂ ∉ krylovSpan M e₁ 1` — the line `ℝ·e₁`, so `hdeg` is load-bearing), the composed-use witness discharging `hdeg` for the degree-5 Chebyshev polynomial by `natDegree_T` alone, and the full hypothesis-form skeleton instantiated on the diagonal fixture with all twelve hypotheses hand-discharged and the bound constant `2` pinned against raw `rayleigh diagM b = 1` — witness kinds that strengthen existing coverage without touching the parametric gap; held). Earlier: 1571 declarations across 41 modules (count synced 2026-08-23 with the discrete-affine delivery, `DiscreteAffine_QA` +25 in the new `Dynamics` domain — both convergence statements witnessed by **two independent routes** (the delivered theorems vs. entrywise/Pi-topology limits from the pin's own scalar decay lemma, the lifting exercised through disjoint API paths), the closed form and per-coordinate geometric decay pinned from the recurrence, and *both* endpoint hypotheses refuted-on-omission as proved non-convergence with complementary fixtures (`α = 2` oscillation with `0 < α` intact — exactly `hα2` isolated; `α = 0` constancy with `α < 2` intact — exactly `hα0` isolated) — witness kinds that strengthen existing coverage without touching the parametric gap; held). Earlier: 1546 declarations across 40 modules (count synced 2026-08-23 with the Tikhonov Phase-2 delivery, `Tikhonov_QA` +24 — the hard-filter limit's tail energy pinned in **closed form** on a genuinely two-mode tail (the diagonal `diag13` fixture reused from `Band_QA`) and evaluated collapsing to exact numerics `1/121 → 1/10201`, the corollary consumed at a concrete tolerance through `Metric.tendsto_nhds_nhds`, and *both* hypothesis levels refuted-on-omission in proved form (the scalar `lam = 0` form has no limit at all; the tail form with the kernel mode included provably stays `≥ 1/2` at every nonzero `π` — the requester's mandated band-projector one-sidedness witness) — witness kinds that strengthen existing coverage without touching the parametric gap; held). Earlier: 1522 declarations across 40 modules (count synced 2026-08-23 with the heat Phase C Step-2 delivery, `Heat_QA` 50 → 66 — the first-order remainder bound's spectral constant evaluated to *exactly* `4` on K₂ (eigenvalue inventory from PSD/trace/determinant plus the eigenmode structure `v = c • ![1,-1]`, `2c² = 1`), the raw closed-form value `1 − 2t − e^{-2t}` pinned at every time, the concrete bounds `e⁻¹ ≤ 1` and `|1/2 − e^{-1/2}| ≤ 1/4` composed from raw values and theorem bounds at two times, the `t²` scaling pinned by both times' concrete constants, and the window hypothesis *refuted* beyond `t = 1/2` — witness kinds that strengthen existing coverage without touching the parametric gap; held). Earlier: 1507 declarations across 40 modules (count synced 2026-08-23 with the heat Phase C Step-1 delivery, `Heat_QA` 46 → 50 — the heat-flow derivative's numeric value on K₂ pinned by **two independent routes to one statement** (eigenbasis expansion + termwise differentiation vs. the Step-4 closed form + scalar calculus only), and infinitesimal mass conservation cross-checked against Step 3's conservation in both directions — witness kinds that strengthen existing coverage without touching the parametric gap; held). Earlier: 1503 declarations across 40 modules (count synced 2026-08-23 with the heat Step-4 delivery, `Heat_QA` 25 → 46 — eigenmode decay and the DC limit each witnessed by two independent routes to one statement, the new eigenmode engine and rank-one-idempotent collapse cross-validated against each other at a nonzero eigenvalue, the K₂ Laplacian spectrum pinned `[0, 2]` from trace/determinant/sortedness with the decay-monotonicity constants read from the pin — witness kinds that strengthen existing coverage without touching the parametric gap; held. Earlier: 1482 across 40 modules (count synced 2026-08-23 with the heat Step-3 delivery, `Heat_QA` 17 → 25 — mass conservation witnessed by **two independent routes to one statement**: the theorem route on the asymmetric fixture against the hand-computed route (the closed form `!![1-t, t; -t, 1+t]` multiplied onto `onesVec` entrywise, independent of the theorem), plus the raw kernel-instance check, the symmetric-fixture instantiation, the **per-component no-leakage witness** on a new disconnected `Fin 3` fixture (the `{0,1}`-component indicator checked `L`-harmonic raw from the definitions, then fixed by the kernel-vector engine at every time — heat provably does not cross components, so conservation is not accidentally vacuous on disconnected input), and the kernel-hypothesis guard (a non-kernel vector provably *not* fixed, `![0,-1] ≠ ![1,0]`) — score held at 4.0, the parametric/randomized gap untouched). Earlier: 1474 declarations across 40 modules (count synced 2026-08-23 with the heat Step-2 delivery, `Heat_QA` 10 → 17 — the semigroup law witnessed by **two independent routes to one closed-form statement**: the hand multiplication `!![1-s, s; -s, 1+s] · !![1-t, t; -t, 1+t]` (every entry `ring`, independent of the theorem) against the theorem-route composition, plus the every-time closed form for symbolic `t`, the numeric instance `s = 2, t = 3`, the group property `e^{-L} · e^{+L} = 1`, and the degenerate `t = 0` identities — score held at 4.0, the parametric/randomized gap untouched). Earlier: 1467 declarations across 40 modules (count synced 2026-08-23 with the heat Step-1 delivery, `Heat_QA` a new file at 10 theorem declarations — the time-zero identity computed on both fixtures (hypothesis-free, holding where the symmetry theorem cannot apply); symmetry through the theorem with the hypothesis derived from the literal; the **exact closed form** `heatKernel asymAdj 1 = !![0, 1; -1, 2]` on the square-zero-Laplacian fixture (the collapse makes the exponential exactly evaluable, and the spike caught the first draft's wrong `(1,1)` entry — the failure mode numeric QA exists for); the symmetry hypothesis refuted-on-omission (`1 ≠ -1` with the fixture's `IsSymm` provably violated at the same pair); and the sign witness `e^{-L} ≠ e^{+L}` entrywise (`0 ≠ 2`) — score held at 4.0, the parametric/randomized gap untouched). Earlier: 1457 across 39 modules, synced 2026-08-23 with the Fiedler Phase B delivery, `Fiedler_QA` 57 → 65 — the K₂ certificate witnesses: `cheegerConstant (K₂) = 1` pinned both directions through the singleton identification, the attainment instantiation, the **Rayleigh transfer cross-checked** against the independently pinned `lambda2 = 2`, the certified cut identified with its bound theorem-sourced and displayed as `1 ≤ 4`, and the `d = 100` regularity refutation `1 ≤ 1/25` with every other hypothesis proved to hold; score held at 4.0 — the parametric/randomized gap untouched). Earlier: synced 1449 with the Cheeger Step-1c delivery, `Cheeger_QA` 78 → 104 — the median forced into its interval on a tie-heavy fixture, the per-part bound at the 1b equality data, the norm split's `+4m²` remainder pinned at two medians, the sweep on `K₂` and `C₄`, and the retirement instance `1/2 ≤ λ₂ = 2` through the proved theorem), zero `sorry`/`admit`, all modules individually compiled; coverage no longer degenerate-skewed (2026-08-17, `Exhaustive_QA`): exhaustive kernel-checked sweeps over **all** cuts of the 3-vertex path and the 4-cycle, negative witnesses, and walk row sums computed independently of their theorem. **Computational eigenvalue checks now exist (2026-08-18, `Cheeger_QA`)**: the corrected Cheeger spectral side is pinned to its classical value on the two-vertex edge (`edge_normLap_secondEval_eq_two_QA`: trace + determinant + sortedness, no axiom), and the pre-repair axiom shape is **refuted in proved form** (`old_cheeger_lower_bound_refuted_QA`: the old side evaluated to `1/2 ≤ 0` on `K₂`) — the QA program caught a materially false admitted statement. **Load-bearingness witnesses for hypothesis structure (2026-08-18, `Connectivity_QA`)**: the disconnected `Fin 4` fixture shows the kernel-characterization conclusion failing when connectivity is dropped (component indicator in the kernel, not constant; support graph proved not connected). **Adapter agreement computed, not rewritten (2026-08-18, `SimpleGraphAdapter_QA`)**: weights, degrees, both Laplacian sides, boundary, handshake, and kernel membership evaluated against hand-expected numbers, plus a disconnected witness where the kernel is proved ≠ `span {onesVec}` through the adapter. **Cross-representation coherence computed (2026-08-18, `KernelBridge_QA`)**: on the connected path, the bridge's dimension count and the connected span theorem hold simultaneously (dimension `1`, basis vector constantly `1`); on the disconnected fixture the component count is computed to `2` **independently of the transferred theorem** (block classification + `Nat.card_eq_two_iff`), the transferred dimension reads `2`, and the two basis vectors are computed to the component indicators `![1,1,0,0]`/`![0,0,1,1]`. **Unsolvability certified, not just solvability (2026-08-18, `PotentialSolvability_QA`)**: potentials are computed to hand values on the edge and the 3-path (`![1,0]` carrying `L *ᵥ ![1,0] = e₀ − e₁`, `![1,0,−1]` fixed by the path Laplacian), and the negative witnesses use the reciprocity identity with kernel certificates (all-ones on the connected edge; component indicator on the disconnected fixture) to prove *in Lean* that a non-zero-sum demand and a cross-component zero-sum demand have no solution — both hypotheses of the solvability theorem are shown load-bearing. **A second materially false admitted statement refuted in proved form (2026-08-18, `Variational_QA`)**: the pre-repair `lambda2_variational` shape (symmetry hypotheses only) is refuted on a negative-weight two-vertex graph (`λ₂ = 0` while the constraint set's infimum is `-2`, every element computed parametrically), and the proved theorem is instantiated exactly on `K₂` — `λ₂ = 2` computed twice, once from trace/determinant/sortedness and once *through* the theorem from the independently computed Rayleigh side — plus the disconnected instantiation `λ₂ = 0` and the path bound `λ₂(P₃) ≤ 1`. **The proved Cheeger upper bound exercised on computed data (2026-08-18, `Cheeger_QA`)**: the cut test vector pinned to `![1,-1]` on `K₂`, its Rayleigh value computed to `2` (exactly the pinned `λ₂(L_sym)` — the test-vector bound attained), the theorem itself instantiated on `K₂` as `λ₂ = 2φ` from independently computed values, and on `C₄` as `λ₂ ≤ 1` through the exhaustively computed adjacent-pair conductance `1/2`, whose test-vector Rayleigh value computes to exactly `1`. **A noncomputable object pinned through its defining properties (2026-08-18, `Fiedler_QA`)**: the Fiedler vector cannot be decided entrywise (spectral theorem + classical choice), so the witnesses derive its structure from the proved eigen equation, unit norm, and orthogonality — on `K₂` the partition is pinned to a singleton half with boundary `1`; on the `P₄` barbell `λ₂ ≤ 1` is computed through the proved Rayleigh engine, `λ₂ ≠ 1` from the eigen equations, and the resulting sign pattern forces the partition to be exactly the known good cut `{0,1}` (or its complement) with boundary `1`, volume `3`, conductance `1/3`; the disconnected fixture proves the `0 < λ₂` hypothesis load-bearing (`λ₂ = 0`, and `onesVec` is a nonzero eigenvector there whose sign filter is all of `univ`). **A false admitted identity refuted with its hypotheses proved satisfied (2026-08-18, `MatrixUpdates_QA`, the first Core-domain QA file)**: the retired Woodbury shape is restated at `Fin 1` over `ℚ` and negated (`old_woodbury_identity_refuted_QA`, consuming no axiom), with the old middle and sum determinant hypotheses *separately proved to hold* at the counterexample (`A = U = V = 1`, `C = 0` — the refutation is of a genuinely applicable statement), the corrected `IsUnit C.det` hypothesis proved to exclude that instance, and positive instances at scalars and at a non-scalar rank-one update whose theorem-consumed right sides compute to the independently computed true inverses (`1/5`; `!![3/8,-1/8;-1/8,3/8]` through the computed middle factor `(1+1)⁻¹ = 1/2`). **Both directions of a proved engine exercised against computed spectra (2026-08-18, `CourantFischer_QA`):** the fixture `!![2,1;1,2]` has its spectrum `[1,3]` pinned from trace/determinant/sortedness independent of the theorem; the competitor direction is instantiated on a hand-checked line, the existence direction yields (through `eq_top_of_finrank_eq`) the *derived universal* that every Rayleigh quotient is at most the top eigenvalue, and the competitor witness is then pinned to attain `evals 1 = 3` exactly through both directions; negative witnesses refute the existence-direction property on the wrong line (`3 ≤ 1`), prove the dimension hypothesis load-bearing (the conclusion is false on a one-dimensional subspace at index `1`), and — at the interior index `k = 1 < n−1` on the three-vertex path Laplacian — refute a wrong two-dimensional subspace (`4/3 ≤ evals 1` vs. the theorem-derived `evals 1 ≤ 1`, cross-checked against the older `secondEval_le_rayleigh` engine). **The retired Sherman–Morrison axiom's theorem interface exercised at a computed instance (2026-08-18, `MatrixUpdates_QA`)**: at `A = diag 2 2`, `u = v = ![1,1]` the rank-one update's true inverse `!![3/8,-1/8;-1/8,3/8]` is computed independently by the adjugate formula, and the theorem-consumed right side (scalar denominator computed to `1` from the definitions) pins to the same value; the negative witness proves the excluded denominator `v ⬝ᵥ (A⁻¹ *ᵥ u) = -1` attained at a `Fin 1` fixture where the update is exactly the singular zero matrix. **The interlacing window instantiated numerically, superseding the old "no thin QA exists" note (2026-08-18, `Interlacing_QA`):** the retired axiom's statement is now checked at `K₂` with the singleton submatrix — ambient spectrum `[0, 2]` and submatrix spectrum `[1]` both pinned from trace/determinant/sortedness independent of the theorem, the window instantiated to `0 ≤ 1 ≤ 2`, and both collapsed one-sided bounds (`μ₀ ≤ λ₀`, `λ₁ ≤ μ₀`) refuted in proved form, so the two-sided window shape itself is witnessed. **Flow interfaces computed from raw definitions with two convention guards (2026-08-19, `ElectricalFlow_QA`):** the `K₂` current matrix `!![0,1;-1,0]` and divergence `![1,-1]`, and the 3-path unit flow with the internal vertex's divergence computed to `0` (Kirchhoff conservation away from source/sink), all evaluated independently of the Kirchhoff bridge; the negative witnesses guard the statement conventions the proposal names as traps — an asymmetric network makes the current provably non-antisymmetric (`2 ≠ 1`), and an edgeless-network phantom (antisymmetric, unit divergence) is excluded by the zero-conductance support conjunct alone. **Flow energy pinned by triple-route agreement and two convention guards at the energy level (2026-08-19, `ElectricalFlow_QA` step 2):** energies `1` (edge) and `2` (path) each computed from the raw `flowEnergy` definition, cross-checked against the independently computed Dirichlet energies and the pinned resistance values — three routes meeting at each number; the **double-counting guard** proves the raw ordered-pair sum computes to `2 ≠ 1` = the Dirichlet energy, so `flowEnergy`'s `1/2` factor is numerically mandatory; the **hypothesis-set witness** instantiates the agreement on a symmetric negative-weight network (energy `-1 < 0`, so `flowEnergy_nonneg`'s hypothesis is load-bearing while the agreement itself needs no nonnegativity); and the **zero-energy competitor** — an antisymmetric unit-divergence flow routing through zero-conductance pairs on a real-edge-plus-isolated-vertex network — dissipates `0 < 1` = the real resistance and is excluded by the support conjunct alone: exactly the witness that keeps Thomson's principle (the proposal's step 3) true over valid flows. **Variational witnesses on a network with competing routes (2026-08-19, `ElectricalFlow_QA` step 3, on the triangle `K₃`)**: attainment at the split current (`2/3` — two routes exercised at once, computed from the raw definitions), a strict competitor (the detour unit flow: valid, energy `2`, `2/3 < 2`), and the superposition decomposition `2 = 2/3 + 4/3` with all three values computed independently — the minimizer, its competitor, and the difference flow all pinned numerically. **A network-comparison theorem certified with an orientation guard (2026-08-19, `ElectricalFlow_QA` step 4)**: the capacity increase `1 → 2` on the unit edge certifies the resistance decrease `1 → 1/2` from an independent potential witness, Rayleigh monotonicity is instantiated and the decrease certified strict, and the **orientation guard** refutes the reverse inequality numerically (`1 ≤ 1/2` false — the proposal names a reversed conductance/resistance orientation as a statement bug, and this witness would catch it); the competitor transfer is computed on both sides (`1/2 ≤ 1`), and a partial increase on the triangle (`2/3 → 2/5`, the new value pinned by the independent potential `![2/5, 0, 1/5]`) exercises the theorem where `A < B` on exactly one undirected edge. **The reinforcement operation itself computed, not just instantiated (2026-08-19, `ElectricalFlow_QA` step 5)**: on the Mathlib path graph through `toWAdj`, `increaseConductance … 0 1 1` evaluates entrywise to the concrete doubled-path matrix, the adapter weights are bridged to the weighted-fixture world, the reinforced resistance `3/2` is pinned by an independent potential witness with connectivity from explicit walks (independent of the adapter the theorem consumes), and the certified decrease is strict `3/2 < 2` against the pinned original value `2`. **A global identity checked by two independent routes with the double-counting factor refuted-on-omission (2026-08-19, `Foster_QA`)**: on the cliques `K₃`/`K₄`, the path `P₃`, and the 3-leaf star, every effective resistance is pinned by an explicit potential witness (`K₄` through the general-pair potential `(e i − e j)/4`, proved to solve the unit demand for *every* pair via the entrywise `L = 4I − J` structure), each ordered Foster sum is computed independently of the theorem (`4`, `6`, `4`, `6`) and cross-checked against the theorem's `card V − 1` (`2`, `3`, `2`, `3`), and the ordered sums are proved *not equal* to `n − 1` on both cliques (`4 ≠ 2`, `6 ≠ 3`) — the theorem's `/ 2` factor is load-bearing, exactly the calibration the proposal demands; non-edge pairs provably contribute nothing (zero conductance). **A discrepancy core checked from the raw definitions with three negative witnesses (2026-08-19, `Expander_QA`)**: cut weights, centered indicators, and centered cross terms all computed on a fresh `C₄` fixture (adjacent cut `1`, opposite cut `0`, half-and-half `2`, total `8`); the `d`-regular decomposition instantiated on both an adjacent (`1 = 1/2 + 1/2`) and an opposite (`0 = 1/2 − 1/2`) cut with independently computed cross terms; and the refutations — main-term-only dropped (`0 ≠ 1/2`), wrong degree (`1 ≠ 3/4`), asymmetric weight breaks cut symmetry (`2 ≠ 1`). **The first kernel-`decide`d algorithmic QA (2026-08-19, `SpectralCertificates_QA`):** the integer twin's accept/reject/non-orthogonal/zero/fractional paths are all evaluated by plain kernel `decide` on `C₄`; the accepted certificates feed the soundness theorems end-to-end (`lambda2 ≤ 2` and `≤ 5/2` from `decide`d integer data); the ℚ specification checker — *not* kernel-decidable, the Step 0 wall — is proved `= true` only through the proved cross-multiplication bridge, making the bridge load-bearing in QA; the certified bound is pinned to the test vector's exact Rayleigh quotient (`4/2 = 2`); and the guard-free statement shape is refuted at `onesVec` (`rayleigh = 0 < lambda2` on the connected fixture), so the orthogonality conjunct is witnessed load-bearing. **Exact spectrum pins and second-size demonstrations (2026-08-19, step 4):** the same chain kernel-decided at `C₆` (accept `1`/reject `0`, fractional `3/2`/`1/2`, bridge, end-to-end `lambda2 (C₆) ≤ 1`); a `C₄` Poincaré inequality consumes the **lower** half of `lambda2_variational` (its first `≥`-direction QA consumer) to pin `lambda2 (C₄) = 2` exactly, with the kernel checker accepting precisely at the true value and rejecting below it — the certificate method witnessed exactly tight; the `K₃` energy identity pins `λ₂ = λ_max = 3` and `μ = 1`; the EML is attained exactly on both `K₃` cuts tested and on the `C₆` alternating cut. **An operator-norm identity computed against the pinned spectrum (2026-08-19, `Resolvent_QA`, the first OperatorTheory-domain QA file):** the `!![2,1;1,2]` fixture's spectrum `[1,3]` pinned from trace/determinant/sortedness, both directions of the norm bridge instantiated to pin `‖M‖ = 3` exactly (the literature spectral-norm value), the packaged extremal form instantiated, and the **negative witness** `¬(‖M‖ ≤ 1)` refuting a bound by one eigenvalue's absolute value — the `∀ k` hypothesis load-bearing; the shifted-PSD invertibility cross-checked against computed determinants (`3`, `8`) with the **shift-load-bearing witness** (the unshifted Laplacian's determinant is exactly `0`); and the resolvent identity checked with both sides independently computed to the same literal matrix from the pinned resolvent. **The resolvent bounds attained with route agreement and both guards refuted-on-omission (2026-08-19, `Resolvent_QA` Step 2):** the norm bound is *attained* — `‖(L(K₂)+1)⁻¹‖ = 1` exactly, with the theorem's energy route and the eigenvalue-bridge route (pinned spectrum `{1/3, 1}` of `(1/3)!![2,1;1,2]`) independently meeting at the value, so the bound is tight, not slack; the general-`t` instance `‖(L+2•1)⁻¹‖ = 1/2` exactly (spectrum `{1/4, 1/2}`) — also attained; the Lipschitz instance with both sides independently pinned (difference spectrum `{-2/3, 0}`, norm `2/3`; `‖L‖ = 2`; the instantiated theorem reads `2/3 ≤ 2`); the **shift guard** (the invertible PSD `(1/4)I` alone has `‖A⁻¹‖ = 4 > 1` — PSD alone gives no bounded inverse); and the **hypothesis guard** (the symmetric non-PSD `-(3/4)I`'s shift is invertible with inverse norm `4 > 1`, the violated quadForm hypothesis exhibited at `![1,0] = -3/4`). **Injectivity instantiated at two distinct PSD pairs and the invertibility guard refuted-on-omission (2026-08-20, `Resolvent_QA` Step 3):** the theorem's output bridged to numeric facts with both resolvents independently left-inverse-pinned (`(lap2+1)⁻¹ = (1/3)!![2,1;1,2]`, `(mat2+1)⁻¹ = (1/8)!![3,-1;-1,3]`) and distinctness verified by entries (`1/3 ≠ 0`, `2/3 ≠ 3/8`); the packaged iff consumed contrapositively (resolvent equality as a certificate of matrix equality); and the hypothesis-free implication "equal resolvents → equal matrices" **refuted** at `A = -1` vs `B = -1 + E` (`E` nilpotent): distinct matrices, both `+1` shifts singular (determinant `0` by a zero row), both resolvents the junk inverse `0` — the core theorem's determinant hypotheses are load-bearing. **A retired perturbation axiom's interface checked against pinned spectra with attainment, strictness, and a window guard (2026-08-20, `Weyl_QA`):** on the nonzero fixture `A = E = !![2,1;1,2]`, both spectra (`[1,3]`, `[2,6]`) pinned independently from trace/determinant/sortedness and `‖E‖ = 3` through the proved bridge — the bound instantiated at both indices, **attained exactly** at the top (`|6−3| = 3`), **strict** at the bottom (`1 < 3`, the proposal's required non-vacuity witness), both additive bounds instantiated at both indices with endpoint attainment, and the **window-endpoint guard** refuting `λ₁(E)` in place of `λₙ(E)` (`6 ≤ 4` false). **A noncomputable spectral construction pinned against hand-solved linear algebra (2026-08-20, `Tikhonov_QA`):** the eigenbasis-defined minimizer — not entrywise computable, like the Fiedler vector — is pinned through the proved *converse characterization* of the normal equation: the candidate `![2/3,1/3]` is verified by entrywise Gaussian elimination on `(L+1) *ᵥ z = 1 • ![1,0]` (independent of the module) and promoted to `tikhonovMinimizer = ![2/3,1/3]`, so the spectral-theorem construction and a hand-solved 2×2 system meet at the same vector; a second hand-solved system pins `T(T y) = ![5/9,4/9] ≠ ![6/9,3/9] = T y` — the not-a-projection claim witnessed numerically, a projection having to fix its own output; the objective pinned exactly (`obj(x*) = 1/3` against `obj(y) = obj(0) = 1`, minimality instantiated and strictness certified); the shrinkage story exact at the pinned spectrum `{0,2}` (factors `1` and `1/3`, ordering by the antitonicity theorem, `1/3 ∈ Ioo 0 1`); mean preservation instantiated twice (`∑ T y = ∑ T(T y) = ∑ y = 1`); and the **`hπ` guard refuted-on-omission** — at `π = 0` the minimizer is the zero vector and the hypothesis-free minimality would read `1 ≤ 0`. **A spectral construction pinned through sign-invariant eigenvector directions (2026-08-20, `Band_QA`):** the diagonal fixture `!![1,0;0,3]` has one-dimensional eigenspaces, so the eigen equations force the eigenvector *directions* (`λ = 1 ⇒ v = ![±1,0]`) independent of what the spectral theorem's classical choice produced — making the band projector's value pinable entrywise against the hand-computed outer product `e₀e₀ᵀ` at any threshold in `[1,3)`; band values computed independently (low band `diag(1,0)`, high band `diag(0,1)`, covering band `1`, and the between-eigenvalues band `= 0` — the gapped-definition guard); idempotence checked by raw literal multiplication as well as through the theorem; the nestedness cross-law instantiated in both orders; and mode selection witnessed in both directions, with the excluded mode **annihilated and provably not fixed** against its nonzero eigenvector. **Disjoint-band orthogonality checked by dual routes with a same-band counter-witness and an overlap guard (2026-08-20, `Band_QA` Step 2):** the disjoint low/high bands' composition to zero verified through the theorem *and* by raw literal multiplication on the pinned band values, in both orders; image orthogonality on concrete vectors computed both ways, with the same band paired with itself giving dot product `1 ≠ 0` (so the vanishing is genuinely about disjointness, not the fixture's zeros); the composed action `B_high *ᵥ (B_low *ᵥ x)` annihilating a filtered signal, again by both routes; and the **overlap guard** — bands `(−1, 3]` and `(1, 4]` sharing the eigenvalue `3` compose to the provably nonzero `diag(0,1)`, refuting the hypothesis-free form and witnessing the `b ≤ c` disjointness hypothesis load-bearing. **A partition identity checked by dual routes with both endpoint guards (2026-08-20, `Band_QA` Step 3):** the covering two-band family `t k = 2k` sums to the identity both through the completeness theorem and from independently pinned band values (`diag(1,0) + diag(0,1) = 1`); a three-band partition with an empty middle band (zero-width member contributing nothing) and its top threshold exactly touching the top eigenvalue (the closed right endpoint exercised); the **endpoint guards** — a family starting above the lowest mode, or truncated below the highest one, provably fails to sum to the identity (each with the violated covering hypothesis separately proved violated: `2 < 1` and `3 ≤ 2` both false at the pinned spectra) — the design note's "silently ignores modes" failure mode witnessed in both directions; the unconditional telescoping law on a deliberately non-monotone family whose junk band `−1` cancels the covering band `1`, both sides independently computed to `0`; and the vector decomposition `∑ B_k *ᵥ x = x` on a concrete signal by theorem and raw routes. **A Hilbert-space closest-point claim pinned numerically with an independent cross-check and a hypothesis guard (2026-08-21, `Band_QA` Step 4):** the identification of Mathlib's `orthogonalProjection` at the transported band range with the band-filtered signal instantiated on the fixture; minimality **attained** (the signal-to-projection distance is exactly `4`), **strict over the zero signal** (`4 ≤ 5` — the 3-4-5 triangle, so the theorem genuinely improves on non-optimal range members), and **generic over the whole range line** (`4 ≤ √((3−t)²+16)` with both norms pinned through `‖e v‖² = v ⬝ᵥ v`), with `band_diag13_hilb_min_line_raw` reproducing the identical line inequality from bare square-positivity — an independent hand-check the transported theorem's claim must match; the residual-orthogonality engine witnessed by both routes (theorem and `![0,4] ⬝ᵥ ![1,0] = 0` by raw arithmetic); the high band instantiated too (not fixture-locked); and the **fixed-space guard** — the hypothesis-free form refuted at the unfiltered signal (distance `0 < 4`, the signal provably not fixed by the band), so the fixed-point hypothesis is load-bearing. Remaining gap: no parametric (randomized) property QA. |
| Citation fidelity | 3.5 | Every axiom carries author/title/locator + statement-differences; false Chung provenance corrected against git history; Horn–Johnson/Chung page-level locators explicitly unconfirmed rather than invented; the Cheeger axioms' Lean statements now match their cited source after the 2026-08-18 shape repair. |
| Downstream reuse | 4.0 | The derived layer consumes the concentration and perturbation bridges end-to-end; the walk/normalized interfaces now have **two** consuming modules: `GraphTheory.Stationary` (2026-08-17, runs 2–3: kernel `L_sym √deg = 0`, stationary degree measure, conservation of mass) and `GraphTheory.VariationalTransfer` (2026-08-17, run 2: quadratic-form/Rayleigh transfer through the congruence, `normalizedLaplacian_psd`). Scores raised 2.5 → 3.0 → 3.5 → 4.0 with those milestones; the proved `cheeger_upper_bound` (2026-08-18) additionally consumes the variational engine (`secondEval_variational`/`secondEval_le_rayleigh`) as the first axiom-retirement proof built on a locally proved engine; and the Fiedler Phase A module (2026-08-18) consumes the electrical program's kernel characterization (`laplacian_kernel_eq_span_onesVec` — load-bearing in `lambda2_pos_of_connected`) and the multiplicity pins, with its QA consuming the proved Rayleigh engine (`secondEval_le_rayleigh`); the interlacing retirement (2026-08-18) is the min–max engine's first **proof-level** consumer — the retirement proof itself consumes both Courant–Fischer witness directions through the padding bridge; the Weyl retirement (2026-08-20) is the min–max engine's second proof-level consumer (after interlacing) and the operator-norm bridge's first, with its QA pinning both perturbed spectra and the norm independently; remaining gap: the remaining admitted axioms (the concentration family, Perron–Frobenius) have derived consumers but no proof-level consumer yet — the Cheeger hard direction joined the proof-consumer set 2026-08-23 (its retirement proof consumes `secondEval_variational`, `coarea_core`, and the 1a algebra, with the two former axiom-consuming QA theorems shedding the dependency). |

**Weakest assurance axes:** two axes sit at 3.5 (proved depth,
citation fidelity) — the
inequality engines remain admitted by design. Axiom minimization was
re-scored 3.5 → 4.0 on 2026-08-18 (`lambda2_variational`: the first
axiom removed by proof rather than deprecation) and 4.0 → 4.5 on
2026-08-18 (`woodbury_identity`: the first retirement motivated by the
admitted statement being verified *false*; the corrected theorem is
proved from Mathlib, removing the false-axiom category among checked
statements). QA was re-scored
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
Subject axis 3 (variational) was re-scored 3.5 → 4.0 on
2026-08-18 (`prove-courant-fischer.md` delivered: the fixed-index
Courant–Fischer engine generalized to the full subspace min–max at
every index, symmetry-only, with both directions QA-exercised against
independently pinned spectra).
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
resistance metric, and Matrix–Tree/Kirchhoff are still absent). The
score was **held at 3.0** on 2026-08-19 (electrical-flow proposal
steps 0–1: the flow/conservation interface delivered and QA-witnessed,
recorded per protocol — the axis is reserved to rise with Thomson's
principle and Rayleigh monotonicity, steps 3–4, which the interface
exists to carry; the delivered one-sided Dirichlet bound remains the
axis's only inequality) and **held at 3.0** again the same day
(electrical-flow step 2: `flowEnergy` delivered with the energy
agreement `flowEnergy A (electricalCurrent A f) = quadForm (laplacian A)
f` — symmetry-only, QA-witnessed on both hypothesis-set sides — plus
`flowEnergy_nonneg` and the unit-demand identity `energy =
effectiveResistance`; an identity, not a new inequality, so the
reserved-raise rationale stands, and the axis's inequality frontier
remains steps 3–4). It was re-scored **3.0 → 3.5** on 2026-08-19
(electrical-flow step 3: **Thomson's principle proved** —
`effectiveResistance A u v ≤ flowEnergy A θ` for every valid unit
flow, the electrical current as the energy minimizer, through the
divergence-free superposition lemma; QA witnesses attainment at the
split current on the triangle, a strict competitor (detour, `2/3 < 2`),
and the decomposition `2 = 2/3 + 4/3` — the reserved trigger fired;
the score stays below 4.0 because Rayleigh monotonicity, the
resistance metric, and Matrix–Tree/Kirchhoff remain absent). It was
re-scored **3.5 → 4.0** on 2026-08-19 (electrical-flow step 4:
Rayleigh monotonicity in conductance form — both inequality engines
of the flow proposal landed, the recorded reservation firing; the
change was recorded at delivery in the axis row above and in
`AGENT_ACTIVITY.md` and is logged here for continuity) and **held at
4.0** the same day (electrical-flow step 5: the ICP
capacity-reinforcement example — a one-hypothesis packaging of the
monotonicity with the connectivity adapter; the electrical-flow
program is complete, and the axis's remaining gaps are unchanged:
resistance metric, Matrix–Tree, Kirchhoff network theorems). It was
re-scored **4.0 → 4.5** on 2026-08-19 (Foster's theorem proved,
`proposals/spectral-graph-sparsification.md` Phase A — the first
global network identity on the axis, `(∑ i, ∑ j, A i j * R i j)/2 =
card V − 1`, zero new axioms via the pseudoinverse-free eigenbasis
route; a new theorem family rather than packaging, with QA witnessing
the ordered-pair double-counting factor on both cliques `K₃` (`4 ≠ 2`)
and `K₄` (`6 ≠ 3`)).
The QA axis was **held at 4.0** on
2026-08-19 (decidable-certificates step 2: the mixing-lemma QA adds two
new witness *kinds* — a **derived hypothesis** (`μ = 2` proved on `C₄`
from a test vector, a sum-of-squares estimate, and PSD bounds, not
assumed) and **sharpness witnesses** (the opposite cut and the
alternating vector attain the bound exactly, so the derived `μ` is
tight and the theorem not vacuous) — but the axis's named gap,
parametric/randomized QA, is untouched; the count synced to 666/30).
The QA axis was **held at 4.0** again on 2026-08-19
(decidable-certificates Step 3: `SpectralCertificates_QA` adds the
first kernel-`decide`d algorithmic QA kind — accept/reject paths
decided by the kernel on `C₄`, the ℚ specification reached only
through the proved bridge, and the orthogonality guard refuted on
omission — but the named gap, parametric/randomized QA, is still
untouched; the count synced to 688/31). Subject axis 7
(perturbation/randomness/algorithms) was re-scored **3.0 → 3.5** on
2026-08-19 (decidable-certificates Step 3: the verified
proof-carrying certificate layer is the axis's first
numerical/spectral algorithm driver — computable checkers,
kernel-`decide`able, with proved soundness into the real center;
random-graph models remain the axis's absent category).
The QA axis was **held at 4.0** on 2026-08-19
(decidable-certificates Step 4: the QA adds exact spectrum pins —
`lambda2 (C₄) = 2` through the *lower* half of `lambda2_variational`,
its first `≥`-direction consumer — second-size `C₆` kernel
demonstrations, and the Ramanujan fixture family with exact `μ` values,
but the named gap, parametric/randomized QA, is untouched; the count
synced to 752/31; subject axes 4 and 7 held per protocol — the pins
strengthen existing coverage without adding a theorem family or
capability).
It was previously held at 4.0 on 2026-08-19 (decidable-certificates
steps 0–1: the convention decision and ℚ-`decide` spike are recorded
decisions, and the Expander module is the mixing lemma's interface
plumbing; the count synced to 647/30 with the discrepancy-core QA kind
described). Downstream reuse was re-scored 3.5 → 4.0 on
2026-08-17 (`VariationalTransfer`, the second consuming module); the
remaining gap is consumption by an admitted-axiom consumer. Subject
axis 4 (cuts/expansion/clustering) was re-scored 3.0 → 3.5 on
2026-08-18 (Fiedler Phase A: the axis's named missing interface — the
Fiedler vector and sign-pattern partition, with the algebraic-
connectivity certificate `lambda2_pos_of_connected` — delivered as
hard crust and QA-computed on the barbell against the known good cut;
the score stays below 4.0 because the *certified* partition-quality
guarantee is Phase B, which inherits the Cheeger hard direction's
admitted status until that is proved).
Subject axis 4 (cuts/expansion/clustering) was re-scored 3.5 → 4.0 on
2026-08-19 (decidable-certificates Step 2: the Expander Mixing Lemma
proved as hard crust — the axis's first spectral–combinatorial
discrepancy result, with QA deriving the spectral hypothesis on the
fixture and attaining the bound exactly; a new theorem family, not
packaging).
The QA axis was **held at 4.0** and subject axis 2 was **held at
3.5** on 2026-08-19 (resolvent-calculus steps 0–1: the operator-norm
bridge is a new proved identity on axis 2 and the resolvent QA adds
the pinned-norm, shift-guard, and identity-check kinds, but the QA
axis's named gap — parametric/randomized QA — is untouched and the
bridge is a single-identity interface rather than a new theorem family
or capability; the count synced to 782/32).
Subject axis 2 and the QA axis were **held** again on 2026-08-19
(resolvent-calculus Step 2: the norm and Lipschitz bounds complete the
operator-norm family counted at Step 0 — completion, not a new
capability family — and the QA additions (attainment with route
agreement, the shift/hypothesis guards) strengthen existing kinds
without touching the QA axis's named parametric gap; the count synced
to 827/32).
Subject axis 2, the proved-depth axis, and the QA axis were **held** on
2026-08-20 (resolvent-calculus Step 3: injectivity completes the
program within the interfaces already counted — the core theorem is
Step-1 algebra consumed contrapositively — and the QA additions
(two-pair instantiation with left-inverse-pinned resolvents, the
invertibility guard) strengthen existing kinds; the parametric gap is
untouched; the count synced to 846/32).
Subject axes 2 and 7, the proved-depth, axiom-minimization, and QA
axes were **held** on 2026-08-20 (the Weyl retirement: `weyl_inequality`
converted from admitted to proved within the perturbation area axis 7
already counts as *present-but-admitted*, and axis 2's evidence row —
the same conversion for the min–max engine's second proof-level
consumer; assurance tracks it separately through the shrinking axiom count
(13 → 12, trend extended) and the proved-depth list rather than a
subject re-score — the axiom-minimization axis holds at 4.5 as a
trend continuation within the same cited-and-QA'd admitted set, the
first perturbation-bridge retirement but not a new threshold; the QA
additions (attainment, strictness, window guard) strengthen existing
kinds without touching the parametric gap; the count synced to 860/32).

Subject axis 7 (perturbation/randomness/algorithms) was re-scored
**3.5 → 4.0** and the QA axis **held at 4.0** on 2026-08-21 (the
Davis–Kahan retirement, `proposals/discharge-perturbation-axioms.md`
Step 1 complete; explicit axioms 11 → 10): the axis gains its first
calculus-based proof technique — the Duhamel/exponential-integral route
(`Analysis.OperatorTheory.Perturbation.Duhamel`: a vector-level heat
semigroup, an FTC assembly over an explicit exponential majorant, and a
limit-at-infinity argument, none previously present anywhere on the
shelf) — which retires the last admitted perturbation engine, leaves
`davisKahanTwoPoint` fully hard crust and `eventStreamProjectorDrift`
conditional on `matrix_azuma_hoeffding` alone, and adds the equal-rank
projector identity (`ProjectionGap`, delivered the same day) as a new
hard-crust gap-metric theorem. Per protocol this is a new capability
family (an integral-representation technique), not a completion of a
counted interface; the axis's absent categories (random-graph models;
parametric QA) are untouched. The QA axis count synced to 1061/35 (the
retirement's strict non-vacuity witness — a genuinely rotated projector
at `1/√10` against the `1/3` bound, every quantity pinned from
trace/determinant/sortedness and the eigen equations — strengthens
existing witness kinds without touching the parametric gap).

Subject axis 5 (random walks and diffusion) was **held at 3.0** on
2026-08-22 (the geometric decay engine, `proposals/mixing-time-bound.md`
Step 3 component 1 of the authorized sub-decomposition; zero new
axioms): the mathematical core of the program's hardest step is now
QA'd hard crust — walk powers conjugate across the proved similarity
(`√D *ᵥ (Pᵗ *ᵥ g) = (1 − L_sym)ᵗ *ᵥ (√D *ᵥ g)`, so the non-symmetric
power is never diagonalized), eigencoordinates evolve geometrically
through the new generic center lemma
(`Spectral.eigvecOf_dotProduct_one_sub_mulVec`), Parseval resolves the
π-weighted norm exactly, and the ℓ²(π) contraction holds term-wise with
value-based mode exclusion (`eigvalOf i = 0`, true unconditionally on
degenerate graphs — QA'd in both directions: exact decay on the
non-bipartite K₃ at rate 1/2, and the mode-hypothesis negative witness
`1 ≤ 1/4` refuted with the hypothesis provably unsatisfiable). The
score is **held** per the proposal's own gate — no re-score until a
step's proof *and* its QA pass, and the mixing *statement* (the χ²
decay bound `χ² ≤ (λ*)²ᵗ · normalization`) is component 2's to
deliver; that delivery is the axis's standing re-score trigger, now
with every interface it consumes already on the shelf. The QA axis
count synced to 1162/36 (the new QA kinds — a basis-independent
eigenvalue case analysis on a concrete graph and an *exact-decay*
fixture with equality pins at two time steps — strengthen existing
witness kinds without touching the parametric gap; held).

Subject axis 5 (random walks and diffusion) was re-scored
**3.0 → 3.5** and the QA axis **held at 4.0** on 2026-08-22 (the χ²
assembly, `proposals/mixing-time-bound.md` Step 3 component 2 — the
program's closing statement; zero new axioms): the mixing *statement*
itself — the standing re-score trigger every prior Step-3 record named
— is now proved hard crust, `chiSquareDistance_le_of_connected`:
`χ²(t, x) ≤ r ^ (2t) · ((π x)⁻¹ − 1)` on connected
symmetric-nonnegative positive-degree networks under the rate
hypothesis. Its one genuinely new mathematical component is the
connectivity kernel characterization of the *normalized* Laplacian —
`ker L_sym` transferred through the proved congruence
`√D L_sym √D = laplacian A` to the shelf's
`laplacian_kernel_eq_span_onesVec`, then composed with mass
conservation (`∑ deg (h₀ − 1) = 0`) to supply the contraction's mode
hypothesis; the rest is the gluing the component-1 delivery licensed
(centered evolution `h_t − 1 = Pᵗ *ᵥ (h₀ − 1)` through the new
constant fix `P *ᵥ 1 = 1`). Per the proposal's own gate this re-score
fires only when the step's proof *and* its QA pass; both have now —
the QA pins the bound **attained exactly** on K₃ at two time steps
(`1/2 ≤ (1/4)·2`, `1/8 ≤ (1/16)·2`), derives the P₃ rate
basis-independently from two sum-of-squares certificates (the Dirichlet
identity `v ⬝ L_sym v = (v₀ − v₁/√2)² + (v₂ − v₁/√2)²` and its
`2‖v‖² − ·` counterpart — every eigenvalue pinned into `[0, 2]` with
no exact-spectrum computation), and delivers the connectivity negative
witness the whole program points at: a triangle⊕self-loop `Fin 4`
fixture, disconnected because loops are not support-graph edges, whose
spectrum `{0, 0, 3/2, 3/2}` is derived basis-independently so the rate
hypothesis *provably holds* at `r = 1/2` — the loop's `μ = 0` mode is
excluded from the rate hypothesis by design, exactly the hole
connectivity plugs — while the conclusion is refuted
(`χ²(3) = 3/8 > 3/64`). This is a new theorem family on the axis (a
convergence-rate/mixing statement, not packaging within the counted
walk-operator family); the axis's absent categories (heat kernels —
the reversibility proposal's gated Phase B — and the ℓ² → TV
conversion, the mixing proposal's own optional Step 4) are untouched
and both remain separate proposal-scale decisions. The QA axis count
synced to 1212/36 (`Mixing_QA` 67 → 117: the exact-equality
instantiation of a *final statement* at two time steps, the
SOS-derived rate band, and the disconnected-fixture
spectrum-then-refute witness — the mode exclusion of an *axiom-free*
theorem tied to its load-bearing hypothesis — strengthen existing
witness kinds without touching the parametric gap; held).

The QA axis was **held at 4.0** and its count synced to **1423/39** on
2026-08-23 (the Cheeger hard-direction Step 1b,
`proposals/discharge-perturbation-axioms.md`: `Cheeger_QA.lean` 59 → 78
— the co-area core's constants pinned numerically (the `K₂` **equality**
pin, both sides independently `2`, so any defective constant in the
layer-cake chain breaks it; the strict multi-level `C₄` witness
`20φ ≤ 10 < 16` through the exhaustively computed adjacent-pair
conductance; the dictionary's closed-set semantics pinned at a boundary
level) plus the minority-hypothesis refutation-on-omission (`4 ≤ 0` at
`![1,1]` with the hypothesis provably unsatisfiable at `t = 1`) —
witness kinds that strengthen existing coverage without touching the
parametric gap, hence the hold).

The QA axis was **held at 4.0** and its count synced to **1404/39** on
2026-08-23 (the Cheeger hard-direction Step 1a,
`proposals/discharge-perturbation-axioms.md`: `Cheeger_QA.lean` 33 → 59
— the pure-algebra component's constants pinned numerically (Component A
on `K₂` with all three quantities independently computed and the strict
gap `4 < 8` visible; the contraction in equality *and* strict cases on
`C₄`; the normalization cross-checked against the independently pinned
`λ₂(L_sym) = 2`) plus two guard refutations fencing the new theorems'
`IsSymm` and nonnegativity hypotheses against hypothesis-free forms —
witness kinds that strengthen existing coverage without touching the
parametric gap, hence the hold).

The QA axis was **held at 4.0** and its count synced to **1378/39** on
2026-08-22 (the Perron–Frobenius admission,
`proposals/admit-perron-frobenius.md`: the new
`LinearAlgebra/PerronFrobenius_QA.lean` at 36 declarations — the
axiom's Perron root derived to be exactly the hand value on two
asymmetric irreducible fixtures, the simplicity and
complex-spectrum-domination clauses pinned against hand factorizations,
and the proposal-mandated **imprimitive-cycle negative witness**
`strict_dominance_refuted_QA` (on the directed 2-cycle `!![0,4;1,0]`
the strengthening's `|μ| < r` is refuted at `|−2| = 2 = r` while the
admitted statement's `|−2| ≤ r` holds *with equality* — a genuinely new
witness kind, a falsification fence around an admitted axiom's
qualification level, and the first QA file in the LinearAlgebra domain;
the parametric coverage gap — unit tests over parametric definitions —
is untouched, hence the hold).

The QA axis was **held at 4.0** and its count synced to **1342/38** on
2026-08-22 (the directed normalized Laplacian,
`proposals/directed-graph-operators.md` Step 2 + the Step-3 agreement
brick, zero new axioms: `SpectralGraph/Directed_QA` 41 → 88
declarations — all nine `L_dir` entries computed from the entry form
on the all-square-degree fixture, the hypothesis-free symmetry
instantiated on asymmetric input, the conjugate's two sides
independently hand-checked, and a genuinely new **calibration negative
witness**: symmetric-but-not-PSD, `quadForm` refuted at `!![0,4;1,0]`
with `−1/2 < 0` — a refutation-of-transfer witness kind rather than a
new parametric capability, so the axis's named gap is untouched and
the score holds).

The QA axis was **held at 4.0** and its count synced to **1295/38** on
2026-08-22 (the directed degree layer, `proposals/directed-graph-operators.md`
Steps 0+1, zero new axioms: the new `SpectralGraph/Directed_QA` at 41
declarations — the genuinely-directed fixture with both degree functions
pinned raw through a `rfl` entry table, the negative witnesses
`outDeg ≠ inDeg` and the directed walk matrix's refuted symmetry, and
the load-bearing certification of the pre-existing undirected-shelf walk
operators on asymmetric input; witness kinds the axis already counts, so
no re-score).

The QA axis was previously **held at 4.0** and its count synced to
**1254/37** on
2026-08-22 (first the finite-relative-entropy program, then the
subgaussian repair-and-retire, `proposals/prove-subgaussian-tail-bound.md`
— `Scalar_QA` 6 → 17 with the falsification-pattern QA the axis already
counts: the retired axiom shape refuted *with its hypotheses proved
satisfied* at the `3 • δ₀` fixture, the empty-set junk mechanism
exhibited as a theorem, and the nonzero instance pinned raw on both
sides; a witness kind the axis already has, so no re-score). The QA
axis was previously held at 4.0 and synced to **1243/37** on
2026-08-22 (the finite-relative-entropy program,
`proposals/finite-relative-entropy.md`, zero new axioms; no subject-axis
re-score — entropy is not an SGT axis statement, it is backlog item 6's
entropy-half interface delivered in the new `InformationTheory` QA
domain): the new QA kinds strengthen existing witness families without
touching the parametric gap — a *hand-computed transcendental identity*
witness (the biased coin's divergence and entropy each reduced to closed
log-forms by `log_pow`/`log_mul`/`log_inv` algebra alone, independent of
the theorems), a *bridge cross-check* (the uniform bridge verified
numerically at the fair coin: `¼·log(27/16) = log 2 − ¼·log(256/27)`,
both sides independently pinned — load-bearing on the one theorem
connecting the two quantities), and an *equality-case-only strictness*
witness (the non-uniform `Fin 4` distribution strictly below the
entropy maximum, where strictness is derivable only through the
equality-case iff, not the plain bound).

Subject axis 5 (random walks and diffusion) was re-scored
**2.5 → 3.0** and the QA axis **held at 4.0** on 2026-08-22 (the
walk-matrix eigenpair transfer, `proposals/mixing-time-bound.md`
Step 1; zero new axioms): the axis's own evidence row had named the
walk-spectrum transfer as *the* gap on this axis, and it is now closed
as QA'd hard crust — eigenpairs conjugate through the proved similarity
in both directions (the non-symmetric walk matrix gains a spectrum
interface without ever being symmetric), the transition matrix's
eigenvalues are the reflected `1 − λ` with explicit nonzero
eigenvector witnesses (`walkEvals` +
`exists_eigenvector_walkTransitionMatrix_eq_walkEvals`), and the
transferred family is complete (`walk_eigvec_expansion`, the
diagonalizability interface). Per the proposal's own gate this re-score
was deferred until a step's proof *and* its QA passed; both have now.
This is a new capability family on the axis (spectral treatment of the
walk operator), not packaging; the axis's absent categories (mixing
statements themselves — the decay bound is the program's Step 2+ —,
heat kernels, reversibility) are untouched. The QA axis count synced to
1081/35 (the transfer QA's new kind — a non-symmetric operator's
spectrum pinned through transfer witnesses with raw-arithmetic
cross-checks and two shortcut-refuting guards — strengthens existing
witness kinds without touching the parametric gap; held).

Subject axis 5 (random walks and diffusion) was **held at 3.0** on
2026-08-22 (reversibility/detailed balance, `proposals/
reversibility-and-heat-semigroup.md` Phase A, both of the phase's steps
in one run; zero new axioms): `GraphTheory.Stationary` gained the
detailed-balance layer — the degree-measure identity
`deg i * P i j = deg j * P j i` (both sides exactly `A i j`), the
stationary-measure form `π i * P i j = π j * P j i` at
`π = deg/vol` (no volume hypothesis carried), the symmetrizability
packaging `(D * P).IsSymm` (reversibility *is* symmetrizability — the
self-adjointness interface spectral mixing arguments consume), and the
regular uniform-measure corollary composed from the already-proved
`transitionMatrix_symmetric`. QA: the P₃ fixture's balance instantiated
through the theorems at every index pair and cross-checked by raw
literal arithmetic (volume pinned to `4` independently), plus the
prescribed negative witness — an asymmetric weight matrix with positive
degrees where the hypothesis-free balance is refuted (`2 ≠ 1`) and the
symmetry hypothesis is provably violated at the same entry pair. The
score is **held** per protocol: this is a composed identity within the
walk-operator interface family already counted at the 2026-08-22
mixing-time re-score, not a new capability family; the axis's natural
re-score triggers remain the mixing-time decay bound itself (the
program's Step 2+) and heat kernels (Phase B, still gated on the
operator decision that proposal records). The QA axis count synced to
1095/35 (the new negative-witness kind — a *reversibility* guard tying
the failed identity to the violated symmetry hypothesis — strengthens
existing witness kinds; held).

Subject axis 5 (random walks and diffusion) was **held at 3.0** on
2026-08-22 (the ℓ²-mixing proxy, `proposals/mixing-time-bound.md`
Step 2, the new `GraphTheory.Mixing`; zero new axioms): the mixing
program's decide-and-record scoping gate was made first (ℓ² alone
satisfies the goal; within ℓ² the weighted χ² form is primary because
the Step-3 decay bound is Parseval-exact only in the π-weighted inner
product where the transferred eigenbasis is orthogonal). The axis's
walk-operator family gains the mixing objects the decay statement
quantifies over — `stationaryVec` (π = deg/vol, proved stationary,
positive, a probability vector), `walkDistribution` (`(Pᵀ)ᵗ *ᵥ δₓ`
with evolution equations and mass conservation), `walkDensity` with
the density-coordinate evolution `walkDensity_succ` (`h_{t+1} =
P *ᵥ h_t`, the first consumer of the same day's detailed-balance
interface — the form the transferred eigenbasis diagonalizes), and
`chiSquareDistance` (nonnegative, vanishing iff the law is π, the
`t = 0` normalization `(π x)⁻¹ − 1`, the density-form equivalence, and
the plain-ℓ² corollary bridge). The score is **held** per the
proposal's own operating instruction — no re-score until a step's
*proof* lands and its QA passes, and the mixing statement itself is
Step 3's decay bound; the QA'd P₃ fixture already pins the λ* = 1
bipartite non-decay (`χ²(1) = χ²(2) = 1`) that the Step-3 bound must
reproduce, not contradict. The QA axis count synced to 1128/36 (the
new QA kinds — a mixing-distance fixture with both-route pins and the
two hypothesis-guards for stationarity and vanishing — strengthen
existing witness kinds without touching the parametric gap; held).

Subject axis 2 (spectral linear algebra) was re-scored **4.0 → 4.5**
and the QA axis **held at 4.0** on 2026-08-21 (the band-projector Step
4 delivery, proposal `spectral-band-projectors.md`; the program is
complete): the two prior records reserved exactly this event as the
trigger — "the genuinely new capability dimension, consuming Mathlib's
Hilbert projection theorem, is Step 4" — and it landed as reserved. The
axis's spectral-operator layer gains a *characterized
closest-point/projection interface* into Mathlib's
inner-product-space machinery (`Analysis/InnerProductSpace/Projection.lean`,
the SGT center's first consumption of it): the residual-orthogonality
engine, the identification of the band projector with
`orthogonalProjection` at its transported range, and the closest-point
minimality over its fixed space — so every downstream
distance-to-band / best-band-approximation claim is now derivable
rather than re-provable per use. This is an interface capability
family, not another member of the counted band-operator family (the
Step-2/Step-3 holds) and not packaging. The QA axis held: `Band_QA`
(+25 declarations by the generator metric, 109 in file) strengthens
existing kinds (attainment and strict-improvement numeric pins through
the `‖e v‖² = v ⬝ᵥ v` identity, the dual-route residual-orthogonality
check, an independent raw-arithmetic cross-check of the whole
closest-point line inequality, and the fixed-space guard refuting the
hypothesis-free form at the unfiltered signal) while the parametric
gap stays untouched; the count synced to 998/34.

Subject axis 2 (spectral linear algebra) was re-scored **3.5 → 4.0**
and the QA axis **held at 4.0** on 2026-08-20 (the Tikhonov delivery,
proposal `tikhonov-shrinkage-filter.md`): axis 2 gains its first
*constructed application-facing operator family* — the
regularization/smoothing filter with its eigenbasis definition,
closed-form eigencoefficient algebra, normal equation plus converse
characterization, strict-convexity minimality/uniqueness, mean
preservation, and not-a-projection theorem — a new capability family
rather than packaging or a completion of the counted resolvent
interface (the EML re-score's precedent class). The QA axis held: the
Tikhonov QA (+30 declarations, 890/33) strengthens an existing kind
(pinning a noncomputable spectral object through a proved
characterization against hand-computed values, plus a guard refuted
on-omission) while the parametric gap stays untouched; the count
synced to 890/33.

Subject axis 2 and the QA axis were **held** on 2026-08-20 (the
band-projector Step 1 delivery, proposal
`spectral-band-projectors.md`): axis 2 gains the two-sided band
projector family — the `(a, b]` band as the difference of two
`spectralProjector` calls, idempotence through the new nestedness
cross-law, and the mode-selection action interface — which extends the
*constructed application-facing operator family* capability the axis
already counted at the Tikhonov re-score (a second member of the
counted class, not a new capability family; Steps 2–4 of the proposal
— orthogonality, partition completeness, the Hilbert projection
specialization — remain open and are the natural next re-score
triggers). The QA axis held: `Band_QA` (+27 declarations, 917/34)
strengthens an existing kind (pinning a noncomputable spectral object
through proved characterizations against hand-computed values, plus
guards — here the between-eigenvalues zero band and the
excluded-mode-not-fixed witness) while the parametric gap stays
untouched; the count synced to 917/34.

Subject axis 2 and the QA axis were **held** on 2026-08-20 (the
band-projector Step 3 delivery, proposal
`spectral-band-projectors.md`): axis 2 gains completeness under a
partition — the unconditional telescoping law, the covering-family
resolution of the identity from exactly the two endpoint hypotheses,
monotone-family orthogonality (where monotonicity is exactly what is
consumed), and the consumer's vector decomposition `x = ∑ B_k x` —
which completes the partition half of the band family counted at
Step 1 (the Hilbert projection specialization, Step 4, remains open
and stays the natural re-score trigger, being the genuinely new
capability dimension: consuming Mathlib's inner-product-space
machinery). The QA axis held: `Band_QA` (+41 declarations, 973/34)
strengthens existing kinds (dual-route theorem-vs-pinned-value
summation checks, both endpoint guards each with its violated
hypothesis separately refuted, and the non-monotone telescoping
witness) while the parametric gap stays untouched; the count synced
to 973/34.

Subject axis 2 and the QA axis were **held** on 2026-08-20 (the
band-projector Step 2 delivery, proposal
`spectral-band-projectors.md`): axis 2 gains the disjoint-band
orthogonality layer — both composition orders through the collapsing
four-term cross-law expansion, image orthogonality, and
shared-mode-freeness — which completes the pairwise half of the band
family counted at Step 1 (partition completeness, Step 3, and the
Hilbert projection specialization, Step 4, remain open and stay the
natural re-score triggers). The QA axis held: `Band_QA` (+16
declarations, 932/34) strengthens existing kinds (dual-route
theorem-vs-raw-literal checks, a same-band counter-witness separating
disjointness from fixture zeros, and the overlap guard refuting the
hypothesis-free form) while the parametric gap stays untouched; the
count synced to 932/34.

Subject axis 5 (random walks and diffusion) was re-scored
**3.5 → 4.0** and the QA axis **held at 4.0** on 2026-08-23 (the
heat-semigroup payoff statement, `proposals/reversibility-and-
heat-semigroup.md` Phase B Step 4 — the proposal COMPLETE; zero new
axioms): the standing re-score trigger the Step-3 hold record named —
"the axis's remaining heat-kernel *statement* (eigenmode decay with
the DC limit, Step 4)" — is now delivered as QA'd hard crust, and with
it the axis's continuous-time side is a closed capability family: the
definition and identity (Step 1), the semigroup law (Step 2), mass
conservation (Step 3), and now per-mode decay (`heatKernel_mulVec_
eigvecOf` at every time with the sorted-spectrum monotonicity and the
PSD dissipation bound), the spectral-calculus expansion
(`heatKernel_mulVec_eq_sum`), and the convergence statement itself
(`heatKernel_mulVec_tendsto_atTop`: free diffusion on a connected
graph leaves only the DC component — the mean vector — as `t → ∞`,
load-bearing on PSD, the kernel characterization, and the proved
orthonormal eigenbasis, with Step 3's convergence machinery consumed
by the eigenmode engine rather than bypassed). Per protocol this is a
new theorem family on the axis (a convergence/decay statement for the
heat flow, not packaging within the counted interface), and the
external-consumer interface (`sgt-gaps.md`) is fully discharged. The
axis's absent categories reduce to one: the ℓ² → total-variation
conversion (the mixing proposal's own optional Step 4, a separate
proposal-scale decision). The QA axis count synced to 1503/40
(`Heat_QA` 25 → 46: two independent routes to each of the mode-decay
and DC-limit statements, the engine⇄collapse cross-validation at a
nonzero eigenvalue, and the spectrum-pinned monotonicity
instantiation — witness kinds that strengthen existing coverage
without touching the parametric gap; held).

Subject axis 5 (random walks and diffusion) was **held at 4.0** and the
QA axis **held at 4.0** on 2026-08-23 (the heat-flow derivative at
zero, `proposals/reversibility-and-heat-semigroup.md` Phase C Step 1,
the second `sgt-gaps.md` request; zero new axioms): the derivative
`heatKernel_mulVec_hasDerivAt_zero` (`d/dt e^{-tL} x |₀ = -L x` in
`HasDerivAt` form, entrywise engine + `hasDerivAt_pi` assembly) is the
infinitesimal-generator packaging of the continuous-time family the
axis already counts at 4.0 — a new *calculus* statement on the closed
capability family rather than a new capability category, so per
protocol this is a hold with the natural re-score trigger unchanged
(the ℓ² → total-variation conversion remains the axis's one absent
category). The QA axis count synced to 1507/40 (`Heat_QA` 46 → 50: the
numeric derivative pinned by two independent routes — eigenbasis
expansion + termwise differentiation vs. closed-form collapse + scalar
calculus — and infinitesimal mass conservation cross-checked against
Step 3's conservation in both directions; witness kinds that strengthen
existing coverage without touching the parametric gap; held).

Subject axis 5 (random walks and diffusion) was **held at 4.0** and the
QA axis **held at 4.0** on 2026-08-23 (the first-order remainder bound,
`proposals/reversibility-and-heat-semigroup.md` Phase C Step 2,
completing Phase C and the proposal; zero new axioms): the bound
`|(e^{-tL} x) a − x a + t (L x) a| ≤ t² · ∑ᵢ λᵢ² |vᵢ ⬝ᵥ x| |vᵢ a|` on
the window `|t · λᵢ| ≤ 1` (plus its uniform `[0, T]` interval
packaging) is a quantitative refinement *within* the calculus layer the
axis already counts at 4.0 — the Taylor-remainder companion of the
delivered derivative, not a new capability category — so per protocol
this is a hold with the natural re-score trigger unchanged (the ℓ² →
total-variation conversion remains the axis's one absent category).
The QA axis count synced earlier to 1546/40 with the Tikhonov
Phase-2 delivery (superseded by the 1571/41 sync above — the
discrete-affine delivery's own note; `Tikhonov_QA` +24: the two-mode-tail closed-form pin
with collapsing exact numerics, the concrete-tolerance consumption, and
both boundary refutations — scalar `lam = 0` and tail-with-kernel-mode
— the latter the `sgt-gaps.md` requester's mandated non-overclaim
witness; held at 4.0, the parametric/randomized gap untouched).

Earlier sync note: the QA axis count synced to 1522/40 (`Heat_QA` 50 → 66: the spectral
constant evaluated to exactly `4` on K₂ with the eigenmode structure
making it orientation-sign-independent, the raw closed-form value
`1 − 2t − e^{-2t}` pinned at every time, the concrete bounds composed
at two times pinning the `t²` scaling, and the window fence refuted
beyond `t = 1/2`; held).

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
