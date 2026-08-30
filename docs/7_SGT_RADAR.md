# SGT Coverage Radar

**Status:** Canonical coverage assessment  
**Last reviewed:** August 27, 2026

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
| 1 | Graph and Laplacian models | 4.0 | Weighted arbitrary graphs (`WAdj`), combinatorial Laplacian with symmetry/kernel/Dirichlet/PSD **proved**; normalized Laplacian both regular (`Cheeger.regularNormalizedLaplacian`) and general/irregular (`Normalized.normalizedLaplacian`, congruence + similarity **proved**); both `SimpleGraph` adapter directions landed — `supportGraph : WAdj → SimpleGraph` (2026-08-18, consumed by the kernel characterization) and `SimpleGraph.toWAdj` (2026-08-18, `GraphTheory.SimpleGraphAdapter`, with the proved agreement family `laplacian G.toWAdj = G.lapMatrix ℝ`, degree/volume/boundary agreement, handshake, and the roundtrip `supportGraph (toWAdj G) = G`); the directed operators **delivered** (2026-08-22, backlog item 8: `GraphTheory.Directed`'s `inDeg`/`rfl` identifications and `directedNormalizedLaplacian I − ½(SAS + SAᵀS)` with hypothesis-free symmetry and the `√D L_dir √D` conjugate — this row's previous "absent: directed graphs" clause was stale, repaired with the 2026-08-26 sync); the magnetic Laplacian **delivered** (2026-08-25, the shelf's first complex Hermitian object, with the gauge kernel characterization now at action level); and **signed graphs delivered** (2026-08-26, `GraphTheory.Signed`, `proposals/signed-graphs-balance.md`: the signed Laplacian `D − A_σ` at a `{±1}` signing, the magnetic π-flux join with the energy identity derived from the delivered `magnetic_energy`, the kernel↔edge-alignment characterization, **Harary balance in kernel form** `IsBalanced A s ↔ ∃ x ≠ 0, L_σ *ᵥ x = 0` on connected symmetric nonnegative input, positive definiteness under frustration, and the switching similarity `diag(g) · L_σ · diag(g) = laplacian A` with two-way eigenpair transfer — all proved, zero new axioms). Re-scored 3.5 → 4.0 with the signed-graph delivery: the axis's two previously-named absent categories (directed, signed) are both now occupied by verified interfaces, the signed slice being a new model family consuming the magnetic program (load-bearing growth), not packaging. |
| 2 | Spectral linear algebra | 4.5 | Sorted spectrum `evals` + monotonicity + `evals_mem_eigvalOf` (**proved**); `secondEval` (matrix-facing λ₂ API) and the trace/Rayleigh pinning tools `eigvalOf_sum_eq_trace`, `eigvalOf_le_of_quadForm_nonpos` **proved** (2026-08-18); eigenbasis orthonormality/completeness and projector algebra **proved**; interlacing **proved** (2026-08-18: `eigen_interlacing_principal_submatrix` retired from axiom, derived from the Courant–Fischer engine through the extend-by-zero padding bridge and the subspace-intersection dimension count; QA pins the window to `0 ≤ 1 ≤ 2` on `K₂` with a singleton submatrix, with both collapsed one-sided bounds refuted); Weyl **proved** (retired from axiom 2026-08-20, `proposals/discharge-perturbation-axioms.md`: the additive bounds `weyl_additive_upper`/`weyl_additive_lower` from this axis's min–max engine plus the bottom-domination mirror `evals_first_mul_dotProduct_le_quadForm`, composed with the operator-norm bridge — gap stability fully hard crust) with Davis–Kahan **proved** (retired 2026-08-21 — see axis 7) and the two-point wrapper **fully hard crust**. **The operator-norm ↔ spectrum bridge is proved** (2026-08-19, `Analysis.OperatorTheory.Resolvent`, proposal `resolvent-calculus-psd.md` Step 0): for every real symmetric matrix, `|λ| ≤ ‖M‖` for all eigenvalues and conversely `‖M‖ ≤ c` when all `|λ| ≤ c`, packaged as `l2OpNorm_eq_max_abs_evals` (`‖M‖ = max |evals hM 0| |evals hM last|`) — the axis's first operator-norm identity, and the finite-dimensional spectral-radius fact for real symmetric matrices; route recorded after the C*-algebra thread `IsSelfAdjoint.spectralRadius_eq_nnnorm` was elaboration-verified **structurally inapplicable** to real matrices (`CStarAlgebra` requires `NormedAlgebra ℂ`), the fallback proved from the eigenbasis machinery (Parseval + eigenaction + `cstar_norm_def` transport). Step 1 added shifted-PSD invertibility (`M + t•1`, `t > 0`, no symmetry needed) and the resolvent identity `(A+1)⁻¹ − (B+1)⁻¹ = (A+1)⁻¹(B−A)(B+1)⁻¹`. Step 2 (2026-08-19) completed the family with the operator-norm bounds — `‖(M + t•1)⁻¹‖ ≤ t⁻¹` for any quadForm-nonneg matrix (no symmetry; the energy route: `t‖y‖² ≤ quadForm M y + t‖y‖² = y ⬝ᵥ x ≤ ‖y‖‖x‖`, a recorded deviation from the sketched eigenvalue transfer) and the `1`-Lipschitz stability `‖(A+1)⁻¹ − (B+1)⁻¹‖ ≤ ‖A−B‖` (Step-1 identity + `norm_mul_le` + the norm bound; QA shows both attained with equality at `K₂`, the energy and spectral routes agreeing at `1`, and the shift/hypothesis guards refuted-on-omission). Step 3 (2026-08-20) completed the program with **injectivity of the resolvent map** — `A ≠ B → (A+1)⁻¹ ≠ (B+1)⁻¹` on quadForm-nonneg matrices (contrapose the Step-1 identity, cancel both invertible outer factors), with the packaged iff `inv_add_one_eq_inv_add_one_iff_of_quadForm_nonneg` stating resolvent equality as a certificate of matrix equality; QA instantiates it at two distinct PSD pairs with both resolvents left-inverse-pinned (`lap2` vs `0`, `lap2` vs `mat2`), and **refutes the hypothesis-free implication** at `A = -1` vs `-1 + nilpotent` (both `+1` shifts singular, both resolvents the junk `0`). Score held at 3.5 at Step 3 (the resolvent family completed within the operator-norm interface already counted at Step 0 — completion, not a new capability family). **Tikhonov regularization in the Laplacian eigenbasis is proved** (2026-08-20, `GraphTheory.Tikhonov`, proposal `tikhonov-shrinkage-filter.md`, zero new axioms): the axis's first *constructed application-facing operator family* — the smoothing filter minimizing `‖x−y‖² + (1/π)·xᵀLx`, defined by the eigenbasis formula with the closed-form eigencoefficient shrinkage identity, the normal equation `(L+π•1) *ᵥ x* = π•y` and its converse characterization, minimality/uniqueness through the strict-convexity decomposition `obj(x)−obj(x*) = ∑_k (1+λ_k/π)(d_k−d*_k)²`, mean preservation (symmetry + `π ≠ 0` only), and the not-a-projection idempotence-failure theorem distinguishing it from `spectralProjector`; the attenuation factor's endpoint behavior corrected against the proposal's sketch (`= 1` exactly at `λ = 0` — the kernel mode untouched — and `< 1` iff `λ > 0`). Re-scored 3.5 → 4.0 with this milestone (a new capability family — a constructed spectral filter with a variational characterization, not packaging and not a completion of the counted resolvent interface; QA pins the minimizer against a hand-solved linear system through the converse characterization). **The two-sided spectral band projectors are proved** (2026-08-20, `GraphTheory.Band`, proposal `spectral-band-projectors.md` Step 1, zero new axioms): the `(a, b]` band as the difference of two `spectralProjector` calls with idempotence through the **nestedness cross-law** `P_{c₁} * P_{c₂} = P_{min c₁ c₂}` (added to `GraphTheory.Spectral` with its ordered forms; the old `spectralProjector_idempotent` re-derived from it at unchanged statement), the complete projector-eigenvector action description (`P_c *ᵥ vᵢ = if λᵢ ≤ c then vᵢ else 0`), and the band mode-selection interface — in-band modes fixed, out-of-band modes annihilated — plus the below-spectrum special case and the covering band. Step 2 (2026-08-20, same proposal) added the **orthogonality layer for disjoint bands**: the two band projectors compose to zero in both orders (the four-term cross-law expansion collapsing under `b ≤ c` — exactly interval disjointness, load-bearing), their images are dot-orthogonal (`bandProjector_inner_eq_zero`), and no nonzero vector is fixed by both (`eq_zero_of_bandProjector_mulVec_eq_self`, the subspace-level reading of "they share no eigenvector"); score held at 4.0 (completion within the band family already counted at Step 1; Steps 3–4 — partition completeness and the Hilbert projection specialization — remain the natural re-score triggers). Step 3 (2026-08-20, same proposal) added **completeness under a partition**: the unconditional telescoping law `∑_{k<n} B(t_k, t_{k+1}) = P_{t_n} − P_{t_0}` for *any* threshold sequence (ordered or not — load-bearing on the band definition's exact difference shape), the covering-family resolution of the identity `∑ B_k = 1` from exactly the two endpoint hypotheses (`t₀` below every eigenvalue, `tₙ` covering them all — both refutable-on-omission), distinct members of a **monotone** family composing to zero (monotonicity deliberately not a hypothesis of the sum identity — it is exactly what the orthogonality statement consumes, making the family a partition), and the consumer's vector decomposition `x = ∑ B_k *ᵥ x`; score held at 4.0 (the same-family completion the Step-1 re-score named as a trigger — the genuinely new capability dimension, consuming Mathlib's Hilbert projection theorem, is Step 4). Step 4 (2026-08-21, same proposal, program complete) added **the Hilbert-projection specialization**: the residual-orthogonality engine `(x − B*ᵥx) ⬝ᵥ (B*ᵥz) = 0` (load-bearing on exactly the two Step-1 facts — symmetry and idempotence), the identification `bandProjector_toEuclidean_apply_eq_orthogonalProjection` (Mathlib's `orthogonalProjection` at the transported band range *is* the band-filtered signal — the SGT center's first consumption of `Analysis/InnerProductSpace/Projection.lean`, through the `toEuclideanLin` transport the resolvent Step-0 record named as precedent), and the closest-point property `norm_sub_bandProjector_apply_le` (`‖e x − e (B*ᵥx)‖ ≤ ‖e x − e y‖` for every fixed point `y` — equivalently every range member — from `orthogonalProjection_minimal` + `ciInf_le`; stated at `EuclideanSpace ℝ V` because the bare `V → ℝ` default norm is the sup norm). QA pins attainment (`= 4` exactly), strict improvement over the zero signal (`4 ≤ 5`, the 3-4-5 triangle), the whole range line `4 ≤ √((3−t)²+16)` with an independent raw-arithmetic cross-check, and refutes the hypothesis-free form at the unfiltered signal. Re-scored 4.0 → 4.5 with this milestone (the capability dimension the two prior records explicitly reserved as the trigger: the spectral-operator layer gains a *characterized closest-point/projection interface* into Mathlib's inner-product-space machinery — every downstream distance-to-band and best-band-approximation claim is now derivable — not another member of the counted band family). Davis–Kahan remains admitted. |
| 3 | Variational and functional methods | 4.0 | `quadForm`/Dirichlet identity and PSD **proved**; `rayleigh` defined; normalized↔combinatorial transfer **proved** (2026-08-17, `VariationalTransfer`: congruence lemma, degree-weighted Rayleigh quotient `rayleigh L_sym (√D y) = (yᵀ L y)/∑ deg·y²`, `normalizedLaplacian_psd`); **λ₂ variational characterization (Courant–Fischer) now proved** (2026-08-18, `lambda2_variational`: `λ₂ = sInf` of the Rayleigh quotient over nonzero vectors ⊥ `onesVec`, for symmetric nonnegative weights — retired from axiom, whose symmetry-only shape was false and is refuted in QA; matrix-world proof through eigenbasis expansion, Parseval, the spectral resolution of `quadForm`, and two sorted-multiset multiplicity pins; the semidefinite Cauchy–Schwarz `laplacian_cauchy_schwarz` is also proved); **general Courant–Fischer min–max proved at every index** (2026-08-18, proposal `prove-courant-fischer.md`: `evals_min_max` with the two witness directions `exists_submodule_forall_rayleigh_le` / `exists_ne_mem_rayleigh_ge_of_finrank_eq` — only symmetry assumed, no positivity or graph structure; the general-`k` multiplicity pins and component-form Rayleigh bounds are new public center API; QA pins both directions on a spectrum-`[1,3]` fixture, derives the top-eigenvalue domination universal through the theorem, and refutes wrong and under-dimensional subspaces plus an interior-index wrong two-dimensional subspace on the path Laplacian). Re-scored 3.5 → 4.0 with this milestone (the fixed-index engine generalized to the full subspace min–max; the axis's remaining named gaps are functional inequalities). **The connectivity transfer is proved** (2026-08-26, the irregular family's own priced follow-on, pure hard crust): `secondEval_normalizedLaplacian_pos_iff_connected` — `0 < λ₂(L_sym) ↔ connected` on every symmetric nonnegative positive-degree graph — through the kernel characterization `normalizedLaplacian_mulVec_eq_zero_iff` (the stretched-constant line `√D·1`, via the electrical program's combinatorial kernel characterization), the Fiedler mirror `secondEval_normalizedLaplacian_pos_of_connected` (PSD + sorted + multiplicity pin + orthonormality), the disconnected converse via the component-indicator Gram–Schmidt route through `secondEval_le_rayleigh_of_ker`, and the Cheeger consumer corollary `cheegerConstant_pos_of_connected` (`0 < φ` on connected irregular graphs, joined to the delivered easy direction). Absent: Poincaré, log-Sobolev. |
| 4 | Cuts, expansion, clustering | 5.0 | `vol`/`boundary`/`conductance`/`cheegerConstant` with nonnegativity, GLB, and full cut duality (**proved**, run 10); **the Cheeger *upper* bound (easy direction, `λ₂(L_sym) ≤ 2φ`) is proved** (2026-08-18, `cheeger_upper_bound` retired from axiom) — the volume-centered cut-indicator interface (`cutTestVector`: orthogonality, the general weighted-graph cut-energy identity `xᵀLx = boundary·vol V²`, the norm identity, and the Rayleigh value `boundary·vol V/(vol S·vol Sᶜ)`), instantiated in QA on `K₂` (bound attained: `λ₂ = 2φ = 2`) and on `C₄` (`λ₂ ≤ 1` through the exhaustively computed conductance `1/2`); **the Cheeger *lower* bound (hard direction) is proved** (2026-08-23, `cheeger_lower_bound` retired from axiom at the unchanged statement by the median-split route of `proposals/discharge-perturbation-axioms.md` Steps 1a/1b/1c — the Cauchy–Schwarz core and fused median-part contraction, the interval-integral co-area core `coarea_core`, and the median/level-set/assembly layer: `exists_median` by pure Finset arithmetic, the per-part bound `φ²·d·‖y‖² ≤ E'(y)`, the norm split, the sweep lemma `φ²/2 ≤ R_{L_sym}(x)` for every nonzero `x ⊥ 1`, closed through `secondEval_variational`; explicit axioms 10 → 9; the spectral side had been restated 2026-08-18 at the source-faithful `secondEval (L_sym)` shape after QA refuted the previous `lambda2`-composed side, and is pinned to the classical value `2` on `K₂`). Re-scored 4.0 → 4.5 with this milestone (both directions of the axis's central isoperimetric–spectral family now proved — a new theorem family, the hard direction, not packaging). **The Fiedler-vector interface exists and the sign partition is proved sane (2026-08-18, `GraphTheory.Fiedler`, proposal `fiedler-partitioning.md` Phase A — no new axioms):** `fiedlerVector` (the eigenbasis vector at `lambda2`) with the eigenvector equation, unit norm, and `fiedlerVector_quadForm`; the algebraic-connectivity certificate `lambda2_pos_of_connected` (connected ⇒ `0 < λ₂`, consuming the kernel characterization and both multiplicity pins); and `fiedlerPartition` proved nonempty and proper on connected graphs through the zero-sum identity (QA on the `P₄` barbell — two `K₂` near-cliques joined by a bridge — derives the sign pattern from the eigen equations and computes the partition to be exactly the known good cut `{0,1}` or its complement: boundary `1`, volume `3`, conductance `1/3`). **The Expander Mixing Lemma is proved** (2026-08-19, proposal `decidable-spectral-certificates.md` Step 2, `GraphTheory.Expander` + two generic additions to `GraphTheory.Spectral`; zero new axioms): for symmetric, nonnegative, `d`-regular networks with Laplacian-spectrum hypothesis `μ ≥ max |d − λ₂(L)| |d − λ_max(L)|`, the `(S,T)` cut weight deviates from the population main term `d•|S|•|T|/|V|` by at most `μ • √(|S||T|(|V|−|S|)(|V|−|T|))/|V|` — the axis's first discrepancy/pseudorandomness result, i.e. the quantitative form of "spectral gap ⇒ cut pseudorandomness". Route: a Rayleigh sandwich on `1⊥` (the `d`-regular identity `xᵀAx + xᵀLx = d•‖x‖²` trading the proved `λ₂•‖x‖² ≤ xᵀLx` against the new generic top domination `xᵀLx ≤ λ_max•‖x‖²`), then the sharp bilinear form by the polarization/scaling trick (`a² = Y, b² = X` attains AM–GM equality — no slack), then the variance identity for the geometric factor; no eigenspace split, no kernel case analysis, no affine spectrum transfer. QA (+19 declarations): the spectral hypothesis **derived on the fixture** (test vector, sum-of-squares, PSD) and the bound **attained exactly** on `C₄`'s opposite cut and on the alternating vector — the derived `μ` is tight. Re-scored 3.5 → 4.0 with this milestone (a new theorem family — spectral–combinatorial discrepancy — not packaging; the certified partition-quality guarantee remains Phase B, and multiway/irregular variants remain absent). Step 4 (2026-08-19, QA-only) made the fixture evidence exact: `lambda2 (C₄) = 2` and `λ_max(C₄) = 4` pinned (Poincaré through the lower half of `lambda2_variational`; the alternating vector through `quadForm_le_evals_last`), so `μ(C₄) = 2` *exactly* — the Ramanujan bound `2√(d−1)` attained with equality; `K₃` pinned (`λ₂ = λ_max = 3`, `μ = 1`, strictly Ramanujan, EML attained exactly on both cuts tested) and the `C₆` EML instantiated with derived `μ ≤ 2`, attained on the alternating cut — the Step 0 scope decision's `Kₙ`/`Cₙ` Ramanujan fixture family delivered. Score held at 4.0 (QA strengthening, no new theorem family). > **The certified partition-quality guarantee is delivered** (2026-08-23, `fiedler-partitioning.md` Phase B, pure hard crust, zero new axioms): `cheeger_cut_existence` — on every connected `d`-regular graph, `∃ S` nonempty proper with `conductance S ^ 2 ≤ 2 · lambda2 / d` — the axis's first application-ring certificate (an algorithmically consumable existence guarantee, not just an inequality about an infimum), assembled from the proved sweep lemma at the Fiedler vector, the Rayleigh transfer `R_{L_sym}(f) = lambda2 / d`, and the new `cheegerConstant_attained` (the conductance minimum realized by `Finset.exists_min_image` over the filtered powerset). The proposal's operator gate dissolved with the 2026-08-23 hard-direction retirement, so this is composition of proved pieces, and the score **held at 4.5** per protocol: the certificate's mathematical content is the (already counted) Cheeger family plus a finiteness attainment lemma — completion within the counted family, not a new theorem family; the honest statement-shape deviation is recorded (the sign cut is not certifiable from λ₂ alone; the certified object is the minimizer, and the sweep-level-set extraction is the named strengthening follow-on). QA is load-bearing on the retirement (the Rayleigh transfer cross-checked against the pinned `lambda2 (K₂) = 2`; the regularity hypothesis refuted-on-omission at `d = 100`). **The swept-level-set certified cut is delivered** (2026-08-24, `proposals/sweep-cut-extraction.md`, Phase C in `GraphTheory.Fiedler` + the `SweepExtraction` section of `GraphTheory.Cheeger`; zero new axioms): `fiedler_sweep_cut` — on every connected `d`-regular graph, a *closed superlevel or sublevel set of the Fiedler vector itself* (the object the spectral-partitioning sweep returns, not the non-constructive conductance minimizer of Phase B) satisfies `conductance S² ≤ 2λ₂/d` — through the per-part `sweep_level_extract` (attainment over the finitely many positive values of `y²`, the covering fact that every closed superlevel set equals one at an attained value, a non-strict layer-cake integration cloned from `coarea_core`, Component A) and the median assembly `cheeger_sweep_cut` (same constant 2 as `cheeger_sweep`, witness explicit — a strengthening of the sweep lemma itself, load-bearing on the whole Step-1a/1b/1c chain). **The irregular (volume-weighted) easy direction is proved** (2026-08-25, `proposals/irregular-cheeger-variational-transfer.md` Steps 0+1: `cheeger_upper_bound_normalized` — `secondEval (normalizedLaplacian A) ≤ 2 * cheegerConstant A` on arbitrary symmetric nonnegative positive-degree graphs, no regularity, no connectivity — through the degree-stretched cut indicator `√D · cutTestVector` (orthogonality to the true kernel vector `√D · 1` by the volume identity, no regularity), the new general-kernel `secondEval_le_rayleigh_of_ker`, and the `VariationalTransfer` congruence engine; the same Rayleigh quotient as the regular family, closing arithmetic verbatim; QA on `P₃` with the eigenpair-independent spectral bound and both fences). **The irregular (volume-weighted) hard direction is proved — the full irregular Cheeger pair delivered** (2026-08-25/26, the same proposal's deferred half, opened by run `20260825T221207Z-run-1` and verified/recorded by continuation `20260826T010711Z-run-1`: `cheeger_lower_bound_normalized` — `cheegerConstant A ^ 2 / 2 ≤ secondEval (normalizedLaplacian A)` on exactly the easy direction's hypotheses — through the `VolumeHardDirection` section of `Cheeger.lean` (the volume median `exists_median_vol`, minority conductance at volume strength where `min (vol S) (vol Sᶜ) = vol S` is pure `vol_compl` arithmetic, the degree-weighted layer-cake `coarea_core_vol`, the per-part bound with the regular family's already-degree-weighted Cauchy–Schwarz core and fused contraction consumed verbatim, the weighted norm split), the new general-kernel sInf engine `secondEval_variational_of_ker` in `Spectral.lean` (Courant–Fischer at an arbitrary kernel vector — every future irregular consumer whose operator is killed by `√D·1`, not `1`, shares it), and the sweep lemma + headline in `VariationalTransfer.lean`, the sInf set's nonemptiness witnessed by the easy direction's own cut test vector — one test object, both directions of the pair; QA +31 with the P₃ headline joined to the easy delivery's independently pinned `λ₂ ≤ 1` bracket, the K₂ regular recovery at `λ₂ = 2` raw, and the minority/nonnegativity fences in proved form). **The volume-weighted sweep-cut extraction is proved** (2026-08-26, the irregular family's follow-on delivery: `sweep_level_extract_vol` + `cheeger_sweep_cut_normalized` — the regular family's 2026-08-24 attainment route ported to the volume measure, the `boundary / vol` ratio minimized over the positive values of `y²`, so every nonzero degree-weighted zero-sum `f` carries an *explicit swept* nonempty proper cut at `conductance² ≤ 2 · R_{L_sym}(√D f)`, no regularity/connectivity/cardinality hypothesis; QA +10 with the witness level set forced on irregular input, the shared cut test vector now consumed by both Cheeger directions *and* the sweep, and the degree-weighted zero-sum fence refuting the hypothesis-dropped conclusion for every swept candidate). **The irregular Fiedler instantiation is proved — the family's algorithm-facing capstone** (2026-08-26, the standing handoff's named bounded candidate: `fiedler_sweep_cut_normalized` in `VariationalTransfer.lean`'s new Fiedler-instantiation section — the normalized Fiedler interface (`fiedlerIndexNormalized`/`fiedlerVectorNormalized`: eigen equation, unit norm, `rayleigh = λ₂`) plus the `D^{-1/2}` pullback `fiedlerSweepVector` with the stretch cancellation `√D f = u`, nonvanishing, and the degree-weighted zero-sum obtained from the eigen-orthogonality hinge at the true kernel vector `√D·1` (connectivity's exact entry point, `0 < λ₂` from the delivered transfer) — so that on every connected symmetric nonnegative positive-degree graph an explicit closed superlevel/sublevel cut of the sweep vector itself satisfies `conductance S² ≤ 2 λ₂ (L_sym)`, exactly the regular family's `fiedler_sweep_cut` constant `2λ₂/d` on the cone: the spectral-partitioning algorithm's own input and output as one shelf theorem; QA +9 with the exact pin `λ₂ (L_sym P₃) = 1` (the new `≥ 1` side by the `2 x₁²` sum-of-squares through the sInf engine, nonemptiness witnessed by the concrete eigenpair at Rayleigh exactly `1`), the instances on `P₃`/`K₂` joined to independent pins, the pullback hinge raw at the concrete eigenpair, and the connectivity mechanism fenced on the disconnected fixture — at the pinned `λ₂ = 0`, a kernel eigenvector provably violates the orthogonality hinge, so the constraint genuinely needs the connectivity-supplied gap). Held at 4.5 per protocol: the Fiedler instantiation is the algorithm-facing join within the already-counted irregular Cheeger + connectivity families (composition with a new exact spectral pin), not a new theorem family; the irregular statement and its sweep extraction are complete, but the raise this would earn is bounded by the axis's genuinely remaining absent category. **The multiway (higher-order Cheeger) easy direction is proved** (2026-08-26, `proposals/multiway-expansion.md` COMPLETE, pure hard crust, zero new axioms, `GraphTheory.Multiway` + a k-general engine extension of `GraphTheory.Spectral`): `cheeger_upper_bound_multiway` — `evals (L_sym) ⟨k−1⟩ ≤ 2 · maxᵢ (boundary(Sᵢ)/vol(Sᵢ))` for *every* disjoint nonempty k-family on every symmetric nonnegative positive-degree graph (the every-family form: no partition-space attainment, no ρ_k minimum), plus the conductance form at `2 ≤ k` — through the Step-0 verdict's two dissolutions (cross-part energy *absorbed* pointwise by `(a−b)² ≤ 2a² + 2b²` at the theorem's constant exactly 2, not eliminated; no centering, no kernel-orthogonality — the subspace engine's dimension count replaces the k = 2 constraint), the genuinely new k-general engine pieces `evals_le_of_card_eigvalOf_le` (the order-statistics↔counting bridge — the shelf had only the two endpoints) and `evals_le_of_linearIndependent` (the general-k subspace Rayleigh–Ritz engine, no PSD/kernel hypothesis — every future k-way or interlacing-shaped statement consumes it), and the per-part indicator energy identity `quadForm_laplacian_partIndicator`. QA +73 (`MultiwayCheeger_QA`, 2422 total): tight equalities at `k = n` on K₂ (`2 = 2·1`, both forms, against the raw anti-aligned pin) and the all-rational C₄ (`λ₄ = 2 = 2·1`, alternating-vector + trace-4 pin), the P₃ non-covering family (a certificate from a family that provably does not cover), the P₃ `k = 3` partition with `λ₃ = 2` pinned by trace arithmetic + a raw eigenvector, the `k = 1` edge, absorption pinned at *equality* on both fixtures, and the C₄ cyclic-pair overlap fence (every other hypothesis verified, disjointness refuted, conclusion refuted at `2 > 1`). Held at 4.5 per protocol: the higher-order family's easy half is a genuinely new theorem family (a raise-earning event), but the raise is bounded by the family's other half — the structural mirror of the 2-way family's pre-2026-08-23 state (easy delivered 2026-08-18, the 4.5 came only with both directions); the named 5.0 trigger is the multiway hard direction or the ρ_k packaging. **The ρ_k partition-minimum packaging was delivered 2026-08-26** (the delivery's own follow-on, pure hard crust, zero new axioms, QA 2422 → 2444): `cheeger_upper_bound_multiway_rhoK` — the classical `evals (L_sym) ⟨k−1⟩ ≤ 2 · multiwayExpansion A k` at the minimum over k-way partitions, through `IsMultiwayPartition`/`maxPartConductance`/`multiwayExpansion` with attainment over the finite partition space (`Set.Nonempty.csInf_mem`; the every-family form makes it a pure attainment task, no new engine) and the `k ≤ card V` existence supplier — the pre-recorded 5.0 trigger met, **axis raised 4.5 → 5.0**: the higher-order family's easy half now stands in its full classical statement form (every-family certificate AND packaged minimum), with the QA making attainment falsifiable (the star instance `ρ₂(C₄) = 1/2` exact — forced by the theorem joined to the independently pinned `λ₂ = 1` — with the minimum provably beating the diagonal partition's `1`, and the empty-set junk fence `ρ₃(K₂) = sInf ∅ = 0` proving partition-existence load-bearing). Beyond the scale: the multiway *hard* direction (λ_k from below) — genuinely multi-run, gated on a named consumer, recorded as the axis's one remaining named extension. **Alon–Boppana delivered 2026-08-26/27** (`GraphTheory.AlonBoppana`, Steps 0–5 pure hard crust): the field's canonical *lower* companion to Cheeger — `alonBoppana_nilli`, `secondEval (d•1 − A) ≤ d − (1 + 2k√(d−1))/(k+1)` under two far-apart full-tree-ball edges, with the classical error shape and the honest diameter bookkeeping — the axis's Have column now closes both directions of the expansion–spectrum relationship. **The expansion ceiling was delivered 2026-08-27** (`proposals/ramanujan-expansion-ceiling.md`, `AlonBoppana.lean`'s first theorem consumer: `ramanujan_expansion_ceiling` — `cheegerConstant A ≤ √(2 (1 − 2√(d−1)/d + 2√(d−1)/(d (k+1))))` under exactly the Alon–Boppana hypotheses, composing the capstone with the proved Cheeger hard direction through the new engine pieces `secondEval_smul_of_pos` (exact positive scaling, variational route) and `secondEval_congr` (the proof-irrelevance bridge across equal operator spellings) — the first shelf statement connecting the "how good can expansion be" upper-limit direction to the lower-bound machinery; obstruction scope only, no tightness claim; score **held at 5.0** per protocol: a two-composition joining two already-counted families plus one small engine piece, not a new theorem family). **Fiedler-subspace stability delivered 2026-08-28** (`proposals/fiedler-subspace-stability-davis-kahan.md` Step 1: `fiedlerSubspace_stability` in `GraphTheory.Fiedler` — the bottom-2 invariant spectral subspace of the combinatorial Laplacian (on a connected base, the Fiedler cluster `span {onesVec, fiedlerVector}`) moves by at most `‖laplacian E‖/δ` under a symmetric perturbation at separation `δ ≤ λ₃(L(A+E)) − λ₂(L A)` — the axis's first *stability* statement about the Fiedler object itself, as distinct from its static conductance-certificate content, and the proved `davis_kahan_sin_theta`'s first graph-theoretic consumer (the perturbation theorem's exact hypothesis shape — single-pair two-cluster separation, `k = 1` convention, tie-awareness — first exercised at graph spectra; QA +19 with the exact combinatorial P₃ pins `λ₂ = 1, λ₃ = 3`, the two-route zero-perturbation cross-check, and the K₃ tie-witness proving the hypothesis set empty at the `λ₂ = λ₃ = 3` tie); score **held at 5.0** per protocol: a consumer instantiation of an already-counted perturbation theorem at the axis's existing Fiedler object — load-bearing growth (a misstated hypothesis shape breaks exactly this wrapper and its spectrum pins), but not a new theorem family. **The Fiedler-line rotation was delivered 2026-08-28** (the same proposal's Step 2, its payoff slice: `fiedlerLine_stability` — the residual (Fiedler-mode) projector difference `‖(P₁' − P₀') − (P₁ − P₀)‖ ≤ ‖laplacian E‖/δ` on connected base and perturbed graphs — via the common-kernel identification `initialProjector_laplacian_zero_eq_of_connected`, the fixed-space uniqueness lemma, the projector eigenbasis expansion, and the connectivity-free fixed-space iff, making the kernel-characterization ecosystem load-bearing on a projector-equality statement for the first time, with the disconnected fence proving connectivity load-bearing; score **held at 5.0** per the same protocol: the identification layer is new engine machinery inside the already-counted projector/kernel families, load-bearing (an error in the kernel characterization, the projector definition, or the eigenbasis machinery breaks exactly this chain) but not a new theorem family). |
| 5 | Random walks and diffusion | 4.0 | Regular and irregular transition matrices with row-stochasticity **proved**; walk↔normalized similarity and both Laplacian bridges **proved**; the walk-matrix **eigenpair transfer proved** (2026-08-22, `proposals/mixing-time-bound.md` Step 1: eigenpairs conjugate through the similarity in both directions, `walkEvals` certifying each transferred entry a genuine eigenvalue of the non-symmetric walk matrix with explicit nonzero eigenvector witnesses, and `walk_eigvec_expansion` the diagonalizability interface — the axis's named walk-spectrum gap, closed as QA'd hard crust; re-scored 2.5 → 3.0); **reversibility (detailed balance) proved** (2026-08-22, `proposals/reversibility-and-heat-semigroup.md` Phase A: `deg i * P i j = deg j * P j i` with both forms — degree measure and stationary measure `π = deg/vol` — plus the symmetrizability packaging `D * P` symmetric and the regular uniform-measure corollary, zero new axioms, in `GraphTheory.Stationary`); **the ℓ²-mixing proxy defined with its evolution interface** (2026-08-22, `proposals/mixing-time-bound.md` Step 2, the new `GraphTheory.Mixing`: `stationaryVec`/`walkDistribution`/`walkDensity`/`chiSquareDistance` all proved-interface hard crust, `walkDensity_succ` consuming the detailed-balance interface — the density-coordinate evolution `h_{t+1} = P *ᵥ h_t` that the transferred eigenbasis diagonalizes); **the geometric decay engine proved** (2026-08-22, Step 3 component 1: the conjugated-power transfer `√D *ᵥ (Pᵗ *ᵥ g) = (1 − L_sym)ᵗ *ᵥ (√D *ᵥ g)`, eigencoordinate evolution, the Parseval-exact decay identity, and the ℓ²(π) contraction under value-based mode exclusion); and **the χ² mixing statement itself proved — the program's closing theorem** (2026-08-22, Step 3 component 2: `chiSquareDistance_le_of_connected` — `χ²(t, x) ≤ r ^ (2t) · ((π x)⁻¹ − 1)` on connected symmetric-nonnegative positive-degree networks under the rate hypothesis — assembled from the centered density evolution `h_t − 1 = Pᵗ *ᵥ (h₀ − 1)`, the connectivity kernel characterization of `L_sym` (the shelf's `laplacian_kernel_eq_span_onesVec` transferred through the proved congruence `√D L_sym √D = L`, composed with mass conservation), and the delivered contraction; zero new axioms; QA pins the bound **attained exactly** on K₃ at `t = 1, 2` (`1/2 ≤ (1/4)·2`, `1/8 ≤ (1/16)·2` — equalities), the λ* = 1 no-decay behavior on P₃ (rate derived basis-independently from two sum-of-squares certificates pinning the spectrum into `[0, 2]`), and refutes the connectivity-dropped form on a triangle⊕self-loop fixture where the rate hypothesis provably holds at `r = 1/2` yet `χ²(3) = 3/8 > 3/64` — the loop's `μ = 0` mode being exactly the hole connectivity plugs; re-scored 3.0 → 3.5). Heat semigroup **in delivery** (2026-08-23, `proposals/reversibility-and-heat-semigroup.md` Phase B Steps 0–3, the Active table's single High row — its gate resolved by the real external consumer `sgt-gaps.md`: the new `GraphTheory.Heat` defines the matrix-level `heatKernel A t = e^{-tL}` on `laplacian A` with symmetry under `A.IsSymm` through the pin's `Matrix.IsSymm.exp`, the hypothesis-free time-zero identity, the square-zero exponential collapse, **the semigroup law** `heatKernel A s * heatKernel A t = heatKernel A (s + t)` (Step 2, delivered 2026-08-23: hypothesis-free, via `Matrix.exp_add_of_commute` at the commuting negated scalar multiples, QA witnessing the law by two independent routes — hand multiplication of the fixture's closed forms vs. the theorem), and **mass conservation** `heatKernel A t *ᵥ onesVec = onesVec` (Step 3, delivered 2026-08-23: hypothesis-free, through the entrywise-built exponential-series convergence `expSeries_hasSum_exp` — the summability content constructed from scratch because the pin's normed `expSeries_summable'` cannot be applied at matrix type and the pin has no Pi-HasSum lemmas at all — and the kernel-vector engine `exp_mulVec_eq_of_mulVec_eq_zero`, whose per-kernel-vector generality the QA consumes for the per-component no-leakage witness on a disconnected fixture; the raw-vs-theorem two-route conservation check and the non-kernel-vector guard complete the witness set) — zero new axioms; held at 3.5 pending Step 4); and **the heat-kernel *statements* themselves — eigenmode decay and the DC limit — proved, closing the heat family** (Step 4, delivered 2026-08-23: the eigenmode engine `exp_mulVec_eq_smul_of_mulVec_eq_smul` (`M *ᵥ v = μ • v → exp ℝ M *ᵥ v = e^μ • v`, Step 3's convergence consumed at an eigenvector, the kernel engine its `μ = 0` case), `heatKernel_mulVec_eigvecOf` (every eigenbasis vector an eigenvector of `heatKernel A t` at every time, eigenvalue `e^{−t·λᵢ}`), the sorted-spectrum decay monotonicity with the PSD `≤ 1` dissipation bound, the eigenbasis expansion `heatKernel_mulVec_eq_sum` (the spectral-calculus identity in action form), and the payoff **DC limit** `heatKernel_mulVec_tendsto_atTop` (on connected graphs the heat flow of any vector converges to its mean `((∑ j, x j)/|V|) • onesVec` — assembled from PSD, `det L = 0` + `det_eq_prod_eigenvalues`, the kernel characterization, uniqueness-by-orthogonality, and finite-sum limit passage; zero new axioms; QA: two independent routes to the mode-decay statement and to the DC limit on K₂, the new rank-one-idempotent closed form `heatKernel K₂ t = 1 + ((e^{−2t}−1)/2) • L`, the K₂ spectrum pinned `[0,2]` from trace/determinant, and the engine⇄collapse cross-validation at a nonzero eigenvalue; re-scored 3.5 → 4.0 — the named trigger fired, and the continuous-time side of the axis is now a closed capability family: definition, identity, semigroup, conservation, mode decay, convergence). Absent: the ℓ² → total-variation conversion (the mixing proposal's own optional Step 4 — a separate proposal-scale decision) — the axis's only remaining absent category. |
| 6 | Combinatorial and electrical structure | 4.5 | The connectivity/kernel hinge is **proved** (2026-08-18, proposal `electrical-structure-crust.md` step 2 after the re-sequencing): for connected symmetric nonnegative weights, `ker (laplacian A) = span ℝ {onesVec}` (`laplacian_kernel_eq_span_onesVec`, built on `supportGraph` + `SimpleGraph.Walk` induction), with connected and disconnected QA witnesses. **Component structure is complete for weighted graphs** (2026-08-18, proposal step 3): the component-form kernel characterization `L *ᵥ f = 0 ↔ f` constant on each support-graph component (`laplacian_mulVec_eq_zero_iff_forall_reachable`), the kernel-equality bridge `ker (laplacian A) = ker ((supportGraph A).lapMatrix ℝ)`, kernel dimension = component count, and the component-indicator basis (Mathlib's `lapMatrix_ker_basis`/rank theorem inherited through the bridge; QA computes the count to `2` and the basis to `![1,1,0,0]`/`![0,0,1,1]` on the disconnected fixture). **The potential equation is completely characterized on connected graphs** (2026-08-18, proposal step 4): every zero-sum demand is solvable (`exists_laplacian_mulVec_eq_of_sum_eq_zero`, constructive eigenbasis witness `f = ∑_{λᵢ ≠ 0} (vᵢ ⬝ᵥ b/λᵢ)•vᵢ` — the load-bearing consumer of the proved eigenbasis algebra and the step-2 kernel theorem), the unit demand `e u − e v` is solvable (`exists_laplacian_mulVec_eq_single_sub_single`), and the reciprocity identity `w ⬝ᵥ (L *ᵥ f) = (L *ᵥ w) ⬝ᵥ f` (`laplacian_dotProduct_mulVec`) certifies in proved QA form that non-zero-sum demands are unsolvable and that zero-sum does not suffice without connectivity. **Effective resistance is a defined, well-determined quantity** (2026-08-18, proposal step 5, `GraphTheory.Electrical`; Mathlib surveyed: no resistance declaration, no pseudoinverse): `IsEffectiveResistance A u v r` by the potential equation, existence from step 4, uniqueness of `r` at reachability-pair strength, the total function `effectiveResistance` with proved agreement theorems and an honestly QA-witnessed junk fallback, the energy identity at solution and function level (`quadForm L f = f u − f v`; `R = energy`), nonnegativity from PSD, hypothesis-free relation symmetry, and `R u u = 0` unconditional; QA computes `R = 1` on the unit edge, `R = 2` on the 3-vertex path (series edges add), and cross-checks the energy identity against an independently computed energy. **The one-sided Dirichlet bound is proved** (2026-08-18, proposal step 6, program complete): `(f u − f v)² / quadForm L f ≤ R u v` for every test potential of positive energy (`effectiveResistance_ge_sq_div_quadForm`), via the semidefinite Cauchy–Schwarz `laplacian_cauchy_schwarz` (no connectivity hypothesis; the pin's only C–S is the definite inner-product one — polarization route recorded); QA attains equality at both harmonic potentials (`1/1 = 1`, `4/2 = 2`), shows strictness at a non-harmonic potential, refutes the reverse inequality numerically, and witnesses the energy guard. **The potential API is now a routing object** (2026-08-19, proposal `electrical-flow-routing.md` steps 0–1, `GraphTheory.ElectricalFlow`; Mathlib re-surveyed: no flow/circulation/divergence API anywhere in the pin): `electricalCurrent` (Ohm's law on ordered pairs, conductance convention), `flowDivergence`, the predicates `IsFlowOn` (antisymmetry + zero-conductance support — the support conjunct QA-witnessed load-bearing by an edgeless-network phantom that satisfies every other unit-flow condition) and `IsUnitFlow`, and the Kirchhoff bridge `flowDivergence_electricalCurrent` + headline `isUnitFlow_electricalCurrent`: every unit-demand potential induces a valid unit flow (load-bearing on the center's exact Laplacian sign convention through `laplacian_mulVec_apply`); QA computes the `K₂` and 3-path currents and divergences from the definitions with internal-vertex conservation `0`, and refutes current antisymmetry on an asymmetric network (`2 ≠ 1`). **Flow energy agrees with the Dirichlet energy and the resistance it routes** (2026-08-19, proposal step 2): `flowEnergy` with the explicit zero branch and the mandatory `1/2` ordered-pair factor; `flowEnergy_electricalCurrent` (symmetry-only — the entrywise Ohm's-law algebra needs no nonnegativity, QA-witnessed both ways), `flowEnergy_nonneg` (nonnegativity load-bearing, QA exhibits energy `-1` on a symmetric negative-weight network), and `flowEnergy_electricalCurrent_eq_effectiveResistance`; QA pins energies `1`/`2` from the raw definitions against independently computed Dirichlet energies and pinned resistances, guards the `1/2` factor numerically (raw ordered-pair sum `2 ≠ 1`), pins the step-1 phantom's zero energy, and exhibits the zero-energy competitor — an antisymmetric unit-divergence flow through zero-conductance pairs with energy `0 < 1` = the real resistance, excluded by the support conjunct alone. **Thomson's principle is proved** (2026-08-19, proposal step 3): `effectiveResistance A u v ≤ flowEnergy A θ` for every valid unit flow (`effectiveResistance_le_flowEnergy`) — the electrical current is the energy minimizer — via the divergence-free superposition lemma `flowEnergy_add_of_flowDivergence_eq_zero` (discrete integration by parts; stated with **no hypotheses on `A`**, only the perturbation's flow properties), `isFlowOn_sub`/`flowDivergence_sub` linearity, and `flowEnergy_nonneg`; QA witnesses attainment at the split current on the triangle (`K₃`, `R = 2/3` = the current's energy, computed from the raw definitions), a **strict competitor** (the detour flow around the two-edge path: valid `IsUnitFlow`, energy `2`, `2/3 < 2`), and the superposition decomposition `2 = 2/3 + 4/3` with all three values computed independently. **Rayleigh monotonicity in conductance form is proved** (2026-08-19, proposal step 4): entrywise `A ≤ B` on connected symmetric nonnegative networks gives `effectiveResistance B u v ≤ effectiveResistance A u v` (`effectiveResistance_le_of_le`) — the first *network-comparison* theorem on the axis (it relates two graphs, not two objects of one graph) and the ICP-facing fact that adding capacity cannot worsen the certified energy cost of electrical routing — via the two new reusable interfaces `isFlowOn_of_le` (flow-space growth: a flow supported on `A` is a flow on every `B ≥ A ≥ 0`, support load-bearing) and `flowEnergy_le_of_le` (raising conductances lowers dissipated energy, termwise; support load-bearing again on the `A i j = 0 < B i j` branch), composed with Thomson on `B` at the transferred `A`-current and the step-2 energy identity; QA certifies the proposal's capacity-increase fixture `1 → 1/2` strict with the **orientation guard** (the reverse inequality `1 ≤ 1/2` refuted numerically — weights are conductances), the competitor transfer instantiated on computed objects, and a partial increase on the triangle (`2/3 → 2/5`, new value pinned by an independent potential). **The program is complete (2026-08-19, step 5)**: `increaseConductance` raises one undirected pair's conductance (both ordered entries together), and the one-hypothesis headline `effectiveResistance_le_increaseConductance` packages the monotonicity as the ICP-facing capacity-reinforcement theorem — only the original network's connectivity is hypothesized, the reinforced network's derived by `supportGraph_connected_of_le` (support graphs grow along entrywise domination — `supportGraph_le_of_le`, no nonnegativity needed — and Mathlib's `SimpleGraph.Connected.mono` lifts connectedness); QA is the release example: the Mathlib `Fin 3` path graph through `toWAdj`, the reinforcement computed to the concrete doubled-path matrix, the reinforced resistance `3/2` pinned by an independent potential witness, and the decrease certified strict `3/2 < 2`. Re-scored 3.5 → 4.0 per the step-3 recorded reservation (the axis rises when Thomson/Rayleigh land; both have now landed); held at 4.0 at step 5 (packaging, not new mathematics). **Foster's theorem is proved** (2026-08-19, proposal `spectral-graph-sparsification.md` Phase A, `GraphTheory.Foster`; zero new axioms — `#print axioms` reads only the three standard axioms): `(∑ i, ∑ j, A i j * R i j) / 2 = card V − 1` on every connected symmetric-nonnegative network, via the proposal's pseudoinverse-free eigenbasis route (the per-pair spectral sum `effectiveResistance_eq_sum_eigbasis` = energy identity + `quadForm_eigvalOf` + self-adjointness; the double-sum swap with per-eigenvector Dirichlet evaluation `∑_{i,j} A i j (v_k i − v_k j)² = 2 λ_k`; and the one-kernel-index count `card_filter_eigvalOf_laplacian_eq_zero` against `laplacian_kernel_eq_span_onesVec`) — the first **global network identity** on the axis, tying the electrical quantities to the combinatorial spanning-tree count; the sparsification-facing leverage scores are defined with their probability normalization proved (`sum_leverageScore_eq_two`; QA pins the `K₃` edge leverage `1/3` and the `K₄` edge `1/6`). Re-scored 4.0 → 4.5 with this milestone (a new theorem family — global identities — not packaging; QA witnesses the ordered-pair double-counting factor on both cliques, `4 ≠ 2` on `K₃` and `6 ≠ 3` on `K₄`, so a statement shape dropping the `/ 2` would be refuted). **The resistance metric is proved** (2026-08-24, proposal `resistance-metric.md`, backlog item 7's two named non-gated residuals, `GraphTheory.Electrical`; zero new axioms): the **maximum principle** for unit-demand potentials (`min (f u) (f v) ≤ f x ≤ max (f u) (f v)`, by diffusion-form propagation — `laplacian_mulVec_apply` + nonneg-termwise-zero + walk induction, the kernel-characterization argument run at an inequality), the definiteness residual `effectiveResistance A u v = 0 ↔ u = v` (positivity off-diagonal via the one-sided Dirichlet bound at the indicator `e u`, whose energy `∑_{j≠u} A u j` is positive by connectivity), and the **triangle inequality** `R u w ≤ R u v + R v w` (the polarization cross term `f v − f w ≤ 0` of the `f + g` assembly — the Step-0 survey records that the eigenbasis route yields only the *root*-triangle, so the maximum principle is the mathematical crux, not a convenience); with the earlier nonnegativity/symmetry/self-distance laws this makes `effectiveResistance` a genuine metric on every connected network (the classical resistance distance). Held at 4.5 (the metric's named gaps close, but the axis's absent list still holds Matrix–Tree and Kirchhoff; QA fences `hnonneg` across all three new theorems on one signed fixture). Absent: spanning-tree enumeration (Matrix–Tree), and the Kirchhoff loop/cut-space theorems. |
| 7 | Perturbation, randomness, algorithms | 4.5 | Weyl **proved** (retired 2026-08-20); **Davis–Kahan proved** (retired from axiom 2026-08-21, `proposals/discharge-perturbation-axioms.md` Step 1 complete — explicit axioms 11 → 10: the Duhamel/exponential-integral route, components `Analysis.OperatorTheory.Perturbation.{ProjectionGap,Duhamel}` — the equal-rank projector identity `‖P − Q‖ = ‖(I−Q)P‖` and the Duhamel bound `‖(I−Q)P‖ ≤ ‖E‖/(b−a)` from the vector-level heat semigroup, scalar pairing FTC, and cluster-filtered Parseval damping, with the eigenvalue-tie cases collapsed through the proved Weyl additive bound; `davis_kahan_sin_theta` at its unchanged statement now reads only `propext, Classical.choice, Quot.sound`; the derived chain's `davisKahanTwoPoint` **fully hard crust** and `eventStreamProjectorDrift` conditional on `matrix_azuma_hoeffding` alone — the axis's first calculus-based (FTC/integral) proof technique, re-scored 3.5 → 4.0); scalar + matrix concentration **admitted** with the **derived** event-stream tail. **The shelf's first concrete probability space delivered (2026-08-27, sparsification Step 1 Slice 1, `Probability/BernoulliProduct`, zero new axioms):** the independent-Bernoulli product measure on `ι → Bool` with pairwise `IndepFun` of coordinates and the matrix-codomain transfer layer — the exact clause machinery (`h_meas`/`h_indep`/`h_mean`) every concrete instantiation of the admitted concentration axioms needs and that neither the shelf nor the pinned Mathlib supplied. **The named raise trigger is met twice over (2026-08-27): the sparsification Step-1 assembly gave `matrix_bernstein` its first real theorem consumer (`Derived.SparsificationTail`, conditional on that axiom alone), and the empirical-stationary-distribution Steps 0+1 gave `hoeffding_empirical` its first (`Derived.EmpiricalStationary`'s `hoeffding_empirical_iid` + `empiricalWalkDistribution_tail` — the fixed-time empirical visit-frequency concentration `P{|p̂_i(n) − ν_{t₀} i| ≥ t} ≤ 2 exp(−2nt²)` on the new V-valued i.i.d. product space `Probability.IIDProduct`, the BernoulliProduct construction generalized to an arbitrary normalized factor, with the walk law certified a probability vector by the new proved `walkDistribution_nonneg`; no symmetry/connectivity/mixing hypothesis). Score 4.0 → 4.5: two admitted concentration axioms now have load-bearing theorem consumers whose every hypothesis clause is discharged by proof — the axis's named absent category (concrete probability-theoretic sampling + concentration of estimators) gains real occupants.** **Third consumer delivered 2026-08-28** (`proposals/matrix-hoeffding-spectral-gap-estimation.md`): `matrix_hoeffding` — the last of the concentration family's dimension-prefactored trio with zero theorem consumers — now has its own (`Derived.EdgePerturbationTail`'s `edgePerturbation_norm_tail`/`edgePerturbation_quadForm_tail` at a sign-free centered Bernoulli edge design, conditional on that axiom alone), and the delivery's Step-0 defect check **repaired all three matrix axioms in place** (each was inconsistent at the degenerate dimension `card V = 0`, `t = 0`; `[Nonempty V]` guard added, hypothesis-form refutation records in `Matrix_QA.lean`, consumers threaded). Score held at 4.5 per protocol: a third consumer instantiation within the already-counted category plus an axiom-consistency repair — load-bearing (an unrepaired axiom made every conditional theorem vacuous), but not a new capability family. **Second axiom-consistency repair of the family 2026-08-29** (Errata §6, `proposals/pairwise-independence-concentration-repair.md`): all six independence-carrying concentration axioms (`hoeffding_inequality`, `hoeffding_empirical`, `bernstein_inequality`, `bernstein_bounded_variance`, `matrix_hoeffding`, `matrix_bernstein`) hypothesized only *pairwise* `IndepFun` — insufficient for Hoeffding/Chernoff (the fifteen Walsh characters of 4 fair coins are pairwise independent with sum `15` on a `1/16`-mass atom; six hypothesis-form refutations in `PairwiseIndependence_QA.lean`) — and were repaired in place to `iIndepFun` with the mutual-independence engines added to both sampling spaces (`BernoulliProduct`, `IIDProduct`) and every consumer threaded at unchanged public statements. Score held at 4.5 per protocol: same class as the degenerate-dimension repair — load-bearing correctness (an unrepaired hypothesis shape made every conditional tail unbacked), not a new capability family. **Third axiom-consistency repair of the family 2026-08-29** (Errata §7, `proposals/audit-matrix-azuma-mds-measurability-hazard.md` — the standing §12 junk-integral residual's own deferred Step 0): the `MatrixMDS` encoding of Tropp's adaptedness carried no ambient strong-measurability clause and its `adapted` field was content-free (`mdsFiltration` is the comap σ-algebra the `X j` generate themselves), so the `cond_mean_zero` set-integrals were junk zeros and `matrix_azuma_hoeffding` was satisfiable by a bounded non-measurable drift — refuted in hypothesis form at a 33-point caterpillar fixture with every old field *proved*; repaired in place (the vacuous field replaced by `measurable : ∀ k, StronglyMeasurable (X k)`, both Derived consumers threaded to ambient `h_meas`, the exclusion fence proving the repaired field rejects the refuting drift). Score held at 4.5 per protocol: same class again — the trust boundary under the retained persistence tail chain made honest, not a new capability family. Earlier: the sampling space itself had been held at 4.0 per protocol (the gate on the sparsifier theorem and the empirical consumer, not yet a new theorem family). **A verified numerical/spectral algorithm driver now exists (2026-08-19, decidable-certificates Step 3, `GraphTheory.SpectralCertificates`):** proof-carrying λ₂ upper-bound certificates — a ℚ specification checker with a proved soundness theorem consuming `lambda2_variational`, a kernel-`decide`able integer cross-multiplied twin (fractional variant included), and proved cross-multiplication bridges making the specification reachable from kernel-verifiable arithmetic — with C₄ QA demonstrating the full chain (`decide`d integer data → verified `lambda2 ≤ 2`, `≤ 5/2`). Re-scored 3.0 → 3.5 with this milestone (the axis's named absent category "numerical/spectral algorithm drivers" gains its first verified occupant — a new capability family, not packaging; random-graph models remain absent). Step 4 (2026-08-19, QA-only) completed the demonstration: the certificate chain kernel-decided at the second required size (`C₆`: `lambda2 ≤ 1` end-to-end from `decide`d integer data) and, on `C₄`, witnessed **exactly tight** — the checker accepts precisely at the true `lambda2 = 2` (pinned by a Poincaré inequality) and rejects every integer bound below it. Score held at 3.5 (verification strengthening of the existing occupant, no new capability family). |
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
**the Hoffman-type independence bound** (`hoffman_independence_bound`,
2026-08-25 — the mixing lemma's first theorem consumer, the classical
ratio bound at the lemma's own `μ` hypothesis, with both classical
tight cases attained in QA; held at 4.5 per protocol as a one-shot
corollary within the already-counted discrepancy family — but the
previously-idle hypothesis shape of `expander_mixing_lemma` now
carries weight, the strategy's load-bearing-growth finding); the
swept-level-set certified cut (`fiedler_sweep_cut`) was delivered
2026-08-24, the irregular *easy* direction 2026-08-25
(`cheeger_upper_bound_normalized`), the irregular *hard* direction and
the Fiedler instantiations 2026-08-26, and **the multiway (higher-order
Cheeger) easy direction 2026-08-26** (`cheeger_upper_bound_multiway`,
the every-family form with the k-general subspace engine); the multiway
*hard* direction and the ρ_k packaging remain its nearest completions.

## Assurance radar

| Axis | Score | Evidence |
|------|------:|----------|
| Proved depth | 3.5 | Interfaces and algebra are hard crust (projector algebra, cut duality, all Laplacian/normalized/walk bridges, gap stability, electrical structure through the one-sided Dirichlet bound and the flow/Kirchhoff-conservation interface (`isUnitFlow_electricalCurrent`, 2026-08-19) with its flow-energy agreement (`flowEnergy_electricalCurrent` and the unit-demand identity `flowEnergy_electricalCurrent_eq_effectiveResistance`, 2026-08-19) **and Thomson's principle** (`effectiveResistance_le_flowEnergy` over every valid unit flow via the divergence-free superposition lemma `flowEnergy_add_of_flowDivergence_eq_zero` — hypothesis-free on `A` — plus flow-space linearity; QA: attainment, strict competitor, decomposition, 2026-08-19) **and Rayleigh monotonicity** (`effectiveResistance_le_of_le`, 2026-08-19 — the conductance-form network comparison `A ≤ B ⇒ R_B ≤ R_A`, via flow-space growth `isFlowOn_of_le` and the energy comparison `flowEnergy_le_of_le`, composed with Thomson on `B`; QA: capacity increase `1 → 1/2` certified strict with the orientation guard, partial increase `2/3 → 2/5` on the triangle), plus the one-hypothesis capacity-reinforcement packaging `effectiveResistance_le_increaseConductance` with the `supportGraph_connected_of_le` connectivity adapter (2026-08-19, completing the flow program), the Fiedler-vector/sign-partition interface of Phase A incl. the algebraic-connectivity certificate `lambda2_pos_of_connected`, 2026-08-18, and the Woodbury matrix-update identity proved from Mathlib, 2026-08-18; **the Expander Mixing Lemma and its Rayleigh-sandwich bridge are hard crust** (2026-08-19, `expander_mixing_lemma` with the operator bound on `1⊥`, the sharp bilinear form, the generic top Rayleigh domination `quadForm_le_evals_last`, and the `d`-regular identity `quadForm_add_quadForm_laplacian`)); **Weyl's inequality is hard crust** (retired 2026-08-20, `proposals/discharge-perturbation-axioms.md`: `weyl_inequality` proved at its unchanged axiom statement from the additive window via the min–max engine's two witness forms plus both Rayleigh domination bounds, composed with the operator-norm bridge — with the public additive interfaces `weyl_additive_upper`/`weyl_additive_lower`); the operator-norm bridge and the resolvent calculus are hard crust too (2026-08-19, `Analysis.OperatorTheory.Resolvent`: `l2OpNorm_eq_max_abs_evals` with both directions, shifted-PSD invertibility `isUnit_det_add_smul_one_of_quadForm_nonneg`, `resolvent_identity_sub`, and — Step 2, same day — the resolvent norm bound `l2OpNorm_inv_add_smul_one_le_inv_of_quadForm_nonneg` (general `t`, no symmetry, energy route) and the Lipschitz bound `l2OpNorm_resolvent_sub_le_of_quadForm_nonneg`; and — Step 3, 2026-08-20, completing the program — the resolvent-map injectivity `resolvent_map_injective_of_quadForm_nonneg` with its core form `eq_of_inv_add_one_eq_inv_add_one` and the certificate iff `inv_add_one_eq_inv_add_one_iff_of_quadForm_nonneg`); the *variational* engine is proved in full generality (`lambda2_variational` + its general-operator form `secondEval_variational`, 2026-08-18, and the general Courant–Fischer min–max at every index — `evals_min_max` with both witness directions — later the same day, no positivity or graph hypotheses), the *Cheeger easy direction* is proved on top of it (`cheeger_upper_bound`, retired the same day), and **Cauchy interlacing is proved on top of the min–max engine** (`eigen_interlacing_principal_submatrix`, retired 2026-08-18 — the engine's first named consumer, consuming both witness directions through the extend-by-zero padding bridge), so the remaining admitted engines are the Cheeger hard direction and concentration — each with documented statement differences (Weyl left this list 2026-08-20; **Davis–Kahan left it 2026-08-21** — `davis_kahan_sin_theta` proved by the Duhamel/exponential-integral route, the equal-rank projector identity plus the heat-semigroup FTC assembly, with the equal-rank identity itself a new hard-crust gap-metric theorem). |
| Axiom minimization | 4.5 | 10 explicit axioms, all cited and indexed (the row-head count had drifted stale at 9 across the 2026-08-24 primitive-power admission — repaired with this sync, the same drift class the 2026-08-22 PF sync fixed; the count reached 10 on 2026-08-20 with the Weyl retirement — `weyl_inequality` proved at its unchanged statement from the Courant–Fischer engine plus the operator-norm bridge, `proposals/discharge-perturbation-axioms.md`; the perturbation bridge's admitted set is now Davis–Kahan alone, and the derived projector-drift chain is conditional on two axioms instead of three); `spectral_gap_stability`, `hoeffding_iid`, `bernstein_iid` converted from admitted to proved; **`lambda2_variational` retired from axiom to proved theorem (2026-08-18) — the first axiom removed by proof rather than deprecation — and `cheeger_upper_bound` retired the same way one milestone later** (the Cheeger easy direction, proved from the generalized `secondEval_variational`; both false pre-repair shapes refuted in QA); **`woodbury_identity` retired 2026-08-18 as an emergency correctness repair — the first retirement motivated by the axiom being verified *false* rather than merely unproved, proved from Mathlib's `Matrix.invOf_add_mul_mul` at zero local proof cost**; **`sherman_morrison` retired 2026-08-18 as the `k = Fin 1` specialization of the proved Woodbury theorem — a pure proof task at unchanged name/hypotheses (the statement had been verified correct against the repaired Woodbury shape first), completing the matrix-update bridge at zero axiom cost**; **`eigen_interlacing_principal_submatrix` retired 2026-08-18 — Cauchy interlacing proved from the locally proved Courant–Fischer engine, the engine's first named consumer and the first SGT-center retirement (all prior retirees were variational, update-identity, or derived statements)**; `spectral_persistence` deprecated 2026-08-17 with a migration note and removed 2026-08-20 (zero non-QA consumers throughout; the derived two-endpoint chain covers the motivating use). Net trend 26 → 19 → 18 → 17 → 16 → 15 → 14 → 13 → 12 → 11 → 10 → 9 → 10 → 9 → 10 (the 2026-08-24 up-step is the `primitive_power_tendsto` admission, Horn & Johnson §8.5 at the row-stochastic specialization — the directed axis' first *convergence* axiom, the standing no-dominance scope of `perron_frobenius` being precisely why it was needed, fenced by the 2-cycle periodicity refutation; the 2026-08-25 Hoffman delivery touches no axiom — pure hard crust, the count held);the 2026-08-21 step is `davis_kahan_sin_theta`, proved by the Duhamel route of `proposals/discharge-perturbation-axioms.md`; the 2026-08-22 down-step is `subgaussian_tail_bound`, the **second false-axiom repair retirement** after Woodbury — the mandated Step 0 spike proved the old `subgaussianNorm ≤ K`-shaped axiom materially false through two independent junk mechanisms (`Real.sInf_empty` vacuity; `integral_undef` junk-zero MGF integrals making the defining set full for heavy tails), refuted in QA with the old hypotheses satisfied, and the theorem restated at the same name/conclusion with the moment integrable — the falseness category is empty again among checked statements, and the first measure-theoretic retirement landed; the 2026-08-22 up-step is the Perron–Frobenius admission (the directed axis' second spectral toolkit — a deliberate admission, not drift); the 2026-08-23 down-step is `cheeger_lower_bound`, the Cheeger hard direction proved at the unchanged statement by the median-split route of `proposals/discharge-perturbation-axioms.md` — the discharge program complete: Weyl, Davis–Kahan, and both Cheeger directions all proved; the count also passed through 11 on 2026-08-20 with the operator-directed `spectral_persistence` removal, an editorial deletion rather than a proof retirement). Score held at 4.5 (a retirement within the already-cited-and-QA'd admitted set; the falseness category stays empty). Score 4.5 (re-scored 4.0 → 4.5 at the Woodbury repair: the false-axiom category is now empty among statements whose truth has been checked, and the false Woodbury shape was removed rather than merely replaced; the Sherman–Morrison and interlacing retirements continue the trend without crossing a new threshold — the Core update-identity bridge and the interlacing window are now axiom-free; the Weyl retirement likewise continues the trend — the first *perturbation-bridge* retirement, but within the same cited-and-QA'd admitted set rather than a new threshold; the subgaussian repair holds the score — the second false-axiom repair confirms the falsification discipline works, but the discovered falseness itself is not minimization progress to score). |
| Mathlib interoperability | 4.5 | Native `Matrix`, `IsSymm`, `Matrix.L2OpNorm`, `Matrix.PosSemidef`, `ProbabilityTheory.IndepFun`, `OrthonormalBasis`; the matrix-first representation is bridged in **both** directions and mutually consistently — `supportGraph : WAdj → SimpleGraph` (2026-08-18, consumed by the proved kernel characterization) and `SimpleGraph.toWAdj` (2026-08-18, `GraphTheory.SimpleGraphAdapter`), tied by the proved roundtrip `supportGraph (toWAdj G) = G`; through the agreement `laplacian G.toWAdj = G.lapMatrix ℝ`, Mathlib's unweighted kernel/reachable and component-count results are transferred onto the Scaffold side (`laplacian_toWAdj_mulVec_eq_zero_iff_reachable`, `finrank_ker_laplacian_toWAdj`), and every center theorem becomes callable on Mathlib graphs. Remaining documented deviation: `MatrixMDS` pending a Mathlib filtration API. |
| QA | 4.0 | 3118 declarations across 67 modules (count synced 2026-08-29 with the MatrixMDS ambient-measurability repair — no new file, +19: `Matrix_QA.lean`'s repair record proving the pre-repair `matrix_azuma_hoeffding` hypothesis shape materially false (the 33-point caterpillar fixture: every old `MatrixMDS` field *proved* at the drift — adaptedness content-free by the comap structure (`measurable_mdsFiltration_QA`), the conditional means vanishing through the explicitly exhibited junk-integral mechanism, the bound at `R = 1` — while the tail event carries mass `> 1/2` against the bound `≤ 1/2` from `exp 3 ≥ 4`; plus `azDrift_not_stronglyMeasurable_QA`, the exclusion fence proving the repaired `measurable` field rejects the same drift, so the repair does real exclusion work); the refutation/fence/vacuity/fixture family at exactly the standard three (`wip/azumajunk_axcheck.lean`/`wip/azumajunk_axcheck2.lean`), the axiom-instantiating consumers honestly carrying `matrix_azuma_hoeffding` alone; the score held at 4.0 per protocol — a falsification record for a hypothesis-shape repair, not a new theorem family). Earlier: 3099 declarations across 67 modules (count synced 2026-08-29 with the pairwise-independence repair — one new file, +91: `Concentration/PairwiseIndependence_QA.lean` at 89 declarations — the Walsh-character refutation family proving each of the six concentration axioms' *pre-repair* pairwise-`IndepFun` hypothesis shapes materially false (the fifteen nontrivial characters of the fair coin on `Fin 4 → Bool` pairwise independent by the xor-translation group action, centered by the flip involution, sum `15` on the all-false atom of mass `1/16` against bounds proved `< 1/16` from `e^{1/2} ≥ 3/2` and `e ≥ 9/4`), every other hypothesis clause *proved* at each fixture — the scalar pair directly, the matrix pair through the rank-one idempotent lift `‖E‖ = 1`, and the `[0,1]`-valued affine images for `hoeffding_empirical` — all six at exactly the standard three axioms (`wip/pairwise2_axcheck.lean`), plus the two `iIndepFun_const_*_QA` re-instantiation lemmas; the score held at 4.0 per protocol — falsification records for a hypothesis-shape repair, not a new theorem family). Earlier: 3008 declarations across 66 modules (count synced 2026-08-29 with the dissolution-completion delivery — no new file, +5: `EdgePerturbation_QA.lean`'s AdmissibilityDissolution completion subsection, the QA of the window family's floor and swept-cut members made unconditional — the all-false disconnectedness witness (the kernel-constancy contrapositive at the zero adjacency, the `![1, 0]` component indicator non-constant), the **strict-containment witness** (the all-false outcome provably *in* the unconditional sweep bad event while provably *not* admissible — the dissolution genuinely enlarged the measured event, the degree-tail term its honest price; hard crust), the good-outcome conjunction at the dissolution's window (`conductance² ≤ 4` inside the ceiling `81/4` — the bad event not all of `Ω`), and the two closed-form instances (`4 exp(−1/4096) + 4 exp(−1/16)` each, the sweep one's floor hypothesis genuinely holding at `3/16`); three of the five at the standard three (`wip/dissolve2_axcheck.lean`), the two theorem-instantiating pins honestly carrying both `matrix_hoeffding` and `hoeffding_inequality`; the score held at 4.0 per protocol — the completion of the already-counted dissolution within the already-counted window family, not a new theorem family). Earlier: 3003 declarations across 66 modules (count synced 2026-08-29 with the admissibility-dissolution delivery — no new file, +16: `EdgePerturbation_QA.lean`'s AdmissibilityDissolution section, the QA of the window family's first unconditional measured event — the pair design condition pinned at both uniform designs (`½ + ½ = 1` the boundary, `1/10 + 1/10` with slack), the boundary entry pin (the all-false `p ≡ ½` off-diagonal entry exactly `0` — the engine's inequality tight at the boundary), the **dropped-pair-condition fence** (at `p ≡ 9/10` the same entry exactly `−4/5` — nonnegativity genuinely failing at a design legal in every other respect), the transfer's positive witness at `p ≡ 1/10` (deviations `|−1/5| < 1/2`, base degrees in the shrunk window `[1, 2]`, derived degree `4/5` by the design's own identity), the strictness-boundary coherence (the `p ≡ ½` all-false outcome in the degree event and provably not admissible), and the closed-form instance `4 exp(−1/4096) + 4 exp(−1/16)`; 15 of the 16 at the standard three (`wip/dissolve_axcheck.lean`), the closed-form pin honestly carrying both `matrix_hoeffding` and `hoeffding_inequality` — the family's first deliberate two-axiom member; the score held at 4.0 per protocol — the first composition of the already-counted degree-tail and window families, dissolving a recorded honesty note rather than adding a theorem family). Earlier: 2987 declarations across 66 modules (count synced 2026-08-29 with the Bernstein-twin delivery — no new file, +10: `EdgePerturbation_QA.lean`'s bernsteinTwin section, the QA of `bernstein_inequality`'s and `bernstein_bounded_variance`'s first theorem consumers — the true variance statistic pinned exactly (`σ²₀ = ½` on `K₂` at the fair coin) with the Poisson-trial shape (`∑ w² p = 1`) **refuted** (the centered-vs-uncentered distinction load-bearing in the Bernstein denominator), the fourfold variance reduction as an equation (`σ²₀ = S₀/4`, sharp at the fair coin), the engine integral at an incident pair (`¼`), the **strict variance-adaptivity improvement proved** (`2 exp(−3/5) < 2 exp(−1/4)`, the cross-axiom coherence check showing the Bernstein tail genuinely stronger than the delivered Hoeffding tail at the same fixture and threshold — hard crust), the budget relaxation pinned honest (`≤`), and the two closed-form conditional instances; eight of the ten at the standard three (`wip/berntwin_axcheck.lean`), the two theorem-instantiating pins honestly carrying their own axiom; the score held at 4.0 per protocol — axiom-consumer instantiations within the already-counted concentration category, the same protocol as the degree-concentration note). Earlier: 2977 declarations across 66 modules (count synced 2026-08-29 with the degree-concentration delivery — no new file, +14: `EdgePerturbation_QA.lean`'s degreeTail section, the QA of `hoeffding_inequality`'s first theorem consumer — the variance statistic pinned exactly (`S₀ = 2` on `K₂`) with the single-counted `1` refuted (the ordered-pair double count load-bearing in the exponent), the deviation identity at the all-true outcome by **two independent routes** (raw weight-space `2 • K₂` vs the design's `1 + ½ + ½`) and at the all-false outcome joined to the corner audit, the closed-form instances (`2 exp(−1/4)`, union `4 exp(−1/4)` with the collapse demonstrated numerically at equal statistics), and the **exact event measure `1/2`** computed through the design's own independence machinery (`indepFun_coord` + `toMeasure_cyl`), independently of the tail theorem, putting the bound's fixture-scale slack on the record beside it; 12 of the 14 at the standard three (`wip/degconc_axcheck.lean`), the two theorem-instantiating pins honestly carrying `hoeffding_inequality`; the score held at 4.0 per protocol — an axiom-consumer instantiation within the already-counted concentration category, the same protocol as the third-consumer note, not a new theorem family). Earlier: synced 2963 declarations across 66 modules with the degenerate-degree corner-audit delivery — no new file, +12: `EdgePerturbation_QA.lean`'s cornerAudit section settling the window family's parked spike-level finding in proved form — at nonpositive degrees (`√0 = 0` with `0⁻¹ = 0`; `Real.sqrt` of a negative — the hitherto-unrecorded *negative-degree* corner, the `p ≠ ½` outcomes route) the normalized Laplacian degenerates to the identity whose sorted spectrum is `1` (`evals_one`, the new `Spectral` pin), not the zero matrix's `0` — the easy misprediction exhibited as the proved spectral contrast `λ₂(L) = 0 ∧ λ₂(L_sym) = 1` at the same all-false outcome, the honesty note's floor-condition mechanism proved as a fixture instance, and the vanishing iff exercised on both sides; all 15 audited declarations at the standard three (`wip/degcorner_axcheck.lean`); the score held at 4.0 per protocol — a corner audit pinning the already-counted definitions' junk behavior, not a new theorem family; the run's two adversarial attacks on the shelf's dropped-guard honesty notes both *survived*, with the structural reasons recorded in the proposal). Earlier: synced 2951 declarations across 66 modules with the C₄ guard-fence delivery — no new file, +29: `EdgePerturbation_QA.lean`'s guard-fence section with the C₄ fixture at the hypothesis-loosened window `[1, 2]`, the perfect-matching outcome proved admissible (degrees all `2`) and disconnected (the component indicator a non-constant Laplacian-kernel vector, connectivity⇒kernel-constants contrapositive), its atom mass exactly `2⁻¹⁶`, the variance statistic bounded `≤ 64` (triangle + submultiplicativity + `l2OpNorm_rankOne_le`) and pinned positive (the `(0,0)` entry `= 8` by sixteen-way literal enumeration), and the headline `epC4_sweepWindow_unguarded_refuted_QA` — the un-guarded conclusion of `edgePerturbation_fiedler_sweep_cut_tail` refuted in proved arithmetic at `t = 9000` (`8/(1 + 9000²/128) < 1/65536`), correcting the previous honesty note whose obstruction had anchored on the t-monotone eigenvalue-floor route and on fixtures without admissible-disconnected outcomes; all eight audited declarations at the standard three (a refutation cannot consume the axiom-conditional theorem); the score held at 4.0 per protocol — a negative-witness fence on the already-counted window family, not a new theorem family). Earlier: synced 2922 declarations across 66 modules with the swept-Fiedler-cut consumer delivery — no new file, +4: `EdgePerturbation_QA.lean`'s sweepWindow section with the all-true K₂ good-outcome witness (connected by a raw two-vertex walk, the swept cut from the deterministic `fiedler_sweep_cut_normalized` at the pinned `λ₂(L_sym) = 2` giving `conductance² ≤ 4`, numerically inside the window bound `16.25` — a wrong constant on the ceiling, the sweep constant, or the pinned spectrum breaks the join) and the closed-form K₂/P₃ tail instances at `t = 1/16` (`4 exp(−1/4096)`, `6 exp(−1/6144)`, the floor hypothesis genuinely holding at `1/16 < 1/8`); two of the four at the standard three (`wip/sweepwin_axcheck.lean`), the two theorem-instantiating pins honestly carrying `matrix_hoeffding`; the score held at 4.0 per protocol — a composition of the already-counted window, connectivity-transfer, and sweep-extraction families, not a new theorem family). Earlier: synced 2918 declarations across 66 modules with the irregular-Cheeger-window delivery — no new file, +16: `EdgePerturbation_QA.lean`'s normWindow section with the window-Cheeger engine pair pinned on `K₂` (ceiling `2 = 2·(1·φ)` attained with equality) and on the genuinely irregular `P₃` (`1/2 ≤ 1 ≤ 4`, honest slack; φ(P₃) = 1 transferred entrywise from the irregular-Cheeger fixture), the scale-invariance raw computation (`normalizedLaplacian` of the weight-2 edge = that of the unit edge, entrywise) with `λ₂(L_sym) = 2` at the all-true outcome, the admissibility witnesses on both sides of the window (all-false excluded by the degree floor `0 < 1/2`; `P₃` all-true by the degree ceiling `5 > 3` with nonnegative entries), the complement witness (`2` strictly inside the window at `t = 1/2`, against floor `−1/8` and ceiling `9`), and the two closed-form instances (`4 exp(−1/64)`); 12 audited declarations at exactly the standard three (`wip/irrwin_axcheck.lean`), the two theorem-instantiating pins honestly carrying `matrix_hoeffding`; the score held at 4.0 per protocol — a composition of the already-counted edge-perturbation, Cheeger, and degree-sandwich families plus the window-Cheeger engine pair, not a new theorem family). Earlier: synced 2902 declarations across 66 modules with the degree-eigenvalue-sandwich delivery — one new file, +37: `DegreeSandwich_QA.lean` with the P₃ exact pin `λ₂(L_sym) = 1` by two independent raw computations (the `≤` side at the eigenpair witness through the general-kernel lemma, the `≥` side by the degree-weighted zero-sum constraint algebra through the variational-of-kernel), the upper side of the sandwich **attained at equality** (`1 = λ₂/dmin` — a wrong `dmin`-side constant breaks exactly this), the wrong-constant pairing fence (`1 ≤ 1/2` refuted), the K₂ regular squeeze tight on both ends (`2 ≤ 2 ≤ 2`), the engine at a non-second index through trace-route pins (`3/2 ≤ 2`), and the **`dmin = 0` isolated-vertex fence** — the degree-floor hypothesis still holds at `dmin = 0` on the fixture while the un-guarded upper side reads `1 ≤ lambda2/0 = 0`, refuted: the junk-instantiation failure mode the positivity guard fences; all audited declarations at the standard three axioms (`wip/ds_qa_spike.lean`'s print-axioms probes); the score held at 4.0 per protocol — the axis's named gap, parametric/randomized QA, is untouched). Earlier: synced 2865 declarations across 65 modules with the sharpened drift-interface delivery — no new file, +10: `EdgePerturbation_QA.lean`'s sharpened-interface section with the envelope arithmetic *proved* (domination `t ≤ γt/(t+δ)` and the same-threshold identity `(γt/(t+δ))/(γ−γt/(t+δ)) = t/δ`, general and joined to concrete numerics at the naive `(1, ½)` instance of `γ = 2`), the closed-form three-path instances at the join point (`6 exp(−1/24)`, both sharpened variants) and at the non-trivial threshold `2` (`s = 4/3`, `6 exp(−2/27)`), the naive delivered-theorem instance at threshold `2`, and the strict-improvement pin `6 exp(−2/27) < 6 exp(−1/24)`; six of the ten unconditional at the standard three, the four theorem-instantiating pins honestly carrying `matrix_hoeffding` (`wip/sharpdrift_axcheck.lean`); the score held at 4.0 per protocol — a matched-threshold *repackaging* of the already-counted drift family plus its envelope arithmetic, not a new theorem family). Earlier: synced 2855 with the Cheeger-window consumer delivery — no new file, +12: `EdgePerturbation_QA.lean`'s Cheeger-window section with the φ(K₂) = 1 and 1-regularity pins transferred at definitional equality from `Cheeger_QA`'s fixture (the join point to the Cheeger QA stack), the base λ₂ = 2 at the `lambda2` interface, the engine window instantiated with the **ceiling attained at equality** (`λ₂ = 2 = 2·(1·φ)`, the third conjunct), the closed-form floor/bracket tail instances at `t = 1/2` (`4 exp(−1/64)`), and **both-sides non-vacuity witnesses** (the all-false outcome below the floor with `λ₂ = 0` attained at equality; the all-true outcome above the ceiling at `λ₂ = 4 ≥ 5/2`)); ten of the 12 unconditional at the standard three, the two tail-instantiating pins honestly carrying `matrix_hoeffding` (`wip/cheegerfloor_axcheck.lean`); the score held at 4.0 per protocol — a composition of the already-counted edge-perturbation and Cheeger families plus their two-engine interface pair, not a new theorem family. Earlier: synced 2843 with the eigenvalue-level edge-perturbation tail delivery — no new file, +13: `EdgePerturbation_QA.lean`'s spectral-gap section with the base and perturbed K₂ spectra pinned by the kernel-plus-trace route (`λ₂ = 2`; `λ₂ = 4` at the all-true outcome where the resampled graph is the weight-2 edge), the Weyl transfer pinned *tight* at that genuine design outcome (`|4 − 2| = ‖L(E_ω)‖ = 2`, both sides independent routes), the closed-form eigenvalue/λ₂/uniform-form instances on K₂ and the three-path, and the `x = 0` guard fence refuting the un-guarded uniform statement in proved arithmetic (the un-guarded event is all of `Ω`, measure `1`, against `4 exp(−49/16) < 1`); 9 of the 13 unconditional at the standard three, the four tail-instantiating pins honestly carrying `matrix_hoeffding` (`wip/ept_axcheck.lean`); the score held at 4.0 per protocol — a spectrum-level packaging of the already-counted edge-perturbation family, not a new theorem family. Earlier: synced 2830 with the graph-vector sparsification delivery — no new file, +22: `SparsificationTail_QA.lean`'s new graph-vector section with the raw pins `xᵀLx = 4` (Dirichlet identity) and `xᵀL̃x = 8` (per-pair evaluation of the sampled Laplacian's definition), the transport isometry instance joined to the raw `4`, the correspondence joined by two independent routes (the raw `8` against the sampled operator's own evaluation through the claim-A dot values `√(1/2)·2 = √2`), the tight `ε = 1` instance (`8 = 2·4` attained, a pure-data join), failure-event nonemptiness, both interface pins, and the **signed-fixture fences** — one fixture (`L = −rankOne ![1,−2,1]`, all eigenvalues nonpositive, kernel non-constant) where the transport is provably junk-zero while `xᵀLx = −36` and `√(A₀₂/2) ≠ 0`: both the isometry and claim A refuted in proved form without `hnn`, nonnegativity load-bearing on both new engines; 20 of the 22 unconditional at the standard three, the two interface pins honestly carrying `matrix_bernstein` (`wip/ssgv_axcheck.lean`); the score held at 4.0 per protocol — the graph-vector form is the textbook *statement shape* of the already-counted sparsification family, not a new theorem family. Earlier: synced 2808 with the sparsification follow-on delivery — no new file, +8: `SparsificationTail_QA.lean`'s new `(1±ε)` section with the edge vector's *order-independent* im-Π membership pin (at a zero-eigenvalue basis index the edge vector's own definition vanishes, so no `eigvalOf` ordering assumption anywhere), the engine-identity instance joined to the existing four-pair pin, the tight ε = 1 two-sided instance (upper bound attained with equality, consistent with the deviation norm `= 1 = 1/q`), failure-event nonemptiness at hand values (`1 > 3/4`), and the **cone fence** — the un-guarded pointwise multiplicative claim *refuted* at the all-false outcome (`S = 0` proved, `(1/2)·2 = 1 > 0 = qF(S) ones`: the `im Π` restriction load-bearing exactly where the engine lemma needs it) — plus the two interface pins (the multiplicative tail and the `q ≥ (8/3)·log(2d/δ)/ε²` budget corollary at `ε = δ = 1/2`, `q = 100`, the budget hypothesis discharged from `Real.add_one_le_exp`); six of the eight unconditional at the standard three, the two interface pins honestly carrying `matrix_bernstein` (`wip/ssmult_axcheck.lean`); the score held at 4.0 per protocol — the field-standard *packaging* of the already-counted sparsification family plus its engine lemma, not a new theorem family. Earlier: synced 2800 with the PF-family degenerate-corner audit — no new file, +15: `PerronFrobenius_QA.lean`'s audit section (the empty-card verdict `perron_frobenius_hex_unsat_card_zero_QA` — `False` from `hex` alone at `Fintype.card V = 0`, standard three axioms only; the singleton pins `S1_charpoly_QA`/`S1_rootMultiplicity_QA`; the axiom-consumed `perron_frobenius_S1_QA` with the root pinned exactly `1` and the simplicity clause exactly the hand `rootMultiplicity 1 = 1`) and `DirectedMixing_QA.lean` Section D (the empty-card verdict `mass_one_unsat_card_zero_QA` — `False` from `hπsum` alone, the empty sum; the `P1`/`u1` hypothesis stack; the hand constant-sequence limit `P1_singleton_hand_QA` and the non-vacuous axiom instance `P1_singleton_axiom_QA`); the two verdict lemmas and hand pins unconditional at the standard three, the two singleton instances honestly carrying exactly their named axiom (`wip/pfa_axcheck.lean`); the score held at 4.0 per protocol — audit records and corner fixtures, not a new theorem family. Earlier: synced 2785 with the concentration → subspace-stability pipeline delivery — no new file, +20: `EdgePerturbation_QA.lean`'s new drift section with the packaging identity pinned by two independent routes on K₂ (raw weight-space arithmetic vs the design route through the identity theorem — a wrong `laplacian_sum`/`laplacian_smul` breaks exactly one), the three-path variance statistic exact (`∑ₑ L_e² = 4 • L(P₃)`, `‖·‖ = 12` through the pinned λ₃ = 3), the per-outcome stack at p ≡ ¼ (support-graph equality — every edge survives in every outcome), and the closed-form Fiedler-line drift instance `6 exp(−1/24)`; the instance honestly carries `matrix_hoeffding` (`wip/csd_axcheck.lean`), the other 16 new QA theorems unconditional at the standard three). Earlier: synced 2765 with the matrix-Hoeffding consumer delivery — one new file `Derived/EdgePerturbation_QA.lean` (+12) and `Matrix_QA.lean`'s repair section (+4: the three degenerate-dimension refutation records `old_matrix_*_refuted_fin0_QA` proving the pre-repair shapes of `matrix_hoeffding`/`matrix_bernstein`/`matrix_azuma_hoeffding` inconsistent at `card V = 0`, `t = 0` — each from the instantiated old inequality, standard three axioms — plus the `t = 0` honesty lemma `two_card_bound_honest_QA`; the EdgePerturbation QA pins the variance statistic exactly (`‖∑_e L_e²‖ = 8`, the rank-one norm two-sided by the squared-action bound), the all-true outcome's sum exactly the unit edge Laplacian, the closed-form tail instance `4 exp(−1/16)`, the degenerate zero-weight graph, the `p ∉ [0,1]` interval fence, and the negative-weight sign-free witness; the tail instance honestly carries `matrix_hoeffding` (`wip/mh_axcheck.lean`), everything else the standard three). Earlier: synced 2749 with the integrability-audit delivery — no new file, +18: `Scalar_QA.lean`'s new refutation family for the pre-repair `hoeffding_lemma` (the constant defect `old_hoeffding_lemma_refuted_constant_QA` at the fair-coin Rademacher probability fixture with every old hypothesis genuinely satisfied and the norm pinned `≥ 6/5 > 1`; the guard defect `old_hoeffding_lemma_refuted_guard_QA` at the mass-19/10 rescaling with the mean still genuinely zero and the norm pinned `≥ 21/5 > 4`, so no constant rescues the old shape), the re-instantiation `hoeffding_lemma_rademacher_QA` of the repaired axiom (`≤ √6·1`) at the very fixture that kills the old constant, the fixture's integrability routing through the new shelf safety lemma, and the centered-square safety instance; 17 of the 18 new QA theorems unconditional at the standard three, the re-instantiation honestly carrying `hoeffding_lemma` (`wip/asc_axcheck.lean`); the repair itself — probability-measure guard + `√6·a` — is in the Mathlib layer with its two proved safety lemmas `integrable_of_bounded_measurable`/`integrable_sq_sub_mean`, the audit's durable output). Earlier: synced 2731 with the Fiedler-line delivery — no new file, +17: `Fiedler_QA.lean`'s new `FiedlerLineStability` section with the P₃ → K₃ edge-addition headline instance (separation `δ = 2` discharged against the two pinned spectra, the single-edge perturbation norm pinned exactly `2` from both sides — rank-one bound and quadForm witness through the Sparsification delivery's transfer lemmas, consumed cross-module — so the derived bound is exactly `≤ 1`, the perturbed side sitting on Davis–Kahan's own tie branch with zero slack), the common-kernel identification instance at the genuine two-spectrum pair P₃/K₃, the fix-iff vector pins, and the disconnected fence proving the identification's connectivity hypothesis load-bearing (both iff directions exercised); all 17 new public QA theorems unconditional at the standard three (`wip/fsd2_axcheck.lean`). Earlier: synced 2714 with the Fiedler-subspace Davis–Kahan delivery — no new file, +19: `Fiedler_QA.lean`'s new `FiedlerSubspaceStability` section with the exact combinatorial P₃ spectrum pins (λ₂ = 1, the `≥` side new by the sum-of-squares identity `E(x) = ‖x‖² + 3(x₀+x₂)²` on the zero-sum constraint; λ₃ = 3 by the trace identity; λ₀ = 0 by the new `laplacian_evals_zero`), the two-route zero-perturbation cross-check (wrapper instance with the load-bearing separation discharge vs the raw `P₃ + 0 = P₃` identity, meeting at exactly `0`), and the K₃ tie-awareness witness (λ₂ = λ₃ = 3 both sides exact, the wrapper's hypothesis set provably empty at the tie — vacuous, not silently bounded); all 17 public QA theorems unconditional at the standard three (`wip/fsd_axcheck.lean`). Earlier: synced 2695 with the empirical-stationary-distribution delivery — two new files, +29: `Probability/IIDProduct_QA.lean` (+16) with the four-atom fixture pinned raw at every level (joint masses, total by two routes, the indicator marginal, the centering integral, the numeric independence split `2/3 · 2/3 = 4/9` against the raw atom, and the non-normalized-`q` fence `4 ≠ 1`), and `Derived/EmpiricalStationary_QA.lean` (+13) with the proposal's three obligations — the path-fixture instance with the event honestly characterized empty at `t = 1`, the `n = 0` boundary identified (`univ`, bound `2`) plus the `n ≠ 0` centering fence `0 ≠ 2/3`, and the raw two-sample measure `1/9` meeting the axiom-backed bound `2 exp(−1)` at a number proved from `Real.add_one_le_exp`; the three tail-instantiating pins carry `hoeffding_empirical` honestly, the raw computations are axiom-free. Earlier: synced 2666 with the Ramanujan expansion ceiling delivery — no new file, +7: `Variational_QA`'s K₂ scaling pins (two independent routes to `secondEval (3 • L) = 6` — raw trace/determinant/sortedness vs the lemma joined to the pinned `λ₂ = 2`, so a wrong scaling constant breaks exactly one route — and the negative-`c` fence refuting the conclusion at `c = -1`, sorted spectrum `[-2, 0]`, the `0 < c` hypothesis load-bearing) and `AlonBoppana_QA`'s Step 6 (the C₈ ceiling instance evaluating to `√2` at `k = 0`, the fixture's actual Cheeger constant pinned `≤ 1/4` by the exhibited half-set cut — the independent cut-level route proving the ceiling non-vacuous with strict slack, never tight — and the two-`k` improvement as arithmetic on the statement's own constants with the honest C₈-hosts-only-`k = 0` note). Earlier: synced 2659 with the sparsification Step-1 Slice-3 delivery — `Derived/SparsificationTail_QA.lean` a new file, +27: the K₂ deviation identity pinned with every piece visible (the four-ordered-pair evaluation `0 + (v_e v_eᵀ) + (v_e v_eᵀ) + 0` at the all-true outcome — a wrong guard, weight, or projector identity breaks the value), **the deviation norm `= 1 = 1/q` exactly** (tight both sides, the lower side through the eigenvector witness — the classical bound's constant attained at a real outcome), the transfer lemma's bound attained with **equality** (`|qF(S)v − qF(Π)v| = t·(v⬝v) = 1/2`, the Slice-2 identity `quadForm_imageProjector_eq`'s first consumer at `qF(Π)v = 1/2`), both tail theorems' interface instances, the nonempty-event witness, and the two-sided connectivity content on one fixture — the **disconnected fence** (leverage budget `0 ≠ card − 1` on two components: connectivity load-bearing exactly at the Foster budget) beside the **connectivity-free positive** (the tail needs no connectivity; the deviation is identically zero there); the axiom-conditional tails' QA pins report `matrix_bernstein` honestly in `#print axioms` while the other 25 stay at the standard three). Earlier: synced 2632 with the sparsification Step-1 Slice-2 delivery — `SpectralGraph/Sparsification_QA.lean` a new file, +23: the K₂ leverage budget pinned by two independent routes (the Foster corollary `∑ ‖v_e‖² = 1` vs the raw four-ordered-pair enumeration `1/2 + 1/2 + 0 + 0` — a wrong ordered-pair normalization breaks exactly one route), the rank-one norm identity pinned two-sided at a concrete vector (`‖![1,2] ![1,2]ᵀ‖ = 5`, the lower side through the eigenvector witness itself — the mechanism that then pins the K₂ edge vector's norm `1/2`), the projector trace `= 1`, the exact variance coefficient `c_(0,1) = 1/2`, the bound instance `‖Σ‖ ≤ 1 = 1/q`, and three proved fences — the **Finding-A fence** (the *unguarded* saturated summand's norm `1/2` refutes `≤ 1/q = 1/4` at the missed outcome: the saturation guard load-bearing), the **`q = 0` fence** (junk `min 1 0 = 0` probabilities, conclusion refuted), and the centering instance). Earlier: synced 2609 with the sparsification Step-1 Slice-1 delivery — `Probability/BernoulliProduct_QA.lean` a new file and QA domain, +24: the four-atom fixture at `p = ![1/2, 1/3]` with total mass by two independent routes, the numeric independence pin through `indepFun_coord` (`1/2 · 2/3 = 1/3` joined to the cylinder pins), the centering integral by two routes, the matrix-layer clause instances, and two proved fences — the `[0,1]` bounds load-bearing for the mass normalization, and the `p e ≠ 0` centering hypothesis refuted at the junk `0/0` value). Earlier: synced 2585 with the Alon–Boppana Step-5 delivery — the program's capstone — `AlonBoppana_QA` extended +9: the capstone instance `secondEval (2•1 − C₈) ≤ 2 − (1 + 0)/1 = 1` through the `√` packaging, the classical-shape instance documenting the error term swallowing the content at `k = 0` (`≤ 2 − 2 + 2`), the diameter instance `3 ≤ diam (supportGraph C₈)` through the new bridge `distEdge_le_diam`, the **loop-pair fence** (the loop `(2,2)`'s level-0 class is `{2}` of card `1 ≠ 2` — `IsTreeBall` fails and the two-vector orthogonality fails with it, `⟨![1,1,−1],1⟩ = 1 ≠ 0`), and the **independent integer-witness engine route** `secondEval (2•1 − C₈) ≤ (2·6 − 8)/6 = 2/3` at `![1,1,0,−1,−1,−1,0,1]` — strictly stronger than both theorem routes' `≤ 1`, with squared norm `6`, quadratic form `8`, and orthogonality all computed raw. Earlier: the Step-4 delivery synced 2576 (+16: two-route orthogonality, `hfar`/overlap fences, the first eigenvalue-level instance); the Step-3b delivery synced 2549 → 2560 (the numerator pinned tight at equality `6 = 6` with three hypothesis fences); the Step-3a delivery synced 2539 → 2549 (the squared-norm pin by two routes, the K₂ `d = 1` degeneracy fence). |
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

Subject axis 1 (graph and Laplacian models) was re-scored **3.5 → 4.0**
on 2026-08-26 (the signed-graph delivery, `proposals/signed-graphs-balance.md`:
a new model family — the signed Laplacian at a `{±1}` signing, with
Harary balance in kernel form, the magnetic π-flux join making the
2026-08-25 magnetic delivery carry weight from a second theorem family,
and the switching similarity with two-way eigenpair transfer — proved
hard crust at zero new axioms, QA +62). The same sync repaired the
row's stale "absent: directed graphs" clause: directed operators were
delivered 2026-08-22 and the magnetic Laplacian 2026-08-25 under
backlog item 8 — the axis row had not been updated with either. With
both of the axis's named absent categories (directed, signed) now
occupied by verified interfaces, the axis has no named absent
category; its remaining gaps (e.g. signed Cheeger, the multiset-level
signed spectrum equality) are priced follow-ons in the proposal, not
absent model families.

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
