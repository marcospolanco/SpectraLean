# Perturbation Theory

This index maps Lean modules and axioms for perturbation theory and
spectral stability.

## Status

**Implemented and build-certified** (see the QA scoreboard):
`Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.{Weyl,DavisKahan,BandDavisKahan}`.

## Implemented Modules

### Weyl Bounds

**Module**: `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl`

All proved, zero axioms (`weyl_inequality` retired from admitted axiom to
proved theorem on 2026-08-20 — `proposals/discharge-perturbation-axioms.md`,
the additive window from the Courant–Fischer engine composed with the proved
`l2OpNorm_eq_max_abs_evals` bridge).

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `weyl_inequality` | proved (retired from axiom 2026-08-20) | Each sorted eigenvalue moves by at most `‖E‖` under a symmetric perturbation | [Weyl 1912 / Bhatia 1997](../sources/weyl_1912_bhatia.md) |
| `weyl_additive_upper` | proved | `λᵢ(A+E) ≤ λᵢ(A) + λₙ(E)` — the top half of the additive Weyl window, from the Courant–Fischer engine's two witness forms | [Horn & Johnson, Matrix Analysis, Thm 4.3.1](../sources/weyl_1912_bhatia.md); [Weyl 1912 / Bhatia 1997](../sources/weyl_1912_bhatia.md) |
| `weyl_additive_lower` | proved | `λᵢ(A) + λ₁(E) ≤ λᵢ(A+E)` — the bottom half of the additive window (mirror route; consumes `evals_first_mul_dotProduct_le_quadForm`, the bottom Rayleigh domination added to `GraphTheory.Spectral` with this retirement) | same |
| `spectral_gap_stability` | proved (fully hard crust since the Weyl retirement) | A gap shrinks by at most `2‖E‖` | corollary; see [Weyl 1912 / Bhatia 1997](../sources/weyl_1912_bhatia.md) |

**Adversarial fence audit (2026-09-04,
`proposals/adversarial-fences-davis-kahan-core-family.md`):**
`spectral_gap_stability`'s two load-bearing clauses carry hypothesis-form
negative witnesses in `Weyl_QA.lean` — `hnorm` at the gap-shrinking
`diag(0,−1)` perturbation (gap `2 → 1` at norm `1`, the dropped statement
read at `ε = 1/4` demanding `1 ≥ 3/2`) and `hγ` at the inflated
`γ = 100`. The additive pair's `hcard` is recorded non-fenceable by a
distinct mechanism: the conclusion's own `Fin` index proof term
(`⟨Fintype.card V - 1, by omega⟩`) consumes it, so the dropped statement
does not elaborate (proof-term-in-display entanglement).

### Davis–Kahan

**Module**: `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `davis_kahan_sin_theta` | **proved theorem** (retired from axiom 2026-08-21 — the Duhamel/exponential-integral route; `#print axioms` reads only the three standard axioms) | Projector rotation `≤ ‖E‖/δ` under the two-cluster separation `λ_{k+1}(A+E) - λ_k(A) ≥ δ` (single-pair form, the YWS Theorem 1 operator-norm variant at the bottom cluster — locator corrected 2026-08-21, see the source index); proof: three-way tie split consuming the equal-rank identity and the Duhamel bound below, plus Weyl and the `≤ 1` endpoint for the tied cases | [Davis & Kahan 1970](../sources/davis_kahan_1970.md) |

**Adversarial fence audit (2026-09-04,
`proposals/adversarial-fences-davis-kahan-core-family.md`):** the
theorem's two free clauses carry hypothesis-form negative witnesses in
`DavisKahan_QA.lean` — `hδ` at the negative-`δ` corner (the separation
genuine at `δ = −1/2`, the bound's right side `−3/2` against a
nonnegative norm) and `hsep` at the inflated `δ = 100` (the pinned exact
distance `√(1/10) > 3/400`). The `hA`/`hAE`/`hk` clauses are
signature-entangled (the `initialProjector` displays consume the proofs)
— recorded non-fenceable.

### Band Davis–Kahan (bounded windows)

**Module**: `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan`
(delivered 2026-08-24, `proposals/band-davis-kahan.md`, backlog item 9;
the difference form added the same day by
`proposals/band-davis-kahan-difference.md`; all proved, zero axioms —
the algebraic commutator/shift route)

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `l2OpNorm_bandProjector_mul_bandProjector_le_of_lt` | proved | The bounded-window Davis–Kahan product bound: `B`'s band `(a₂, b₂]` strictly above `A`'s `(a₁, b₁]` (`b₁ + δ ≤ a₂`) ⇒ `‖Q * P‖ ≤ ‖A − B‖ / δ`, constant 1, no rank hypothesis, no sorted-spectrum index — the band-projector sibling of `davis_kahan_sin_theta` | [Vershynin, HDP 2018, Thm 4.1.15–4.1.16 (route)](../sources/vershynin_hdp.md); classical statement Davis–Kahan 1970 / YWS 2015 Thm 1 (see [Davis & Kahan 1970](../sources/davis_kahan_1970.md)) |
| `l2OpNorm_bandProjector_mul_bandProjector_le_of_gt` | proved | The mirror orientation: `B`'s band strictly below `A`'s (`b₂ + δ ≤ a₁`) ⇒ the same product bound | same |
| `l2OpNorm_bandProjector_sub_bandProjector_le` | proved | **The difference (sin Θ) form:** equal-rank band projectors with B's out-of-window eigenvalues δ-away from A's window closure `[a₁, b₁]` ⇒ `‖P_A − P_B‖ ≤ ‖A − B‖ / δ`, constant 1 — the subspace-distance shape, through the equal-rank gap identity `l2OpNorm_sub_eq_of_rank_eq` (its first consumer) plus the engine re-run at the complement projector `1 − Q` | [Davis & Kahan 1970 / YWS 2015 Thm 1 (operator-norm difference shape)](../sources/davis_kahan_1970.md); the consumed identity: Kato, *Perturbation Theory for Linear Operators*, 2nd ed., 1976, Ch. I §4 (cited in `Perturbation/ProjectionGap.lean`) |
| `l2OpNorm_bandProjector_sub_bandProjector_le_of_mem` | proved | The interval-margin corollary: B's window containing A's with δ-margin (`a₂ + δ ≤ a₁`, `b₁ + δ ≤ b₂`) discharges the eigenvalue-level separation | same |
| `l2OpNorm_bandProjector_sub_bandProjector_le_of_pairwise` | proved | **The cluster form:** the same difference bound under *pairwise* separation — every eigenvalue of `B` outside its window δ-away from every eigenvalue of `A` inside its window, the literal YWS Theorem 1 δ — strictly weaker than the closure separation (interior B-eigenvalues covered: handled in-proof by a projector-free Parseval expansion at the eigenvector forcing `δ ≤ ‖A − B‖`, boundary ones by the engine at the cluster-range center/radius) | [YWS 2015 Theorem 1 (the pairwise mixed separation at constant 1)](../sources/davis_kahan_1970.md) |
| `l2OpNorm_bandProjector_sub_bandProjector_le_two_of_symm` | proved | **The symmetric form:** both out-of-window flanks δ-separated pairwise (B-out vs A-in *and* A-out vs B-in) ⇒ `‖P_A − P_B‖ ≤ 2‖A − B‖/δ` with **no rank hypothesis** — the YWS both-gaps dimension-freeness; 2 is exactly the triangle inequality at `P − Q = (I−Q)P − Q(I−P)`, the rank-free pairwise product bound instantiated at both argument orders (the engine's 4th/5th consumers), the right action moved by `l2OpNorm_transpose`; when ranks differ `δ ≤ ‖A − B‖` is forced in-proof (the honest trivial-regime degradation) | [YWS 2015 Theorem 1 (the both-gaps variants at constant 2; the pairwise-separation analog)](../sources/davis_kahan_1970.md) |
| `l2OpNorm_transpose` | proved | **Transpose invariance** of the ℓ² operator norm (`‖Mᵀ‖ = ‖M‖`), by two pairing-characterization applications; absent from the pinned Mathlib and the shelf before the symmetric form — any consumer that bounds a right action while the engine states the left action needs it | standard |
| `bandProjector_eq_of_forall_mem_iff` | proved | **Capture equality:** two (non-junk) windows selecting the same eigenvalues give the same band projector — the cluster is a window-mod-class, not a window; the window-existence argument's transfer step | standard |
| `bandProjector_eq_zero_of_forall_not_mem` | proved | The empty-cluster corner: a non-junk window selecting no eigenvalue gives the zero projector | standard |
| `rank_bandProjector_eq_card` | proved | **The rank supplier:** a band projector's rank is exactly the count of in-band eigenvalues (via trace — a symmetric idempotent's spectrum lies in `{0,1}` exactly); makes the difference form's equal-rank hypothesis checkable | standard |
| `trace_spectralProjector_eq_card` / `trace_bandProjector_eq_card` | proved | The trace parents of the rank supplier (each outer product contributes its unit eigenvector's squared diagonal) | standard |
| `l2OpNorm_mulVec_le` | proved | The vector action bound `‖M *ᵥ v‖ ≤ ‖M‖ ‖v‖` in the sqrt-of-dot-product packaging — the shelf gap landed with this module (absent from the pinned Mathlib; through the `cstar_norm_def` + `toEuclideanCLM` spine) | Mathlib C*-algebra norm transport |
| `mulVec_bandProjector_comm` | proved | A self-adjoint matrix commutes with its own band projector at the vector level (the 2026-08-21 survey's spike-verified fact, landed here; componentwise through the eigenbasis) | standard |

### Set-form Davis–Kahan (cluster projectors)

**Module**: `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan`
(the `SetForm` sections; delivered 2026-08-24, `proposals/cluster-projector.md`,
extended the same day by `proposals/cluster-projector-symmetric.md` — the
cluster/symmetric deliveries' recorded follow-ons; all proved,
zero axioms — the commutator/shift engine re-run at
`GraphTheory.ClusterProjector`'s set-valued projectors, the component
action its only projector input)

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `l2OpNorm_clusterProjector_mul_clusterProjector_le` | proved | **The set-form product bound:** `‖Q_T * P_S‖ ≤ ‖A − B‖/δ` at constant 1 when every in-`S` eigenvalue of `A` lies within `r` of `c` and every in-`T` eigenvalue of `B` lies at distance ≥ `r + δ` from `c` — the hypotheses the algebraic engine actually consumes, stated between the clusters as sets; no interval structure assumed of `S` or `T` | [Vershynin, HDP 2018, Thm 4.1.15–4.1.16 (route)](../sources/vershynin_hdp.md); set statement shape: Davis–Kahan 1970 / YWS 2015 Thm 1 cluster form (see [Davis & Kahan 1970](../sources/davis_kahan_1970.md)) |
| `l2OpNorm_clusterProjector_sub_clusterProjector_le` | proved | **The set-form difference bound (equal rank):** `‖P_A(S) − P_B(T)‖ ≤ ‖A − B‖/δ` at constant 1, same `hnear`, with every *out-of-`T`* eigenvalue of `B` at distance ≥ `r + δ` from `c` — **no dichotomy, no interior case**: the equal-rank identity reduces to the one-sided residual, the complement law `1 − Q_T = Q_{Tᶜ}` (a definition-level fact the window family lacks) replaces the window form's separate complement engine, and the product form applies at `Tᶜ` | same; the consumed identity: Kato Ch. I §4 (`Perturbation/ProjectionGap.lean`) |
| `l2OpNorm_clusterProjector_sub_clusterProjector_le_two_of_symm` | proved | **The two-sided set-form difference bound (no rank hypothesis):** `‖P_A(S) − P_B(T)‖ ≤ 2‖A − B‖/δ` under *both-flank* separation with two center/radius pairs (A's in-`S` cluster within `rS` of `cS` with B's out-of-`T` cluster ≥ `rS + δ` from `cS`; B's in-`T` cluster within `rT` of `cT` with A's out-of-`S` cluster ≥ `rT + δ` from `cT`) — the YWS Theorem 1 both-gaps shape at arbitrary eigenvalue sets, **no multiplicity counting anywhere**; a pure composition (ring identity + complement law at both residuals + `l2OpNorm_transpose`, the constant 2 exactly the triangle inequality — the set product bound's unconditional hypotheses make the window form's regime split unnecessary) | [Davis & Kahan 1970](../sources/davis_kahan_1970.md) (both-gaps set-cluster form; the window twin: YWS 2015 Thm 1, operator-norm variant) |

### The Duhamel Bound (Davis–Kahan Step 1, component 2)

**Module**: `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Duhamel`

Delivered 2026-08-21, all proved, zero new axioms — the second of the
two components `discharge-perturbation-axioms.md`'s Step-0 survey named
as required: the exponential-integral route that reaches the
constant-1 operator-norm bound the entrywise eigenbasis-coordinate
route provably cannot.

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `l2OpNorm_one_sub_spectralProjector_mul_spectralProjector_le` | proved | **The Duhamel bound**: `‖(1 − Q) * P‖ ≤ ‖E‖ / (b − a)` for `P = spectralProjector A a`, `Q = spectralProjector (A+E) c'`, every eigenvalue of `A+E` above `c'` at least `b > a`; scalar pairing + FTC + cluster-filtered Parseval damping + the pairing (duality) norm reduction | proposal's route; the standard semigroup/Duhamel argument specialized to finite dimensions, no single external citation |
| `l2OpNorm_le_of_abs_dotProduct_le` | proved | Operator-norm bound through pairings (duality): `|y ⬝ᵥ (M *ᵥ x)| ≤ c‖x‖‖y‖` forces `‖M‖ ≤ c` — by self-application | same |
| `heatApply` and its layer | proved | The vector-level heat semigroup (damped eigenbasis expansion), Parseval damping, eigenaction, differentiability in `t`, the `t = 0` expansion identity | spike-verified primitives (`wip/dk_spike.lean`), transferred |
| `evals_succ_le_of_lt` | proved | Sorted-spectrum step: eigenvalues strictly above `evals ⟨k⟩` are at least `evals ⟨k+1⟩` — the interior companion of the two extreme pins | closed-form |
| `dotProduct_eigvecOf_spectralProjector_mulVec` | proved | The projector coefficient filter: `vᵢ ⬝ᵥ (P_c *ᵥ z) = if λᵢ ≤ c then vᵢ ⬝ᵥ z else 0` | closed-form |
| `heatApply_dotProduct_self_le_of_le` / `_of_gt` | proved | Cluster-filtered decay: `‖e^{-tM} z‖² ≤ e^{-2bt}‖z‖²` (z orthogonal to the low cluster, eigenvalues above it ≥ b) and the growing-side mirror | Parseval damping |
| `rank_spectralProjector_eq_card_filter` / `rank_spectralProjector_evals_of_lt` | proved | The rank of a spectral projector is the threshold filter's card; exactly `k+1` under no tie | closed-form |
| `l2OpNorm_sub_le_one_of_isSymm_idempotent` | proved | The trivial gap-metric endpoint `‖P − Q‖ ≤ 1`, load-bearing for the retirement's tie cases | closed-form |

**Adversarial fence audit (2026-09-04,
`proposals/adversarial-fences-davis-kahan-core-family.md`):** the
Duhamel bound's two free clauses (`hab`, `hcl`), the rank pin's no-tie
clause, the trivial endpoint's four projector-structure clauses, and the
sorted-step lemma's eigenvalue clause all carry hypothesis-form negative
witnesses in `DavisKahan_QA.lean` — `hab` at the negative-denominator
corner with `hcl` genuine; `hcl` at the inflated window `b = 100`
through a new threshold-`1` projector pin (the witness square
`‖(1−Q)P‖² ≥ 1/10` against `(3/400)²`); the zero-matrix tie giving
`rank 2 ≠ 1` via `spectralProjector_eq_one`; the endpoint's clauses at
an asymmetric idempotent (`‖P‖² ≥ 5`) and a symmetric non-idempotent
(`‖P‖² ≥ 4`); and the sorted step at the pinned bottom eigenvalue
(`2 ≤ 0`).

### Equal-Rank Projector Identity (Davis–Kahan Step 1, component 1)

**Module**: `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.ProjectionGap`

Delivered 2026-08-21, all proved, zero new axioms — the first of the two
components `discharge-perturbation-axioms.md`'s Step-0 survey named as
required to retire `davis_kahan_sin_theta` at its exact constant-1
operator-norm statement.

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `l2OpNorm_sub_eq_max_of_isSymm_idempotent` | proved | `‖P−Q‖ = max ‖(I−Q)P‖ ‖(I−P)Q‖` for symmetric idempotent `P, Q` — always true, no rank hypothesis | proposal's route, layer (A) |
| `l2OpNorm_sub_eq_of_rank_eq` | proved | The headline identity: `‖P−Q‖ = ‖(I−Q)P‖` when `P, Q` additionally have equal rank (principal-angles route via the sandwich `PQP`, eigenspace transfer, and the norm-eigenvalue bridge) | proposal's route, layer (B); no external citation — closed-form finite-dimensional linear algebra |
| `l2OpNorm_one_sub_mul_sq_eq` | proved | The squared-residual pin `‖(I−Q)P‖² = 1 − τ` (`τ` the sandwich's threshold eigenvalue) underlying the headline identity | same |
| `evals_pqp_eq_evals_qpq` | proved | Spectral symmetry `evals(PQP) = evals(QPQ)` via the injective eigenspace transfer `v ↦ QPv` — the equal-rank core's key symmetry step | same |

**Adversarial fence audit (2026-09-04,
`proposals/adversarial-fences-davis-kahan-core-family.md`):** both
headline identities have signature-free clause surfaces — the most
fenceable class in the library — and `ProjectionGap_QA.lean` now fences
eight of the ten: the identity's `hP`/`hPP`/`hQ`/`hQQ`/`hrank` and the
core's `hPP`/`hQQ`/`hrank`, at trivial fixtures (an asymmetric
idempotent, symmetric non-idempotents, the zero matrix against the
delivered rotation projector) with witness-vector norm bounds. The
core's `hP`/`hQ` are deferred with the zero-residual analysis recorded:
an idempotent `P` of equal rank whose residual `(1−Q)P` vanishes has
`range P = range Q`, forcing `(1−P)Q = 0` too — both computed rank-1
cases came out equal, suggesting truth-removability.

### Matrix Update Identities (bridge utilities)

**Module**: `Scaffold.Mathlib.Core.MatrixUpdates`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `woodbury_identity` | proved (from Mathlib's `Matrix.invOf_add_mul_mul`) | Woodbury identity for low-rank event updates, at the standard middle factor `C⁻¹ + V A⁻¹ U`; retired from a verified-false axiom on 2026-08-18 (see the source file's repair record) | [Higham 2002](../sources/higham_matrix_updates.md) |
| `sherman_morrison` | proved (the `k = Fin 1` specialization of the proved `woodbury_identity`) | Rank-one Sherman–Morrison formula; retired from axiom on 2026-08-18 as a pure proof task (statement already correct — no repair) | [Higham 2002](../sources/higham_matrix_updates.md) |

### Resolvent Calculus

**Module**: `Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent`

All proved, zero axioms (delivered 2026-08-19 for proposal steps 0–2 of
`proposals/resolvent-calculus-psd.md`; step 3 — injectivity — added
2026-08-20, completing the program).

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `abs_eigvalOf_le_l2OpNorm` | proved | Every eigenvalue of a symmetric matrix is bounded by the `L2OpNorm` operator norm (unit eigenvector through `toEuclideanCLM`) | proposal's Step-0 fallback route (eigenbasis); the C*-algebra thread `IsSelfAdjoint.spectralRadius_eq_nnnorm` is structurally inapplicable to real matrices (requires `NormedAlgebra ℂ`) |
| `l2OpNorm_le_of_abs_eigvalOf_le` | proved | `‖M‖ ≤ c` whenever every eigenvalue satisfies `|λ| ≤ c` (Parseval + eigenaction resolution) | same route |
| `abs_evals_le_l2OpNorm` / `l2OpNorm_le_of_abs_evals_le` | proved | The two bridge directions restated in the sorted-spectrum `evals` API | corollaries of the two above |
| `l2OpNorm_eq_max_abs_evals` | proved | `‖M‖ = max |evals hM 0| |evals hM last|` — the finite-dimensional spectral-radius identity for real symmetric matrices | the proposal's Step-0 target statement |
| `isUnit_det_add_smul_one_of_quadForm_nonneg` | proved | `M + t • 1` invertible for any matrix with nonnegative quadratic form and `t > 0` (kernel vector route; no symmetry needed) | proposal item 1 |
| `isUnit_det_add_one_of_quadForm_nonneg` | proved | The `t = 1` instance — the resolvent's own shift | corollary |
| `resolvent_identity_sub` | proved | `(A+1)⁻¹ − (B+1)⁻¹ = (A+1)⁻¹ * (B − A) * (B+1)⁻¹` | proposal item 3 |
| `l2OpNorm_inv_add_smul_one_le_inv_of_quadForm_nonneg` | proved | `‖(M + t•1)⁻¹‖ ≤ t⁻¹` for any matrix with nonnegative quadratic form and `t > 0` — no symmetry hypothesis (the recorded Step-2 route deviation: energy inequality + dot-product Cauchy–Schwarz through the bridge's transport spine, not the eigenvalue transfer) | proposal item 2 (general-`t` strengthening) |
| `l2OpNorm_inv_add_one_le_one_of_quadForm_nonneg` | proved | The `t = 1` instance: the resolvent is a contraction | proposal item 2 |
| `l2OpNorm_resolvent_sub_le_of_quadForm_nonneg` | proved | The resolvent map is `1`-Lipschitz: `‖(A+1)⁻¹ − (B+1)⁻¹‖ ≤ ‖A − B‖` (Step-1 identity + scoped `NormedRing` submultiplicativity + the norm bound twice) | proposal item 4 |
| `eq_of_inv_add_one_eq_inv_add_one` | proved | Equal resolvents of `+1`-invertible matrices force equal matrices (contrapose the Step-1 identity, cancel both invertible outer factors; the determinant hypotheses are load-bearing) | proposal item 5, core form |
| `resolvent_map_injective_of_quadForm_nonneg` | proved | `A ≠ B → (A+1)⁻¹ ≠ (B+1)⁻¹` on quadForm-nonneg matrices — the resolvent map is injective on the PSD cone | proposal item 5 |
| `inv_add_one_eq_inv_add_one_iff_of_quadForm_nonneg` | proved | Resolvent equality ↔ matrix equality on quadForm-nonneg matrices — the certificate form for contrapositive consumers | proposal item 5, packaged |

**Adversarial fences** (2026-09-05,
`proposals/adversarial-fences-resolvent-family.md`): the shelf's
hypothesis-necessity surface is complete — 12 hypothesis-form fences in
`Resolvent_QA.lean`'s `AdversarialFences` section, reconciling the
pre-discipline QA's five free-form witnesses into the fence discipline.
Both upper bridges' `0 ≤ c` clauses are load-bearing only through the
`Fin 0` corner (on nonempty types the eigenvalue hypothesis already
forces `c ≥ 0`); the invertibility `hpsd` clauses fall at `M = -1` and
the `ht` clause at `t = 0` on the `K₂` Laplacian with PSD genuine; the
resolvent identity's determinant clauses separate at a one-sided
singular shift (`-1 ≠ 0` / `1 ≠ 0` — a both-singular pair collapses
both sides identically); the norm bound's `ht` needs an *invertible*
PSD fixture at `t = 0` (the junk inverse of a singular one satisfies
the dropped statement vacuously); both Lipschitz `quadForm` clauses
separate `4×` (`3 ≤ 3/4`); the injectivity trio's jointly dropped
clauses fall to the delivered `-1` vs `-1 + nilpotent` guard, while the
individually dropped determinant clauses are P4 truth-removable
(recorded mechanism). The five `hM` clauses are signature-entangled and
`hcard` proof-term-in-display — recorded non-fenceables.

## Deferred Work

The following entries from an earlier plan remain unimplemented and are
not promised: `davis_kahan_tan_theta`, `davis_kahan_delta`, and a
separate spectral-projector module (the real projector definitions live
in `Scaffold.Mathlib.GraphTheory.Spectral`). The resolvent *injectivity*
statement formerly listed here was delivered 2026-08-20 (Step 3,
completing the resolvent program).

A distinct *bounded-window* Davis–Kahan theorem (both clusters finite,
provable by pure algebra against `GraphTheory.Band` — see
`docs/6_SGT_BACKLOG.md` item 9 and `index/sources/vershynin_hdp.md`'s
Chapter 4 note) was delivered 2026-08-24 in both forms: the product
bound (`proposals/band-davis-kahan.md`) and the difference/sin-Θ form
(`proposals/band-davis-kahan-difference.md`, the section above). It is
not the same statement as `davis_kahan_sin_theta` and was not part of
its retirement.

## Applications

- `weyl_inequality` / `spectral_gap_stability` (both proved since the
  2026-08-20 retirement) control how far event
  streams can move Laplacian spectra ([Spectral Graph Theory map](spectral_graph.md)).
- `davis_kahan_sin_theta` is the engine of the derived projector-drift
  chain (`Derived.davisKahanTwoPoint`, `Derived.eventStreamProjectorDrift`),
  which covers the motivating use of the now-retired (2026-08-20)
  `spectral_persistence` compatibility axiom.

## See Also

- [Sources Index](../sources/) for detailed bibliographic information
