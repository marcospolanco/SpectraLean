# Perturbation Theory

This index maps Lean modules and axioms for perturbation theory and
spectral stability.

## Status

**Implemented and build-certified** (see the QA scoreboard):
`Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.{Weyl,DavisKahan}`.

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

### Davis–Kahan

**Module**: `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `davis_kahan_sin_theta` | **proved theorem** (retired from axiom 2026-08-21 — the Duhamel/exponential-integral route; `#print axioms` reads only the three standard axioms) | Projector rotation `≤ ‖E‖/δ` under the two-cluster separation `λ_{k+1}(A+E) - λ_k(A) ≥ δ` (single-pair form, the YWS Theorem 1 operator-norm variant at the bottom cluster — locator corrected 2026-08-21, see the source index); proof: three-way tie split consuming the equal-rank identity and the Duhamel bound below, plus Weyl and the `≤ 1` endpoint for the tied cases | [Davis & Kahan 1970](../sources/davis_kahan_1970.md) |

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
Chapter 4 note) is recorded as a future opportunity, not the same
statement as `davis_kahan_sin_theta` and not part of its retirement.

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
