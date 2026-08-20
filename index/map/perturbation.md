# Perturbation Theory

This index maps Lean modules and axioms for perturbation theory and
spectral stability.

## Status

**Implemented and build-certified** (see the QA scoreboard):
`Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.{Weyl,DavisKahan}`.

## Implemented Modules

### Weyl Bounds

**Module**: `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `weyl_inequality` | axiom | Each sorted eigenvalue moves by at most `‖E‖` under a symmetric perturbation | [Weyl 1912 / Bhatia 1997](../sources/weyl_1912_bhatia.md) |
| `spectral_gap_stability` | proved (from `weyl_inequality`) | A gap shrinks by at most `2‖E‖` | corollary; see [Weyl 1912 / Bhatia 1997](../sources/weyl_1912_bhatia.md) |

### Davis–Kahan

**Module**: `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan`

| Declaration | Kind | Description | Source |
|-------------|------|-------------|--------|
| `davis_kahan_sin_theta` | axiom | Projector rotation `≤ ‖E‖/δ` under the two-cluster separation `λ_{k+1}(A+E) - λ_k(A) ≥ δ` (single-pair form, matching Yu–Wang–Samworth Thm 2) | [Davis & Kahan 1970](../sources/davis_kahan_1970.md) |

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

## Applications

- `weyl_inequality` / `spectral_gap_stability` control how far event
  streams can move Laplacian spectra ([Spectral Graph Theory map](spectral_graph.md)).
- `davis_kahan_sin_theta` is the engine of the derived projector-drift
  chain (`Derived.davisKahanTwoPoint`, `Derived.eventStreamProjectorDrift`)
  and was the engine of the now-deprecated (2026-08-17)
  `spectral_persistence` compatibility axiom.

## See Also

- [Sources Index](../sources/) for detailed bibliographic information
