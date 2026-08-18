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
| `sherman_morrison` | axiom | Rank-one Sherman–Morrison formula | [Higham 2002](../sources/higham_matrix_updates.md) |

## Deferred Work

The following entries from an earlier plan remain unimplemented and are
not promised: `davis_kahan_tan_theta`, `davis_kahan_delta`, resolvent
bounds, and a separate spectral-projector module (the real projector
definitions live in `Scaffold.Mathlib.GraphTheory.Spectral`).

## Applications

- `weyl_inequality` / `spectral_gap_stability` control how far event
  streams can move Laplacian spectra ([Spectral Graph Theory map](spectral_graph.md)).
- `davis_kahan_sin_theta` is the engine of the derived projector-drift
  chain (`Derived.davisKahanTwoPoint`, `Derived.eventStreamProjectorDrift`)
  and was the engine of the now-deprecated (2026-08-17)
  `spectral_persistence` compatibility axiom.

## See Also

- [Sources Index](../sources/) for detailed bibliographic information
