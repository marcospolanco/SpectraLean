# Perturbation Theory

This index maps Lean modules and axioms for perturbation theory and
spectral stability.

## Status

**Implemented and build-certified** (see the QA scoreboard):
`Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.{Weyl,DavisKahan}`.

## Implemented Modules

### Weyl Bounds

**Module**: `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl`

| Axiom | Description | Source |
|-------|-------------|--------|
| `weyl_inequality` | Each sorted eigenvalue moves by at most `‖E‖` under a symmetric perturbation | [Weyl 1912 / Bhatia 1997](../sources/weyl_1912_bhatia.md) |
| `spectral_gap_stability` | A gap shrinks by at most `2‖E‖` | [Weyl 1912 / Bhatia 1997](../sources/weyl_1912_bhatia.md) |

### Davis–Kahan

**Module**: `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan`

| Axiom | Description | Source |
|-------|-------------|--------|
| `davis_kahan_sin_theta` | Projector rotation `≤ ‖E‖/δ` under two-sided spectral separation | [Davis & Kahan 1970](../sources/davis_kahan_1970.md) |

### Matrix Update Identities (bridge utilities)

**Module**: `Scaffold.Mathlib.Core.MatrixUpdates`

| Axiom | Description | Source |
|-------|-------------|--------|
| `woodbury_identity` | Woodbury identity for low-rank event updates | [Higham 2002](../sources/higham_matrix_updates.md) |
| `sherman_morrison` | Rank-one Sherman–Morrison formula | [Higham 2002](../sources/higham_matrix_updates.md) |

## Deferred Work

The following entries from an earlier plan remain unimplemented and are
not promised: `davis_kahan_tan_theta`, `davis_kahan_delta`, resolvent
bounds, and a separate spectral-projector module (the real projector
definitions live in `Scaffold.Mathlib.GraphTheory.Spectral`).

## Applications

- `weyl_inequality` / `spectral_gap_stability` control how far event
  streams can move Laplacian spectra ([Spectral Graph Theory map](spectral_graph.md)).
- `davis_kahan_sin_theta` is the per-step engine of the admitted
  `spectral_persistence` principle.

## See Also

- [Sources Index](../sources/) for detailed bibliographic information
