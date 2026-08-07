# Perturbation Theory

This index maps Lean modules and axioms for perturbation theory and spectral stability.

## Status

**Currently implemented**: None (planned for v0.3.0)

## Planned Modules

### Davis-Kahan Theorems

**Module**: `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan`

| Axiom | Description | Source |
|-------|-------------|--------|
| `davis_kahan_sin_theta` | Sin Θ theorem for eigenvector perturbation | Stewart (1974) |
| `davis_kahan_tan_theta` | Tan Θ variant | Stewart (1974) |
| `davis_kahan_delta` | Δ theorem | Davis & Kahan (1970) |

### Resolvent Bounds

**Module**: `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.ResolventBounds`

| Axiom | Description | Source |
|-------|-------------|--------|
| `resolvent_perturbation_bound` | Bound on resolvent difference | Bhatia (1997) |
| `resolvent_norm_bound` | General resolvent inequality | Kato (1966) |

### Spectral Projectors

**Module**: `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.SpectralProjectors`

| Axiom | Description | Source |
|-------|-------------|--------|
| `spectral_projector_stability` | Perturbation of spectral projectors | Bhatia (1997) |
| `spectral_gap_perturbation` | Gap-dependent bounds | Kato (1966) |

## Applications

These results are used in:

- Random matrix theory (eigenvalue separation)
- Spectral clustering (stability of clustering)
- Dimensionality reduction (perturbation of principal components)
- Graph theory (eigenvalue interlacing)

## See Also

- [Random Matrix Theory](random_matrix.md) for matrix concentration
- [Sources Index](../sources/) for detailed bibliographic information
