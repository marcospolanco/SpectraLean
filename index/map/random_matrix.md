# Random Matrix Theory

This index maps Lean modules and axioms for random matrix concentration inequalities.

## Status

**Currently implemented**: None (planned for v0.2.0)

## Planned Modules

### Matrix Concentration

**Module**: `Scaffold.Mathlib.LinearAlgebra.RandomMatrix.MatrixBernstein`

| Axiom | Description | Source |
|-------|-------------|--------|
| `matrix_bernstein` | Matrix Bernstein inequality | Tropp Thm 1.1 |
| `matrix_bernstein_simplified` | Simplified form | Tropp Cor 1.5 |

**Module**: `Scaffold.Mathlib.LinearAlgebra.RandomMatrix.MatrixHoeffding`

| Axiom | Description | Source |
|-------|-------------|--------|
| `matrix_hoeffding` | Matrix Hoeffding inequality | Tropp Thm 1.4 |

### Gaussian Random Matrices

**Module**: `Scaffold.Mathlib.LinearAlgebra.RandomMatrix.GaussianSpectralNorm`

| Axiom | Description | Source |
|-------|-------------|--------|
| `gaussian_matrix_concentration` | Spectral norm of Gaussian matrices | Vershynin Thm 5.3.1 |
| `gaussian_matrix_expectation` | Expected spectral norm | Vershynin Thm 5.3.1 |

## See Also

- [Probability Concentration](probability_concentration.md) for scalar inequalities
- [Sources Index](../sources/) for detailed bibliographic information
