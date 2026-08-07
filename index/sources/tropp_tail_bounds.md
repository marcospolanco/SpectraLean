# Tropp - User-Friendly Tail Bounds for Sums of Random Matrices

## Bibliographic Information

- **Author**: Joel A. Tropp
- **Title**: User-Friendly Tail Bounds for Sums of Random Matrices
- **Journal**: Foundations of Computational Mathematics
- **Year**: 2012
- **Volume**: 12
- **Issue**: 4
- **Pages**: 389-434
- **DOI**: 10.1007/s10208-011-9099-z

## Scope of Results Used

This paper is the primary source for matrix concentration inequalities in Scaffold. Results include:

- Matrix Bernstein inequality
- Matrix Hoeffding inequality
- Related matrix concentration tools

## Theorem to Axiom Mapping

### Main Results

| Theorem | Page | Lean Axiom | Module |
|---------|------|------------|--------|
| Theorem 1.1 (Matrix Bernstein) | 393 | `matrix_bernstein` | TODO |
| Theorem 1.4 (Matrix Hoeffding) | 398 | `matrix_hoeffding` | TODO |
| Corollary 1.5 (Simplified Bernstein) | 399 | `matrix_bernstein_simplified` | TODO |

## Notes

- Tropp's matrix Bernstein inequality is the standard reference for matrix concentration
- The paper provides both tail bound and expectation forms
- Scaffold uses the tail bound form for consistency with scalar inequalities
- All matrix inequalities are stated for self-adjoint random matrices
