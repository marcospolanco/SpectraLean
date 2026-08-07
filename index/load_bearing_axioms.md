# Load-bearing Axioms

This document tracks axioms that are critical dependencies for many downstream results.

## Definition

A **load-bearing axiom** is an axiom that:

1. Many other axioms or theorems depend on (directly or transitively)
2. Would be high-impact to formalize in mathlib
3. Represents a significant mathematical result

## Current Load-bearing Axioms

### Scalar Concentration

#### `subgaussian_tail_bound`
- **Source**: Vershynin, High-Dimensional Probability, Theorem 2.1.1
- **Impact**: Foundation for all subgaussian concentration
- **Dependencies**: Used by most scalar concentration inequalities
- **Formalization priority**: HIGH

#### `hoeffding_lemma`
- **Source**: Vershynin, High-Dimensional Probability, Lemma 2.6.2
- **Impact**: Connects boundedness to subgaussian property
- **Dependencies**: Used by Hoeffding and Bernstein inequalities
- **Formalization priority**: HIGH

#### `bernstein_inequality`
- **Source**: Vershynin, High-Dimensional Probability, Theorem 2.8.1
- **Impact**: Provides variance-dependent bounds (tighter than Hoeffding)
- **Dependencies**: Used throughout ML theory and statistics
- **Formalization priority**: HIGH

### Matrix Concentration

#### `matrix_bernstein`
- **Source**: Tropp, User-Friendly Tail Bounds, Theorem 1.1
- **Impact**: Foundation for matrix concentration
- **Dependencies**: Will be used by all matrix concentration results
- **Formalization priority**: HIGH

### Perturbation Theory

#### `davis_kahan_sin_theta`
- **Source**: Stewart, Matrix Algorithms, Volume II
- **Impact**: Foundation for eigenvector perturbation
- **Dependencies**: Used by spectral clustering, PCA analysis
- **Formalization priority**: MEDIUM

## Impact Assessment

### If Formalized in Mathlib

1. **Immediate benefits**:
   - Scaffold can re-export mathlib versions
   - Reduced trust base (axiom becomes theorem)
   - Improved consistency with mathlib

2. **Migration effort**:
   - Minimal if names match exactly
   - Moderate if signatures differ
   - Significant if mathematical formulation differs

### Formalization Priority Ranking

1. **HIGH**: subgaussian_tail_bound, hoeffding_lemma, bernstein_inequality, matrix_bernstein
2. **MEDIUM**: davis_kahan_sin_theta, matrix_hoeffding
3. **LOW**: Specialized corollaries and variants

## Tracking

This list will be updated as new axioms are added. Maintainers should review this list quarterly.

## See Also

- [Axiom Policy](../../governance/AXIOM_POLICY.md) for axiom guidelines
- [Deprecation Policy](../../governance/DEPRECATION_POLICY.md) for migration process
