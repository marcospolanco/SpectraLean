# Load-bearing Axioms

This document tracks axioms that are critical dependencies for many downstream results.

## Definition

A **load-bearing axiom** is an axiom that:

1. Many other axioms or theorems depend on (directly or transitively)
2. Would be high-impact to formalize in mathlib
3. Represents a significant mathematical result

## Current Load-bearing Axioms

### Scalar Concentration

#### `subgaussian_tail_bound` (proved 2026-08-22 — no longer an axiom)
- **Source**: Vershynin, High-Dimensional Probability, Proposition 2.5.2 (ii)
- **Impact**: Foundation for subgaussian concentration
- **Dependencies**: None currently; the proof is Markov's inequality at the stated moment
- **Formalization priority**: closed (retired from the axiom boundary)

#### `hoeffding_lemma`
- **Source**: Vershynin, High-Dimensional Probability, Lemma 2.6.2
- **Impact**: Connects boundedness to the subgaussian property (probability measure; conclusion `≤ √6·a` — repaired 2026-08-28, the pre-repair shape was materially false per `proposals/audit-scalar-concentration-integrability-hazard.md`)
- **Dependencies**: Retired to a proved theorem 2026-08-30 (`proposals/retire-hoeffding-lemma-pointwise-collapse.md`) — the pointwise-collapse route through the sharper companion `subgaussianNorm_le_of_bounded` (`≤ a/√(log 2)`, no centering); former QA contact (`subgaussian_norm_zero_QA`, `hoeffding_lemma_rademacher_QA`) now hard crust
- **Formalization priority**: closed (retired from the axiom boundary)

#### `bernstein_inequality`
- **Source**: Vershynin, High-Dimensional Probability, Theorem 2.8.1
- **Impact**: Provides variance-dependent bounds (tighter than Hoeffding)
- **Dependencies**: Retired to a proved theorem 2026-08-30 (Errata §8, `proposals/repair-and-retire-bernstein-pair.md`) — repaired to the source-faithful centered bound and proved by the local Bennett MGF engine
- **Formalization priority**: closed (retired from the axiom boundary)

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

1. **HIGH**: matrix_bernstein, matrix_hoeffding, matrix_azuma_hoeffding, perron_frobenius, primitive_power_tendsto (the five remaining admitted axioms — every one has theorem consumers; the scalar family is fully proved: `subgaussian_tail_bound` retired 2026-08-22, `hoeffding_inequality`/`hoeffding_empirical` and `bernstein_inequality`/`bernstein_bounded_variance` and `hoeffding_lemma` retired 2026-08-30)
3. **LOW**: Specialized corollaries and variants

## Tracking

This list will be updated as new axioms are added. Maintainers should review this list quarterly.

## See Also

- [Architecture and axiom policy](../docs/2_ARCHITECTURE.md) for admission and migration rules
