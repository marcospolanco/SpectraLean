# Scalar Concentration Inequalities

This directory contains axioms for concentration inequalities of scalar (real-valued) random variables.

## Modules

### `Subgaussian.lean`

Subgaussian random variables and their properties.

**Axioms**:
- `subgaussian_norm` - Orlicz norm definition
- `subgaussian_tail_bound` - P(|X| ≥ t) ≤ 2exp(-t²/(2K²))
- `subgaussian_moment_growth` - E[|X|^p]^(1/p) ≤ CK√p
- `subgaussian_linear_combination` - Closure under linear combinations
- `subgaussian_centering` - Centering preserves subgaussian property
- `hoeffding_lemma` - Bounded ⇒ subgaussian
- `subgaussian_sum_bound` - Sum of independent subgaussian

**Source**: Vershynin, High-Dimensional Probability, Chapter 2

### `Hoeffding.lean`

Hoeffding's inequality for bounded independent variables.

**Axioms**:
- `hoeffding_inequality` - General Hoeffding with varying bounds
- `hoeffding_iid` - IID version with common bound
- `hoeffding_empirical` - Empirical averages

**Sources**:
- Vershynin, High-Dimensional Probability, Theorem 2.2.2
- Boucheron-Lugosi-Massart, Concentration Inequalities, Theorem 2.8

### `Bernstein.lean`

Bernstein's inequality incorporating variance information.

**Axioms**:
- `bernstein_inequality` - General Bernstein with variance term
- `bernstein_bounded_variance` - Bounded variance form
- `bernstein_iid` - IID version

**Sources**:
- Vershynin, High-Dimensional Probability, Theorem 2.8.1
- Wainwright, High-Dimensional Statistics, Theorem 2.15

## Usage Patterns

### For Bounded Variables

```lean
-- Variables bounded by [a_i, b_i]
have h_sub := hoeffding_lemma (X i) (max |a_i| |b_i|)
-- Apply subgaussian concentration
```

### When Variance is Known

```lean
-- Small variance relative to bounds
apply bernstein_inequality
-- Provides tighter bound than Hoeffding
```

### For Linear Combinations

```lean
-- Weighted sums of subgaussian variables
have := subgaussian_linear_combination X a K
```

## Planned Additions

- `Subexponential.lean` - Subexponential random variables
- `Azuma.lean` - Martingale concentration (Azuma-Hoeffding)
- `Freedman.lean` - Martingale concentration with variance

## See Also

- [Index: Probability Concentration](../../../../../index/map/probability_concentration.md)
- [Sources](../../../../../index/sources/)
