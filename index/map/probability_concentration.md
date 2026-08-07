# Probability Concentration Inequalities

This index maps Lean modules and axioms for concentration inequalities by topic area.

## Scalar Concentration

### Subgaussian Random Variables

**Module**: `Scaffold.Mathlib.Probability.Concentration.Scalar.Subgaussian`

| Axiom | Description | Source |
|-------|-------------|--------|
| `subgaussian_norm` | Orlicz norm definition | Vershynin Def 2.5.1 |
| `subgaussian_tail_bound` | P(\|X\| ≥ t) ≤ 2exp(-t²/(2K²)) | Vershynin Thm 2.1.1 |
| `subgaussian_moment_growth` | E[\|X\|^p]^(1/p) ≤ CK√p | Vershynin Ex 2.1.5 |
| `subgaussian_linear_combination` | Closure under linear combinations | Vershynin Lem 2.5.2 |
| `subgaussian_centering` | Centering preserves subgaussian property | Vershynin Ex 2.5.5 |
| `hoeffding_lemma` | Bounded ⇒ subgaussian | Vershynin Lem 2.6.2 |
| `subgaussian_sum_bound` | Sum of independent subgaussian | Vershynin Thm 2.6.3 |

### Hoeffding's Inequality

**Module**: `Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding`

| Axiom | Description | Source |
|-------|-------------|--------|
| `hoeffding_inequality` | Sums of bounded independent variables | Vershynin Thm 2.2.2 |
| `hoeffding_iid` | IID bounded variables | Vershynin Cor 2.2.3 |
| `hoeffding_empirical` | Empirical averages | Boucheron-Lugosi-Massart Thm 2.8 |

### Bernstein's Inequality

**Module**: `Scaffold.Mathlib.Probability.Concentration.Scalar.Bernstein`

| Axiom | Description | Source |
|-------|-------------|--------|
| `bernstein_inequality` | Tail bound with variance | Vershynin Thm 2.8.1 |
| `bernstein_bounded_variance` | Bounded variance form | Wainwright Thm 2.15 |
| `bernstein_iid` | IID variance form | Vershynin Cor 2.8.3 |

## Martingale Concentration

### Azuma-Hoeffding

**Module**: TODO (planned for v0.2.0)

| Axiom | Description | Source |
|-------|-------------|--------|
| `azuma_inequality` | Martingale tail bound | Standard reference |

### Freedman's Inequality

**Module**: TODO (planned for v0.2.0)

| Axiom | Description | Source |
|-------|-------------|--------|
| `freedman_inequality` | Martingale with variance process | Freedman (1975) |

## Matrix Concentration

### Matrix Hoeffding

**Module**: TODO (planned for v0.2.0)

| Axiom | Description | Source |
|-------|-------------|--------|
| `matrix_hoeffding` | Bounded self-adjoint matrices | Tropp Thm 1.4 |

### Matrix Bernstein

**Module**: TODO (planned for v0.2.0)

| Axiom | Description | Source |
|-------|-------------|--------|
| `matrix_bernstein` | Matrix Bernstein inequality | Tropp Thm 1.1 |
| `matrix_bernstein_simplified` | Simplified form | Tropp Cor 1.5 |

### Gaussian Random Matrices

**Module**: TODO (planned for v0.2.0)

| Axiom | Description | Source |
|-------|-------------|--------|
| `gaussian_matrix_concentration` | Gaussian matrix spectral norm | Vershynin Thm 5.3.1 |

## Usage Patterns

### For Bounded Variables

1. Use `hoeffding_lemma` to show subgaussian
2. Apply `subgaussian_sum_bound` or `hoeffding_inequality`

### For Variance-Dependent Bounds

1. Use `bernstein_inequality` when variance is small
2. Provides tighter bounds than Hoeffding when Var(X) ≪ bound²

### For Martingales

1. Azuma for bounded differences
2. Freedman when variance process is available

## See Also

- [Sources Index](../sources/) for detailed bibliographic information
- [Load-bearing Axioms](../load_bearing_axioms.md) for critical dependencies
