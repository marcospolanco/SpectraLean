# Vershynin - High-Dimensional Probability

## Bibliographic Information

- **Author**: Roman Vershynin
- **Title**: High-Dimensional Probability: An Introduction with Applications in Data Science
- **Edition**: 2nd edition
- **Year**: 2018
- **Publisher**: Cambridge University Press
- **ISBN**: 978-1108415194

## Scope of Results Used

This textbook is a primary source for modern concentration inequalities. Scaffold uses results from:

- Chapter 2: Concentration inequalities (subgaussian, Hoeffding, Bernstein)
- Chapter 3: Random vectors in high dimensions (Gaussian concentration)
- Chapter 5: Random matrices (matrix concentration, spectral bounds)

## Theorem to Axiom Mapping

### Chapter 2: Concentration

| Theorem | Page | Lean Axiom | Module |
|---------|------|------------|--------|
| Definition 2.5.1 (Subgaussian norm) | 27 | `subgaussian_norm` | `Subgaussian.lean` |
| Theorem 2.1.1 (Tail bound) | 21 | `subgaussian_tail_bound` | `Subgaussian.lean` |
| Exercise 2.1.5 (Moment growth) | 24 | `subgaussian_moment_growth` | `Subgaussian.lean` |
| Lemma 2.5.2 (Linear combinations) | 28 | `subgaussian_linear_combination` | `Subgaussian.lean` |
| Exercise 2.5.5 (Centering) | 30 | `subgaussian_centering` | `Subgaussian.lean` |
| Lemma 2.6.2 (Hoeffding's lemma) | 32 | `hoeffding_lemma` | `Subgaussian.lean` |
| Theorem 2.6.3 (Sum bound) | 33 | `subgaussian_sum_bound` | `Subgaussian.lean` |
| Theorem 2.2.2 (Hoeffding's inequality) | 24 | `hoeffding_inequality` | `Hoeffding.lean` |
| Corollary 2.2.3 (IID Hoeffding) | 25 | `hoeffding_iid` | `Hoeffding.lean` |
| Theorem 2.8.1 (Bernstein's inequality) | 43 | `bernstein_inequality` | `Bernstein.lean` |
| Corollary 2.8.3 (IID Bernstein) | 45 | `bernstein_iid` | `Bernstein.lean` |

### Chapter 3: Random Vectors

| Theorem | Page | Lean Axiom | Module |
|---------|------|------------|--------|
| Theorem 3.1.1 (Gaussian concentration) | 60 | `gaussian_lipschitz_concentration` | TODO |

### Chapter 5: Random Matrices

| Theorem | Page | Lean Axiom | Module |
|---------|------|------------|--------|
| Theorem 5.1.1 (Matrix Hoeffding) | 180 | `matrix_hoeffding` | TODO |
| Theorem 5.2.2 (Matrix Bernstein) | 190 | `matrix_bernstein` | TODO |

## Notes

- This textbook is the primary reference for scalar concentration inequalities in Scaffold
- All Lean statements are faithful to the mathematical formulations
- Some results are simplified for clarity (e.g., universal constants may be abstracted)
