# Wainwright - High-Dimensional Statistics

## Bibliographic Information

- **Author**: Martin J. Wainwright
- **Title**: High-Dimensional Statistics: A Non-Asymptotic Viewpoint
- **Edition**: 1st edition
- **Year**: 2019
- **Publisher**: Cambridge University Press
- **ISBN**: 978-1108498029

## Scope of Results Used

This textbook provides alternative formulations and proofs of concentration inequalities. Scaffold uses results from:

- Chapter 2: Concentration inequalities (Bernstein, Chernoff bounds)
- Chapter 6: Subgaussian and subexponential random variables

## Theorem to Axiom Mapping

### Chapter 2: Concentration

| Theorem | Page | Lean Axiom | Module |
|---------|------|------------|---------|
| Theorem 2.15 (Bernstein's inequality) | 52 | `bernstein_bounded_variance` | `Scalar/Bernstein.lean` |
| Proposition 2.2 (Chernoff bound) | 35 | `chernoff_bound_generic` | TODO |

### Chapter 6: Subgaussian and Subexponential

| Theorem | Page | Lean Axiom | Module |
|---------|------|------------|--------|
| Definition 6.1 (Subgaussian) | 180 | `subgaussian_norm_alt` | TODO |
| Example 6.3 (Bounded variables) | 183 | Reference to `hoeffding_lemma` | `Subgaussian.lean` |

## Notes

- Wainwright's treatment emphasizes the connection between moment generating functions and concentration
- Provides alternative formulations that are sometimes more convenient for applications
- Used as a secondary reference to verify consistency across sources
