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

| Theorem | Page | Lean Declaration | Module |
|---------|------|------------|---------|
| Definition 2.5.1 / Prop. 2.5.2 (Subgaussian norm) | 27/29 | `subgaussianNorm` (real definition) | `Scalar/Subgaussian.lean` |
| Proposition 2.5.2 (ii) (Tail bound) | 29 | `subgaussian_tail_bound` (**proved 2026-08-22**; repaired hypotheses — the moment stated integrably at `K`, conclusion unchanged; the former axiom shape was materially false, refuted in QA at `3 • δ₀`) | `Scalar/Subgaussian.lean` |
| Lemma 2.6.2 (Hoeffding's lemma) | 32 | `hoeffding_lemma` (axiom) | `Scalar/Subgaussian.lean` |
| Theorem 2.2.2 (Hoeffding's inequality) | 24 | `hoeffding_inequality` (axiom) | `Scalar/Hoeffding.lean` |
| Corollary 2.2.3 (IID Hoeffding) | 25 | `hoeffding_iid` (proved from `hoeffding_inequality`) | `Scalar/Hoeffding.lean` |
| Theorem 2.8.1 (Bernstein's inequality) | 43 | `bernstein_inequality` (axiom) | `Scalar/Bernstein.lean` |
| Corollary 2.8.3 (IID Bernstein) | 45 | `bernstein_iid` (proved from `bernstein_inequality`) | `Scalar/Bernstein.lean` |

Statements from Chapter 2 that were previously admitted but have no named
downstream consumer (`subgaussian_moment_growth` from Exercise 2.1.5,
`subgaussian_linear_combination` from Lemma 2.5.2,
`subgaussian_centering` from Exercise 2.5.5, and `subgaussian_sum_bound`
from Theorem 2.6.3) were removed from the axiom boundary in the 2026-08-17
concentration repair; they can be re-admitted when a consumer needs them.

### Chapter 5: Random Matrices

Matrix concentration from this chapter is covered through the Tropp 2012
source (see `tropp_tail_bounds.md`); the Chapter 5 matrix statements are
not separately admitted.

### Chapter 4: Matrix Perturbation Theory (route reference, not an axiom source)

Not currently mapped to any Scaffold declaration. Recorded 2026-08-21 as
a *route reference* discovered during the Davis–Kahan Step-0/1 survey
(`proposals/discharge-perturbation-axioms.md`): Thm 4.1.15
(eigenvector-angle Davis–Kahan) and Thm 4.1.16 (spectral-projection
Davis–Kahan) are a textbook packaging of a commutator/shift proof
technique, distinct from the Davis & Kahan 1970 / Yu–Wang–Samworth 2015
route already cited for `davis_kahan_sin_theta`
(`index/sources/davis_kahan_1970.md`). The technique proves a
*bounded-window* Davis–Kahan statement, not the half-line threshold form
Scaffold's axiom states — see the survey record and
`docs/6_SGT_BACKLOG.md` item 9 for the precise scope and why it does not
substitute for the existing axiom's retirement. Do not cite this chapter
for `davis_kahan_sin_theta` itself; it would be the source for a future,
separate band-form theorem only.

## Notes

- This textbook is the primary reference for scalar concentration inequalities in Scaffold
- All Lean statements are faithful to the mathematical formulations
- Some results are simplified for clarity (e.g., universal constants may be abstracted)
