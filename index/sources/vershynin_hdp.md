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
| Lemma 2.6.2 (Hoeffding's lemma) | 32 | `hoeffding_lemma` (**proved theorem since 2026-08-30** — the pointwise-collapse retirement, `proposals/retire-hoeffding-lemma-pointwise-collapse.md`: at the `√6·a` constant the defining set sees only the bound and the mass, so the sharper companion `subgaussianNorm_le_of_bounded` (`≤ a/√(log 2)`, no centering) implies the admitted shape at the statement unchanged; repaired 2026-08-28 when the pre-repair `≤ a` shape was found materially false, two refutations in QA) | `Scalar/Subgaussian.lean` |
| Theorem 2.2.2 (Hoeffding's inequality) | 24 | `hoeffding_inequality` (**proved theorem since 2026-08-30** — the Hoeffding retirement, `proposals/prove-hoeffding-inequality-mgf.md`) | `Scalar/Hoeffding.lean` |
| Corollary 2.2.3 (IID Hoeffding) | 25 | `hoeffding_iid` (proved from `hoeffding_inequality`) | `Scalar/Hoeffding.lean` |
| Theorem 2.8.1 (Bernstein's inequality) | 43 | `bernstein_inequality` (**proved theorem since 2026-08-30** — the repair-and-retirement, Errata §8: the admitted form's *uncentered* bound hypothesis materially understated the Bennett price; repaired to the source's centered bound and proved by the local Bennett MGF engine) | `Scalar/Bernstein.lean` |
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

### Chapter 4: Matrix Perturbation Theory (route reference for a *proved* theorem)

Mapped 2026-08-24 to a proved declaration: Thm 4.1.15–4.1.16 are the
textbook packaging of the commutator/shift proof technique behind
`Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.`
`l2OpNorm_bandProjector_mul_bandProjector_le_of_lt` / `_of_gt`
(`Perturbation/BandDavisKahan.lean`, proposal `proposals/band-davis-kahan.md`,
backlog item 9): the bounded-window Davis–Kahan product bound
`‖Q * P‖ ≤ ‖A − B‖ / δ` for δ-separated band projectors — **a proved
theorem, not an axiom; the locator is route provenance only** (carried
with the standing caveat that locator numbers are to be confirmed
against a physical or publisher copy, not invented here). The chapter
is still *not* a source for `davis_kahan_sin_theta` itself — the
half-line threshold form that statement uses is the Davis & Kahan 1970
/ Yu–Wang–Samworth 2015 Theorem 1 route
(`index/sources/davis_kahan_1970.md`), proved since 2026-08-21 by the
Duhamel route; the two are genuinely different theorems and neither
substitutes for the other (see the survey record in
`proposals/discharge-perturbation-axioms.md`).

## Notes

- This textbook is the primary reference for scalar concentration inequalities in Scaffold
- All Lean statements are faithful to the mathematical formulations
- Some results are simplified for clarity (e.g., universal constants may be abstracted)
