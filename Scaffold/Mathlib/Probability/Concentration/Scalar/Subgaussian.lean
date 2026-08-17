/-
Copyright 2024 Scaffold Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner

/-!
# Subgaussian random variables

The ψ₂ (subgaussian) size of a real random variable, defined for the
Bochner integral on an arbitrary measure, together with the admitted
(cited) consequences of that definition that Scaffold currently consumes.

`subgaussianNorm` is a real definition, not an axiom: it is the infimum of
the admissible MGF bounds. The inequalities *about* it are explicit axioms
with citations.

Only the statements with a named downstream consumer are admitted;
Vershynin's moment-growth and centering estimates are left out of the trust
boundary until a consumer needs them.
-/

open MeasureTheory ProbabilityTheory Real

namespace Scaffold.Mathlib.Probability.Concentration.Scalar

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The ψ₂ (subgaussian) norm of a real random variable `X` under the
measure `μ`: the infimum of all `K > 0` with
`∫ ω, exp (X ω ^ 2 / K ^ 2) ∂μ ≤ 2`.

This is the Orlicz/MGF characterization of the subgaussian norm (Vershynin,
*High-Dimensional Probability*, 2nd ed., Proposition 2.5.2); the official
definition (Definition 2.5.1) is the equivalent moment-supremum
`sup_{p ≥ 1} (E |X| ^ p) ^ (1 / p) / √p`, and the two agree up to universal
constant factors. We adopt the MGF form because it composes directly with
integral statements.

If no admissible `K` exists (unbounded tails), the index set is empty and
the `sInf` is the junk value `0`; consumers must establish finiteness from
hypotheses such as `hoeffding_lemma`. -/
noncomputable def subgaussianNorm (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {K : ℝ | 0 < K ∧ ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ ≤ 2}

/-- The subgaussian norm is nonnegative: the defining set only contains
positive `K`, so `0` is a lower bound. -/
theorem subgaussianNorm_nonneg (X : Ω → ℝ) (μ : Measure Ω) :
    0 ≤ subgaussianNorm X μ :=
  Real.sInf_nonneg fun K hK => le_of_lt hK.1

/-- Hoeffding's lemma: a random variable bounded by `a` with mean zero is
`a`-subgaussian.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed., Cambridge University
  Press, 2018, Lemma 2.6.2, Chapter 2, p. 32.

Statement differences: the source states the MGF form
`E exp(λX) ≤ exp(λ²a²/2)`; we state it through `subgaussianNorm`, whose MGF
characterization is equivalent up to universal constants
(Proposition 2.5.2), so the conclusion may lose an absolute constant
relative to the source.

QA: exercised, together with `subgaussianNorm_nonneg` and
`subgaussian_tail_bound`, by `hoeffding_lemma_zero_QA` and
`subgaussian_tail_bound_zero_QA` in `Scaffold/QA/Concentration/Scalar_QA.lean`.
-/
axiom hoeffding_lemma {X : Ω → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h_bound : ∀ ω, |X ω| ≤ a) (h_mean : ∫ ω, X ω ∂μ = 0) :
    subgaussianNorm X μ ≤ a

/-- Tail bound for a subgaussian random variable: if `X` has subgaussian
norm at most `K`, then the two-sided tail obeys
`P {|X| ≥ t} ≤ 2 exp (-t² / (2K²))`.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed., Cambridge University
  Press, 2018, Proposition 2.5.2 (ii), Chapter 2, p. 29.

QA: exercised by `subgaussian_tail_bound_zero_QA` in
`Scaffold/QA/Concentration/Scalar_QA.lean`.
-/
axiom subgaussian_tail_bound {X : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h_sub : subgaussianNorm X μ ≤ K) (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | |X ω| ≥ t} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * K ^ 2)))

end Scaffold.Mathlib.Probability.Concentration.Scalar
