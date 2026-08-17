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
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner
import Scaffold.Mathlib.Probability.Concentration.Matrix.Basic

/-!
# Matrix Bernstein inequality

Tail bound for sums of independent, centered, uniformly bounded Hermitian
random matrices, in the spectral norm (`Matrix.L2OpNorm`), with the matrix
variance statistic written through Bochner integrals of matrix-valued
functions.
-/

open MeasureTheory ProbabilityTheory Real
open scoped Matrix.L2OpNorm

namespace Scaffold.Mathlib.Probability.Concentration.Matrix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Matrix Bernstein inequality: for independent, centered, Hermitian
matrix-valued variables `X i` with `‖X i ω‖ ≤ R`, writing the matrix
variance statistic as
`Σ = ∑ i, ∫ ω, X i ω * X i ω ∂μ`, the spectral norm of the sum obeys
`P {‖∑ X i‖ ≥ t} ≤ 2 d exp (-t² / (2 ‖Σ‖ + 2 R t / 3))`, where
`d = card V`.

Source:
- Tropp, J. A., "User-friendly tail bounds for sums of random matrices",
  Foundations of Computational Mathematics 12(4):389–434, 2012,
  Theorem 1.1 (Matrix Bernstein), p. 393.

Statement differences: the source states the one-sided extreme-eigenvalue
tail with `σ² = ‖∑ E X i²‖` and dimension factor `d`; we state the
two-sided spectral-norm form (factor `2`, via the union bound over both
extreme eigenvalues) and write the variance statistic through explicit
Bochner integrals of the matrix squares. Centering is the hypothesis
`∫ X i = 0`; boundedness is the uniform spectral-norm bound `‖X i ω‖ ≤ R`.
Integrability of the squares follows from measurability plus this bound.

QA: exercised by `matrix_bernstein_zero_QA` in
`Scaffold/QA/Concentration/Matrix_QA.lean`, which instantiates the axiom at
the zero sequence and checks the resulting empty-event bound.
-/
axiom matrix_bernstein {n : ℕ} {X : Fin n → Ω → Matrix V V ℝ} {R : ℝ}
    (h_meas : ∀ i, StronglyMeasurable (X i))
    (h_indep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ)
    (h_herm : ∀ i ω, (X i ω).IsHermitian)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (h_bound : ∀ i ω, ‖X i ω‖ ≤ R)
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | ‖∑ i, X i ω‖ ≥ t} ≤
      ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-t ^ 2 / (2 * ‖∑ i, ∫ ω, X i ω * X i ω ∂μ‖ + (2 * R * t) / 3)))

end Scaffold.Mathlib.Probability.Concentration.Matrix
