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
# Matrix Hoeffding inequality

Tail bound for sums of independent, centered, Hermitian random matrices
whose squares are dominated in the semidefinite order, in the spectral
norm (`Matrix.L2OpNorm`).

This is the matrix concentration statement consumed by Scaffold's
event-stream frontier: bounded per-event Laplacian perturbations with
independent events. Repaired 2026-08-30 with the centering clause
`h_mean` (Errata §9): without it the statement is refuted by the
deterministic uncentered family — see the axiom's statement-history note
and `old_matrix_hoeffding_refuted_uncentered_QA` in
`Scaffold/QA/Concentration/Matrix_QA.lean`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped Matrix.L2OpNorm

namespace Scaffold.Mathlib.Probability.Concentration.Matrix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Matrix Hoeffding inequality: for independent, centered, Hermitian
matrix-valued variables `X i` with `X i ω ^ 2 ⪯ A i ^ 2` in the semidefinite
order (written `Matrix.PosSemidef (A i * A i - X i ω * X i ω)`), the spectral
norm of the sum obeys
`P {‖∑ X i‖ ≥ t} ≤ 2 d exp (-t² / (2 ‖∑ A i²‖))`, where
`d = card V`.

Source:
- Tropp, J. A., "User-friendly tail bounds for sums of random matrices",
  Foundations of Computational Mathematics 12(4):389–434, 2012,
  Theorem 1.4 (Matrix Hoeffding), p. 398.

Statement differences: the source states the one-sided extreme-eigenvalue
tail `P {λ_max (∑ X i) ≥ t} ≤ d exp (-σ² ...)` with the variance statistic
`σ² = ‖∑ A i²‖`; we state the two-sided spectral-norm form, applying the
source bound to `∑ X i` and `∑ -X i` and using the union bound, which
introduces the factor `2`. The semidefinite order is Mathlib's
`Matrix.PosSemidef` and the norm is the operator ℓ² ("spectral") norm
`Matrix.L2OpNorm`. Centering is the hypothesis
`h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0`, the same clause idiom as the sibling
`matrix_bernstein`; the semidefinite domination `X i ω² ⪯ A i ²` alone
carries no information about the mean.

Statement history: repaired in place 2026-08-28 (run
`20260828T090419Z-run-1`, Step 0 of
`proposals/matrix-hoeffding-spectral-gap-estimation.md`): the pre-repair
statement had no nondegeneracy hypothesis and was materially false at the
corner `Fintype.card V = 0`, `t = 0` — the tail event `{ω | ‖∑ X i ω‖ ≥ 0}`
is all of `Ω` (nonnegativity of the norm), so a probability measure gives
`1`, while the dimension prefactor makes the bound `2 · 0 · exp … = 0`;
the instantiated axiom reads `1 ≤ 0`, refuted in hypothesis form as
`old_matrix_hoeffding_refuted_fin0_QA` in
`Scaffold/QA/Concentration/Matrix_QA.lean`. The cited Tropp theorem is
stated for dimension-`d` matrices, carrying the implicit `d ≥ 1` of
nonempty matrix dimensions; the `[Nonempty V]` guard makes that
assumption explicit. At `t = 0` the repaired statement is honest on
nonempty `V`: `(1 : ℝ≥0∞) ≤ 2 d` (`two_card_bound_honest_QA`, same file).

Repaired in place again 2026-08-30 (run `20260830T183850Z-run-1`,
Errata §9, `proposals/repair-matrix-hoeffding-centering.md`): the
statement had no centering clause — an earlier note here even claimed
"the source needs no centering hypothesis" — and was materially false in
hypothesis shape: the deterministic uncentered family `X i ≡ 1` (with
`A i ≡ 1`) satisfies the semidefinite domination at equality and every
other hypothesis, yet at `V = Fin 1`, `n = 2`, `t = 2` the tail event is
all of `Ω` against the bound `2 · exp (−1) < 1`; refuted in hypothesis
form as `old_matrix_hoeffding_refuted_uncentered_QA` (same QA file),
with every old hypothesis clause separately proved at the fixture
(`ones_family_old_clauses_QA`) and the repaired clause's exclusion
proved (`ones_mean_ne_zero_QA`: the refuting family integrates to
`1 ≠ 0`). Whatever hypothesis set the cited source carries (centering,
or a distributional-symmetry condition implying it), it must exclude
exactly this uncentered deterministic family — the symmetrization step
in the source's own framework requires centered summands — so the
centering clause is the encoding that keeps the deterministic centered
designs (the edge-perturbation window family) instantiable; the
locator-level check against a physical copy of the source remains an
open item per the standing locator rule.

Replacement path: proved locally by completing the matrix master-bound
retirement route (`proposals/matrix-master-bound-first-slice.md`): the
delivered `matrix_master_bound` (Tropp Proposition 3.1, proved,
`Matrix/MasterBound.lean`) already supplies the Laplace-transform step
every matrix concentration proof consumes; the remaining step is the
Lieb-class sum-MGF bound (Tropp Theorem 6.1 via Lieb's concavity
theorem), the route's gated Step 2. Alternatively, upstream replacement
when Mathlib gains an equivalent matrix Hoeffding (adapter per
`docs/2_ARCHITECTURE.md` §9).

QA: exercised by `matrix_hoeffding_zero_QA` in
`Scaffold/QA/Concentration/Matrix_QA.lean`, which instantiates the axiom at
the zero sequence and checks the resulting empty-event bound. -/
axiom matrix_hoeffding {n : ℕ} [Nonempty V] {X : Fin n → Ω → Matrix V V ℝ}
    {A : Fin n → Matrix V V ℝ}
    (h_meas : ∀ i, StronglyMeasurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n =>
      (inferInstance : MeasurableSpace (Matrix V V ℝ))) X μ)
    (h_herm : ∀ i ω, (X i ω).IsHermitian)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (h_bound : ∀ i ω, Matrix.PosSemidef (A i * A i - X i ω * X i ω))
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | ‖∑ i, X i ω‖ ≥ t} ≤
      ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-t ^ 2 / (2 * ‖∑ i, A i * A i‖)))

end Scaffold.Mathlib.Probability.Concentration.Matrix
