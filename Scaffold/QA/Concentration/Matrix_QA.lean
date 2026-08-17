/-
  Matrix_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.Probability.Concentration.Matrix.*`:
  the matrix Hoeffding and Bernstein tail bounds and the matrix
  Azuma–Hoeffding inequality for martingale difference sequences.

  Each axiom is instantiated at a degenerate constant-zero sequence, so
  the hypothesis interface (strong measurability, independence of
  constants at the matrix codomain, Hermitianity, semidefinite
  domination, the `MatrixMDS` structure fields) is discharged
  constructively, and the event side evaluates exactly.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not prove
  the axioms; it checks their interfaces and degenerate cases.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Probability.Concentration.Matrix.Hoeffding
import Scaffold.Mathlib.Probability.Concentration.Matrix.Bernstein
import Scaffold.Mathlib.Probability.Concentration.Matrix.Azuma

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Probability.Concentration.Matrix.QA

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Independence at the matrix codomain
-/

/-- Constant matrix-valued variables are independent of anything under a
probability measure: the generated σ-algebra is trivial. This exercises
the product σ-algebra instance on `Matrix V V ℝ` at the boundary the
matrix axioms consume. -/
theorem indepFun_const_matrix_QA (A : Matrix V V ℝ) (Y : Ω → Matrix V V ℝ) :
    IndepFun (fun _ => A) Y μ := by
  rw [IndepFun_iff_Indep, MeasurableSpace.comap_const]
  exact indep_bot_left _

/-!
## Matrix Hoeffding interface
-/

/-- Matrix Hoeffding instantiated at the constant-zero family with zero
dominators `A i = 0`: all hypotheses are discharged constructively
(`PosSemidef.zero` for the semidefinite order, `isHermitian_zero`,
`stronglyMeasurable_const`, constant independence). -/
theorem matrix_hoeffding_zero_QA {n : ℕ} (t : ℝ) (ht : 0 < t) :
    μ {ω : Ω | ‖∑ i : Fin n, (0 : Matrix V V ℝ)‖ ≥ t} ≤
      ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-(t ^ 2) / (2 * ‖∑ i : Fin n, (0 : Matrix V V ℝ) * 0‖))) := by
  exact matrix_hoeffding (X := fun _ _ => 0) (A := fun _ => 0)
    (fun i => stronglyMeasurable_const) (fun i j _ => indepFun_const_matrix_QA 0 _)
    (fun i ω => Matrix.isHermitian_zero) (fun i ω => by simpa using Matrix.PosSemidef.zero)
    t ht.le

/-- The matrix-Hoeffding zero-family event is empty, so its measure is
exactly `0`. -/
theorem matrix_hoeffding_zero_event_QA {n : ℕ} {t : ℝ} (ht : 0 < t) :
    μ {ω : Ω | ‖∑ i : Fin n, (0 : Matrix V V ℝ)‖ ≥ t} = 0 := by
  have hempty : {ω : Ω | ‖∑ i : Fin n, (0 : Matrix V V ℝ)‖ ≥ t} = ∅ := by
    ext ω
    simp only [Finset.sum_const_zero, norm_zero]
    simp [ht.not_le]
  rw [hempty, measure_empty]

/-!
## Matrix Bernstein interface
-/

/-- Matrix Bernstein instantiated at the constant-zero family with bound
`R = 0`: the matrix variance statistic specializes to `0`. -/
theorem matrix_bernstein_zero_QA {n : ℕ} (t : ℝ) (ht : 0 < t) :
    μ {ω : Ω | ‖∑ i : Fin n, (0 : Matrix V V ℝ)‖ ≥ t} ≤
      ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-(t ^ 2) / (2 * ‖∑ i : Fin n, ∫ ω : Ω,
          (0 : Matrix V V ℝ) * 0 ∂μ‖ + (2 * 0 * t) / 3))) :=
  matrix_bernstein (X := fun _ _ => 0) (R := 0)
    (fun i => stronglyMeasurable_const) (fun i j _ => indepFun_const_matrix_QA 0 _)
    (fun i ω => Matrix.isHermitian_zero) (fun i => by simp)
    (fun i ω => by simp) t ht.le

/-!
## Matrix Azuma interface
-/

/-- The constant-zero difference sequence is a `MatrixMDS` with bound
`R = 0`: adaptedness holds because every σ-algebra dominates the trivial
one, the conditional means vanish on every past event, and the norm bound
is `‖0‖ ≤ 0`. -/
def zeroMatrixMDS : MatrixMDS (V := V) μ where
  R := 0
  X := fun _ _ => 0
  adapted := fun k =>
    (stronglyMeasurable_bot_iff (f := fun _ => (0 : Matrix V V ℝ))).2 ⟨0, rfl⟩ |>.mono bot_le
  cond_mean_zero := fun k S _ => by simp
  norm_bound := fun k ω => by simp

/-- Matrix Azuma instantiated at the constant-zero difference sequence:
all structure fields come from `zeroMatrixMDS`, so the axiom's martingale
interface is discharged constructively. The denominator carries the
cumulative variance factor `m · 0² = 0` (junk division), matching the
repaired statement. -/
theorem matrix_azuma_zero_QA (m : ℕ) (t : ℝ) (ht : 0 < t) :
    μ {ω : Ω | ‖∑ k in Finset.range m, (0 : Matrix V V ℝ)‖ ≥ t} ≤
      ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-(t ^ 2) / (8 * (m : ℝ) * (0 : ℝ) ^ 2))) :=
  matrix_azuma_hoeffding m zeroMatrixMDS t ht.le

/-- The matrix-Azuma zero-sequence event is empty, so its measure is
exactly `0`. -/
theorem matrix_azuma_zero_event_QA {m : ℕ} {t : ℝ} (ht : 0 < t) :
    μ {ω : Ω | ‖∑ k in Finset.range m, (0 : Matrix V V ℝ)‖ ≥ t} = 0 := by
  have hempty : {ω : Ω | ‖∑ k in Finset.range m, (0 : Matrix V V ℝ)‖ ≥ t} = ∅ := by
    ext ω
    simp only [Finset.sum_const_zero, norm_zero]
    simp [ht.not_le]
  rw [hempty, measure_empty]

end Scaffold.Mathlib.Probability.Concentration.Matrix.QA
