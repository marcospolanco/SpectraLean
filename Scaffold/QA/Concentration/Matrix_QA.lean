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
theorem matrix_hoeffding_zero_QA [Nonempty V] {n : ℕ} (t : ℝ) (ht : 0 < t) :
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
theorem matrix_bernstein_zero_QA [Nonempty V] {n : ℕ} (t : ℝ) (ht : 0 < t) :
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
theorem matrix_azuma_zero_QA [Nonempty V] (m : ℕ) (t : ℝ) (ht : 0 < t) :
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

/-!
## The degenerate-dimension refutations (2026-08-28 repair records)

Each of the three matrix concentration axioms was repaired on 2026-08-28
by adding the `[Nonempty V]` guard (run `20260828T090419Z-run-1`, Step 0
of `proposals/matrix-hoeffding-spectral-gap-estimation.md`). The lemmas
below refute the *pre-repair shapes in hypothesis form*: the hypothesis is
exactly the old axiom instantiated at the corner `V = Fin 0`, `t = 0`, the
constant-zero family (every old hypothesis satisfied there — measurability
and Hermitianity of constants, independence of constants, the semidefinite
and norm bounds at zero), and from it `False` follows: the tail event
`{ω | ‖0‖ ≥ 0}` is all of `Ω` by nonnegativity of the norm, so a
probability measure gives `1`, while the dimension prefactor
`2 · (card (Fin 0) : ℝ) · exp … = 0` regardless of the (junk-free)
denominator. This is the same failure class as the pre-repair
`cheeger_lower_bound` shape (`1/2 ≤ 0` on `K₂`): an axiom inconsistent at
a degenerate corner makes every conditional theorem vacuous.
-/

/-- The pre-repair `matrix_hoeffding` shape is refuted at
`V = Fin 0`, `t = 0`, the zero family: `1 ≤ 0`. -/
theorem old_matrix_hoeffding_refuted_fin0_QA {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : μ {_ω : Ω | ‖∑ _i : Fin 1, (0 : Matrix (Fin 0) (Fin 0) ℝ)‖ ≥ (0 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 0) : ℝ) *
        Real.exp (-(0 : ℝ) ^ 2 / (2 * ‖(0 : Matrix (Fin 0) (Fin 0) ℝ)‖)))) :
    False := by
  have hev : {_ω : Ω | ‖∑ _i : Fin 1, (0 : Matrix (Fin 0) (Fin 0) ℝ)‖ ≥ (0 : ℝ)}
      = Set.univ := by
    ext _ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, ge_iff_le]
    exact iff_of_true (norm_nonneg (∑ _i : Fin 1, (0 : Matrix (Fin 0) (Fin 0) ℝ)))
      trivial
  rw [hev] at h
  have huniv : μ Set.univ = 1 := measure_univ
  rw [huniv] at h
  have hc : (Fintype.card (Fin 0) : ℝ) = 0 := by norm_num [Fintype.card_fin]
  rw [hc, mul_zero, zero_mul, ENNReal.ofReal_zero] at h
  exact absurd h (not_le.mpr zero_lt_one)

/-- The pre-repair `matrix_bernstein` shape is refuted at the same corner
(zero family, `R = 0`, `t = 0`): `1 ≤ 0`. -/
theorem old_matrix_bernstein_refuted_fin0_QA {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : μ {_ω : Ω | ‖∑ _i : Fin 1, (0 : Matrix (Fin 0) (Fin 0) ℝ)‖ ≥ (0 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 0) : ℝ) *
        Real.exp (-(0 : ℝ) ^ 2 / (2 * ‖∑ _i : Fin 1,
          ∫ _ω : Ω, (0 : Matrix (Fin 0) (Fin 0) ℝ) * 0 ∂μ‖
          + (2 * 0 * (0 : ℝ)) / 3)))) :
    False := by
  have hev : {_ω : Ω | ‖∑ _i : Fin 1, (0 : Matrix (Fin 0) (Fin 0) ℝ)‖ ≥ (0 : ℝ)}
      = Set.univ := by
    ext _ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, ge_iff_le]
    exact iff_of_true (norm_nonneg (∑ _i : Fin 1, (0 : Matrix (Fin 0) (Fin 0) ℝ)))
      trivial
  rw [hev] at h
  have huniv : μ Set.univ = 1 := measure_univ
  rw [huniv] at h
  have hc : (Fintype.card (Fin 0) : ℝ) = 0 := by norm_num [Fintype.card_fin]
  rw [hc, mul_zero, zero_mul, ENNReal.ofReal_zero] at h
  exact absurd h (not_le.mpr zero_lt_one)

/-- The pre-repair `matrix_azuma_hoeffding` shape is refuted at the same
corner (zero difference sequence, `m = 1`, `t = 0`): `1 ≤ 0`. -/
theorem old_matrix_azuma_refuted_fin0_QA {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : μ {_ω : Ω | ‖∑ _k in Finset.range 1, (0 : Matrix (Fin 0) (Fin 0) ℝ)‖
        ≥ (0 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 0) : ℝ) *
        Real.exp (-(0 : ℝ) ^ 2 / (8 * (1 : ℝ) * (0 : ℝ) ^ 2)))) :
    False := by
  have hev : {_ω : Ω | ‖∑ _k in Finset.range 1, (0 : Matrix (Fin 0) (Fin 0) ℝ)‖
        ≥ (0 : ℝ)} = Set.univ := by
    ext _ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, ge_iff_le]
    exact iff_of_true
      (norm_nonneg (∑ _k in Finset.range 1, (0 : Matrix (Fin 0) (Fin 0) ℝ)))
      trivial
  rw [hev] at h
  have huniv : μ Set.univ = 1 := measure_univ
  rw [huniv] at h
  have hc : (Fintype.card (Fin 0) : ℝ) = 0 := by norm_num [Fintype.card_fin]
  rw [hc, mul_zero, zero_mul, ENNReal.ofReal_zero] at h
  exact absurd h (not_le.mpr zero_lt_one)

/-- The repaired statements are honest at `t = 0` on nonempty `V`: the
bound `2 d` dominates the trivial probability `1` (`d ≥ 1`). -/
theorem two_card_bound_honest_QA {W : Type*} [Fintype W] [Nonempty W] :
    (1 : ENNReal) ≤ ENNReal.ofReal (2 * (Fintype.card W : ℝ)) := by
  have h0 : (1 : ℕ) ≤ Fintype.card W := by
    have := Fintype.card_pos (α := W)
    omega
  have h1 : (1 : ℝ) ≤ 2 * (Fintype.card W : ℝ) := by
    have hc : (1 : ℝ) ≤ (Fintype.card W : ℝ) := by exact_mod_cast h0
    linarith
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal h1

end Scaffold.Mathlib.Probability.Concentration.Matrix.QA
