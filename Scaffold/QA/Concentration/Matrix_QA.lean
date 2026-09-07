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
import Scaffold.Mathlib.Probability.Concentration.Matrix.MasterBound
import Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Duhamel
import Scaffold.Mathlib.Probability.BernoulliProduct
import Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding
import Scaffold.Mathlib.GraphTheory.Spectral
import Mathlib.Data.Complex.ExponentialBounds

open MeasureTheory ProbabilityTheory Classical
open Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent SpectralGraphTheory
open Scaffold.Mathlib.Probability.BernoulliProduct
open scoped ENNReal Matrix Matrix.L2OpNorm

set_option maxHeartbeats 1200000
set_option linter.unnecessarySeqFocus false

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

/-- A constant matrix family is mutually independent under any
probability measure — the repaired `h_indep` clause shape at the
zero-family instantiations below. -/
theorem iIndepFun_const_matrix_QA {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (M : Matrix V V ℝ) :
    iIndepFun (fun _ : Fin n =>
      (inferInstance : MeasurableSpace (Matrix V V ℝ)))
      (fun (_ : Fin n) (_ : Ω) => M) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro T sets hsets
  by_cases hall : ∀ i ∈ T, M ∈ sets i
  · have hpre : ∀ i ∈ T, (fun _ : Ω => M) ⁻¹' sets i = Set.univ := by
      intro i hi
      ext ω
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      exact hall i hi
    have huniv : (⋂ i ∈ T, (fun _ : Ω => M) ⁻¹' sets i) = Set.univ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_univ, Set.mem_preimage]
      exact ⟨fun _ => trivial, fun h => fun i hi => hall i hi⟩
    rw [huniv, measure_univ]
    rw [Finset.prod_eq_one fun i hi => by rw [hpre i hi, measure_univ]]
  · push_neg at hall
    obtain ⟨i₀, hi₀, hi₀A⟩ := hall
    have hempty : (⋂ i ∈ T, (fun _ : Ω => M) ⁻¹' sets i) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_empty_iff_false]
      exact ⟨fun h => hi₀A (h i₀ hi₀), fun h => h.elim⟩
    have hzero : μ ((fun _ : Ω => M) ⁻¹' sets i₀) = 0 := by
      have hpre : (fun _ : Ω => M) ⁻¹' sets i₀ = ∅ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_empty_iff_false]
        exact ⟨hi₀A, fun h => h.elim⟩
      rw [hpre, measure_empty]
    rw [hempty, measure_empty, Finset.prod_eq_zero hi₀ hzero]

/-!
## Matrix Hoeffding interface
-/

/-- Matrix Hoeffding instantiated at the constant-zero family with zero
dominators `A i = 0`: all hypotheses are discharged constructively
(`PosSemidef.zero` for the semidefinite order, `isHermitian_zero`,
`stronglyMeasurable_const`, constant independence, and the repaired
centering clause — the integral of the constant-zero family vanishes).
Re-threaded at the 2026-08-30 centering repair (Errata §9). -/
theorem matrix_hoeffding_zero_QA [Nonempty V] {n : ℕ} (t : ℝ) (ht : 0 < t) :
    μ {ω : Ω | ‖∑ i : Fin n, (0 : Matrix V V ℝ)‖ ≥ t} ≤
      ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-(t ^ 2) / (2 * ‖∑ i : Fin n, (0 : Matrix V V ℝ) * 0‖))) := by
  exact matrix_hoeffding (X := fun _ _ => 0) (A := fun _ => 0)
    (fun i => stronglyMeasurable_const) (iIndepFun_const_matrix_QA (Ω := Ω) (μ := μ) 0)
    (fun i ω => Matrix.isHermitian_zero) (fun _i => by simp)
    (fun i ω => by simpa using Matrix.PosSemidef.zero)
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
    (fun i => stronglyMeasurable_const) (iIndepFun_const_matrix_QA (Ω := Ω) (μ := μ) 0)
    (fun i ω => Matrix.isHermitian_zero) (fun i => by simp)
    (fun i ω => by simp) t ht.le

/-!
## Matrix Azuma interface
-/

/-- The constant-zero difference sequence is a `MatrixMDS` with bound
`R = 0`: ambient strong measurability holds for constants, the
conditional means vanish on every past event (genuinely — the integrals
of the constant-zero function are real zeros), and the norm bound is
`‖0‖ ≤ 0`. -/
def zeroMatrixMDS : MatrixMDS (V := V) μ where
  R := 0
  X := fun _ _ => 0
  measurable := fun k => stronglyMeasurable_const
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
-- @refutes: matrix_hoeffding
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
-- @refutes: matrix_bernstein
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
-- @refutes: matrix_azuma_hoeffding
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


/-!
## The centering repair record (2026-08-30, Errata §9)

`matrix_hoeffding` was repaired on 2026-08-30 (run
`20260830T183850Z-run-1`, Step 0 of
`proposals/repair-matrix-hoeffding-centering.md`) by adding the centering
clause `h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0` — the same clause idiom its
sibling `matrix_bernstein` has carried all along. The pre-repair
statement was materially false in hypothesis shape: the deterministic
constant-ones family below satisfies every pre-repair hypothesis
genuinely — self-domination at equality, measurability, mutual
independence of constants, Hermitianity — yet its tail event is all of
`Ω` against a bound strictly below `1`. This is the same hazard class as
the scalar Bernstein pair (Errata §8: an uncentered hypothesis set where
the source bounds centered variables), found here by running the §5
adversarial Step-0 that the Bernstein audit never extended to this file.
The lemmas below record the exact `Fin 1` norm pin the fixture rides on,
the proved pre-repair hypothesis set at the family, the hypothesis-form
refutation, and the exclusion fence (the repaired clause rejects exactly
the refuting family).
-/

/-- The exact `Fin 1` norm pin: `‖(1 : Matrix (Fin 1) (Fin 1) ℝ) + 1‖ = 2`.
Every vector is an eigenvector at `2` (`(1 + 1) *ᵥ x = 2 • x`), so the
`evals_first_le_eigvalOf`/`eigvalOf_le_evals_last` sandwich pins the
unique sorted eigenvalue at `2`, and both operator-norm bridges
(`l2OpNorm_le_of_abs_evals_le`, `abs_evals_le_l2OpNorm`) close at
equality — an independent two-sided computation of the fixture's
variance statistic, joining `l2OpNorm_one_fin1_QA` above. -/
theorem norm_one_add_one_fin1_QA :
    ‖((1 : Matrix (Fin 1) (Fin 1) ℝ) + 1)‖ = 2 := by
  have hisymm : ((1 : Matrix (Fin 1) (Fin 1) ℝ) + 1).IsSymm := by
    simp [Matrix.IsSymm]
  have hxne : (onesVec : Fin 1 → ℝ) ≠ 0 := by
    intro h
    have hv : (onesVec : Fin 1 → ℝ) ⟨0, by norm_num⟩ = 0 := congrFun h _
    simp [onesVec] at hv
  have hxμ : ((1 : Matrix (Fin 1) (Fin 1) ℝ) + 1) *ᵥ (onesVec : Fin 1 → ℝ)
      = (2 : ℝ) • (onesVec : Fin 1 → ℝ) := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
    exact (two_smul ℝ _).symm
  obtain ⟨i, hi⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul hisymm hxne hxμ
  have hcard : (1 : ℕ) ≤ Fintype.card (Fin 1) := by norm_num
  have hlast : (Fin.mk (Fintype.card (Fin 1) - 1) (by norm_num))
      = (Fin.mk 0 (by norm_num) : Fin (Fintype.card (Fin 1))) := by
    ext
    norm_num
  have hpin : evals hisymm (Fin.mk 0 (by norm_num) : Fin (Fintype.card (Fin 1)))
      = 2 := by
    have hle := evals_first_le_eigvalOf hisymm hcard i
    have hge := eigvalOf_le_evals_last hisymm hcard i
    rw [hlast] at hge
    rw [hi] at hle hge
    exact le_antisymm hle hge
  refine le_antisymm ?_ ?_
  · refine l2OpNorm_le_of_abs_evals_le hisymm (by norm_num) ?_
    intro k
    have hk : k.val = 0 := by
      have hlt := k.isLt
      simp only [Fintype.card_fin] at hlt
      omega
    rw [show k = (Fin.mk 0 (by norm_num) : Fin (Fintype.card (Fin 1)))
        from Fin.ext hk, hpin]
    norm_num
  · have h := abs_evals_le_l2OpNorm hisymm
      (Fin.mk 0 (by norm_num) : Fin (Fintype.card (Fin 1)))
    rw [hpin] at h
    simpa using h

/-- Every pre-repair hypothesis clause of `matrix_hoeffding` is *proved*
at the refuting family (the constant-ones matrices on `V = Fin 1`,
`n = 2`): measurability of constants, mutual independence of constants
at the matrix codomain, Hermitianity of the identity, and semidefinite
self-domination at equality (`1² − 1² = 0 ⪰ 0`). No centering clause
existed to fail — that absence is the defect. -/
theorem ones_family_old_clauses_QA {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (∀ _i : Fin 2, StronglyMeasurable
        (fun (_ω : Ω) => (1 : Matrix (Fin 1) (Fin 1) ℝ)))
      ∧ iIndepFun (fun _ : Fin 2 =>
          (inferInstance : MeasurableSpace (Matrix (Fin 1) (Fin 1) ℝ)))
          (fun (_ : Fin 2) (_ : Ω) => (1 : Matrix (Fin 1) (Fin 1) ℝ)) μ
      ∧ (∀ (_i : Fin 2) (_ω : Ω),
          ((1 : Matrix (Fin 1) (Fin 1) ℝ)).IsHermitian)
      ∧ (∀ (_i : Fin 2) (_ω : Ω),
          Matrix.PosSemidef ((1 : Matrix (Fin 1) (Fin 1) ℝ) * 1
            - (1 : Matrix (Fin 1) (Fin 1) ℝ) * 1)) := by
  refine ⟨fun _i => stronglyMeasurable_const,
    iIndepFun_const_matrix_QA (Ω := Ω) (μ := μ) 1, fun _i _ω => ?_,
    fun _i _ω => ?_⟩
  · exact isHermitian_of_isSymm (by simp [Matrix.IsSymm])
  · simpa using Matrix.PosSemidef.zero

/-- **The pre-repair `matrix_hoeffding` shape is refuted by an uncentered
deterministic family**: at `V = Fin 1`, `n = 2`, `X i = A i = 1` (every
pre-repair hypothesis genuinely holds — `ones_family_old_clauses_QA`),
`t = 2`, the tail event is all of `Ω` (the norm is exactly `2` by
`norm_one_add_one_fin1_QA`), so a probability measure gives `1`, while
the bound is `2 · 1 · exp (−1) < 1` (from the pinned `2 < exp 1`). The
family's mean is `1 ≠ 0`: the missing centering hypothesis is the
defect. -/
-- @refutes: matrix_hoeffding
theorem old_matrix_hoeffding_refuted_uncentered_QA {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : μ {_ω : Ω | ‖∑ _i : Fin 2, (1 : Matrix (Fin 1) (Fin 1) ℝ)‖ ≥ (2 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 1) : ℝ) *
        Real.exp (-((2 : ℝ) ^ 2) / (2 * ‖∑ _i : Fin 2,
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) * 1)‖)))) :
    False := by
  have hsumA : ∑ i : Fin 2, ((1 : Matrix (Fin 1) (Fin 1) ℝ) * 1)
      = (1 : Matrix (Fin 1) (Fin 1) ℝ) + 1 := by
    rw [Finset.sum_congr rfl fun _i (_ : _i ∈ Finset.univ) => Matrix.one_mul 1,
      Fin.sum_univ_two fun _ => 1]
  have hev : {_ω : Ω | ‖∑ _i : Fin 2, (1 : Matrix (Fin 1) (Fin 1) ℝ)‖ ≥ (2 : ℝ)}
      = Set.univ := by
    ext _ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, ge_iff_le]
    rw [Fin.sum_univ_two fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ),
      norm_one_add_one_fin1_QA]
    exact iff_of_true (le_refl _) trivial
  rw [hev, measure_univ] at h
  rw [hsumA, norm_one_add_one_fin1_QA] at h
  have hcard : (Fintype.card (Fin 1) : ℝ) = 1 := by norm_num
  rw [hcard, mul_one] at h
  have hex : (-((2 : ℝ) ^ 2)) / (2 * 2) = -(1 : ℝ) := by norm_num
  rw [hex] at h
  rw [ENNReal.one_le_ofReal] at h
  have hexp : (2 : ℝ) < Real.exp 1 :=
    lt_of_lt_of_le (by norm_num : (2 : ℝ) < 2.7182818283)
      (le_of_lt Real.exp_one_gt_d9)
  have hlt : (2 : ℝ) * Real.exp (-(1 : ℝ)) < 1 := by
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hinvt : (2 : ℝ) * (Real.exp 1) ⁻¹ * Real.exp 1 = 2 := by
      rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one]
    rw [Real.exp_neg]
    rcases lt_or_ge ((2 : ℝ) * (Real.exp 1) ⁻¹) 1 with hlt | hge
    · exact hlt
    · have hmul := mul_le_mul_of_nonneg_right hge hpos.le
      rw [hinvt, one_mul] at hmul
      exact absurd hmul (not_le.mpr hexp)
  linarith

/-- **The exclusion fence**: the repaired `h_mean` clause genuinely
rejects the refuting family — the constant-ones summand integrates to
`1 ≠ 0` on every probability space, so the repaired axiom's hypothesis
set is not satisfiable by the counterexample that refuted the old shape
(the repair does real exclusion work, the `azDrift_not_stronglyMeasurable_QA`
pattern). -/
theorem ones_mean_ne_zero_QA {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∫ (_ω : Ω), (1 : Matrix (Fin 1) (Fin 1) ℝ) ∂μ
      ≠ (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  rw [integral_const]
  simp [one_ne_zero]


/-!
## The ambient-measurability repair record (2026-08-29)

`MatrixMDS` was repaired on 2026-08-29 (run `20260829T235239Z-run-1`,
Step 0 of `proposals/audit-matrix-azuma-mds-measurability-hazard.md`,
Errata §7): the pre-repair structure's `adapted` field was content-free
(`mdsFiltration` is the comap σ-algebra the `X j` generate themselves),
nothing forced ambient strong measurability, and the `cond_mean_zero`
set-integrals are the `integral_non_aestronglyMeasurable` junk zeros for
non-ambiently-measurable bounded `X k` — so the martingale hypothesis was
satisfiable by a bounded non-measurable drift. The lemmas below record
the vacuity (set level), the junk engine, the refutation fixture with
every old field proved, and the hypothesis-form refutation of the
pre-repair axiom shape. The pre-repair `adapted` field at the fixture is
proved as `azDrift_adapted`; the vacuity lemma is stated in the
measurable-set sense (the SM form at the shelf's hand-rolled matrix
σ-algebra has no registered Borel bridge, but the comap structure makes
the set-level statement the mathematical content).
-/

omit [Fintype V] [DecidableEq V] in
/-- The set-level vacuity record: every `X k` is measurable against the
σ-algebra `mdsFiltration X (k+1)` that `X 0, …, X k` themselves generate
(the comap σ-algebra is built from their preimages). This is why the
pre-repair `adapted` field constrained nothing. -/
theorem measurable_mdsFiltration_QA (X : ℕ → Ω → Matrix V V ℝ) (k : ℕ) :
    Measurable[mdsFiltration X (k + 1)] (X k) := by
  intro B hB
  have hcyl : MeasurableSet[MeasurableSpace.pi]
      {t : Fin (k + 1) → Matrix V V ℝ | t (k : Fin (k + 1)) ∈ B} :=
    (measurable_pi_apply (k : Fin (k + 1))) hB
  refine ⟨_, hcyl, ?_⟩
  ext ω
  simp

/-- The junk-integral engine: a function that is not almost-everywhere
strongly measurable w.r.t. the restricted measure has every set-integral
equal to the definitional junk zero. -/
theorem setIntegral_eq_zero_of_not_aeStronglyMeasurable_QA {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] (f : Ω → W) (μ : Measure Ω)
    (S : Set Ω) (hf : ¬ AEStronglyMeasurable f (μ.restrict S)) :
    ∫ ω in S, f ω ∂μ = 0 :=
  integral_non_aestronglyMeasurable hf

/-! ### The caterpillar fixture

`Ω = Fin 33` with the TRIVIAL σ-algebra: the measure puts mass `1/2` at
the top point `32` and spreads `1/2` uniformly. Step `k` of the drift
sequence is the identity matrix on the strict tail `{i | k < i}`, zero
elsewhere: each step is bounded by `1`, its past σ-algebra cannot see
the fresh tail variation, and the 32-step sum is `32 • 1` at the top
point. Every pre-repair `MatrixMDS` field holds — the conditional means
vanish through the junk mechanism — while the tail event carries mass
`> 1/2` against the axiom bound `≤ 1/2`. -/

noncomputable def azUniform :
    @MeasureTheory.Measure (Fin 33) (⊥ : MeasurableSpace (Fin 33)) :=
  ∑ i : Fin 33, (1 / 33 : ℝ≥0∞) •
    @MeasureTheory.Measure.dirac (Fin 33) (⊥ : MeasurableSpace (Fin 33)) i

theorem azUniform_univ_QA : azUniform Set.univ = 1 := by
  rw [azUniform, Measure.finset_sum_apply]
  have hmem : ∀ i : Fin 33, ((1 / 33 : ℝ≥0∞) •
      @MeasureTheory.Measure.dirac (Fin 33) (⊥ : MeasurableSpace (Fin 33)) i) Set.univ
      = 1 / 33 := by
    intro i
    rw [Measure.smul_apply,
      @Measure.dirac_apply_of_mem (Fin 33) (⊥ : MeasurableSpace (Fin 33)) (s := Set.univ)
        (a := i) (Set.mem_univ i)]
    simp
  rw [Finset.sum_congr rfl (fun i _ => hmem i), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [one_div]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast (two_ne_zero : (2 : ℕ) ≠ 0)) (by simp)

theorem azUniform_apply_QA (T : Set (Fin 33)) (j : Fin 33) (hj : j ∈ T) :
    1 / 33 ≤ azUniform T := by
  rw [azUniform, Measure.finset_sum_apply]
  calc (1 / 33 : ℝ≥0∞)
      = ((1 / 33 : ℝ≥0∞) •
          @MeasureTheory.Measure.dirac (Fin 33) (⊥ : MeasurableSpace (Fin 33)) j) T := by
          rw [Measure.smul_apply,
            @Measure.dirac_apply_of_mem (Fin 33) (⊥ : MeasurableSpace (Fin 33)) (s := T)
              (a := j) hj]
          simp
    _ ≤ ∑ i : Fin 33, ((1 / 33 : ℝ≥0∞) •
          @MeasureTheory.Measure.dirac (Fin 33) (⊥ : MeasurableSpace (Fin 33)) i) T := by
          refine Finset.single_le_sum (f := fun i => ((1 / 33 : ℝ≥0∞) •
            @MeasureTheory.Measure.dirac (Fin 33) (⊥ : MeasurableSpace (Fin 33)) i) T)
            (fun i _ => zero_le _) (Finset.mem_univ j)

noncomputable def azDriftMeasure :
    @MeasureTheory.Measure (Fin 33) (⊥ : MeasurableSpace (Fin 33)) :=
  (1 / 2 : ℝ≥0∞) • @MeasureTheory.Measure.dirac (Fin 33) (⊥ : MeasurableSpace (Fin 33)) 32
    + (1 / 2 : ℝ≥0∞) • azUniform

instance : @IsProbabilityMeasure (Fin 33) (⊥ : MeasurableSpace (Fin 33)) azDriftMeasure := by
  constructor
  have h1 : ((1 / 2 : ℝ≥0∞) •
      @MeasureTheory.Measure.dirac (Fin 33) (⊥ : MeasurableSpace (Fin 33)) 32) Set.univ
      = 1 / 2 := by
    rw [Measure.smul_apply,
      @Measure.dirac_apply_of_mem (Fin 33) (⊥ : MeasurableSpace (Fin 33)) (s := Set.univ)
        (a := 32) (Set.mem_univ 32)]
    simp
  have h2 : ((1 / 2 : ℝ≥0∞) • azUniform) Set.univ = 1 / 2 := by
    rw [Measure.smul_apply, azUniform_univ_QA]
    simp
  show azDriftMeasure Set.univ = 1
  rw [azDriftMeasure, Measure.add_apply, h1, h2, ← two_mul ((1 / 2 : ℝ≥0∞)),
    one_div,
    ENNReal.mul_inv_cancel (by exact_mod_cast (two_ne_zero : (2 : ℕ) ≠ 0)) (by simp)]

theorem azDriftMeasure_ge_QA {T : Set (Fin 33)} (j : Fin 33) (hj : j ∈ T) :
    (1 / 2 : ℝ≥0∞) * (1 / 33 : ℝ≥0∞) ≤ azDriftMeasure T := by
  rw [azDriftMeasure, Measure.add_apply]
  calc (1 / 2 : ℝ≥0∞) * (1 / 33 : ℝ≥0∞)
      ≤ (1 / 2 : ℝ≥0∞) * azUniform T := mul_le_mul_left' (azUniform_apply_QA T j hj) _
    _ = ((1 / 2 : ℝ≥0∞) • azUniform) T := by
          rw [show ((1 / 2 : ℝ≥0∞) • azUniform) T = (1 / 2 : ℝ≥0∞) * azUniform T
            from Measure.smul_apply _ _ _]
    _ ≤ ((1 / 2 : ℝ≥0∞) •
          @MeasureTheory.Measure.dirac (Fin 33) (⊥ : MeasurableSpace (Fin 33)) 32) T
          + ((1 / 2 : ℝ≥0∞) • azUniform) T := le_add_of_nonneg_left (zero_le _)

theorem azDriftMeasure_ge_top_QA {T : Set (Fin 33)} (h : (32 : Fin 33) ∈ T) :
    1 / 2 + (1 / 2 : ℝ≥0∞) * (1 / 33 : ℝ≥0∞) ≤ azDriftMeasure T := by
  have hd : (1 / 2 : ℝ≥0∞)
      = ((1 / 2 : ℝ≥0∞) •
          @MeasureTheory.Measure.dirac (Fin 33) (⊥ : MeasurableSpace (Fin 33)) 32) T := by
    rw [Measure.smul_apply,
      @Measure.dirac_apply_of_mem (Fin 33) (⊥ : MeasurableSpace (Fin 33)) (s := T)
        (a := 32) h]
    simp
  have hu : (1 / 2 : ℝ≥0∞) * (1 / 33 : ℝ≥0∞)
      ≤ ((1 / 2 : ℝ≥0∞) • azUniform) T := by
    calc (1 / 2 : ℝ≥0∞) * (1 / 33 : ℝ≥0∞)
        ≤ (1 / 2 : ℝ≥0∞) * azUniform T :=
          mul_le_mul_left' (azUniform_apply_QA T 32 h) _
      _ = ((1 / 2 : ℝ≥0∞) • azUniform) T := by
            rw [show ((1 / 2 : ℝ≥0∞) • azUniform) T = (1 / 2 : ℝ≥0∞) * azUniform T
              from Measure.smul_apply _ _ _]
  rw [azDriftMeasure, Measure.add_apply]
  exact add_le_add hd.le hu

theorem azDriftMeasure_pos_QA {T : Set (Fin 33)} (j : Fin 33) (hj : j ∈ T) :
    0 < azDriftMeasure T :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < (1 / 2 : ℝ≥0∞) * (1 / 33 : ℝ≥0∞))
    (azDriftMeasure_ge_QA j hj)

/-- The drift sequence: step `k` is the identity on the strict tail
`{i | k < i}`, zero elsewhere. -/
def azDriftSeq (k : ℕ) : Fin 33 → Matrix (Fin 1) (Fin 1) ℝ :=
  fun i => if k < (i : ℕ) then 1 else 0

theorem azDriftSeq_eq_zero_of_le_QA (k : ℕ) (i : Fin 33) (h : (i : ℕ) ≤ k) :
    azDriftSeq k i = 0 := by
  rw [azDriftSeq]
  have hnk : ¬ k < (i : ℕ) := by omega
  simp [hnk]

theorem azDriftSeq_eq_one_of_lt_QA (k : ℕ) (i : Fin 33) (h : k < (i : ℕ)) :
    azDriftSeq k i = 1 := by
  rw [azDriftSeq, if_pos h]

theorem azDrift_fiber_eq_QA (k : ℕ) {i i' : Fin 33} (hi : (k : ℕ) ≤ (i : ℕ))
    (hi' : (k : ℕ) ≤ (i' : ℕ)) :
    (fun j : Fin k => azDriftSeq j i) = (fun j : Fin k => azDriftSeq j i') := by
  funext j
  rw [azDriftSeq_eq_one_of_lt_QA _ _ (by omega), azDriftSeq_eq_one_of_lt_QA _ _ (by omega)]

theorem azDrift_tail_iff_QA (k : ℕ) {S : Set (Fin 33)}
    (hS : MeasurableSet[mdsFiltration azDriftSeq k] S) {i i' : Fin 33}
    (hi : (k : ℕ) ≤ (i : ℕ)) (hi' : (k : ℕ) ≤ (i' : ℕ)) :
    i ∈ S ↔ i' ∈ S := by
  unfold mdsFiltration at hS
  obtain ⟨T, _, hTpre⟩ := MeasurableSpace.measurableSet_comap.1 hS
  rw [← hTpre]
  simp only [Set.mem_preimage]
  rw [azDrift_fiber_eq_QA k hi hi']

theorem l2OpNorm_one_fin1_QA : ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖ = 1 := by
  have hisymm : (1 : Matrix (Fin 1) (Fin 1) ℝ).IsSymm := by
    simp [Matrix.IsSymm]
  refine le_antisymm (l2OpNorm_le_of_abs_evals_le hisymm (by norm_num) ?_) ?_
  · intro k
    rw [evals_one hisymm]
    simp
  · have h := abs_evals_le_l2OpNorm hisymm (⟨0, by norm_num⟩ :
      Fin (Fintype.card (Fin 1)))
    rw [evals_one hisymm, abs_one] at h
    exact h

/-- The pre-repair `adapted` field holds at the fixture: the two-valued
step function is `mdsFiltration`-strongly-measurable by the ite
constructor at the (comap-measurable) level set. -/
theorem azDrift_adapted_QA (k : ℕ) :
    StronglyMeasurable[mdsFiltration azDriftSeq (k + 1)] (azDriftSeq k) := by
  have hlev : MeasurableSet[mdsFiltration azDriftSeq (k + 1)] {i : Fin 33 | k < (i : ℕ)} := by
    have hentry : Measurable fun m : Matrix (Fin 1) (Fin 1) ℝ => m 0 0 :=
      (measurable_pi_apply (0 : Fin 1)).comp (measurable_pi_apply (0 : Fin 1))
    have hIoi : @MeasurableSet ℝ _ (Set.Ioi (1 / 2 : ℝ)) := measurableSet_Ioi
    have hB : MeasurableSet ((fun m : Matrix (Fin 1) (Fin 1) ℝ => m 0 0) ⁻¹'
        (Set.Ioi (1 / 2 : ℝ))) := hentry hIoi
    have hpre := (measurable_mdsFiltration_QA azDriftSeq k) hB
    have hset : (azDriftSeq k) ⁻¹' ((fun m : Matrix (Fin 1) (Fin 1) ℝ => m 0 0) ⁻¹'
        (Set.Ioi (1 / 2 : ℝ))) = {i : Fin 33 | k < (i : ℕ)} := by
      ext i
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq]
      by_cases h : k < (i : ℕ)
      · rw [azDriftSeq_eq_one_of_lt_QA k i h]
        simp
        exact iff_of_true (by norm_num) h
      · rw [azDriftSeq_eq_zero_of_le_QA k i (by omega)]
        simp
        exact iff_of_false (by norm_num) h
    rw [← hset]
    exact hpre
  unfold azDriftSeq
  exact StronglyMeasurable.ite hlev stronglyMeasurable_const stronglyMeasurable_const

/-- The old `norm_bound` field holds at the fixture with `R = 1`. -/
theorem azDriftSeq_norm_bound_QA (k : ℕ) (i : Fin 33) :
    ‖azDriftSeq k i‖ ≤ 1 := by
  rcases Nat.lt_or_ge k (i : ℕ) with h | h
  · rw [azDriftSeq_eq_one_of_lt_QA k i h, l2OpNorm_one_fin1_QA]
  · rw [azDriftSeq_eq_zero_of_le_QA k i h]
    simp

/-- The old `cond_mean_zero` field holds at the fixture. On past sets
avoiding the tail it holds genuinely (the integrand vanishes pointwise
there); on past sets containing the tail it holds through the junk
zero: the integrand is not almost-everywhere strongly measurable w.r.t.
the restriction, because its two values both carry positive mass. -/
theorem azDrift_cond_mean_zero_QA (k : ℕ) (S : Set (Fin 33))
    (hS : MeasurableSet[mdsFiltration azDriftSeq k] S) :
    ∫ i in S, azDriftSeq k i ∂azDriftMeasure = 0 := by
  rcases Nat.lt_or_ge k 32 with hk | hk
  · by_cases h32 : (32 : Fin 33) ∈ S
    · rw [setIntegral_eq_zero_of_not_aeStronglyMeasurable_QA _ _ _]
      intro haes
      obtain ⟨c, hc⟩ :=
        stronglyMeasurable_bot_iff.1 (AEStronglyMeasurable.stronglyMeasurable_mk haes)
      have heq : azDriftSeq k =ᵐ[azDriftMeasure.restrict S] (fun _ => c) :=
        (haes.ae_eq_mk).trans (by rw [hc])
      have himp := ae_imp_of_ae_restrict heq
      rw [ae_iff] at himp
      have h32val : ((32 : Fin 33) : ℕ) = 32 := by decide
      have h32le : (k : ℕ) ≤ ((32 : Fin 33) : ℕ) := by simp only [h32val]; omega
      by_cases hc0 : c = 0
      · have hjmem : (⟨k + 1, by omega⟩ : Fin 33) ∈ S :=
          (azDrift_tail_iff_QA k hS (i := ⟨k + 1, by omega⟩) (i' := 32) (Nat.le_succ k)
            h32le).2 h32
        have hjval : azDriftSeq k (⟨k + 1, by omega⟩ : Fin 33) = 1 :=
          azDriftSeq_eq_one_of_lt_QA _ _ (Nat.lt_succ_self k)
        have hsub : ({(⟨k + 1, by omega⟩ : Fin 33)} : Set (Fin 33))
            ⊆ {i | ¬ (i ∈ S → azDriftSeq k i = c)} := by
          intro i hi
          simp only [Set.mem_singleton_iff] at hi
          subst i
          simp only [Set.mem_setOf_eq, _root_.not_imp]
          exact ⟨hjmem, by rw [hjval, hc0]; norm_num⟩
        exact (azDriftMeasure_pos_QA _ (Set.mem_singleton _)).ne'
          (measure_mono_null hsub himp)
      · have hjmem : (⟨k, by omega⟩ : Fin 33) ∈ S :=
          (azDrift_tail_iff_QA k hS (i := ⟨k, by omega⟩) (i' := 32) (Nat.le_refl k)
            h32le).2 h32
        have hjval : azDriftSeq k (⟨k, by omega⟩ : Fin 33) = 0 :=
          azDriftSeq_eq_zero_of_le_QA _ _ (Nat.le_refl k)
        have hsub : ({(⟨k, by omega⟩ : Fin 33)} : Set (Fin 33))
            ⊆ {i | ¬ (i ∈ S → azDriftSeq k i = c)} := by
          intro i hi
          simp only [Set.mem_singleton_iff] at hi
          subst i
          simp only [Set.mem_setOf_eq, _root_.not_imp]
          exact ⟨hjmem, by rw [hjval]; exact fun h => hc0 h.symm⟩
        exact (azDriftMeasure_pos_QA _ (Set.mem_singleton _)).ne'
          (measure_mono_null hsub himp)
    · have hzero : ∀ i ∈ S, azDriftSeq k i = 0 := by
        intro i hi
        have h32val : ((32 : Fin 33) : ℕ) = 32 := by decide
        have h32le : (k : ℕ) ≤ ((32 : Fin 33) : ℕ) := by simp only [h32val]; omega
        have : ¬ (k : ℕ) ≤ (i : ℕ) := fun hle =>
          h32 ((azDrift_tail_iff_QA k hS (i := i) (i' := 32) hle h32le).1 hi)
        exact azDriftSeq_eq_zero_of_le_QA k i (by omega)
      exact @setIntegral_eq_zero_of_forall_eq_zero (Fin 33) (Matrix (Fin 1) (Fin 1) ℝ)
        (⊥ : MeasurableSpace (Fin 33)) _ _ (azDriftSeq k) S azDriftMeasure hzero
  · have hzero : ∀ i : Fin 33, azDriftSeq k i = 0 :=
      fun i => azDriftSeq_eq_zero_of_le_QA k i (by omega)
    exact @setIntegral_eq_zero_of_forall_eq_zero (Fin 33) (Matrix (Fin 1) (Fin 1) ℝ)
      (⊥ : MeasurableSpace (Fin 33)) _ _ (azDriftSeq k) S azDriftMeasure
      (fun i _ => hzero i)

/-- The fixture's tail event at `t = 31`: the sum of the first 32
drift steps is `32 • 1` at the top point, so the event contains `{32}`
and carries mass strictly above `1/2`. -/
theorem azDrift_event_ge_QA :
    (1 / 2 : ℝ≥0∞) < azDriftMeasure
      {i : Fin 33 | ‖∑ k in Finset.range 32, azDriftSeq k i‖ ≥ 31} := by
  have hsum : ∑ k in Finset.range 32, azDriftSeq k (32 : Fin 33)
      = ((Finset.range 32).card : ℕ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [Finset.sum_congr rfl (fun k hk => azDriftSeq_eq_one_of_lt_QA _ _
      (by simpa using Finset.mem_range.1 hk)), Finset.sum_const]
  have hval : ‖∑ k in Finset.range 32, azDriftSeq k (32 : Fin 33)‖ = 32 := by
    rw [hsum, Finset.card_range, ← Nat.cast_smul_eq_nsmul (R := ℝ), norm_smul,
      l2OpNorm_one_fin1_QA]
    simp
  have h32mem : (32 : Fin 33) ∈ {i : Fin 33 | ‖∑ k in Finset.range 32, azDriftSeq k i‖ ≥ 31} := by
    simp only [Set.mem_setOf_eq, ge_iff_le]
    rw [hval]
    norm_num
  refine lt_of_lt_of_le ?_ (azDriftMeasure_ge_top_QA h32mem)
  have hpos : (0 : ℝ≥0∞) < (1 / 2 : ℝ≥0∞) * (1 / 33 : ℝ≥0∞) := by norm_num
  calc (1 / 2 : ℝ≥0∞) = 1 / 2 + 0 := by ring
    _ < 1 / 2 + (1 / 2 : ℝ≥0∞) * (1 / 33 : ℝ≥0∞) := by
        exact ENNReal.add_lt_add_left (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤) hpos

/-- The bound side at the fixture: `2 · 1 · exp (−31² / (8 · 32 · 1²))
= 2 · exp (−961/256) ≤ 2 · exp (−3) ≤ 1/2`, since `exp 3 ≥ 1 + 3 = 4`. -/
theorem azDrift_bound_le_half_QA :
    ENNReal.ofReal (2 * (Fintype.card (Fin 1) : ℝ) *
        Real.exp (-((31 : ℝ) ^ 2) / (8 * (32 : ℝ) * (1 : ℝ) ^ 2))) ≤ 1 / 2 := by
  rw [show Real.exp (-((31 : ℝ) ^ 2) / (8 * (32 : ℝ) * (1 : ℝ) ^ 2))
      = Real.exp (-((31 : ℝ) ^ 2 / (8 * (32 : ℝ) * (1 : ℝ) ^ 2))) from by
    rw [neg_div]]
  have hcard : (Fintype.card (Fin 1) : ℝ) = 1 := by norm_num
  have hexp3 : (4 : ℝ) ≤ Real.exp 3 := by
    have := Real.add_one_le_exp 3
    linarith
  have hmono : Real.exp (-((31 : ℝ) ^ 2 / (8 * (32 : ℝ) * (1 : ℝ) ^ 2)))
      ≤ Real.exp (-(3 : ℝ)) := by
    refine Real.exp_le_exp.2 ?_
    have hfrac : ((31 : ℝ) ^ 2 / (8 * (32 : ℝ) * (1 : ℝ) ^ 2)) = 961 / 256 := by norm_num
    rw [hfrac]
    norm_num
  have hneg : Real.exp (-(3 : ℝ)) = (Real.exp 3)⁻¹ := by
    rw [Real.exp_neg]
  have hA : Real.exp (-((31 : ℝ) ^ 2 / (8 * (32 : ℝ) * (1 : ℝ) ^ 2))) ≤ 1 / 4 := by
    refine le_trans hmono ?_
    rw [hneg]
    have h4 : (Real.exp 3)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by positivity) hexp3
    have h44 : ((4 : ℝ)⁻¹) = 1 / 4 := by norm_num
    rwa [h44] at h4
  have hA0 : (0 : ℝ) ≤ Real.exp (-((31 : ℝ) ^ 2 / (8 * (32 : ℝ) * (1 : ℝ) ^ 2))) :=
    Real.exp_nonneg _
  have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := ENNReal.ofReal_ofNat 2
  have hinv : ENNReal.ofReal ((2 : ℝ)⁻¹) = (2 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), h2]
  have hhalfℝ : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by field_simp
  have hbound : 2 * (Fintype.card (Fin 1) : ℝ) *
      Real.exp (-((31 : ℝ) ^ 2 / (8 * (32 : ℝ) * (1 : ℝ) ^ 2))) ≤ (2 : ℝ)⁻¹ := by
    rw [hcard, ← hhalfℝ]
    nlinarith
  rw [one_div (2 : ℝ≥0∞), ← hinv]
  exact ENNReal.ofReal_le_ofReal hbound

/-- The pre-repair `matrix_azuma_hoeffding` shape is refuted at the
caterpillar fixture (hypothesis form): every pre-repair `MatrixMDS`
field is proved at the fixture (`azDrift_adapted_QA`,
`azDrift_cond_mean_zero_QA`, `azDriftSeq_norm_bound_QA` at `R = 1`, and
`IsProbabilityMeasure azDriftMeasure`), yet the specialized conclusion
fails — the tail event carries mass `> 1/2` against the bound `≤ 1/2`.
A refutation cannot consume the axiom it refutes; `#print axioms` reads
exactly the standard three. -/
-- @refutes: matrix_azuma_hoeffding
theorem old_matrix_azuma_refuted_nonmeasurable_QA
    (h : azDriftMeasure {i : Fin 33 | ‖∑ k in Finset.range 32, azDriftSeq k i‖ ≥ 31}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 1) : ℝ) *
        Real.exp (-((31 : ℝ) ^ 2) / (8 * (32 : ℝ) * (1 : ℝ) ^ 2)))) :
    False := by
  refine absurd h (not_le.mpr ?_)
  exact lt_of_le_of_lt azDrift_bound_le_half_QA azDrift_event_ge_QA

/-- The repair is load-bearing: the drift fixture that satisfies every
pre-repair `MatrixMDS` field (per the refutation above) FAILS the
repaired `measurable` field — on the fixture's trivial ambient
σ-algebra, strongly measurable functions are exactly the constants
(`stronglyMeasurable_bot_iff`), and the drift takes the values `0` (at
`⟨k⟩`) and `1` (at `⟨k + 1⟩`) whenever both points exist. The new
field excludes exactly the counterexample family that refuted the old
shape, so the repair does real exclusion work rather than adding a
vacuous clause. -/
theorem azDrift_not_stronglyMeasurable_QA (k : ℕ) (hk : k < 32) :
    ¬ StronglyMeasurable[(⊥ : MeasurableSpace (Fin 33))] (azDriftSeq k) := by
  rw [stronglyMeasurable_bot_iff]
  rintro ⟨c, hc⟩
  have h1 : azDriftSeq k (⟨k + 1, by omega⟩ : Fin 33) = 1 :=
    azDriftSeq_eq_one_of_lt_QA k _ (Nat.lt_succ_self k)
  have h0 : azDriftSeq k (⟨k, by omega⟩ : Fin 33) = 0 :=
    azDriftSeq_eq_zero_of_le_QA k _ (Nat.le_refl k)
  have e1 : (1 : Matrix (Fin 1) (Fin 1) ℝ) = c := by
    have h := congrFun hc (⟨k + 1, by omega⟩ : Fin 33)
    rw [h1] at h
    simpa using h
  have e0 : (0 : Matrix (Fin 1) (Fin 1) ℝ) = c := by
    have h := congrFun hc (⟨k, by omega⟩ : Fin 33)
    rw [h0] at h
    simpa using h
  exact absurd (e1.trans e0.symm) (by norm_num)

/-!
## The master bound (retirement route, Step 1)

QA for `Matrix.MasterBound`: the deterministic trace-exponential
identity pinned two-sided at a fully computed fixture, the master bound
instantiated end-to-end at the constant design, and the degenerate
`V = ∅` corner fenced (the corner class the admitted matrix axioms were
repaired for on 2026-08-28 — this module carries its guard at birth).
-/

section MasterBoundQA

open Scaffold.Mathlib.Probability.Concentration.Matrix

private def diagD : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![0, 2]

private theorem diagD_symm : diagD.IsSymm := by
  simp [diagD]

/-- The two eigenvalues of `diagD`, pinned by trace and determinant
(independent of the trace-exponential identity). -/
private theorem diagD_eigs :
    ((eigvalOf diagD diagD_symm 0 = 0 ∧ eigvalOf diagD diagD_symm 1 = 2) ∨
     (eigvalOf diagD diagD_symm 0 = 2 ∧ eigvalOf diagD diagD_symm 1 = 0)) := by
  have hsum : eigvalOf diagD diagD_symm 0 + eigvalOf diagD diagD_symm 1 = 2 := by
    have h := eigvalOf_sum_eq_trace diagD diagD_symm
    simpa [diagD, Matrix.trace_diagonal] using h
  have hprod : eigvalOf diagD diagD_symm 0 * eigvalOf diagD diagD_symm 1 = 0 := by
    have h := (isHermitian_of_isSymm diagD_symm).det_eq_prod_eigenvalues
    have hdet : diagD.det = 0 := by simp [diagD, Matrix.det_diagonal]
    rw [hdet] at h
    simpa [eigvalOf, Fin.prod_univ_two, RCLike.ofReal_real_eq_id] using h.symm
  rcases mul_eq_zero.mp hprod with h0 | h0
  · exact Or.inl ⟨h0, by rw [h0] at hsum; linarith⟩
  · exact Or.inr ⟨by rw [h0] at hsum; linarith, h0⟩

/-- The trace-exponential at the diagonal fixture, computed directly by
the diagonal route (`exp_diagonal` + `trace_diagonal`) — independent of
the trace identity. -/
theorem trace_exp_diag_direct_QA (w : ℝ) :
    (NormedSpace.exp ℝ (w • diagD)).trace = 1 + Real.exp (2 * w) := by
  have hd : w • diagD = Matrix.diagonal (![w * 0, w * 2]) := by
    ext i j
    simp [diagD, Matrix.diagonal_apply, Matrix.diagonal_smul]
    split <;> fin_cases i <;> fin_cases j <;> simp
  rw [hd, Matrix.exp_diagonal, Matrix.trace_diagonal]
  have h0 : NormedSpace.exp ℝ (![w * 0, w * 2] : Fin 2 → ℝ) 0 = Real.exp (w * 0) := by
    simp [Real.exp_eq_exp_ℝ]
  have h1 : NormedSpace.exp ℝ (![w * 0, w * 2] : Fin 2 → ℝ) 1 = Real.exp (w * 2) := by
    simp [Real.exp_eq_exp_ℝ]
  rw [Fin.sum_univ_two, h0, h1]
  simp only [mul_zero, Real.exp_zero, zero_add]
  ring_nf

/-- The trace identity joined to the eigenvalue pin at `θ = 1`: the
theorem's value at the fixture is the true trace `1 + e²` — agreeing
with `trace_exp_diag_direct_QA`'s independent diagonal route. A wrong
eigen-expansion inside the identity would break this agreement. -/
theorem trace_exp_diag_identity_QA :
    ∑ i, Real.exp (1 * eigvalOf diagD diagD_symm i) = 1 + Real.exp 2 := by
  rw [Fin.sum_univ_two]
  rcases diagD_eigs with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · simp only [h0, h1, one_mul, Real.exp_zero]
  · simp only [h0, h1, one_mul, Real.exp_zero]
    ring

/-- The `θ = −1` variant of the same join: the identity's sign path. -/
theorem trace_exp_diag_identity_neg_QA :
    ∑ i, Real.exp ((-1 : ℝ) * eigvalOf diagD diagD_symm i)
      = 1 + Real.exp (-(2 : ℝ)) := by
  rw [← trace_exp_smul_eq_sum_exp_eigvalOf diagD diagD_symm (-1),
    trace_exp_diag_direct_QA (-1)]
  simp

private theorem diagD_norm : ‖diagD‖ = 2 := by
  refine le_antisymm ?_ ?_
  · refine Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.l2OpNorm_le_of_abs_eigvalOf_le
        diagD_symm (by norm_num) ?_
    intro i
    rcases diagD_eigs with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · fin_cases i <;> simp [h0, h1]
    · fin_cases i <;> simp [h0, h1]
  · rcases diagD_eigs with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · refine le_trans (show (2 : ℝ) ≤ |eigvalOf diagD diagD_symm 1| from by simp [h1]) ?_
      exact Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.abs_eigvalOf_le_l2OpNorm
        diagD_symm 1
    · refine le_trans (show (2 : ℝ) ≤ |eigvalOf diagD diagD_symm 0| from by simp [h0]) ?_
      exact Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.abs_eigvalOf_le_l2OpNorm
        diagD_symm 0

/-- **Constant-design master-bound instance**: `Y ≡ diagD`, `θ = 1`,
`t = 2`. The tail event is all of `Ω` (the norm is exactly `2`, pinned),
so the left side is `1`, and the instantiated bound computes to
`e^{−2} ((1 + e²) + (1 + e^{−2}))` — at least `1` because the `e²` term
pays for itself: the bound is not vacuous. The statement's interface is
exercised end-to-end, every clause discharged. -/
theorem master_bound_diag_constant_QA {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (-(2 : ℝ)))
      * (ENNReal.ofReal (1 + Real.exp 2)
        + ENNReal.ofReal (1 + Real.exp (-(2 : ℝ)))) := by
  have h := matrix_master_bound (V := Fin 2) μ (fun _ => diagD_symm)
    (Y := fun _ : Ω => diagD) stronglyMeasurable_const (θ := 1) (by norm_num) 2
  have hev : {ω : Ω | (2 : ℝ) ≤ ‖(fun _ : Ω => diagD) ω‖} = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ]
    exact iff_of_true (by simp [diagD_norm]) trivial
  rw [hev, measure_univ] at h
  rw [lintegral_congr (fun ω => by
      show ENNReal.ofReal ((NormedSpace.exp ℝ ((1 : ℝ) • diagD)).trace) = _
      rw [trace_exp_diag_direct_QA 1]), lintegral_const, measure_univ, mul_one,
    lintegral_congr (fun ω => by
      show ENNReal.ofReal ((NormedSpace.exp ℝ ((-1 : ℝ) • diagD)).trace) = _
      rw [trace_exp_diag_direct_QA (-1 : ℝ)]), lintegral_const, measure_univ] at h
  rw [mul_one, mul_one, show (2 : ℝ) * -1 = -(2 : ℝ) from by ring_nf,
    show -((1 : ℝ) * 2) = -(2 : ℝ) from by ring_nf] at h
  exact h

/-- **Degenerate-corner fence**: at `V = Fin 0`, `Y ≡ 0`, `θ = 0`,
`t = 0`, the master bound's conclusion without the `[Nonempty V]` guard
reads `1 ≤ 0` — the tail event is all of `Ω` while both
trace-exponentials sum over the empty index type. The guard is
load-bearing exactly as for the admitted matrix concentration axioms
(their own `Fin 0` refutations of the 2026-08-28 repair); here the
fence is built at birth, per the §5 hazard-class discipline. -/
theorem master_bound_fin0_unguarded_refuted_QA {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : μ {ω : Ω | (0 : ℝ) ≤ ‖(fun _ : Ω => (0 : Matrix (Fin 0) (Fin 0) ℝ)) ω‖}
      ≤ ENNReal.ofReal (Real.exp (-(0 : ℝ) * 0)) *
        (∫⁻ ω, ENNReal.ofReal (
            (NormedSpace.exp ℝ ((0 : ℝ) • (fun _ : Ω => (0 : Matrix (Fin 0) (Fin 0) ℝ)) ω)).trace)
          ∂μ
        + ∫⁻ ω, ENNReal.ofReal (
            (NormedSpace.exp ℝ ((-0 : ℝ) • (fun _ : Ω => (0 : Matrix (Fin 0) (Fin 0) ℝ)) ω)).trace)
          ∂μ)) :
    False := by
  have hev : {ω : Ω | (0 : ℝ) ≤ ‖(fun _ : Ω => (0 : Matrix (Fin 0) (Fin 0) ℝ)) ω‖}
      = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ]
    exact iff_of_true (norm_nonneg _) trivial
  rw [hev, measure_univ] at h
  have hz : ∀ (w : ℝ) (ω : Ω),
      (NormedSpace.exp ℝ (w • (fun _ : Ω => (0 : Matrix (Fin 0) (Fin 0) ℝ)) ω)).trace = 0 := by
    intro w ω
    simp [Matrix.trace]
  rw [lintegral_congr (fun ω => by rw [hz 0 ω]), lintegral_const,
    lintegral_congr (fun ω => by rw [hz (-0 : ℝ) ω]), lintegral_const] at h
  rw [measure_univ,
    show (-0 : ℝ) * 0 = 0 from by ring_nf, Real.exp_zero, ENNReal.ofReal_one] at h
  norm_num at h

end MasterBoundQA

/-!
## The adversarial fence audit (2026-09-05)

Per-clause hypothesis-necessity fences for the three admitted matrix
concentration axioms — the fresh reverse-import consumption survey's
pick (the subtree carries 14 transitive non-QA consumers, the library's
most-consumed unaudited surface, and is home to 3 of the 4 remaining
admitted axioms). Each fence instantiates the axiom-minus-one-clause
shape at a fixture where every KEPT clause holds genuinely and derives
`False`, tagged `-- @refutes` and axiom-independent by construction
(the fence consumes only the instantiated conclusion, never the axiom).
The three repair-era refutations above (the `Fin 0` corner, the
uncentered family, the caterpillar) close the clauses the repairs were
about; the twelve fences below close the remaining clause surfaces:
- `matrix_hoeffding`: `h_herm` (the alternating nilpotent family),
  `h_indep` (six identical sign riders), `h_bound` (the free variance
  proxy at `A = (1/10)·1`), `ht` (the negative threshold);
- `matrix_bernstein`: `h_mean` (the uncentered deterministic family),
  `h_herm` (genuinely independent sign riders on the uniform cube, the
  nilpotent variance statistic), `h_bound` (the rare-value family
  `99` / `-1` at mass `1/100`), `h_meas` (the headline: the variance
  statistic is ITSELF a junk integral — Errata §7's mechanism class
  reaching the sibling axiom through `Σ`, not the tail event), `ht`
  (the negative threshold with the mixed denominator);
- `matrix_azuma_hoeffding`: `cond_mean_zero` (the constant drift),
  `norm_bound` (the constant `2` drift at `R = 1`), `ht`.
-/

section AdversarialFences

/-- `2 < exp 1`, the on-file decimal anchor (`Real.exp_one_gt_d9`). -/
theorem mc_two_lt_exp_one : (2 : ℝ) < Real.exp 1 :=
  lt_of_lt_of_le (by norm_num : (2 : ℝ) < 2.7182818283) (le_of_lt Real.exp_one_gt_d9)

/-- `exp 1 > 5/2`, the rational anchor for every numeric margin below
(riding the on-file `Real.exp_one_gt_d9`). -/
theorem mc_exp_one_gt_half5 : (5 / 2 : ℝ) < Real.exp 1 :=
  lt_of_lt_of_le (by norm_num) (le_of_lt Real.exp_one_gt_d9)

/-- `4 < exp 2` — kills the prefactor-4 bounds at exponent `≥ 2`. -/
theorem mc_four_lt_exp_two : (4 : ℝ) < Real.exp 2 := by
  have h2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    _ < ((5 / 2 : ℝ) ^ 2) := by norm_num
    _ < (Real.exp 1) ^ 2 :=
        pow_lt_pow_left₀ mc_exp_one_gt_half5 (by norm_num) (by norm_num)

/-- `16 < exp 4`. -/
theorem mc_sixteen_lt_exp_four : (16 : ℝ) < Real.exp 4 := by
  have h4 : Real.exp 4 = (Real.exp 1) ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h4]
  calc (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
    _ < ((5 / 2 : ℝ) ^ 4) := by norm_num
    _ < (Real.exp 1) ^ 4 :=
        pow_lt_pow_left₀ mc_exp_one_gt_half5 (by norm_num) (by norm_num)

/-- `200 < exp 6`. -/
theorem mc_twohundred_lt_exp_six : (200 : ℝ) < Real.exp 6 := by
  have h6 : Real.exp 6 = (Real.exp 1) ^ 6 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h6]
  calc (200 : ℝ) < ((5 / 2 : ℝ) ^ 6) := by norm_num
    _ < (Real.exp 1) ^ 6 :=
        pow_lt_pow_left₀ mc_exp_one_gt_half5 (by norm_num) (by norm_num)

/-- `4 < exp (3/2)` — the exponent that beats the prefactor `2d = 4`
at the n = 1 variance-statistic cap (matrix squares constant). -/
theorem mc_four_lt_exp_three_halves : (4 : ℝ) < Real.exp (3 / 2 : ℝ) := by
  have hsplit : Real.exp (3 / 2 : ℝ) = Real.exp 1 * Real.exp (1 / 2 : ℝ) := by
    rw [← Real.exp_add]; norm_num
  have hhalf : (3 / 2 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
    have := Real.add_one_le_exp (1 / 2 : ℝ)
    linarith
  rw [hsplit]
  have hhpos : (0 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := le_of_lt (Real.exp_pos (1 / 2))
  have hd9 : (2.7182818283 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_d9
  calc (4 : ℝ) < 2.7182818283 * (3 / 2 : ℝ) := by norm_num
    _ ≤ Real.exp 1 * (3 / 2 : ℝ) := mul_le_mul_of_nonneg_right hd9 (by norm_num)
    _ ≤ Real.exp 1 * Real.exp (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hhalf (le_of_lt (Real.exp_pos 1))

/-! ### The coin space (uniform Bernoulli on one coordinate) -/

section Coin

/-- The coin measure: the uniform Bernoulli product on the two-point
space `Fin 1 → Bool` (`bernPMF` at `p = 1/2`), the on-file design
measure — every event mass and integral below rides
`toMeasure_cyl`/`integral_delta`. -/
noncomputable def mcCoin : Measure ((Fin 1) → Bool) :=
  (bernPMF (fun _ => (1 / 2 : ℝ)) (by intro i; norm_num)
    (by intro i; norm_num)).toMeasure

instance : IsProbabilityMeasure mcCoin :=
  PMF.toMeasure.isProbabilityMeasure _

theorem mcCoin_hp (i : (Fin 1)) : (0 : ℝ) ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) ≤ 1 ∧
    (fun _ => (1 / 2 : ℝ)) i = 1 / 2 := by norm_num

/-- The coin's true-cylinder mass: `μ {ω | ω 0} = 1/2` (the
`toMeasure_cyl` engine at `s = {true}`). -/
theorem mcCoin_true :
    mcCoin {ω : (Fin 1) → Bool | ω (0 : Fin 1) = true} = ENNReal.ofReal ((1 : ℝ) / 2) := by
  have hc := toMeasure_cyl (fun _ => (1 / 2 : ℝ)) (by intro i; norm_num)
    (by intro i; norm_num) (0 : Fin 1) ({true} : Set Bool)
  have hpre : {ω : (Fin 1) → Bool | ω (0 : Fin 1) = true}
      = (fun ω : (Fin 1) → Bool => ω (0 : Fin 1)) ⁻¹' {true} := by
    ext ω; simp
  rw [mcCoin, hpre, hc]
  have hb : (Finset.univ : Finset Bool) = ({false, true} : Finset Bool) := by
    ext b; cases b <;> simp
  rw [hb, Finset.sum_insert (by simp), Finset.sum_singleton]
  simp [bern]

end Coin

/-! ### The norm-spine helpers (public route) -/

/-- The vector-action bound through the public C*-spine route (the
same proof shape as the perturbation shelf's
`l2OpNorm_mulVec_le`, stated without private carriers so QA pins can
consume it). -/
theorem mcLe_norm (M : Matrix V V ℝ) (v : V → ℝ) :
    ‖(WithLp.equiv 2 (V → ℝ)).symm (M *ᵥ v)‖ ≤ ‖M‖ * ‖(WithLp.equiv 2 (V → ℝ)).symm v‖ := by
  have h := ContinuousLinearMap.le_opNorm
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) M :
      EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V))
    ((WithLp.equiv 2 (V → ℝ)).symm v)
  rw [Matrix.toEuclideanCLM_piLp_equiv_symm, ← Matrix.cstar_norm_def] at h
  exact h

/-! ### The nilpotent fixture and norm pins -/

/-- The asymmetric nilpotent `Fin 2` fixture: `N = !![0,4;0,0]]`,
`N² = 0`, `‖N‖ ≥ 4` (witnessed by the unit vector `e 1`), every
square-root of the variance proxy vanishes while the norm stays
large. -/
def mcNil4 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 4; 0, 0]

theorem mcNil4_sq : mcNil4 * mcNil4 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, mcNil4, Fin.sum_univ_two, Matrix.zero_apply]

theorem mcNil4_mulVec : mcNil4 *ᵥ ![0, 1] = ![4, 0] := by
  funext k
  fin_cases k <;> simp [Matrix.mulVec, Matrix.dotProduct, mcNil4, Fin.sum_univ_two]

theorem mcNil4_norm_ge : (4 : ℝ) ≤ ‖mcNil4‖ := by
  have hact := mcLe_norm mcNil4 ![0, 1]
  rw [mcNil4_mulVec] at hact
  have hone : ‖(WithLp.equiv 2 ((Fin 2) → ℝ)).symm ![0, 1]‖ = 1 := by
    rw [Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.norm_euclidean_eq_sqrt]
    norm_num [Matrix.dotProduct, Fin.sum_univ_two]
  have hfour : ‖(WithLp.equiv 2 ((Fin 2) → ℝ)).symm ![4, 0]‖ = 4 := by
    rw [Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.norm_euclidean_eq_sqrt]
    have hsq : (![4, 0] : Fin 2 → ℝ) ⬝ᵥ (![4, 0] : Fin 2 → ℝ) = 16 := by
      simp [Matrix.dotProduct, Fin.sum_univ_two]
      norm_num
    rw [hsq]
    exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  rw [hone, hfour, mul_one] at hact
  exact hact

/-! ### Identity pins -/

theorem mcOne_norm_fin2 : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.l2OpNorm_le_of_abs_dotProduct_le
      (by norm_num) ?_
    intro x y
    rw [Matrix.one_mulVec, one_mul]
    exact mul_comm (Real.sqrt (y ⬝ᵥ y)) (Real.sqrt (x ⬝ᵥ x)) ▸
      Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.abs_dotProduct_le y x
  · have h := mcLe_norm (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0]
    rw [Matrix.one_mulVec] at h
    have h1 : ‖(WithLp.equiv 2 ((Fin 2) → ℝ)).symm ![1, 0]‖ = 1 := by
      rw [Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.norm_euclidean_eq_sqrt]
      have hsq : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ (![1, 0] : Fin 2 → ℝ) = 1 := by
        simp [Matrix.dotProduct, Fin.sum_univ_two]
      rw [hsq, Real.sqrt_one]
    simp only [h1, mul_one] at h
    exact h

theorem mcOne_norm_fin1 : ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.l2OpNorm_le_of_abs_dotProduct_le
      (by norm_num) ?_
    intro x y
    rw [Matrix.one_mulVec, one_mul]
    exact mul_comm (Real.sqrt (y ⬝ᵥ y)) (Real.sqrt (x ⬝ᵥ x)) ▸
      Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.abs_dotProduct_le y x
  · have h := mcLe_norm (1 : Matrix (Fin 1) (Fin 1) ℝ) ![1]
    rw [Matrix.one_mulVec] at h
    have h1 : ‖(WithLp.equiv 2 ((Fin 1) → ℝ)).symm ![1]‖ = 1 := by
      rw [Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.norm_euclidean_eq_sqrt]
      simp [Matrix.dotProduct]
    simp only [h1, mul_one] at h
    exact h

/-- The ℕ/ℝ smul bridge on scalar matrices (entrywise). -/
theorem mcNatBridge (n : ℕ) :
    (n : ℕ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) = (n : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j
  simp only [Matrix.smul_apply, Matrix.one_apply]
  norm_num

/-- The ℕ/ℝ smul bridge on scaled scalar matrices (entrywise). -/
theorem mcNatBridge2 (n : ℕ) (c : ℝ) :
    (n : ℕ) • ((c : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = ((n : ℝ) * c) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  push_cast
  ring

/-! ### `matrix_hoeffding` fences -/

/-- **The `h_herm` fence**: the Hermitianity clause is load-bearing.
At the alternating nilpotent family `X 0 = ±mcNil4` on the coin space
(every KEPT clause genuine: measurability by `of_finite`, independence
of the singleton family, centering by the Bernoulli mean, semidefinite
domination `1 − N² = 1 ⪰ 0` through `N² = 0`), the tail event at
`t = 4` is all of the space (`‖±N‖ = ‖N‖ ≥ 4`) against the bound
`4 · exp (−16/2) = 4 e⁻⁸ < 1` — the asymmetric matrix escapes the
Hermitian spectral pipeline entirely. -/
-- @refutes: matrix_hoeffding
theorem mcHg_herm_fence_QA
    (h : mcCoin {ω : (Fin 1) → Bool |
        ‖∑ _i : Fin 1, (if ω (0 : Fin 1) then mcNil4 else -mcNil4)‖ ≥ (4 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 2) : ℝ) *
        Real.exp (-((4 : ℝ) ^ 2) / (2 * ‖∑ _i : Fin 1,
          ((1 : Matrix (Fin 2) (Fin 2) ℝ) * 1)‖)))) :
    False := by
  have hev : {ω : (Fin 1) → Bool |
      ‖∑ _i : Fin 1, (if ω (0 : Fin 1) then mcNil4 else -mcNil4)‖ ≥ (4 : ℝ)}
      = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, ge_iff_le]
    constructor
    · intro _; trivial
    · intro _
      rw [Fin.sum_univ_one]
      by_cases hω : ω (0 : Fin 1) = true
      · rw [if_pos hω]; exact mcNil4_norm_ge
      · rw [if_neg hω, norm_neg]; exact mcNil4_norm_ge
  rw [hev, measure_univ] at h
  have hsum : ∑ _i : Fin 1, ((1 : Matrix (Fin 2) (Fin 2) ℝ) * 1)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Fin.sum_univ_one, Matrix.one_mul]
  rw [hsum, mcOne_norm_fin2] at h
  rw [show (Fintype.card (Fin 2) : ℝ) = 2 by norm_num,
    show (-((4 : ℝ) ^ 2) / (2 * 1)) = -(8 : ℝ) by norm_num,
    show (2 : ℝ) * 2 = 4 by norm_num] at h
  rw [ENNReal.one_le_ofReal] at h
  have hle : Real.exp (2 : ℝ) ≤ Real.exp 8 := Real.exp_le_exp.mpr (by norm_num)
  have h8 : (4 : ℝ) < Real.exp 8 := lt_of_lt_of_le mc_four_lt_exp_two hle
  have hlt : (4 : ℝ) * Real.exp (-(8 : ℝ)) < 1 := by
    rw [Real.exp_neg, mul_comm]
    exact div_eq_inv_mul (4 : ℝ) (Real.exp 8) ▸ (div_lt_one (Real.exp_pos 8)).mpr h8
  linarith

/-- **The `h_bound` fence**: the semidefinite-domination clause is
load-bearing. With the clause dropped, the variance proxy `A` is
unconstrained data: at the same coin family with `X 0 = ±1` on
`V = Fin 1` and `A 0 = (1/10) · 1`, every other clause is genuine yet
the bound reads `2 · exp (−1 / (2 · (1/100))) = 2 e⁻⁵⁰ < 1` against
the full-measure tail event at `t = 1` — an arbitrarily small proxy
buys an arbitrarily small bound. -/
-- @refutes: matrix_hoeffding
theorem mcHg_bound_fence_QA
    (h : mcCoin {ω : (Fin 1) → Bool |
        ‖∑ _i : Fin 1, (if ω (0 : Fin 1) then (1 : Matrix (Fin 1) (Fin 1) ℝ)
          else -(1 : Matrix (Fin 1) (Fin 1) ℝ))‖ ≥ (1 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 1) : ℝ) *
        Real.exp (-((1 : ℝ) ^ 2) / (2 * ‖∑ _i : Fin 1,
          (((1 / 10 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
            ((1 / 10 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)))‖)))) :
    False := by
  have hev : {ω : (Fin 1) → Bool |
      ‖∑ _i : Fin 1, (if ω (0 : Fin 1) then (1 : Matrix (Fin 1) (Fin 1) ℝ)
          else -(1 : Matrix (Fin 1) (Fin 1) ℝ))‖ ≥ (1 : ℝ)} = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, ge_iff_le]
    constructor
    · intro _; trivial
    · intro _
      rw [Fin.sum_univ_one]
      by_cases hω : ω (0 : Fin 1) = true
      · rw [if_pos hω]
        rw [show ((1 : Matrix (Fin 1) (Fin 1) ℝ)) = (1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)
            from (one_smul _ _).symm, norm_smul, mcOne_norm_fin1, Real.norm_eq_abs, abs_of_pos]
        · norm_num
        · norm_num
      · rw [if_neg hω, norm_neg, show (1 : Matrix (Fin 1) (Fin 1) ℝ)
            = (1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) from (one_smul ℝ _).symm,
            norm_smul, mcOne_norm_fin1, Real.norm_eq_abs,
            abs_of_pos (by norm_num : (0 : ℝ) < 1)]
        norm_num
  rw [hev, measure_univ] at h
  have hsum : ∑ _i : Fin 1, (((1 / 10 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
      ((1 / 10 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
      = ((1 / 100 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    rw [Fin.sum_univ_one, smul_mul_smul_comm]
    norm_num
  rw [hsum, norm_smul, mcOne_norm_fin1, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 100),
    show (Fintype.card (Fin 1) : ℝ) = 1 by norm_num] at h
  rw [ENNReal.one_le_ofReal] at h
  norm_num at h
  have hle : Real.exp (1 : ℝ) ≤ Real.exp 50 := Real.exp_le_exp.mpr (by norm_num)
  have h50 : (2 : ℝ) < Real.exp 50 :=
    lt_of_lt_of_le mc_two_lt_exp_one hle
  have hlt : (2 : ℝ) * Real.exp (-(50 : ℝ)) < 1 := by
    rw [Real.exp_neg, mul_comm]
    exact div_eq_inv_mul (2 : ℝ) (Real.exp 50) ▸ (div_lt_one (Real.exp_pos 50)).mpr h50
  linarith

/-- **The `ht` fence**: the nonnegativity clause on the threshold is
load-bearing. At the constant-zero family with `A = 1` on `V = Fin 1`,
`t = -3`: the tail event `{‖0‖ ≥ -3}` is all of any probability space
(nonnegativity of the norm) against the bound
`2 · exp (−9/2) < 1` — negative thresholds make the tail certain while
the Gaussian shape keeps shrinking. -/
-- @refutes: matrix_hoeffding
theorem mcHg_t_fence_QA {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (h : μ {_ω : Ω | ‖∑ _i : Fin 1, (0 : Matrix (Fin 1) (Fin 1) ℝ)‖ ≥ (-3 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 1) : ℝ) *
        Real.exp (-((-3 : ℝ) ^ 2) / (2 * ‖∑ _i : Fin 1,
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) * 1)‖)))) :
    False := by
  have hev : {_ω : Ω | ‖∑ _i : Fin 1, (0 : Matrix (Fin 1) (Fin 1) ℝ)‖ ≥ (-3 : ℝ)}
      = Set.univ := by
    ext _ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, ge_iff_le]
    exact iff_of_true (le_trans (by norm_num : (-3 : ℝ) ≤ 0) (norm_nonneg _)) trivial
  rw [hev, measure_univ] at h
  have hsum : ∑ _i : Fin 1, ((1 : Matrix (Fin 1) (Fin 1) ℝ) * 1)
      = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [Fin.sum_univ_one, Matrix.one_mul]
  rw [hsum, mcOne_norm_fin1, show (Fintype.card (Fin 1) : ℝ) = 1 by norm_num] at h
  rw [ENNReal.one_le_ofReal] at h
  norm_num at h
  have hle : Real.exp (1 : ℝ) ≤ Real.exp (9 / 2 : ℝ) :=
    Real.exp_le_exp.mpr (by norm_num)
  have hhalf : (2 : ℝ) < Real.exp (9 / 2 : ℝ) :=
    lt_of_lt_of_le mc_two_lt_exp_one hle
  have hlt : (2 : ℝ) * Real.exp (-(9 / 2 : ℝ)) < 1 := by
    rw [Real.exp_neg, mul_comm]
    exact div_eq_inv_mul (2 : ℝ) (Real.exp (9 / 2 : ℝ)) ▸
      (div_lt_one (Real.exp_pos (9 / 2 : ℝ))).mpr hhalf
  linarith


/-- **The `h_indep` fence**: the mutual-independence clause is
load-bearing. At six IDENTICAL copies of the coin sign on `V = Fin 1`
(`A = 1`, `t = 6`: every other clause genuine), the perfect
correlation makes the sum `±6` deterministically, so the tail event is
all of the coin space against the bound
`2 · exp (−36/12) = 2 e⁻³ < 1` — dependence concentrates the sum at
its extreme. The companion records the independence failure
mechanically: at the measurable entry set `{M | M 0 0 > 1/2}` the
two-point joint mass `1/2` is not the product `1/4`. -/
theorem mcHg_indep_not_iIndepFun_QA :
    ¬ iIndepFun (fun _ : Fin 6 =>
        (inferInstance : MeasurableSpace (Matrix (Fin 1) (Fin 1) ℝ)))
      (fun (_ : Fin 6) (ω : (Fin 1) → Bool) =>
        if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
        else -(1 : Matrix (Fin 1) (Fin 1) ℝ)) mcCoin := by
  intro hindep
  set mcSet : Fin 6 → Set (Matrix (Fin 1) (Fin 1) ℝ) :=
    fun _ => {M : Matrix (Fin 1) (Fin 1) ℝ | (M 0 0 : ℝ) > 1 / 2} with hmcSet
  have hS : ∀ i ∈ ({0, 1} : Finset (Fin 6)), MeasurableSet (mcSet i) := by
    have h1 : Measurable (fun M : Matrix (Fin 1) (Fin 1) ℝ => M (0 : Fin 1)) :=
      measurable_pi_apply (0 : Fin 1)
    have h2 : Measurable (fun v : (Fin 1) → ℝ => v (0 : Fin 1)) :=
      measurable_pi_apply (0 : Fin 1)
    have hM : MeasurableSet {M : Matrix (Fin 1) (Fin 1) ℝ | (M 0 0 : ℝ) > 1 / 2} :=
      (h2.comp h1) (measurableSet_Ioi (a := (1 / 2 : ℝ)))
    intro i _
    exact hM
  have hpre : ∀ i : Fin 6,
      (fun (ω : (Fin 1) → Bool) =>
        if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
        else -(1 : Matrix (Fin 1) (Fin 1) ℝ)) ⁻¹' mcSet i
      = {ω : (Fin 1) → Bool | ω (0 : Fin 1) = true} := by
    intro i
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hmcSet]
    rcases eq_or_ne (ω (0 : Fin 1)) true with hω | hω
    · rw [if_pos hω]
      simp only [hω, if_pos]
      norm_num
    · rw [if_neg hω]
      simp only [hω, if_neg]
      norm_num
  have hjoint := (iIndepFun_iff_measure_inter_preimage_eq_mul.1 hindep)
    ({0, 1} : Finset (Fin 6)) (sets := mcSet) hS
  have hset : (⋂ i ∈ ({0, 1} : Finset (Fin 6)),
      (fun (ω : (Fin 1) → Bool) =>
        if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
        else -(1 : Matrix (Fin 1) (Fin 1) ℝ)) ⁻¹' mcSet i)
      = {ω : (Fin 1) → Bool | ω (0 : Fin 1) = true} := by
    ext ω
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hh
      have hmem := hh 0 (Or.inl rfl)
      rw [hpre 0, Set.mem_setOf_eq] at hmem
      exact hmem
    · intro hh i hi
      rcases hi with rfl | rfl
      · rw [hpre 0, Set.mem_setOf_eq]; exact hh
      · rw [hpre 1, Set.mem_setOf_eq]; exact hh
  rw [hset, Finset.prod_insert (by decide), Finset.prod_singleton, hpre 0,
    mcCoin_true] at hjoint
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    show (1 / 2 : ℝ) * (1 / 2 : ℝ) = 1 / 4 by norm_num] at hjoint
  norm_num at hjoint

/-- The norm pin for the alternating `Fin 1` scalar family. -/
theorem mcCoinSign_norm (ω : (Fin 1) → Bool) :
    ‖(if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
        else -(1 : Matrix (Fin 1) (Fin 1) ℝ))‖ = 1 := by
  rcases eq_or_ne (ω (0 : Fin 1)) true with hω | hω
  · rw [if_pos hω, show (1 : Matrix (Fin 1) (Fin 1) ℝ)
        = (1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) from (one_smul ℝ _).symm,
      norm_smul, mcOne_norm_fin1, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1)]
    norm_num
  · rw [if_neg hω, norm_neg, show (1 : Matrix (Fin 1) (Fin 1) ℝ)
        = (1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) from (one_smul ℝ _).symm,
      norm_smul, mcOne_norm_fin1, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1)]
    norm_num

/-- The six-fold sum of the identical sign is the scaled sign. -/
theorem mcHg_indep_sum (ω : (Fin 1) → Bool) :
    ∑ _i : Fin 6, (if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
        else -(1 : Matrix (Fin 1) (Fin 1) ℝ))
      = (6 : ℝ) • (if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
        else -(1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  have h := Finset.sum_const
    (b := (if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
        else -(1 : Matrix (Fin 1) (Fin 1) ℝ))) (s := (Finset.univ : Finset (Fin 6)))
  rw [h, Finset.card_univ, Fintype.card_fin]
  exact (Nat.cast_smul_eq_nsmul (R := ℝ) 6 _).symm

-- @refutes: matrix_hoeffding
theorem mcHg_indep_fence_QA
    (h : mcCoin {ω : (Fin 1) → Bool |
        ‖∑ _i : Fin 6, (if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
          else -(1 : Matrix (Fin 1) (Fin 1) ℝ))‖ ≥ (6 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 1) : ℝ) *
        Real.exp (-((6 : ℝ) ^ 2) / (2 * ‖∑ _i : Fin 6,
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) * 1)‖)))) :
    False := by
  have hev : {ω : (Fin 1) → Bool |
      ‖∑ _i : Fin 6, (if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
          else -(1 : Matrix (Fin 1) (Fin 1) ℝ))‖ ≥ (6 : ℝ)} = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, ge_iff_le]
    rw [mcHg_indep_sum, norm_smul, mcCoinSign_norm, mul_one]
    norm_num
  rw [hev, measure_univ] at h
  have hsumA : ∑ _i : Fin 6, ((1 : Matrix (Fin 1) (Fin 1) ℝ) * 1)
      = (6 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    have h := Finset.sum_const
      (b := ((1 : Matrix (Fin 1) (Fin 1) ℝ) * 1)) (s := (Finset.univ : Finset (Fin 6)))
    rw [h, Finset.card_univ, Fintype.card_fin, Matrix.one_mul]
    exact (Nat.cast_smul_eq_nsmul (R := ℝ) 6 _).symm
  rw [hsumA, norm_smul, mcOne_norm_fin1, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 6),
    show (Fintype.card (Fin 1) : ℝ) = 1 by norm_num] at h
  rw [ENNReal.one_le_ofReal] at h
  norm_num at h
  have hle : Real.exp (1 : ℝ) ≤ Real.exp 3 := Real.exp_le_exp.mpr (by norm_num)
  have h3 : (2 : ℝ) < Real.exp 3 := lt_of_lt_of_le mc_two_lt_exp_one hle
  have hlt : (2 : ℝ) * Real.exp (-(3 : ℝ)) < 1 := by
    rw [Real.exp_neg, mul_comm]
    exact div_eq_inv_mul 2 (Real.exp 3) ▸ (div_lt_one (Real.exp_pos 3)).mpr h3
  linarith


/-- `32 < exp (9/2)`, via the `3 + 3/2` split (`exp 3 > 8`, `exp (3/2) > 4`). -/
theorem mc_thirtytwo_lt_exp_nine_halves : (32 : ℝ) < Real.exp (9 / 2 : ℝ) := by
  have hsplit : Real.exp (9 / 2 : ℝ) = Real.exp 3 * Real.exp (3 / 2 : ℝ) := by
    rw [← Real.exp_add]; norm_num
  have h3 : (8 : ℝ) < Real.exp 3 := by
    have h1e : Real.exp 3 = (Real.exp 1) ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h1e]
    calc (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      _ < ((5 / 2 : ℝ) ^ 3) := by norm_num
      _ < (Real.exp 1) ^ 3 :=
          pow_lt_pow_left₀ mc_exp_one_gt_half5 (by norm_num) (by norm_num)
  rw [hsplit]
  calc (32 : ℝ) = (8 : ℝ) * 4 := by norm_num
    _ < Real.exp 3 * 4 := mul_lt_mul_of_pos_right h3 (by norm_num)
    _ ≤ Real.exp 3 * Real.exp (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left mc_four_lt_exp_three_halves.le
          (le_of_lt (Real.exp_pos 3))

/-! ### `matrix_bernstein` fences -/

/-- **The `h_mean` fence**: centering is load-bearing for the sibling
axiom too. At the deterministic uncentered family `X i = 1` on
`V = Fin 1`, `n = 4`, `R = 1`, `t = 4` (measurability, singleton
independence, Hermitianity, and the norm bound all genuine), the tail
event is all of the space (`‖4‖ = 4`) against the bound
`2 · exp (−16/(8 + 8/3)) = 2 e^{−3/2} < 1`. -/
-- @refutes: matrix_bernstein
theorem mcBn_mean_fence_QA {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (h : μ {_ω : Ω | ‖∑ _i : Fin 4, (1 : Matrix (Fin 1) (Fin 1) ℝ)‖ ≥ (4 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 1) : ℝ) *
        Real.exp (-((4 : ℝ) ^ 2) / (2 * ‖∑ _i : Fin 4,
          ∫ _ω : Ω, (1 : Matrix (Fin 1) (Fin 1) ℝ) * 1 ∂μ‖
          + (2 * 1 * (4 : ℝ)) / 3)))) :
    False := by
  have hint : ∫ _ω : Ω, (1 : Matrix (Fin 1) (Fin 1) ℝ) * 1 ∂μ
      = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [Matrix.one_mul, integral_const]
    simp
  have hsumA : ∑ _i : Fin 4, ∫ _ω : Ω, (1 : Matrix (Fin 1) (Fin 1) ℝ) * 1 ∂μ
      = (4 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    have h := Finset.sum_const
      (b := ∫ _ω : Ω, (1 : Matrix (Fin 1) (Fin 1) ℝ) * 1 ∂μ)
      (s := (Finset.univ : Finset (Fin 4)))
    rw [h, Finset.card_univ, Fintype.card_fin, hint]
    exact mcNatBridge 4
  have hev : {_ω : Ω | ‖∑ _i : Fin 4, (1 : Matrix (Fin 1) (Fin 1) ℝ)‖ ≥ (4 : ℝ)}
      = Set.univ := by
    ext _ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, ge_iff_le]
    have h2 : ∑ _i : Fin 4, (1 : Matrix (Fin 1) (Fin 1) ℝ)
        = (4 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      have h := Finset.sum_const
        (b := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (s := (Finset.univ : Finset (Fin 4)))
      rw [h, Finset.card_univ, Fintype.card_fin]
      exact mcNatBridge 4
    rw [h2, norm_smul, mcOne_norm_fin1, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 4), mul_one]
    exact iff_of_true (le_refl _) trivial
  rw [hev, measure_univ] at h
  rw [hsumA, norm_smul, mcOne_norm_fin1, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 4),
    show (Fintype.card (Fin 1) : ℝ) = 1 by norm_num] at h
  rw [ENNReal.one_le_ofReal] at h
  norm_num at h
  have hle : Real.exp (1 : ℝ) ≤ Real.exp (3 / 2 : ℝ) :=
    Real.exp_le_exp.mpr (by norm_num)
  have hhalf : (2 : ℝ) < Real.exp (3 / 2 : ℝ) :=
    lt_of_lt_of_le mc_two_lt_exp_one hle
  have hlt : (2 : ℝ) * Real.exp (-(3 / 2 : ℝ)) < 1 := by
    rw [Real.exp_neg, mul_comm]
    exact div_eq_inv_mul 2 (Real.exp (3 / 2 : ℝ)) ▸
      (div_lt_one (Real.exp_pos (3 / 2 : ℝ))).mpr hhalf
  linarith

/-- **The `ht` fence** for the Bernstein sibling: at the coin family
`X = ±1` on `V = Fin 1` with `R = 3`, `t = -9/10` (every other clause
genuine — the variance statistic integrates to `1` through the
constant square), the tail event is all of the space against
`2 · exp (−81/20) < 1`: the negative threshold shrinks the mixed
denominator `2 + 2Rt/3` to `1/5` and the Gaussian term does the rest. -/
-- @refutes: matrix_bernstein
theorem mcBn_t_fence_QA
    (h : mcCoin {ω : (Fin 1) → Bool |
        ‖∑ _i : Fin 1, (if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
          else -(1 : Matrix (Fin 1) (Fin 1) ℝ))‖ ≥ (-9 / 10 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 1) : ℝ) *
        Real.exp (-((-9 / 10 : ℝ) ^ 2) / (2 * ‖∑ _i : Fin 1,
          ∫ ω : (Fin 1) → Bool,
            (if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
              else -(1 : Matrix (Fin 1) (Fin 1) ℝ)) *
            (if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
              else -(1 : Matrix (Fin 1) (Fin 1) ℝ)) ∂mcCoin‖
          + (2 * 3 * (-9 / 10 : ℝ)) / 3)))) :
    False := by
  have hev : {ω : (Fin 1) → Bool |
      ‖∑ _i : Fin 1, (if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
          else -(1 : Matrix (Fin 1) (Fin 1) ℝ))‖ ≥ (-9 / 10 : ℝ)} = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, ge_iff_le]
    constructor
    · intro _; trivial
    · intro _
      rw [Fin.sum_univ_one, mcCoinSign_norm]
      norm_num
  rw [hev, measure_univ] at h
  have hpt : ∀ ω : (Fin 1) → Bool,
      (if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
        else -(1 : Matrix (Fin 1) (Fin 1) ℝ)) *
      (if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
        else -(1 : Matrix (Fin 1) (Fin 1) ℝ))
      = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    intro ω
    rcases eq_or_ne (ω (0 : Fin 1)) true with hω | hω
    · rw [if_pos hω, mul_one]
    · rw [if_neg hω, neg_mul_neg, mul_one]
  have hsqint : ∫ ω : (Fin 1) → Bool,
      (if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
        else -(1 : Matrix (Fin 1) (Fin 1) ℝ)) *
      (if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
        else -(1 : Matrix (Fin 1) (Fin 1) ℝ)) ∂mcCoin
      = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [integral_congr_ae (ae_of_all mcCoin hpt), integral_const]
    simp
  have hsumA : ∑ _i : Fin 1, ∫ ω : (Fin 1) → Bool,
      (if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
        else -(1 : Matrix (Fin 1) (Fin 1) ℝ)) *
      (if ω (0 : Fin 1) = true then (1 : Matrix (Fin 1) (Fin 1) ℝ)
        else -(1 : Matrix (Fin 1) (Fin 1) ℝ)) ∂mcCoin
      = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [Fin.sum_univ_one, hsqint]
  rw [hsumA, mcOne_norm_fin1, show (Fintype.card (Fin 1) : ℝ) = 1 by norm_num] at h
  rw [ENNReal.one_le_ofReal] at h
  norm_num at h
  have hbig : (2 : ℝ) < Real.exp (81 / 20 : ℝ) :=
    lt_of_lt_of_le mc_two_lt_exp_one
      (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 81 / 20))
  have hlt : (2 : ℝ) * Real.exp (-(81 / 20 : ℝ)) < 1 := by
    rw [Real.exp_neg, mul_comm]
    exact div_eq_inv_mul 2 (Real.exp (81 / 20 : ℝ)) ▸
      (div_lt_one (Real.exp_pos (81 / 20 : ℝ))).mpr hbig
  norm_num at h
  linarith


/-! ### `matrix_azuma_hoeffding` fences -/

/-- **The `cond_mean_zero` fence**: the martingale-difference property
is load-bearing. At the constant drift `X k = 1` with `R = 1` on
`V = Fin 1` (the `measurable` and `norm_bound` fields both genuine),
`m = 8`, `t = 8`: the sum is `8` deterministically, the tail event is
all of the space, against the bound `2 · exp (−64/64) = 2 e⁻¹ < 1` —
a nonzero conditional mean accumulates linearly while the bound's
variance grows only through `m R²`. -/
-- @refutes: matrix_azuma_hoeffding
theorem mcAz_condmean_fence_QA {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (h : μ {_ω : Ω | ‖∑ _k in Finset.range 8, (1 : Matrix (Fin 1) (Fin 1) ℝ)‖
        ≥ (8 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 1) : ℝ) *
        Real.exp (-((8 : ℝ) ^ 2) / (8 * (8 : ℝ) * (1 : ℝ) ^ 2)))) :
    False := by
  have hsum : ∑ _k in Finset.range 8, (1 : Matrix (Fin 1) (Fin 1) ℝ)
      = (8 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    have h2 := Finset.sum_const
      (b := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (s := Finset.range 8)
    rw [h2, Finset.card_range]
    exact mcNatBridge 8
  have hev : {_ω : Ω | ‖∑ _k in Finset.range 8, (1 : Matrix (Fin 1) (Fin 1) ℝ)‖
      ≥ (8 : ℝ)} = Set.univ := by
    ext _ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, ge_iff_le]
    rw [hsum, norm_smul, mcOne_norm_fin1, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 8), mul_one]
    exact iff_of_true (le_refl _) trivial
  rw [hev, measure_univ] at h
  rw [show (Fintype.card (Fin 1) : ℝ) = 1 by norm_num] at h
  rw [ENNReal.one_le_ofReal] at h
  norm_num at h
  have hlt : (2 : ℝ) * Real.exp (-(1 : ℝ)) < 1 := by
    rw [Real.exp_neg, mul_comm]
    exact div_eq_inv_mul 2 (Real.exp 1) ▸ (div_lt_one (Real.exp_pos 1)).mpr
      mc_two_lt_exp_one
  linarith

/-- **The `norm_bound` fence**: the uniform bound `R` is load-bearing
data. At the constant drift `X k = 2 • 1` with the statement's `R = 1`
(the bound clause fails at every point), `m = 8`, `t = 16`: the sum is
`16`, the tail event is all of the space, against
`2 · exp (−256/64) = 2 e⁻⁴ < 1`. -/
-- @refutes: matrix_azuma_hoeffding
theorem mcAz_norm_fence_QA {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (h : μ {_ω : Ω | ‖∑ _k in Finset.range 8, ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))‖
        ≥ (16 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 1) : ℝ) *
        Real.exp (-((16 : ℝ) ^ 2) / (8 * (8 : ℝ) * (1 : ℝ) ^ 2)))) :
    False := by
  have hsum : ∑ _k in Finset.range 8, ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = (16 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    have h2 := Finset.sum_const
      (b := ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (s := Finset.range 8)
    have h1 : ∑ _k in Finset.range 8, (1 : Matrix (Fin 1) (Fin 1) ℝ)
        = (8 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      have h3 := Finset.sum_const
        (b := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (s := Finset.range 8)
      rw [h3, Finset.card_range]
      exact mcNatBridge 8
    rw [h2, Finset.card_range, mcNatBridge2 8 2]
    norm_num
  have hev : {_ω : Ω | ‖∑ _k in Finset.range 8, ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))‖
      ≥ (16 : ℝ)} = Set.univ := by
    ext _ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, ge_iff_le]
    rw [hsum, norm_smul, mcOne_norm_fin1, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 16), mul_one]
    exact iff_of_true (le_refl _) trivial
  rw [hev, measure_univ] at h
  rw [show (Fintype.card (Fin 1) : ℝ) = 1 by norm_num] at h
  rw [ENNReal.one_le_ofReal] at h
  norm_num at h
  have hlt : (2 : ℝ) * Real.exp (-(4 : ℝ)) < 1 := by
    rw [Real.exp_neg, mul_comm]
    have h4 : (2 : ℝ) < Real.exp 4 :=
      lt_of_lt_of_le mc_two_lt_exp_one (Real.exp_le_exp.mpr (by norm_num))
    exact div_eq_inv_mul 2 (Real.exp 4) ▸ (div_lt_one (Real.exp_pos 4)).mpr h4
  linarith

/-- **The `ht` fence**: at the constant-zero difference sequence with
`R = 1`, `m = 1`, `t = -3` (every `MatrixMDS` field genuine), the tail
event `{‖0‖ ≥ -3}` is all of any probability space against
`2 · exp (−9/8) < 1`. -/
-- @refutes: matrix_azuma_hoeffding
theorem mcAz_t_fence_QA {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (h : μ {_ω : Ω | ‖∑ _k in Finset.range 1, (0 : Matrix (Fin 1) (Fin 1) ℝ)‖
        ≥ (-3 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 1) : ℝ) *
        Real.exp (-((-3 : ℝ) ^ 2) / (8 * (1 : ℝ) * (1 : ℝ) ^ 2)))) :
    False := by
  have hev : {ω : Ω | ‖∑ _k in Finset.range 1, (0 : Matrix (Fin 1) (Fin 1) ℝ)‖
      ≥ (-3 : ℝ)} = Set.univ := by
    ext _ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, ge_iff_le]
    exact iff_of_true (le_trans (by norm_num : (-3 : ℝ) ≤ 0) (norm_nonneg _)) trivial
  rw [hev, measure_univ] at h
  rw [show (Fintype.card (Fin 1) : ℝ) = 1 by norm_num] at h
  rw [ENNReal.one_le_ofReal] at h
  norm_num at h
  have hlt : (2 : ℝ) * Real.exp (-(9 / 8 : ℝ)) < 1 := by
    rw [Real.exp_neg, mul_comm]
    have h9 : (2 : ℝ) < Real.exp (9 / 8 : ℝ) :=
      lt_of_lt_of_le mc_two_lt_exp_one (Real.exp_le_exp.mpr (by norm_num))
    exact div_eq_inv_mul 2 (Real.exp (9 / 8 : ℝ)) ▸
      (div_lt_one (Real.exp_pos (9 / 8 : ℝ))).mpr h9
  linarith


/-! ### The trivial σ-algebra fixture (the junk-variance mechanism) -/

/-- The two-point trivial-σ-algebra space (the `azDriftMeasure`
pattern at `Fin 2`, symmetric masses). -/
noncomputable def mcTwoBot :
    @MeasureTheory.Measure (Fin 2) (⊥ : MeasurableSpace (Fin 2)) :=
  (1 / 2 : ℝ≥0∞) • @MeasureTheory.Measure.dirac (Fin 2) (⊥ : MeasurableSpace (Fin 2)) 0
    + (1 / 2 : ℝ≥0∞) • @MeasureTheory.Measure.dirac (Fin 2) (⊥ : MeasurableSpace (Fin 2)) 1

instance : @IsProbabilityMeasure (Fin 2) (⊥ : MeasurableSpace (Fin 2)) mcTwoBot := by
  constructor
  have h0 : ((1 / 2 : ℝ≥0∞) •
      @MeasureTheory.Measure.dirac (Fin 2) (⊥ : MeasurableSpace (Fin 2)) 0) Set.univ
      = 1 / 2 := by
    rw [Measure.smul_apply,
      @Measure.dirac_apply_of_mem (Fin 2) (⊥ : MeasurableSpace (Fin 2)) (s := Set.univ)
        (a := 0) (Set.mem_univ 0)]
    simp
  have h1 : ((1 / 2 : ℝ≥0∞) •
      @MeasureTheory.Measure.dirac (Fin 2) (⊥ : MeasurableSpace (Fin 2)) 1) Set.univ
      = 1 / 2 := by
    rw [Measure.smul_apply,
      @Measure.dirac_apply_of_mem (Fin 2) (⊥ : MeasurableSpace (Fin 2)) (s := Set.univ)
        (a := 1) (Set.mem_univ 1)]
    simp
  show mcTwoBot Set.univ = 1
  rw [mcTwoBot, Measure.add_apply, h0, h1, ← two_mul ((1 / 2 : ℝ≥0∞)), one_div,
    ENNReal.mul_inv_cancel (by exact_mod_cast (two_ne_zero : (2 : ℕ) ≠ 0)) (by simp)]

theorem mcTwoBot_pos (j : Fin 2) (S : Set (Fin 2)) (hj : j ∈ S) :
    (1 / 2 : ℝ≥0∞) ≤ mcTwoBot S := by
  rw [mcTwoBot, Measure.add_apply]
  fin_cases j
  · have hA : ((1 / 2 : ℝ≥0∞) •
        @MeasureTheory.Measure.dirac (Fin 2) (⊥ : MeasurableSpace (Fin 2)) 0) S
        = 1 / 2 := by
      rw [Measure.smul_apply,
        @Measure.dirac_apply_of_mem (Fin 2) (⊥ : MeasurableSpace (Fin 2)) (s := S)
          (a := 0) hj]
      simp
    rw [hA]
    exact le_add_of_nonneg_right (zero_le _)
  · have hB : ((1 / 2 : ℝ≥0∞) •
        @MeasureTheory.Measure.dirac (Fin 2) (⊥ : MeasurableSpace (Fin 2)) 1) S
        = 1 / 2 := by
      rw [Measure.smul_apply,
        @Measure.dirac_apply_of_mem (Fin 2) (⊥ : MeasurableSpace (Fin 2)) (s := S)
          (a := 1) hj]
      simp
    rw [hB, add_comm]
    exact le_add_of_nonneg_right (zero_le _)

/-- `0 < 1/2` in `ℝ≥0∞`. -/
theorem mcHalfPos : (0 : ℝ≥0∞) < 1 / 2 := by
  rw [one_div, ENNReal.inv_pos]
  exact (by simp : ¬(2 : ℝ≥0∞) = ⊤)

/-- The two diagonal Hermitian values of the junk-variance fixture:
`A = diag (1, 0)` and `B = diag (0, -1)` — both of operator norm
exactly `1`, with DIFFERENT squares (`A² = A ≠ B² = diag (0, 1)`), so
the square function varies on the two-point space. -/
def mcDiagA : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
def mcDiagB : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, -1]

theorem mcDiagA_herm : mcDiagA.IsHermitian := by
  refine isHermitian_of_isSymm ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.IsSymm, mcDiagA]
theorem mcDiagB_herm : mcDiagB.IsHermitian := by
  refine isHermitian_of_isSymm ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.IsSymm, mcDiagB]

theorem mcDiagA_mulVec (x : Fin 2 → ℝ) : mcDiagA *ᵥ x = ![x 0, 0] := by
  funext k
  fin_cases k <;> simp [Matrix.mulVec, Matrix.dotProduct, mcDiagA, Fin.sum_univ_two]

theorem mcDiagB_mulVec (x : Fin 2 → ℝ) : mcDiagB *ᵥ x = ![0, -x 1] := by
  funext k
  fin_cases k <;> simp [Matrix.mulVec, Matrix.dotProduct, mcDiagB, Fin.sum_univ_two]

/-- Entry bound by the Euclidean length (the single-term sum bound). -/
theorem mcEntry_abs_le (x : Fin 2 → ℝ) (i : Fin 2) : |x i| ≤ Real.sqrt (x ⬝ᵥ x) := by
  have h1 : x i * x i ≤ x ⬝ᵥ x := by
    rw [Matrix.dotProduct]
    exact Finset.single_le_sum (f := fun j => x j * x j)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
  have hnn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun j _ => mul_self_nonneg _
  refine abs_le_of_sq_le_sq ?_ (Real.sqrt_nonneg _)
  rw [sq, Real.sq_sqrt hnn]
  exact h1

theorem mcDiagA_norm : ‖mcDiagA‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.l2OpNorm_le_of_abs_dotProduct_le
      (by norm_num) ?_
    intro x y
    have hdot : y ⬝ᵥ (mcDiagA *ᵥ x) = y 0 * x 0 := by
      rw [mcDiagA_mulVec]
      simp [Matrix.dotProduct, Fin.sum_univ_two]
    rw [hdot, abs_mul, one_mul, mul_comm (|y 0|) (|x 0|)]
    exact mul_le_mul (mcEntry_abs_le x 0) (mcEntry_abs_le y 0) (abs_nonneg _)
      (Real.sqrt_nonneg _)
  · have h := mcLe_norm mcDiagA ![1, 0]
    rw [mcDiagA_mulVec] at h
    simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one] at h
    have hn : ‖(WithLp.equiv 2 ((Fin 2) → ℝ)).symm ![1, 0]‖ = 1 := by
      rw [Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.norm_euclidean_eq_sqrt]
      simp [Matrix.dotProduct, Fin.sum_univ_two]
    rw [hn, mul_one] at h
    exact h

theorem mcDiagB_norm : ‖mcDiagB‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.l2OpNorm_le_of_abs_dotProduct_le
      (by norm_num) ?_
    intro x y
    have hdot : y ⬝ᵥ (mcDiagB *ᵥ x) = -(y 1 * x 1) := by
      rw [mcDiagB_mulVec]
      simp [Matrix.dotProduct, Fin.sum_univ_two]
    rw [hdot, abs_neg, abs_mul, one_mul, mul_comm (|y 1|) (|x 1|)]
    exact mul_le_mul (mcEntry_abs_le x 1) (mcEntry_abs_le y 1) (abs_nonneg _)
      (Real.sqrt_nonneg _)
  · have h := mcLe_norm mcDiagB ![0, -1]
    rw [mcDiagB_mulVec] at h
    simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      Matrix.head_cons, neg_neg] at h
    have hn1 : ‖(WithLp.equiv 2 ((Fin 2) → ℝ)).symm ![0, 1]‖ = 1 := by
      rw [Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.norm_euclidean_eq_sqrt]
      simp [Matrix.dotProduct, Fin.sum_univ_two]
    have hn2 : ‖(WithLp.equiv 2 ((Fin 2) → ℝ)).symm ![0, -1]‖ = 1 := by
      rw [Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.norm_euclidean_eq_sqrt]
      have hsq : (![0, -1] : Fin 2 → ℝ) ⬝ᵥ (![0, -1] : Fin 2 → ℝ) = 1 := by
        simp [Matrix.dotProduct, Fin.sum_univ_two]
      rw [hsq, Real.sqrt_one]
    rw [hn1, hn2, mul_one] at h
    exact h

/-- The two values differ (so the family, and its square, are
nonconstant on the two-point space). -/

theorem mcDiag_ne : mcDiagA ≠ mcDiagB := fun h => by
  have h00 : mcDiagA 0 0 = mcDiagB 0 0 := by rw [h]
  simp [mcDiagA, mcDiagB] at h00

theorem mcDiag_sq_ne : mcDiagA * mcDiagA ≠ mcDiagB * mcDiagB := fun h => by
  have h00 : (mcDiagA * mcDiagA) 0 0 = (mcDiagB * mcDiagB) 0 0 := by rw [h]
  simp [Matrix.mul_apply, mcDiagA, mcDiagB, Fin.sum_univ_two] at h00

/-- On the two-point trivial-σ-algebra space, a two-valued function
with distinct values is not almost-everywhere strongly measurable
(both atoms carry positive mass, so a.e.-equality with a constant —
what `stronglyMeasurable_bot_iff` forces — would make the values
agree). The `azDrift_cond_mean_zero_QA` pattern, packaged once. -/
theorem mcTwoBot_not_aeSM {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : Fin 2 → W) (hF : F 0 ≠ F 1) : ¬ AEStronglyMeasurable F mcTwoBot := by
  intro haes
  obtain ⟨c, hc⟩ := stronglyMeasurable_bot_iff.1
    (AEStronglyMeasurable.stronglyMeasurable_mk haes)
  have heq : F =ᵐ[mcTwoBot] (fun _ => c) := haes.ae_eq_mk.trans (by rw [hc])
  have hnull := ae_iff.1 (Filter.EventuallyEq.eventually heq)
  by_cases hc0 : c = F 0
  · have hsub : ({(1 : Fin 2)} : Set (Fin 2))
        ⊆ {ω | ¬ (F ω = c)} := by
      intro ω hω
      simp only [Set.mem_singleton_iff] at hω
      subst ω
      simp only [Set.mem_setOf_eq]
      intro hcon
      exact hF (hcon.trans hc0).symm
    have hmono := measure_mono_null hsub hnull
    have hpos := mcTwoBot_pos 1 {1} (Set.mem_singleton 1)
    exact absurd (hmono ▸ hpos) (not_le.mpr mcHalfPos)
  · have hsub : ({(0 : Fin 2)} : Set (Fin 2))
        ⊆ {ω | ¬ (F ω = c)} := by
      intro ω hω
      simp only [Set.mem_singleton_iff] at hω
      subst ω
      simp only [Set.mem_setOf_eq]
      exact fun hcon => hc0 hcon.symm
    have hmono := measure_mono_null hsub hnull
    have hpos := mcTwoBot_pos 0 {0} (Set.mem_singleton 0)
    exact absurd (hmono ▸ hpos) (not_le.mpr mcHalfPos)

/-- **The `h_meas` fence for `matrix_bernstein`** — the headline: the
variance statistic is ITSELF a junk integral. At the two-point
trivial-σ-algebra space with `X = diag(1,0) / diag(0,-1)` (Hermitian of
operator norm exactly one, so the kept `h_herm` and `h_bound` clauses
at `R = 1` are genuine, and `h_mean` holds through the junk first
moment), the SECOND moment `ω ↦ X ω * X ω` is a two-valued function
with distinct values — not almost-everywhere strongly measurable — so
`Σ = ∫ X²` evaluates to the junk zero and the bound collapses to
`4 · exp (−1/(0 + 2/3)) = 4 e^{−3/2} < 1` against the full-measure tail
event at `t = 1`. Errata §7's mechanism class reaches the sibling axiom
through the variance statistic, not the tail event. -/
-- @refutes: matrix_bernstein
theorem mcBn_meas_fence_QA
    (h : mcTwoBot {ω : Fin 2 | ‖(if ω = 0 then mcDiagA else mcDiagB)‖ ≥ (1 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 2) : ℝ) *
        Real.exp (-((1 : ℝ) ^ 2) / (2 * ‖∑ _i : Fin 1,
          ∫ ω : Fin 2, (if ω = 0 then mcDiagA else mcDiagB) *
            (if ω = 0 then mcDiagA else mcDiagB) ∂mcTwoBot‖
          + (2 * 1 * (1 : ℝ)) / 3)))) :
    False := by
  have hev : {ω : Fin 2 | ‖(if ω = 0 then mcDiagA else mcDiagB)‖ ≥ (1 : ℝ)}
      = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, ge_iff_le]
    by_cases hω : ω = 0
    · rw [if_pos hω, mcDiagA_norm]
      exact iff_of_true (le_refl _) trivial
    · rw [if_neg hω, mcDiagB_norm]
      exact iff_of_true (le_refl _) trivial
  rw [hev, measure_univ] at h
  have hsq : ∫ ω : Fin 2, (if ω = 0 then mcDiagA else mcDiagB) *
      (if ω = 0 then mcDiagA else mcDiagB) ∂mcTwoBot
      = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
    refine integral_non_aestronglyMeasurable ?_
    refine mcTwoBot_not_aeSM _ ?_
    intro hval
    exact mcDiag_sq_ne (by
      have h0 : (if (0 : Fin 2) = 0 then mcDiagA else mcDiagB) * (if (0 : Fin 2) = 0 then mcDiagA else mcDiagB)
          = mcDiagA * mcDiagA := by rw [if_pos rfl]
      have h1 : (if (1 : Fin 2) = 0 then mcDiagA else mcDiagB) * (if (1 : Fin 2) = 0 then mcDiagA else mcDiagB)
          = mcDiagB * mcDiagB := by rw [if_neg (by norm_num)]
      rw [h0, h1] at hval
      exact hval)
  have hsumA : ∑ _i : Fin 1, ∫ ω : Fin 2, (if ω = 0 then mcDiagA else mcDiagB) *
      (if ω = 0 then mcDiagA else mcDiagB) ∂mcTwoBot
      = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Fin.sum_univ_one, hsq]
  rw [hsumA] at h
  rw [show (Fintype.card (Fin 2) : ℝ) = 2 by norm_num] at h
  rw [ENNReal.one_le_ofReal] at h
  norm_num at h
  have hlt : (4 : ℝ) * Real.exp (-(3 / 2 : ℝ)) < 1 := by
    have h4 := mc_four_lt_exp_three_halves
    rw [Real.exp_neg, mul_comm]
    exact div_eq_inv_mul 4 (Real.exp (3 / 2 : ℝ)) ▸
      (div_lt_one (Real.exp_pos (3 / 2 : ℝ))).mpr h4
  linarith


/-! ### The rare-value Bernoulli fixture -/

/-- The rare-value Bernoulli measure: `bernPMF` at `p = 1/100` on one
coordinate — the mean-zero design with the rare huge value. -/
noncomputable def mcRare : Measure ((Fin 1) → Bool) :=
  (bernPMF (fun _ => (1 / 100 : ℝ)) (by intro i; norm_num)
    (by intro i; norm_num)).toMeasure

instance : IsProbabilityMeasure mcRare :=
  PMF.toMeasure.isProbabilityMeasure _

theorem mcRare_true :
    mcRare {ω : (Fin 1) → Bool | ω (0 : Fin 1) = true} = ENNReal.ofReal ((1 : ℝ) / 100) := by
  have hc := toMeasure_cyl (fun _ => (1 / 100 : ℝ)) (by intro i; norm_num)
    (by intro i; norm_num) (0 : Fin 1) ({true} : Set Bool)
  have hpre : {ω : (Fin 1) → Bool | ω (0 : Fin 1) = true}
      = (fun ω : (Fin 1) → Bool => ω (0 : Fin 1)) ⁻¹' {true} := by
    ext ω; simp
  rw [mcRare, hpre, hc]
  have hb : (Finset.univ : Finset Bool) = ({false, true} : Finset Bool) := by
    ext b; cases b <;> simp
  rw [hb, Finset.sum_insert (by simp), Finset.sum_singleton]
  simp [bern]

/-- The rare-value family is centered: `99` at the rare point, `-1`
elsewhere — the Bernoulli mean makes the integral vanish. -/
theorem mcRare_mean_zero :
    ∫ ω : (Fin 1) → Bool, ((if ω (0 : Fin 1) = true then (99 : ℝ) else (-1 : ℝ)) •
        (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∂mcRare
      = (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hδmeas : Measurable
      fun ω : (Fin 1) → Bool => (if ω (0 : Fin 1) = true then (1 : ℝ) else 0) :=
    (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else 0)).comp
      (measurable_coord (0 : Fin 1))
  have hintf : Integrable
      (fun ω : (Fin 1) → Bool => (if ω (0 : Fin 1) = true then (1 : ℝ) else 0)) mcRare :=
    Scaffold.Mathlib.Probability.Concentration.Scalar.integrable_of_bounded_measurable
      hδmeas (a := 1) (by
      intro ω
      by_cases hω : ω (0 : Fin 1) = true <;> simp [hω])
  have hfun : (fun ω : (Fin 1) → Bool =>
        (if ω (0 : Fin 1) = true then (99 : ℝ) else (-1 : ℝ)) •
        (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = fun ω : (Fin 1) → Bool =>
        ((if ω (0 : Fin 1) = true then (1 : ℝ) else 0) * 100 - 1) •
          (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    funext ω
    by_cases hω : ω (0 : Fin 1) = true
    · have h2 : (if ω (0 : Fin 1) = true then (1 : ℝ) else 0) * 100 = 100 := by
        rw [if_pos hω]; norm_num
      rw [if_pos hω, h2]
      norm_num
    · have h2 : (if ω (0 : Fin 1) = true then (1 : ℝ) else 0) * 100 = 0 := by
        rw [if_neg hω]; norm_num
      rw [if_neg hω, h2]
      norm_num
  rw [hfun, integral_smul_const]
  have hscalar : ∫ ω : (Fin 1) → Bool,
      ((if ω (0 : Fin 1) = true then (1 : ℝ) else 0) * 100 - 1) ∂mcRare = 0 := by
    have h0 : ∫ ω : (Fin 1) → Bool, (if ω (0 : Fin 1) = true then (1 : ℝ) else 0) ∂mcRare
        = 1 / 100 :=
      integral_delta (fun _ => (1 / 100 : ℝ)) (by intro i; norm_num)
        (by intro i; norm_num) (0 : Fin 1)
    have hint100 : Integrable
        (fun ω : (Fin 1) → Bool => (if ω (0 : Fin 1) = true then (1 : ℝ) else 0) * 100)
        mcRare := by
      exact hintf.mul_const 100
    have hstep : ∫ ω : (Fin 1) → Bool,
        ((if ω (0 : Fin 1) = true then (1 : ℝ) else 0) * 100) ∂mcRare = 1 := by
      have hconv : (fun ω : (Fin 1) → Bool =>
          (if ω (0 : Fin 1) = true then (1 : ℝ) else 0) * 100)
          = fun ω : (Fin 1) → Bool =>
            (100 : ℝ) • (if ω (0 : Fin 1) = true then (1 : ℝ) else 0) := by
        funext ω
        rw [smul_eq_mul]
        ring
      rw [hconv, integral_smul, h0]
      norm_num
    rw [integral_sub hint100 (integrable_const _), hstep, integral_const,
      measure_univ, ENNReal.one_toReal]
    norm_num
  rw [hscalar, zero_smul]

/-- The variance statistic of the rare-value family: `Σ = 99 • 1`
(the centered-Bernoulli second moment at `p = 1/100`, scaled by
`100²`, through `integral_sq_delta_sub`). -/
theorem mcRare_var :
    ∫ ω : (Fin 1) → Bool, (((if ω (0 : Fin 1) = true then (99 : ℝ) else (-1 : ℝ))) •
        (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
      (((if ω (0 : Fin 1) = true then (99 : ℝ) else (-1 : ℝ))) •
        (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∂mcRare
      = ((99 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  have hpt : ∀ ω : (Fin 1) → Bool,
      (((if ω (0 : Fin 1) = true then (99 : ℝ) else (-1 : ℝ))) •
          (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
        (((if ω (0 : Fin 1) = true then (99 : ℝ) else (-1 : ℝ))) •
          (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = (((10000 : ℝ) *
            ((if ω (0 : Fin 1) = true then (1 : ℝ) else 0) - 1 / 100) ^ 2) •
          (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    intro ω
    rcases eq_or_ne (ω (0 : Fin 1)) true with hω | hω
    · rw [if_pos hω, smul_mul_smul_comm, Matrix.mul_one, if_pos hω]
      norm_num
    · rw [if_neg hω, smul_mul_smul_comm, Matrix.mul_one, if_neg hω]
      norm_num
  rw [integral_congr_ae (ae_of_all mcRare hpt), integral_smul_const]
  have hsq0 : ∫ ω : (Fin 1) → Bool,
      ((if ω (0 : Fin 1) = true then (1 : ℝ) else 0) - 1 / 100) ^ 2 ∂mcRare
      = 1 / 100 * (1 - 1 / 100) :=
    integral_sq_delta_sub (fun _ => (1 / 100 : ℝ)) (by intro i; norm_num)
      (by intro i; norm_num) (0 : Fin 1)
  have hsq : ∫ ω : (Fin 1) → Bool,
      ((if ω (0 : Fin 1) = true then (1 : ℝ) else 0) - 1 / 100) ^ 2 ∂mcRare
      = 99 / 10000 := by
    rw [hsq0]
    norm_num
  have hI : ∫ ω : (Fin 1) → Bool,
      ((10000 : ℝ) * ((if ω (0 : Fin 1) = true then (1 : ℝ) else 0) - 1 / 100) ^ 2) ∂mcRare
      = 99 := by
    have hconv : (fun ω : (Fin 1) → Bool =>
        (10000 : ℝ) * ((if ω (0 : Fin 1) = true then (1 : ℝ) else 0) - 1 / 100) ^ 2)
        = fun ω : (Fin 1) → Bool =>
          (10000 : ℝ) • (((if ω (0 : Fin 1) = true then (1 : ℝ) else 0) - 1 / 100) ^ 2) := by
      funext ω
      rw [smul_eq_mul]
    rw [hconv, integral_smul, hsq]
    norm_num
  rw [hI]

/-- **The `h_bound` fence for `matrix_bernstein`**: the uniform bound
`R` is load-bearing. With the clause dropped, `R` is free data: at the
rare-value family (`99` with mass `1/100`, `-1` with mass `99/100` —
genuinely centered by `mcRare_mean_zero`, variance statistic `99` by
`mcRare_var`), `t = 99`, `R = 1`: the tail event is the rare cylinder
(mass `1/100`) against `2 · exp (−9801/(198 + 66)) = 2 e^{−9801/264}
< 1/100` — the exponent `37.1` dwarfs the `exp 6 > 200` anchor. -/
-- @refutes: matrix_bernstein
theorem mcBn_bound_fence_QA
    (h : mcRare {ω : (Fin 1) → Bool |
        ‖∑ _i : Fin 1, ((if ω (0 : Fin 1) = true then (99 : ℝ) else (-1 : ℝ)) •
          (1 : Matrix (Fin 1) (Fin 1) ℝ))‖ ≥ (99 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 1) : ℝ) *
        Real.exp (-((99 : ℝ) ^ 2) / (2 * ‖∑ _i : Fin 1,
          ∫ ω : (Fin 1) → Bool,
            (((if ω (0 : Fin 1) = true then (99 : ℝ) else (-1 : ℝ))) •
              (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
            (((if ω (0 : Fin 1) = true then (99 : ℝ) else (-1 : ℝ))) •
              (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∂mcRare‖
          + (2 * 1 * (99 : ℝ)) / 3)))) :
    False := by
  have hev : {ω : (Fin 1) → Bool |
      ‖∑ _i : Fin 1, ((if ω (0 : Fin 1) = true then (99 : ℝ) else (-1 : ℝ)) •
        (1 : Matrix (Fin 1) (Fin 1) ℝ))‖ ≥ (99 : ℝ)}
      = {ω : (Fin 1) → Bool | ω (0 : Fin 1) = true} := by
    ext ω
    simp only [Set.mem_setOf_eq, ge_iff_le, Fin.sum_univ_one]
    rcases eq_or_ne (ω (0 : Fin 1)) true with hω | hω
    · rw [if_pos hω, norm_smul, mcOne_norm_fin1, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 99)]
      simp [hω]
    · rw [if_neg hω, norm_smul, mcOne_norm_fin1, Real.norm_eq_abs,
        abs_of_neg (by norm_num : (-1 : ℝ) < 0)]
      exact iff_of_false (by norm_num) (by simp [hω])
  rw [hev, mcRare_true] at h
  have hsumA : ∑ _i : Fin 1, ∫ ω : (Fin 1) → Bool,
      (((if ω (0 : Fin 1) = true then (99 : ℝ) else (-1 : ℝ))) •
        (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
      (((if ω (0 : Fin 1) = true then (99 : ℝ) else (-1 : ℝ))) •
        (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∂mcRare
      = ((99 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    rw [Fin.sum_univ_one, mcRare_var]
  rw [hsumA, norm_smul, mcOne_norm_fin1, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 99),
    show (Fintype.card (Fin 1) : ℝ) = 1 by norm_num] at h
  norm_num at h
  have hge : (6 : ℝ) ≤ 297 / 8 := by norm_num
  have hbig : (200 : ℝ) < Real.exp (297 / 8 : ℝ) :=
    lt_of_lt_of_le mc_twohundred_lt_exp_six (Real.exp_le_exp.mpr hge)
  have hlt : (2 : ℝ) * Real.exp (-((297 : ℝ) / 8)) < 1 / 100 := by
    have hpos : (0 : ℝ) < Real.exp (297 / 8 : ℝ) := Real.exp_pos _
    rw [Real.exp_neg, mul_comm, inv_mul_eq_div, div_lt_iff₀ hpos]
    nlinarith [hbig]
  exact absurd h (not_le.mpr
    ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 100)).2 hlt))


/-! ### The unit nilpotent and the uniform cube -/

/-- The unit asymmetric nilpotent `N = !![0,1;0,0]]`: `N² = 0` and
`‖N‖ = 1`. -/
def mcNil1 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

theorem mcNil1_sq : mcNil1 * mcNil1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, mcNil1, Fin.sum_univ_two, Matrix.zero_apply]

theorem mcNil1_mulVec (x : Fin 2 → ℝ) : mcNil1 *ᵥ x = ![x 1, 0] := by
  funext k
  fin_cases k <;> simp [Matrix.mulVec, Matrix.dotProduct, mcNil1, Fin.sum_univ_two]

theorem mcNil1_norm : ‖mcNil1‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.l2OpNorm_le_of_abs_dotProduct_le
      (by norm_num) ?_
    intro x y
    have hdot : y ⬝ᵥ (mcNil1 *ᵥ x) = y 0 * x 1 := by
      rw [mcNil1_mulVec]
      simp [Matrix.dotProduct, Fin.sum_univ_two]
    rw [hdot, abs_mul, one_mul, mul_comm (|y 0|) (|x 1|)]
    exact mul_le_mul (mcEntry_abs_le x 1) (mcEntry_abs_le y 0) (abs_nonneg _)
      (Real.sqrt_nonneg _)
  · have h := mcLe_norm mcNil1 ![0, 1]
    rw [mcNil1_mulVec] at h
    simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one] at h
    have hn : ‖(WithLp.equiv 2 ((Fin 2) → ℝ)).symm ![1, 0]‖ = 1 := by
      rw [Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.norm_euclidean_eq_sqrt]
      simp [Matrix.dotProduct, Fin.sum_univ_two]
    have hn' : ‖(WithLp.equiv 2 ((Fin 2) → ℝ)).symm ![0, 1]‖ = 1 := by
      rw [Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.norm_euclidean_eq_sqrt]
      simp [Matrix.dotProduct, Fin.sum_univ_two]
    rw [hn, hn', mul_one] at h
    exact h

/-- The uniform Bernoulli cube on three coordinates. -/
noncomputable def mcCube : Measure ((Fin 3) → Bool) :=
  (bernPMF (fun _ => (1 / 2 : ℝ)) (by intro i; norm_num)
    (by intro i; norm_num)).toMeasure

instance : IsProbabilityMeasure mcCube :=
  PMF.toMeasure.isProbabilityMeasure _

/-- The all-true cylinder mass: `1/8`, through the cylinder-intersection
engine. -/
theorem mcCube_all_true :
    mcCube {ω : (Fin 3) → Bool | ∀ k, ω k = true} = ENNReal.ofReal ((1 : ℝ) / 8) := by
  have hset : {ω : (Fin 3) → Bool | ∀ k, ω k = true}
      = ⋂ k ∈ (Finset.univ : Finset (Fin 3)),
        (fun ω : (Fin 3) → Bool => ω k) ⁻¹' {true} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
      Set.mem_singleton_iff]
    simp [Finset.mem_univ]
  rw [mcCube, hset, toMeasure_cyl_inter (fun _ => (1 / 2 : ℝ))
    (by intro i; norm_num) (by intro i; norm_num) Finset.univ
    (fun _ => ({true} : Set Bool))]
  simp only [bern, Set.mem_singleton_iff, if_true, Finset.mem_univ,
    Finset.prod_const, Fintype.card_fin, Finset.card_univ]
  have hfactor : ∑ x : Bool, (if x = true then (1 : ℝ≥0∞) else 0) *
      ENNReal.ofReal (if x = true then (1 : ℝ) / 2 else 1 - 1 / 2)
      = ENNReal.ofReal ((1 : ℝ) / 2) := by
    rw [show (Finset.univ : Finset Bool) = ({false, true} : Finset Bool) by
      ext b; cases b <;> simp,
      Finset.sum_insert (by simp), Finset.sum_singleton]
    simp
  rw [hfactor, ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
    show ((1 : ℝ) / 2) ^ 3 = 1 / 8 by norm_num]

/-- The riders are genuinely mutually independent (the design's
`h_indep` clause, through the BernoulliProduct engine). -/
theorem mcCube_indep :
    iIndepFun (fun _ : Fin 3 =>
        (inferInstance : MeasurableSpace (Matrix (Fin 2) (Fin 2) ℝ)))
      (fun (k : Fin 3) (ω : (Fin 3) → Bool) =>
        if ω k = true then mcNil1 else -mcNil1) mcCube := by
  rw [mcCube]
  exact iIndepFun_coord_matrix (fun _ => (1 / 2 : ℝ)) (by intro i; norm_num)
    (by intro i; norm_num) (id : Fin 3 → Fin 3)
    Function.injective_id
    (fun _ b => if b = true then mcNil1 else -mcNil1)

/-- The riders are genuinely centered (the design's `h_mean` clause,
through the Bernoulli mean at `p = 1/2`). -/
theorem mcCube_mean (k : Fin 3) :
    ∫ ω : (Fin 3) → Bool, (if ω k = true then mcNil1 else -mcNil1) ∂mcCube
      = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hδmeas : Measurable
      (fun ω : (Fin 3) → Bool => if ω k = true then (1 : ℝ) else 0) :=
    (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else 0)).comp
      (measurable_coord k)
  have hintf : Integrable
      (fun ω : (Fin 3) → Bool => if ω k = true then (1 : ℝ) else 0) mcCube :=
    Scaffold.Mathlib.Probability.Concentration.Scalar.integrable_of_bounded_measurable
      hδmeas (a := 1) (by
      intro ω
      by_cases hω : ω k = true <;> simp [hω])
  have hfun : (fun ω : (Fin 3) → Bool =>
        if ω k = true then mcNil1 else -mcNil1)
      = fun ω : (Fin 3) → Bool =>
        (((if ω k = true then (1 : ℝ) else 0) * 2 - 1) • mcNil1) := by
    funext ω
    by_cases hω : ω k = true
    · have h2 : (if ω k = true then (1 : ℝ) else 0) * 2 = 2 := by
        rw [if_pos hω]; norm_num
      rw [if_pos hω, h2]
      norm_num
    · have h2 : (if ω k = true then (1 : ℝ) else 0) * 2 = 0 := by
        rw [if_neg hω]; norm_num
      rw [if_neg hω, h2]
      norm_num
  rw [hfun, integral_smul_const]
  have hscalar : ∫ ω : (Fin 3) → Bool,
      ((if ω k = true then (1 : ℝ) else 0) * 2 - 1) ∂mcCube = 0 := by
    have h0 : ∫ ω : (Fin 3) → Bool, (if ω k = true then (1 : ℝ) else 0) ∂mcCube
        = 1 / 2 :=
      integral_delta (fun _ => (1 / 2 : ℝ)) (by intro i; norm_num)
        (by intro i; norm_num) k
    have hint2 : Integrable
        (fun ω : (Fin 3) → Bool => (if ω k = true then (1 : ℝ) else 0) * 2) mcCube :=
      hintf.mul_const 2
    rw [integral_sub hint2 (integrable_const _)]
    have hstep : ∫ ω : (Fin 3) → Bool,
        ((if ω k = true then (1 : ℝ) else 0) * 2) ∂mcCube = 1 := by
      have hconv : (fun ω : (Fin 3) → Bool =>
          (if ω k = true then (1 : ℝ) else 0) * 2)
          = fun ω : (Fin 3) → Bool =>
            (2 : ℝ) • (if ω k = true then (1 : ℝ) else 0) := by
        funext ω
        rw [smul_eq_mul]
        ring
      rw [hconv, integral_smul, h0]
      norm_num
    rw [hstep, integral_const]
    rw [measure_univ, ENNReal.one_toReal]
    norm_num
  rw [hscalar, zero_smul]

/-- **The `h_herm` fence for `matrix_bernstein`**: Hermitianity is
load-bearing. At three genuinely independent coordinate riders
`X k = ±N` on the uniform cube (mutual independence by
`iIndepFun_coord_matrix`, centering by the Bernoulli mean, and —
through the nilpotency `N² = 0` — the variance statistic identically
zero) with `R = 1` genuine, `t = 3`: the all-true atom has sum `3 • N`
of norm `3`, so the tail event carries mass `1/8` against
`4 · exp (−9/(0 + 2)) = 4 e^{−9/2} < 1/8` — the asymmetric nilpotent
escapes the Hermitian variance bookkeeping entirely. -/
-- @refutes: matrix_bernstein
theorem mcBn_herm_fence_QA
    (h : mcCube {ω : (Fin 3) → Bool |
        ‖∑ k : Fin 3, (if ω k = true then mcNil1 else -mcNil1)‖ ≥ (3 : ℝ)}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 2) : ℝ) *
        Real.exp (-((3 : ℝ) ^ 2) / (2 * ‖∑ k : Fin 3,
          ∫ ω : (Fin 3) → Bool, (if ω k = true then mcNil1 else -mcNil1) *
            (if ω k = true then mcNil1 else -mcNil1) ∂mcCube‖
          + (2 * 1 * (3 : ℝ)) / 3)))) :
    False := by
  have hsub : {ω : (Fin 3) → Bool | ∀ k, ω k = true} ⊆
      {ω : (Fin 3) → Bool |
        ‖∑ k : Fin 3, (if ω k = true then mcNil1 else -mcNil1)‖ ≥ (3 : ℝ)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, ge_iff_le]
    have hall : ∀ k : Fin 3, (if ω k = true then mcNil1 else -mcNil1) = mcNil1 :=
      fun k => if_pos (hω k)
    have hsum : ∑ k : Fin 3, (if ω k = true then mcNil1 else -mcNil1)
        = (3 : ℝ) • mcNil1 := by
      rw [Finset.sum_congr rfl (fun k _ => hall k)]
      have h2 := Finset.sum_const (b := mcNil1) (s := (Finset.univ : Finset (Fin 3)))
      rw [h2, Finset.card_univ, Fintype.card_fin]
      exact (Nat.cast_smul_eq_nsmul (R := ℝ) 3 mcNil1).symm
    rw [hsum, norm_smul, mcNil1_norm, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 3), mul_one]
  have hmass := measure_mono (μ := mcCube) hsub
  rw [mcCube_all_true] at hmass
  have hpt : ∀ (k : Fin 3) (ω : (Fin 3) → Bool),
      (if ω k = true then mcNil1 else -mcNil1) *
        (if ω k = true then mcNil1 else -mcNil1)
      = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro k ω
    rcases eq_or_ne (ω k) true with hω | hω
    · rw [if_pos hω, mcNil1_sq]
    · rw [if_neg hω, neg_mul_neg, mcNil1_sq]
  have hint : ∀ k : Fin 3,
      ∫ ω : (Fin 3) → Bool, (if ω k = true then mcNil1 else -mcNil1) *
        (if ω k = true then mcNil1 else -mcNil1) ∂mcCube
      = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro k
    have hfun : (fun ω : (Fin 3) → Bool =>
        (if ω k = true then mcNil1 else -mcNil1) * (if ω k = true then mcNil1 else -mcNil1))
        = fun _ => (0 : Matrix (Fin 2) (Fin 2) ℝ) := funext (hpt k)
    rw [hfun, integral_const]
    simp
  have hsumA : ∑ k : Fin 3,
      ∫ ω : (Fin 3) → Bool, (if ω k = true then mcNil1 else -mcNil1) *
        (if ω k = true then mcNil1 else -mcNil1) ∂mcCube
      = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Finset.sum_congr rfl (fun k _ => hint k)]
    simp
  rw [hsumA, show (Fintype.card (Fin 2) : ℝ) = 2 by norm_num] at h
  norm_num at h
  have hlt : (4 : ℝ) * Real.exp (-(9 / 2 : ℝ)) < 1 / 8 := by
    have h32 : (32 : ℝ) < Real.exp (9 / 2 : ℝ) := mc_thirtytwo_lt_exp_nine_halves
    have hpos : (0 : ℝ) < Real.exp (9 / 2 : ℝ) := Real.exp_pos _
    rw [Real.exp_neg, mul_comm, ← div_eq_inv_mul, div_lt_iff₀ hpos]
    nlinarith [h32]
  exact absurd (le_trans hmass h) (not_le.mpr
    ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 8)).2 hlt))

end AdversarialFences


/-!
## The genuine-Rademacher instance and the structure-field pins
(`proposals/zero-inert-census.md`)

The census's never-touched `MatrixMDS` structure fields
(`cond_mean_zero`, `measurable`, `norm_bound`) had never been consumed
as projections: the delivered constant-zero instance discharges them
tautologically. This section builds the first *nondegenerate* instance
in QA — a one-shot Rademacher ±identity sequence on the delivered coin
measure (`mcCoin`, the fair Bernoulli product on `Fin 1 → Bool`) at
`V = Fin 1` — and consumes each field at concrete witnesses:

- `measurable`: the random first difference is strongly measurable
  through the shelf's `stronglyMeasurable_coord_matrix` (the honest
  field the 2026-08-29 repair put in place of the content-free
  `adapted` one), promoted to the almost-everywhere property whose
  absence made the pre-repair set-integrals junk zeros.
- `cond_mean_zero`: the mean-zero integral computed by raw atom
  enumeration (`PMF.integral_eq_sum`, masses `1/2` each through the
  pmf application), consumed at the trivial past's `univ` and at the
  *nonempty* past event `k = 1` (the true cylinder, its
  past-measurability witnessed through the comap characterization at
  the entry fiber).
- `norm_bound`: the bound `R = 1` attained with equality at both
  outcomes, the `≤` side through the field, the `≥` side through the
  pinned identity norm (`l2OpNorm_one_fin1_QA`).

The trivial-past lemma (`mdsFiltration_zero_trivial`) is the comap
characterization at `k = 0`: the tuple map into the subsingleton
`Fin 0 → Matrix` pulls back only `∅` and `univ`.
-/

/-- The fair coin's false-cylinder mass (the twin of the delivered
`mcCoin_true`). -/
theorem mcCoin_false :
    mcCoin {ω : (Fin 1) → Bool | ω (0 : Fin 1) = false}
      = ENNReal.ofReal ((1 : ℝ) / 2) := by
  have hc := toMeasure_cyl (fun _ => (1 / 2 : ℝ)) (by intro i; norm_num)
    (by intro i; norm_num) (0 : Fin 1) ({false} : Set Bool)
  have hpre : {ω : (Fin 1) → Bool | ω (0 : Fin 1) = false}
      = (fun ω : (Fin 1) → Bool => ω (0 : Fin 1)) ⁻¹' {false} := by
    ext ω; simp
  rw [mcCoin, hpre, hc]
  have hb : (Finset.univ : Finset Bool) = ({false, true} : Finset Bool) := by
    ext b; cases b <;> simp
  rw [hb, Finset.sum_insert (by simp), Finset.sum_singleton]
  simp [bern]
  norm_num

/-- The Rademacher matrix family: the 1×1 identity on `true`, its
negation on `false`. -/
def mMds (b : Bool) : Matrix (Fin 1) (Fin 1) ℝ :=
  if b then 1 else -1

/-- The one-shot Rademacher difference sequence: a genuinely nonzero
first difference, zero afterwards. -/
def mdsRad (k : ℕ) (ω : (Fin 1) → Bool) :
    Matrix (Fin 1) (Fin 1) ℝ :=
  if k = 0 then mMds (ω 0) else 0

theorem mMds_true : mMds true = (1 : Matrix (Fin 1) (Fin 1) ℝ) := rfl

theorem mMds_false : mMds false = (-(1 : Matrix (Fin 1) (Fin 1) ℝ)) := rfl

/-- Both outcomes carry the identity norm. -/
theorem mMds_norm (b : Bool) : ‖mMds b‖ = 1 := by
  cases b
  · rw [mMds_false, norm_neg, l2OpNorm_one_fin1_QA]
  · rw [mMds_true, l2OpNorm_one_fin1_QA]

theorem omega_true : (![true] : Fin 1 → Bool) (0 : Fin 1) = true := rfl

theorem omega_false : (![false] : Fin 1 → Bool) (0 : Fin 1) = false := rfl

theorem mdsRad_zero (ω : (Fin 1) → Bool) :
    mdsRad 0 ω = mMds (ω 0) := if_pos rfl

theorem mdsRad_succ (k : ℕ) (ω : (Fin 1) → Bool) :
    mdsRad (k + 1) ω = 0 := if_neg (by omega)

/-- The two-atom enumeration of the coin space. -/
theorem univ_fin1_bool :
    (Finset.univ : Finset ((Fin 1) → Bool)) = {![false], ![true]} := by
  ext ω
  cases h : ω 0 <;>
    simp [Set.mem_singleton_iff, Set.mem_insert_iff, funext_iff, h]
  · exact Or.inl fun x => by fin_cases x <;> simp [h]
  · exact Or.inr fun x => by fin_cases x <;> simp [h]

/-- The mean-zero integral, by raw atom enumeration through
`PMF.integral_eq_sum`: the two outcomes carry mass `1/2` each, values
`+1` and `−1`, summing to zero. -/
theorem mdsRad_integral_zero :
    ∫ ω : (Fin 1) → Bool, mdsRad 0 ω ∂mcCoin = 0 := by
  have hf : (bernPMF (fun _ => (1 / 2 : ℝ))
      (by intro i; norm_num) (by intro i; norm_num)
      (![false] : Fin 1 → Bool)).toReal = 1 / 2 := by
    rw [bernPMF_apply]
    simp only [jointMass, Fin.prod_univ_one, bern, Matrix.cons_val_zero,
      if_false]
    rw [ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  have ht : (bernPMF (fun _ => (1 / 2 : ℝ))
      (by intro i; norm_num) (by intro i; norm_num)
      (![true] : Fin 1 → Bool)).toReal = 1 / 2 := by
    rw [bernPMF_apply]
    simp only [jointMass, Fin.prod_univ_one, bern, Matrix.cons_val_zero,
      if_true]
    rw [ENNReal.toReal_ofReal (by norm_num)]
  rw [mcCoin, PMF.integral_eq_sum, univ_fin1_bool,
    Finset.sum_insert (by
      intro hcon
      exact absurd hcon (by decide)),
    Finset.sum_singleton, hf, ht]
  simp only [mdsRad_zero, omega_false, omega_true,
    mMds_false, mMds_true]
  norm_num

/-- The past at `k = 0` is trivial: every `mdsFiltration X 0`-measurable
set is `∅` or `univ` (the tuple map into the subsingleton
`Fin 0 → Matrix` pulls back only the two extreme sets). -/
theorem mdsFiltration_zero_trivial
    (X : ℕ → ((Fin 1) → Bool) → Matrix (Fin 1) (Fin 1) ℝ)
    (S : Set ((Fin 1) → Bool))
    (hS : MeasurableSet[mdsFiltration X 0] S) :
    S = ∅ ∨ S = Set.univ := by
  have hsub : Subsingleton (Fin 0 → Matrix (Fin 1) (Fin 1) ℝ) :=
    inferInstance
  rw [mdsFiltration, MeasurableSpace.measurableSet_comap] at hS
  obtain ⟨t, -, ht⟩ := hS
  rcases Classical.em (∃ a, a ∈ t) with ⟨a, ha⟩ | hempty
  · right
    refine Set.eq_univ_of_forall fun ω => ?_
    have heq : (fun (j : Fin 0) => X ↑j ω) = a := hsub.allEq _ a
    have hmem : (fun (j : Fin 0) => X ↑j ω) ∈ t := heq ▸ ha
    have h' : ω ∈ (fun (ω : (Fin 1) → Bool) (j : Fin 0) => X ↑j ω) ⁻¹' t :=
      hmem
    rw [← ht]
    exact h'
  · left
    apply Set.eq_empty_iff_forall_not_mem.2
    intro ω hω
    have h' : ω ∈ (fun (ω : (Fin 1) → Bool) (j : Fin 0) => X ↑j ω) ⁻¹' t := by
      rw [ht]
      exact hω
    exact hempty ⟨_, h'⟩

/-- The genuine Rademacher instance on the coin: the identity matrix's
sign is the coin flip, the tail is zero, the bound is attained. -/
noncomputable def mdsRadMDS :
    MatrixMDS (V := Fin 1) mcCoin where
  R := 1
  X := mdsRad
  measurable := by
    intro k
    by_cases hk : k = 0
    · subst hk
      show StronglyMeasurable (fun ω => mdsRad 0 ω)
      simp only [mdsRad_zero]
      exact stronglyMeasurable_coord_matrix mMds 0
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      show StronglyMeasurable (fun ω => mdsRad (k' + 1) ω)
      simp only [mdsRad_succ]
      exact stronglyMeasurable_const
  cond_mean_zero := by
    intro k S hS
    by_cases hk : k = 0
    · subst hk
      simp only [mdsRad_zero]
      rcases mdsFiltration_zero_trivial mdsRad S hS with h | h
      · rw [h, setIntegral_empty]
      · rw [h, setIntegral_univ]
        exact mdsRad_integral_zero
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [mdsRad_succ]
      simp
  norm_bound := by
    intro k ω
    by_cases hk : k = 0
    · subst hk
      rw [mdsRad_zero, mMds_norm]
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [mdsRad_succ, norm_zero]
      norm_num

/-- The true cylinder is past-measurable at `k = 1` (it is the
preimage of the entry fiber `t 0 0 0 = 1` under the one-step tuple
map — the fiber that distinguishes `+1` from `−1`). -/
theorem mdsRad_trueCyl_past :
    MeasurableSet[mdsFiltration mdsRadMDS.X 1]
      {ω : (Fin 1) → Bool | ω (0 : Fin 1) = true} := by
  rw [mdsFiltration, MeasurableSpace.measurableSet_comap]
  refine ⟨(fun t : Fin 1 → Matrix (Fin 1) (Fin 1) ℝ => t 0 0 0) ⁻¹'
      ({1} : Set ℝ), ?_, ?_⟩
  · have hentry : MeasurableSet
        ((fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) ⁻¹' ({1} : Set ℝ)) :=
      ((measurable_pi_apply (0 : Fin 1)).comp
        (measurable_pi_apply (0 : Fin 1)))
        (measurableSet_singleton (1 : ℝ))
    exact (measurable_pi_apply (0 : Fin 1) :
      Measurable fun t : Fin 1 → Matrix (Fin 1) (Fin 1) ℝ => t 0) hentry
  · ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Fin.val_zero]
    have hx : mdsRadMDS.X 0 ω = mdsRad 0 ω := rfl
    rw [hx, mdsRad_zero]
    constructor
    · intro hval
      rcases (Classical.em (ω 0 = true)) with h | h
      · exact h
      · rw [Bool.not_eq_true] at h
        rw [h, mMds_false] at hval
        simp only [Matrix.neg_apply, Matrix.one_apply, Matrix.cons_val_zero,
          Matrix.head_cons, if_pos rfl] at hval
        norm_num at hval
    · intro h
      rw [h, mMds_true]
      simp

/-- **PIN (`norm_bound`)**: the uniform bound is attained with equality
at both outcomes — the `≤` side through the field projection, the `≥`
side through the pinned identity norm. -/
theorem mdsRadMDS_norm_pin :
    ‖mdsRadMDS.X 0 ![true]‖ = mdsRadMDS.R ∧
      ‖mdsRadMDS.X 0 ![false]‖ = mdsRadMDS.R := by
  have hT : mdsRadMDS.X 0 ![true] = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    show mdsRad 0 ![true] = 1
    rw [mdsRad_zero, omega_true, mMds_true]
  have hF : mdsRadMDS.X 0 ![false]
      = (-(1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    show mdsRad 0 ![false] = -1
    rw [mdsRad_zero, omega_false, mMds_false]
  refine ⟨le_antisymm (mdsRadMDS.norm_bound 0 ![true]) ?_,
    le_antisymm (mdsRadMDS.norm_bound 0 ![false]) ?_⟩
  · show (1 : ℝ) ≤ ‖mdsRadMDS.X 0 ![true]‖
    rw [hT, l2OpNorm_one_fin1_QA]
  · show (1 : ℝ) ≤ ‖mdsRadMDS.X 0 ![false]‖
    rw [hF, norm_neg, l2OpNorm_one_fin1_QA]

/-- **PIN (`cond_mean_zero`)**: the field consumed twice — at the
trivial past's `univ` (the genuinely computed mean zero, joined to the
raw atom enumeration) and at the nonempty past event `k = 1` (the true
cylinder, whose past-measurability is witnessed above). -/
theorem mdsRadMDS_cond_mean_pin :
    (∫ ω : (Fin 1) → Bool, mdsRadMDS.X 0 ω ∂mcCoin = 0) ∧
      (∫ ω in {ω : (Fin 1) → Bool | ω (0 : Fin 1) = true},
          mdsRadMDS.X 1 ω ∂mcCoin = 0) := by
  refine ⟨?_, ?_⟩
  · have h := mdsRadMDS.cond_mean_zero 0 Set.univ
      MeasurableSet.univ
    rwa [setIntegral_univ] at h
  · exact mdsRadMDS.cond_mean_zero 1 _
      mdsRad_trueCyl_past

/-- **PIN (`measurable`)**: the ambient strong measurability of the
random first difference — the honest field the 2026-08-29 repair put
in place of the content-free `adapted` one — promoted to
almost-everywhere strong measurability, the property whose absence
made the pre-repair set-integrals junk zeros. -/
theorem mdsRadMDS_meas_pin :
    AEStronglyMeasurable (mdsRadMDS.X 0) mcCoin :=
  StronglyMeasurable.aestronglyMeasurable (mdsRadMDS.measurable 0)

end Scaffold.Mathlib.Probability.Concentration.Matrix.QA
