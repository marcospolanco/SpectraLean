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
import Scaffold.Mathlib.GraphTheory.Spectral
import Mathlib.Data.Complex.ExponentialBounds

open MeasureTheory ProbabilityTheory Classical
open Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent SpectralGraphTheory
open scoped ENNReal Matrix Matrix.L2OpNorm

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

end Scaffold.Mathlib.Probability.Concentration.Matrix.QA
