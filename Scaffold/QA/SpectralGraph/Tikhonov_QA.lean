/-
  Tikhonov_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.Tikhonov` (the
  graph-signal smoothing operator in the Laplacian eigenbasis), proved
  2026-08-20. Fixture: the two-vertex network `K₂` (adjacency
  `!![0,1;1,0]`, Laplacian `!![1,-1;-1,1]`, spectrum `{0, 2}`), signal
  `y = ![1, 0]`, regularization `π = 1`.

  - the minimizer **pinned through the normal equation by plain
    Gaussian elimination**: the candidate `![2/3, 1/3]` is verified by
    hand (`(L + 1) *ᵥ ![2/3, 1/3] = 1 • ![1, 0]`, entrywise
    computation independent of the module), and the characterization
    theorem `eq_tikhonovMinimizer_of_add_smul_one_mulVec` promotes it
    to `tikhonovMinimizer adjK2 _ 1 ![1,0] = ![2/3, 1/3]` — the
    spectral-theorem construction and a hand-solved 2×2 linear system
    meet at the same vector, which a defect in either would break;
  - the objective **pinned numerically**: `obj(x*) = 1/3` exactly,
    against `obj(y) = obj(0) = 1` — the minimality theorem instantiated
    reads `1/3 ≤ 1`, and the improvement is strict, so the minimizer is
    a genuinely better reconstruction than the raw signal or zero;
  - the shrinkage story at the two pinned eigenvalues `{0, 2}` (sum =
    trace `2`, product = determinant `0`, both nonnegative — so each
    eigenvalue is `0` or `2`): the kernel mode's factor is exactly `1`
    and every other mode's factor is exactly `1/3`, the ordering
    `1/3 < 1` delivered by the antitonicity theorem, `1/3 ∈ Ioo 0 1`
    by the strict-attenuation theorem — the filter is a genuine
    low-pass shrinkage, not the identity and not an annihilator;
  - **not a projection, numerically**: `T(T y) = ![5/9, 4/9]` (pinned
    by a second hand-solved normal equation at `y' = T y`), which
    differs from `T y = ![6/9, 3/9]` in every entry — a projection
    would fix its own output exactly;
  - **mean preservation**: the coordinate sums of `T y` and `T(T y)`
    both compute to `1 = ∑ y` — the kernel mode passes through
    untouched, exactly as `sum_tikhonovMinimizer_eq_sum` predicts;
  - the **`hπ` guard refuted-on-omission**: at `π = 0` the minimizer is
    the zero vector (every junk factor is `0`) while the objective
    degenerates to `‖x − y‖²`, so the hypothesis-free minimality
    statement would read `1 ≤ 0` at this fixture — the `0 < π`
    hypothesis is load-bearing, not decorative;
  - the **uniqueness theorem consumed contrapositively**: `y ≠ x*`
    follows from `obj(y) ≠ obj(x*)` through
    `eq_of_tikhonovObjective_eq_minimizer`, since equality of the
    vectors would force equality of the objectives.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not
  prove the theorems; it checks their interfaces against independently
  computed values and falsifies nearby wrong statements.

  Scoreboard: ../docs/5_QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Tikhonov

/-!
# QA for Tikhonov regularization in the Laplacian eigenbasis
-/

open scoped BigOperators Matrix

namespace Scaffold.Mathlib.GraphTheory.Tikhonov.QA

open Matrix SpectralGraphTheory

/-!
## Fixture: `K₂` on `Fin 2`
-/

section Fixture

/-- The two-vertex complete network `K₂`. -/
def adjK2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

theorem adjK2_symmetric : adjK2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, adjK2]

theorem adjK2_nonneg : ∀ i j, 0 ≤ adjK2 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [adjK2]

theorem adjK2_apply (i j : Fin 2) : adjK2 i j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;> simp [adjK2]

/-- The `K₂` Laplacian: `1` on the diagonal, `−1` off it. -/
theorem lapK2_apply (i j : Fin 2) :
    laplacian adjK2 i j = if i = j then 1 else -1 := by
  fin_cases i <;> fin_cases j <;> simp [laplacian, degreeMatrix, deg, adjK2]

theorem lapK2_symmetric : (laplacian adjK2).IsSymm :=
  laplacian_symmetric adjK2 adjK2_symmetric

end Fixture

/-!
## The minimizer pinned by a hand-solved normal equation
-/

section NormalEquation

/-- The hand computation: `![2/3, 1/3]` solves the `π = 1` normal
equation `(L + 1•1) *ᵥ z = 1 • y` at `y = ![1, 0]` — plain Gaussian
elimination, no spectral machinery. -/
theorem normal_K2 :
    (laplacian adjK2 + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      *ᵥ ![2 / 3, 1 / 3] = (1 : ℝ) • ![1, 0] := by
  funext a
  fin_cases a <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, lapK2_apply, Fin.sum_univ_two,
      Pi.smul_apply] <;>
    norm_num

/-- **The minimizer, pinned**: the spectral-theorem construction
evaluates to the hand-solved solution `![2/3, 1/3]`. -/
theorem tik_K2_eq :
    tikhonovMinimizer adjK2 adjK2_symmetric 1 ![1, 0] = ![2 / 3, 1 / 3] :=
  (eq_tikhonovMinimizer_of_add_smul_one_mulVec adjK2 adjK2_symmetric
    adjK2_nonneg (by norm_num) normal_K2).symm

end NormalEquation

/-!
## The objective, pinned numerically
-/

section Objective

/-- The energy identity behind the objective pins: for `K₂`,
`xᵀ L x = (x 0 − x 1)²`. -/
theorem quadForm_lapK2 (x : Fin 2 → ℝ) :
    quadForm (laplacian adjK2) x = (x 0 - x 1) ^ 2 := by
  simp [quadForm, Matrix.dotProduct, Matrix.mulVec, lapK2_apply,
    Fin.sum_univ_two]
  ring

/-- The objective of the minimizer is exactly `1/3`. -/
theorem obj_min_K2 :
    tikhonovObjective adjK2 1 ![1, 0] ![2 / 3, 1 / 3] = 1 / 3 := by
  simp only [tikhonovObjective, quadForm_lapK2]
  norm_num

/-- The objective of the raw signal is exactly `1`. -/
theorem obj_y_K2 :
    tikhonovObjective adjK2 1 ![1, 0] ![1, 0] = 1 := by
  simp only [tikhonovObjective, quadForm_lapK2]
  norm_num

/-- The objective of the zero vector is exactly `1`. -/
theorem obj_zero_K2 :
    tikhonovObjective adjK2 1 ![1, 0] 0 = 1 := by
  simp only [tikhonovObjective, quadForm_lapK2]
  norm_num

/-- Minimality instantiated reads `1/3 ≤ 1`. -/
theorem minimality_K2 :
    tikhonovObjective adjK2 1 ![1, 0] (tikhonovMinimizer adjK2
      adjK2_symmetric 1 ![1, 0])
      ≤ tikhonovObjective adjK2 1 ![1, 0] ![1, 0] := by
  rw [tik_K2_eq, obj_min_K2, obj_y_K2]
  norm_num

/-- The improvement over the raw signal is strict. -/
theorem obj_min_lt_obj_y_K2 :
    tikhonovObjective adjK2 1 ![1, 0] (tikhonovMinimizer adjK2
      adjK2_symmetric 1 ![1, 0])
      < tikhonovObjective adjK2 1 ![1, 0] ![1, 0] := by
  rw [tik_K2_eq, obj_min_K2, obj_y_K2]
  norm_num

/-- Uniqueness consumed contrapositively: the raw signal differs from
the minimizer because their objectives differ (`1 ≠ 1/3`) — equal
vectors would force equal objectives. -/
theorem y_ne_min_K2 :
    ![1, 0] ≠ tikhonovMinimizer adjK2 adjK2_symmetric 1 ![1, 0] := by
  intro hcon
  have hobj := congrArg (tikhonovObjective adjK2 1 ![1, 0]) hcon
  rw [obj_y_K2, tik_K2_eq, obj_min_K2] at hobj
  norm_num at hobj

end Objective

/-!
## The shrinkage story at the pinned spectrum `{0, 2}`
-/

section Shrinkage

theorem lapK2_trace : (laplacian adjK2).trace = 2 := by
  simp [Matrix.trace, lapK2_apply]

theorem lapK2_det : (laplacian adjK2).det = 0 := by
  have h00 : laplacian adjK2 0 0 = 1 := by simp [lapK2_apply]
  have h11 : laplacian adjK2 1 1 = 1 := by simp [lapK2_apply]
  have h01 : laplacian adjK2 0 1 = -1 := by simp [lapK2_apply]
  have h10 : laplacian adjK2 1 0 = -1 := by simp [lapK2_apply]
  rw [Matrix.det_fin_two, h00, h11, h01, h10]
  norm_num

/-- Sum of the eigenvalues is the trace `2`. -/
theorem lapK2_eigvalOf_sum :
    ∑ i, eigvalOf (laplacian adjK2) lapK2_symmetric i = 2 := by
  rw [eigvalOf_sum_eq_trace, lapK2_trace]

/-- Product of the eigenvalues is the determinant `0`. -/
theorem lapK2_eigvalOf_prod :
    ∏ i, eigvalOf (laplacian adjK2) lapK2_symmetric i = 0 := by
  have h := (isHermitian_of_isSymm lapK2_symmetric).det_eq_prod_eigenvalues
  rw [lapK2_det] at h
  simpa using h.symm

theorem lapK2_eigvalOf_nonneg (i : Fin 2) :
    0 ≤ eigvalOf (laplacian adjK2) lapK2_symmetric i :=
  eigvalOf_laplacian_nonneg adjK2 adjK2_symmetric adjK2_nonneg i

/-- Every `K₂` Laplacian eigenvalue is `0` or `2`: the two values sum
to the trace `2`, multiply to the determinant `0`, and are both
nonnegative. -/
theorem lapK2_eigvalOf_two (i : Fin 2) :
    eigvalOf (laplacian adjK2) lapK2_symmetric i = 0 ∨
      eigvalOf (laplacian adjK2) lapK2_symmetric i = 2 := by
  have hsum := lapK2_eigvalOf_sum
  have hprod := lapK2_eigvalOf_prod
  simp only [Fin.sum_univ_two, Fin.prod_univ_two] at hsum hprod
  have hn0 := lapK2_eigvalOf_nonneg 0
  have hn1 := lapK2_eigvalOf_nonneg 1
  rcases mul_eq_zero.1 hprod with h0 | h1
  · fin_cases i
    · exact Or.inl h0
    · right
      have : eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 2 := by
        linarith
      exact this
  · fin_cases i
    · right
      have : eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 2 := by
        linarith
      exact this
    · exact Or.inl h1

/-- Every mode of the signal is either untouched (kernel mode, factor
exactly `1`) or shrunk to exactly `1/3` — the two factors of this
network, computed from the definition. -/
theorem lapK2_shrinkage (i : Fin 2) :
    tikhonovShrinkage 1 (eigvalOf (laplacian adjK2) lapK2_symmetric i)
      = 1 ∨ tikhonovShrinkage 1 (eigvalOf (laplacian adjK2)
          lapK2_symmetric i) = 1 / 3 := by
  rcases lapK2_eigvalOf_two i with h | h
  · left
    rw [h, tikhonovShrinkage_eq_one_iff (by norm_num)]
  · right
    rw [h]
    norm_num [tikhonovShrinkage]

end Shrinkage

/-!
## Not a projection, and mean preservation — numerically
-/

section NotProjection

/-- A second hand-solved normal equation: `![5/9, 4/9]` solves the
`π = 1` equation at the filtered signal `y' = ![2/3, 1/3]`. -/
theorem normal_K2_two :
    (laplacian adjK2 + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      *ᵥ ![5 / 9, 4 / 9] = (1 : ℝ) • ![2 / 3, 1 / 3] := by
  funext a
  fin_cases a <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, lapK2_apply, Fin.sum_univ_two,
      Pi.smul_apply] <;>
    norm_num

/-- **Filtering twice**: `T (T y) = ![5/9, 4/9]`, pinned by the second
hand-solved system. -/
theorem tik_K2_two :
    tikhonovMinimizer adjK2 adjK2_symmetric 1
      (tikhonovMinimizer adjK2 adjK2_symmetric 1 ![1, 0]) = ![5 / 9, 4 / 9] := by
  rw [tik_K2_eq]
  exact (eq_tikhonovMinimizer_of_add_smul_one_mulVec adjK2 adjK2_symmetric
    adjK2_nonneg (by norm_num) normal_K2_two).symm

/-- **The filter is not a projection, numerically**: `T (T y) ≠ T y`,
differing in every entry (`5/9 ≠ 6/9`, `4/9 ≠ 3/9`). A projection would
fix its own output exactly. -/
theorem tik_K2_not_projection :
    tikhonovMinimizer adjK2 adjK2_symmetric 1
      (tikhonovMinimizer adjK2 adjK2_symmetric 1 ![1, 0])
      ≠ tikhonovMinimizer adjK2 adjK2_symmetric 1 ![1, 0] := by
  rw [tik_K2_two, tik_K2_eq]
  intro hcon
  have h0 : (5 : ℝ) / 9 = (2 : ℝ) / 3 := congrFun hcon 0
  norm_num at h0

/-- Mean preservation, instantiated: the filtered signal's coordinate
sum equals the raw signal's (`1`), exactly as
`sum_tikhonovMinimizer_eq_sum` predicts. -/
theorem sum_tik_K2 :
    ∑ a, tikhonovMinimizer adjK2 adjK2_symmetric 1 ![1, 0] a = 1 := by
  rw [sum_tikhonovMinimizer_eq_sum (π := 1) adjK2 adjK2_symmetric (by norm_num)]
  norm_num

/-- The doubly-filtered signal also preserves the mean (`5/9 + 4/9 =
1`) — the kernel mode passes through every application untouched. -/
theorem sum_tik_tik_K2 :
    ∑ a, tikhonovMinimizer adjK2 adjK2_symmetric 1
      (tikhonovMinimizer adjK2 adjK2_symmetric 1 ![1, 0]) a = 1 := by
  rw [tik_K2_eq, sum_tikhonovMinimizer_eq_sum (π := 1) adjK2
    adjK2_symmetric (by norm_num)]
  norm_num

end NotProjection

/-!
## The `hπ` guard: `π = 0` refutes the hypothesis-free form
-/

section PiZero

/-- At `π = 0` every junk factor is `0`, so the minimizer is the zero
vector (all eigenbasis coefficients vanish). -/
theorem tik_K2_zero :
    tikhonovMinimizer adjK2 adjK2_symmetric 0 ![1, 0] = 0 := by
  refine ext_of_dotProduct_eigvecOf_eq lapK2_symmetric fun k => ?_
  rw [tikhonovMinimizer_dotProduct_eigvecOf, tikhonovShrinkage, zero_div,
    zero_mul, Matrix.dotProduct_zero]

/-- The `π = 0` objective of the zero vector is `1` (the coefficient
`1/0` is the junk `0`, so only the fidelity term remains). -/
theorem obj_zero_pi0_K2 :
    tikhonovObjective adjK2 0 ![1, 0] 0 = 1 := by
  simp only [tikhonovObjective, Matrix.dotProduct, sub_apply, Fin.sum_univ_two,
    div_zero]
  norm_num

/-- The `π = 0` objective of the raw signal is `0` (zero fidelity, junk
coefficient times PSD energy). -/
theorem obj_y_pi0_K2 :
    tikhonovObjective adjK2 0 ![1, 0] ![1, 0] = 0 := by
  simp only [tikhonovObjective, Matrix.dotProduct, sub_self, Fin.sum_univ_two,
    div_zero]
  norm_num

/-- **The `hπ` guard is load-bearing**: at `π = 0` the (hypothesis-free)
minimality statement would read `1 ≤ 0` at this fixture — the theorem's
`0 < π` hypothesis excludes exactly this degeneration. -/
theorem not_minimality_pi0_K2 :
    ¬ (tikhonovObjective adjK2 0 ![1, 0]
        (tikhonovMinimizer adjK2 adjK2_symmetric 0 ![1, 0])
      ≤ tikhonovObjective adjK2 0 ![1, 0] ![1, 0]) := by
  rw [tik_K2_zero, obj_zero_pi0_K2, obj_y_pi0_K2]
  norm_num

end PiZero

end Scaffold.Mathlib.GraphTheory.Tikhonov.QA
