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

  Phase 2 (the hard-filter limit, 2026-08-23), on two fixtures:

  - **the two-mode tail on the diagonal fixture `diag13`** (reused from
    `Band_QA`: spectrum `{1, 3}`, each eigenspace a coordinate axis):
    the tail energy pinned in *closed form* `tikhonovShrinkage π 1 ^ 2`
    at every `π` (the `λ = 3` mode's coefficient is provably `0`, the
    `λ = 1` mode's provably squares to `1`), evaluated exactly at
    `π = 1/10` (`1/121`) and `π = 1/100` (`1/10201`) — the energy
    visibly collapsing as `π → 0` — and the corollary consumed at a
    concrete tolerance (`∃ δ > 0` forcing tail energy below `1/100`
    near `0`);
  - **the scalar `lam = 0` refutation**: the hypothesis-free form of
    the hard-filter limit is false — the factor is `1` at every
    `π ≠ 0` and `0` at `π = 0`, so it has no limit at all;
  - **the tail-level boundary refutation on `K₂`** (the requester's
    mandated "must not be phrased as a band projector" witness): with
    the kernel mode included in the tail (the eigenvalue bound
    dropped), the tail energy provably stays `≥ 1/2` at every nonzero
    `π` — the kernel mode passes through untouched — so the tail
    statement is *false*, the `lam ≤ λᵢ` hypothesis load-bearing;
  - **the minimizer-form corollary instantiated on `K₂`** at the
    filtered nonzero-mode tail (the set identified as exactly the
    eigenvalue-`2` singleton), with its `π = 1` energy pinned to
    `1/18` through the coefficient identity (`(1/3)² · c²` with
    `c² = 1/2` by Parseval and the kernel line).

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not
  prove the theorems; it checks their interfaces against independently
  computed values and falsifies nearby wrong statements.

  Scoreboard: ../docs/5_QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Tikhonov
import Scaffold.QA.SpectralGraph.Band_QA

/-!
# QA for Tikhonov regularization in the Laplacian eigenbasis
-/

open scoped BigOperators Matrix Topology

namespace Scaffold.Mathlib.GraphTheory.Tikhonov.QA

open Matrix SpectralGraphTheory Filter SpectralGraphTheory.QA

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

/-!
## The hard-filter limit (Phase 2): the two-mode tail on `diag13`

The diagonal fixture `diag13` (from `Band_QA`: spectrum `{1, 3}`, each
eigenspace one coordinate axis) supplies a genuine two-mode tail at
`lam = 1`: *both* modes clear the eigenvalue bound, so the corollary's
sum combinator is exercised with two genuinely distinct attenuations.
-/

section HardFilterDiag

/-- The signal coefficient at the eigenvalue-`1` mode squares to `1`
(the mode is the first coordinate axis and the signal is `e₀`). -/
theorem coeff_sq_of_eq_one {i : Fin 2}
    (hi : eigvalOf diag13 diag13_symm i = 1) :
    (Matrix.dotProduct (eigvecOf diag13 diag13_symm i) ![1, 0]) ^ 2 = 1 := by
  obtain ⟨hv1, hv0⟩ := eigvecOf_diag13_one i hi
  simp only [Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, one_mul, zero_add, sq]
  linarith

/-- The signal coefficient at the eigenvalue-`3` mode is `0` (the mode
is the second coordinate axis and the signal is `e₀`). -/
theorem coeff_of_eq_three {i : Fin 2}
    (hi : eigvalOf diag13 diag13_symm i = 3) :
    Matrix.dotProduct (eigvecOf diag13 diag13_symm i) ![1, 0] = 0 := by
  obtain ⟨hv0, -⟩ := eigvecOf_diag13_three i hi
  simp [Matrix.dotProduct, hv0, Fin.sum_univ_two]

/-- The whole `λ = 1`-mode term of the tail energy, in product-square
form: it is exactly the squared shrinkage factor. -/
theorem term_of_eq_one {i : Fin 2} (hi : eigvalOf diag13 diag13_symm i = 1)
    (π : ℝ) :
    (tikhonovShrinkage π (eigvalOf diag13 diag13_symm i)
      * Matrix.dotProduct (eigvecOf diag13 diag13_symm i) ![1, 0]) ^ 2
      = tikhonovShrinkage π 1 ^ 2 := by
  rw [hi, mul_pow, coeff_sq_of_eq_one hi, mul_one]

/-- The whole `λ = 3`-mode term of the tail energy: it is exactly `0`
(the mode's signal coefficient vanishes). -/
theorem term_of_eq_three {i : Fin 2} (hi : eigvalOf diag13 diag13_symm i = 3)
    (π : ℝ) :
    (tikhonovShrinkage π (eigvalOf diag13 diag13_symm i)
      * Matrix.dotProduct (eigvecOf diag13 diag13_symm i) ![1, 0]) ^ 2
      = 0 := by
  rw [hi, coeff_of_eq_three hi, mul_zero]
  norm_num

/-- **The two-mode tail energy in closed form**: on the full two-mode
tail, the filtered coefficient energy is exactly
`tikhonovShrinkage π 1 ^ 2` — the `λ = 3` mode contributes nothing (its
coefficient is `0`), the `λ = 1` mode carries the whole (vanishing)
energy. -/
theorem diag13_tail_energy_eq (π : ℝ) :
    ∑ i, (tikhonovShrinkage π (eigvalOf diag13 diag13_symm i)
      * Matrix.dotProduct (eigvecOf diag13 diag13_symm i) ![1, 0]) ^ 2
      = tikhonovShrinkage π 1 ^ 2 := by
  obtain ⟨i₁, hi₁⟩ := diag13_exists_one
  fin_cases i₁
  · have hi₁' : eigvalOf diag13 diag13_symm 0 = 1 := hi₁
    have h1 : eigvalOf diag13 diag13_symm 1 = 3 :=
      diag13_other_eq_three (by decide) hi₁'
    rw [Fin.sum_univ_two, term_of_eq_one hi₁', term_of_eq_three h1, add_zero]
  · have hi₁' : eigvalOf diag13 diag13_symm 1 = 1 := hi₁
    have h0 : eigvalOf diag13 diag13_symm 0 = 3 :=
      diag13_other_eq_three (by decide) hi₁'
    rw [Fin.sum_univ_two, term_of_eq_three h0, term_of_eq_one hi₁', zero_add]

/-- The closed form evaluated at `π = 1/10`: the energy is exactly
`1/121`. -/
theorem diag13_tail_energy_pi_tenth :
    ∑ i, (tikhonovShrinkage (1 / 10 : ℝ) (eigvalOf diag13 diag13_symm i)
      * Matrix.dotProduct (eigvecOf diag13 diag13_symm i) ![1, 0]) ^ 2
      = 1 / 121 := by
  rw [diag13_tail_energy_eq]
  norm_num [tikhonovShrinkage]

/-- The closed form evaluated further down at `π = 1/100`: exactly
`1/10201` — the energy visibly collapses as `π → 0`. -/
theorem diag13_tail_energy_pi_hundredth :
    ∑ i, (tikhonovShrinkage (1 / 100 : ℝ) (eigvalOf diag13 diag13_symm i)
      * Matrix.dotProduct (eigvecOf diag13 diag13_symm i) ![1, 0]) ^ 2
      = 1 / 10201 := by
  rw [diag13_tail_energy_eq]
  norm_num [tikhonovShrinkage]

/-- The two-mode-tail hypothesis holds at `lam = 1`. -/
theorem diag13_tail_hyp (i : Fin 2) :
    1 ≤ eigvalOf diag13 diag13_symm i := by
  rcases diag13_eigvalOf_mem i with h | h
  · rw [h]
  · rw [h]; norm_num

/-- **The corollary instantiated on the two-mode tail** and consumed at
a concrete tolerance: some `δ > 0` forces every `π` within `δ` of `0`
to tail energy below `1/100`. -/
theorem diag13_corollary_consumed :
    ∃ δ > 0, ∀ π : ℝ, |π| < δ →
      ∑ i, (tikhonovShrinkage π (eigvalOf diag13 diag13_symm i)
        * Matrix.dotProduct (eigvecOf diag13 diag13_symm i) ![1, 0]) ^ 2
        < 1 / 100 := by
  have h := tikhonovShrinkage_tail_energy_tendsto_zero
    (V := Fin 2) diag13_symm (by norm_num) ![1, 0] Finset.univ
    (fun i _ => diag13_tail_hyp i)
  rw [Metric.tendsto_nhds_nhds] at h
  obtain ⟨δ, hδ, hδ'⟩ := h (1 / 100) (by norm_num)
  refine ⟨δ, hδ, fun π hπ => ?_⟩
  have hdist := hδ' (by rw [Real.dist_eq, sub_zero]; exact hπ)
  rw [Real.dist_eq, sub_zero, abs_lt] at hdist
  linarith [hdist.2]

end HardFilterDiag

/-!
## The hard-filter limit (Phase 2): boundary refutations

Both hypotheses of the tail-suppression statement are load-bearing, and
QA refutes the hypothesis-dropped forms at both levels: scalar (`0 <
lam`) and tail (`lam ≤ λᵢ` for every tail mode — including the kernel
mode breaks it).
-/

section HardFilterFence

theorem shrinkage_eq_one_of_ne_zero {π : ℝ} (hπ : π ≠ 0) :
    tikhonovShrinkage π 0 = 1 := by
  rw [tikhonovShrinkage, zero_add, div_self hπ]

/-- **The `0 < lam` hypothesis is load-bearing**: at `lam = 0` the
scalar statement is false — the factor is `1` at every `π ≠ 0` and `0`
at `π = 0`, so it has no limit at all, in particular not to `0`. -/
theorem not_shrinkage_zero_tendsto :
    ¬ Filter.Tendsto (fun π : ℝ => tikhonovShrinkage π 0) (𝓝 0) (𝓝 0) := by
  intro h
  rw [Metric.tendsto_nhds_nhds] at h
  obtain ⟨δ, hδ, hδ'⟩ := h (1 / 2) (by norm_num)
  have hmin0 : 0 < min (δ / 2) 1 := lt_min (by linarith) zero_lt_one
  have hminlt : min (δ / 2) 1 < δ := by
    rcases le_or_gt δ 2 with hle | hgt
    · rw [min_eq_left (by linarith)]
      linarith
    · rw [min_eq_right (by linarith)]
      linarith
  have hdist := hδ' (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hmin0]; exact hminlt)
  rw [Real.dist_eq, sub_zero, shrinkage_eq_one_of_ne_zero (ne_of_gt hmin0),
    abs_one] at hdist
  norm_num at hdist

end HardFilterFence

/-!
## The hard-filter limit (Phase 2): the `K₂` tail boundary and the
minimizer-form instantiation
-/

section HardFilterK2

/-- Some `K₂` Laplacian eigenvalue is zero (the product/determinant
route). -/
theorem lapK2_exists_zero :
    ∃ i : Fin 2, eigvalOf (laplacian adjK2) lapK2_symmetric i = 0 := by
  have hprod := lapK2_eigvalOf_prod
  simp only [Fin.prod_univ_two] at hprod
  rcases mul_eq_zero.1 hprod with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

/-- The eigen-action fact on the `K₂` Laplacian. -/
theorem lapK2_mulVec_eigvecOf (i : Fin 2) :
    (laplacian adjK2) *ᵥ (eigvecOf (laplacian adjK2) lapK2_symmetric i)
      = eigvalOf (laplacian adjK2) lapK2_symmetric i
        • (eigvecOf (laplacian adjK2) lapK2_symmetric i) :=
  (isHermitian_of_isSymm lapK2_symmetric).mulVec_eigenvectorBasis i

/-- A kernel-mode eigenvector of `K₂` is constant (its two coordinates
agree — the kernel is the diagonal line). -/
theorem lapK2_eigvecOf_eq_of_eq_zero {i : Fin 2}
    (hi : eigvalOf (laplacian adjK2) lapK2_symmetric i = 0) :
    eigvecOf (laplacian adjK2) lapK2_symmetric i 0
      = eigvecOf (laplacian adjK2) lapK2_symmetric i 1 := by
  have hev := lapK2_mulVec_eigvecOf i
  rw [hi] at hev
  have h0 := congrFun hev 0
  simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    Pi.smul_apply, smul_eq_mul, zero_mul] at h0
  rw [show laplacian adjK2 0 0 = (1 : ℝ) from by simp [lapK2_apply],
      show laplacian adjK2 0 1 = (-1 : ℝ) from by simp [lapK2_apply]] at h0
  simp only [one_mul, neg_mul, one_mul] at h0
  linarith

/-- The kernel-mode coefficient of the signal `![1,0]` squares to
exactly `1/2` (constant unit vector dotted with `e₀`). -/
theorem lapK2_coeff_sq_of_eq_zero {i : Fin 2}
    (hi : eigvalOf (laplacian adjK2) lapK2_symmetric i = 0) :
    (Matrix.dotProduct (eigvecOf (laplacian adjK2) lapK2_symmetric i)
        ![1, 0]) ^ 2 = 1 / 2 := by
  have hEq := lapK2_eigvecOf_eq_of_eq_zero hi
  have hnorm := eigvecOf_inner (laplacian adjK2) lapK2_symmetric i i
  rw [if_pos rfl, Fin.sum_univ_two] at hnorm
  simp only [Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, mul_one, mul_zero, add_zero,
    sq] at hnorm ⊢
  rw [← hEq] at hnorm
  linarith

/-- If one eigenvalue is zero, the other is exactly `2` (the trace
route). -/
theorem lapK2_other_eq_two {i j : Fin 2} (hij : i ≠ j)
    (hi : eigvalOf (laplacian adjK2) lapK2_symmetric i = 0) :
    eigvalOf (laplacian adjK2) lapK2_symmetric j = 2 := by
  have hsum := lapK2_eigvalOf_sum
  simp only [Fin.sum_univ_two] at hsum
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · have hi' : eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 0 := hi
    show eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 2
    rw [hi'] at hsum
    linarith
  · have hi' : eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 0 := hi
    show eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 2
    rw [hi'] at hsum
    linarith
  · exact absurd rfl hij

/-- The non-kernel coefficient also squares to `1/2` — by Parseval, the
two coefficients' squares sum to the signal norm `1`. -/
theorem lapK2_coeff_sq_of_other {i j : Fin 2} (hij : i ≠ j)
    (hi : eigvalOf (laplacian adjK2) lapK2_symmetric i = 0) :
    (Matrix.dotProduct (eigvecOf (laplacian adjK2) lapK2_symmetric j)
        ![1, 0]) ^ 2 = 1 / 2 := by
  have hparseval : (1 : ℝ) =
      ∑ k, (Matrix.dotProduct (eigvecOf (laplacian adjK2) lapK2_symmetric k)
          ![1, 0]) * (Matrix.dotProduct (eigvecOf (laplacian adjK2)
            lapK2_symmetric k) ![1, 0]) := by
    rw [← dotProduct_eigvecOf lapK2_symmetric ![1, 0] ![1, 0]]
    simp [Matrix.dotProduct, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · have hi' : eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 0 := hi
    have hc0 := lapK2_coeff_sq_of_eq_zero hi'
    simp only [Fin.sum_univ_two] at hparseval
    show (Matrix.dotProduct (eigvecOf (laplacian adjK2) lapK2_symmetric 1)
        ![1, 0]) ^ 2 = 1 / 2
    rw [sq] at hc0 ⊢
    linarith
  · have hi' : eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 0 := hi
    have hc1 := lapK2_coeff_sq_of_eq_zero hi'
    simp only [Fin.sum_univ_two] at hparseval
    show (Matrix.dotProduct (eigvecOf (laplacian adjK2) lapK2_symmetric 0)
        ![1, 0]) ^ 2 = 1 / 2
    rw [sq] at hc1 ⊢
    linarith
  · exact absurd rfl hij

/-- **The energy lower bound**: with the kernel mode included in the
tail (the eigenvalue-bound hypothesis dropped), the filtered coefficient
energy at every nonzero `π` is at least `1/2` — the kernel mode passes
through the filter untouched, exactly as it must. -/
theorem lapK2_energy_ge (π : ℝ) (hπ : π ≠ 0) :
    1 / 2 ≤ ∑ i, (tikhonovShrinkage π
        (eigvalOf (laplacian adjK2) lapK2_symmetric i)
      * Matrix.dotProduct (eigvecOf (laplacian adjK2) lapK2_symmetric i)
        ![1, 0]) ^ 2 := by
  obtain ⟨i₀, hi₀⟩ := lapK2_exists_zero
  fin_cases i₀
  · have hi₀' : eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 0 := hi₀
    have hc0 := lapK2_coeff_sq_of_eq_zero hi₀'
    have e0 : (tikhonovShrinkage π
          (eigvalOf (laplacian adjK2) lapK2_symmetric 0)
        * Matrix.dotProduct (eigvecOf (laplacian adjK2) lapK2_symmetric 0)
          ![1, 0]) ^ 2 = 1 / 2 := by
      rw [hi₀', shrinkage_eq_one_of_ne_zero hπ, one_mul]
      exact hc0
    have e1 : 0 ≤ (tikhonovShrinkage π
          (eigvalOf (laplacian adjK2) lapK2_symmetric 1)
        * Matrix.dotProduct (eigvecOf (laplacian adjK2) lapK2_symmetric 1)
          ![1, 0]) ^ 2 := sq_nonneg _
    simp only [Fin.sum_univ_two]
    linarith [e0, e1]
  · have hi₀' : eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 0 := hi₀
    have hc1 := lapK2_coeff_sq_of_eq_zero hi₀'
    have e1 : (tikhonovShrinkage π
          (eigvalOf (laplacian adjK2) lapK2_symmetric 1)
        * Matrix.dotProduct (eigvecOf (laplacian adjK2) lapK2_symmetric 1)
          ![1, 0]) ^ 2 = 1 / 2 := by
      rw [hi₀', shrinkage_eq_one_of_ne_zero hπ, one_mul]
      exact hc1
    have e0 : 0 ≤ (tikhonovShrinkage π
          (eigvalOf (laplacian adjK2) lapK2_symmetric 0)
        * Matrix.dotProduct (eigvecOf (laplacian adjK2) lapK2_symmetric 0)
          ![1, 0]) ^ 2 := sq_nonneg _
    simp only [Fin.sum_univ_two]
    linarith [e0, e1]

/-- **The boundary refutation at the tail level**: with the kernel mode
included, the tail-energy statement is *false* — the energy stays above
`1/2` at every nonzero `π`, so it cannot tend to `0`. The `lam ≤ λᵢ`
hypothesis is load-bearing, not decorative. -/
theorem not_lapK2_univ_tail_tendsto :
    ¬ Filter.Tendsto (fun π : ℝ =>
        ∑ i, (tikhonovShrinkage π
            (eigvalOf (laplacian adjK2) lapK2_symmetric i)
          * Matrix.dotProduct (eigvecOf (laplacian adjK2)
              lapK2_symmetric i) ![1, 0]) ^ 2)
      (𝓝 0) (𝓝 0) := by
  intro h
  rw [Metric.tendsto_nhds_nhds] at h
  obtain ⟨δ, hδ, hδ'⟩ := h (1 / 4) (by norm_num)
  have hmin0 : 0 < min (δ / 2) 1 := lt_min (by linarith) zero_lt_one
  have hminlt : min (δ / 2) 1 < δ := by
    rcases le_or_gt δ 2 with hle | hgt
    · rw [min_eq_left (by linarith)]
      linarith
    · rw [min_eq_right (by linarith)]
      linarith
  have hE := lapK2_energy_ge (min (δ / 2) 1) (ne_of_gt hmin0)
  have hdist := hδ' (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hmin0]; exact hminlt)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)] at hdist
  linarith

/-- At most one index carries the eigenvalue `2`: two would force the
trace sum to `4 ≠ 2`. -/
theorem lapK2_unique_two (i j : Fin 2)
    (hi : eigvalOf (laplacian adjK2) lapK2_symmetric i = 2)
    (hj : eigvalOf (laplacian adjK2) lapK2_symmetric j = 2) :
    i = j := by
  have hsum := lapK2_eigvalOf_sum
  simp only [Fin.sum_univ_two] at hsum
  fin_cases i <;> fin_cases j
  · rfl
  · have hi' : eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 2 := hi
    have hj' : eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 2 := hj
    rw [hi', hj'] at hsum
    norm_num at hsum
  · have hi' : eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 2 := hi
    have hj' : eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 2 := hj
    rw [hi', hj'] at hsum
    norm_num at hsum
  · rfl

/-- The eigenvalue-`2` index exists (the complement of the kernel
index). -/
theorem lapK2_exists_nonzero :
    ∃ j : Fin 2, eigvalOf (laplacian adjK2) lapK2_symmetric j = 2 := by
  obtain ⟨i₀, hi₀⟩ := lapK2_exists_zero
  fin_cases i₀
  · exact ⟨1, lapK2_other_eq_two (by decide)
      (show eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 0 from hi₀)⟩
  · exact ⟨0, lapK2_other_eq_two (by decide)
      (show eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 0 from hi₀)⟩

/-- The `1 ≤`-filter of the spectrum is exactly the singleton of the
eigenvalue-`2` index. -/
theorem lapK2_filter_eq_singleton (j : Fin 2)
    (hj : eigvalOf (laplacian adjK2) lapK2_symmetric j = 2) :
    Finset.univ.filter
        (fun i => 1 ≤ eigvalOf (laplacian adjK2) lapK2_symmetric i)
      = {j} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton]
  constructor
  · intro h1
    have hi2 : eigvalOf (laplacian adjK2) lapK2_symmetric i = 2 := by
      rcases lapK2_eigvalOf_two i with h | h
      · rw [h] at h1; norm_num at h1
      · exact h
    exact lapK2_unique_two i j hi2 hj
  · intro hsub
    rw [hsub, hj]; norm_num

/-- **The minimizer-form corollary instantiated on `K₂`** at the
filtered nonzero-mode tail: the filtered signal's coefficient energy on
the tail vanishes as `π → 0`. -/
theorem lapK2_minimizer_tail :
    Filter.Tendsto (fun π : ℝ =>
        ∑ i ∈ Finset.univ.filter
            (fun i => 1 ≤ eigvalOf (laplacian adjK2) lapK2_symmetric i),
          (Matrix.dotProduct (eigvecOf (laplacian adjK2) lapK2_symmetric i)
            (tikhonovMinimizer adjK2 adjK2_symmetric π ![1, 0])) ^ 2)
      (𝓝 0) (𝓝 0) :=
  tikhonovMinimizer_tail_energy_tendsto_zero adjK2 adjK2_symmetric
    (by norm_num) ![1, 0] _
    (fun _ hi => (Finset.mem_filter.mp hi).2)

/-- The tail energy of the minimizer at `π = 1`, pinned through the
coefficient identity: the nonzero mode's filtered coefficient is
`(1/3)·c` with `c² = 1/2`, so the energy is exactly `1/18`. -/
theorem lapK2_minimizer_tail_energy_pi_one :
    ∑ i ∈ Finset.univ.filter
        (fun i => 1 ≤ eigvalOf (laplacian adjK2) lapK2_symmetric i),
      (Matrix.dotProduct (eigvecOf (laplacian adjK2) lapK2_symmetric i)
        (tikhonovMinimizer adjK2 adjK2_symmetric 1 ![1, 0])) ^ 2
      = 1 / 18 := by
  obtain ⟨j, hj⟩ := lapK2_exists_nonzero
  obtain ⟨i₀, hi₀⟩ := lapK2_exists_zero
  have hij : i₀ ≠ j := by
    intro hcon
    rw [← hcon, hi₀] at hj
    norm_num at hj
  have hcj := lapK2_coeff_sq_of_other hij hi₀
  rw [lapK2_filter_eq_singleton j hj, Finset.sum_singleton,
    tikhonovMinimizer_dotProduct_eigvecOf adjK2 adjK2_symmetric 1 ![1, 0] j,
    hj, mul_pow, hcj]
  have hs : tikhonovShrinkage 1 2 = 1 / 3 := by
    norm_num [tikhonovShrinkage]
  rw [hs]
  norm_num

end HardFilterK2

end Scaffold.Mathlib.GraphTheory.Tikhonov.QA
