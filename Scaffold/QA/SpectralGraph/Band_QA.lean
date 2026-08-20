/-
  Band_QA.lean

  Purpose
  -------
  QA lemmas for the two-sided spectral band projector of
  `Scaffold.Mathlib.GraphTheory.Band` (Step 1 of
  `proposals/spectral-band-projectors.md`): band values computed
  independently of the construction, idempotence instantiated both
  through the theorem and by raw matrix arithmetic, the nestedness
  cross-law instantiated numerically, and the mode-selection interface
  witnessed in both directions — an excluded mode annihilated (and
  provably not fixed), an in-band mode fixed, a mode strictly between
  the band's endpoints fixed, and a band strictly between two
  eigenvalues equal to zero (no mode silently grabbed).

  Fixture: the diagonal matrix `!![1, 0; 0, 3]` on `Fin 2` — chosen
  over the dense `!![2, 1; 1, 2]` used elsewhere because its
  one-dimensional eigenspaces force the eigenvector *directions* to be
  computable (an eigenvector at eigenvalue `1` is `![±1, 0]`), so the
  band projector's value can be pinned entrywise as the hand-computed
  outer product `e₀e₀ᵀ` without any control over which sign or index
  Mathlib's spectral theorem happens to produce. The spectrum `{1, 3}`
  is pinned from trace and determinant (the same technique as the
  Resolvent/Courant–Fischer QA), independent of the projector
  machinery under test.

  Implementation note: `fin_cases` produces eta-expanded indices that
  defeat syntactic atom matching (`rw`/`linarith`); all case analyses
  coerce back to literal indices with defeq-tolerant `have`s, the
  recorded `Fin 2`/`Fin 4` trap from earlier QA runs.

  All proofs are real Lean proofs (no `sorry`/`admit`).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Band

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## Fixture: the diagonal matrix `!![1, 0; 0, 3]` and its spectrum
-/

/-- The band QA fixture: symmetric diagonal with separated spectrum
`{1, 3}`, so each eigenspace is one-dimensional along a coordinate
axis. -/
def diag13 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 3]

theorem diag13_symm : diag13.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, diag13]

theorem diag13_trace : diag13.trace = 4 := by
  simp [Matrix.trace, diag13]
  norm_num

theorem diag13_det : diag13.det = 3 := by
  rw [diag13, Matrix.det_fin_two]
  norm_num

theorem diag13_sum :
    eigvalOf diag13 diag13_symm 0 + eigvalOf diag13 diag13_symm 1 = 4 := by
  have h := eigvalOf_sum_eq_trace diag13 diag13_symm
  rwa [Fin.sum_univ_two, diag13_trace] at h

theorem diag13_prod :
    eigvalOf diag13 diag13_symm 0 * eigvalOf diag13 diag13_symm 1 = 3 := by
  have h := Matrix.IsHermitian.det_eq_prod_eigenvalues
    (isHermitian_of_isSymm diag13_symm)
  rw [diag13_det] at h
  simpa [Fin.prod_univ_two] using h.symm

/-- Every eigenvalue of the fixture is `1` or `3`: with sum `4` and
product `3`, each eigenvalue `x` satisfies `(x − 1)(x − 3) = 0`. -/
theorem diag13_eigvalOf_mem (i : Fin 2) :
    eigvalOf diag13 diag13_symm i = 1 ∨
      eigvalOf diag13 diag13_symm i = 3 := by
  have key : ∀ x y : ℝ, x + y = 4 → x * y = 3 →
      (x - 1) * (x - 3) = 0 := by
    intro x y hxy hprod
    have hr : (x - 1) * (x - 3)
        = x * x - (4 : ℝ) * x + (3 : ℝ) := by ring
    rw [hr, ← hxy, ← hprod]
    ring
  fin_cases i
  · show eigvalOf diag13 diag13_symm 0 = 1 ∨ eigvalOf diag13 diag13_symm 0 = 3
    rcases mul_eq_zero.1 (key _ _ diag13_sum diag13_prod) with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · show eigvalOf diag13 diag13_symm 1 = 1 ∨ eigvalOf diag13 diag13_symm 1 = 3
    have hsum' : eigvalOf diag13 diag13_symm 1 + eigvalOf diag13 diag13_symm 0
        = 4 := by rw [add_comm]; exact diag13_sum
    have hprod' : eigvalOf diag13 diag13_symm 1 * eigvalOf diag13 diag13_symm 0
        = 3 := by rw [mul_comm]; exact diag13_prod
    rcases mul_eq_zero.1 (key _ _ hsum' hprod') with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

theorem diag13_exists_one : ∃ i : Fin 2, eigvalOf diag13 diag13_symm i = 1 := by
  by_contra hcon
  push_neg at hcon
  have hsum := diag13_sum
  rcases diag13_eigvalOf_mem 0 with h0 | h0
  · exact hcon 0 h0
  · rcases diag13_eigvalOf_mem 1 with h1 | h1
    · exact hcon 1 h1
    · rw [h0, h1] at hsum
      norm_num at hsum

/-- Eigenvalue `1` occurs at exactly one index: two distinct indices
both carrying it would force the trace sum to `2 ≠ 4`. -/
theorem diag13_unique_one (i j : Fin 2)
    (hi : eigvalOf diag13 diag13_symm i = 1)
    (hj : eigvalOf diag13 diag13_symm j = 1) : i = j := by
  by_contra hne
  have hsum := diag13_sum
  fin_cases i <;> fin_cases j
  · exact absurd rfl hne
  · have ha : eigvalOf diag13 diag13_symm 0 = 1 := hi
    have hb : eigvalOf diag13 diag13_symm 1 = 1 := hj
    rw [ha, hb] at hsum
    norm_num at hsum
  · have ha : eigvalOf diag13 diag13_symm 1 = 1 := hi
    have hb : eigvalOf diag13 diag13_symm 0 = 1 := hj
    rw [ha, hb] at hsum
    norm_num at hsum
  · exact absurd rfl hne

/-- The index not carrying eigenvalue `1` carries eigenvalue `3`. -/
theorem diag13_other_eq_three {i j : Fin 2} (hij : i ≠ j)
    (hi : eigvalOf diag13 diag13_symm i = 1) :
    eigvalOf diag13 diag13_symm j = 3 := by
  rcases diag13_eigvalOf_mem j with h | h
  · exact absurd (diag13_unique_one j i h hi) hij.symm
  · exact h

/-!
## Eigenvector directions at the two eigenvalues
-/

/-- An eigenvector at eigenvalue `1` points along the first axis: its
second entry vanishes and its first entry squares to `1` (the sign is
whatever the spectral theorem chose; the outer product below does not
depend on it). -/
theorem eigvecOf_diag13_one (i : Fin 2)
    (hi : eigvalOf diag13 diag13_symm i = 1) :
    eigvecOf diag13 diag13_symm i 1 = 0 ∧
      eigvecOf diag13 diag13_symm i 0 * eigvecOf diag13 diag13_symm i 0
        = 1 := by
  have hev : diag13 *ᵥ eigvecOf diag13 diag13_symm i
      = eigvalOf diag13 diag13_symm i • eigvecOf diag13 diag13_symm i :=
    (isHermitian_of_isSymm diag13_symm).mulVec_eigenvectorBasis i
  rw [hi] at hev
  have h1 := congrFun hev 1
  simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    Pi.smul_apply, smul_eq_mul, one_mul] at h1
  rw [show diag13 1 0 = (0 : ℝ) from by simp [diag13],
      show diag13 1 1 = (3 : ℝ) from by simp [diag13]] at h1
  simp only [zero_mul, zero_add] at h1
  have hv1 : eigvecOf diag13 diag13_symm i 1 = 0 := by linarith
  refine ⟨hv1, ?_⟩
  have hnorm := eigvecOf_inner diag13 diag13_symm i i
  rw [if_pos rfl, Fin.sum_univ_two, hv1] at hnorm
  simpa using hnorm

/-- An eigenvector at eigenvalue `3` points along the second axis. -/
theorem eigvecOf_diag13_three (i : Fin 2)
    (hi : eigvalOf diag13 diag13_symm i = 3) :
    eigvecOf diag13 diag13_symm i 0 = 0 ∧
      eigvecOf diag13 diag13_symm i 1 * eigvecOf diag13 diag13_symm i 1
        = 1 := by
  have hev : diag13 *ᵥ eigvecOf diag13 diag13_symm i
      = eigvalOf diag13 diag13_symm i • eigvecOf diag13 diag13_symm i :=
    (isHermitian_of_isSymm diag13_symm).mulVec_eigenvectorBasis i
  rw [hi] at hev
  have h0 := congrFun hev 0
  simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    Pi.smul_apply, smul_eq_mul] at h0
  rw [show diag13 0 0 = (1 : ℝ) from by simp [diag13],
      show diag13 0 1 = (0 : ℝ) from by simp [diag13]] at h0
  simp only [one_mul, zero_mul, add_zero] at h0
  have hv0 : eigvecOf diag13 diag13_symm i 0 = 0 := by linarith
  refine ⟨hv0, ?_⟩
  have hnorm := eigvecOf_inner diag13 diag13_symm i i
  rw [if_pos rfl, Fin.sum_univ_two, hv0] at hnorm
  simpa using hnorm

/-- No eigenvector of the fixture is the zero vector (unit norm). -/
theorem eigvecOf_diag13_ne_zero (i : Fin 2) :
    eigvecOf diag13 diag13_symm i ≠ 0 := by
  intro hz
  have hnorm := eigvecOf_inner diag13 diag13_symm i i
  rw [if_pos rfl, Fin.sum_univ_two, hz] at hnorm
  simp at hnorm

/-!
## The projector pin: threshold in `[1, 3)` selects exactly the first
axis
-/

/-- At any threshold in `[1, 3)`, the spectral projector is the
hand-computed outer product `e₀e₀ᵀ = !![1, 0; 0, 0]`: the threshold
filter is the singleton carrying eigenvalue `1`, and that eigenvector's
outer product is sign-independent (`s² = 1`, second entry `0`). This is
the proposal's positive witness — the projector value pinned against a
hand-computed eigenvector sum. -/
theorem spectralProjector_diag13_eq (c : ℝ) (hc1 : (1 : ℝ) ≤ c)
    (hc3 : c < 3) :
    spectralProjector diag13 diag13_symm c = !![1, 0; 0, 0] := by
  obtain ⟨i1, hi1⟩ := diag13_exists_one
  have hfilter : (Finset.univ : Finset (Fin 2)).filter
      (fun i => eigvalOf diag13 diag13_symm i ≤ c) = {i1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hle
      rcases diag13_eigvalOf_mem i with h | h
      · exact diag13_unique_one i i1 h hi1
      · rw [h] at hle
        linarith
    · intro h
      rw [h, hi1]
      exact hc1
  obtain ⟨hv1, hv0⟩ := eigvecOf_diag13_one i1 hi1
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [spectralProjector, Matrix.of_apply, hfilter, hv1, hv0]

/-!
## Band values, computed independently
-/

/-- The low band `(−1, 2]` is the first-axis projector. -/
theorem band_diag13_low :
    bandProjector diag13 diag13_symm (-1) 2 = !![1, 0; 0, 0] := by
  rw [bandProjector_eq_spectralProjector_of_lt diag13 diag13_symm (-1) 2
      (fun i => by
        rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num),
    spectralProjector_diag13_eq 2 (by norm_num) (by norm_num)]

/-- The high band `(2, 4]` is the second-axis projector. -/
theorem band_diag13_high :
    bandProjector diag13 diag13_symm 2 4 = !![0, 0; 0, 1] := by
  rw [bandProjector, spectralProjector_eq_one diag13 diag13_symm 4
      (fun i => by
        rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num),
    spectralProjector_diag13_eq 2 (by norm_num) (by norm_num)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.one_apply]

/-- The covering band `(−1, 4]` is the identity (the two-band instance
of completeness). -/
theorem band_diag13_full : bandProjector diag13 diag13_symm (-1) 4 = 1 :=
  bandProjector_eq_one diag13 diag13_symm (-1) 4
    (fun i => by
      rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num)
    (fun i => by
      rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num)

/-- A band strictly between the two eigenvalues is zero: `(3/2, 5/2]`
contains no mode, and none is silently grabbed — the guard against the
gapped-definition failure mode the proposal's design note names. -/
theorem band_diag13_gap :
    bandProjector diag13 diag13_symm (3 / 2) (5 / 2) = 0 := by
  rw [bandProjector,
    spectralProjector_diag13_eq (5 / 2) (by norm_num) (by norm_num),
    spectralProjector_diag13_eq (3 / 2) (by norm_num) (by norm_num)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

/-!
## Idempotence and the nestedness cross-law, instantiated numerically
-/

/-- Raw arithmetic: the first-axis projector squares to itself,
computed by matrix multiplication on literals, independent of every
theorem. -/
theorem diag13_low_axis_mul_self :
    (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
      = (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The low band is idempotent, computed by rewriting to raw arithmetic
(`band_diag13_low` on both factors, then literal multiplication). -/
theorem band_diag13_low_mul_self :
    bandProjector diag13 diag13_symm (-1) 2 * bandProjector diag13 diag13_symm (-1) 2
      = (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [band_diag13_low, diag13_low_axis_mul_self]

/-- The idempotence theorem instantiated at the low band. -/
theorem band_diag13_low_idempotent :
    bandProjector diag13 diag13_symm (-1) 2 * bandProjector diag13 diag13_symm (-1) 2
      = bandProjector diag13 diag13_symm (-1) 2 :=
  bandProjector_idempotent diag13 diag13_symm (-1) 2 (by norm_num)

/-- The nestedness cross-law instantiated numerically in one order:
`P_2 * P_4 = P_2`, both sides computed from the pins. -/
theorem spectralProjector_diag13_mul_low :
    spectralProjector diag13 diag13_symm 2 * spectralProjector diag13 diag13_symm 4
      = spectralProjector diag13 diag13_symm 2 := by
  rw [spectralProjector_eq_one diag13 diag13_symm 4
      (fun i => by
        rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num),
    mul_one, spectralProjector_diag13_eq 2 (by norm_num) (by norm_num)]

/-- The nestedness cross-law instantiated in the other order:
`P_4 * P_2 = P_2` as well. -/
theorem spectralProjector_diag13_mul_low' :
    spectralProjector diag13 diag13_symm 4 * spectralProjector diag13 diag13_symm 2
      = spectralProjector diag13 diag13_symm 2 := by
  rw [spectralProjector_eq_one diag13 diag13_symm 4
      (fun i => by
        rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num),
    one_mul, spectralProjector_diag13_eq 2 (by norm_num) (by norm_num)]

/-!
## Mode selection: the action interface witnessed in both directions
-/

/-- The excluded mode is genuinely absent from the band's range-side
action: the eigenvalue-`1` eigenvector is annihilated by the high band
`(2, 4]` (its eigenvalue is at most the lower endpoint `2`). -/
theorem band_diag13_high_excludes_low_mode (i : Fin 2)
    (hi : eigvalOf diag13 diag13_symm i = 1) :
    bandProjector diag13 diag13_symm 2 4 *ᵥ eigvecOf diag13 diag13_symm i = 0 :=
  bandProjector_mulVec_eigvecOf_eq_zero_left diag13 diag13_symm 2 4
    (by norm_num) i (by rw [hi]; norm_num)

/-- The excluded mode is not fixed: annihilation meets a nonzero vector,
so a definition that silently kept out-of-band modes would fail here. -/
theorem band_diag13_high_not_fix_low_mode (i : Fin 2)
    (hi : eigvalOf diag13 diag13_symm i = 1) :
    bandProjector diag13 diag13_symm 2 4 *ᵥ eigvecOf diag13 diag13_symm i
      ≠ eigvecOf diag13 diag13_symm i := by
  rw [band_diag13_high_excludes_low_mode i hi]
  exact Ne.symm (eigvecOf_diag13_ne_zero i)

/-- A mode strictly between the band's endpoints is fixed: the
eigenvalue-`3` eigenvector lies strictly inside `(2, 4]`. -/
theorem band_diag13_high_fixes_high_mode (i : Fin 2)
    (hi : eigvalOf diag13 diag13_symm i = 3) :
    bandProjector diag13 diag13_symm 2 4 *ᵥ eigvecOf diag13 diag13_symm i
      = eigvecOf diag13 diag13_symm i :=
  bandProjector_mulVec_eigvecOf_self diag13 diag13_symm 2 4 i
    (by rw [hi]; norm_num) (by rw [hi]; norm_num)

/-- The low band fixes the eigenvalue-`1` mode (theorem form). -/
theorem band_diag13_low_fixes_low_mode (i : Fin 2)
    (hi : eigvalOf diag13 diag13_symm i = 1) :
    bandProjector diag13 diag13_symm (-1) 2 *ᵥ eigvecOf diag13 diag13_symm i
      = eigvecOf diag13 diag13_symm i :=
  bandProjector_mulVec_eigvecOf_self diag13 diag13_symm (-1) 2 i
    (by rw [hi]; norm_num) (by rw [hi]; norm_num)

/-- The low band's action computed by raw arithmetic on the pinned
matrix value and the pinned eigenvector direction — the numeric
cross-check of `band_diag13_low_fixes_low_mode`:
`!![1, 0; 0, 0] *ᵥ ![s, 0] = ![s, 0]`, with the direction pin
supplying `v 1 = 0`. -/
theorem band_diag13_low_mulVec_numeric (i : Fin 2)
    (hi : eigvalOf diag13 diag13_symm i = 1) :
    (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ
        eigvecOf diag13 diag13_symm i
      = eigvecOf diag13 diag13_symm i := by
  obtain ⟨hv1, -⟩ := eigvecOf_diag13_one i hi
  funext k
  fin_cases k <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, hv1]

end SpectralGraphTheory.QA
