/-
  Band_QA.lean

  Purpose
  -------
  QA lemmas for the two-sided spectral band projector of
  `Scaffold.Mathlib.GraphTheory.Band` (Steps 1, 2, and 3 of
  `proposals/spectral-band-projectors.md`): band values computed
  independently of the construction, idempotence instantiated both
  through the theorem and by raw matrix arithmetic, the nestedness
  cross-law instantiated numerically, and the mode-selection interface
  witnessed in both directions — an excluded mode annihilated (and
  provably not fixed), an in-band mode fixed, a mode strictly between
  the band's endpoints fixed, and a band strictly between two
  eigenvalues equal to zero (no mode silently grabbed). The Step-2
  slice: disjoint bands' composition to zero computed through the
  theorem and by raw literal arithmetic in both orders, vector-level
  orthogonality of the images (with the same-band counter-witness
  showing the vanishing is genuinely about disjointness), the composed
  action annihilating a filtered signal, and the overlap guard — two
  bands sharing an eigenvalue compose to a provably nonzero matrix,
  refuting the hypothesis-free form of the disjointness statement. The
  Step-3 slice: the partition witness — a covering two-band family
  summing to the identity both through the completeness theorem and
  from independently pinned band values — a three-band partition with
  an empty middle band whose top threshold exactly touches the top
  eigenvalue (the closed right endpoint), the two endpoint guards (a
  family starting above the lowest mode, or ending below the highest
  one, provably fails to sum to the identity — the design note's
  "silently ignores modes" failure mode), the unconditional telescoping
  law witnessed on a deliberately non-monotone family whose junk bands
  cancel, monotone-family orthogonality instantiated, and the vector
  decomposition `∑ B_k *ᵥ x = x` on a concrete signal by both routes. The
  Step-4 slice: the Hilbert-projection specialization instantiated on the
  same fixture — the orthogonal projection onto the band's transported
  range identified with the band-filtered signal, the closest-point
  minimality instantiated at three competitors (attained with equality at
  the projection itself, strictly improved over the zero signal — the
  3-4-5 triangle — and over a generic in-band point), an independent
  raw-arithmetic cross-check of closest-point on the band's range line,
  the residual-orthogonality engine witnessed on both routes, and the
  fixed-space guard: a non-range competitor (the unfiltered signal
  itself) is strictly closer than the projection, refuting the
  hypothesis-free form of the minimality statement.

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

/-!
## Step 2: orthogonality of disjoint bands

The low band `(−1, 2]` (value `diag(1, 0)`) and the high band `(2, 4]`
(value `diag(0, 1)`) are disjoint — the shared endpoint `2 ≤ 2` is the
disjointness hypothesis in force. Every statement below is instantiated
twice: through the new theorem and by raw literal arithmetic on the
pinned band values, so a wrong composition law would fail the numeric
cross-check.
-/

/-- Raw arithmetic: the two pinned single-axis band values multiply to
zero by literal matrix multiplication, independent of every theorem. -/
theorem diag13_axis_mul_axis_raw :
    (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
      (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Raw arithmetic, flipped order. -/
theorem diag13_axis_mul_axis_raw' :
    (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) *
      (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Disjoint bands compose to zero — computed from the pinned band
values and raw literal multiplication, no theorem consumed. -/
theorem band_diag13_low_mul_high_raw :
    bandProjector diag13 diag13_symm (-1) 2 * bandProjector diag13 diag13_symm 2 4
      = 0 := by
  rw [band_diag13_low, band_diag13_high, diag13_axis_mul_axis_raw]

/-- Disjoint bands compose to zero — the theorem route. Both routes
meet at `0`: a wrong cross-law expansion would leave a nonzero literal
product. -/
theorem band_diag13_low_mul_high :
    bandProjector diag13 diag13_symm (-1) 2 * bandProjector diag13 diag13_symm 2 4
      = 0 :=
  bandProjector_mul_bandProjector_eq_zero diag13 diag13_symm (-1) 2 2 4
    (by norm_num) (by norm_num) (by norm_num)

/-- Flipped order, raw route. -/
theorem band_diag13_high_mul_low_raw :
    bandProjector diag13 diag13_symm 2 4 * bandProjector diag13 diag13_symm (-1) 2
      = 0 := by
  rw [band_diag13_low, band_diag13_high, diag13_axis_mul_axis_raw']

/-- Flipped order, theorem route. -/
theorem band_diag13_high_mul_low :
    bandProjector diag13 diag13_symm 2 4 * bandProjector diag13 diag13_symm (-1) 2
      = 0 :=
  bandProjector_mul_bandProjector_eq_zero' diag13 diag13_symm (-1) 2 2 4
    (by norm_num) (by norm_num) (by norm_num)

/-- Vector-level orthogonality, theorem route: the low-band image of
`![1, 2]` is dot-orthogonal to the high-band image of `![3, 5]`. -/
theorem band_diag13_orthogonal_vectors :
    (bandProjector diag13 diag13_symm (-1) 2 *ᵥ (![1, 2] : Fin 2 → ℝ))
      ⬝ᵥ (bandProjector diag13 diag13_symm 2 4 *ᵥ (![3, 5] : Fin 2 → ℝ))
      = 0 :=
  bandProjector_inner_eq_zero diag13 diag13_symm (-1) 2 2 4
    (by norm_num) (by norm_num) (by norm_num) _ _

/-- Vector-level orthogonality, raw route: `diag(1,0) *ᵥ ![1,2] =
![1,0]` and `diag(0,1) *ᵥ ![3,5] = ![0,5]`, whose dot product
`1·0 + 0·5` vanishes. -/
theorem band_diag13_orthogonal_vectors_raw :
    (bandProjector diag13 diag13_symm (-1) 2 *ᵥ (![1, 2] : Fin 2 → ℝ))
      ⬝ᵥ (bandProjector diag13 diag13_symm 2 4 *ᵥ (![3, 5] : Fin 2 → ℝ))
      = 0 := by
  rw [band_diag13_low, band_diag13_high]
  simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-- Counter-witness: the *same* band paired with itself is not
orthogonal — the raw computation gives `1·1 + 0·0 = 1 ≠ 0` — so the
vanishing above is genuinely about disjointness, not an artifact of the
fixture's zero entries. -/
theorem band_diag13_low_not_orthogonal_self :
    (bandProjector diag13 diag13_symm (-1) 2 *ᵥ (![1, 2] : Fin 2 → ℝ))
      ⬝ᵥ (bandProjector diag13 diag13_symm (-1) 2 *ᵥ (![1, 2] : Fin 2 → ℝ))
      ≠ 0 := by
  rw [band_diag13_low]
  simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-- The composed action annihilates, theorem route: applying the high
band after the low band kills every vector. -/
theorem band_diag13_high_after_low :
    bandProjector diag13 diag13_symm 2 4 *ᵥ
      (bandProjector diag13 diag13_symm (-1) 2 *ᵥ (![1, 2] : Fin 2 → ℝ))
      = 0 := by
  rw [Matrix.mulVec_mulVec,
    bandProjector_mul_bandProjector_eq_zero' diag13 diag13_symm (-1) 2 2 4
      (by norm_num) (by norm_num) (by norm_num),
    Matrix.zero_mulVec]

/-- The composed action annihilates, raw route: `diag(1,0) *ᵥ ![1,2] =
![1,0]`, then `diag(0,1) *ᵥ ![1,0] = ![0,0]`. -/
theorem band_diag13_high_after_low_raw :
    bandProjector diag13 diag13_symm 2 4 *ᵥ
      (bandProjector diag13 diag13_symm (-1) 2 *ᵥ (![1, 2] : Fin 2 → ℝ))
      = 0 := by
  rw [band_diag13_low, band_diag13_high]
  funext k
  fin_cases k <;> simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-- A low-band range vector is killed by the high band: `![1,0]` lies in
the low band's range (the low band fixes it) and the high band
annihilates it — the numeric companion of
`eq_zero_of_bandProjector_mulVec_eq_self`: disjoint bands share no
nonzero vector. -/
theorem band_diag13_high_kills_low_range_vector :
    bandProjector diag13 diag13_symm 2 4 *ᵥ (![1, 0] : Fin 2 → ℝ) = 0 ∧
      bandProjector diag13 diag13_symm (-1) 2 *ᵥ (![1, 0] : Fin 2 → ℝ)
        = (![1, 0] : Fin 2 → ℝ) := by
  refine ⟨?_, ?_⟩
  · rw [band_diag13_high]
    funext k
    fin_cases k <;> simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  · rw [band_diag13_low]
    funext k
    fin_cases k <;> simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-!
### The overlap guard: disjointness is load-bearing
-/

/-- Pin: the threshold-`1` projector is the first-axis projector — the
eigenvalue `1` is the only one at or below `1`. -/
theorem spectralProjector_diag13_one :
    spectralProjector diag13 diag13_symm 1 = !![1, 0; 0, 0] :=
  spectralProjector_diag13_eq 1 (by norm_num) (by norm_num)

/-- The overlapping band `(−1, 3]` covers the whole spectrum: it is the
identity. -/
theorem band_diag13_overlap_low :
    bandProjector diag13 diag13_symm (-1) 3 = 1 := by
  rw [bandProjector,
    spectralProjector_eq_one diag13 diag13_symm 3
      (fun i => by
        rcases diag13_eigvalOf_mem i with h | h
        · rw [h]; norm_num
        · rw [h]),
    spectralProjector_eq_zero diag13 diag13_symm (-1)
      (fun i => by
        rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num),
    sub_zero]

/-- The overlapping band `(1, 4]` keeps the eigenvalue-`3` mode only:
the second-axis projector. -/
theorem band_diag13_overlap_high :
    bandProjector diag13 diag13_symm 1 4 = !![0, 0; 0, 1] := by
  rw [bandProjector,
    spectralProjector_eq_one diag13 diag13_symm 4
      (fun i => by
        rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num),
    spectralProjector_diag13_one]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.one_apply]

/-- The overlap guard: the bands `(−1, 3]` and `(1, 4]` overlap — both
contain the eigenvalue `3`, so `b ≤ c` fails (`3 ≤ 1` is false) — and
their product is the nonzero second-axis projector. The hypothesis-free
form "any two bands compose to zero" is thereby refuted: the
disjointness hypothesis of `bandProjector_mul_bandProjector_eq_zero` is
load-bearing, not decorative. -/
theorem band_diag13_overlap_mul_ne_zero :
    bandProjector diag13 diag13_symm (-1) 3 * bandProjector diag13 diag13_symm 1 4
      ≠ 0 := by
  rw [band_diag13_overlap_low, band_diag13_overlap_high, one_mul]
  intro h
  have h11 := congrFun (congrFun h 1) 1
  simp at h11

/-!
## Step 3: completeness under a partition

Every family below lives on the pinned fixture (spectrum `{1, 3}`), and
each summation identity is checked twice: through the new theorem and
from band values pinned by the Step-1/Step-2 machinery — so a wrong
telescoping law or a wrong pin would break one route while the other
still computes.
-/

/-- Pin: the zero-threshold projector vanishes (both eigenvalues are
positive). -/
theorem spectralProjector_diag13_zero :
    spectralProjector diag13 diag13_symm 0 = 0 :=
  spectralProjector_eq_zero diag13 diag13_symm 0
    (fun i => by
      rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num)

/-- Raw arithmetic: the two single-axis band values of a partition add
to the identity matrix. -/
theorem diag13_axis_add_axis_raw :
    (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) +
      (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)
      = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.add_apply, Matrix.one_apply]

/-- Raw arithmetic, flipped order. -/
theorem diag13_axis_add_axis_raw' :
    (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) +
      (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
      = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.add_apply, Matrix.one_apply]

/-- An eigenvalue `3` occurs somewhere (the index other than the one
carrying `1`). -/
theorem diag13_exists_three : ∃ j : Fin 2, eigvalOf diag13 diag13_symm j = 3 := by
  obtain ⟨i, hi⟩ := diag13_exists_one
  fin_cases i
  · exact ⟨1, diag13_other_eq_three (by decide) hi⟩
  · exact ⟨0, diag13_other_eq_three (by decide) hi⟩

/-! ### The two-band partition `t k = 2k` (thresholds `0, 2, 4`) -/

/-- The two-band partition family: monotone, starting strictly below
the spectrum (`0 < 1`) and ending above it (`4 ≥ 3`). -/
def part2 : ℕ → ℝ := fun k => 2 * k

theorem part2_monotone : Monotone part2 := by
  intro a b hab
  simp only [part2]
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.2 hab) (by norm_num)

theorem part2_zero : part2 0 = 0 := by simp [part2]

theorem part2_one : part2 1 = 2 := by simp [part2]

theorem part2_two : part2 2 = 4 := by norm_num [part2]

theorem part2_cover_low (i : Fin 2) :
    part2 0 < eigvalOf diag13 diag13_symm i := by
  rw [part2_zero]
  rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num

theorem part2_cover_high (i : Fin 2) :
    eigvalOf diag13 diag13_symm i ≤ part2 2 := by
  rw [part2_two]
  rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num

/-- The partition's low band `(0, 2]` is the first-axis projector
(`P_0 = 0` below, `P_2 = e₀e₀ᵀ` at the middle threshold). -/
theorem band_diag13_part2_low :
    bandProjector diag13 diag13_symm 0 2 = !![1, 0; 0, 0] := by
  rw [bandProjector, spectralProjector_diag13_zero, sub_zero,
    spectralProjector_diag13_eq 2 (by norm_num) (by norm_num)]

/-- The partition witness, raw route: the sum computed from the two
pinned band values, no completeness theorem consumed. -/
theorem sum_band_diag13_part2_raw :
    ∑ k in Finset.range 2,
      bandProjector diag13 diag13_symm (part2 k) (part2 (k + 1)) = 1 := by
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  show bandProjector diag13 diag13_symm (part2 0) (part2 1)
      + bandProjector diag13 diag13_symm (part2 1) (part2 2) = 1
  rw [part2_zero, part2_one, part2_two, band_diag13_part2_low,
    band_diag13_high, diag13_axis_add_axis_raw]

/-- The partition witness, theorem route — both routes meet at `1`:
the covering two-band family resolves the identity. -/
theorem sum_band_diag13_part2 :
    ∑ k in Finset.range 2,
      bandProjector diag13 diag13_symm (part2 k) (part2 (k + 1)) = 1 :=
  sum_range_bandProjector_eq_one diag13 diag13_symm part2 2
    part2_cover_low part2_cover_high

/-- Distinct members of the monotone family are orthogonal, theorem
route: the two bands of the partition compose to zero. -/
theorem band_diag13_part2_orthogonal :
    bandProjector diag13 diag13_symm (part2 0) (part2 1) *
      bandProjector diag13 diag13_symm (part2 1) (part2 2) = 0 :=
  bandProjector_mul_bandProjector_eq_zero_of_monotone diag13 diag13_symm
    part2 part2_monotone 0 1 (by norm_num)

/-- The vector decomposition, theorem route: the signal `![7, −5]` is
the sum of its band components. -/
theorem sum_band_diag13_part2_mulVec :
    ∑ k in Finset.range 2, bandProjector diag13 diag13_symm (part2 k)
      (part2 (k + 1)) *ᵥ (![7, -5] : Fin 2 → ℝ)
      = (![7, -5] : Fin 2 → ℝ) :=
  sum_range_bandProjector_mulVec_eq_self diag13 diag13_symm part2 2
    part2_cover_low part2_cover_high _

/-- The vector decomposition, raw route: `diag(1,0) *ᵥ ![7,−5] =
![7,0]` plus `diag(0,1) *ᵥ ![7,−5] = ![0,−5]`, adding back to the
signal. -/
theorem sum_band_diag13_part2_mulVec_raw :
    ∑ k in Finset.range 2, bandProjector diag13 diag13_symm (part2 k)
      (part2 (k + 1)) *ᵥ (![7, -5] : Fin 2 → ℝ)
      = (![7, -5] : Fin 2 → ℝ) := by
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  show bandProjector diag13 diag13_symm (part2 0) (part2 1) *ᵥ (![7, -5] : Fin 2 → ℝ)
      + bandProjector diag13 diag13_symm (part2 1) (part2 2) *ᵥ (![7, -5] : Fin 2 → ℝ)
      = (![7, -5] : Fin 2 → ℝ)
  rw [part2_zero, part2_one, part2_two, band_diag13_part2_low,
    band_diag13_high]
  funext k
  fin_cases k <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-! ### The three-band partition `t k = k` (thresholds `0, 1, 2, 3`)

The middle band `(1, 2]` is empty — no eigenvalue lies strictly above
`1` and at most `2` — and the top threshold `3` exactly touches the top
eigenvalue, exercising the closed right endpoint of the band intervals.
-/

/-- The three-band partition family: `t k = k`, monotone by
`Nat.cast_mono`. -/
def part3 : ℕ → ℝ := fun k => (k : ℝ)

theorem part3_monotone : Monotone part3 := by
  intro a b hab
  exact Nat.cast_le.2 hab

theorem part3_cover_low (i : Fin 2) :
    part3 0 < eigvalOf diag13 diag13_symm i := by
  rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num [part3]

theorem part3_cover_high (i : Fin 2) :
    eigvalOf diag13 diag13_symm i ≤ part3 3 := by
  rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num [part3]

theorem part3_eq_zero : part3 0 = 0 := by norm_num [part3]

theorem part3_eq_one : part3 1 = 1 := by norm_num [part3]

theorem part3_eq_two : part3 2 = 2 := by norm_num [part3]

theorem part3_eq_three : part3 3 = 3 := by norm_num [part3]

/-- The partition's low band `(0, 1]`: the first-axis projector. -/
theorem band_diag13_part3_low :
    bandProjector diag13 diag13_symm 0 1 = !![1, 0; 0, 0] := by
  rw [bandProjector, spectralProjector_diag13_one,
    spectralProjector_diag13_zero, sub_zero]

/-- The partition's middle band `(1, 2]` is empty: both thresholds
select exactly the eigenvalue-`1` mode, so their difference is zero —
a zero-width member of the partition, contributing nothing. -/
theorem band_diag13_part3_mid :
    bandProjector diag13 diag13_symm 1 2 = 0 := by
  rw [bandProjector,
    spectralProjector_diag13_eq 2 (by norm_num) (by norm_num),
    spectralProjector_diag13_one, sub_self]

/-- The partition's top band `(2, 3]`: the second-axis projector — the
eigenvalue `3` sits exactly at the closed right endpoint `t 3 = 3`. -/
theorem band_diag13_part3_high :
    bandProjector diag13 diag13_symm 2 3 = !![0, 0; 0, 1] := by
  rw [bandProjector,
    spectralProjector_eq_one diag13 diag13_symm 3
      (fun i => by
        rcases diag13_eigvalOf_mem i with h | h <;> simp only [h] <;> norm_num),
    spectralProjector_diag13_eq 2 (by norm_num) (by norm_num)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.one_apply]

/-- The three-band partition sums to the identity, raw route: the
empty middle band contributes zero and the two axis projectors add to
the identity. -/
theorem sum_band_diag13_part3_raw :
    ∑ k in Finset.range 3,
      bandProjector diag13 diag13_symm (part3 k) (part3 (k + 1)) = 1 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  show bandProjector diag13 diag13_symm (part3 0) (part3 1)
      + bandProjector diag13 diag13_symm (part3 1) (part3 2)
      + bandProjector diag13 diag13_symm (part3 2) (part3 3) = 1
  rw [part3_eq_zero, part3_eq_one, part3_eq_two, part3_eq_three,
    band_diag13_part3_low, band_diag13_part3_mid, add_zero,
    band_diag13_part3_high, diag13_axis_add_axis_raw]

/-- The three-band partition sums to the identity, theorem route. -/
theorem sum_band_diag13_part3 :
    ∑ k in Finset.range 3,
      bandProjector diag13 diag13_symm (part3 k) (part3 (k + 1)) = 1 :=
  sum_range_bandProjector_eq_one diag13 diag13_symm part3 3
    part3_cover_low part3_cover_high

/-! ### The endpoint guards: covering is load-bearing both ways -/

/-- A family that starts too high: thresholds `2, 4` — the mode `1`
lies strictly below the first threshold, exactly the "silently ignores
a mode" failure mode the design note names. -/
def gap_hi : ℕ → ℝ := fun k => 2 + 2 * k

theorem gap_hi_zero : gap_hi 0 = 2 := by simp [gap_hi]

theorem gap_hi_one : gap_hi 1 = 4 := by norm_num [gap_hi]

theorem gap_hi_violates_cover_low :
    ¬ ∀ i, gap_hi 0 < eigvalOf diag13 diag13_symm i := by
  intro h
  obtain ⟨i, hi⟩ := diag13_exists_one
  have hvi := h i
  rw [hi, gap_hi_zero] at hvi
  norm_num at hvi

/-- The high-start guard: the one-band family `(2, 4]` sums to the
second-axis projector, not the identity (entry `(0,0)` is `0 ≠ 1`) —
the hypothesis-free form of completeness is refuted. -/
theorem sum_band_diag13_gap_hi_ne_one :
    ∑ k in Finset.range 1,
      bandProjector diag13 diag13_symm (gap_hi k) (gap_hi (k + 1)) ≠ 1 := by
  rw [Finset.sum_range_one]
  show bandProjector diag13 diag13_symm (gap_hi 0) (gap_hi 1) ≠ 1
  rw [gap_hi_zero, gap_hi_one, band_diag13_high]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp at h00

theorem part2_violates_cover_high :
    ¬ ∀ i, eigvalOf diag13 diag13_symm i ≤ part2 1 := by
  intro h
  obtain ⟨j, hj⟩ := diag13_exists_three
  have hvj := h j
  rw [hj, part2_one] at hvj
  norm_num at hvj

/-- The low-end guard: truncating the partition at `n = 1` (top
threshold `2` below the eigenvalue `3`) sums to the first-axis
projector, not the identity (entry `(1,1)` is `0 ≠ 1`). -/
theorem sum_band_diag13_part2_truncated_ne_one :
    ∑ k in Finset.range 1,
      bandProjector diag13 diag13_symm (part2 k) (part2 (k + 1)) ≠ 1 := by
  rw [Finset.sum_range_one]
  show bandProjector diag13 diag13_symm (part2 0) (part2 1) ≠ 1
  rw [part2_zero, part2_one, band_diag13_part2_low]
  intro h
  have h11 := congrFun (congrFun h 1) 1
  simp at h11

/-! ### The unconditional telescoping law on a non-monotone family -/

/-- A deliberately non-monotone family `4, 0, 4`: its middle band is
the negated junk value `B(4, 0] = −1`, and the telescoping law must
still hold — the junk cancels against the covering band `B(0, 4] = 1`. -/
def nonmono : ℕ → ℝ := fun k => if k = 1 then 0 else 4

theorem nonmono_zero : nonmono 0 = 4 := by simp [nonmono]

theorem nonmono_one : nonmono 1 = 0 := by simp [nonmono]

theorem nonmono_two : nonmono 2 = 4 := by simp [nonmono]

/-- The junk band: `B(4, 0] = P_0 − P_4 = 0 − 1 = −1`, the negated
covering band. -/
theorem band_diag13_four_zero :
    bandProjector diag13 diag13_symm 4 0 = -1 := by
  rw [bandProjector, spectralProjector_diag13_zero,
    spectralProjector_eq_one diag13 diag13_symm 4
      (fun i => by
        rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num),
    zero_sub]

/-- The covering band at the partition-friendly endpoints:
`B(0, 4] = P_4 − P_0 = 1 − 0 = 1`. -/
theorem band_diag13_zero_four :
    bandProjector diag13 diag13_symm 0 4 = 1 := by
  rw [bandProjector,
    spectralProjector_eq_one diag13 diag13_symm 4
      (fun i => by
        rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num),
    spectralProjector_diag13_zero, sub_zero]

/-- The telescoping law on the non-monotone family, theorem route. -/
theorem sum_band_diag13_nonmono :
    ∑ k in Finset.range 2,
      bandProjector diag13 diag13_symm (nonmono k) (nonmono (k + 1))
      = spectralProjector diag13 diag13_symm (nonmono 2)
          - spectralProjector diag13 diag13_symm (nonmono 0) :=
  sum_range_bandProjector_eq_sub diag13 diag13_symm nonmono 2

/-- Both sides of the telescoping law compute to zero on the
non-monotone family: the sum is `−1 + 1 = 0` from the pinned band
values, and the residue is `P_4 − P_4 = 1 − 1 = 0` from the pinned
extreme projectors. The law is unconditional — no order, no covering. -/
theorem sum_band_diag13_nonmono_both_zero :
    ∑ k in Finset.range 2,
      bandProjector diag13 diag13_symm (nonmono k) (nonmono (k + 1)) = 0 ∧
      spectralProjector diag13 diag13_symm (nonmono 2)
        - spectralProjector diag13 diag13_symm (nonmono 0) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_range_succ, Finset.sum_range_one]
    show bandProjector diag13 diag13_symm (nonmono 0) (nonmono 1)
        + bandProjector diag13 diag13_symm (nonmono 1) (nonmono 2) = 0
    rw [nonmono_zero, nonmono_one, nonmono_two, band_diag13_four_zero,
      band_diag13_zero_four]
    exact neg_add_cancel _
  · rw [nonmono_two, nonmono_zero,
      spectralProjector_eq_one diag13 diag13_symm 4
        (fun i => by
          rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num),
      sub_self]

/-!
## Step 4: the Hilbert-projection specialization

The band `(0, 2]` (value `diag(1, 0)`, pinned below from the pinned
threshold projectors) is the projector onto the first coordinate axis,
and the signal `![3, 4]` has band image `![3, 0]` with residual
`![0, 4]` — the 3-4-5 triangle, so every closest-point claim below has
exact numerically checkable content. Norms are pinned through the
identity `‖e v‖² = v ⬝ᵥ v` (`e` the Euclidean packaging), independent
of the projection machinery under test.
-/

/-- The band `(0, 2]` is the first-axis projector, from the pinned
threshold projector at `2` and the pinned vanishing one at `0`. -/
theorem band_diag13_pos_low :
    bandProjector diag13 diag13_symm 0 2 = !![1, 0; 0, 0] := by
  rw [bandProjector, spectralProjector_diag13_eq 2 (by norm_num)
    (by norm_num), spectralProjector_diag13_zero]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.sub_apply]

/-- Raw arithmetic: the band `(0, 2]` filters `![3, 4]` to `![3, 0]`. -/
theorem band_diag13_pos_low_mulVec :
    bandProjector diag13 diag13_symm 0 2 *ᵥ ![3, 4] = ![3, 0] := by
  rw [band_diag13_pos_low]
  funext k
  fin_cases k <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-- Raw arithmetic: the high band `(2, 4]` filters `![3, 4]` to
`![0, 4]`. -/
theorem band_diag13_high_mulVec :
    bandProjector diag13 diag13_symm 2 4 *ᵥ ![3, 4] = ![0, 4] := by
  rw [band_diag13_high]
  funext k
  fin_cases k <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-- Raw arithmetic: the band `(0, 2]` filters `![1, 1]` to `![1, 0]`
(the residual-orthogonality witness's second argument). -/
theorem band_diag13_pos_low_mulVec_one_one :
    bandProjector diag13 diag13_symm 0 2 *ᵥ ![1, 1] = ![1, 0] := by
  rw [band_diag13_pos_low]
  funext k
  fin_cases k <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-- Raw arithmetic: every point of the range line `![t, 0]` is fixed by
the band. -/
theorem band_diag13_pos_low_fixes (t : ℝ) :
    bandProjector diag13 diag13_symm 0 2 *ᵥ ![t, 0] = ![t, 0] := by
  rw [band_diag13_pos_low]
  funext k
  fin_cases k <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-- The zero vector is fixed (its own band image). -/
theorem band_diag13_pos_low_fixes_zero :
    bandProjector diag13 diag13_symm 0 2 *ᵥ 0 = 0 := by
  rw [band_diag13_pos_low, Matrix.mulVec_zero]

/-- The Euclidean norm squared of a packaged function is its dot
product with itself — the pin every numeric norm claim below routes
through (same identity as the Resolvent QA, restated locally). -/
private theorem norm_euclidean_sq (v : Fin 2 → ℝ) :
    ‖((WithLp.equiv 2 (Fin 2 → ℝ)).symm v : EuclideanSpace ℝ (Fin 2))‖ ^ 2
      = v ⬝ᵥ v := by
  have h : inner
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm v : EuclideanSpace ℝ (Fin 2))
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm v) = v ⬝ᵥ v := by
    rw [EuclideanSpace.inner_piLp_equiv_symm]
    simp [star_trivial]
  rw [← real_inner_self_eq_norm_sq, h]

/-- A nonnegative real pinned by its square. -/
private theorem norm_pin_of_sq {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r)
    (h : x ^ 2 = r ^ 2) : x = r := by
  have key : (x - r) * (x + r) = 0 := by
    have h' : (x - r) * (x + r) = x ^ 2 - r ^ 2 := by ring
    rw [h', h, sub_self]
  rcases mul_eq_zero.1 key with h' | h'
  · exact sub_eq_zero.1 h'
  · have hx0 : x = 0 := by linarith
    have hr0 : r = 0 := by linarith
    rw [hx0, hr0]

/-- Pin via the square-root form: when the dot product evaluates to a
nonnegative `r`, the packaged norm is `√r`. -/
private theorem norm_euclidean_eq_sqrt_pin {v : Fin 2 → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (h : v ⬝ᵥ v = r) :
    ‖((WithLp.equiv 2 (Fin 2 → ℝ)).symm v : EuclideanSpace ℝ (Fin 2))‖
      = Real.sqrt r :=
  ((Real.sqrt_eq_iff_eq_sq hr (norm_nonneg _)).2
    (by rw [norm_euclidean_sq, h])).symm

/-- Packaging transports subtraction (`rfl`: `WithLp` is a type synonym
on this Mathlib snapshot). -/
private theorem toEuclidean_sub (u v : Fin 2 → ℝ) :
    (WithLp.equiv 2 (Fin 2 → ℝ)).symm u -
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm v
      = (WithLp.equiv 2 (Fin 2 → ℝ)).symm (u - v) := rfl

/-- Raw arithmetic: the residual of `![3, 4]` against its band image. -/
theorem sub_three_four_three_zero :
    (![3, 4] - ![3, 0] : Fin 2 → ℝ) = ![0, 4] := by
  funext k
  fin_cases k <;> simp

/-- Raw arithmetic: the signal against a generic range point. -/
theorem sub_three_four_t_zero (t : ℝ) :
    (![3, 4] - ![t, 0] : Fin 2 → ℝ) = ![3 - t, 4] := by
  funext k
  fin_cases k <;> simp

theorem dot_zero_four_self : (![0, 4] ⬝ᵥ ![0, 4] : ℝ) = 16 := by
  simp [Matrix.dotProduct, Fin.sum_univ_two]
  norm_num

theorem dot_three_four_self : (![3, 4] ⬝ᵥ ![3, 4] : ℝ) = 25 := by
  simp [Matrix.dotProduct, Fin.sum_univ_two]
  norm_num

theorem dot_three_zero_self : (![3, 0] ⬝ᵥ ![3, 0] : ℝ) = 9 := by
  simp [Matrix.dotProduct, Fin.sum_univ_two]
  norm_num

theorem dot_zero_four_one_zero : (![0, 4] ⬝ᵥ ![1, 0] : ℝ) = 0 := by
  simp [Matrix.dotProduct, Fin.sum_univ_two]

/-- Pin: the packaged residual has norm `4`. -/
theorem norm_euclidean_zero_four :
    ‖((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![0, 4] :
      EuclideanSpace ℝ (Fin 2))‖ = 4 :=
  norm_pin_of_sq (norm_nonneg _) (by norm_num)
    (by rw [norm_euclidean_sq, dot_zero_four_self]; norm_num)

/-- Pin: the packaged signal has norm `5`. -/
theorem norm_euclidean_three_four :
    ‖((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![3, 4] :
      EuclideanSpace ℝ (Fin 2))‖ = 5 :=
  norm_pin_of_sq (norm_nonneg _) (by norm_num)
    (by rw [norm_euclidean_sq, dot_three_four_self]; norm_num)

/-- Pin: the packaged band image has norm `3`. -/
theorem norm_euclidean_three_zero :
    ‖((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![3, 0] :
      EuclideanSpace ℝ (Fin 2))‖ = 3 :=
  norm_pin_of_sq (norm_nonneg _) (by norm_num)
    (by rw [norm_euclidean_sq, dot_three_zero_self]; norm_num)

/-- **The identification, instantiated.** Mathlib's orthogonal
projection of the packaged signal onto the transported band range is
the packaged band image `![3, 0]`. -/
theorem band_diag13_hilb_identification :
    (orthogonalProjection
        (LinearMap.range
          (Matrix.toEuclideanLin (bandProjector diag13 diag13_symm 0 2)))
        ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![3, 4]) :
      EuclideanSpace ℝ (Fin 2))
      = (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![3, 0] := by
  rw [bandProjector_toEuclidean_apply_eq_orthogonalProjection
    diag13 diag13_symm 0 2 (by norm_num) ![3, 4],
    band_diag13_pos_low_mulVec]

/-- **The residual-orthogonality engine, instantiated.** The out-of-band
residual of the signal is dot-orthogonal to the band image of any
signal — here `![1, 1]`. -/
theorem band_diag13_residual_orthogonal :
    (![3, 4] - bandProjector diag13 diag13_symm 0 2 *ᵥ ![3, 4]) ⬝ᵥ
      (bandProjector diag13 diag13_symm 0 2 *ᵥ ![1, 1]) = 0 :=
  bandProjector_residual_dotProduct_eq_zero diag13 diag13_symm 0 2
    (by norm_num) ![3, 4] ![1, 1]

/-- The same fact by raw literal arithmetic on the pinned band values:
`![0, 4] ⬝ᵥ ![1, 0] = 0` — the two routes meet at `0`. -/
theorem band_diag13_residual_orthogonal_raw :
    (![3, 4] - bandProjector diag13 diag13_symm 0 2 *ᵥ ![3, 4]) ⬝ᵥ
      (bandProjector diag13 diag13_symm 0 2 *ᵥ ![1, 1]) = 0 := by
  rw [band_diag13_pos_low_mulVec, band_diag13_pos_low_mulVec_one_one,
    sub_three_four_three_zero, dot_zero_four_one_zero]

/-- **Attainment, numeric.** The distance from the signal to its band
image is exactly `4` — the closest-point distance is achieved, not
merely bounded. -/
theorem band_diag13_hilb_min_attained :
    ‖(WithLp.equiv 2 (Fin 2 → ℝ)).symm ![3, 4] -
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm
        (bandProjector diag13 diag13_symm 0 2 *ᵥ ![3, 4])‖ = 4 := by
  rw [band_diag13_pos_low_mulVec, toEuclidean_sub,
    sub_three_four_three_zero, norm_euclidean_zero_four]

/-- **Minimality over the range line.** For every point `![t, 0]` of
the band's range, the projection `![3, 0]` is at least as close to the
signal `![3, 4]` — the instantiated theorem, reduced to pinned norms:
`4 ≤ ‖![3 − t, 4]‖`. -/
theorem band_diag13_hilb_min_line (t : ℝ) :
    (4 : ℝ) ≤ ‖((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![3 - t, 4] :
      EuclideanSpace ℝ (Fin 2))‖ := by
  have h := norm_sub_bandProjector_apply_le diag13 diag13_symm 0 2
    (by norm_num) ![3, 4] ![t, 0] (band_diag13_pos_low_fixes t)
  rw [band_diag13_pos_low_mulVec, toEuclidean_sub,
    sub_three_four_three_zero, norm_euclidean_zero_four,
    toEuclidean_sub, sub_three_four_t_zero] at h
  exact h

/-- The same line inequality with the right-hand norm evaluated to a
square root. -/
theorem band_diag13_hilb_min_line_sqrt (t : ℝ) :
    (4 : ℝ) ≤ Real.sqrt ((3 - t) ^ 2 + 4 ^ 2) := by
  have hdot : (![3 - t, 4] ⬝ᵥ ![3 - t, 4] : ℝ)
      = (3 - t) ^ 2 + 4 ^ 2 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
    ring
  rw [← norm_euclidean_eq_sqrt_pin (v := ![3 - t, 4])
    (r := (3 - t) ^ 2 + 4 ^ 2)
    (by
      have hsq := sq_nonneg (3 - t)
      nlinarith)
    hdot]
  exact band_diag13_hilb_min_line t

/-- Raw arithmetic, no theorem consumed: `4 ≤ √((3 − t)² + 16)` is
plain positivity of a square — an independent hand-check of
closest-point on the band's range line that the transported theorem's
claim (`band_diag13_hilb_min_line_sqrt`) must reproduce. -/
theorem band_diag13_hilb_min_line_raw (t : ℝ) :
    (4 : ℝ) ≤ Real.sqrt ((3 - t) ^ 2 + 4 ^ 2) := by
  have hsq := sq_nonneg (3 - t)
  have h16 : (4 : ℝ) ^ 2 = 16 := by norm_num
  calc (4 : ℝ) = Real.sqrt 16 :=
        ((Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
          (by norm_num)).symm
    _ ≤ Real.sqrt ((3 - t) ^ 2 + 4 ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [h16]
        nlinarith

/-- **Minimality at the zero competitor, numeric.** The projection is
strictly closer than the zero signal: `4 ≤ 5` (the 3-4-5 triangle). -/
theorem band_diag13_hilb_min_zero_numeric : (4 : ℝ) ≤ 5 := by
  have h := norm_sub_bandProjector_apply_le diag13 diag13_symm 0 2
    (by norm_num) ![3, 4] 0 band_diag13_pos_low_fixes_zero
  rw [band_diag13_pos_low_mulVec, toEuclidean_sub,
    sub_three_four_three_zero, norm_euclidean_zero_four,
    toEuclidean_sub, sub_zero, norm_euclidean_three_four] at h
  exact h

/-- **Minimality on the high band too, numeric.** The high band's
projection `![0, 4]` of the same signal is closer than the zero signal
(`3 ≤ 5`) — the closest-point property is not locked to the low-band
fixture. -/
theorem band_diag13_hilb_high_min_zero_numeric : (3 : ℝ) ≤ 5 := by
  have h := norm_sub_bandProjector_apply_le diag13 diag13_symm 2 4
    (by norm_num) ![3, 4] 0 (by
      rw [band_diag13_high, Matrix.mulVec_zero])
  rw [band_diag13_high_mulVec, toEuclidean_sub,
    show (![3, 4] - ![0, 4] : Fin 2 → ℝ) = ![3, 0] from by
      funext k; fin_cases k <;> simp,
    norm_euclidean_three_zero,
    toEuclidean_sub, sub_zero, norm_euclidean_three_four] at h
  exact h

/-- **The fixed-space guard.** The hypothesis-free form of minimality
("the projection beats *every* vector") is false: the unfiltered signal
`![3, 4]` is not a range point (not fixed by the band), and it is
strictly closer to itself (distance `0`) than the projection is
(distance `4`). The fixed-point hypothesis is load-bearing. -/
theorem band_diag13_hilb_guard :
    ¬ ∀ y : Fin 2 → ℝ,
      ‖(WithLp.equiv 2 (Fin 2 → ℝ)).symm ![3, 4] -
        (WithLp.equiv 2 (Fin 2 → ℝ)).symm
          (bandProjector diag13 diag13_symm 0 2 *ᵥ ![3, 4])‖
        ≤ ‖(WithLp.equiv 2 (Fin 2 → ℝ)).symm ![3, 4] -
          (WithLp.equiv 2 (Fin 2 → ℝ)).symm y‖ := by
  intro h
  have h0 := h ![3, 4]
  rw [band_diag13_pos_low_mulVec, toEuclidean_sub,
    sub_three_four_three_zero, norm_euclidean_zero_four,
    toEuclidean_sub, sub_self,
    show ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (0 : Fin 2 → ℝ) :
      EuclideanSpace ℝ (Fin 2)) = 0 from rfl,
    norm_zero] at h0
  norm_num at h0

end SpectralGraphTheory.QA
