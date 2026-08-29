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
import Scaffold.Mathlib.GraphTheory.Spectral
import Scaffold.Mathlib.GraphTheory.Cheeger

/-!
# The general (irregular) normalized Laplacian

Backlog item 2 of the broad-SGT program: the symmetric normalized
Laplacian `L_sym = I - D^{-1/2} A D^{-1/2}` for *arbitrary* graphs with
positive degrees, removing the `d`-regular restriction of
`SpectralGraphTheory.regularNormalizedLaplacian`.

The obstruction recorded in the backlog was the absence of a matrix
square root in the pinned Mathlib. The observation implemented here is
that only a **diagonal** square root is ever needed: `D^{1/2}` is the
diagonal matrix of `Real.sqrt (deg A i)`, which is a real definition
requiring no matrix machinery. The reciprocal `D^{-1/2}` is likewise
diagonal.

Delivered (all proved, no axioms):

- `degreeSqrt`, `degreeInvSqrt` — the diagonal `√D` and `1/√D` matrices;
- `degreeSqrt_mul_degreeSqrt` — `√D √D = degreeMatrix` (nonneg degrees);
- `degreeSqrt_mul_degreeInvSqrt` — `√D (1/√D) = 1` (positive degrees);
- `degreeSqrt_mulVec_apply` / `degreeInvSqrt_mulVec_apply` — the entry
  forms of the conjugating actions (the interface the mixing program's
  kernel-characterization transfer and QA consume);
- `normalizedLaplacian` — `L_sym = 1 - (1/√D) A (1/√D)`;
- `normalizedLaplacian_symmetric` — symmetry for symmetric `A`;
- `degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt` — the congruence
  `√D L_sym √D = D - A = laplacian A`: the square roots cancel, so this
  is the exact square-root-free-shaped relation between the normalized
  and combinatorial worlds (all quadratic-form statements transfer);
- `normalizedLaplacian_eq_regularNormalizedLaplacian` — agreement with
  the regular cone: on `d`-regular graphs the general definition
  specializes to `regularNormalizedLaplacian A d`;
- `walkTransitionMatrix_mulVec_one` — the constant fix `P *ᵥ 1 = 1`
  (row-stochasticity in vector form; the stationary direction of the
  density dynamics, consumed by the mixing program's centered-evolution
  step).

Delivered 2026-08-29 (the degenerate-degree corner audit,
`proposals/matrix-hoeffding-spectral-gap-estimation.md`'s window-family
honesty notes; all proved, no axioms):

- `degreeInvSqrt_apply_eq_zero_iff` — the reciprocal degree factor
  vanishes exactly at nonpositive degrees (both the zero corner and the
  negative corner, the `p ≠ ½` outcomes route);
- `normalizedLaplacian_eq_one_of_forall_deg_nonpos` — at all-nonpositive
  degrees the normalized Laplacian degenerates to the *identity* `1`,
  whose sorted spectrum is `1` (`Spectral.evals_one`), not the zero
  matrix's `0` — the junk corner refutation-fixture design in this
  family must predict correctly.

Delivered 2026-08-22 (`proposals/mixing-time-bound.md` Step 1; all
proved, no axioms) — the eigenpair transfer through the similarity:

- `walkLaplacian_mulVec_degreeInvSqrt` / `normalizedLaplacian_mulVec_degreeSqrt`
  — eigenpairs transfer in **both directions** between `L_sym` and the
  non-symmetric `L_walk` by conjugating the eigenvector with `1/√D`/`√D`,
  at the same eigenvalue;
- `walkTransitionMatrix_mulVec_degreeInvSqrt` — the transition-matrix
  form: a `μ`-eigenpair of `L_sym` gives a `(1 - μ)`-eigenpair of
  `P = D⁻¹A`;
- `walkLaplacian_mulVec_eigvecOf` / `walkTransitionMatrix_mulVec_eigvecOf`
  — the transfer instantiated at the spectral-theorem eigenbasis of
  `L_sym`;
- `walk_eigvec_expansion` — completeness of the transferred family: every
  vector is reconstructed from the transferred walk eigenvectors (the
  diagonalizability interface the mixing-decay step consumes);
- `walkEvals` with
  `exists_eigenvector_walkTransitionMatrix_eq_walkEvals` — the walk
  spectrum `1 - evals L_sym`, each entry certified a genuine eigenvalue
  of `P` by an explicit transferred eigenvector witness;
- `degreeSqrt_mulVec_pow_walkTransitionMatrix` — the conjugated-power
  transfer: a power of the non-symmetric walk matrix, conjugated by
  `√D`, is the same power of the *symmetric* `1 − L_sym` (the
  matrix-power layer of the mixing program's Step 3, through the
  commutation form `degreeSqrt_mul_walkTransitionMatrix_eq`).

The pinned Mathlib snapshot has no general
similar-matrices-share-eigenvalues interface (surveyed 2026-08-22: no
`IsSimilar`, no charpoly-conjugation invariance), so the transfer is
proved directly at the diagonal case from the similarity identity — the
route `proposals/mixing-time-bound.md` anticipated as the cheaper branch.
-/

namespace SpectralGraphTheory

open Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Diagonal degree square roots
-/

/-- The diagonal matrix `√D` of square roots of the degrees. Real
definition: only the pointwise `Real.sqrt` is used, so no matrix square
root is required. Noncomputable because `Real.sqrt` is. -/
noncomputable def degreeSqrt (A : WAdj (V := V)) : Matrix V V ℝ :=
  Matrix.diagonal (fun i => Real.sqrt (deg A i))

/-- The diagonal matrix `D^{-1/2}` of reciprocal square roots of the
degrees. Noncomputable because `Real.sqrt` and `ℝ` inversion are. -/
noncomputable def degreeInvSqrt (A : WAdj (V := V)) : Matrix V V ℝ :=
  Matrix.diagonal (fun i => (Real.sqrt (deg A i))⁻¹)

/-- `√D √D = D`: squaring the diagonal degree square root recovers the
degree matrix (degrees nonnegative). -/
theorem degreeSqrt_mul_degreeSqrt (A : WAdj (V := V))
    (hdeg : ∀ i, 0 ≤ deg A i) :
    degreeSqrt A * degreeSqrt A = degreeMatrix A := by
  rw [degreeSqrt, Matrix.diagonal_mul_diagonal,
    show degreeMatrix A = Matrix.diagonal (deg A) from rfl]
  funext i j
  simp only [Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp only [if_pos rfl]
    exact Real.mul_self_sqrt (hdeg i)
  · simp [h]

/-- `√D (1/√D) = 1` when every degree is positive: the two diagonal
matrices are inverse. -/
theorem degreeSqrt_mul_degreeInvSqrt (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) :
    degreeSqrt A * degreeInvSqrt A = 1 := by
  rw [degreeSqrt, degreeInvSqrt, Matrix.diagonal_mul_diagonal,
    show (1 : Matrix V V ℝ) = Matrix.diagonal (fun _ => 1) from rfl]
  funext i j
  simp only [Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp only [if_pos rfl]
    exact mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (hd i))
  · simp [h]

/-- `(1/√D) √D = 1` when every degree is positive. -/
theorem degreeInvSqrt_mul_degreeSqrt (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) :
    degreeInvSqrt A * degreeSqrt A = 1 := by
  rw [degreeInvSqrt, degreeSqrt, Matrix.diagonal_mul_diagonal,
    show (1 : Matrix V V ℝ) = Matrix.diagonal (fun _ => 1) from rfl]
  funext i j
  simp only [Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp only [if_pos rfl]
    exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (hd i))
  · simp [h]

/-- Entry form of the degree-square-root action:
`(√D *ᵥ f) i = √(deg A i) * f i`. The entry-level interface the
mixing program's conjugation lemmas and QA consume. -/
theorem degreeSqrt_mulVec_apply (A : WAdj (V := V)) (f : V → ℝ) (i : V) :
    (degreeSqrt A *ᵥ f) i = Real.sqrt (deg A i) * f i := by
  simp [degreeSqrt, Matrix.mulVec_diagonal]

/-- Entry form of the reciprocal action:
`((1/√D) *ᵥ f) i = (√(deg A i))⁻¹ * f i`. -/
theorem degreeInvSqrt_mulVec_apply (A : WAdj (V := V)) (f : V → ℝ) (i : V) :
    (degreeInvSqrt A *ᵥ f) i = (Real.sqrt (deg A i))⁻¹ * f i := by
  simp [degreeInvSqrt, Matrix.mulVec_diagonal]

/-!
## The normalized Laplacian
-/

/-- The general (irregular) symmetric normalized Laplacian
`L_sym = I - D^{-1/2} A D^{-1/2}`, defined through the diagonal matrices
`degreeInvSqrt`. For graphs with positive degrees and symmetric `A` this
is symmetric (`normalizedLaplacian_symmetric`), congruent to the
combinatorial Laplacian
(`degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt`), and agrees with
`regularNormalizedLaplacian` on `d`-regular graphs
(`normalizedLaplacian_eq_regularNormalizedLaplacian`). Noncomputable
because `Real.sqrt` and `ℝ` inversion are. -/
noncomputable def normalizedLaplacian (A : WAdj (V := V)) :
    Matrix V V ℝ :=
  1 - degreeInvSqrt A * A * degreeInvSqrt A

/-- The normalized Laplacian of a symmetric adjacency matrix is
symmetric: transposing the diagonal congruence `T A T` exchanges `A`
with its transpose and leaves the diagonal factors in place. -/
theorem normalizedLaplacian_symmetric (A : WAdj (V := V))
    (hA : A.IsSymm) :
    (normalizedLaplacian A).IsSymm := by
  have hT : (degreeInvSqrt A)ᵀ = degreeInvSqrt A :=
    Matrix.diagonal_transpose _
  show (normalizedLaplacian A)ᵀ = normalizedLaplacian A
  rw [normalizedLaplacian, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_mul, Matrix.transpose_mul, hT, hA, Matrix.mul_assoc]

/-- The congruence bridge to the combinatorial center:
`√D L_sym √D = D - A = laplacian A`. The square roots cancel exactly
(`√D (1/√D) = 1`), so this identity is the square-root-free-shaped
relation between the normalized and combinatorial worlds: every
quadratic-form statement about `laplacian` transfers to the normalized
setting by substituting `x = √D y`. -/
theorem degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt
    (A : WAdj (V := V)) (hd : ∀ i, 0 < deg A i) :
    degreeSqrt A * normalizedLaplacian A * degreeSqrt A = laplacian A := by
  have hST : degreeSqrt A * degreeInvSqrt A = 1 :=
    degreeSqrt_mul_degreeInvSqrt A hd
  have hTS : degreeInvSqrt A * degreeSqrt A = 1 :=
    degreeInvSqrt_mul_degreeSqrt A hd
  have hkey : degreeSqrt A * (degreeInvSqrt A * A * degreeInvSqrt A)
      * degreeSqrt A = A := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hST, Matrix.one_mul,
      Matrix.mul_assoc, hTS, Matrix.mul_one]
  rw [normalizedLaplacian, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, hkey, degreeSqrt_mul_degreeSqrt A
      (fun i => le_of_lt (hd i)), laplacian]

/-- The left-multiplied congruence: `L_sym √D = (1/√D) L`, the identity
through which the normalized Laplacian's kernel is located — multiply the
combinatorial kernel equation by `1/√D`. -/
theorem normalizedLaplacian_mul_degreeSqrt (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) :
    normalizedLaplacian A * degreeSqrt A
      = degreeInvSqrt A * laplacian A := by
  have h1 : degreeInvSqrt A * (degreeSqrt A * normalizedLaplacian A
      * degreeSqrt A)
      = normalizedLaplacian A * degreeSqrt A := by
    rw [show degreeSqrt A * normalizedLaplacian A * degreeSqrt A
        = degreeSqrt A * (normalizedLaplacian A * degreeSqrt A) from
        Matrix.mul_assoc _ _ _]
    rw [← Matrix.mul_assoc, degreeInvSqrt_mul_degreeSqrt A hd,
      Matrix.one_mul]
  rw [← degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt A hd, h1]

/-- **The kernel vector of the normalized Laplacian is the stretched
constant `√D · onesVec`, not `onesVec`.** This is the structural fact
that separates the irregular from the regular variational picture: on a
genuinely irregular graph `L_sym *ᵥ onesVec ≠ 0`, so the delivered
`secondEval_le_rayleigh` (orthogonality to `onesVec`) cannot express
Cheeger-type test-vector arguments, while this vector can. Proof: the
left-multiplied congruence moves the combinatorial row-sum identity
(`laplacian_ones_in_kernel`) across the degree scaling. First consumer:
the irregular Cheeger upper bound
(`GraphTheory.VariationalTransfer.cheeger_upper_bound_normalized`,
2026-08-25). -/
theorem normalizedLaplacian_mulVec_degreeSqrt_onesVec (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) :
    normalizedLaplacian A *ᵥ (degreeSqrt A *ᵥ onesVec) = 0 := by
  have h1 : (normalizedLaplacian A * degreeSqrt A) *ᵥ onesVec = 0 := by
    rw [normalizedLaplacian_mul_degreeSqrt A hd, ← Matrix.mulVec_mulVec,
      laplacian_ones_in_kernel A, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec]
  exact h1

/-!
## Degenerate-degree corners

The definition's honest junk behavior, pinned as theorems (the corner
audit of `proposals/matrix-hoeffding-spectral-gap-estimation.md`'s
window-family honesty notes, 2026-08-29). At a vertex of nonpositive
degree, `Real.sqrt` of a nonpositive number is `0` and `0⁻¹ = 0`, so the
reciprocal degree factor vanishes; if *every* degree is nonpositive the
whole congruence collapses and `normalizedLaplacian` degenerates to the
*identity* `1` — whose sorted spectrum is `1` at every index
(`Spectral.evals_one`), **not** the zero matrix's `0`. Two corners land
here: the zero-degree corner (the all-false outcomes of the
edge-resampling designs at any `p`) and the negative-degree corner (the
outcomes of designs at `p ≠ ½`, where resampled adjacencies can carry
negative row sums). Predicting refutation fixtures against such
outcomes means predicting the identity's junk spectrum; these lemmas
make that a shelf fact rather than a spike finding.
-/

/-- The reciprocal degree factor vanishes exactly at nonpositive
degrees — both the zero corner (`√0 = 0`, `0⁻¹ = 0`) and the negative
corner (`Real.sqrt` of a negative number is `0`) — while a positive
degree keeps it nonzero. -/
theorem degreeInvSqrt_apply_eq_zero_iff (A : WAdj (V := V)) (i : V) :
    degreeInvSqrt A i i = 0 ↔ deg A i ≤ 0 := by
  rw [degreeInvSqrt, Matrix.diagonal_apply_eq]
  constructor
  · intro h
    by_contra hpos
    push_neg at hpos
    exact (inv_ne_zero (Real.sqrt_ne_zero'.mpr hpos)) h
  · intro h
    rw [Real.sqrt_eq_zero_of_nonpos h, _root_.inv_zero]

/-- **The identity degeneration**: at all-nonpositive degrees the
normalized Laplacian is the identity matrix `1` (the reciprocal factor
is the zero matrix, and `1 − 0 = 1`) — the degenerate corner whose junk
spectrum is `1`, not the zero matrix's `0`. QA:
`Scaffold.QA.Derived.EdgePerturbation`'s degenerate-degree corner audit
(both corners witnessed, the spectral contrast pinned). -/
theorem normalizedLaplacian_eq_one_of_forall_deg_nonpos (A : WAdj (V := V))
    (hdeg : ∀ i, deg A i ≤ 0) :
    normalizedLaplacian A = 1 := by
  have hd0 : degreeInvSqrt A = 0 := by
    ext i j
    by_cases h : i = j
    · subst h
      rw [degreeInvSqrt, Matrix.diagonal_apply_eq, Matrix.zero_apply,
        Real.sqrt_eq_zero_of_nonpos (hdeg i), _root_.inv_zero]
    · rw [Matrix.zero_apply, degreeInvSqrt]
      simp [Matrix.diagonal_apply, h]
  rw [normalizedLaplacian, hd0]
  simp

/-- Agreement with the regular cone: on a `d`-regular graph with
positive degree, the general normalized Laplacian *is*
`regularNormalizedLaplacian A d` (the two normalizations coincide
exactly when all degrees are equal). -/
theorem normalizedLaplacian_eq_regularNormalizedLaplacian
    (A : WAdj (V := V)) (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d) :
    normalizedLaplacian A = regularNormalizedLaplacian A d := by
  have hs : Real.sqrt d ≠ 0 := Real.sqrt_ne_zero'.mpr hdpos
  have hsq : Real.sqrt d * Real.sqrt d = d :=
    Real.mul_self_sqrt hdpos.le
  have hentry : ∀ i j : V,
      (degreeInvSqrt A * A * degreeInvSqrt A) i j = d⁻¹ * A i j := by
    intro i j
    simp only [degreeInvSqrt, Matrix.diagonal_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, hd i, hd j]
    field_simp [hs, hsq]
  ext i j
  simp only [normalizedLaplacian, regularNormalizedLaplacian,
    Matrix.sub_apply, Pi.one_apply, Matrix.one_apply, Matrix.smul_apply,
    smul_eq_mul, hentry]

/-!
## The walk form (general, irregular)
-/

/-- The walk transition matrix of an arbitrary graph with positive
degrees: `P = D⁻¹ A`, i.e. `P i j = A i j / deg A i`. Row-stochastic
(`walkTransitionMatrix_row_sum`); this is the transition kernel of the
simple random walk on a general (irregular) weighted graph — the
interface Markov-chain consumers need. Noncomputable because `ℝ`
inversion is. -/
noncomputable def walkTransitionMatrix (A : WAdj (V := V)) :
    Matrix V V ℝ :=
  Matrix.diagonal (fun i => (deg A i)⁻¹) * A

/-- Row-stochasticity of the general walk transition matrix: for
positive degrees, every row of `P = D⁻¹ A` sums to one. This removes the
`d`-regularity restriction of `RandomWalk.transitionMatrix_row_sum`. -/
theorem walkTransitionMatrix_row_sum (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) (i : V) :
    ∑ j, walkTransitionMatrix A i j = 1 := by
  simp only [walkTransitionMatrix, Matrix.diagonal_mul, ← Finset.mul_sum,
    deg]
  exact inv_mul_cancel₀ (ne_of_gt (hd i))

/-- Entry form of the general walk transition matrix:
`P i j = (deg A i)⁻¹ * A i j`. The entry-level interface that
detailed-balance (`Stationary.walk_detailed_balance`) and per-edge flow
computations consume. -/
theorem walkTransitionMatrix_apply (A : WAdj (V := V)) (i j : V) :
    walkTransitionMatrix A i j = (deg A i)⁻¹ * A i j := by
  simp only [walkTransitionMatrix, Matrix.diagonal_mul]

/-- The constant fix: row-stochasticity in vector form, `P *ᵥ 1 = 1`.
The stationary direction of the walk's density dynamics — the piece the
mixing program's centered-evolution step
(`Mixing.walkDensity_sub_one`) consumes alongside
`walkDensity_succ` to evolve the *centered* density. -/
theorem walkTransitionMatrix_mulVec_one (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) :
    walkTransitionMatrix A *ᵥ (1 : V → ℝ) = 1 := by
  funext i
  simp only [Matrix.mulVec, Matrix.dotProduct, Pi.one_apply, mul_one,
    walkTransitionMatrix_row_sum A hd i]

/-- The walk Laplacian of an arbitrary graph with positive degrees:
`L_walk = I - D⁻¹ A`. Unlike `normalizedLaplacian` this matrix is *not*
symmetric in general (`(D⁻¹A)ᵀ = A D⁻¹ ≠ D⁻¹ A` for irregular degrees);
it is similar to the symmetric normalized Laplacian
(`degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt`). Noncomputable
because `ℝ` inversion is. -/
noncomputable def walkLaplacian (A : WAdj (V := V)) : Matrix V V ℝ :=
  1 - walkTransitionMatrix A

/-- The similarity identity: `√D · L_walk · (1/√D) = L_sym`. The walk
Laplacian is similar (conjugated by `√D`) to the symmetric normalized
Laplacian, so every spectral statement about one transfers to the other
in the usual linear-algebra sense.

The eigenvalue content of this identity is now delivered above (2026-08-22,
`proposals/mixing-time-bound.md` Step 1): eigenpairs transfer in both
directions by conjugating the eigenvector with `1/√D`/`√D` — no
characteristic-polynomial-roots interface is needed (`walkEvals` certifies
each transferred entry a genuine eigenvalue of the walk matrix with an
explicit eigenvector witness). The former "named gap" note here
anticipated a charpoly route the delivered `mulVec` algebra dissolves. -/
theorem degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt
    (A : WAdj (V := V)) (hd : ∀ i, 0 < deg A i) :
    degreeSqrt A * walkLaplacian A * degreeInvSqrt A
      = normalizedLaplacian A := by
  have hST : degreeSqrt A * degreeInvSqrt A = 1 :=
    degreeSqrt_mul_degreeInvSqrt A hd
  have hSDinv : degreeSqrt A * Matrix.diagonal (fun i => (deg A i)⁻¹)
      = degreeInvSqrt A := by
    rw [degreeSqrt, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i j
    simp only [Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      simp only [Matrix.diagonal_apply, if_true, degreeInvSqrt]
      have hs : Real.sqrt (deg A i) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr (hd i)
      have hsq : Real.sqrt (deg A i) * Real.sqrt (deg A i) = deg A i :=
        Real.mul_self_sqrt (le_of_lt (hd i))
      rw [show (deg A i)⁻¹
          = (Real.sqrt (deg A i))⁻¹ * (Real.sqrt (deg A i))⁻¹ by
        rw [← mul_inv, hsq]]
      exact mul_inv_cancel_left₀ hs _
    · simp [h, degreeInvSqrt]
  rw [walkLaplacian, walkTransitionMatrix, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, ← Matrix.mul_assoc, hSDinv, hST,
    normalizedLaplacian]

/-!
## Eigenpair transfer through the similarity

`L_walk` is not symmetric in general, so `evals` (defined for `IsSymm`
matrices) does not apply to it. The similarity identity
`degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt` nevertheless transfers
every eigenpair between the two worlds, in both directions, at the same
eigenvalue — no characteristic-polynomial machinery is required. This is
Step 1 of the mixing-time program (`proposals/mixing-time-bound.md`).
-/

/-- Eigenvectors of a symmetric matrix are nonzero: the eigenbasis is
orthonormal, so each basis vector has unit self-inner-product. Support
lemma for the transferred-eigenpair witnesses. -/
theorem eigvecOf_ne_zero (M : Matrix V V ℝ) (hM : M.IsSymm) (i : V) :
    eigvecOf M hM i ≠ 0 := by
  intro h
  have h1 : ∑ k, eigvecOf M hM i k * eigvecOf M hM i k = 1 := by
    simpa using eigvecOf_inner M hM i i
  rw [h] at h1
  simp at h1

/-- **Forward eigenpair transfer**: every eigenpair of the symmetric
normalized Laplacian conjugates to an eigenpair of the (non-symmetric)
walk Laplacian, at the *same* eigenvalue. The walk eigenvector is
`(1/√D) *ᵥ v`. Load-bearing on the similarity identity
`√D · L_walk · (1/√D) = L_sym`: conjugating the eigen-equation by
`1/√D` on both sides cancels the outer factor exactly. -/
theorem walkLaplacian_mulVec_degreeInvSqrt (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) {v : V → ℝ} {μ : ℝ}
    (h : normalizedLaplacian A *ᵥ v = μ • v) :
    walkLaplacian A *ᵥ (degreeInvSqrt A *ᵥ v)
      = μ • (degreeInvSqrt A *ᵥ v) := by
  have hcancel : ∀ x : V → ℝ,
      degreeInvSqrt A *ᵥ (degreeSqrt A *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, degreeInvSqrt_mul_degreeSqrt A hd,
      Matrix.one_mulVec]
  have h' : normalizedLaplacian A *ᵥ v
      = degreeSqrt A *ᵥ (walkLaplacian A *ᵥ (degreeInvSqrt A *ᵥ v)) := by
    rw [← degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt A hd,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [h'] at h
  have h2 := congrArg (Matrix.mulVec (degreeInvSqrt A)) h
  rw [hcancel, Matrix.mulVec_smul_assoc] at h2
  exact h2

/-- **Backward eigenpair transfer**: every eigenpair of the walk
Laplacian conjugates back to an eigenpair of the symmetric normalized
Laplacian, at the same eigenvalue. The normalized eigenvector is
`√D *ᵥ w`. Together with `walkLaplacian_mulVec_degreeInvSqrt` this is
the full two-way spectral bridge between the walk and normalized
worlds. -/
theorem normalizedLaplacian_mulVec_degreeSqrt (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) {w : V → ℝ} {μ : ℝ}
    (h : walkLaplacian A *ᵥ w = μ • w) :
    normalizedLaplacian A *ᵥ (degreeSqrt A *ᵥ w)
      = μ • (degreeSqrt A *ᵥ w) := by
  have hcancel : ∀ x : V → ℝ,
      degreeInvSqrt A *ᵥ (degreeSqrt A *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, degreeInvSqrt_mul_degreeSqrt A hd,
      Matrix.one_mulVec]
  calc normalizedLaplacian A *ᵥ (degreeSqrt A *ᵥ w)
      = degreeSqrt A *ᵥ (walkLaplacian A *ᵥ
          (degreeInvSqrt A *ᵥ (degreeSqrt A *ᵥ w))) := by
        rw [← degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt A hd,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = degreeSqrt A *ᵥ (walkLaplacian A *ᵥ w) := by rw [hcancel]
    _ = degreeSqrt A *ᵥ (μ • w) := by rw [h]
    _ = μ • (degreeSqrt A *ᵥ w) := Matrix.mulVec_smul_assoc _ _ _

/-- The transition-matrix form of the forward transfer: a `μ`-eigenpair
of `L_sym` gives a `(1 - μ)`-eigenpair of the walk transition matrix
`P = D⁻¹A` (since `L_walk = 1 - P`). This is the shape the mixing-time
program consumes: the walk's nontrivial eigenvalues are `1 - λ` for the
normalized spectrum `λ`. -/
theorem walkTransitionMatrix_mulVec_degreeInvSqrt (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) {v : V → ℝ} {μ : ℝ}
    (h : normalizedLaplacian A *ᵥ v = μ • v) :
    walkTransitionMatrix A *ᵥ (degreeInvSqrt A *ᵥ v)
      = (1 - μ) • (degreeInvSqrt A *ᵥ v) := by
  have hw := walkLaplacian_mulVec_degreeInvSqrt A hd h
  rw [walkLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec] at hw
  have hP : walkTransitionMatrix A *ᵥ (degreeInvSqrt A *ᵥ v)
      = (degreeInvSqrt A *ᵥ v) - μ • (degreeInvSqrt A *ᵥ v) := by
    rw [← hw, sub_sub_cancel]
  rw [hP, sub_smul, one_smul]

/-- The forward transfer instantiated at the spectral-theorem
eigenbasis: the `i`-th eigenvector of `L_sym`, conjugated by `1/√D`, is
an eigenvector of the non-symmetric walk Laplacian at the same
eigenvalue. -/
theorem walkLaplacian_mulVec_eigvecOf (A : WAdj (V := V))
    (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i) (i : V) :
    walkLaplacian A *ᵥ (degreeInvSqrt A *ᵥ
        eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA) i)
      = eigvalOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA) i
        • (degreeInvSqrt A *ᵥ
        eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA) i) :=
  walkLaplacian_mulVec_degreeInvSqrt A hd
    ((isHermitian_of_isSymm (normalizedLaplacian_symmetric A hA)).mulVec_eigenvectorBasis i)

/-- The transition-matrix form at the eigenbasis: the `i`-th
normalized-Laplacian eigenvector, conjugated by `1/√D`, is an
eigenvector of the walk transition matrix at eigenvalue
`1 - eigvalOf`. -/
theorem walkTransitionMatrix_mulVec_eigvecOf (A : WAdj (V := V))
    (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i) (i : V) :
    walkTransitionMatrix A *ᵥ (degreeInvSqrt A *ᵥ
        eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA) i)
      = (1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i)
        • (degreeInvSqrt A *ᵥ
        eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA) i) :=
  walkTransitionMatrix_mulVec_degreeInvSqrt A hd
    ((isHermitian_of_isSymm (normalizedLaplacian_symmetric A hA)).mulVec_eigenvectorBasis i)

/-- Conjugation by the invertible `1/√D` preserves nonvanishing. The
transferred eigenvector witnesses are genuine (nonzero) eigenvectors. -/
theorem degreeInvSqrt_mulVec_ne_zero (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) {v : V → ℝ} (hv : v ≠ 0) :
    degreeInvSqrt A *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have hc : degreeSqrt A *ᵥ (degreeInvSqrt A *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, degreeSqrt_mul_degreeInvSqrt A hd,
      Matrix.one_mulVec]
  rw [← hc, h, Matrix.mulVec_zero]

/-- **Completeness of the transferred family**: every vector is
reconstructed from the transferred walk eigenvectors
`(1/√D) *ᵥ vᵢ`, with coefficients `vᵢ ⬝ᵥ (√D *ᵥ w)`. This is the
diagonalizability interface of the walk transition matrix through the
normalized eigenbasis — the mixing-decay step expands the walk's action
on these components. Load-bearing on both the similarity invertibility
(`√D (1/√D) = 1`) and `eigvecOf_expansion_apply`. -/
theorem walk_eigvec_expansion (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) (w : V → ℝ) :
    ∑ i, Matrix.dotProduct
        (eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA) i)
        (degreeSqrt A *ᵥ w)
      • (degreeInvSqrt A *ᵥ
          eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA) i)
      = w := by
  have hcancel' : ∀ x : V → ℝ,
      degreeInvSqrt A *ᵥ (degreeSqrt A *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, degreeInvSqrt_mul_degreeSqrt A hd,
      Matrix.one_mulVec]
  have hexp : ∀ x : V → ℝ,
      ∑ i, Matrix.dotProduct
          (eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA) i) x
        • eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA) i
      = x := by
    intro x
    funext a
    simpa using eigvecOf_expansion_apply
      (normalizedLaplacian_symmetric A hA) x a
  have hlinear : ∀ (c : V → ℝ) (y : V → (V → ℝ)),
      (∑ i, c i • (degreeInvSqrt A *ᵥ y i))
        = degreeInvSqrt A *ᵥ (∑ i, c i • y i) := by
    intro c y
    funext a
    simp only [Matrix.mulVec, Matrix.dotProduct, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    calc ∑ i, c i * ∑ j, degreeInvSqrt A a j * y i j
        = ∑ i, ∑ j, c i * (degreeInvSqrt A a j * y i j) := by
          exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
      _ = ∑ j, ∑ i, c i * (degreeInvSqrt A a j * y i j) := Finset.sum_comm
      _ = ∑ j, degreeInvSqrt A a j * ∑ i, c i * y i j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  rw [hlinear]
  rw [show (∑ i, Matrix.dotProduct
        (eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA) i)
        (degreeSqrt A *ᵥ w)
      • eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA) i)
      = degreeSqrt A *ᵥ w from hexp (degreeSqrt A *ᵥ w)]
  exact hcancel' w

/-- The spectrum of the walk transition matrix, transferred through the
similarity: `walkEvals A hA i = 1 - evals (L_sym) i`, the sorted
normalized spectrum reflected about `1/2`. Real definition (same
provenance as `evals`); `exists_eigenvector_walkTransitionMatrix_eq_walkEvals`
certifies each entry is a genuine eigenvalue of `walkTransitionMatrix A`
with an explicit transferred eigenvector as witness. -/
noncomputable def walkEvals (A : WAdj (V := V)) (hA : A.IsSymm)
    (i : Fin (Fintype.card V)) : ℝ :=
  1 - evals (normalizedLaplacian_symmetric A hA) i

/-- Every entry of the transferred walk spectrum is a genuine eigenvalue
of the walk transition matrix: the witness is the conjugated eigenbasis
vector. This closes `Normalized.lean`'s named residual gap — the
non-symmetric walk matrix has no `evals` of its own, but its eigenvalues
are now available, with witnesses, through `walkEvals`. -/
theorem exists_eigenvector_walkTransitionMatrix_eq_walkEvals
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    (k : Fin (Fintype.card V)) :
    ∃ w : V → ℝ, w ≠ 0 ∧
      walkTransitionMatrix A *ᵥ w = walkEvals A hA k • w := by
  obtain ⟨i, hi⟩ :=
    evals_mem_eigvalOf (normalizedLaplacian_symmetric A hA) k
  refine ⟨degreeInvSqrt A *ᵥ
    eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA) i,
    degreeInvSqrt_mulVec_ne_zero A hd
      (eigvecOf_ne_zero _ _ i), ?_⟩
  rw [walkTransitionMatrix_mulVec_eigvecOf A hA hd i]
  simp only [walkEvals, ← hi]

/-!
## The conjugated-power transfer

The matrix-power layer of the mixing program's Step 3: powers of the
non-symmetric walk matrix move across the similarity, where the
orthonormal eigenbasis of `L_sym` governs them. The commutation form
`√D * P = (1 − L_sym) * √D` is the one-line algebraic content; the
power transfer is its induction.
-/

/-- The commutation form of the similarity: `√D * P = (1 − L_sym) * √D`.
The symmetrized walk operator `1 − L_sym` absorbs the degree square root
on the right — equivalently, `(1 − L_sym) = √D P (1/√D)` — so the walk's
action conjugated by `√D` is the action of a *symmetric* operator. This
is the identity the conjugated-power transfer below runs on. -/
theorem degreeSqrt_mul_walkTransitionMatrix_eq (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) :
    degreeSqrt A * walkTransitionMatrix A
      = (1 - normalizedLaplacian A) * degreeSqrt A := by
  have h1 : (1 - normalizedLaplacian A) * degreeSqrt A
      = degreeSqrt A - degreeSqrt A * walkLaplacian A := by
    rw [Matrix.sub_mul, Matrix.one_mul,
      ← degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt A hd,
      Matrix.mul_assoc, degreeInvSqrt_mul_degreeSqrt A hd, Matrix.mul_one]
  rw [h1, walkLaplacian, Matrix.mul_sub, Matrix.mul_one, sub_sub_cancel]

/-- **The conjugated-power transfer**: `√D *ᵥ (Pᵗ *ᵥ g)` is the `t`-th
power of the *symmetrized* walk operator `1 − L_sym` acting on
`√D *ᵥ g`. The non-symmetric power never has to be diagonalized: it is
moved across the similarity (one `√D` factor per step, the interior
`√D (1/√D)` collapsing to `1`), where the orthonormal eigenbasis of
`L_sym` — the basis the Step-1 transfer certifies — governs it. This is
the matrix-power layer of `proposals/mixing-time-bound.md` Step 3,
load-bearing on the similarity identity
`degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt`. -/
theorem degreeSqrt_mulVec_pow_walkTransitionMatrix (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) (t : ℕ) (g : V → ℝ) :
    degreeSqrt A *ᵥ ((walkTransitionMatrix A ^ t) *ᵥ g)
      = ((1 - normalizedLaplacian A) ^ t) *ᵥ (degreeSqrt A *ᵥ g) := by
  induction t with
  | zero => simp
  | succ t ih =>
    calc degreeSqrt A *ᵥ ((walkTransitionMatrix A ^ (t + 1)) *ᵥ g)
        = degreeSqrt A *ᵥ (walkTransitionMatrix A *ᵥ
            ((walkTransitionMatrix A ^ t) *ᵥ g)) := by
              rw [pow_succ', Matrix.mulVec_mulVec g
                (walkTransitionMatrix A) (walkTransitionMatrix A ^ t)]
      _ = (degreeSqrt A * walkTransitionMatrix A) *ᵥ
            ((walkTransitionMatrix A ^ t) *ᵥ g) :=
              Matrix.mulVec_mulVec _ _ _
      _ = ((1 - normalizedLaplacian A) * degreeSqrt A) *ᵥ
            ((walkTransitionMatrix A ^ t) *ᵥ g) := by
              rw [degreeSqrt_mul_walkTransitionMatrix_eq A hd]
      _ = (1 - normalizedLaplacian A) *ᵥ
            (degreeSqrt A *ᵥ ((walkTransitionMatrix A ^ t) *ᵥ g)) :=
              (Matrix.mulVec_mulVec _ _ _).symm
      _ = (1 - normalizedLaplacian A) *ᵥ
            (((1 - normalizedLaplacian A) ^ t) *ᵥ
              (degreeSqrt A *ᵥ g)) := by rw [ih]
      _ = ((1 - normalizedLaplacian A) ^ (t + 1)) *ᵥ
            (degreeSqrt A *ᵥ g) := by
              rw [pow_succ', ← Matrix.mulVec_mulVec (degreeSqrt A *ᵥ g)
                (1 - normalizedLaplacian A)
                ((1 - normalizedLaplacian A) ^ t)]

end SpectralGraphTheory
