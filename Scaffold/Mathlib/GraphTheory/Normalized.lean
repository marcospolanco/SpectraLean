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
- `normalizedLaplacian` — `L_sym = 1 - (1/√D) A (1/√D)`;
- `normalizedLaplacian_symmetric` — symmetry for symmetric `A`;
- `degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt` — the congruence
  `√D L_sym √D = D - A = laplacian A`: the square roots cancel, so this
  is the exact square-root-free-shaped relation between the normalized
  and combinatorial worlds (all quadratic-form statements transfer);
- `normalizedLaplacian_eq_regularNormalizedLaplacian` — agreement with
  the regular cone: on `d`-regular graphs the general definition
  specializes to `regularNormalizedLaplacian A d`.

Deferred to the next slice (see `docs/6_SGT_BACKLOG.md`): spectral
similarity transfer to the walk form `I - D⁻¹A` (same spectrum as
`L_sym`), which needs an invariance-of-`evals`-under-similarity
interface.
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

Named gap (deferred): turning this identity into an equality of
eigenvalue *lists* requires a characteristic-polynomial-roots interface
for the non-symmetric walk matrix, which the pinned Mathlib snapshot
does not provide; Scaffold's `evals` is defined only for `IsSymm`
matrices and therefore does not apply to `L_walk` directly. -/
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

end SpectralGraphTheory
