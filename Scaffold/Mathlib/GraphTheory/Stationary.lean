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
import Scaffold.Mathlib.GraphTheory.RandomWalk
import Scaffold.Mathlib.GraphTheory.Normalized

/-!
# Stationary structure of the walk and normalized Laplacians

The downstream consumer of the `GraphTheory.RandomWalk` and
`GraphTheory.Normalized` interfaces: the stationary/kernel structure
that every mixing or diffusion argument starts from, proved from those
modules' row-sum and diagonal-bridge theorems (all hard crust, no
axioms).

- `normalizedLaplacian_mulVec_sqrtDeg_eq_zero`: the kernel of the
  general (irregular) symmetric normalized Laplacian is the
  degree-square-root vector `√deg` — the change of variables through
  `degreeSqrt` that connects to the combinatorial kernel `1`.
- `walkTransitionMatrix_transpose_mulVec_deg`: the degree vector is
  stationary for the adjoint walk, i.e. the probability measure
  `π i = deg A i / vol A univ` is the stationary distribution of the
  simple random walk on a general graph with positive degrees — the
  interface a Markov-mixing consumer needs.
- `walk_detailed_balance` / `walk_detailed_balance_measure` /
  `diagonal_deg_mul_walkTransitionMatrix_isSymm` (delivered 2026-08-22,
  `proposals/reversibility-and-heat-semigroup.md` Phase A): the walk is
  *reversible* with respect to its stationary measure —
  `π i * P i j = π j * P j i`, equivalently the degree-weighted
  transition matrix `D * P` is symmetric. This is the property that
  makes spectral methods apply to the walk, and the interface the
  ℓ²-mixing proxy of `proposals/mixing-time-bound.md` Steps 2–3
  consumes; `transitionMatrix_detailed_balance_uniform` is the
  `d`-regular uniform-measure counterpart, composed from
  `RandomWalk.transitionMatrix_symmetric`.
- `randomWalkLaplacian_mulVec_one_eq_zero` (regular) and
  `walkLaplacian_mulVec_one_eq_zero` (general): the walk Laplacian
  kills the constant vector — conservation of mass, equivalently total
  probability is preserved by each step of the walk. These consume
  `RandomWalk.transitionMatrix_row_sum` and
  `Normalized.walkTransitionMatrix_row_sum` respectively.
-/

namespace SpectralGraphTheory

open Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Row sums: `A *ᵥ 1 = deg A` (the defining property of the degree
function, in vector form). -/
theorem mulVec_one_eq_deg (A : WAdj (V := V)) :
    A *ᵥ (fun _ => (1 : ℝ)) = deg A := by
  funext i
  simp [Matrix.mulVec, Matrix.dotProduct, deg]

/-- The kernel vector of the general (irregular) symmetric normalized
Laplacian is `√deg`: `L_sym *ᵥ √d = 0`.

Proof: with `T = 1/√D`, `(T A T) *ᵥ √d = T *ᵥ (A *ᵥ (T *ᵥ √d))`, and
`T *ᵥ √d = 1` (inverses cancel), `A *ᵥ 1 = deg` (row sums), and
`T *ᵥ deg = √deg` (since `√d · √d = d`). So the whole second term of
`L_sym = 1 - T A T` is `√d` itself and cancels the identity part.

This is the normalized counterpart of the proved
`laplacian_ones_in_kernel` for the combinatorial Laplacian: the two
kernel vectors correspond under the `degreeSqrt` change of variables. -/
theorem normalizedLaplacian_mulVec_sqrtDeg_eq_zero (A : WAdj (V := V))
    (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i) :
    normalizedLaplacian A *ᵥ (fun i => Real.sqrt (deg A i)) = 0 := by
  have hT1 : degreeInvSqrt A *ᵥ (fun i => Real.sqrt (deg A i))
      = fun _ => (1 : ℝ) := by
    funext i
    have hsingle : ∀ x : V, (if i = x then (Real.sqrt (deg A i))⁻¹ else 0)
          * Real.sqrt (deg A x)
        = if i = x then (Real.sqrt (deg A i))⁻¹ * Real.sqrt (deg A x)
          else 0 := fun x => by split <;> simp
    simp only [degreeInvSqrt, Matrix.mulVec, Matrix.dotProduct,
      Matrix.diagonal_apply]
    rw [Finset.sum_congr rfl (fun x _ => hsingle x), Finset.sum_ite_eq,
      if_pos (Finset.mem_univ i), inv_mul_cancel₀
        (Real.sqrt_ne_zero'.mpr (hd i))]
  have hT2 : degreeInvSqrt A *ᵥ (fun i => deg A i)
      = fun i => Real.sqrt (deg A i) := by
    funext i
    have hsingle : ∀ x : V, (if i = x then (Real.sqrt (deg A i))⁻¹ else 0)
          * deg A x
        = if i = x then (Real.sqrt (deg A i))⁻¹ * deg A x else 0 :=
      fun x => by split <;> simp
    simp only [degreeInvSqrt, Matrix.mulVec, Matrix.dotProduct,
      Matrix.diagonal_apply]
    rw [Finset.sum_congr rfl (fun x _ => hsingle x), Finset.sum_ite_eq,
      if_pos (Finset.mem_univ i), inv_mul_eq_div,
      div_eq_iff (Real.sqrt_ne_zero'.mpr (hd i)),
      Real.mul_self_sqrt (le_of_lt (hd i))]
  have hkey : (degreeInvSqrt A * A * degreeInvSqrt A)
      *ᵥ (fun i => Real.sqrt (deg A i))
      = fun i => Real.sqrt (deg A i) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hT1,
      mulVec_one_eq_deg, hT2]
  rw [normalizedLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec, hkey,
    sub_self]

/-- The degree vector is stationary for the adjoint walk:
`Pᵀ *ᵥ deg = deg`. Since `walkTransitionMatrix` is row-stochastic, this
says the probability measure `π i = deg A i / ∑ j deg A j` is the
stationary distribution of the simple random walk on a general
(irregular) graph with positive degrees — the interface a
Markov-mixing consumer starts from.

Proof: by symmetry `Pᵀ = A D⁻¹`, and `(A D⁻¹) *ᵥ deg
= A *ᵥ (D⁻¹ *ᵥ deg) = A *ᵥ 1 = deg`. -/
theorem walkTransitionMatrix_transpose_mulVec_deg (A : WAdj (V := V))
    (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i) :
    (walkTransitionMatrix A)ᵀ *ᵥ (deg A) = deg A := by
  have hT : (walkTransitionMatrix A)ᵀ
      = A * Matrix.diagonal (fun i => (deg A i)⁻¹) := by
    rw [walkTransitionMatrix, Matrix.transpose_mul,
      Matrix.diagonal_transpose, hA.eq]
  have hdinv : Matrix.diagonal (fun i => (deg A i)⁻¹) *ᵥ (deg A)
      = fun _ => (1 : ℝ) := by
    funext i
    have hsingle : ∀ x : V, (if i = x then (deg A i)⁻¹ else 0) * deg A x
        = if i = x then (deg A i)⁻¹ * deg A x else 0 :=
      fun x => by split <;> simp
    simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.diagonal_apply]
    rw [Finset.sum_congr rfl (fun x _ => hsingle x), Finset.sum_ite_eq,
      if_pos (Finset.mem_univ i), inv_mul_cancel₀ (ne_of_gt (hd i))]
  rw [hT, ← Matrix.mulVec_mulVec, hdinv, mulVec_one_eq_deg]

/-!
## Reversibility: detailed balance
-/

/-- Detailed balance (reversibility) for the simple random walk on a
weighted undirected graph, unnormalized degree-measure form:
`deg A i * P i j = deg A j * P j i` for `P = walkTransitionMatrix A`.

Both sides are exactly `A i j`: the degree weight cancels the `D⁻¹` row
factor of `walkTransitionMatrix` on the left, the same happens on the
right, and `A.IsSymm` identifies the two adjacency entries. This is the
defining property that makes spectral (rather than merely stochastic)
methods apply to the walk at all: `P` is self-adjoint in the
degree-weighted inner product — see the matrix packaging
`diagonal_deg_mul_walkTransitionMatrix_isSymm`.

Delivered 2026-08-22, `proposals/reversibility-and-heat-semigroup.md`
Phase A Step 1. -/
theorem walk_detailed_balance (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) (i j : V) :
    deg A i * walkTransitionMatrix A i j
      = deg A j * walkTransitionMatrix A j i := by
  have hL : deg A i * ((deg A i)⁻¹ * A i j) = A i j := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (hd i)), one_mul]
  have hR : deg A j * ((deg A j)⁻¹ * A j i) = A j i := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (hd j)), one_mul]
  rw [walkTransitionMatrix_apply, walkTransitionMatrix_apply, hL, hR]
  exact hA.apply j i

/-- Detailed balance in the stationary-measure form: with
`π i = deg A i / vol A univ` — the stationary distribution certified by
`walkTransitionMatrix_transpose_mulVec_deg` — the walk satisfies
`π i * P i j = π j * P j i`. The normalized counterpart of
`walk_detailed_balance`, obtained by dividing the degree-measure
identity through by the total volume; the identity itself carries no
volume hypothesis (for positive degrees on a nonempty vertex type the
volume is positive and `π` is a probability measure). This is the shape
every introductory Markov-chains text states as reversibility with
respect to the stationary measure. -/
theorem walk_detailed_balance_measure (A : WAdj (V := V))
    (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i) (i j : V) :
    deg A i / vol A (Finset.univ : Finset V) * walkTransitionMatrix A i j
      = deg A j / vol A (Finset.univ : Finset V)
          * walkTransitionMatrix A j i := by
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
    walk_detailed_balance A hA hd i j]

/-- The matrix form of detailed balance: weighting the walk transition
matrix by the diagonal degree matrix on the left symmetrizes it,
`(D * P).IsSymm`. Reversibility *is* symmetrizability — this is the
self-adjointness packaging spectral arguments consume, and it is the
adjoint form of the similarity identity
`degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt` at the transition
matrix rather than the Laplacian. -/
theorem diagonal_deg_mul_walkTransitionMatrix_isSymm (A : WAdj (V := V))
    (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i) :
    (Matrix.diagonal (deg A) * walkTransitionMatrix A).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [Matrix.diagonal_mul]
  exact (walk_detailed_balance A hA hd i j).symm

/-- Detailed balance, regular (`d`-regular cone) uniform-measure form:
with `π` the uniform distribution `(card V)⁻¹`, the regular transition
matrix `RandomWalk.transitionMatrix A d` satisfies
`π i * P i j = π j * P j i`. The regular-case counterpart of
`walk_detailed_balance_measure`, composed from the already-proved
`transitionMatrix_symmetric` (the transition matrix of a `d`-regular
graph is symmetric, so both balance sides agree) rather than re-proved —
`proposals/reversibility-and-heat-semigroup.md` Phase A Step 2. -/
theorem transitionMatrix_detailed_balance_uniform (A : WAdj (V := V))
    (hA : A.IsSymm) (d : ℝ) (i j : V) :
    (Fintype.card V : ℝ)⁻¹ * transitionMatrix A d i j
      = (Fintype.card V : ℝ)⁻¹ * transitionMatrix A d j i := by
  rw [(transitionMatrix_symmetric A hA d).apply i j]

/-!
## Conservation of mass: the walk Laplacian kills constants
-/

/-- Conservation of mass, regular case: the walk Laplacian of a
`d`-regular graph kills the constant vector,
`L_rw *ᵥ 1 = 0` — each step of the walk preserves total probability.
Consumes `RandomWalk.transitionMatrix_row_sum`. -/
theorem randomWalkLaplacian_mulVec_one_eq_zero (A : WAdj (V := V))
    (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d) :
    randomWalkLaplacian A d *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  have hP : transitionMatrix A d *ᵥ (fun _ => (1 : ℝ))
      = fun _ => (1 : ℝ) := by
    funext i
    simp only [Matrix.mulVec, Matrix.dotProduct, mul_one]
    rw [transitionMatrix_row_sum A d hd hdpos i]
  rw [randomWalkLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec, hP,
    sub_self]

/-- Conservation of mass, general (irregular) case: the walk Laplacian
of any graph with positive degrees kills the constant vector. Consumes
`Normalized.walkTransitionMatrix_row_sum`. -/
theorem walkLaplacian_mulVec_one_eq_zero (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) :
    walkLaplacian A *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  have hP : walkTransitionMatrix A *ᵥ (fun _ => (1 : ℝ))
      = fun _ => (1 : ℝ) := by
    funext i
    simp only [Matrix.mulVec, Matrix.dotProduct, mul_one]
    rw [walkTransitionMatrix_row_sum A hd i]
  rw [walkLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec, hP, sub_self]

end SpectralGraphTheory
