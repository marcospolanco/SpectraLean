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
import Scaffold.Mathlib.GraphTheory.Foster
import Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent
import Scaffold.Mathlib.Probability.BernoulliProduct
/-!
# The deterministic Spielman–Srivastava algebra (sparsification Step 1,
Slice 2)

The deterministic core of leverage-score sparsification
(`proposals/spectral-sparsification-via-leverage-scores.md`, the Active
priority table's top High row): the rank-one sampling matrices, their
pointwise norm bound, and the variance statistic — every piece the
`matrix_bernstein` assembly (Slice 3) consumes, at the classical
Spielman–Srivastava constants `R = 1/q` and `‖Σ‖ ≤ 1/q`, here *proved*
rather than asserted (retiring the Step-0 survey's named residual risk).

Design decisions (recorded in the proposal's Step-0 delivery):

- **Eigen-coordinate edge vectors.** `ssEdgeVec A hA u v` is the
  voltage-difference vector of `Foster.lean`'s spectral machinery —
  `√(w/2) · (v_k u − v_k v)/√λ_k` per eigenbasis index, zero-eigenvalue
  entries dropped. No matrix pseudoinverse or square root is ever formed.
- **Ordered-pair halving.** The `1/√2` normalization makes
  `∑_{(u,v)} v_e v_eᵀ` *exactly* the image projector (not twice it) and
  makes the sampling space the delivered Slice-1 `bernPMF` at
  `ι = V × V` verbatim — zero new probability infrastructure.
- **The Finding-A guard.** Saturated pairs (`p_e = 1`) contribute the
  zero matrix — without the guard the uniform pointwise bound fails at
  the missed outcome `δ_e = 0` (refuted in QA). Zero-leverage pairs
  (loops, non-edges) are absorbed by their zero rank-one factor, so
  centering holds with no connectivity hypothesis.

Everything here is proved; this module adds no axioms. QA:
`Scaffold/QA/SpectralGraph/Sparsification_QA.lean`.
-/

open MeasureTheory
open Scaffold.Mathlib.Probability.BernoulliProduct
open scoped BigOperators Matrix Matrix.L2OpNorm

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Rank-one algebra -/

/-- The rank-one outer product `v vᵀ` of a real vector with itself (the
pinned Mathlib has no `outerProduct` at plain-function generality; the
same-vector form is the only one the Spielman–Srivastava design needs). -/
def rankOne (v : V → ℝ) : Matrix V V ℝ :=
  Matrix.of fun i j => v i * v j

omit [Fintype V] [DecidableEq V] in
theorem rankOne_apply (v : V → ℝ) (i j : V) : rankOne v i j = v i * v j := rfl

omit [Fintype V] [DecidableEq V] in
theorem rankOne_isSymm (v : V → ℝ) : (rankOne v).IsSymm :=
  Matrix.IsSymm.ext fun i j => by simp [rankOne, mul_comm]

omit [Fintype V] [DecidableEq V] in
theorem rankOne_neg (v : V → ℝ) : rankOne (-v) = rankOne v := by
  ext i j; simp [rankOne, neg_mul_neg]

omit [DecidableEq V] in
theorem dotProduct_self_nonneg (v : V → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

omit [DecidableEq V] in
theorem dotProduct_self_pos_of_ne_zero {v : V → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  by_contra hle
  push_neg at hle
  have heq : v ⬝ᵥ v = 0 := le_antisymm hle (dotProduct_self_nonneg v)
  apply hv
  funext k
  have hmem : k ∈ (Finset.univ : Finset V) := Finset.mem_univ k
  have hk := Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (v j)) |>.mp heq k hmem
  simpa using mul_self_eq_zero.1 hk

omit [DecidableEq V] in
theorem rankOne_mulVec (v y : V → ℝ) :
    rankOne v *ᵥ y = (v ⬝ᵥ y) • v := by
  funext i
  have h : ∀ j : V, (v i * v j) * y j = v i * (v j * y j) := fun j => by ring
  have hmul := Finset.mul_sum (Finset.univ : Finset V)
    (fun j => v j * y j) (v i)
  simp only [Matrix.mulVec, rankOne_apply, h, Matrix.dotProduct,
    Pi.smul_apply, smul_eq_mul]
  rw [← hmul]
  ring

omit [DecidableEq V] in
theorem rankOne_quadForm (v x : V → ℝ) :
    quadForm (rankOne v) x = (x ⬝ᵥ v) ^ 2 := by
  rw [quadForm, rankOne_mulVec, Matrix.dotProduct_smul, smul_eq_mul,
    Matrix.dotProduct_comm v x]
  ring

omit [DecidableEq V] in
theorem rankOne_mul_self (v : V → ℝ) :
    rankOne v * rankOne v = (v ⬝ᵥ v) • rankOne v := by
  ext i k
  have h : ∀ j : V, (v i * v j) * (v j * v k) = (v i * v k) * (v j * v j) :=
    fun j => by ring
  have hmul := Finset.mul_sum (Finset.univ : Finset V)
    (fun j => v j * v j) (v i * v k)
  simp only [Matrix.mul_apply, rankOne_apply, h, Matrix.smul_apply,
    smul_eq_mul, rankOne_apply, Matrix.dotProduct]
  rw [← hmul]
  ring

omit [DecidableEq V] in
/-- Squared Cauchy–Schwarz in plain dot-product form (the only
Cauchy–Schwarz input the slice needs; proved through the Euclidean inner
product). -/
theorem dotProduct_sq_le (x y : V → ℝ) :
    (x ⬝ᵥ y) * (x ⬝ᵥ y) ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  have hin : (inner ((WithLp.equiv 2 (V → ℝ)).symm x :
      EuclideanSpace ℝ V) ((WithLp.equiv 2 (V → ℝ)).symm y)) = x ⬝ᵥ y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]; simp
  have hcs := abs_real_inner_le_norm
    (x := (WithLp.equiv 2 (V → ℝ)).symm x) (y := (WithLp.equiv 2 (V → ℝ)).symm y)
  rw [hin] at hcs
  have hinx : (inner ((WithLp.equiv 2 (V → ℝ)).symm x : EuclideanSpace ℝ V)
      ((WithLp.equiv 2 (V → ℝ)).symm x)) = x ⬝ᵥ x := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]; simp
  have hiny : (inner ((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)
      ((WithLp.equiv 2 (V → ℝ)).symm y)) = y ⬝ᵥ y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]; simp
  have hnx : ‖(WithLp.equiv 2 (V → ℝ)).symm x‖ ^ 2 = x ⬝ᵥ x := by
    rw [← real_inner_self_eq_norm_sq, hinx]
  have hny : ‖(WithLp.equiv 2 (V → ℝ)).symm y‖ ^ 2 = y ⬝ᵥ y := by
    rw [← real_inner_self_eq_norm_sq, hiny]
  obtain ⟨ha, hb⟩ := abs_le.mp hcs
  have key : (x ⬝ᵥ y) * (x ⬝ᵥ y)
      ≤ ((‖(WithLp.equiv 2 (V → ℝ)).symm x‖ * ‖(WithLp.equiv 2 (V → ℝ)).symm y‖)
        * (‖(WithLp.equiv 2 (V → ℝ)).symm x‖ * ‖(WithLp.equiv 2 (V → ℝ)).symm y‖)) := by
    have hb : (0 : ℝ) ≤ ‖(WithLp.equiv 2 (V → ℝ)).symm x‖
        * ‖(WithLp.equiv 2 (V → ℝ)).symm y‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [ha, hb]
  have hsplit : ((‖(WithLp.equiv 2 (V → ℝ)).symm x‖ * ‖(WithLp.equiv 2 (V → ℝ)).symm y‖)
        * (‖(WithLp.equiv 2 (V → ℝ)).symm x‖ * ‖(WithLp.equiv 2 (V → ℝ)).symm y‖))
      = (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
    nlinarith [hnx, hny]
  exact key.trans (le_of_eq hsplit)

/-- **The rank-one operator-norm bound**: `‖v vᵀ‖ ≤ v ⬝ᵥ v`. Every
eigenvalue of the rank-one matrix is its Rayleigh quotient at a unit
eigenvector, which is a squared coordinate dot product, bounded by
Cauchy–Schwarz. -/
theorem l2OpNorm_rankOne_le (v : V → ℝ) : ‖rankOne v‖ ≤ v ⬝ᵥ v := by
  refine Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.l2OpNorm_le_of_abs_eigvalOf_le
    (rankOne_isSymm v) (dotProduct_self_nonneg v) fun i => ?_
  rw [abs_le, ← quadForm_eigvecOf_self (rankOne_isSymm v) i,
    rankOne_quadForm]
  have hunit : (eigvecOf (rankOne v) (rankOne_isSymm v) i)
      ⬝ᵥ (eigvecOf (rankOne v) (rankOne_isSymm v) i) = 1 := by
    simpa [Matrix.dotProduct] using
      eigvecOf_inner (rankOne v) (rankOne_isSymm v) i i
  have hcs := dotProduct_sq_le (eigvecOf (rankOne v) (rankOne_isSymm v) i) v
  rw [hunit, one_mul] at hcs
  have hsq : 0 ≤ (eigvecOf (rankOne v) (rankOne_isSymm v) i ⬝ᵥ v)
      * (eigvecOf (rankOne v) (rankOne_isSymm v) i ⬝ᵥ v) :=
    mul_self_nonneg _
  constructor
  · rw [pow_two]; linarith
  · rw [pow_two]; linarith

/-! ## The bilinear Dirichlet identity -/

/-- Polarized Dirichlet form: for symmetric `A`, the mixed double sum is
twice the bilinear form `x ⬝ᵥ (L *ᵥ y)`. Polarization of
`laplacian_quadForm` at `x + y`, with the cross term identified by
symmetry of `L`. -/
theorem laplacian_dirichlet_bilinear (A : WAdj (V := V)) (hA : A.IsSymm)
    (x y : V → ℝ) :
    ∑ i, ∑ j, A i j * ((x i - x j) * (y i - y j))
      = 2 * (x ⬝ᵥ (laplacian A *ᵥ y)) := by
  have hL : (laplacian A).IsSymm := laplacian_symmetric A hA
  have hLt : (laplacian A)ᵀ = laplacian A := hL
  have hij : ∀ i j : V, laplacian A i j = laplacian A j i := by
    intro i j
    have h0 : (laplacian A)ᵀ i j = laplacian A i j :=
      congrFun (congrFun hLt i) j
    rw [Matrix.transpose_apply] at h0
    exact h0.symm
  have hexp : ∀ u w : V → ℝ, u ⬝ᵥ (laplacian A *ᵥ w)
      = ∑ i, ∑ j, u i * laplacian A i j * w j := by
    intro u w
    simp only [Matrix.dotProduct, Matrix.mulVec, Matrix.dotProduct]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  have hcross : y ⬝ᵥ (laplacian A *ᵥ x) = x ⬝ᵥ (laplacian A *ᵥ y) := by
    rw [hexp y x, hexp x y, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [hij]; ring
  have hqf : quadForm (laplacian A) (x + y)
      = quadForm (laplacian A) x + quadForm (laplacian A) y
        + (x ⬝ᵥ (laplacian A *ᵥ y) + y ⬝ᵥ (laplacian A *ᵥ x)) := by
    simp only [quadForm, Matrix.mulVec_add, Matrix.add_dotProduct,
      Matrix.dotProduct_add]
    ring
  have hD : ∑ i, ∑ j, A i j * ((x i + y i - (x j + y j)) ^ 2)
      = ∑ i, ∑ j, A i j * (x i - x j) ^ 2
        + ∑ i, ∑ j, A i j * (y i - y j) ^ 2
        + 2 * ∑ i, ∑ j, A i j * ((x i - x j) * (y i - y j)) := by
    have h : ∀ i j : V, A i j * ((x i + y i - (x j + y j)) ^ 2)
        = A i j * (x i - x j) ^ 2 + A i j * (y i - y j) ^ 2
          + 2 * (A i j * ((x i - x j) * (y i - y j))) := by
      intro i j
      have h2 : (x i + y i - (x j + y j)) ^ 2
          = (x i - x j) ^ 2 + (y i - y j) ^ 2
            + 2 * ((x i - x j) * (y i - y j)) := by ring
      rw [h2]; ring
    have hpull : 2 * ∑ i, ∑ j, A i j * ((x i - x j) * (y i - y j))
        = ∑ i, ∑ j, 2 * (A i j * ((x i - x j) * (y i - y j))) := by
      calc 2 * ∑ i, ∑ j, A i j * ((x i - x j) * (y i - y j))
          = ∑ i, 2 * ∑ j, A i j * ((x i - x j) * (y i - y j)) :=
            Finset.mul_sum (Finset.univ : Finset V)
              (fun i => ∑ j, A i j * ((x i - x j) * (y i - y j))) 2
        _ = ∑ i, ∑ j, 2 * (A i j * ((x i - x j) * (y i - y j))) :=
            Finset.sum_congr rfl fun i _ =>
              Finset.mul_sum (Finset.univ : Finset V)
                (fun j => A i j * ((x i - x j) * (y i - y j))) 2
    simp only [h, Finset.sum_add_distrib, Finset.mul_sum]
  have e1 : ∑ i, ∑ j, A i j * ((x i + y i - (x j + y j)) ^ 2)
      = 2 * quadForm (laplacian A) (x + y) := by
    rw [laplacian_quadForm A hA (x + y)]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have e2 : ∑ i, ∑ j, A i j * (x i - x j) ^ 2
      = 2 * quadForm (laplacian A) x := by
    rw [laplacian_quadForm A hA x]; ring
  have e3 : ∑ i, ∑ j, A i j * (y i - y j) ^ 2
      = 2 * quadForm (laplacian A) y := by
    rw [laplacian_quadForm A hA y]; ring
  rw [e1, e2, e3, hqf] at hD
  linarith

/-! ## The Spielman–Srivastava edge vectors -/

section EdgeVec

variable (A : WAdj (V := V)) (hA : A.IsSymm)

theorem eigvalOf_laplacian_nonneg (hnn : ∀ i j, 0 ≤ A i j) (k : V) :
    0 ≤ eigvalOf (laplacian A) (laplacian_symmetric A hA) k := by
  have h := quadForm_eigvecOf_self (laplacian_symmetric A hA) k
  rw [← h]
  exact laplacian_psd A hA hnn _

/-- **The Spielman–Srivastava edge vector**, in eigen-coordinate form:
for the ordered pair `(u, v)`, the vector whose `k`-th entry is the
voltage difference of the `k`-th Laplacian eigenvector across the pair,
scaled by `√(w/2)` and de-scaled by `√λ_k` (zero-eigenvalue entries
dropped). The `1/√2` is the ordered-pair halving: the unordered edge
`{u, v}` is carried by the two ordered pairs `(u, v)` and `(v, u)` in
equal halves, so that `∑_{(u,v)} v_e ⊗ v_e` is *exactly* the image
projector (not twice it) and each vector's squared norm is the pair's
half-share of the Foster leverage budget. No matrix pseudoinverse or
square root is ever formed; the representation is exactly the one
`Foster.lean`'s spectral machinery produces. -/
noncomputable def ssEdgeVec (u v : V) : V → ℝ :=
  fun k => if eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0 then 0
    else Real.sqrt (A u v / 2)
      * (eigvecOf (laplacian A) (laplacian_symmetric A hA) k u
        - eigvecOf (laplacian A) (laplacian_symmetric A hA) k v)
      / Real.sqrt (eigvalOf (laplacian A) (laplacian_symmetric A hA) k)

theorem ssEdgeVec_self (u : V) : ssEdgeVec A hA u u = 0 := by
  funext k
  by_cases h0 : eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0
  · simp [ssEdgeVec, h0]
  · simp only [ssEdgeVec, if_neg h0, sub_self, mul_zero, zero_div]
    simp

theorem ssEdgeVec_swap (u v : V) :
    ssEdgeVec A hA u v = -(ssEdgeVec A hA v u) := by
  funext k
  by_cases h0 : eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0
  · simp [ssEdgeVec, h0]
  · simp only [ssEdgeVec, if_neg h0, Pi.neg_apply]
    rw [hA.apply u v]
    ring

/-- **The edge vector's squared norm is the pair's leverage share**:
`‖v_e‖² = w_e R_eff(u,v)/2`, the ordered-pair half-share of the Foster
budget term (summed over ordered pairs: `card V - 1`). -/
theorem ssEdgeVec_dotProduct_self (hnn : ∀ i j, 0 ≤ A i j)
    (hconn : (supportGraph A hA).Connected) (u v : V) :
    ssEdgeVec A hA u v ⬝ᵥ ssEdgeVec A hA u v
      = A u v * effectiveResistance A u v / 2 := by
  have hterm : ∀ k : V,
      ssEdgeVec A hA u v k * ssEdgeVec A hA u v k
        = (A u v / 2) * (if eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0
            then (0 : ℝ)
            else (eigvecOf (laplacian A) (laplacian_symmetric A hA) k u
              - eigvecOf (laplacian A) (laplacian_symmetric A hA) k v) ^ 2
              / eigvalOf (laplacian A) (laplacian_symmetric A hA) k) := by
    intro k
    by_cases h0 : eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0
    · simp [ssEdgeVec, h0]
    · have hkpos : 0 < eigvalOf (laplacian A) (laplacian_symmetric A hA) k := by
        rcases eq_or_lt_of_le (eigvalOf_laplacian_nonneg A hA hnn k) with h | h
        · exact absurd h.symm h0
        · exact h
      have hμ : Real.sqrt (eigvalOf (laplacian A) (laplacian_symmetric A hA) k)
          * Real.sqrt (eigvalOf (laplacian A) (laplacian_symmetric A hA) k)
          = eigvalOf (laplacian A) (laplacian_symmetric A hA) k :=
        Real.mul_self_sqrt hkpos.le
      have hsqA : Real.sqrt (A u v / 2) * Real.sqrt (A u v / 2) = A u v / 2 :=
        Real.mul_self_sqrt (div_nonneg (hnn u v) zero_le_two)
      have hnum : (Real.sqrt (A u v / 2) * (eigvecOf (laplacian A) (laplacian_symmetric A hA) k u
              - eigvecOf (laplacian A) (laplacian_symmetric A hA) k v))
            * (Real.sqrt (A u v / 2) * (eigvecOf (laplacian A) (laplacian_symmetric A hA) k u
              - eigvecOf (laplacian A) (laplacian_symmetric A hA) k v))
            = (Real.sqrt (A u v / 2) * Real.sqrt (A u v / 2))
              * (eigvecOf (laplacian A) (laplacian_symmetric A hA) k u
                - eigvecOf (laplacian A) (laplacian_symmetric A hA) k v) ^ 2 := by ring
      show ssEdgeVec A hA u v k * ssEdgeVec A hA u v k = _
      simp only [ssEdgeVec, if_neg h0]
      rw [div_mul_div_comm, hnum, hsqA, hμ]
      ring
  simp only [Matrix.dotProduct]
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  have hmul := Finset.mul_sum (Finset.univ : Finset V)
    (fun k => if eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0 then (0 : ℝ)
      else (eigvecOf (laplacian A) (laplacian_symmetric A hA) k u
        - eigvecOf (laplacian A) (laplacian_symmetric A hA) k v) ^ 2
        / eigvalOf (laplacian A) (laplacian_symmetric A hA) k) (A u v / 2)
  rw [← hmul, effectiveResistance_eq_sum_eigbasis A hA hnn hconn u v]
  ring

/-- **The Foster budget in edge-vector form**: the ordered-pair squared
norms sum to `card V - 1` — the total leverage budget at the ordered-pair
halved normalization. This is Foster's theorem read through the norm
identity; the expected number of unsaturated samples at budget `q` is
`q (card V - 1)`. -/
theorem sum_ssEdgeVec_dotProduct_self (hnn : ∀ i j, 0 ≤ A i j)
    (hconn : (supportGraph A hA).Connected) :
    ∑ u, ∑ v, ssEdgeVec A hA u v ⬝ᵥ ssEdgeVec A hA u v
      = (Fintype.card V : ℝ) - 1 := by
  have h := foster_theorem A hA hnn hconn
  have hsplit : ∑ u, ∑ v, ssEdgeVec A hA u v ⬝ᵥ ssEdgeVec A hA u v
      = (∑ u, ∑ v, A u v * effectiveResistance A u v) / 2 := by
    have e1 : ∀ u : V, ∑ v, A u v * effectiveResistance A u v / 2
        = (∑ v, A u v * effectiveResistance A u v) / 2 :=
      fun u => (Finset.sum_div (Finset.univ : Finset V)
        (fun v => A u v * effectiveResistance A u v) 2).symm
    calc ∑ u, ∑ v, ssEdgeVec A hA u v ⬝ᵥ ssEdgeVec A hA u v
        = ∑ u, ∑ v, A u v * effectiveResistance A u v / 2 :=
          Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
            ssEdgeVec_dotProduct_self A hA hnn hconn u v
      _ = ∑ u, (∑ v, A u v * effectiveResistance A u v) / 2 :=
          Finset.sum_congr rfl fun u _ => e1 u
      _ = (∑ u, ∑ v, A u v * effectiveResistance A u v) / 2 :=
          (Finset.sum_div (Finset.univ : Finset V)
            (fun u => ∑ v, A u v * effectiveResistance A u v) 2).symm
  rw [hsplit, h]

end EdgeVec

/-! ## The image projector -/

section Projector

variable (A : WAdj (V := V)) (hA : A.IsSymm)

/-- **The coordinate form of the orthogonal projector onto `im L`**: the
diagonal matrix keeping exactly the nonzero-eigenvalue eigenbasis
directions (`Π_{im L} = Π_{(ker L)^⊥}` in eigen-coordinates). At a
connected graph this is the projector off the constant direction. -/
noncomputable def imageProjector : Matrix V V ℝ :=
  Matrix.diagonal fun k =>
    if eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0 then (0 : ℝ) else 1

theorem imageProjector_isSymm : (imageProjector A hA).IsSymm :=
  Matrix.IsSymm.ext fun i j => by
    by_cases hij : i = j
    · simp [imageProjector, Matrix.diagonal_apply, hij]
    · simp [imageProjector, Matrix.diagonal_apply, hij, Ne.symm hij]

theorem imageProjector_mul_self :
    imageProjector A hA * imageProjector A hA = imageProjector A hA := by
  ext i j
  simp only [imageProjector, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases h : eigvalOf (laplacian A) (laplacian_symmetric A hA) i = 0 <;> simp [h]
  · simp [hij]

private theorem imageProjector_mulVec_apply (x : V → ℝ) (k : V) :
    (imageProjector A hA *ᵥ x) k
      = (if eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0 then (0 : ℝ) else 1)
        * x k := by
  simp [imageProjector, Matrix.mulVec, Matrix.diagonal, Matrix.dotProduct,
    Finset.sum_ite_eq]

theorem quadForm_imageProjector_nonneg (x : V → ℝ) :
    0 ≤ quadForm (imageProjector A hA) x := by
  show ∑ k, x k * (imageProjector A hA *ᵥ x) k ≥ 0
  rw [Finset.sum_congr rfl fun k _ => by rw [imageProjector_mulVec_apply A hA x k]]
  exact Finset.sum_nonneg fun k _ => by
    by_cases h : eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0
    · rw [if_pos h, zero_mul, mul_zero]
    · rw [if_neg h, one_mul]
      exact mul_self_nonneg _

theorem quadForm_imageProjector_le (x : V → ℝ) :
    quadForm (imageProjector A hA) x ≤ x ⬝ᵥ x := by
  show ∑ k, x k * (imageProjector A hA *ᵥ x) k ≤ ∑ k, x k * x k
  rw [Finset.sum_congr rfl fun k _ => by rw [imageProjector_mulVec_apply A hA x k]]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases h : eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0
  · rw [if_pos h, zero_mul, mul_zero]
    exact mul_self_nonneg _
  · rw [if_neg h, one_mul]

theorem l2OpNorm_imageProjector_le : ‖imageProjector A hA‖ ≤ 1 := by
  have hsymm := imageProjector_isSymm A hA
  refine Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.l2OpNorm_le_of_abs_eigvalOf_le
    hsymm zero_le_one fun i => ?_
  rw [abs_le, ← quadForm_eigvecOf_self hsymm i]
  have hle := quadForm_imageProjector_le A hA (eigvecOf (imageProjector A hA) hsymm i)
  have hnn := quadForm_imageProjector_nonneg A hA (eigvecOf (imageProjector A hA) hsymm i)
  have hunit : (eigvecOf (imageProjector A hA) hsymm i)
      ⬝ᵥ (eigvecOf (imageProjector A hA) hsymm i) = 1 := by
    simpa [Matrix.dotProduct] using
      eigvecOf_inner (imageProjector A hA) hsymm i i
  constructor <;> linarith

theorem trace_imageProjector_eq (hnn : ∀ i j, 0 ≤ A i j)
    (hconn : (supportGraph A hA).Connected) :
    Matrix.trace (imageProjector A hA) = (Fintype.card V : ℝ) - 1 := by
  have h0 : (Finset.univ.filter fun k =>
      eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0).card = 1 :=
    card_filter_eigvalOf_laplacian_eq_zero A hA hnn hconn
  have hite : ∀ k : V,
      (if eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0 then (0 : ℝ) else 1)
      = 1 - (if eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0
          then (1 : ℝ) else 0) := by
    intro k
    by_cases h : eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0 <;> simp [h]
  simp only [imageProjector, Matrix.trace]
  rw [Matrix.diag_diagonal, Finset.sum_congr rfl fun k _ => hite k,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_boole, h0]
  simp

/-- **The projector identity**: the ordered-pair outer products of the
edge vectors sum to *exactly* the image projector — the
Spielman–Srivastava identity `∑_e v_e v_eᵀ = Π_{im L}` (halves absorbed
by the `1/√2` normalization). Entrywise: the bilinear Dirichlet identity
at two eigenvectors is twice an eigenvalue-weighted `δ_kl`, and the
`√λ` scalings cancel on the diagonal. -/
theorem sum_rankOne_ssEdgeVec (hnn : ∀ i j, 0 ≤ A i j) :
    ∑ e : V × V, rankOne (ssEdgeVec A hA e.1 e.2) = imageProjector A hA := by
  ext k l
  simp only [Matrix.sum_apply, rankOne_apply, imageProjector,
    Matrix.diagonal_apply]
  rw [Fintype.sum_prod_type]
  by_cases hk : eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0
  · have hzero : ∀ u v : V,
        ssEdgeVec A hA u v k * ssEdgeVec A hA u v l = 0 := by
      intro u v
      have h1 : ssEdgeVec A hA u v k = 0 := by simp [ssEdgeVec, hk]
      rw [h1, zero_mul]
    simp only [hzero, Finset.sum_const_zero]
    by_cases hkl : k = l
    · subst hkl; simp [hk]
    · simp [hkl]
  · by_cases hl : eigvalOf (laplacian A) (laplacian_symmetric A hA) l = 0
    · have hzero : ∀ u v : V,
          ssEdgeVec A hA u v k * ssEdgeVec A hA u v l = 0 := by
        intro u v
        have h2 : ssEdgeVec A hA u v l = 0 := by simp [ssEdgeVec, hl]
        rw [h2, mul_zero]
      simp only [hzero, Finset.sum_const_zero]
      have hkl : k ≠ l := fun h => by rw [h] at hk; exact hk hl
      simp [hkl]
    · have hkpos : 0 < eigvalOf (laplacian A) (laplacian_symmetric A hA) k := by
        rcases eq_or_lt_of_le (eigvalOf_laplacian_nonneg A hA hnn k) with h | h
        · exact absurd h.symm hk
        · exact h
      have hlpos : 0 < eigvalOf (laplacian A) (laplacian_symmetric A hA) l := by
        rcases eq_or_lt_of_le (eigvalOf_laplacian_nonneg A hA hnn l) with h | h
        · exact absurd h.symm hl
        · exact h
      have hterm : ∀ u v : V,
          ssEdgeVec A hA u v k * ssEdgeVec A hA u v l
            = A u v * ((eigvecOf (laplacian A) (laplacian_symmetric A hA) k u - eigvecOf (laplacian A) (laplacian_symmetric A hA) k v)
                * (eigvecOf (laplacian A) (laplacian_symmetric A hA) l u - eigvecOf (laplacian A) (laplacian_symmetric A hA) l v))
              / (2 * Real.sqrt (eigvalOf (laplacian A) (laplacian_symmetric A hA) k)
                * Real.sqrt (eigvalOf (laplacian A) (laplacian_symmetric A hA) l)) := by
        intro u v
        have hA2 : Real.sqrt (A u v / 2) * Real.sqrt (A u v / 2) = A u v / 2 :=
          Real.mul_self_sqrt (div_nonneg (hnn u v) zero_le_two)
        have hn : (Real.sqrt (A u v / 2) * (eigvecOf (laplacian A) (laplacian_symmetric A hA) k u
                - eigvecOf (laplacian A) (laplacian_symmetric A hA) k v))
              * (Real.sqrt (A u v / 2) * (eigvecOf (laplacian A) (laplacian_symmetric A hA) l u
                - eigvecOf (laplacian A) (laplacian_symmetric A hA) l v))
              = (Real.sqrt (A u v / 2) * Real.sqrt (A u v / 2))
                * ((eigvecOf (laplacian A) (laplacian_symmetric A hA) k u
                  - eigvecOf (laplacian A) (laplacian_symmetric A hA) k v)
                  * (eigvecOf (laplacian A) (laplacian_symmetric A hA) l u
                    - eigvecOf (laplacian A) (laplacian_symmetric A hA) l v)) := by ring
        simp only [ssEdgeVec, if_neg hk, if_neg hl]
        rw [div_mul_div_comm, hn, hA2]
        ring
      simp only [hterm]
      have hpull : (∑ u, ∑ v, A u v * ((eigvecOf (laplacian A) (laplacian_symmetric A hA) k u
                - eigvecOf (laplacian A) (laplacian_symmetric A hA) k v)
              * (eigvecOf (laplacian A) (laplacian_symmetric A hA) l u
                - eigvecOf (laplacian A) (laplacian_symmetric A hA) l v)))
            / (2 * Real.sqrt (eigvalOf (laplacian A) (laplacian_symmetric A hA) k)
              * Real.sqrt (eigvalOf (laplacian A) (laplacian_symmetric A hA) l))
          = ∑ u, ∑ v, A u v * ((eigvecOf (laplacian A) (laplacian_symmetric A hA) k u
                - eigvecOf (laplacian A) (laplacian_symmetric A hA) k v)
              * (eigvecOf (laplacian A) (laplacian_symmetric A hA) l u
                - eigvecOf (laplacian A) (laplacian_symmetric A hA) l v))
            / (2 * Real.sqrt (eigvalOf (laplacian A) (laplacian_symmetric A hA) k)
              * Real.sqrt (eigvalOf (laplacian A) (laplacian_symmetric A hA) l)) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun u _ => by rw [Finset.sum_div]
      rw [← hpull,
        laplacian_dirichlet_bilinear A hA (eigvecOf (laplacian A) (laplacian_symmetric A hA) k)
          (eigvecOf (laplacian A) (laplacian_symmetric A hA) l),
        dotProduct_eigvecOf_mulVec (laplacian_symmetric A hA) k
          (eigvecOf (laplacian A) (laplacian_symmetric A hA) l)]
      by_cases hkl : k = l
      · have hδ : (eigvecOf (laplacian A) (laplacian_symmetric A hA) k)
            ⬝ᵥ (eigvecOf (laplacian A) (laplacian_symmetric A hA) k) = 1 := by
          rw [eigvecOf_dotProduct (laplacian_symmetric A hA) k k, if_pos rfl]
        rw [← hkl, hδ, mul_one]
        have hden : 2 * Real.sqrt (eigvalOf (laplacian A) (laplacian_symmetric A hA) k)
              * Real.sqrt (eigvalOf (laplacian A) (laplacian_symmetric A hA) k)
            = 2 * eigvalOf (laplacian A) (laplacian_symmetric A hA) k := by
          rw [mul_assoc, Real.mul_self_sqrt hkpos.le]
        rw [hden, div_self (by positivity : (2 : ℝ)
          * eigvalOf (laplacian A) (laplacian_symmetric A hA) k ≠ 0)]
        simp [hk]
      · have hδ : (eigvecOf (laplacian A) (laplacian_symmetric A hA) k)
            ⬝ᵥ (eigvecOf (laplacian A) (laplacian_symmetric A hA) l) = 0 := by
          rw [eigvecOf_dotProduct (laplacian_symmetric A hA) k l, if_neg hkl]
        rw [hδ, mul_zero]
        simp [hkl]

omit [DecidableEq V] in
private theorem quadForm_finset_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → Matrix V V ℝ) (x : V → ℝ) :
    quadForm (∑ i, M i) x = ∑ i, quadForm (M i) x := by
  have hadd : ∀ P Q : Matrix V V ℝ,
      quadForm (P + Q) x = quadForm P x + quadForm Q x := by
    intro P Q
    show x ⬝ᵥ ((P + Q) *ᵥ x) = x ⬝ᵥ (P *ᵥ x) + x ⬝ᵥ (Q *ᵥ x)
    rw [Matrix.add_mulVec, Matrix.dotProduct_add]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [quadForm]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]

theorem quadForm_imageProjector_eq (hnn : ∀ i j, 0 ≤ A i j) (x : V → ℝ) :
    quadForm (imageProjector A hA) x
      = ∑ e : V × V, (x ⬝ᵥ ssEdgeVec A hA e.1 e.2) ^ 2 := by
  conv_lhs => rw [← sum_rankOne_ssEdgeVec A hA hnn]
  rw [quadForm_finset_sum]
  exact Finset.sum_congr rfl fun e _ =>
    rankOne_quadForm (ssEdgeVec A hA e.1 e.2) x

end Projector

/-! ## The Bernoulli second moment -/

/-- The centered Bernoulli second moment on the product space:
`E[(δ_e/p_e − 1)²] = (1 − p_e)/p_e` at `p_e ≠ 0` — the variance factor
of every sampling summand. Computed by linearizing the square
(`δ² = δ` pointwise) and reusing the delivered first-moment integral
`integral_delta`; no measure-level enumeration is needed. -/
theorem integral_bern_center_sq {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) {e : ι}
    (hpne : p e ≠ 0) :
    ∫ ω : ι → Bool, ((if ω e then (1 : ℝ) else 0) / p e - 1) ^ 2
      ∂(bernPMF p hp0 hp1).toMeasure = (1 - p e) / p e := by
  have hfint : ∀ f : (ι → Bool) → ℝ, Integrable f (bernPMF p hp0 hp1).toMeasure :=
    fun f => Integrable.of_finite
  have hone : ∫ ω : ι → Bool, (1 : ℝ) ∂(bernPMF p hp0 hp1).toMeasure = 1 := by
    rw [integral_const, measure_univ, ENNReal.one_toReal, one_smul]
  have hkey : ∀ a : ℝ, a * a = a →
      (a / p e - 1) ^ 2
        = a / (p e * p e) - 2 * (a / p e) + 1 := by
    intro a ha
    have hexp : (a / p e - 1) ^ 2
        = a * a / (p e * p e) - 2 * (a / p e) + 1 := by
      rw [sq]
      field_simp
      ring
    rw [hexp, ha]
  set fδ : (ι → Bool) → ℝ := fun ω => if ω e then (1 : ℝ) else 0 with hfδ
  have hsq : ∀ ω : ι → Bool, fδ ω * fδ ω = fδ ω := by
    intro ω
    rw [hfδ]
    cases hω : ω e <;> simp [hω]
  have hlin : ∀ ω : ι → Bool,
      (fδ ω / p e - 1) ^ 2
        = fδ ω / (p e * p e) - 2 * (fδ ω / p e) + 1 :=
    fun ω => hkey (fδ ω) (hsq ω)
  have hfun : (fun ω : ι → Bool => (fδ ω / p e - 1) ^ 2)
      = fun ω : ι → Bool => fδ ω / (p e * p e)
        - 2 * (fδ ω / p e) + 1 := funext hlin
  have hδint : ∫ ω : ι → Bool, fδ ω ∂(bernPMF p hp0 hp1).toMeasure = p e :=
    integral_delta p hp0 hp1 e
  have hI1 : ∫ ω : ι → Bool, fδ ω / (p e * p e) ∂(bernPMF p hp0 hp1).toMeasure
      = p e / (p e * p e) := by rw [integral_div, hδint]
  have hI2 : ∫ ω : ι → Bool, 2 * (fδ ω / p e) ∂(bernPMF p hp0 hp1).toMeasure
      = 2 * (p e / p e) := by rw [integral_mul_left, integral_div, hδint]
  rw [hfun, integral_add (hfint _) (hfint _), integral_sub (hfint _) (hfint _),
    hI1, hI2, hone]
  field_simp
  ring

/-! ## The Finding-A-guarded sampling design -/

section Sampling

variable (A : WAdj (V := V)) (hA : A.IsSymm)

/-- Sampling probability at the ordered pair `e = (u, v)` at budget `q`:
`min 1 (q ‖v_e‖²)`. Saturated pairs (`p = 1`) are exactly those the
Finding-A guard zeroes. -/
noncomputable def ssProb (q : ℝ) (e : V × V) : ℝ :=
  min 1 (q * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2))

theorem ssProb_le_one (q : ℝ) (e : V × V) : ssProb A hA q e ≤ 1 :=
  min_le_left _ _

theorem ssProb_nonneg (q : ℝ) (hq : 0 ≤ q) (e : V × V) : 0 ≤ ssProb A hA q e := by
  refine le_min zero_le_one ?_
  exact mul_nonneg hq (dotProduct_self_nonneg _)

/-- Below saturation the probability is exactly the budget multiple. -/
theorem ssProb_eq_of_lt_one (q : ℝ) {e : V × V}
    (hlt : ssProb A hA q e < 1) :
    ssProb A hA q e
      = q * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2) := by
  rcases le_or_lt (q * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2)) 1 with h | h
  · show min 1 (q * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2))
        = q * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2)
    exact min_eq_right h
  · have hone : ssProb A hA q e = 1 := by
      show min 1 (q * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2)) = 1
      exact min_eq_left (le_of_lt h)
    rw [hone] at hlt
    exact absurd hlt (by norm_num)

/-- The Bernoulli indicator of the pair `e` at outcome `ω`. -/
noncomputable def ssDelta (e : V × V) (ω : (V × V) → Bool) : ℝ := if ω e then 1 else 0

/-- **The Finding-A-guarded sampling summand** of the pair `e` at budget
`q`: zero at saturated pairs (the guard that makes the uniform
pointwise norm bound hold — an unguarded saturated pair has a `−v_e⊗v_e`
outcome, refuted in QA), and otherwise the centered reweighted rank-one
contribution `(δ_e/p_e − 1) • (v_e v_eᵀ)`. Zero-leverage pairs (loops,
non-edges) are absorbed automatically: their `v_e` is zero, so the
rank-one factor is the zero matrix whatever the junk coefficient. -/
noncomputable def ssSummand (q : ℝ) (e : V × V) (ω : (V × V) → Bool) : Matrix V V ℝ :=
  if ssProb A hA q e = 1 then 0
  else ((ssDelta e ω / ssProb A hA q e) - 1) • rankOne (ssEdgeVec A hA e.1 e.2)

/-- The product-Bernoulli sampling measure on ordered pairs at the
design probabilities (the Slice-1 `bernPMF` at `ι = V × V`). -/
noncomputable def ssMeasure (q : ℝ) (hq : 0 ≤ q) :
    Measure ((V × V) → Bool) :=
  (bernPMF (fun e => ssProb A hA q e)
    (fun e => ssProb_nonneg A hA q hq e)
    (fun e => ssProb_le_one A hA q e)).toMeasure

theorem ssSummand_isSymm (q : ℝ) (e : V × V) (ω : (V × V) → Bool) :
    (ssSummand A hA q e ω).IsSymm := by
  unfold ssSummand
  split_ifs
  · exact Matrix.IsSymm.ext fun _ _ => rfl
  · exact Matrix.IsSymm.ext fun i j => by
      simp [rankOne_apply, mul_comm]

private theorem integral_ssSummand_of_zero (q : ℝ) (hq : 0 ≤ q)
    {e : V × V} (hz : ssEdgeVec A hA e.1 e.2 = 0) :
    ∫ ω : (V × V) → Bool, ssSummand A hA q e ω ∂ssMeasure A hA q hq = 0 := by
  have h0 : ssSummand A hA q e = fun _ => (0 : Matrix V V ℝ) := by
    funext ω
    unfold ssSummand
    split_ifs
    · rfl
    · rw [hz]
      ext i j
      simp [rankOne]
  rw [h0]
  simp

private theorem ssProb_pos_of_edgeVec_ne_zero (q : ℝ) (hq : 0 < q)
    {e : V × V} (hz : ssEdgeVec A hA e.1 e.2 ≠ 0) : 0 < ssProb A hA q e := by
  unfold ssProb
  exact lt_min zero_lt_one (mul_pos hq (dotProduct_self_pos_of_ne_zero hz))

/-- **Centering of the guarded summand** — the `h_mean` clause of
`matrix_bernstein` at this design: `∫ X_e = 0` for every ordered pair,
with no connectivity or nonnegativity hypothesis (zero-leverage pairs
are absorbed by the zero rank-one factor; saturated pairs by the guard;
the rest have `p_e > 0` and the Slice-1 centering integral applies). -/
theorem integral_ssSummand_eq_zero (q : ℝ) (hq : 0 < q) (e : V × V) :
    ∫ ω : (V × V) → Bool, ssSummand A hA q e ω ∂ssMeasure A hA q hq.le = 0 := by
  by_cases hz : ssEdgeVec A hA e.1 e.2 = 0
  · exact integral_ssSummand_of_zero A hA q hq.le hz
  · have hp0 : 0 < ssProb A hA q e := ssProb_pos_of_edgeVec_ne_zero A hA q hq hz
    by_cases hp1 : ssProb A hA q e = 1
    · have h0 : ssSummand A hA q e = fun _ => (0 : Matrix V V ℝ) := by
        funext ω; simp [ssSummand, hp1]
      rw [h0]; simp
    · have hfun : ssSummand A hA q e = fun ω : (V × V) → Bool =>
          ((if ω e then (1 : ℝ) else 0) / ssProb A hA q e - 1)
            • rankOne (ssEdgeVec A hA e.1 e.2) := by
        funext ω; simp only [ssSummand, ssDelta, if_neg hp1]
      show ∫ ω : (V × V) → Bool, ssSummand A hA q e ω
        ∂(bernPMF (fun e => ssProb A hA q e)
            (fun e => ssProb_nonneg A hA q hq.le e)
            (fun e => ssProb_le_one A hA q e)).toMeasure = 0
      rw [hfun]
      exact integral_coord_center_smul _ _ _ hp0.ne' _

/-- **The pointwise boundedness clause** — the `h_bound` input at this
design: `‖X_e ω‖ ≤ 1/q` for *every* outcome `ω` (the uniformity Finding
A demanded), at `0 < q`. The constant `R = 1/q` is the classical
Spielman–Srivastava value, here proved rather than asserted: the
rank-one norm bound and the unsaturated identification `p_e = q ‖v_e‖²`
compose to exactly `‖v_e‖²/p_e = 1/q`. -/
theorem ssSummand_l2OpNorm_le (q : ℝ) (hq : 0 < q) (e : V × V)
    (ω : (V × V) → Bool) :
    ‖ssSummand A hA q e ω‖ ≤ 1 / q := by
  have h1q : 0 ≤ 1 / q := by positivity
  by_cases hz : ssEdgeVec A hA e.1 e.2 = 0
  · have h0 : ssSummand A hA q e ω = 0 := by
      unfold ssSummand
      split_ifs
      · rfl
      · rw [hz]
        ext i j
        simp [rankOne]
    rw [h0, norm_zero]; exact h1q
  · have hp0 : 0 < ssProb A hA q e := ssProb_pos_of_edgeVec_ne_zero A hA q hq hz
    have hple : ssProb A hA q e ≤ 1 := ssProb_le_one A hA q e
    by_cases hp1 : ssProb A hA q e = 1
    · have h0 : ssSummand A hA q e ω = 0 := by simp [ssSummand, hp1]
      rw [h0, norm_zero]; exact h1q
    · have hp1' : ssProb A hA q e < 1 := lt_of_le_of_ne hple hp1
      have hpval := ssProb_eq_of_lt_one A hA q hp1'
      have habs : |ssDelta e ω / ssProb A hA q e - 1|
          ≤ 1 / ssProb A hA q e := by
        have hinvge : 1 ≤ 1 / ssProb A hA q e :=
          (le_div_iff₀ hp0).2 (by rw [one_mul]; exact hple)
        by_cases hω : ω e = true
        · rw [ssDelta, if_pos hω, abs_le]
          constructor <;> linarith [hinvge]
        · rw [ssDelta, if_neg hω, zero_div, zero_sub, abs_neg, abs_one]
          exact hinvge
      have hval : ssSummand A hA q e ω
          = (ssDelta e ω / ssProb A hA q e - 1)
            • rankOne (ssEdgeVec A hA e.1 e.2) := by
        simp only [ssSummand, if_neg hp1]
      have hstep : ‖ssSummand A hA q e ω‖
          ≤ (1 / ssProb A hA q e)
            * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2) := by
        rw [hval, norm_smul, Real.norm_eq_abs]
        calc |ssDelta e ω / ssProb A hA q e - 1|
              * ‖rankOne (ssEdgeVec A hA e.1 e.2)‖
            ≤ (1 / ssProb A hA q e)
              * ‖rankOne (ssEdgeVec A hA e.1 e.2)‖ :=
              mul_le_mul_of_nonneg_right habs (norm_nonneg _)
          _ ≤ (1 / ssProb A hA q e)
              * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2) :=
              mul_le_mul_of_nonneg_left (l2OpNorm_rankOne_le _) (by positivity)
      have hdotp : 0 < ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2 :=
        dotProduct_self_pos_of_ne_zero hz
      have hfinal : (1 / ssProb A hA q e)
          * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2) = 1 / q := by
        rw [hpval]
        field_simp
        ring
      exact hstep.trans (le_of_eq hfinal)

/-- **The variance statistic** — the axiom's `Σ` at ordered-pair
indexing: `Σ = ∑_e ((1−p_e)/p_e) ‖v_e‖² • (v_e v_eᵀ)`. The junk value at
zero-leverage pairs (`p_e = 0`) is exactly right: `(1−0)/0 = 0` in
ℝ, so such pairs contribute the zero matrix. -/
noncomputable def ssVariance (q : ℝ) : Matrix V V ℝ :=
  ∑ e : V × V, (((1 - ssProb A hA q e) / ssProb A hA q e)
    * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2))
    • rankOne (ssEdgeVec A hA e.1 e.2)

/-- The per-pair variance integral: `∫ X_e X_e = c_e • (v_e v_eᵀ)` with
`c_e = ((1−p_e)/p_e) ‖v_e‖²` — the classical Bernoulli second moment
composed with the rank-one idempotence `(v⊗v)² = ‖v‖² (v⊗v)`. -/
theorem integral_ssSummand_mul_self (q : ℝ) (hq : 0 < q) (e : V × V) :
    ∫ ω : (V × V) → Bool, ssSummand A hA q e ω * ssSummand A hA q e ω
      ∂ssMeasure A hA q hq.le
      = (((1 - ssProb A hA q e) / ssProb A hA q e)
        * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2))
        • rankOne (ssEdgeVec A hA e.1 e.2) := by
  by_cases hz : ssEdgeVec A hA e.1 e.2 = 0
  · have hp : ssProb A hA q e = 0 := by
      unfold ssProb
      rw [hz, Matrix.dotProduct_zero]
      simp
    have h0 : (fun ω : (V × V) → Bool => ssSummand A hA q e ω * ssSummand A hA q e ω)
        = fun _ => (0 : Matrix V V ℝ) := by
      funext ω
      unfold ssSummand
      split_ifs
      · simp
      · rw [hz]
        ext i j
        simp [rankOne, Matrix.mul_apply, Finset.sum_const_zero]
    rw [h0, integral_zero, hp]
    simp
  · have hp0 : 0 < ssProb A hA q e := ssProb_pos_of_edgeVec_ne_zero A hA q hq hz
    by_cases hp1 : ssProb A hA q e = 1
    · have h0 : (fun ω : (V × V) → Bool =>
            ssSummand A hA q e ω * ssSummand A hA q e ω)
          = fun _ => (0 : Matrix V V ℝ) := by
        funext ω; simp [ssSummand, hp1]
      rw [h0, integral_zero, hp1]
      simp
    · have hfun : (fun ω : (V × V) → Bool =>
            ssSummand A hA q e ω * ssSummand A hA q e ω)
          = fun ω : (V × V) → Bool =>
            (((if ω e then (1 : ℝ) else 0) / ssProb A hA q e - 1)
              * ((if ω e then (1 : ℝ) else 0) / ssProb A hA q e - 1)
              * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2))
              • rankOne (ssEdgeVec A hA e.1 e.2) := by
        funext ω
        have hval : ssSummand A hA q e ω
            = (ssDelta e ω / ssProb A hA q e - 1)
              • rankOne (ssEdgeVec A hA e.1 e.2) := by
          simp only [ssSummand, if_neg hp1]
        rw [hval, smul_mul_assoc, Matrix.mul_smul, smul_smul,
          rankOne_mul_self, smul_smul, ssDelta]
      rw [hfun, integral_smul_const, integral_mul_right]
      have hint : ∫ ω : (V × V) → Bool,
          ((if ω e then (1 : ℝ) else 0) / ssProb A hA q e - 1)
            * ((if ω e then (1 : ℝ) else 0) / ssProb A hA q e - 1)
          ∂ssMeasure A hA q hq.le = (1 - ssProb A hA q e) / ssProb A hA q e := by
        have h := integral_bern_center_sq (fun e => ssProb A hA q e)
          (fun e => ssProb_nonneg A hA q hq.le e)
          (fun e => ssProb_le_one A hA q e) (e := e) hp0.ne'
        simpa only [ssMeasure, pow_two] using h
      rw [hint]

/-- The variance statistic is the sum of the per-pair variance
integrals — exactly the `∑ i, ∫ X i * X i` shape `matrix_bernstein`
consumes. -/
theorem sum_integral_ssSummand_mul_self (q : ℝ) (hq : 0 < q) :
    ∑ e : V × V, ∫ ω : (V × V) → Bool,
        ssSummand A hA q e ω * ssSummand A hA q e ω ∂ssMeasure A hA q hq.le
      = ssVariance A hA q :=
  Finset.sum_congr rfl fun e _ => integral_ssSummand_mul_self A hA q hq e

theorem ssVariance_coeff_nonneg (q : ℝ) (hq : 0 ≤ q) (e : V × V) :
    0 ≤ ((1 - ssProb A hA q e) / ssProb A hA q e)
      * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2) := by
  by_cases hp : ssProb A hA q e = 0
  · rw [hp]; norm_num
  · have hp0 : 0 < ssProb A hA q e := lt_of_le_of_ne (ssProb_nonneg A hA q hq e)
      (fun h => hp h.symm)
    refine mul_nonneg ?_ (dotProduct_self_nonneg _)
    exact div_nonneg (by linarith [ssProb_le_one A hA q e]) hp0.le

theorem ssVariance_coeff_le (q : ℝ) (hq : 0 < q) (e : V × V) :
    ((1 - ssProb A hA q e) / ssProb A hA q e)
      * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2) ≤ 1 / q := by
  by_cases hp : ssProb A hA q e = 0
  · rw [hp]; norm_num; positivity
  · by_cases hz : ssEdgeVec A hA e.1 e.2 = 0
    · have hdot : ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2 = 0 := by
        rw [hz, Matrix.dotProduct_zero]
      rw [hdot, mul_zero]; positivity
    · have hdot : 0 < ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2 :=
        dotProduct_self_pos_of_ne_zero hz
      have hp0 : 0 < ssProb A hA q e := ssProb_pos_of_edgeVec_ne_zero A hA q hq hz
      by_cases hp1 : ssProb A hA q e = 1
      · rw [hp1, sub_self, zero_div, zero_mul]
        exact div_nonneg zero_le_one hq.le
      · have hp1' : ssProb A hA q e < 1 :=
          lt_of_le_of_ne (ssProb_le_one A hA q e) hp1
        have hpval := ssProb_eq_of_lt_one A hA q hp1'
        rw [hpval]
        have hkey : ((1 - q * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2))
            / (q * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2)))
            * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2) = 1 / q
            - (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2) := by
          field_simp
          ring
        rw [hkey]
        linarith

omit [DecidableEq V] in
private theorem quadForm_smul' (c : ℝ) (M : Matrix V V ℝ) (x : V → ℝ) :
    quadForm (c • M) x = c * quadForm M x := by
  simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by ring

theorem quadForm_ssVariance_eq (q : ℝ) (x : V → ℝ) :
    quadForm (ssVariance A hA q) x
      = ∑ e : V × V, (((1 - ssProb A hA q e) / ssProb A hA q e)
          * (ssEdgeVec A hA e.1 e.2 ⬝ᵥ ssEdgeVec A hA e.1 e.2))
          * (x ⬝ᵥ ssEdgeVec A hA e.1 e.2) ^ 2 := by
  unfold ssVariance
  rw [quadForm_finset_sum]
  exact Finset.sum_congr rfl fun e _ => by
    rw [quadForm_smul', rankOne_quadForm]

theorem quadForm_ssVariance_nonneg (q : ℝ) (hq : 0 ≤ q) (x : V → ℝ) :
    0 ≤ quadForm (ssVariance A hA q) x := by
  rw [quadForm_ssVariance_eq]
  exact Finset.sum_nonneg fun e _ => mul_nonneg
    (ssVariance_coeff_nonneg A hA q hq e) (sq_nonneg _)

theorem quadForm_ssVariance_le (q : ℝ) (hq : 0 < q) (hnn : ∀ i j, 0 ≤ A i j)
    (x : V → ℝ) :
    quadForm (ssVariance A hA q) x
      ≤ (1 / q) * quadForm (imageProjector A hA) x := by
  have hpull : (1 / q) * ∑ e : V × V, (x ⬝ᵥ ssEdgeVec A hA e.1 e.2) ^ 2
      = ∑ e : V × V, (1 / q) * (x ⬝ᵥ ssEdgeVec A hA e.1 e.2) ^ 2 :=
    Finset.mul_sum (Finset.univ : Finset (V × V))
      (fun e => (x ⬝ᵥ ssEdgeVec A hA e.1 e.2) ^ 2) (1 / q)
  rw [quadForm_ssVariance_eq A hA q x,
    quadForm_imageProjector_eq A hA hnn x, hpull]
  exact Finset.sum_le_sum fun e _ =>
    mul_le_mul_of_nonneg_right (ssVariance_coeff_le A hA q hq e) (sq_nonneg _)

omit [Fintype V] [DecidableEq V] in
private theorem isSymm_finset_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → Matrix V V ℝ) (hM : ∀ e, (M e).IsSymm) : (∑ e, M e).IsSymm := by
  have hzero : ((0 : Matrix V V ℝ)).IsSymm := Matrix.IsSymm.ext fun _ _ => rfl
  have hadd : ∀ P Q : Matrix V V ℝ, P.IsSymm → Q.IsSymm → (P + Q).IsSymm := by
    intro P Q hP hQ
    exact Matrix.IsSymm.ext fun i j => by
      rw [Matrix.add_apply, Matrix.add_apply, hP.apply i j, hQ.apply i j]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => exact hzero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hadd _ _ (hM a) ih

theorem ssVariance_isSymm (q : ℝ) : (ssVariance A hA q).IsSymm := by
  refine isSymm_finset_sum _ fun e => ?_
  apply Matrix.IsSymm.ext
  intro i j
  simp only [Matrix.transpose_smul, Matrix.smul_apply, smul_eq_mul,
    rankOne_apply, mul_comm]

/-- **The variance bound** — the classical `‖Σ‖ ≤ 1/q` (the Step-0
survey's asserted constant, here proved): the coefficients are dominated
by `1/q`, the residual rank-one sum is *exactly* the image projector,
and the projector's Rayleigh form is dominated by `x ⬝ᵥ x`. Eigenvalue
route: every eigenvector's Rayleigh quotient lies in `[0, 1/q]`, so every
eigenvalue does, and the operator norm (the max absolute eigenvalue)
follows. -/
theorem l2OpNorm_ssVariance_le (q : ℝ) (hq : 0 < q) (hnn : ∀ i j, 0 ≤ A i j) :
    ‖ssVariance A hA q‖ ≤ 1 / q := by
  have hsymm := ssVariance_isSymm A hA q
  refine Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.l2OpNorm_le_of_abs_eigvalOf_le
    hsymm (by positivity) fun i => ?_
  rw [abs_le, ← quadForm_eigvecOf_self hsymm i]
  have hge := quadForm_ssVariance_nonneg A hA q hq.le
    (eigvecOf (ssVariance A hA q) hsymm i)
  have hle := quadForm_ssVariance_le A hA q hq hnn
    (eigvecOf (ssVariance A hA q) hsymm i)
  have hproj := quadForm_imageProjector_le A hA
    (eigvecOf (ssVariance A hA q) hsymm i)
  have hunit : (eigvecOf (ssVariance A hA q) hsymm i)
      ⬝ᵥ (eigvecOf (ssVariance A hA q) hsymm i) = 1 := by
    simpa [Matrix.dotProduct] using
      eigvecOf_inner (ssVariance A hA q) hsymm i i
  have h1q : 0 ≤ 1 / q := by positivity
  have hP1 : (1 / q) * quadForm (imageProjector A hA)
      (eigvecOf (ssVariance A hA q) hsymm i) ≤ 1 / q := by
    have hPle1 : quadForm (imageProjector A hA)
        (eigvecOf (ssVariance A hA q) hsymm i) ≤ 1 := hproj.trans_eq hunit
    calc (1 / q) * quadForm (imageProjector A hA)
          (eigvecOf (ssVariance A hA q) hsymm i)
        ≤ (1 / q) * 1 := mul_le_mul_of_nonneg_left hPle1 h1q
      _ = 1 / q := by ring
  constructor
  · linarith
  · linarith

end Sampling

end SpectralGraphTheory

