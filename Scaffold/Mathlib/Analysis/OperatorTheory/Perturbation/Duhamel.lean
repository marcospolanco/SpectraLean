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
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.ProjectionGap
import Scaffold.Mathlib.GraphTheory.Spectral
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.FundThmCalculus

/-!
# The Duhamel bound for spectral projectors

The second component of the Davis–Kahan retirement
(`proposals/discharge-perturbation-axioms.md`, Step-1 split): the
exponential-integral (Duhamel) route to

`‖(1 - Q) * P‖ ≤ ‖E‖ / (b - a)`,

where `P` is the spectral projector of a symmetric `A` at threshold
`a`, `Q` the spectral projector of the symmetric perturbation `A + E`
at threshold `c'`, and every eigenvalue of `A + E` strictly above `c'`
is at least `b > a`. Combined with the equal-rank projector identity
(`ProjectionGap.l2OpNorm_sub_eq_of_rank_eq`, the delivered component 1)
this retires `davis_kahan_sin_theta` at constant 1 in the operator
norm — the bound the cheaper entrywise eigenbasis-coordinate route
provably cannot reach (it caps at the Frobenius shape with constant
√(k+1); see the proposal's Step-0 survey).

Everything is proved — **no statement in this module is admitted**.
`#print axioms` on every public theorem reads only `propext,
Classical.choice, Quot.sound`.

## Route (recorded before stating)

The semigroups live at vector level as damped eigenbasis expansions
(`heatApply`; no `Matrix.exp`):

- `heatApply hM t x = ∑ i, e^{-t λ i} (v i ⬝ᵥ x) • v i` — for a
  symmetric `M` with eigenpairs `(λ i, v i)`; negative `t` is the
  growing semigroup, used on the unperturbed matrix's low cluster.
- Pairing two such solutions along the two matrices gives
  `g t := ⟨e^{-t(A+E)} z_y, e^{tA} z_x⟩` whose derivative is exactly
  `-⟨e^{-t(A+E)} z_y, E e^{tA} z_x⟩` (the Duhamel integrand): the
  `A`-derivative and the `(A+E)`-derivative cancel through the
  symmetry shuffle `dotProduct_mulVec_symm`, leaving the defect `E`.
- The fundamental theorem of calculus on `[0, T]` plus the explicit
  exponential majorant (cluster-filtered Parseval damping supplies
  `‖e^{-t(A+E)} z_y‖ ≤ e^{-t b} ‖z_y‖` and
  `‖e^{tA} z_x‖ ≤ e^{t a} ‖z_x‖`) bounds the pairing at `t = 0` by
  `|g T| + ‖E‖ (1 - e^{-(b-a)T}) / (b-a)`; the boundary term decays
  like `e^{-(b-a)T}`, so `T → ∞` leaves the bound.
- The operator norm is bounded through the pairing (duality)
  characterization `l2OpNorm_le_of_abs_dotProduct_le`.

The `t = 0` identification `heatApply hM 0 z = z` is the eigenbasis
expansion (`eigvecOf_expansion_apply`).
-/

open scoped Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation

open Matrix SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## 1. The heat semigroup at vector level
-/

section Heat

variable {M : Matrix V V ℝ} (hM : M.IsSymm)

/-- The heat semigroup at vector level: damp each eigenbasis
coefficient by `e^{-tλ}`. A finite sum over the eigenbasis; no
`Matrix.exp`. For negative `t` this is the *growing* semigroup
`e^{tM}`, used on the unperturbed matrix's low cluster. -/
noncomputable def heatApply (t : ℝ) (x : V → ℝ) : V → ℝ := fun a =>
  ∑ i, Real.exp (-t * eigvalOf M hM i) *
    (Matrix.dotProduct (eigvecOf M hM i) x * eigvecOf M hM i a)

/-- Reassociated form of the damped expansion, shaped for
`mulVec_eigvecOf_sum_apply`. -/
theorem heatApply_eq (t : ℝ) (x : V → ℝ) :
    heatApply hM t x = fun a => ∑ i, (Real.exp (-t * eigvalOf M hM i) *
      Matrix.dotProduct (eigvecOf M hM i) x) * eigvecOf M hM i a := by
  funext a
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Eigenaction: `M *ᵥ (heatApply t x)` is the damped expansion with the
extra eigenvalue factor — directly from `mulVec_eigvecOf_sum_apply`. -/
theorem heatApply_mulVec (t : ℝ) (x : V → ℝ) (a : V) :
    (M *ᵥ heatApply hM t x) a
      = ∑ i, Real.exp (-t * eigvalOf M hM i) *
        (Matrix.dotProduct (eigvecOf M hM i) x
          * (eigvalOf M hM i * eigvecOf M hM i a)) := by
  rw [heatApply_eq hM t x, mulVec_eigvecOf_sum_apply hM _ a]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The damped signal paired with anything resolves through the damped
coefficients (the adjoint/expansion workhorse). -/
theorem heatApply_dotProduct (t : ℝ) (x y : V → ℝ) :
    Matrix.dotProduct (heatApply hM t x) y
      = ∑ i, Real.exp (-t * eigvalOf M hM i) *
          (Matrix.dotProduct (eigvecOf M hM i) x *
            Matrix.dotProduct (eigvecOf M hM i) y) := by
  have hterm : ∀ i : V,
      Real.exp (-t * eigvalOf M hM i) *
        (Matrix.dotProduct (eigvecOf M hM i) x *
          Matrix.dotProduct (eigvecOf M hM i) y)
      = ∑ a, Real.exp (-t * eigvalOf M hM i) *
          (Matrix.dotProduct (eigvecOf M hM i) x
            * eigvecOf M hM i a) * y a := by
    intro i
    simp only [Matrix.dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  calc Matrix.dotProduct (heatApply hM t x) y
      = ∑ a, (∑ i, Real.exp (-t * eigvalOf M hM i) *
          (Matrix.dotProduct (eigvecOf M hM i) x
            * eigvecOf M hM i a)) * y a := rfl
    _ = ∑ i, ∑ a, Real.exp (-t * eigvalOf M hM i) *
          (Matrix.dotProduct (eigvecOf M hM i) x
            * eigvecOf M hM i a) * y a := by
        simp only [Finset.sum_mul]
        exact Finset.sum_comm
    _ = ∑ i, Real.exp (-t * eigvalOf M hM i) *
          (Matrix.dotProduct (eigvecOf M hM i) x *
            Matrix.dotProduct (eigvecOf M hM i) y) :=
        Finset.sum_congr rfl fun i _ => (hterm i).symm

/-- Parseval damping: the squared norm of the damped signal is the sum
of `e^{-2tλ}`-damped squared coefficients. -/
theorem heatApply_dotProduct_self (t : ℝ) (x : V → ℝ) :
    Matrix.dotProduct (heatApply hM t x) (heatApply hM t x)
      = ∑ i, Real.exp (-t * eigvalOf M hM i) *
          (Real.exp (-t * eigvalOf M hM i) *
            (Matrix.dotProduct (eigvecOf M hM i) x *
              Matrix.dotProduct (eigvecOf M hM i) x)) := by
  rw [heatApply_dotProduct hM t x (heatApply hM t x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hself : ∀ j : V,
      Matrix.dotProduct (eigvecOf M hM j) (eigvecOf M hM j) = 1 := by
    intro j
    rw [show Matrix.dotProduct (eigvecOf M hM j) (eigvecOf M hM j)
        = ∑ k, eigvecOf M hM j k * eigvecOf M hM j k from rfl,
      eigvecOf_inner, if_pos rfl]
  have hcross : ∀ j₁ j₂ : V, j₁ ≠ j₂ →
      Matrix.dotProduct (eigvecOf M hM j₁) (eigvecOf M hM j₂) = 0 := by
    intro j₁ j₂ hj
    rw [show Matrix.dotProduct (eigvecOf M hM j₁) (eigvecOf M hM j₂)
        = ∑ k, eigvecOf M hM j₁ k * eigvecOf M hM j₂ k from rfl,
      eigvecOf_inner, if_neg hj]
  have hflip : Matrix.dotProduct (eigvecOf M hM i) (heatApply hM t x)
      = Real.exp (-t * eigvalOf M hM i)
          * Matrix.dotProduct (eigvecOf M hM i) x := by
    rw [Matrix.dotProduct_comm, heatApply_dotProduct hM t x (eigvecOf M hM i)]
    rw [Finset.sum_eq_single i]
    · rw [hself i]
      ring
    · intro j _ hj
      rw [hcross j i hj]
      ring
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hflip]
  ring

/-- At `t = 0` the semigroup is the identity: the eigenbasis expansion
of the input (`eigvecOf_expansion_apply`). -/
theorem heatApply_zero (x : V → ℝ) : heatApply hM 0 x = x := by
  funext a
  simp only [heatApply, Real.exp_zero, one_mul, neg_zero, zero_mul]
  exact eigvecOf_expansion_apply hM x a

/-- Differentiability of one entry of the damped signal in `t`: the
derivative damps by one more eigenvalue factor. Finite sum of
exponentials. -/
theorem heatApply_hasDerivAt (x : V → ℝ) (a : V) (t : ℝ) :
    HasDerivAt (fun s => heatApply hM s x a)
      (∑ i, -eigvalOf M hM i * Real.exp (-t * eigvalOf M hM i) *
        (Matrix.dotProduct (eigvecOf M hM i) x * eigvecOf M hM i a)) t := by
  have hderiv : ∀ i : V,
      HasDerivAt (fun s => Real.exp (-s * eigvalOf M hM i) *
        (Matrix.dotProduct (eigvecOf M hM i) x * eigvecOf M hM i a))
        (Real.exp (-t * eigvalOf M hM i) * (-1 * eigvalOf M hM i) *
          (Matrix.dotProduct (eigvecOf M hM i) x * eigvecOf M hM i a)) t := by
    intro i
    have h0 : HasDerivAt (fun s => -s * eigvalOf M hM i)
        (-1 * eigvalOf M hM i) t :=
      (hasDerivAt_id t).neg.mul_const (eigvalOf M hM i)
    exact (h0.exp).mul_const
      (Matrix.dotProduct (eigvecOf M hM i) x * eigvecOf M hM i a)
  have hsum : HasDerivAt
      (fun s => ∑ i, Real.exp (-s * eigvalOf M hM i) *
        (Matrix.dotProduct (eigvecOf M hM i) x * eigvecOf M hM i a))
      (∑ i, Real.exp (-t * eigvalOf M hM i) * (-1 * eigvalOf M hM i) *
        (Matrix.dotProduct (eigvecOf M hM i) x * eigvecOf M hM i a)) t :=
    HasDerivAt.sum fun i _ => hderiv i
  convert hsum using 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Continuity in `t` of one entry of the damped signal. -/
theorem continuous_heatApply (x : V → ℝ) (a : V) :
    Continuous fun t => heatApply hM t x a := by
  refine continuous_finset_sum _ fun i _ => ?_
  have hc : Continuous fun t => -t * eigvalOf M hM i :=
    continuous_id.neg.mul continuous_const
  exact (Real.continuous_exp.comp hc).mul continuous_const

end Heat

/-!
## 2. Pairing (duality) bound on the operator norm
-/

section PairingNorm

omit [DecidableEq V] in
/-- The Euclidean norm of the packaged vector is the square root of the
dot product with itself. -/
theorem norm_euclidean_eq_sqrt (z : V → ℝ) :
    ‖((WithLp.equiv 2 (V → ℝ)).symm z : EuclideanSpace ℝ V)‖
      = Real.sqrt (z ⬝ᵥ z) := by
  have h : ‖((WithLp.equiv 2 (V → ℝ)).symm z : EuclideanSpace ℝ V)‖
      * ‖((WithLp.equiv 2 (V → ℝ)).symm z : EuclideanSpace ℝ V)‖
      = z ⬝ᵥ z := by
    rw [← pow_two, ← real_inner_self_eq_norm_sq,
      EuclideanSpace.inner_eq_star_dotProduct]
    simp [star_trivial]
  rw [← h, Real.sqrt_mul_self (norm_nonneg _)]

omit [DecidableEq V] in
/-- Cauchy–Schwarz for the plain dot product, transported through the
Euclidean-space inner product. -/
theorem abs_dotProduct_le (x y : V → ℝ) :
    |x ⬝ᵥ y| ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
  have hinner : inner
      ((WithLp.equiv 2 (V → ℝ)).symm x : EuclideanSpace ℝ V)
      ((WithLp.equiv 2 (V → ℝ)).symm y) = x ⬝ᵥ y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [star_trivial]
  have hcs : |x ⬝ᵥ y|
      ≤ ‖((WithLp.equiv 2 (V → ℝ)).symm x : EuclideanSpace ℝ V)‖ *
        ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖ := by
    rw [← hinner, ← Real.norm_eq_abs]
    exact norm_inner_le_norm _ _
  rw [norm_euclidean_eq_sqrt, norm_euclidean_eq_sqrt] at hcs
  exact hcs

/-- **Operator-norm bound through pairings.** If every pairing
`|y ⬝ᵥ (M *ᵥ x)|` is bounded by `c ‖x‖ ‖y‖` (Euclidean lengths), then
`‖M‖ ≤ c`. Proof by self-application: the pairing bound at
`y := M *ᵥ x` reads `‖M *ᵥ x‖² ≤ c ‖x‖ ‖M *ᵥ x‖`, which forces
`‖M *ᵥ x‖ ≤ c ‖x‖`; squaring gives the hypothesis of the
`opNorm_le_bound` transport. -/
theorem l2OpNorm_le_of_abs_dotProduct_le {M : Matrix V V ℝ} {c : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ x y : V → ℝ, |y ⬝ᵥ (M *ᵥ x)|
      ≤ c * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)) :
    ‖M‖ ≤ c := by
  have hdnn : ∀ w : V → ℝ, 0 ≤ w ⬝ᵥ w := fun w =>
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hsq : ∀ z : V → ℝ, (M *ᵥ z) ⬝ᵥ (M *ᵥ z) ≤ c * c * (z ⬝ᵥ z) := by
    intro z
    have hz := h z (M *ᵥ z)
    rw [abs_of_nonneg (hdnn (M *ᵥ z))] at hz
    have hsnn : 0 ≤ Real.sqrt ((M *ᵥ z) ⬝ᵥ (M *ᵥ z)) := Real.sqrt_nonneg _
    have hrnn : 0 ≤ Real.sqrt (z ⬝ᵥ z) := Real.sqrt_nonneg _
    have hs2 : Real.sqrt ((M *ᵥ z) ⬝ᵥ (M *ᵥ z))
        * Real.sqrt ((M *ᵥ z) ⬝ᵥ (M *ᵥ z)) = (M *ᵥ z) ⬝ᵥ (M *ᵥ z) :=
      Real.mul_self_sqrt (hdnn (M *ᵥ z))
    have hr2 : Real.sqrt (z ⬝ᵥ z) * Real.sqrt (z ⬝ᵥ z) = z ⬝ᵥ z :=
      Real.mul_self_sqrt (hdnn z)
    rcases eq_or_lt_of_le hsnn with h0 | hpos
    · rw [← hs2, ← h0, zero_mul]
      exact mul_nonneg (mul_nonneg hc hc) (hdnn z)
    · have hsr : Real.sqrt ((M *ᵥ z) ⬝ᵥ (M *ᵥ z)) ≤ c * Real.sqrt (z ⬝ᵥ z) :=
        by nlinarith [hz, hs2]
      have hfinal : Real.sqrt ((M *ᵥ z) ⬝ᵥ (M *ᵥ z))
          * Real.sqrt ((M *ᵥ z) ⬝ᵥ (M *ᵥ z))
          ≤ (c * Real.sqrt (z ⬝ᵥ z)) * (c * Real.sqrt (z ⬝ᵥ z)) :=
        mul_le_mul hsr hsr (by nlinarith) (mul_nonneg hc hrnn)
      rw [hs2] at hfinal
      nlinarith [hfinal, hr2, mul_nonneg hc hrnn]
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) M :
      EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)) hc ?_
  intro x
  have hxe : x = (WithLp.equiv 2 (V → ℝ)).symm
      ((WithLp.equiv 2 (V → ℝ)) x) := (Equiv.apply_symm_apply _ _).symm
  have hact : ((Matrix.toEuclideanCLM (𝕜 := ℝ) M :
      EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)) x
      = (WithLp.equiv 2 (V → ℝ)).symm
          (M *ᵥ ((WithLp.equiv 2 (V → ℝ)) x)) := by
    conv_lhs => rw [hxe]
    rw [Matrix.toEuclideanCLM_piLp_equiv_symm, Matrix.toLin'_apply]
  rw [hact, hxe]
  have h2' : ‖((WithLp.equiv 2 (V → ℝ)).symm
      (M *ᵥ ((WithLp.equiv 2 (V → ℝ)) x)) : EuclideanSpace ℝ V)‖ ^ 2
      ≤ (c * ‖((WithLp.equiv 2 (V → ℝ)).symm
          ((WithLp.equiv 2 (V → ℝ)) x) : EuclideanSpace ℝ V)‖) ^ 2 := by
    rw [mul_pow, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, pow_two]
    exact hsq ((WithLp.equiv 2 (V → ℝ)) x)
  have hfinal := abs_le_of_sq_le_sq h2' (mul_nonneg hc (norm_nonneg _))
  rwa [abs_of_nonneg (norm_nonneg _)] at hfinal

end PairingNorm

/-!
## 3. The sorted-spectrum step lemma

Eigenvalues of the eigenbasis listing that are strictly above the `k`-th
sorted entry are at least the `k+1`-st sorted entry — the interior
companion of `evals_first_le_eigvalOf` / `eigvalOf_le_evals_last`,
load-bearing for the `(A + E)`-side decay rate.
-/

section SortedStep

theorem evals_succ_le_of_lt {M : Matrix V V ℝ} (hM : M.IsSymm)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    {i : V} (h : evals hM k < eigvalOf M hM i) :
    evals hM ⟨(k : ℕ) + 1, hk⟩ ≤ eigvalOf M hM i := by
  set L : List ℝ := Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map
        ((isHermitian_of_isSymm hM).eigenvalues)) with hL
  have hlen : L.length = Fintype.card V := by
    rw [hL, Multiset.length_sort, Multiset.card_map]; simp
  have hsort : L.Sorted (fun a b => a ≤ b) := by
    rw [hL]; exact Multiset.sort_sorted _ _
  have hgetle : ∀ q r : Fin L.length, (q : ℕ) ≤ (r : ℕ) → L.get q ≤ L.get r := by
    intro q r hqr
    rcases lt_or_eq_of_le hqr with hlt | heq
    · exact hsort.rel_get_of_lt hlt
    · rw [Fin.ext heq]
  have hmem : eigvalOf M hM i ∈ L := by
    rw [hL, Multiset.mem_sort]
    exact Multiset.mem_map.2 ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨p, hp⟩ := List.mem_iff_get.1 hmem
  have hpn : p.1 < Fintype.card V := by rw [← hlen]; exact p.isLt
  -- the position of `eigvalOf i` in the sorted list is strictly above `k`
  have hklt : (k : ℕ) < L.length := by rw [hlen]; omega
  have hposk : (k : ℕ) < p.1 := by
    by_contra hcon
    push_neg at hcon
    have hle := hgetle p ⟨(k : ℕ), hklt⟩ hcon
    rw [hp] at hle
    have hev : evals hM k = L.get ⟨(k : ℕ), hklt⟩ := rfl
    rw [hev] at h
    exact absurd h (not_lt.2 hle)
  -- so the k+1-st sorted entry sits at or before that position
  have hnextlt : (k : ℕ) + 1 < L.length := by rw [hlen]; omega
  have hge := hgetle ⟨(k : ℕ) + 1, hnextlt⟩ p
    (by show (k : ℕ) + 1 ≤ p.1; omega)
  rw [hp] at hge
  exact hge

end SortedStep

/-!
## 4. The projector coefficient filter
-/

section CoeffFilter

/-- The eigenbasis coefficients of a spectral-projected vector: the
projector at threshold `c` keeps exactly the coefficients at eigenvalues
`≤ c`. Read through the projector's symmetry and its action on the
eigenbasis (`spectralProjector_mulVec_eigvecOf`). -/
theorem dotProduct_eigvecOf_spectralProjector_mulVec {M : Matrix V V ℝ}
    (hM : M.IsSymm) (c : ℝ) (i : V) (z : V → ℝ) :
    Matrix.dotProduct (eigvecOf M hM i) (spectralProjector M hM c *ᵥ z)
      = if eigvalOf M hM i ≤ c
        then Matrix.dotProduct (eigvecOf M hM i) z else 0 := by
  calc Matrix.dotProduct (eigvecOf M hM i) (spectralProjector M hM c *ᵥ z)
      = (eigvecOf M hM i ᵥ* spectralProjector M hM c) ⬝ᵥ z :=
        Matrix.dotProduct_mulVec _ _ _
    _ = ((spectralProjector M hM c)ᵀ *ᵥ eigvecOf M hM i) ⬝ᵥ z := by
        rw [Matrix.mulVec_transpose]
    _ = (spectralProjector M hM c *ᵥ eigvecOf M hM i) ⬝ᵥ z := by
        rw [(spectralProjector_symmetric M hM c).eq]
    _ = (if eigvalOf M hM i ≤ c then eigvecOf M hM i else 0) ⬝ᵥ z := by
        rw [spectralProjector_mulVec_eigvecOf M hM c i]
    _ = if eigvalOf M hM i ≤ c
        then Matrix.dotProduct (eigvecOf M hM i) z else 0 := by
        by_cases h : eigvalOf M hM i ≤ c <;> simp [h]

end CoeffFilter

/-!
## 5. Cluster-filtered decay bounds (Parseval damping)
-/

section Decay

variable {M : Matrix V V ℝ} (hM : M.IsSymm)

/-- **Decaying side.** If `z` has no eigencomponents at eigenvalues `≤ c'`,
then `‖e^{-tM} z‖² ≤ e^{-2bt} ‖z‖²` for `t ≥ 0`, provided every
eigenvalue strictly above `c'` is at least `b`. -/
theorem heatApply_dotProduct_self_le_of_le {c' b t : ℝ} (ht : 0 ≤ t)
    (z : V → ℝ)
    (h : ∀ i : V, eigvalOf M hM i ≤ c' →
      Matrix.dotProduct (eigvecOf M hM i) z = 0)
    (hcl : ∀ i : V, c' < eigvalOf M hM i → b ≤ eigvalOf M hM i) :
    Matrix.dotProduct (heatApply hM t z) (heatApply hM t z)
      ≤ Real.exp (-b * t) * (Real.exp (-b * t) * (z ⬝ᵥ z)) := by
  rw [heatApply_dotProduct_self hM t z]
  have hterm : ∀ i : V,
      Real.exp (-t * eigvalOf M hM i) * (Real.exp (-t * eigvalOf M hM i) *
          (Matrix.dotProduct (eigvecOf M hM i) z *
            Matrix.dotProduct (eigvecOf M hM i) z))
      ≤ Real.exp (-b * t) * (Real.exp (-b * t) *
          (Matrix.dotProduct (eigvecOf M hM i) z *
            Matrix.dotProduct (eigvecOf M hM i) z)) := by
    intro i
    by_cases hc : eigvalOf M hM i ≤ c'
    · rw [h i hc, mul_zero, mul_zero, mul_zero]
      norm_num
    · have hb := hcl i (by linarith)
      have hcnn : 0 ≤ Matrix.dotProduct (eigvecOf M hM i) z *
          Matrix.dotProduct (eigvecOf M hM i) z := mul_self_nonneg _
      have hexp : Real.exp (-t * eigvalOf M hM i) ≤ Real.exp (-b * t) :=
        Real.exp_le_exp.2 (by nlinarith [hb, ht])
      exact mul_le_mul hexp (mul_le_mul_of_nonneg_right hexp hcnn)
        (mul_nonneg (Real.exp_nonneg _) hcnn) (Real.exp_nonneg _)
  have hpar : z ⬝ᵥ z
      = ∑ i, Matrix.dotProduct (eigvecOf M hM i) z
          * Matrix.dotProduct (eigvecOf M hM i) z :=
    dotProduct_eigvecOf hM z z
  calc ∑ i, Real.exp (-t * eigvalOf M hM i) *
        (Real.exp (-t * eigvalOf M hM i) *
          (Matrix.dotProduct (eigvecOf M hM i) z *
            Matrix.dotProduct (eigvecOf M hM i) z))
      ≤ ∑ i, Real.exp (-b * t) * (Real.exp (-b * t) *
          (Matrix.dotProduct (eigvecOf M hM i) z *
            Matrix.dotProduct (eigvecOf M hM i) z)) :=
        (Finset.sum_le_sum fun i _ => hterm i)
    _ = Real.exp (-b * t) * (Real.exp (-b * t) * (z ⬝ᵥ z)) := by
        rw [hpar, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **Growing side.** If `z` has no eigencomponents at eigenvalues
strictly above `a`, then `‖e^{tM} z‖² ≤ e^{2at} ‖z‖²` for `t ≥ 0`. -/
theorem heatApply_dotProduct_self_le_of_gt {a t : ℝ} (ht : 0 ≤ t)
    (z : V → ℝ)
    (h : ∀ i : V, a < eigvalOf M hM i →
      Matrix.dotProduct (eigvecOf M hM i) z = 0) :
    Matrix.dotProduct (heatApply hM (-t) z) (heatApply hM (-t) z)
      ≤ Real.exp (a * t) * (Real.exp (a * t) * (z ⬝ᵥ z)) := by
  rw [heatApply_dotProduct_self hM (-t) z]
  have hterm : ∀ i : V,
      Real.exp (t * eigvalOf M hM i) * (Real.exp (t * eigvalOf M hM i) *
          (Matrix.dotProduct (eigvecOf M hM i) z *
            Matrix.dotProduct (eigvecOf M hM i) z))
      ≤ Real.exp (a * t) * (Real.exp (a * t) *
          (Matrix.dotProduct (eigvecOf M hM i) z *
            Matrix.dotProduct (eigvecOf M hM i) z)) := by
    intro i
    by_cases hc : a < eigvalOf M hM i
    · rw [h i hc, mul_zero, mul_zero, mul_zero]
      norm_num
    · have hle : eigvalOf M hM i ≤ a := by linarith
      have hcnn : 0 ≤ Matrix.dotProduct (eigvecOf M hM i) z *
          Matrix.dotProduct (eigvecOf M hM i) z := mul_self_nonneg _
      have hexp : Real.exp (t * eigvalOf M hM i) ≤ Real.exp (a * t) :=
        Real.exp_le_exp.2 (by nlinarith [hle, ht])
      exact mul_le_mul hexp (mul_le_mul_of_nonneg_right hexp hcnn)
        (mul_nonneg (Real.exp_nonneg _) hcnn) (Real.exp_nonneg _)
  have hnorm : ∀ i : V, Real.exp (-(-t) * eigvalOf M hM i)
      = Real.exp (t * eigvalOf M hM i) := fun i => by
    rw [show -(-t) * eigvalOf M hM i = t * eigvalOf M hM i from by ring]
  have hpar : z ⬝ᵥ z
      = ∑ i, Matrix.dotProduct (eigvecOf M hM i) z
          * Matrix.dotProduct (eigvecOf M hM i) z :=
    dotProduct_eigvecOf hM z z
  calc ∑ i, Real.exp (-(-t) * eigvalOf M hM i) *
        (Real.exp (-(-t) * eigvalOf M hM i) *
          (Matrix.dotProduct (eigvecOf M hM i) z *
            Matrix.dotProduct (eigvecOf M hM i) z))
      = ∑ i, Real.exp (t * eigvalOf M hM i) *
          (Real.exp (t * eigvalOf M hM i) *
            (Matrix.dotProduct (eigvecOf M hM i) z *
              Matrix.dotProduct (eigvecOf M hM i) z)) :=
        Finset.sum_congr rfl fun i _ => by rw [hnorm i]
    _ ≤ ∑ i, Real.exp (a * t) * (Real.exp (a * t) *
          (Matrix.dotProduct (eigvecOf M hM i) z *
            Matrix.dotProduct (eigvecOf M hM i) z)) :=
        (Finset.sum_le_sum fun i _ => hterm i)
    _ = Real.exp (a * t) * (Real.exp (a * t) * (z ⬝ᵥ z)) := by
        rw [hpar, ← Finset.mul_sum, ← Finset.mul_sum]

end Decay

/-!
## 6. The Duhamel assembly
-/

section Assembly

variable {A : Matrix V V ℝ} (hA : A.IsSymm) {E : Matrix V V ℝ} (hAE : (A + E).IsSymm)

set_option maxHeartbeats 2000000 in
/-- **The Duhamel bound.** For symmetric `A` and symmetric perturbation
`A + E`, with `P` the spectral projector of `A` at threshold `a`, `Q`
the spectral projector of `A + E` at threshold `c'`, and every
eigenvalue of `A + E` strictly above `c'` at least `b > a`:

`‖(1 - Q) * P‖ ≤ ‖E‖ / (b - a)`.

This is the constant-1 operator-norm bound the survey identified as
reachable only through the exponential-integral route. Note `E` itself
need not be symmetric: only the two ends `A` and `A + E` enter
symmetrically. -/
theorem l2OpNorm_one_sub_spectralProjector_mul_spectralProjector_le
    (a c' b : ℝ) (hab : a < b)
    (hcl : ∀ i : V, c' < eigvalOf (A + E) hAE i → b ≤ eigvalOf (A + E) hAE i) :
    ‖(1 - spectralProjector (A + E) hAE c') * spectralProjector A hA a‖
      ≤ ‖E‖ / (b - a) := by
  classical
  have hdnn : ∀ w : V → ℝ, 0 ≤ w ⬝ᵥ w := fun w =>
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hδpos : 0 < b - a := sub_pos.2 hab
  set P := spectralProjector A hA a with hPdef
  set Q := spectralProjector (A + E) hAE c' with hQdef
  have hPsymm : P.IsSymm := spectralProjector_symmetric A hA a
  have hPids : P * P = P := spectralProjector_idempotent A hA a
  have hQsymm : Q.IsSymm := spectralProjector_symmetric (A + E) hAE c'
  have hQids : Q * Q = Q := spectralProjector_idempotent (A + E) hAE c'
  have h1Qsymm : (1 - Q).IsSymm := by
    show (1 - Q)ᵀ = 1 - Q
    rw [Matrix.transpose_sub, Matrix.transpose_one, hQsymm.eq]
  have h1Qid : (1 - Q) * (1 - Q) = 1 - Q := by
    have e1 : (1 - Q) * (1 - Q) = (1 - Q) * 1 - (1 - Q) * Q :=
      Matrix.mul_sub _ _ _
    have e2 : (1 - Q) * 1 = 1 * 1 - Q * 1 := Matrix.sub_mul _ _ _
    have e3 : (1 - Q) * Q = 1 * Q - Q * Q := Matrix.sub_mul _ _ _
    have e4 : 1 * Q = Q := Matrix.one_mul Q
    have e5 : Q * 1 = Q := Matrix.mul_one Q
    rw [e1, e2, e3, e4, e5, hQids, Matrix.one_mul]
    abel
  have h1Qle1 : ‖1 - Q‖ ≤ 1 := l2OpNorm_le_one_of_isSymm_idempotent h1Qsymm h1Qid
  have hPle1 : ‖P‖ ≤ 1 := l2OpNorm_le_one_of_isSymm_idempotent hPsymm hPids
  -- contraction of the projector actions
  have h1Qcontr : ∀ y : V → ℝ,
      ((1 - Q) *ᵥ y) ⬝ᵥ ((1 - Q) *ᵥ y) ≤ y ⬝ᵥ y := by
    intro y
    have hn := dotProduct_mulVec_norm2_le_l2OpNorm_sq (1 - Q) y
    have hNN : ‖1 - Q‖ * ‖1 - Q‖ ≤ 1 :=
      by simpa using mul_le_mul h1Qle1 h1Qle1 (norm_nonneg (1 - Q)) zero_le_one
    have hNY : ‖1 - Q‖ * ‖1 - Q‖ * (y ⬝ᵥ y) ≤ 1 * (y ⬝ᵥ y) :=
      mul_le_mul_of_nonneg_right hNN (hdnn y)
    linarith
  have hPcontr : ∀ x : V → ℝ,
      (P *ᵥ x) ⬝ᵥ (P *ᵥ x) ≤ x ⬝ᵥ x := by
    intro x
    have hn := dotProduct_mulVec_norm2_le_l2OpNorm_sq P x
    have hNN : ‖P‖ * ‖P‖ ≤ 1 :=
      by simpa using mul_le_mul hPle1 hPle1 (norm_nonneg P) zero_le_one
    have hNY : ‖P‖ * ‖P‖ * (x ⬝ᵥ x) ≤ 1 * (x ⬝ᵥ x) :=
      mul_le_mul_of_nonneg_right hNN (hdnn x)
    linarith
  -- eigencomponent annihilation through the projector
  have hAnnE : ∀ i : V, eigvalOf (A + E) hAE i ≤ c' → ∀ y : V → ℝ,
      Matrix.dotProduct (eigvecOf (A + E) hAE i) ((1 - Q) *ᵥ y) = 0 := by
    intro i hi y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.dotProduct_sub,
      dotProduct_eigvecOf_spectralProjector_mulVec hAE c' i y]
    simp [hi]
  have hAnnA : ∀ j : V, a < eigvalOf A hA j → ∀ x : V → ℝ,
      Matrix.dotProduct (eigvecOf A hA j) (P *ᵥ x) = 0 := by
    intro j hj x
    rw [dotProduct_eigvecOf_spectralProjector_mulVec hA a j x]
    exact if_neg (by linarith)
  -- the norm bound through pairings
  refine l2OpNorm_le_of_abs_dotProduct_le
    (div_nonneg (norm_nonneg E) (le_of_lt hδpos)) ?_
  intro x y
  set zy : V → ℝ := (1 - Q) *ᵥ y with hzy
  set zx : V → ℝ := P *ᵥ x with hzx
  set u : ℝ → (V → ℝ) := fun t => heatApply hAE t zy with hu
  set w : ℝ → (V → ℝ) := fun t => heatApply hA (-t) zx with hw
  set g : ℝ → ℝ := fun t => (u t) ⬝ᵥ (w t) with hg
  set gd : ℝ → ℝ := fun t => -((u t) ⬝ᵥ (E *ᵥ w t)) with hgd
  set Sx : ℝ := Real.sqrt (x ⬝ᵥ x) with hSx
  set Sy : ℝ := Real.sqrt (y ⬝ᵥ y) with hSy
  -- the pairing to bound is `g 0`
  have hkey : y ⬝ᵥ (((1 - Q) * P) *ᵥ x) = g 0 := by
    rw [← Matrix.mulVec_mulVec x (1 - Q) P, dotProduct_mulVec_symm h1Qsymm, hg]
    simp only [hu, hw, heatApply_zero, neg_zero, hzy, hzx]
  -- entry derivatives
  have huentry : ∀ (t : ℝ) (c : V),
      HasDerivAt (fun s => u s c) (-(((A + E) *ᵥ u t) c)) t := by
    intro t c
    have h1 := heatApply_hasDerivAt hAE zy c t
    have h2 : (∑ i, -eigvalOf (A + E) hAE i
        * Real.exp (-t * eigvalOf (A + E) hAE i)
        * (Matrix.dotProduct (eigvecOf (A + E) hAE i) zy
          * eigvecOf (A + E) hAE i c))
        + (((A + E) *ᵥ (heatApply hAE t zy)) c) = 0 := by
      rw [heatApply_mulVec hAE t zy c, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => by ring
    have h3 : (∑ i, -eigvalOf (A + E) hAE i
        * Real.exp (-t * eigvalOf (A + E) hAE i)
        * (Matrix.dotProduct (eigvecOf (A + E) hAE i) zy
          * eigvecOf (A + E) hAE i c))
        = -(((A + E) *ᵥ (heatApply hAE t zy)) c) := by linarith
    rw [h3] at h1
    exact h1
  have hwentry : ∀ (t : ℝ) (c : V),
      HasDerivAt (fun s => w s c) (((A *ᵥ w t) c)) t := by
    intro t c
    have h1 := (heatApply_hasDerivAt hA zx c (-t)).comp t ((hasDerivAt_id t).neg)
    have h2 : ((∑ j, -eigvalOf A hA j * Real.exp (-(-t) * eigvalOf A hA j)
        * (Matrix.dotProduct (eigvecOf A hA j) zx
          * eigvecOf A hA j c)) * (-1))
        - ((A *ᵥ (heatApply hA (-t) zx)) c) = 0 := by
      rw [heatApply_mulVec hA (-t) zx c, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_eq_zero fun j _ => by ring
    have h3 : ((∑ j, -eigvalOf A hA j * Real.exp (-(-t) * eigvalOf A hA j)
        * (Matrix.dotProduct (eigvecOf A hA j) zx
          * eigvecOf A hA j c)) * (-1))
        = ((A *ᵥ (heatApply hA (-t) zx)) c) := by linarith
    rw [h3] at h1
    exact h1
  -- the pairing derivative is the Duhamel integrand
  have hgderiv : ∀ t : ℝ, HasDerivAt g (gd t) t := by
    intro t
    have hsum : HasDerivAt (fun s => ∑ c : V, u s c * w s c)
      (∑ c : V, (-(((A + E) *ᵥ u t) c) * w t c + u t c * ((A *ᵥ w t) c))) t :=
      HasDerivAt.sum fun c _ => (huentry t c).mul (hwentry t c)
    have hval : (∑ c : V, (-(((A + E) *ᵥ u t) c) * w t c
        + u t c * ((A *ᵥ w t) c)))
        = -((u t) ⬝ᵥ (E *ᵥ w t)) := by
      have hsplit : (∑ c : V, (u t c * ((A *ᵥ w t) c)
            - (((A + E) *ᵥ u t) c * w t c)))
          = ((∑ c : V, u t c * ((A *ᵥ w t) c))
            - (∑ c : V, (((A + E) *ᵥ u t) c * w t c))) :=
        Finset.sum_sub_distrib
      have hd1 : ((u t) ⬝ᵥ (A *ᵥ w t))
          = ∑ c : V, (u t c * ((A *ᵥ w t) c)) := rfl
      have hd2 : (((A + E) *ᵥ u t) ⬝ᵥ w t)
          = ∑ c : V, (((A + E) *ᵥ u t) c * w t c) := rfl
      have hd3 : ((u t) ⬝ᵥ (E *ᵥ w t))
          = ∑ c : V, (u t c * ((E *ᵥ w t) c)) := rfl
      have hX : (u t) ⬝ᵥ ((A + E) *ᵥ w t) = ((A + E) *ᵥ u t) ⬝ᵥ w t :=
        dotProduct_mulVec_symm hAE _ _
      have hvec : (A *ᵥ w t) - ((A + E) *ᵥ w t) = -(E *ᵥ w t) := by
        rw [Matrix.add_mulVec]
        abel
      calc (∑ c : V, (-(((A + E) *ᵥ u t) c) * w t c
            + u t c * ((A *ᵥ w t) c)))
          = ∑ c : V, (u t c * ((A *ᵥ w t) c)
            - (((A + E) *ᵥ u t) c * w t c)) :=
            Finset.sum_congr rfl fun c _ => by ring
        _ = ((u t) ⬝ᵥ (A *ᵥ w t)) - (((A + E) *ᵥ u t) ⬝ᵥ w t) := by
            rw [hsplit, ← hd1, ← hd2]
        _ = ((u t) ⬝ᵥ (A *ᵥ w t)) - ((u t) ⬝ᵥ ((A + E) *ᵥ w t)) := by
            rw [hX]
        _ = (u t) ⬝ᵥ ((A *ᵥ w t) - ((A + E) *ᵥ w t)) := by
            rw [Matrix.dotProduct_sub]
        _ = (u t) ⬝ᵥ (-(E *ᵥ w t)) := by rw [hvec]
        _ = -((u t) ⬝ᵥ (E *ᵥ w t)) := by rw [Matrix.dotProduct_neg]
    have hg' : HasDerivAt g
      (∑ c : V, (-(((A + E) *ᵥ u t) c) * w t c
        + u t c * ((A *ᵥ w t) c))) t := hsum
    rw [hval] at hg'
    exact hg'
  -- continuity
  have hcu : ∀ c : V, Continuous fun t => u t c := continuous_heatApply hAE zy
  have hcw : ∀ c : V, Continuous fun t => w t c := fun c =>
    (continuous_heatApply hA zx c).comp continuous_neg
  have hcg : Continuous g := by
    refine continuous_finset_sum _ fun c _ => (hcu c).mul (hcw c)
  have hEcont : ∀ c : V, Continuous fun t => (E *ᵥ w t) c := by
    intro c
    show Continuous fun t => ∑ k, E c k * w t k
    exact continuous_finset_sum _ fun k _ => continuous_const.mul (hcw k)
  have hcgd : Continuous gd := by
    have : gd = fun t => -(∑ c : V, u t c * (E *ᵥ w t) c) := rfl
    rw [this]
    exact Continuous.neg (continuous_finset_sum _ fun c _ =>
      (hcu c).mul (hEcont c))
  -- the exponential majorant on the derivative
  have hgdabs : ∀ s : ℝ, 0 ≤ s → |gd s|
      ≤ (‖E‖ * Sx * Sy) * Real.exp (-(b - a) * s) := by
    intro s hs
    have hu_dec : (u s) ⬝ᵥ (u s)
        ≤ Real.exp (-b * s) * (Real.exp (-b * s) * (zy ⬝ᵥ zy)) :=
      heatApply_dotProduct_self_le_of_le hAE hs zy (fun i hi => hAnnE i hi y) hcl
    have hw_dec : (w s) ⬝ᵥ (w s)
        ≤ Real.exp (a * s) * (Real.exp (a * s) * (zx ⬝ᵥ zx)) :=
      heatApply_dotProduct_self_le_of_gt hA hs zx (fun j hj => hAnnA j hj x)
    have hEbound : (E *ᵥ w s) ⬝ᵥ (E *ᵥ w s)
        ≤ ‖E‖ * ‖E‖ * ((w s) ⬝ᵥ (w s)) :=
      dotProduct_mulVec_norm2_le_l2OpNorm_sq E (w s)
    have hZy : zy ⬝ᵥ zy ≤ y ⬝ᵥ y := h1Qcontr y
    have hZx : zx ⬝ᵥ zx ≤ x ⬝ᵥ x := hPcontr x
    have hSx2 : Sx * Sx = x ⬝ᵥ x := Real.mul_self_sqrt (hdnn x)
    have hSy2 : Sy * Sy = y ⬝ᵥ y := Real.mul_self_sqrt (hdnn y)
    have hgdval : |gd s| = |(u s) ⬝ᵥ (E *ᵥ w s)| := by
      show |-((u s) ⬝ᵥ (E *ᵥ w s))| = |(u s) ⬝ᵥ (E *ᵥ w s)|
      rw [abs_neg]
    -- Cauchy-Schwarz, squared
    have hcs := abs_dotProduct_le (u s) (E *ᵥ w s)
    have hp : 0 ≤ Real.sqrt ((u s) ⬝ᵥ (u s))
        * Real.sqrt ((E *ᵥ w s) ⬝ᵥ (E *ᵥ w s)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsq : |(u s) ⬝ᵥ (E *ᵥ w s)| * |(u s) ⬝ᵥ (E *ᵥ w s)|
        ≤ ((u s) ⬝ᵥ (u s)) * ((E *ᵥ w s) ⬝ᵥ (E *ᵥ w s)) := by
      have h1 : |(u s) ⬝ᵥ (E *ᵥ w s)| * |(u s) ⬝ᵥ (E *ᵥ w s)|
          ≤ (Real.sqrt ((u s) ⬝ᵥ (u s))
              * Real.sqrt ((E *ᵥ w s) ⬝ᵥ (E *ᵥ w s)))
            * (Real.sqrt ((u s) ⬝ᵥ (u s))
              * Real.sqrt ((E *ᵥ w s) ⬝ᵥ (E *ᵥ w s))) :=
        mul_le_mul hcs hcs (abs_nonneg _) hp
      nlinarith [h1, Real.mul_self_sqrt (hdnn (u s)),
        Real.mul_self_sqrt (hdnn (E *ᵥ w s)), hp]
    -- explicit multiplication chain
    have heb : 0 ≤ Real.exp (-b * s) := Real.exp_nonneg _
    have hea : 0 ≤ Real.exp (a * s) := Real.exp_nonneg _
    have hebb : 0 ≤ Real.exp (-b * s) * (Real.exp (-b * s) * (zy ⬝ᵥ zy)) :=
      mul_nonneg heb (mul_nonneg heb (hdnn zy))
    have heaa : 0 ≤ Real.exp (a * s) * (Real.exp (a * s) * (zx ⬝ᵥ zx)) :=
      mul_nonneg hea (mul_nonneg hea (hdnn zx))
    have henn : 0 ≤ ‖E‖ * ‖E‖ := mul_nonneg (norm_nonneg E) (norm_nonneg E)
    have c1 : ((u s) ⬝ᵥ (u s)) * ((E *ᵥ w s) ⬝ᵥ (E *ᵥ w s))
        ≤ (Real.exp (-b * s) * (Real.exp (-b * s) * (zy ⬝ᵥ zy)))
          * (‖E‖ * ‖E‖ * ((w s) ⬝ᵥ (w s))) :=
      mul_le_mul hu_dec hEbound (hdnn (E *ᵥ w s)) hebb
    have c2 : (Real.exp (-b * s) * (Real.exp (-b * s) * (zy ⬝ᵥ zy)))
          * (‖E‖ * ‖E‖ * ((w s) ⬝ᵥ (w s)))
        ≤ (Real.exp (-b * s) * (Real.exp (-b * s) * (zy ⬝ᵥ zy)))
          * (‖E‖ * ‖E‖ * (Real.exp (a * s)
            * (Real.exp (a * s) * (zx ⬝ᵥ zx)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hw_dec henn) hebb
    have c3a : Real.exp (a * s) * (Real.exp (a * s) * (zx ⬝ᵥ zx))
        ≤ Real.exp (a * s) * (Real.exp (a * s) * (x ⬝ᵥ x)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hZx hea) hea
    have c3 : (Real.exp (-b * s) * (Real.exp (-b * s) * (zy ⬝ᵥ zy)))
          * (‖E‖ * ‖E‖ * (Real.exp (a * s)
            * (Real.exp (a * s) * (zx ⬝ᵥ zx))))
        ≤ (Real.exp (-b * s) * (Real.exp (-b * s) * (y ⬝ᵥ y)))
          * (‖E‖ * ‖E‖ * (Real.exp (a * s)
            * (Real.exp (a * s) * (x ⬝ᵥ x)))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hZy heb) heb)
        (mul_le_mul_of_nonneg_left c3a henn)
        (mul_nonneg henn heaa)
        (mul_nonneg heb (mul_nonneg heb (hdnn y)))
    have hexpmul : Real.exp (-b * s) * Real.exp (a * s)
        = Real.exp (-(b - a) * s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hring : (Real.exp (-b * s) * (Real.exp (-b * s) * (y ⬝ᵥ y)))
          * (‖E‖ * ‖E‖ * (Real.exp (a * s)
            * (Real.exp (a * s) * (x ⬝ᵥ x))))
        = ((‖E‖ * Sx * Sy) * Real.exp (-(b - a) * s))
          * ((‖E‖ * Sx * Sy) * Real.exp (-(b - a) * s)) := by
      rw [← hSy2, ← hSx2]
      have hring2 : (Real.exp (-b * s) * (Real.exp (-b * s) * (Sy * Sy)))
          * (‖E‖ * ‖E‖ * (Real.exp (a * s)
            * (Real.exp (a * s) * (Sx * Sx))))
          = (‖E‖ * Sx * Sy * (Real.exp (-b * s) * Real.exp (a * s)))
            * (‖E‖ * Sx * Sy * (Real.exp (-b * s) * Real.exp (a * s))) := by
        ring
      rw [hring2, hexpmul]
    have hfinal : |(u s) ⬝ᵥ (E *ᵥ w s)| * |(u s) ⬝ᵥ (E *ᵥ w s)|
        ≤ ((‖E‖ * Sx * Sy) * Real.exp (-(b - a) * s))
          * ((‖E‖ * Sx * Sy) * Real.exp (-(b - a) * s)) :=
      hsq.trans (c1.trans (c2.trans (c3.trans (by rw [hring]))))
    have hnnb : 0 ≤ (‖E‖ * Sx * Sy) * Real.exp (-(b - a) * s) := by
      positivity
    have hpow : ((u s) ⬝ᵥ (E *ᵥ w s)) ^ 2
        ≤ ((‖E‖ * Sx * Sy) * Real.exp (-(b - a) * s)) ^ 2 := by
      rw [pow_two, pow_two, ← abs_mul_abs_self ((u s) ⬝ᵥ (E *ᵥ w s))]
      exact hfinal
    have habs := abs_le_of_sq_le_sq hpow hnnb
    rw [hgdval]
    exact habs
  -- the boundary decay
  have hgTabs : ∀ T : ℝ, 0 ≤ T → |g T|
      ≤ (Sx * Sy) * Real.exp (-(b - a) * T) := by
    intro T hT
    have hu_dec : (u T) ⬝ᵥ (u T)
        ≤ Real.exp (-b * T) * (Real.exp (-b * T) * (zy ⬝ᵥ zy)) :=
      heatApply_dotProduct_self_le_of_le hAE hT zy (fun i hi => hAnnE i hi y) hcl
    have hw_dec : (w T) ⬝ᵥ (w T)
        ≤ Real.exp (a * T) * (Real.exp (a * T) * (zx ⬝ᵥ zx)) :=
      heatApply_dotProduct_self_le_of_gt hA hT zx (fun j hj => hAnnA j hj x)
    have hZy : zy ⬝ᵥ zy ≤ y ⬝ᵥ y := h1Qcontr y
    have hZx : zx ⬝ᵥ zx ≤ x ⬝ᵥ x := hPcontr x
    have hSx2 : Sx * Sx = x ⬝ᵥ x := Real.mul_self_sqrt (hdnn x)
    have hSy2 : Sy * Sy = y ⬝ᵥ y := Real.mul_self_sqrt (hdnn y)
    have hgval : g T = (u T) ⬝ᵥ (w T) := rfl
    rw [hgval]
    have hcs := abs_dotProduct_le (u T) (w T)
    have hp : 0 ≤ Real.sqrt ((u T) ⬝ᵥ (u T))
        * Real.sqrt ((w T) ⬝ᵥ (w T)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsq : |(u T) ⬝ᵥ (w T)| * |(u T) ⬝ᵥ (w T)|
        ≤ ((u T) ⬝ᵥ (u T)) * ((w T) ⬝ᵥ (w T)) := by
      have h1 : |(u T) ⬝ᵥ (w T)| * |(u T) ⬝ᵥ (w T)|
          ≤ (Real.sqrt ((u T) ⬝ᵥ (u T)) * Real.sqrt ((w T) ⬝ᵥ (w T)))
            * (Real.sqrt ((u T) ⬝ᵥ (u T)) * Real.sqrt ((w T) ⬝ᵥ (w T))) :=
        mul_le_mul hcs hcs (abs_nonneg _) hp
      nlinarith [h1, Real.mul_self_sqrt (hdnn (u T)),
        Real.mul_self_sqrt (hdnn (w T)), hp]
    have heb : 0 ≤ Real.exp (-b * T) := Real.exp_nonneg _
    have hea : 0 ≤ Real.exp (a * T) := Real.exp_nonneg _
    have hebb : 0 ≤ Real.exp (-b * T) * (Real.exp (-b * T) * (zy ⬝ᵥ zy)) :=
      mul_nonneg heb (mul_nonneg heb (hdnn zy))
    have heaa : 0 ≤ Real.exp (a * T) * (Real.exp (a * T) * (zx ⬝ᵥ zx)) :=
      mul_nonneg hea (mul_nonneg hea (hdnn zx))
    have c1 : ((u T) ⬝ᵥ (u T)) * ((w T) ⬝ᵥ (w T))
        ≤ (Real.exp (-b * T) * (Real.exp (-b * T) * (zy ⬝ᵥ zy)))
          * (Real.exp (a * T) * (Real.exp (a * T) * (zx ⬝ᵥ zx))) :=
      mul_le_mul hu_dec hw_dec (hdnn (w T)) hebb
    have c2 : (Real.exp (-b * T) * (Real.exp (-b * T) * (zy ⬝ᵥ zy)))
          * (Real.exp (a * T) * (Real.exp (a * T) * (zx ⬝ᵥ zx)))
        ≤ (Real.exp (-b * T) * (Real.exp (-b * T) * (y ⬝ᵥ y)))
          * (Real.exp (a * T) * (Real.exp (a * T) * (x ⬝ᵥ x))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hZy heb) heb)
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hZx hea) hea)
        heaa (mul_nonneg heb (mul_nonneg heb (hdnn y)))
    have hexpmul : Real.exp (-b * T) * Real.exp (a * T)
        = Real.exp (-(b - a) * T) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hring : (Real.exp (-b * T) * (Real.exp (-b * T) * (y ⬝ᵥ y)))
          * (Real.exp (a * T) * (Real.exp (a * T) * (x ⬝ᵥ x)))
        = ((Sx * Sy) * Real.exp (-(b - a) * T))
          * ((Sx * Sy) * Real.exp (-(b - a) * T)) := by
      rw [← hSy2, ← hSx2]
      have hring2 : (Real.exp (-b * T) * (Real.exp (-b * T) * (Sy * Sy)))
          * (Real.exp (a * T) * (Real.exp (a * T) * (Sx * Sx)))
          = (Sx * Sy * (Real.exp (-b * T) * Real.exp (a * T)))
            * (Sx * Sy * (Real.exp (-b * T) * Real.exp (a * T))) := by
        ring
      rw [hring2, hexpmul]
    have hfinal : |(u T) ⬝ᵥ (w T)| * |(u T) ⬝ᵥ (w T)|
        ≤ ((Sx * Sy) * Real.exp (-(b - a) * T))
          * ((Sx * Sy) * Real.exp (-(b - a) * T)) :=
      hsq.trans (c1.trans (c2.trans (by rw [hring])))
    have hnnb : 0 ≤ (Sx * Sy) * Real.exp (-(b - a) * T) := by
      positivity
    have hpow : ((u T) ⬝ᵥ (w T)) ^ 2
        ≤ ((Sx * Sy) * Real.exp (-(b - a) * T)) ^ 2 := by
      rw [pow_two, pow_two, ← abs_mul_abs_self ((u T) ⬝ᵥ (w T))]
      exact hfinal
    exact abs_le_of_sq_le_sq hpow hnnb
  -- the explicit exponential integral
  have hexpint : ∀ T : ℝ, ∫ s in (0)..T, (‖E‖ * Sx * Sy) * Real.exp (-(b - a) * s)
      = (‖E‖ * Sx * Sy) / (b - a) * (1 - Real.exp (-(b - a) * T)) := by
    intro T
    have hF : ∀ t : ℝ, HasDerivAt
        (fun t => -((‖E‖ * Sx * Sy) / (b - a)) * Real.exp (-(b - a) * t))
        ((‖E‖ * Sx * Sy) * Real.exp (-(b - a) * t)) t := by
      intro t
      have h0 : HasDerivAt (fun t => -(b - a) * t) (-(b - a)) t := by
        have h := (hasDerivAt_id t).const_mul (-(b - a))
        simpa using h
      have h1 := (h0.exp).const_mul (-((‖E‖ * Sx * Sy) / (b - a)))
      rw [show -((‖E‖ * Sx * Sy) / (b - a)) * (Real.exp (-(b - a) * t) * (-(b - a)))
          = (‖E‖ * Sx * Sy) * Real.exp (-(b - a) * t) from by
        field_simp
        ring] at h1
      exact h1
    have hcont : Continuous fun s : ℝ =>
        (‖E‖ * Sx * Sy) * Real.exp (-(b - a) * s) := by continuity
    have hint : IntervalIntegrable
        (fun s : ℝ => (‖E‖ * Sx * Sy) * Real.exp (-(b - a) * s))
        MeasureTheory.volume (0 : ℝ) T := hcont.intervalIntegrable (0 : ℝ) T
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t =>
        -((‖E‖ * Sx * Sy) / (b - a)) * Real.exp (-(b - a) * t))
      (f' := fun t => (‖E‖ * Sx * Sy) * Real.exp (-(b - a) * t))
      (fun s _ => hF s) hint]
    have hexp0 : Real.exp (-(b - a) * (0 : ℝ)) = 1 := by
      rw [mul_zero, Real.exp_zero]
    rw [hexp0]
    field_simp
    ring
  -- FTC plus comparison
  have hmain : ∀ T : ℝ, 0 ≤ T → |g 0|
      ≤ |g T| + (‖E‖ * Sx * Sy) / (b - a) := by
    intro T hT
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := g) (f' := gd) (fun s _ => hgderiv s) (hcgd.intervalIntegrable (0 : ℝ) T)
    have hcomp : |∫ s in (0)..T, gd s|
        ≤ (‖E‖ * Sx * Sy) / (b - a) := by
      have hcinner : Continuous fun s : ℝ => -(b - a) * s := by continuity
      have hint2 : IntervalIntegrable
          (fun s : ℝ => (‖E‖ * Sx * Sy) * Real.exp (-(b - a) * s))
          MeasureTheory.volume (0 : ℝ) T :=
        (continuous_const.mul
          (Real.continuous_exp.comp hcinner)).intervalIntegrable (0 : ℝ) T
      have hgdint : IntervalIntegrable (fun s : ℝ => ‖gd s‖)
          MeasureTheory.volume (0 : ℝ) T :=
        hcgd.abs.intervalIntegrable (0 : ℝ) T
      have hmono : (∫ t : ℝ in (0)..T, ‖gd t‖)
          ≤ (∫ t : ℝ in (0)..T, (‖E‖ * Sx * Sy) * Real.exp (-(b - a) * t)) := by
        refine intervalIntegral.integral_mono_on (hf := hgdint) (hg := hint2)
          (hab := hT) ?_
        intro t ht
        have ht0 : 0 ≤ t := ht.1
        show ‖gd t‖ ≤ (‖E‖ * Sx * Sy) * Real.exp (-(b - a) * t)
        rw [Real.norm_eq_abs]
        exact hgdabs t ht0
      have habsint : ‖∫ t : ℝ in (0)..T, gd t‖ ≤ (‖E‖ * Sx * Sy) / (b - a) := by
        refine le_trans (intervalIntegral.norm_integral_le_integral_norm hT)
          (le_trans hmono ?_)
        rw [hexpint T]
        have hle1 : (1 : ℝ) - Real.exp (-(b - a) * T) ≤ 1 := by
          linarith [Real.exp_nonneg (-(b - a) * T)]
        have hnnC : 0 ≤ (‖E‖ * Sx * Sy) / (b - a) :=
          div_nonneg (mul_nonneg (mul_nonneg (norm_nonneg E)
            (Real.sqrt_nonneg (x ⬝ᵥ x))) (Real.sqrt_nonneg (y ⬝ᵥ y)))
            (le_of_lt hδpos)
        nlinarith [hle1, hnnC]
      rw [Real.norm_eq_abs] at habsint
      exact habsint
    have habs : |g 0| ≤ |g T| + |∫ s in (0)..T, gd s| := by
      have hg0 : g 0 = g T - ∫ s in (0)..T, gd s := by
        rw [hint]
        ring
      rw [hg0]
      exact abs_sub _ _
    linarith [habs, hcomp]
  -- the boundary term dies at infinity
  have hlim : Filter.Tendsto (fun T : ℝ => |g T|) Filter.atTop (nhds 0) := by
    have hexp : Filter.Tendsto (fun T : ℝ => Real.exp (-(b - a) * T))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun T : ℝ => (b - a) * T) Filter.atTop Filter.atTop :=
        (Filter.tendsto_const_mul_atTop_of_pos hδpos).mpr Filter.tendsto_id
      have he : (fun T : ℝ => Real.exp (-(b - a) * T))
          = fun T : ℝ => (Real.exp ((b - a) * T))⁻¹ := funext fun T => by
        have h := Real.exp_neg ((b - a) * T)
        rw [show -(b - a) * T = -((b - a) * T) from by ring, h]
      rw [he]
      exact tendsto_inv_atTop_zero.comp (Real.tendsto_exp_atTop.comp h1)
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hto0 : ∀ᶠ T in Filter.atTop,
        (Sx * Sy) * Real.exp (-(b - a) * T) < ε := by
      have hc : Filter.Tendsto (fun _ : ℝ => Sx * Sy) Filter.atTop
          (nhds (Sx * Sy)) := tendsto_const_nhds
      have h2 := (Metric.tendsto_nhds.mp
        (by simpa using hc.mul hexp)) ε hε
      have hSxnn : 0 ≤ Sx := Real.sqrt_nonneg (x ⬝ᵥ x)
      have hSynn : 0 ≤ Sy := Real.sqrt_nonneg (y ⬝ᵥ y)
      filter_upwards [h2] with T h2'
      have hconv : Real.exp (-(b - a) * T) = Real.exp ((a - b) * T) := by
        congr 1
        ring
      have hd : dist (Sx * Sy * Real.exp ((a - b) * T)) (0 : ℝ)
          = Sx * Sy * Real.exp ((a - b) * T) := by
        rw [Real.dist_eq, sub_zero]
        exact abs_of_nonneg (by positivity)
      rw [hd] at h2'
      rw [hconv]
      exact h2'
    have hb : ∀ᶠ T in Filter.atTop,
        |g T| ≤ (Sx * Sy) * Real.exp (-(b - a) * T) :=
      (Filter.eventually_ge_atTop (0 : ℝ)).mono fun T hT => hgTabs T hT
    filter_upwards [hto0, hb] with T h1 h2
    have hdist : dist (|g T|) (0 : ℝ) = |g T| := by simp [Real.dist_eq]
    rw [hdist]
    exact lt_of_le_of_lt h2 h1
  -- conclude
  have hfinalbound : |g 0| ≤ (‖E‖ * Sx * Sy) / (b - a) := by
    rcases le_or_gt |g 0| ((‖E‖ * Sx * Sy) / (b - a)) with hle | hlt
    · exact hle
    · exfalso
      have hev : ∀ᶠ T in Filter.atTop,
          |g T| < |g 0| - (‖E‖ * Sx * Sy) / (b - a) := by
        have h2 := (Metric.tendsto_nhds.mp hlim)
          (|g 0| - (‖E‖ * Sx * Sy) / (b - a)) (by linarith)
        have h3 : ∀ T : ℝ, dist (|g T|) (0 : ℝ) = |g T| := fun T => by
          rw [Real.dist_eq, sub_zero, abs_abs]
        simp only [h3] at h2
        exact h2
      obtain ⟨T, hT⟩ := (hev.and (Filter.eventually_ge_atTop (0 : ℝ))).exists
      have hTpos : 0 ≤ T := hT.2
      have hmainT := hmain T hTpos
      have hTg : |g T| < |g 0| - (‖E‖ * Sx * Sy) / (b - a) := hT.1
      linarith
  calc |y ⬝ᵥ (((1 - Q) * P) *ᵥ x)| = |g 0| := by rw [hkey]
    _ ≤ (‖E‖ * Sx * Sy) / (b - a) := hfinalbound
    _ = ‖E‖ / (b - a) * Sx * Sy := by ring

end Assembly

/-!
## 7. Rank of a spectral projector
-/

section Rank

/-- The rank of a spectral projector is the number of eigenbasis
vectors at or below the threshold: the projector's columns span exactly
the filtered eigenbasis (each column is a combination of the filtered
eigenvectors, and each filtered eigenvector is fixed by — hence a
combination of — the projector's columns). -/
theorem rank_spectralProjector_eq_card_filter {M : Matrix V V ℝ}
    (hM : M.IsSymm) (c : ℝ) :
    (spectralProjector M hM c).rank =
      (Finset.univ.filter fun i => eigvalOf M hM i ≤ c).card := by
  classical
  set F := Finset.univ.filter fun i => eigvalOf M hM i ≤ c with hF
  have hcol : ∀ j : V, (spectralProjector M hM c)ᵀ j
      = ∑ i ∈ F, (eigvecOf M hM i j) • (eigvecOf M hM i) := by
    intro j
    funext a
    simp only [Matrix.transpose_apply, spectralProjector, Matrix.of_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsub1 : Submodule.span ℝ (Set.range ((spectralProjector M hM c)ᵀ))
      ≤ Submodule.span ℝ
        (Set.range fun i : {x // x ∈ F} => eigvecOf M hM i.1) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [hcol j]
    refine Submodule.sum_mem _ fun i hi => ?_
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
  have hsub2 : Submodule.span ℝ
        (Set.range fun i : {x // x ∈ F} => eigvecOf M hM i.1)
      ≤ Submodule.span ℝ (Set.range ((spectralProjector M hM c)ᵀ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, hi⟩, rfl⟩
    show eigvecOf M hM i ∈ _
    have hic : eigvalOf M hM i ≤ c := by
      rw [hF] at hi
      simpa using (Finset.mem_filter.1 hi).2
    have hfix : spectralProjector M hM c *ᵥ eigvecOf M hM i
        = eigvecOf M hM i := spectralProjector_mulVec_eigvecOf_self M hM c i hic
    have hexp : eigvecOf M hM i
        = ∑ j : V, (eigvecOf M hM i j) • ((spectralProjector M hM c)ᵀ j) := by
      funext a
      calc eigvecOf M hM i a
          = (spectralProjector M hM c *ᵥ eigvecOf M hM i) a := by rw [hfix]
        _ = ∑ j : V, (spectralProjector M hM c) a j
            * eigvecOf M hM i j := rfl
        _ = ∑ j : V, eigvecOf M hM i j
            * (spectralProjector M hM c)ᵀ j a := by
            simp only [Matrix.transpose_apply]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = (∑ j : V, (eigvecOf M hM i j)
            • ((spectralProjector M hM c)ᵀ j)) a := by
            rw [Finset.sum_apply]
            simp only [Pi.smul_apply, smul_eq_mul]
    rw [hexp]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  rw [Matrix.rank_eq_finrank_span_cols]
  have heq : Submodule.span ℝ (Set.range ((spectralProjector M hM c)ᵀ))
      = Submodule.span ℝ
        (Set.range fun i : {x // x ∈ F} => eigvecOf M hM i.1) :=
    le_antisymm hsub1 hsub2
  rw [heq, finrank_span_eigvecOf_finset hM F]

/-- **No-tie rank pin.** When the `k`-th sorted eigenvalue is strictly
below the `k+1`-st (no tie at the threshold), the spectral projector at
`evals hM k` has rank exactly `k + 1` — the two public count pins
bracket the filter from both sides. -/
theorem rank_spectralProjector_evals_of_lt {M : Matrix V V ℝ} (hM : M.IsSymm)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (h : evals hM ⟨(k : ℕ), k.isLt⟩ < evals hM ⟨(k : ℕ) + 1, hk⟩) :
    (spectralProjector M hM (evals hM ⟨(k : ℕ), k.isLt⟩)).rank
      = (k : ℕ) + 1 := by
  rw [rank_spectralProjector_eq_card_filter]
  refine Nat.le_antisymm ?_ (succ_le_card_filter_eigvalOf_le hM _)
  have hsub : (Finset.univ.filter fun i => eigvalOf M hM i
      ≤ evals hM ⟨(k : ℕ), k.isLt⟩) ⊆
      Finset.univ.filter fun i => eigvalOf M hM i
        < evals hM ⟨(k : ℕ) + 1, hk⟩ := by
    intro i hi
    refine Finset.mem_filter.2 ⟨Finset.mem_univ i, ?_⟩
    exact lt_of_le_of_lt (Finset.mem_filter.1 hi).2 h
  calc (Finset.univ.filter fun i => eigvalOf M hM i
        ≤ evals hM ⟨(k : ℕ), k.isLt⟩).card
      ≤ (Finset.univ.filter fun i => eigvalOf M hM i
          < evals hM ⟨(k : ℕ) + 1, hk⟩).card := Finset.card_le_card hsub
    _ ≤ (k : ℕ) + 1 := card_filter_eigvalOf_lt_evals_le hM ⟨(k : ℕ) + 1, hk⟩

end Rank

/-!
## 8. The trivial endpoint of the gap metric
-/

section One

/-- Two orthogonal projectors are at distance at most `1` (the trivial
endpoint of the gap metric). Load-bearing for the tie cases of the
Davis–Kahan retirement: when either spectrum is tied at its threshold,
the separation hypothesis plus Weyl force `δ ≤ ‖E‖`, and this bound
finishes `‖P − Q‖ ≤ 1 ≤ ‖E‖ / δ` without Duhamel. -/
theorem l2OpNorm_sub_le_one_of_isSymm_idempotent {P Q : Matrix V V ℝ}
    (hP : P.IsSymm) (hPP : P * P = P)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) :
    ‖P - Q‖ ≤ 1 := by
  have h1Q : (1 - Q).IsSymm := by
    show (1 - Q)ᵀ = 1 - Q
    rw [Matrix.transpose_sub, Matrix.transpose_one, hQ.eq]
  have h1Pid : (1 - P) * (1 - P) = 1 - P := by
    have e1 : (1 - P) * (1 - P) = (1 - P) * 1 - (1 - P) * P :=
      Matrix.mul_sub _ _ _
    have e2 : (1 - P) * 1 = 1 * 1 - P * 1 := Matrix.sub_mul _ _ _
    have e3 : (1 - P) * P = 1 * P - P * P := Matrix.sub_mul _ _ _
    have e4 : 1 * P = P := Matrix.one_mul P
    have e5 : P * 1 = P := Matrix.mul_one P
    rw [e1, e2, e3, e4, e5, hPP, Matrix.one_mul]
    abel
  have h1Qid : (1 - Q) * (1 - Q) = 1 - Q := by
    have e1 : (1 - Q) * (1 - Q) = (1 - Q) * 1 - (1 - Q) * Q :=
      Matrix.mul_sub _ _ _
    have e2 : (1 - Q) * 1 = 1 * 1 - Q * 1 := Matrix.sub_mul _ _ _
    have e3 : (1 - Q) * Q = 1 * Q - Q * Q := Matrix.sub_mul _ _ _
    have e4 : 1 * Q = Q := Matrix.one_mul Q
    have e5 : Q * 1 = Q := Matrix.mul_one Q
    rw [e1, e2, e3, e4, e5, hQQ, Matrix.one_mul]
    abel
  have h1P : (1 - P).IsSymm := by
    show (1 - P)ᵀ = 1 - P
    rw [Matrix.transpose_sub, Matrix.transpose_one, hP.eq]
  have h1Qle : ‖1 - Q‖ ≤ 1 := l2OpNorm_le_one_of_isSymm_idempotent h1Q h1Qid
  have h1Ple : ‖1 - P‖ ≤ 1 := l2OpNorm_le_one_of_isSymm_idempotent h1P h1Pid
  have hPle : ‖P‖ ≤ 1 := l2OpNorm_le_one_of_isSymm_idempotent hP hPP
  have hQle : ‖Q‖ ≤ 1 := l2OpNorm_le_one_of_isSymm_idempotent hQ hQQ
  rw [l2OpNorm_sub_eq_max_of_isSymm_idempotent hP hPP hQ hQQ]
  refine max_le ?_ ?_
  · exact le_trans (norm_mul_le (1 - Q) P)
      (by simpa using mul_le_mul h1Qle hPle (norm_nonneg P) zero_le_one)
  · exact le_trans (norm_mul_le (1 - P) Q)
      (by simpa using mul_le_mul h1Ple hQle (norm_nonneg Q) zero_le_one)

end One

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation
