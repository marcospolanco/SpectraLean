/-
  Cheeger_QA.lean

  Purpose
  -------
  QA lemmas for the Cheeger inequality interface of
  `Scaffold.Mathlib.GraphTheory.Cheeger`: structural conductance facts
  proved from the definitions, and coherence checks that derive
  consequences from the two admitted bounds.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not
  prove the Cheeger axioms; it checks that their interfaces compose.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Cheeger

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Structural conductance facts (proved)
-/

/-- The boundary of `S` equals the boundary of its complement for
symmetric weights. -/
theorem boundary_complement_QA (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (S : Finset V) :
    boundary A Sᶜ = boundary A S := by
  show (∑ i in Sᶜ, ∑ j in Sᶜᶜ, A i j) = ∑ i in S, ∑ j in Sᶜ, A i j
  rw [compl_compl, Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    rw [hA.apply y x]

/-- The boundary of `S` is at most the volume of `S`. -/
theorem boundary_le_vol_QA (A : WAdj (V := V)) (hnonneg : ∀ i j, 0 ≤ A i j)
    (S : Finset V) :
    boundary A S ≤ vol A S := by
  have h : ∀ i : V, (∑ j in Sᶜ, A i j) ≤ deg A i := by
    intro i
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun j _ _ => hnonneg i j
  show (∑ i in S, ∑ j in Sᶜ, A i j) ≤ vol A S
  exact Finset.sum_le_sum fun i _ => h i

/-- The boundary is bounded by both volumes, hence by their minimum. -/
theorem boundary_le_min_vol_QA (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (S : Finset V) :
    boundary A S ≤ min (vol A S) (vol A Sᶜ) := by
  refine le_min_iff.mpr ⟨boundary_le_vol_QA A hnonneg S, ?_⟩
  rw [← boundary_complement_QA A hA S]
  exact boundary_le_vol_QA A hnonneg Sᶜ

/-- Conductance is bounded by one for symmetric nonnegative weights. In
the zero-volume case the conductance evaluates to the junk value
`0 / 0 = 0`, still at most one. -/
theorem conductance_le_one_QA (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (S : Finset V) :
    conductance A S ≤ 1 := by
  rcases lt_or_le 0 (min (vol A S) (vol A Sᶜ)) with hpos | hnpos
  · rw [conductance]
    exact (div_le_one hpos).mpr (boundary_le_min_vol_QA A hA hnonneg S)
  · have h0min : 0 ≤ min (vol A S) (vol A Sᶜ) :=
      le_min_iff.mpr ⟨vol_nonneg A hnonneg S, vol_nonneg A hnonneg Sᶜ⟩
    have hmin : min (vol A S) (vol A Sᶜ) = 0 := le_antisymm hnpos h0min
    have hbd : boundary A S = 0 :=
      le_antisymm (le_trans (boundary_le_min_vol_QA A hA hnonneg S)
        (hmin ▸ le_refl _)) (boundary_nonneg A hnonneg S)
    rw [conductance, hbd, hmin, div_zero]
    exact zero_le_one

/-- The Cheeger constant is at most one whenever a nonempty proper
subset exists (in particular for at least two vertices). -/
theorem cheegerConstant_le_one_QA (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (S : Finset V)
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    cheegerConstant A ≤ 1 :=
  le_trans (conductance_ge_cheegerConstant A hnonneg S hS hSc)
    (conductance_le_one_QA A hA hnonneg S)

/-!
## Coherence of the admitted Cheeger bounds
-/

/-- A positive Cheeger constant forces a positive second eigenvalue of
the regular normalized Laplacian, derived from the admitted lower
bound. (Conditional on the axiom; this is an interface consequence,
not a proof of the axiom.) -/
theorem cheeger_positive_implies_lambda2_pos_QA (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j)
    (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d)
    (hcard : 2 ≤ Fintype.card V) (hpos : 0 < cheegerConstant A) :
    0 < lambda2 (regularNormalizedLaplacian A d)
      (regularNormalizedLaplacian_symmetric A hA d) hcard := by
  have h := cheeger_lower_bound A hA hnonneg d hd hdpos hcard
  calc 0 < (cheegerConstant A) ^ 2 / 2 :=
        div_pos (sq_pos_of_pos hpos) (by norm_num)
    _ ≤ lambda2 (regularNormalizedLaplacian A d)
        (regularNormalizedLaplacian_symmetric A hA d) hcard := h

/-- The two admitted Cheeger bounds are mutually coherent: the squared
constant is controlled by `λ₂` and `λ₂` by twice the constant, for the
same matrix, regularity data, and Cheeger constant. -/
theorem cheeger_bounds_coherent_QA (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j)
    (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d)
    (hcard : 2 ≤ Fintype.card V) :
    (cheegerConstant A) ^ 2 / 2 ≤
        lambda2 (regularNormalizedLaplacian A d)
          (regularNormalizedLaplacian_symmetric A hA d) hcard ∧
      lambda2 (regularNormalizedLaplacian A d)
          (regularNormalizedLaplacian_symmetric A hA d) hcard ≤
        2 * cheegerConstant A :=
  ⟨cheeger_lower_bound A hA hnonneg d hd hdpos hcard,
    cheeger_upper_bound A hA hnonneg d hd hdpos hcard⟩

end SpectralGraphTheory.QA
