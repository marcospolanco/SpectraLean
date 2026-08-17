/-
  Cheeger_QA.lean

  Purpose
  -------
  QA lemmas for Cheeger inequalities and related properties.

  These verify basic consequences of Cheeger bounds that should
  follow immediately from the axioms.

  Compilation Status: 📋 TODO
  -------------------------------
  Imports the canonical `Scaffold.Mathlib.GraphTheory.Spectral` module.
  Next: Verify compilation with `lake build` (waiting for mathlib download).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## QA 1: Cheeger constant is bounded by 1

Verify that the Cheeger constant cannot exceed 1 for any graph.
-/

theorem cheegerConstant_le_one_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (hnonneg : ∀ i j, 0 ≤ A i j) :
  cheegerConstant A ≤ 1 := by
  -- Conductance φ(S) = boundary(S) / max(vol(S), vol(Sᶜ))
  -- Since boundary(S) ≤ vol(S) (each vertex in S contributes at most its degree)
  -- we have φ(S) ≤ 1 for all S, so h(G) = inf φ(S) ≤ 1
  unfold cheegerConstant
  apply le_cInf_i18n
  · intro S
      rw [conductance]
      apply div_le_one_of_le (boundary_nonneg A hnonneg S)
      · apply Real.max_le.mpr
        · have : vol A S ≤ boundary A S + vol A Sᶜ := by
            unfold vol boundary
            apply Finset.sum_le_sum
            intro i _\            have : deg A i = ∑ j, A i j := rfl
            rw [this]\            apply Finset.sum_le_sum_of_subset
            · intro j _\              simp only [Finset.mem_compl, Finset.mem_union]
              intro h'
              cases h'
              · assumption
              · contradiction
            · simp
          · linarith
        · exact vol_nonneg A hnonneg S
      · apply le_max (vol A S) (vol A Sᶜ)
  · apply le_max (vol A ∅) (vol A (Finset.univ : Finset V))
    · exact vol_nonneg A hnonneg (Finset.univ : Finset V)

/-!
## QA 2: Cheeger upper bound implies connectivity

Verify that positive Cheeger constant implies the graph is connected
(i.e., λ₂ > 0).
-/

theorem cheeger_positive_implies_connected_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (hnonneg : ∀ i j, 0 ≤ A i j)
  (hpos : 0 < cheegerConstant A) :
  0 < lambda2 A := by
  -- By Cheeger lower bound: λ₂ ≥ h(G)²/2
  -- If h(G) > 0, then λ₂ > 0
  have h := SpectralGraphTheory.cheeger_lower_bound A hA
  have h_nonneg := h.left
  have h_lower := h.right
  calc
    0 < (cheegerConstant A) ^ 2 / 2 := by
      apply div_pos
      · apply sq_pos_of_pos
        exact hpos
      · norm_num
    _ ≤ lambda2 A := by
      exact h_lower

/-!
## QA 3: Complete graph has Cheeger constant 1/2

Verify that for a complete graph on n vertices, h(G) = 1/2.
-/


/-!
## QA 4: Regular graph conductance

Verify that for a d-regular graph, conductance can be expressed
in terms of the degree d.
-/


/-!
## QA 5: Cheeger bound monotonicity

Verify that the Cheeger constant is monotonic with respect to
adding edges (increasing weights).
-/


/-!
## QA 6: Disconnected graph has zero Cheeger constant

Verify that if a graph is disconnected (has multiple components),
its Cheeger constant is 0.
-/

theorem cheegerConstant_disconnected_zero_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (hnonneg : ∀ i j, 0 ≤ A i j)
  (hdisconnected : ∃ S : Finset V, 0 < S.card ∧ S.card < Fintype.card V ∧ boundary A S = 0) :
  cheegerConstant A = 0 := by
  -- If there's a nonempty proper subset S with boundary(S) = 0,
  -- then conductance(S) = 0 / max(vol(S), vol(Sᶜ)) = 0
  -- So h(G) = inf conductance = 0
  unfold cheegerConstant
  cases hdisconnected with
  | intro S hS =>
      have h_nonneg : 0 ≤ cheegerConstant A := by
        apply SpectralGraphTheory.QA.cheegerConstant_nonneg A hA hnonneg
      apply le_antisymm _ h_nonneg
      · apply le_cInf
        · intro t ht
          cases ht with
          | intro ht1 ht2 =>
              rw [← ht1]
              rw [conductance]
              have : boundary A S = 0 := hS.2.2
              rw [this]
              apply div_zero
        · apply le_max (vol A ∅) (vol A (Finset.univ : Finset V))
          · exact vol_nonneg A hnonneg (Finset.univ : Finset V)

end SpectralGraphTheory.QA
