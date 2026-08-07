/-
  Dynamics_QA.lean

  Purpose
  -------
  QA lemmas for event-driven spectral graph theory.

  These verify basic properties of event updates and spectral persistence
  that should follow immediately from the axioms.

  Compilation Status: 📋 TODO
  -------------------------------
  Import fixed to use `spectral.lean`.
  Next: Verify compilation with `lake build` (waiting for mathlib download).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## QA 1: Event update is a small perturbation

Verify that changing one edge weight is a small perturbation in the
operator norm sense, for bounded weight changes.
-/


/-!
## QA 2: Event update preserves zero diagonal

Verify that event updates don't introduce self-loops (diagonal entries remain zero).
-/

theorem eventUpdate_preserves_zero_diagonal_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hzero : ∀ i, A i i = 0)
  (u v : V) (w : ℝ) (huv : u ≠ v) :
  ∀ i, (eventUpdate A u v w) i i = 0 := by
  intro i
  rw [eventUpdate]
  by_cases h : i = u ∧ i = v
  · have h' : u = v := by
      have : i = u := h.left
      have : i = v := h.right
      rw [this]
      exact this.symm
    contradiction
  · by_cases h2 : i = v ∧ i = u
    · have h' : v = u := by
        have : i = v := h2.left
        have : i = u := h2.right
        rw [this]
        exact this.symm
      contradiction
    · apply hzero

/-!
## QA 3: Multiple event updates compose

Verify that applying multiple event updates is equivalent to
applying them in sequence.
-/

theorem eventUpdate_compose_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (u₁ v₁ u₂ v₂ : V) (w₁ w₂ : ℝ) :
  eventUpdate (eventUpdate A u₁ v₁ w₁) u₂ v₂ w₂ =
  eventUpdate (eventUpdate A u₂ v₂ w₂) u₁ v₁ w₁ := by
  ext i j
  rw [eventUpdate, eventUpdate, eventUpdate, eventUpdate]
  by_cases h1 : i = u₁ ∧ j = v₁
  · by_cases h2 : i = u₂ ∧ j = v₂
    · simp [h1, h2]
    · simp [h1, h2]
  · by_cases h2 : i = u₂ ∧ j = v₂
    · simp [h1, h2]
    · by_cases h3 : i = v₁ ∧ j = u₁
      · by_cases h4 : i = v₂ ∧ j = u₂
        · simp [h3, h4]
      · simp [h3, h4]
      · by_cases h4 : i = v₂ ∧ j = u₂
        · simp [h3, h4]
        · simp [h1, h2, h3, h4]
      · simp [h1, h2, h3]
    · by_cases h3 : i = v₁ ∧ j = u₁
      · by_cases h4 : i = v₂ ∧ j = u₂
        · simp [h3, h4]
      · simp [h3, h4]
      · by_cases h4 : i = v₂ ∧ j = u₂
        · simp [h3, h4]
        · simp [h1, h2, h3, h4]
      · simp [h1, h2, h3]
    · simp [h1, h2]

/-!
## QA 4: Laplacian change under event update

Verify how the Laplacian changes when a single edge weight is modified.
-/

theorem laplacian_eventUpdate_change_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (u v : V) (w : ℝ) :
  laplacian (eventUpdate A u v w) - laplacian A =
    fun i j =>
      if (i = u ∧ j = u) then w - A u v
      else if (i = v ∧ j = v) then w - A u v
      else if (i = u ∧ j = v) then -(w - A u v)
      else if (i = v ∧ j = u) then -(w - A u v)
      else 0 := by
  ext i j
  simp only [laplacian, degreeMatrix, eventUpdate, Pi.sub_apply]
  by_cases h1 : i = j
  · by_cases h2 : i = u
    · by_cases h3 : j = v
      · simp [h1, h2, h3]
      · simp [h1, h2, h3]
    · by_cases h3 : i = v
      · simp [h1, h2, h3]
      · simp [h1, h2, h3]
  · by_cases h2 : i = u ∧ j = v
    · simp [h1, h2]
    · by_cases h3 : i = v ∧ j = u
      · simp [h1, h3]
      · simp [h1, h2, h3]


/-!
## QA 6: Small edge weight change preserves connectivity

Verify that small changes to edge weights don't disconnect the graph
(stability of zero eigenvalue multiplicity).
-/


end SpectralGraphTheory.QA
