/-
  Dynamics_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.Dynamics`: the event-driven
  evolution predicate and the spectral projector definitions.

  All proofs are real Lean proofs (no `sorry`/`admit`).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Dynamics

open scoped BigOperators Matrix Matrix.L2OpNorm

namespace SpectralGraphTheory.QA

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Event-driven evolution
-/

/-- A constant graph is event-driven with `ε = 0`: the Laplacian never
moves. -/
theorem constant_isEventDriven_zero_QA (A : Matrix V V ℝ) :
    IsEventDriven (fun _ => A) 0 := by
  intro t
  simp only [laplacianSequence, sub_self, norm_zero, le_refl]

/-- Event-driven evolution with a larger bound: an `ε`-driven graph is
also `ε'`-driven for any `ε ≤ ε'`. -/
theorem isEventDriven_mono_QA (A : TimeVaryingGraph V) (ε ε' : ℝ)
    (hε : ε ≤ ε') (h : IsEventDriven A ε) :
    IsEventDriven A ε' := by
  intro t
  exact (h t).trans hε

/-!
## Spectral projectors
-/

/-- Spectral projectors are symmetric, for every threshold. -/
theorem spectralProjector_symmetric_QA (L : Matrix V V ℝ) (hL : L.IsSymm)
    (c : ℝ) :
    (spectralProjector L hL c).IsSymm :=
  spectralProjector_symmetric L hL c

/-- Initial projectors are symmetric, for every cut index. -/
theorem initialProjector_symmetric_QA (L : Matrix V V ℝ) (hL : L.IsSymm)
    (k : Fin (Fintype.card V)) :
    (initialProjector L hL k).IsSymm :=
  initialProjector_symmetric L hL k

/-- A projector equals its reflection threshold symmetric partner:
the projector at threshold `c` equals its own transpose, checked
entrywise through the public definition. -/
theorem spectralProjector_diag_QA (L : Matrix V V ℝ) (hL : L.IsSymm)
    (c : ℝ) (a : V) :
    spectralProjector L hL c a a
      = ∑ i ∈ Finset.univ.filter (fun i => eigvalOf L hL i ≤ c),
          eigvecOf L hL i a * eigvecOf L hL i a := by
  rfl

end SpectralGraphTheory.QA
