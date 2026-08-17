/-
  Dynamics_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.Dynamics`: the event-driven
  evolution predicate, the spectral projector definitions, and the
  zero-perturbation instance of the admitted persistence principle.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not
  prove the persistence axiom; the zero-event lemma checks its interface.

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

/-!
## Zero-perturbation instance of the admitted persistence principle
-/

set_option linter.deprecated false in
/-- With no events (`ε = 0`) and a persistent positive gap, the admitted
persistence principle forces the projector to be exactly constant along
the evolution. This is an interface consequence of the axiom
`spectral_persistence`, not a proof of it.

The axiom is deprecated (2026-08-17; see its migration note) and this
lemma deliberately continues to exercise the compatibility surface, so
the deprecation linter is silenced for this use only. -/
theorem persistence_zero_perturbation_QA
    (A : TimeVaryingGraph V) (k : Fin (Fintype.card V))
    (hk : (k : ℕ) + 1 < Fintype.card V) (γ : ℝ) (hγ : 0 < γ)
    (hsymm : ∀ t, (A t).IsSymm)
    (hstill : IsEventDriven A 0)
    (hgap : ∀ t, spectralGap (laplacianSequence A t)
      (laplacianSequence_symmetric A hsymm t) k hk ≥ γ) :
    ∀ t, initialProjector (laplacianSequence A (t + 1))
        (laplacianSequence_symmetric A hsymm (t + 1)) k
      = initialProjector (laplacianSequence A t)
        (laplacianSequence_symmetric A hsymm t) k := by
  intro t
  have h := spectral_persistence A k hk 0 γ hγ hsymm hstill hgap t
  rw [zero_div] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

end SpectralGraphTheory.QA
