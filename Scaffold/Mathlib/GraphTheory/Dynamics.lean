/-
  Dynamics.lean

  Purpose
  -------
  Event-driven graph dynamics: time-varying weighted graphs, bounded
  per-step Laplacian perturbations, and real spectral gaps — building
  blocks consumed by `Scaffold.Derived.EventStream` and
  `Scaffold.Derived.ProjectorDrift`.
-/

import Scaffold.Mathlib.GraphTheory.Spectral
import Mathlib.Analysis.CStarAlgebra.Matrix

open scoped BigOperators Matrix Matrix.L2OpNorm

namespace SpectralGraphTheory

/-!
## 1. Time-varying graphs and event streams
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A time-varying weighted graph: a sequence of adjacency matrices. -/
def TimeVaryingGraph (V : Type) [Fintype V] [DecidableEq V] :=
  ℕ → Matrix V V ℝ

/-- The Laplacian sequence of a time-varying graph. -/
def laplacianSequence (A : TimeVaryingGraph V) (t : ℕ) : Matrix V V ℝ :=
  laplacian (A t)

/-- Event-driven evolution: between consecutive times the Laplacian moves
by at most `ε` in the ℓ² operator norm (`Matrix.L2OpNorm`). -/
def IsEventDriven (A : TimeVaryingGraph V) (ε : ℝ) : Prop :=
  ∀ t, ‖laplacianSequence A (t + 1) - laplacianSequence A t‖ ≤ ε

/-- An event-driven graph evolves through symmetric adjacency matrices;
the Laplacian sequence is then symmetric at every time. -/
theorem laplacianSequence_symmetric (A : TimeVaryingGraph V)
    (hsymm : ∀ t, (A t).IsSymm) (t : ℕ) :
    (laplacianSequence A t).IsSymm :=
  laplacian_symmetric (A t) (hsymm t)

/-!
## 2. Spectral projectors

The projector definitions (`spectralProjector`, `initialProjector`) live
in the SGT center `Scaffold.Mathlib.GraphTheory.Spectral`, because the
Davis–Kahan perturbation bridge consumes them as well.
-/

end SpectralGraphTheory
