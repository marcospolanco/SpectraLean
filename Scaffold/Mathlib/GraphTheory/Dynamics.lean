/-
  Dynamics.lean

  Purpose
  -------
  Event-driven spectral dynamics: time-varying weighted graphs, bounded
  per-step Laplacian perturbations, real spectral gaps, real spectral
  projectors built from the orthonormal eigenbasis of the spectral
  theorem, and the admitted (cited) subspace-persistence principle.

  The persistence statement is the dynamic frontier of Scaffold's SGT
  center; its per-step engine is the Davis–Kahan theorem admitted in
  `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan`.

  Source:
  - Davis, C. & Kahan, W. M., "The rotation of eigenvectors by a
    perturbation", SIAM J. Numer. Anal. 7(1):1–46, 1970.
  - Yu, Y., Wang, T., Samworth, R. J., "A useful variant of the
    Davis–Kahan theorem for statisticians", Annals of Statistics
    43(3):2028–2061, 2015 (two-sided gap projector form, constant 1).
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
/-!
## 3. The persistence principle (admitted)

One-step stability of an invariant spectral subspace under bounded,
gap-separated event streams. This is the dynamic-SGT frontier claim; its
classical engine is Davis–Kahan.
-/

/-- Event-driven spectral persistence: if every step perturbs the
Laplacian by at most `ε` in operator norm, and the spectral gap at index
`k` stays at least `γ` along the whole evolution, then the invariant
subspace projector rotates by at most `ε / γ` per step.

Source:
- Davis, C. & Kahan, W. M., SIAM J. Numer. Anal. 7(1):1–46, 1970
  (sin Θ theorem, §3).
- Yu, Y., Wang, T., Samworth, R. J., Annals of Statistics 43(3):2028–2061,
  2015, Theorem 2 (two-sided gap projector variant with constant 1).

Statement differences: stated for the projector onto the `k+1` smallest
eigenvalues of the Laplacian sequence, with the separation hypothesis
phrased through the one-step gap lower bound; the per-step engine is the
projector form of Davis–Kahan. The `1 ≤` version omits the sharper
constants available in the two papers.

QA: exercised by
`SpectralGraphTheory.QA.persistence_zero_perturbation_QA` in
`Scaffold/QA/SpectralGraph/Dynamics_QA.lean`, which checks the zero-event
degenerate case against the axiom's interface.
-/
axiom spectral_persistence
    (A : TimeVaryingGraph V) (k : Fin (Fintype.card V))
    (hk : (k : ℕ) + 1 < Fintype.card V)
    (ε γ : ℝ) (hγ : 0 < γ)
    (hsymm : ∀ t, (A t).IsSymm)
    (hevent : IsEventDriven A ε)
    (hgap : ∀ t, spectralGap (laplacianSequence A t)
      (laplacianSequence_symmetric A hsymm t) k hk ≥ γ) :
    ∀ t, ‖initialProjector (laplacianSequence A (t + 1))
          (laplacianSequence_symmetric A hsymm (t + 1)) k
        - initialProjector (laplacianSequence A t)
          (laplacianSequence_symmetric A hsymm t) k‖ ≤ ε / γ

end SpectralGraphTheory
