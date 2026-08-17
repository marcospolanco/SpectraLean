/-
  Projector_QA.lean

  Purpose
  -------
  QA lemmas for the spectral-projector algebra of
  `Scaffold.Mathlib.GraphTheory.Spectral`: eigenbasis orthonormality and
  completeness, projector idempotence, and the extreme-threshold
  theorems. These are theorems, not axioms, so QA here checks that the
  interfaces compose (extreme thresholds with idempotence, diagonal
  normalizations of the basis relations) rather than hunting for
  axiom-shape defects.

  All proofs are real Lean proofs (no `sorry`/`admit`).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Eigenbasis relations
-/

/-- Diagonal of orthonormality: every eigenvector has unit Euclidean
norm. -/
theorem eigvecOf_norm_one_QA (M : Matrix V V ℝ) (hM : M.IsSymm) (i : V) :
    ∑ k, eigvecOf M hM i k * eigvecOf M hM i k = 1 := by
  rw [eigvecOf_inner, if_pos rfl]

/-- Diagonal of completeness: the eigenbasis resolves every unit vector
with total weight one. -/
theorem eigvecOf_complete_diag_QA (M : Matrix V V ℝ) (hM : M.IsSymm)
    (a : V) :
    ∑ i, eigvecOf M hM i a * eigvecOf M hM i a = 1 := by
  rw [eigvecOf_complete, if_pos rfl]

/-!
## Projector idempotence at extreme thresholds
-/

/-- Below the whole spectrum the projector is zero, hence idempotent:
the composition of `spectralProjector_eq_zero` with idempotence. -/
theorem spectralProjector_below_idempotent_QA (M : Matrix V V ℝ)
    (hM : M.IsSymm) (c : ℝ) (h : ∀ i, c < eigvalOf M hM i) :
    spectralProjector M hM c * spectralProjector M hM c
      = spectralProjector M hM c := by
  rw [spectralProjector_eq_zero M hM c h, mul_zero]

/-- Above the whole spectrum the projector is the identity, hence
idempotent: the composition of `spectralProjector_eq_one` with
idempotence. -/
theorem spectralProjector_above_idempotent_QA (M : Matrix V V ℝ)
    (hM : M.IsSymm) (c : ℝ) (h : ∀ i, eigvalOf M hM i ≤ c) :
    spectralProjector M hM c * spectralProjector M hM c
      = spectralProjector M hM c := by
  rw [spectralProjector_eq_one M hM c h, one_mul]

/-- The invariant-subspace projector interface is idempotent through
`initialProjector`, at every cut index. -/
theorem initialProjector_idempotent_QA (M : Matrix V V ℝ) (hM : M.IsSymm)
    (k : Fin (Fintype.card V)) :
    initialProjector M hM k * initialProjector M hM k
      = initialProjector M hM k :=
  initialProjector_idempotent M hM k

end SpectralGraphTheory.QA
