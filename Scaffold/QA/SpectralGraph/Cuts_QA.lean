/-
  Cuts_QA.lean

  Purpose
  -------
  QA lemmas for the cut-duality block of
  `Scaffold.Mathlib.GraphTheory.Spectral`: volume complementarity,
  boundary and conductance invariance under complementation, and the
  degenerate-cut guards, instantiated at the concrete three-vertex path.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic is
  fully evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## The three-vertex path `0 — 1 — 2` (reused fixture)
-/

/-- Adjacency of the path `0 — 1 — 2` on `Fin 3`: symmetric, unit
weights, degrees (1, 2, 1). -/
def pathAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 0; 1, 0, 1; 0, 1, 0]

theorem pathAdj_isSymm : pathAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [pathAdj]

/-- Row sums of the path: degrees (1, 2, 1). -/
theorem pathAdj_deg_zero : deg pathAdj 0 = 1 := by
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem pathAdj_deg_one : deg pathAdj 1 = 2 := by
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem pathAdj_deg_two : deg pathAdj 2 = 1 := by
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

/-- The diagonal entry `pathAdj 0 0` vanishes (no self-loops). -/
theorem pathAdj_zero_zero : pathAdj 0 0 = 0 := by norm_num [pathAdj]

/-- The sum of row `0` over `{0}ᶜ` computes to the single edge to the
center, via total-row-sum minus the (vanishing) diagonal entry. -/
theorem path_row0_compl_sum :
    ∑ j in ({0} : Finset (Fin 3))ᶜ, pathAdj 0 j = 1 := by
  have hsplit := Finset.sum_add_sum_compl
    ({0} : Finset (Fin 3)) (fun j => pathAdj 0 j)
  have hsingle : ∑ j in ({0} : Finset (Fin 3)), pathAdj 0 j
      = pathAdj 0 0 := Finset.sum_singleton _ _
  rw [hsingle, pathAdj_zero_zero, zero_add] at hsplit
  exact hsplit.trans pathAdj_deg_zero

/-- The singleton cut `{0}`: its boundary is the single edge to the
center. -/
theorem path_boundary_singleton_QA :
    boundary pathAdj {0} = 1 := by
  simp only [boundary, Finset.sum_singleton]
  exact path_row0_compl_sum

/-- Duality computes at the singleton cut: the boundary of the
complement `{1, 2}` equals the boundary of `{0}`, both `1` — the cut is
a property of the partition. -/
theorem path_boundary_compl_QA :
    boundary pathAdj ({0} : Finset (Fin 3))ᶜ = 1 :=
  (boundary_compl pathAdj pathAdj_isSymm {0}).symm.trans
    path_boundary_singleton_QA

/-- Conductance invariance computes at the singleton cut:
`conductance {0} = conductance {1,2}` — the Cheeger minimizer may be
canonicalized to either side. -/
theorem path_conductance_compl_QA :
    conductance pathAdj ({0} : Finset (Fin 3))
      = conductance pathAdj ({0} : Finset (Fin 3))ᶜ :=
  conductance_compl pathAdj pathAdj_isSymm {0}

/-- Volume complementarity computes at the singleton cut:
`vol {0} + vol {1,2} = vol univ = 4` (total degree of the path). -/
theorem path_vol_compl_QA :
    vol pathAdj ({0} : Finset (Fin 3)) + vol pathAdj ({0} : Finset (Fin 3))ᶜ
      = 4 := by
  have h := vol_compl pathAdj ({0} : Finset (Fin 3))
  have hvol : vol pathAdj (Finset.univ : Finset (Fin 3)) = 4 := by
    simp only [vol]
    rw [Fin.sum_univ_three, pathAdj_deg_zero, pathAdj_deg_one,
      pathAdj_deg_two]
    norm_num
  rw [hvol] at h
  exact h

/-- Degenerate-cut guards compute: the empty and full cuts have zero
boundary. -/
theorem path_boundary_degenerate_QA :
    boundary pathAdj (∅ : Finset (Fin 3)) = 0
      ∧ boundary pathAdj (Finset.univ : Finset (Fin 3)) = 0 :=
  ⟨boundary_empty pathAdj, boundary_univ pathAdj⟩

end SpectralGraphTheory.QA
