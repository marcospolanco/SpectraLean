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
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_two]
  norm_num

theorem pathAdj_deg_one : deg pathAdj 1 = 2 := by
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_two]
  norm_num

theorem pathAdj_deg_two : deg pathAdj 2 = 1 := by
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_two]
  norm_num

/-- The sum of the off-diagonal entries of row `0` over `{0}ᶜ = {1, 2}`
computes to the single edge to the center. -/
theorem path_row0_compl_sum :
    ∑ j in ({0} : Finset (Fin 3))ᶜ, pathAdj 0 j = 1 := by
  have h0 : pathAdj 0 1 = 1 := by norm_num [pathAdj]
  have h1 : pathAdj 0 2 = 0 := by norm_num [pathAdj]
  rw [Finset.compl_singleton, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide)]
  simp only [Finset.sum_empty]
  rw [h0, h1]
  norm_num

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
    simp only [vol, Finset.sum_congr rfl
      (show ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        deg pathAdj i = if i = 0 then 1 else if i = 1 then 2 else 1 from
        by intro i _
         fin_cases i
         · rw [if_pos rfl, pathAdj_deg_zero]
         · rw [if_neg (by decide), if_pos rfl, pathAdj_deg_one]
         · rw [if_neg (by decide), if_neg (by decide), pathAdj_deg_two])]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
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
