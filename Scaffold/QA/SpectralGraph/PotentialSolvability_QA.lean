/-
  PotentialSolvability_QA.lean

  Purpose
  -------
  QA for the potential-solvability hinge of proposal
  `proposals/electrical-structure-crust.md` step 4, delivered in
  `Scaffold.Mathlib.GraphTheory.Spectral`
  (`exists_laplacian_mulVec_eq_of_sum_eq_zero`,
  `exists_laplacian_mulVec_eq_single_sub_single`, and their supports
  `laplacian_dotProduct_mulVec`,
  `dotProduct_eq_zero_of_laplacian_mulVec_eq_zero`,
  `exists_mulVec_eq_of_zero_comp`, `mulVec_eigvecOf_sum_apply`).

  Per the proposal's step-4 witness spec: a positive witness (potentials
  computed by hand on the two-vertex edge and on the connected
  three-vertex path, plus theorem instantiations), a negative witness
  for the zero-sum hypothesis (a non-zero-sum demand with no solution on
  a connected graph), and a negative witness for the connectivity
  hypothesis (a zero-sum demand with no solution on the disconnected
  two-edge fixture — cross-component demand, certified unsolvable
  through the kernel indicator).

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is fully evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral
import Scaffold.QA.SpectralGraph.Connectivity_QA
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## Connected witness: the two-vertex edge `0 — 1`
-/

/-- Adjacency of the two-vertex edge on `Fin 2`: symmetric unit weight. -/
def psEdgeAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 1; 1, 0]

theorem psEdgeAdj_isSymm : psEdgeAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [psEdgeAdj]

theorem psEdgeAdj_nonneg : ∀ i j, 0 ≤ psEdgeAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [psEdgeAdj]

/-- The support graph of the edge is connected: every vertex is reachable
from `0` (`0` trivially, `1` across the single edge). -/
theorem edge_supportGraph_connected :
    (supportGraph psEdgeAdj psEdgeAdj_isSymm).Connected := by
  have hfrom0 : ∀ v : Fin 2,
      (supportGraph psEdgeAdj psEdgeAdj_isSymm).Reachable 0 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
        ⟨by decide, by simp [psEdgeAdj]⟩ SimpleGraph.Walk.nil⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, hfrom0⟩

/-- The unit demand `e 0 − e 1` is zero-sum: `1 − 1 = 0`. -/
theorem edge_demand_sum_eq_zero_QA :
    ∑ i, (Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) : Fin 2 → ℝ) i = 0 := by
  simp [Pi.sub_apply]

/-- **Positive value witness (edge):** the potential `f = ![1, 0]` solves
the unit-demand equation, computed entrywise from the definitions. The
Laplacian of the edge is `[[1, −1], [−1, 1]]`, so `L *ᵥ ![1, 0] =
![1, −1] = e 0 − e 1`. -/
theorem edge_potential_value_QA :
    (laplacian psEdgeAdj).mulVec ![1, 0]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, psEdgeAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_two]

/-- **Interface instantiation (edge):** the unit-demand solvability
theorem applies to the edge graph. -/
theorem edge_unit_demand_solvability_QA :
    ∃ f : Fin 2 → ℝ, (laplacian psEdgeAdj).mulVec f
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) :=
  exists_laplacian_mulVec_eq_single_sub_single psEdgeAdj psEdgeAdj_isSymm
    psEdgeAdj_nonneg edge_supportGraph_connected 0 1

/-!
## Negative witness on the edge: a non-zero-sum demand is unsolvable

The zero-sum hypothesis is load-bearing already on the two-vertex edge:
the injection demand `e 0` has total `1 ≠ 0`, and the reciprocity
identity (through `dotProduct_eq_zero_of_laplacian_mulVec_eq_zero`,
with the all-ones kernel certificate `laplacian_ones_in_kernel`)
certifies that no potential exists.
-/

/-- **Negative witness (zero-sum hypothesis):** the demand `e 0` — sum
`1`, not zero — admits no potential on the connected edge graph. -/
theorem edge_unit_injection_unsolvable_QA :
    ¬ ∃ f : Fin 2 → ℝ, (laplacian psEdgeAdj).mulVec f = Pi.single 0 (1 : ℝ) := by
  rintro ⟨f, hf⟩
  have h0 : Matrix.dotProduct onesVec ((laplacian psEdgeAdj).mulVec f) = 0 :=
    dotProduct_eq_zero_of_laplacian_mulVec_eq_zero psEdgeAdj psEdgeAdj_isSymm
      (laplacian_ones_in_kernel psEdgeAdj)
  rw [hf] at h0
  simp [onesVec, Matrix.dotProduct, Fin.sum_univ_two] at h0

/-!
## Connected witness: the three-vertex path `0 — 1 — 2`
(reusing the `Connectivity_QA` fixture)
-/

/-- **Positive value witness (path):** the potential `f = ![1, 0, −1]`
solves the endpoint unit-demand equation on the path, computed entrywise
from the definitions — the path Laplacian carries `![1, 0, −1]` to
itself. -/
theorem path_potential_value_QA :
    (laplacian connPathAdj).mulVec ![1, 0, -1]
      = Pi.single 0 (1 : ℝ) - Pi.single 2 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, connPathAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three]

/-- **Interface instantiation (path):** the general zero-sum solvability
theorem and its unit-demand specialization both apply to the path. -/
theorem path_unit_demand_solvability_QA :
    ∃ f : Fin 3 → ℝ, (laplacian connPathAdj).mulVec f
      = Pi.single 0 (1 : ℝ) - Pi.single 2 (1 : ℝ) :=
  exists_laplacian_mulVec_eq_single_sub_single connPathAdj connPathAdj_isSymm
    connPathAdj_nonneg connPath_supportGraph_connected 0 2

/-- An arbitrary zero-sum demand on the path is solvable: the general
theorem instantiated at the alternating demand `![1, −2, 1]`
(sum `0`, not of unit-injection shape). -/
theorem path_general_demand_solvability_QA :
    ∃ f : Fin 3 → ℝ, (laplacian connPathAdj).mulVec f = ![1, -2, 1] := by
  refine exists_laplacian_mulVec_eq_of_sum_eq_zero connPathAdj
    connPathAdj_isSymm connPathAdj_nonneg connPath_supportGraph_connected ?_
  norm_num [Fin.sum_univ_three]

/-!
## Negative witness on the disconnected fixture: connectivity is
load-bearing

The two disjoint edges `0 — 1   2 — 3` (`Connectivity_QA` fixture) carry
the zero-sum cross-component demand `e 0 − e 2`. It is zero-sum, yet no
potential exists: the component indicator `![1, 1, 0, 0]` is a kernel
vector (computed in `Connectivity_QA`), and reciprocity forces every
image `L *ᵥ f` to be `⬝ᵥ`-orthogonal to it — but the demand is not. So
zero-sum alone does not suffice: connectivity (equivalently, the kernel
being exactly the constants) is what the solvability theorem consumes.
-/

/-- The cross-component demand `e 0 − e 2` on the disconnected fixture
is zero-sum. -/
theorem disc_demand_sum_eq_zero_QA :
    ∑ i, (Pi.single 0 (1 : ℝ) - Pi.single 2 (1 : ℝ) : Fin 4 → ℝ) i = 0 := by
  simp [Pi.sub_apply]

/-- **Negative witness (connectivity hypothesis):** the zero-sum demand
`e 0 − e 2` admits no potential on the disconnected fixture. -/
theorem disc_cross_demand_unsolvable_QA :
    ¬ ∃ f : Fin 4 → ℝ, (laplacian connDiscAdj).mulVec f
      = Pi.single 0 (1 : ℝ) - Pi.single 2 (1 : ℝ) := by
  rintro ⟨f, hf⟩
  have h0 : Matrix.dotProduct (![1, 1, 0, 0] : Fin 4 → ℝ)
      ((laplacian connDiscAdj).mulVec f) = 0 :=
    dotProduct_eq_zero_of_laplacian_mulVec_eq_zero connDiscAdj
      connDiscAdj_isSymm connDisc_indicator_in_kernel_QA
  rw [hf] at h0
  simp [Matrix.dotProduct, Fin.sum_univ_four, Pi.sub_apply] at h0

end SpectralGraphTheory.QA
