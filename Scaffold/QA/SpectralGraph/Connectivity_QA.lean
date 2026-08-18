/-
  Connectivity_QA.lean

  Purpose
  -------
  QA lemmas for the connectivity/kernel characterization block of
  `Scaffold.Mathlib.GraphTheory.Spectral` (`supportGraph` and the
  theorems behind `laplacian_kernel_eq_span_onesVec`): a connected
  positive witness (the three-vertex path, where the characterization
  holds and is exercised in both directions) and a disconnected
  negative witness (two disjoint edges on `Fin 4`, where a component
  indicator lies in the Laplacian kernel yet is not constant and the
  support graph is not connected), showing the connectivity hypothesis
  is load-bearing.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is fully evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## Connected witness: the three-vertex path `0 — 1 — 2`
-/

/-- Adjacency of the path `0 — 1 — 2` on `Fin 3`: symmetric, unit
weights, degrees (1, 2, 1). -/
def connPathAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 0; 1, 0, 1; 0, 1, 0]

theorem connPathAdj_isSymm : connPathAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [connPathAdj]

theorem connPathAdj_nonneg : ∀ i j, 0 ≤ connPathAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [connPathAdj]

/-- The support graph of the path is connected: every vertex is
reachable from the center `1` by an explicit walk, and arbitrary pairs
reach each other through the center. -/
theorem connPath_supportGraph_connected :
    (supportGraph connPathAdj connPathAdj_isSymm).Connected := by
  have hfrom1 : ∀ v : Fin 3,
      (supportGraph connPathAdj connPathAdj_isSymm).Reachable 1 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.cons (u := 1) (v := 0) (w := 0)
        ⟨by decide, by simp [connPathAdj]⟩ SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 1) (v := 2) (w := 2)
        ⟨by decide, by simp [connPathAdj]⟩ SimpleGraph.Walk.nil⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨1, hfrom1⟩

/-- Interface: on the connected path the kernel is exactly the
constants, in both directions of the iff. -/
theorem connPath_kernel_iff_QA (f : Fin 3 → ℝ) :
    (laplacian connPathAdj).mulVec f = 0 ↔ ∃ c : ℝ, f = fun _ => c :=
  laplacian_mulVec_eq_zero_iff_exists_const connPathAdj connPathAdj_isSymm
    connPathAdj_nonneg connPath_supportGraph_connected f

/-- The span form instantiates: the kernel of the path Laplacian is the
line spanned by the all-ones vector. -/
theorem connPath_span_QA :
    LinearMap.ker (Matrix.mulVecLin (laplacian connPathAdj))
      = Submodule.span ℝ ({onesVec} : Set (Fin 3 → ℝ)) :=
  laplacian_kernel_eq_span_onesVec connPathAdj connPathAdj_isSymm
    connPathAdj_nonneg connPath_supportGraph_connected

/-- A constant kernel vector on the path: applying the characterization
returns a constant, and that constant is pinned to the input value. -/
theorem connPath_const_recovered_QA :
    ∃ c : ℝ, ((fun _ : Fin 3 => (5 : ℝ)) = fun _ => c) ∧ ((5 : ℝ) = c) := by
  obtain ⟨c, hc⟩ := (connPath_kernel_iff_QA (fun _ : Fin 3 => (5 : ℝ))).mp
    (laplacian_mulVec_const connPathAdj 5)
  refine ⟨c, hc, ?_⟩
  have h0 := congrFun hc 0
  simpa using h0

/-- Falsification on the connected side: the non-constant vector
`![1, 0, 0]` fails the kernel — computed entrywise from the
definitions, not derived from the theorem. -/
theorem connPath_e0_not_in_kernel_QA :
    (laplacian connPathAdj).mulVec ![1, 0, 0] ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [laplacian, Matrix.sub_apply, degreeMatrix, deg, connPathAdj,
    Matrix.of_apply, Matrix.mulVec, Matrix.dotProduct, Matrix.cons_val_zero,
    Matrix.head_cons, Fin.sum_univ_three, Pi.zero_apply] at h0
  norm_num at h0

/-!
## Disconnected witness: two disjoint edges `0 — 1   2 — 3` on `Fin 4`

All hypotheses of the kernel characterization hold here (symmetric,
nonnegative weights) except connectivity, and the conclusion fails: the
component indicator `![1, 1, 0, 0]` is in the kernel but not constant.
-/

/-- Adjacency of the disconnected graph `0 — 1   2 — 3` on `Fin 4`,
written entrywise (the two edges carry unit weight). -/
def connDiscAdj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
       (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then (1 : ℝ) else 0

theorem connDiscAdj_isSymm : connDiscAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [connDiscAdj]

theorem connDiscAdj_nonneg : ∀ i j, 0 ≤ connDiscAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [connDiscAdj]

/-- Every positive weight of the disconnected fixture stays inside one
block `{0, 1}` or `{2, 3}` (the block index is `(· : ℕ) ≤ 1`). -/
theorem connDisc_blocks : ∀ u v : Fin 4, 0 < connDiscAdj u v →
    ((u : ℕ) ≤ 1 ↔ (v : ℕ) ≤ 1) := by
  intro u v h
  fin_cases u <;> fin_cases v <;> simp [connDiscAdj] at h
  all_goals decide

/-- Support-graph walks of the disconnected fixture never change block:
induction over `SimpleGraph.Walk`, each step staying inside a block by
`connDisc_blocks`. -/
theorem connDisc_walk_blocks {u v : Fin 4}
    (w : (supportGraph connDiscAdj connDiscAdj_isSymm).Walk u v) :
    (u : ℕ) ≤ 1 ↔ (v : ℕ) ≤ 1 := by
  induction w with
  | nil => rfl
  | cons hadj _ ih =>
    exact (connDisc_blocks _ _ ((supportGraph_adj.1 hadj).2)).trans ih

/-- The support graph of the disconnected fixture is not connected:
a walk from `0` to `2` would have to change block. -/
theorem connDisc_not_connected_QA :
    ¬(supportGraph connDiscAdj connDiscAdj_isSymm).Connected := by
  intro h
  obtain ⟨w⟩ := h 0 2
  have hb := connDisc_walk_blocks w
  rw [show (0 : Fin 4).val = 0 from rfl, show (2 : Fin 4).val = 2 from rfl] at hb
  omega

/-- The component indicator `![1, 1, 0, 0]` lies in the Laplacian
kernel of the disconnected fixture — computed entrywise from the
definitions. -/
theorem connDisc_indicator_in_kernel_QA :
    (laplacian connDiscAdj).mulVec ![1, 1, 0, 0] = 0 := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, connDiscAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_four, Pi.zero_apply]

/-- The component indicator is not constant. -/
theorem connDisc_indicator_not_const_QA :
    ¬∃ c : ℝ, (![1, 1, 0, 0] : Fin 4 → ℝ) = fun _ => c := by
  rintro ⟨c, hc⟩
  have h0 : (1 : ℝ) = c := by
    have h := congrFun hc 0; simpa using h
  have h2 : (0 : ℝ) = c := by
    have h := congrFun hc 2; simpa using h
  rw [← h0] at h2
  norm_num at h2

/-- The connectivity hypothesis is load-bearing: on the disconnected
fixture a kernel vector exists that is not constant (and the support
graph is not connected), so no analogue of
`exists_const_of_laplacian_mulVec_eq_zero` can hold without
connectivity. -/
theorem connDisc_kernel_not_constants_QA :
    (laplacian connDiscAdj).mulVec ![1, 1, 0, 0] = 0 ∧
      ¬∃ c : ℝ, (![1, 1, 0, 0] : Fin 4 → ℝ) = fun _ => c :=
  ⟨connDisc_indicator_in_kernel_QA, connDisc_indicator_not_const_QA⟩

end SpectralGraphTheory.QA
