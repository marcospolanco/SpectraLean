/-
  SimpleGraphAdapter_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter`
  (`SimpleGraph.toWAdj` and its agreement theorems with Mathlib's
  unweighted API): a positive witness at the three-vertex path, where
  adapter weights, degrees, the Laplacian/lapMatrix agreement, the
  boundary-as-edge-count, the handshake identity, and the kernel
  roundtrip are computed against hand-expected numbers, and a negative
  witness at two disjoint edges on `Fin 4`, where a component indicator
  lies in the Laplacian kernel yet outside `span {onesVec}` — showing
  the connectivity hypothesis of the kernel characterization is
  load-bearing through the adapter.

  All proofs are real Lean proofs (no `sorry`/`admit`). Where possible,
  values are computed from the definitions (not by rewriting with the
  agreement theorems), so that a mis-defined adapter, degree, boundary,
  or volume self-consistent with its own theorem family would be caught.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## Connected witness: the three-vertex path `0 — 1 — 2`

Adjacency `i.val + j.val = 1` (edge `0 — 1`) or `= 3` (edge `1 — 2`).
Degrees `(1, 2, 1)`; two edges; connected.
-/

/-- The three-vertex path `0 — 1 — 2` as a Mathlib `SimpleGraph`. -/
def pathGraph3 : SimpleGraph (Fin 3) where
  Adj i j := i.val + j.val = 1 ∨ i.val + j.val = 3
  symm := fun i j h => h.imp (fun e => by omega) (fun e => by omega)
  loopless := fun i h => h.elim (fun e => by omega) (fun e => by omega)

instance : DecidableRel pathGraph3.Adj :=
  fun i j => inferInstanceAs (Decidable (i.val + j.val = 1 ∨ i.val + j.val = 3))

/-- The path is connected: every vertex is reachable from the center by
an explicit one-step walk (or is the center). -/
theorem path3_connected : pathGraph3.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨1, fun v => ?_⟩
  fin_cases v
  · exact ⟨SimpleGraph.Walk.cons (show pathGraph3.Adj 1 0 from by decide)
      SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (show pathGraph3.Adj 1 2 from by decide)
      SimpleGraph.Walk.nil⟩

/-- Adapter entries compute: the edge `0 — 1` carries weight `1`. -/
theorem path3_toWAdj_entry_QA : pathGraph3.toWAdj 0 1 = 1 := by
  rw [SimpleGraph.toWAdj_apply, if_pos (show pathGraph3.Adj 0 1 by decide)]

/-- Adapter entries compute: the non-edge `0 — 2` carries weight `0`. -/
theorem path3_toWAdj_nonedge_QA : pathGraph3.toWAdj 0 2 = 0 := by
  rw [SimpleGraph.toWAdj_apply, if_neg (by decide)]

/-- Degree of the path endpoint, computed from the `deg` definition
(row sum of adapter weights), not by the agreement theorem. -/
theorem path3_deg_left_QA : deg pathGraph3.toWAdj 0 = 1 := by
  simp only [deg, SimpleGraph.toWAdj_apply, Fin.sum_univ_three]
  rw [if_neg (show ¬ pathGraph3.Adj 0 0 by decide),
    if_pos (show pathGraph3.Adj 0 1 by decide),
    if_neg (show ¬ pathGraph3.Adj 0 2 by decide)]
  norm_num

/-- Degree of the path center, computed from the definition: `2`. -/
theorem path3_deg_middle_QA : deg pathGraph3.toWAdj 1 = 2 := by
  simp only [deg, SimpleGraph.toWAdj_apply, Fin.sum_univ_three]
  rw [if_pos (show pathGraph3.Adj 1 0 by decide),
    if_neg (show ¬ pathGraph3.Adj 1 1 by decide),
    if_pos (show pathGraph3.Adj 1 2 by decide)]
  norm_num

/-- Degree of the other endpoint, computed from the definition: `1`. -/
theorem path3_deg_right_QA : deg pathGraph3.toWAdj 2 = 1 := by
  simp only [deg, SimpleGraph.toWAdj_apply, Fin.sum_univ_three]
  rw [if_neg (show ¬ pathGraph3.Adj 2 0 by decide),
    if_pos (show pathGraph3.Adj 2 1 by decide),
    if_neg (show ¬ pathGraph3.Adj 2 2 by decide)]
  norm_num

/-- Mathlib degrees evaluate to the same values `(1, 2, 1)`, so the
degree agreement theorem instantiates against computed numbers on both
sides. -/
theorem path3_deg_agreement_QA :
    pathGraph3.degree 0 = 1 ∧ pathGraph3.degree 1 = 2 ∧ pathGraph3.degree 2 = 1 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Laplacian diagonal entry at the center, computed from `laplacian` /
`degreeMatrix`: the degree `2` (self-adjacency is false, so the
adapter entry on the diagonal is `0`). -/
theorem path3_laplacian_diag_QA : laplacian pathGraph3.toWAdj 1 1 = 2 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal, path3_deg_middle_QA,
    SimpleGraph.toWAdj_apply, if_neg (show ¬ pathGraph3.Adj 1 1 by decide), sub_zero]

/-- Laplacian off-diagonal entry at the edge `0 — 1`: `-1`. -/
theorem path3_laplacian_offdiag_QA : laplacian pathGraph3.toWAdj 0 1 = -1 := by
  rw [laplacian, Matrix.sub_apply,
    degreeMatrix_off_diagonal pathGraph3.toWAdj (by decide : (0 : Fin 3) ≠ 1),
    SimpleGraph.toWAdj_apply, if_pos (show pathGraph3.Adj 0 1 by decide), zero_sub]

/-- Laplacian off-diagonal entry at the non-edge `1 — 0` seen from the
center: `-1` (the edge exists from that side too). -/
theorem path3_laplacian_10_QA : laplacian pathGraph3.toWAdj 1 0 = -1 := by
  rw [laplacian, Matrix.sub_apply,
    degreeMatrix_off_diagonal pathGraph3.toWAdj (by decide : (1 : Fin 3) ≠ 0),
    SimpleGraph.toWAdj_apply, if_pos (show pathGraph3.Adj 1 0 by decide), zero_sub]

/-- **Laplian agreement instantiates:** Scaffold's Laplacian of the
adapter equals Mathlib's `lapMatrix ℝ`, here as a checked matrix
equality at the path. -/
theorem path3_lapMatrix_agreement_QA :
    laplacian pathGraph3.toWAdj = pathGraph3.lapMatrix ℝ :=
  laplacian_toWAdj_eq_lapMatrix pathGraph3

/-- Mathlib's own Laplacian entry computes to the same diagonal value
`2` at the center, independently of the agreement theorem. -/
theorem path3_lapMatrix_entry_QA : pathGraph3.lapMatrix ℝ 1 1 = 2 := by
  rw [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
    Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply,
    if_pos rfl, if_neg (show ¬ pathGraph3.Adj 1 1 by decide), sub_zero,
    show pathGraph3.degree 1 = 2 from by decide]
  norm_num

/-- Boundary of the middle singleton, computed from the `boundary`
definition (double sum of adapter weights): `2`. -/
theorem path3_boundary_QA : boundary pathGraph3.toWAdj {1} = 2 := by
  have hcompl : ({1} : Finset (Fin 3))ᶜ = {0, 2} := by
    ext j; simp only [Finset.mem_compl, Finset.mem_singleton, Finset.mem_insert]
    omega
  rw [boundary, hcompl, Finset.sum_singleton,
    Finset.sum_insert (by simp : (0 : Fin 3) ∉ ({2} : Finset (Fin 3))),
    Finset.sum_singleton, SimpleGraph.toWAdj_apply]
  rw [if_pos (show pathGraph3.Adj 1 0 by decide)]
  simp only [SimpleGraph.toWAdj_apply]
  rw [if_pos (show pathGraph3.Adj 1 2 by decide)]
  norm_num

/-- The card-form boundary agreement instantiates (stated with a set
variable so the `Finset.filter` decidability instance elaborates as in
the adapter module). -/
theorem path3_boundary_card_agreement_QA (S : Finset (Fin 3)) :
    boundary pathGraph3.toWAdj S
      = ∑ i in S, (((pathGraph3.neighborFinset i).filter (fun j : Fin 3 => j ∉ S)).card : ℝ) :=
  boundary_toWAdj_eq_sum_card_neighbors pathGraph3 S

/-- The neighbor count itself evaluates to `2`: two crossing edges
(`0 — 1` and `1 — 2`), each counted once. -/
theorem path3_boundary_card_value_QA :
    ((pathGraph3.neighborFinset 1).filter (fun j : Fin 3 => j ∉ ({1} : Finset (Fin 3)))).card
      = 2 := by
  decide

/-- Cast form of the neighbor count: the crossing-edge count is `2`
in `ℝ`. -/
theorem path3_boundary_card_cast_QA :
    (((pathGraph3.neighborFinset 1).filter (fun j : Fin 3 => j ∉ ({1} : Finset (Fin 3)))).card : ℝ)
      = 2 := by
  rw [path3_boundary_card_value_QA]
  norm_num

/-- Total volume from the `deg` values: `4`. -/
theorem path3_vol_univ_QA : vol pathGraph3.toWAdj Finset.univ = 4 := by
  simp only [vol, Fin.sum_univ_three, path3_deg_left_QA, path3_deg_middle_QA,
    path3_deg_right_QA]
  norm_num

/-- Handshake instantiates: total volume `4` equals twice the edge
count, and the edge count itself evaluates to `2`. -/
theorem path3_handshake_QA :
    vol pathGraph3.toWAdj Finset.univ = 2 * (pathGraph3.edgeFinset.card : ℝ) := by
  rw [vol_toWAdj_univ_eq_two_mul_card_edges,
    show pathGraph3.edgeFinset.card = 2 from by decide]

/-- **Kernel roundtrip instantiates:** for the connected path, the
kernel of the Scaffold Laplacian of the adapter is the line of
constants. -/
theorem path3_kernel_span_QA :
    LinearMap.ker (Matrix.mulVecLin (laplacian pathGraph3.toWAdj))
      = Submodule.span ℝ ({onesVec} : Set (Fin 3 → ℝ)) :=
  laplacian_toWAdj_kernel_eq_span_ones pathGraph3 path3_connected

/-- **Reachable bridge instantiates:** kernel membership is equivalent
to constancy along reachability. -/
theorem path3_kernel_iff_reachable_QA (f : Fin 3 → ℝ) :
    (laplacian pathGraph3.toWAdj).mulVec f = 0 ↔
      ∀ i j : Fin 3, pathGraph3.Reachable i j → f i = f j :=
  laplacian_toWAdj_mulVec_eq_zero_iff_reachable pathGraph3 f

/-- Constants are killed (conservation of mass), pinned to the value
`5`. -/
theorem path3_const_in_kernel_QA : (laplacian pathGraph3.toWAdj).mulVec 5 = 0 :=
  funext fun _ => by
    have := (laplacian_mulVec_const pathGraph3.toWAdj 5)
    exact congrFun this _

/-- A non-constant vector is computed *out* of the kernel, entrywise:
row `1` of `L *ᵥ ![1,0,0]` evaluates to `-1 ≠ 0`. -/
theorem path3_nonconstant_out_of_kernel_QA :
    (laplacian pathGraph3.toWAdj).mulVec ![1,0,0] ≠ 0 := by
  intro h
  have h1 : (laplacian pathGraph3.toWAdj).mulVec ![1,0,0] 1 = 0 := by
    rw [h]; rfl
  rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three, path3_laplacian_10_QA,
    path3_laplacian_diag_QA] at h1
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h1

/-!
## Disconnected negative witness: two disjoint edges `0 — 1`, `2 — 3`

Adjacency `i.val + j.val = 1` (edge `0 — 1`) or `= 5` (edge `2 — 3`).
The component indicator `![1,1,0,0]` is a Laplacian-kernel vector that
is not constant and not in `span {onesVec}`: the connectivity
hypothesis of the kernel characterization is load-bearing through the
adapter.
-/

/-- Two disjoint edges `0 — 1` and `2 — 3` on `Fin 4`. -/
def twoEdgeGraph4 : SimpleGraph (Fin 4) where
  Adj i j := i.val + j.val = 1 ∨ i.val + j.val = 5
  symm := fun i j h => h.imp (fun e => by omega) (fun e => by omega)
  loopless := fun i h => h.elim (fun e => by omega) (fun e => by omega)

instance : DecidableRel twoEdgeGraph4.Adj :=
  fun i j => inferInstanceAs (Decidable (i.val + j.val = 1 ∨ i.val + j.val = 5))

theorem twoEdge_deg_0_QA : deg twoEdgeGraph4.toWAdj 0 = 1 := by
  simp only [deg, SimpleGraph.toWAdj_apply, Fin.sum_univ_four]
  rw [if_neg (show ¬ twoEdgeGraph4.Adj 0 0 by decide),
    if_pos (show twoEdgeGraph4.Adj 0 1 by decide),
    if_neg (show ¬ twoEdgeGraph4.Adj 0 2 by decide),
    if_neg (show ¬ twoEdgeGraph4.Adj 0 3 by decide)]
  norm_num

theorem twoEdge_deg_1_QA : deg twoEdgeGraph4.toWAdj 1 = 1 := by
  simp only [deg, SimpleGraph.toWAdj_apply, Fin.sum_univ_four]
  rw [if_pos (show twoEdgeGraph4.Adj 1 0 by decide),
    if_neg (show ¬ twoEdgeGraph4.Adj 1 1 by decide),
    if_neg (show ¬ twoEdgeGraph4.Adj 1 2 by decide),
    if_neg (show ¬ twoEdgeGraph4.Adj 1 3 by decide)]
  norm_num

theorem twoEdge_laplacian_00_QA : laplacian twoEdgeGraph4.toWAdj 0 0 = 1 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal, twoEdge_deg_0_QA,
    SimpleGraph.toWAdj_apply, if_neg (show ¬ twoEdgeGraph4.Adj 0 0 by decide), sub_zero]

theorem twoEdge_laplacian_01_QA : laplacian twoEdgeGraph4.toWAdj 0 1 = -1 := by
  rw [laplacian, Matrix.sub_apply,
    degreeMatrix_off_diagonal twoEdgeGraph4.toWAdj (by decide : (0 : Fin 4) ≠ 1),
    SimpleGraph.toWAdj_apply, if_pos (show twoEdgeGraph4.Adj 0 1 by decide), zero_sub]

theorem twoEdge_laplacian_10_QA : laplacian twoEdgeGraph4.toWAdj 1 0 = -1 := by
  rw [laplacian, Matrix.sub_apply,
    degreeMatrix_off_diagonal twoEdgeGraph4.toWAdj (by decide : (1 : Fin 4) ≠ 0),
    SimpleGraph.toWAdj_apply, if_pos (show twoEdgeGraph4.Adj 1 0 by decide), zero_sub]

theorem twoEdge_laplacian_11_QA : laplacian twoEdgeGraph4.toWAdj 1 1 = 1 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal, twoEdge_deg_1_QA,
    SimpleGraph.toWAdj_apply, if_neg (show ¬ twoEdgeGraph4.Adj 1 1 by decide), sub_zero]

theorem twoEdge_laplacian_20_QA : laplacian twoEdgeGraph4.toWAdj 2 0 = 0 := by
  rw [laplacian, Matrix.sub_apply,
    degreeMatrix_off_diagonal twoEdgeGraph4.toWAdj (by decide : (2 : Fin 4) ≠ 0),
    SimpleGraph.toWAdj_apply, if_neg (show ¬ twoEdgeGraph4.Adj 2 0 by decide)]
  simp

theorem twoEdge_laplacian_21_QA : laplacian twoEdgeGraph4.toWAdj 2 1 = 0 := by
  rw [laplacian, Matrix.sub_apply,
    degreeMatrix_off_diagonal twoEdgeGraph4.toWAdj (by decide : (2 : Fin 4) ≠ 1),
    SimpleGraph.toWAdj_apply, if_neg (show ¬ twoEdgeGraph4.Adj 2 1 by decide)]
  simp

theorem twoEdge_laplacian_30_QA : laplacian twoEdgeGraph4.toWAdj 3 0 = 0 := by
  rw [laplacian, Matrix.sub_apply,
    degreeMatrix_off_diagonal twoEdgeGraph4.toWAdj (by decide : (3 : Fin 4) ≠ 0),
    SimpleGraph.toWAdj_apply, if_neg (show ¬ twoEdgeGraph4.Adj 3 0 by decide)]
  simp

theorem twoEdge_laplacian_31_QA : laplacian twoEdgeGraph4.toWAdj 3 1 = 0 := by
  rw [laplacian, Matrix.sub_apply,
    degreeMatrix_off_diagonal twoEdgeGraph4.toWAdj (by decide : (3 : Fin 4) ≠ 1),
    SimpleGraph.toWAdj_apply, if_neg (show ¬ twoEdgeGraph4.Adj 3 1 by decide)]
  simp

/-- The component indicator is *not constant* — it takes values `1`
and `0`. -/
theorem twoEdge_indicator_not_const_QA :
    ¬ ∃ c : ℝ, (![1,1,0,0] : Fin 4 → ℝ) = fun _ => c := by
  rintro ⟨c, hc⟩
  have h0 : (1:ℝ) = c := by simpa using congrFun hc 0
  have h2 : (0:ℝ) = c := by simpa using congrFun hc 2
  linarith

/-- **The component indicator is computed into the kernel**, entrywise
from the definitions: each row of `L *ᵥ ![1,1,0,0]` evaluates to `0`
(the closed adjacency propositions are decided). -/
theorem twoEdge_indicator_in_kernel_QA :
    (laplacian twoEdgeGraph4.toWAdj).mulVec ![1,1,0,0] = 0 := by
  funext i
  match i with
  | 0 =>
      rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_four,
        twoEdge_laplacian_00_QA, twoEdge_laplacian_01_QA]
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  | 1 =>
      rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_four,
        twoEdge_laplacian_10_QA, twoEdge_laplacian_11_QA]
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  | 2 =>
      rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_four,
        twoEdge_laplacian_20_QA, twoEdge_laplacian_21_QA]
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  | 3 =>
      rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_four,
        twoEdge_laplacian_30_QA, twoEdge_laplacian_31_QA]
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **The indicator is outside `span {onesVec}`:** a `c • onesVec` has
all coordinates equal, the indicator does not. -/
theorem twoEdge_indicator_not_in_span_QA :
    ¬ (![1,1,0,0] : Fin 4 → ℝ) ∈ Submodule.span ℝ ({onesVec} : Set (Fin 4 → ℝ)) := by
  intro h
  rw [Submodule.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have h0 : c = 1 := by simpa [onesVec] using congrFun hc 0
  have h2 : c = 0 := by simpa [onesVec] using congrFun hc 2
  linarith

/-- **The kernel characterization fails without connectivity:** the
kernel of the disconnected graph's Laplacian strictly contains the line
of constants — a kernel vector exists outside `span {onesVec}`. The
connectivity hypothesis in `laplacian_toWAdj_kernel_eq_span_ones` (and
the center's `laplacian_kernel_eq_span_onesVec`) is load-bearing. -/
theorem twoEdge_kernel_ne_span_QA :
    LinearMap.ker (Matrix.mulVecLin (laplacian twoEdgeGraph4.toWAdj))
      ≠ Submodule.span ℝ ({onesVec} : Set (Fin 4 → ℝ)) := by
  intro h
  have hmem : (![1,1,0,0] : Fin 4 → ℝ)
      ∈ LinearMap.ker (Matrix.mulVecLin (laplacian twoEdgeGraph4.toWAdj)) := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact twoEdge_indicator_in_kernel_QA
  rw [h] at hmem
  exact twoEdge_indicator_not_in_span_QA hmem

/-- The component-count re-export instantiates: the kernel dimension
equals the number of connected components, which evaluates to `2`. -/
theorem twoEdge_finrank_QA :
    Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (laplacian twoEdgeGraph4.toWAdj)))
      = Fintype.card twoEdgeGraph4.ConnectedComponent :=
  finrank_ker_laplacian_toWAdj twoEdgeGraph4

theorem twoEdge_components_card_QA :
    Fintype.card twoEdgeGraph4.ConnectedComponent = 2 := by decide

end SpectralGraphTheory.QA
