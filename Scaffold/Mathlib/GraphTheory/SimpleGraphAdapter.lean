/-
  SimpleGraphAdapter.lean

  Purpose
  -------
  The `SimpleGraph → WAdj` interoperability adapter: the second
  direction (with `SpectralGraphTheory.supportGraph`, the
  `WAdj → SimpleGraph` adapter) of the bridge between Mathlib's graph
  objects and Scaffold's matrix-first spectral graph theory center.
  `SimpleGraph.toWAdj G` sends a Mathlib `SimpleGraph` into the center
  as its 0/1 adjacency matrix, so every proved Scaffold theorem
  (Laplacians, spectra, Rayleigh forms, cuts, conductance) becomes
  callable on `G` through one definition, and the agreement theorems
  below transfer Mathlib's `lapMatrix` results onto the Scaffold side
  and back.

  Delivered as step 1 of the re-sequenced proposal
  `proposals/electrical-structure-crust.md` (2026-08-18 corrections),
  which sequences this adapter first as "the highest compounding
  multiplier available". Everything here is hard crust: real
  definitions and proved theorems, no new axioms, no `sorry`.

  Related modules: the weighted Laplacian center is
  `Scaffold.Mathlib.GraphTheory.Spectral`; Mathlib's unweighted
  Laplacian API is `Mathlib.Combinatorics.SimpleGraph.LapMatrix`.
-/

import Scaffold.Mathlib.GraphTheory.Spectral
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open scoped BigOperators Matrix

/-!
## The adapter definition and its intrinsic facts

The adapter is *defined* as Mathlib's `adjMatrix ℝ` — no duplicated
matrix construction — and inherits symmetry and nonnegativity from it.
`toWAdj_nonneg` unlocks every `hnonneg`-hypothesized center theorem
(`laplacian_psd`, `boundary_nonneg`, `cheegerConstant_nonneg`, …) for
Mathlib graphs.
-/

namespace SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

/-- The `SimpleGraph → WAdj` interoperability adapter: a Mathlib
`SimpleGraph` enters Scaffold's matrix-first center as its 0/1
adjacency matrix. Defined as Mathlib's `adjMatrix ℝ` so that no
parallel matrix construction exists to drift out of agreement; the
interface lemma `toWAdj_apply` is the stable entry point for
consumers. -/
def toWAdj : Matrix V V ℝ :=
  G.adjMatrix ℝ

omit [Fintype V] [DecidableEq V] in
@[simp] theorem toWAdj_apply (i j : V) :
    G.toWAdj i j = if G.Adj i j then 1 else 0 :=
  G.adjMatrix_apply i j

omit [Fintype V] [DecidableEq V] in
/-- Adapter weights are symmetric: Mathlib's `adjMatrix` is. -/
theorem toWAdj_symm : G.toWAdj.IsSymm :=
  SimpleGraph.isSymm_adjMatrix (α := ℝ) G

omit [Fintype V] [DecidableEq V] in
/-- Adapter weights are nonnegative (they are `0`/`1`): this discharges
the `hnonneg` hypothesis of every center theorem that needs it. -/
theorem toWAdj_nonneg : ∀ i j : V, 0 ≤ G.toWAdj i j := by
  intro i j
  by_cases h : G.Adj i j
  · simp [toWAdj_apply, h]
  · simp [toWAdj_apply, h]

end SimpleGraph

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

/-!
## Agreement with Mathlib's unweighted API

Degrees, volumes, the Laplacian matrix, and cut boundaries of the
adapter agree with Mathlib's `degree`, `degMatrix`, `lapMatrix`, and
edge counts. `laplacian_toWAdj_eq_lapMatrix` is the headline: it
transfers every Mathlib `lapMatrix` theorem onto `laplacian G.toWAdj`
and every Scaffold Laplacian theorem onto Mathlib graphs, by a single
rewrite.
-/

omit [DecidableEq V] in
/-- Degree agreement: Scaffold's row-sum degree of the adapter is
Mathlib's `G.degree` (via `degree_eq_sum_if_adj`). -/
theorem deg_toWAdj (i : V) : deg G.toWAdj i = (G.degree i : ℝ) := by
  simp only [deg, SimpleGraph.toWAdj_apply]
  exact (G.degree_eq_sum_if_adj (R := ℝ) i).symm

omit [DecidableEq V] in
/-- Volume agreement: the Scaffold volume of `S` under the adapter is
the Mathlib degree sum over `S`. -/
theorem vol_toWAdj_eq_sum_degrees (S : Finset V) :
    vol G.toWAdj S = ∑ i in S, (G.degree i : ℝ) :=
  Finset.sum_congr rfl fun i _ => deg_toWAdj G i

omit [DecidableEq V] in
/-- Handshake: the total adapter volume is twice the edge count —
Mathlib's degree-sum formula (`sum_degrees_eq_twice_card_edges`)
transferred through `vol_toWAdj_eq_sum_degrees`, an external check that
the weighted `vol` machinery agrees with edge counting. -/
theorem vol_toWAdj_univ_eq_two_mul_card_edges :
    vol G.toWAdj (Finset.univ : Finset V) = 2 * (G.edgeFinset.card : ℝ) := by
  rw [vol_toWAdj_eq_sum_degrees, ← Nat.cast_sum,
    G.sum_degrees_eq_twice_card_edges]
  push_cast
  ring

/-- **Laplacian agreement (headline):** Scaffold's `laplacian` of the
adapter is Mathlib's `G.lapMatrix ℝ`, entry for entry. Every Mathlib
`lapMatrix` theorem (positive semidefiniteness, the Dirichlet form,
kernel characterizations, component counting) now applies to
`laplacian G.toWAdj`, and conversely every proved Scaffold Laplacian
theorem applies to Mathlib graphs. -/
theorem laplacian_toWAdj_eq_lapMatrix :
    laplacian G.toWAdj = G.lapMatrix ℝ := by
  ext i j
  by_cases h : i = j
  · subst h
    have hloop : ¬ G.Adj i i := fun ha => G.ne_of_adj ha rfl
    simp only [laplacian, Matrix.sub_apply, degreeMatrix_diagonal,
      SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.diagonal_apply,
      SimpleGraph.toWAdj_apply, SimpleGraph.adjMatrix_apply, if_neg hloop,
      sub_zero]
    exact deg_toWAdj G i
  · simp only [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal _ h,
      SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.diagonal_apply,
      SimpleGraph.toWAdj_apply, SimpleGraph.adjMatrix_apply, if_neg h,
      zero_sub]

/-- Boundary agreement, indicator form: the Scaffold edge boundary of
`S` under the adapter is the sum over `S` of the 0/1 indicators of
"neighbor outside `S`". -/
theorem boundary_toWAdj_eq_sum_neighbors (S : Finset V) :
    boundary G.toWAdj S
      = ∑ i in S, ∑ j in G.neighborFinset i, if j ∉ S then (1:ℝ) else 0 := by
  have hcompl : Sᶜ = (Finset.univ : Finset V).filter (fun j => j ∉ S) := by
    ext j; simp [Finset.mem_filter]
  have hnbr : ∀ i : V, G.neighborFinset i
      = (Finset.univ : Finset V).filter (fun j => G.Adj i j) := by
    intro i; ext j; simp [Finset.mem_filter, G.mem_neighborFinset]
  rw [boundary]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hnbr i, hcompl, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hs : j ∉ S <;> by_cases ha : G.Adj i j <;>
    simp [hs, ha, SimpleGraph.toWAdj_apply]

/-- Boundary agreement, card form: the boundary is the number of edges
crossing the cut, each crossing edge counted exactly once (from its
endpoint inside `S`): for each `i ∈ S`, count the neighbors of `i`
lying outside `S`. -/
theorem boundary_toWAdj_eq_sum_card_neighbors (S : Finset V) :
    boundary G.toWAdj S
      = ∑ i in S, (((G.neighborFinset i).filter (fun j => j ∉ S)).card : ℝ) := by
  have hcard : ∀ i : V,
      (((G.neighborFinset i).filter (fun j => j ∉ S)).card : ℝ)
        = ∑ j in G.neighborFinset i, if j ∉ S then (1:ℝ) else 0 := by
    intro i
    have h1 : ((G.neighborFinset i).filter (fun j => j ∉ S)).card
        = ∑ j in (G.neighborFinset i).filter (fun j => j ∉ S), (1:ℕ) :=
      Finset.card_eq_sum_ones _
    rw [h1, Nat.cast_sum, Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ => by split <;> norm_num
  rw [boundary_toWAdj_eq_sum_neighbors]
  exact Finset.sum_congr rfl fun i _ => (hcard i).symm

/-!
## Neutral re-exports: Mathlib's kernel and component results

Mathlib's unweighted Laplacian theorems, transferred through the
agreement above onto Scaffold's `laplacian G.toWAdj` — the fold-in the
proposal assigns to this step, at zero new proof surface (each is one
or two rewrites).
-/

/-- The kernel of `laplacian G.toWAdj` is exactly the vectors that are
constant along Mathlib reachability — Mathlib's
`lapMatrix_toLin'_apply_eq_zero_iff_forall_reachable` transferred to
the Scaffold side. -/
theorem laplacian_toWAdj_mulVec_eq_zero_iff_reachable (f : V → ℝ) :
    (laplacian G.toWAdj).mulVec f = 0 ↔ ∀ i j : V, G.Reachable i j → f i = f j := by
  rw [laplacian_toWAdj_eq_lapMatrix, ← Matrix.mulVecLin_apply,
    ← Matrix.toLin'_apply']
  exact G.lapMatrix_toLin'_apply_eq_zero_iff_forall_reachable f

/-- The dimension of the kernel of `laplacian G.toWAdj` is the number
of connected components of `G` — Mathlib's
`card_ConnectedComponent_eq_rank_ker_lapMatrix` transferred to the
Scaffold side. -/
theorem finrank_ker_laplacian_toWAdj :
    Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (laplacian G.toWAdj)))
      = Fintype.card G.ConnectedComponent := by
  rw [← Matrix.toLin'_apply', laplacian_toWAdj_eq_lapMatrix,
    G.card_ConnectedComponent_eq_rank_ker_lapMatrix]

/-!
## The adapter roundtrip

`supportGraph` (the `WAdj → SimpleGraph` direction, delivered with the
kernel characterization) applied to `toWAdj` returns `G`: the two
adapters are mutually consistent, and the weighted kernel
characterization of the center applies verbatim to Mathlib graphs.
-/

omit [Fintype V] [DecidableEq V] in
/-- Roundtrip: the support graph of the adapter weights is the original
`SimpleGraph` (`i ≠ j ∧ 0 < toWAdj i j ↔ G.Adj i j`; looplessness of
`G` discharges the `i ≠ j` conjunct). -/
theorem supportGraph_toWAdj_eq_self :
    supportGraph G.toWAdj (SimpleGraph.toWAdj_symm G) = G := by
  ext i j
  rw [supportGraph_adj]
  constructor
  · rintro ⟨-, hpos⟩
    by_cases h : G.Adj i j
    · exact h
    · rw [SimpleGraph.toWAdj_apply, if_neg h] at hpos
      norm_num at hpos
  · intro h
    refine ⟨G.ne_of_adj h, ?_⟩
    rw [SimpleGraph.toWAdj_apply, if_pos h]
    norm_num

/-- **Roundtrip corollary:** for a *connected* Mathlib graph, the
kernel of the Scaffold Laplacian of the adapter is exactly the line of
constants — the delivered weighted kernel characterization
(`laplacian_kernel_eq_span_onesVec`) now applies to `G` directly,
through the roundtrip above. -/
theorem laplacian_toWAdj_kernel_eq_span_ones (hconn : G.Connected) :
    LinearMap.ker (Matrix.mulVecLin (laplacian G.toWAdj))
      = Submodule.span ℝ ({onesVec} : Set (V → ℝ)) :=
  laplacian_kernel_eq_span_onesVec G.toWAdj (SimpleGraph.toWAdj_symm G)
    (SimpleGraph.toWAdj_nonneg G)
    (by rw [supportGraph_toWAdj_eq_self]; exact hconn)

end SpectralGraphTheory
