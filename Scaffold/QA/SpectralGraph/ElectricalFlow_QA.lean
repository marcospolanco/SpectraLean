/-
  ElectricalFlow_QA.lean

  Purpose
  -------
  QA for `Scaffold.Mathlib.GraphTheory.ElectricalFlow` — proposal
  `proposals/electrical-flow-routing.md` step 1 (the electrical
  current, divergence, flow predicates, and the Kirchhoff bridge),
  scoped to that step: no flow energy exists yet, so the proposal's
  double-counting and zero-energy-competitor fixtures (QA plan items 4
  and 5) are represented here in their step-1 form — the ordered-pair
  support guard — and the energy-dependent refutations stay deferred
  to step 2.

  Witness plan (proposal QA items 1, 3, 5, 6):

  - **Single edge** (`K₂`): the current matrix, its divergence, and
    the unit-flow instantiation, all computed from the definitions.
  - **Path** (`0 — 1 — 2`): the unit flow through two edges with the
    internal vertex's divergence computed to `0` — Kirchhoff
    conservation away from the source/sink, exercising the sum over
    more than one edge.
  - **Symmetry guard** (negative): an asymmetric weight matrix makes
    the electrical current fail antisymmetry — `A.IsSymm` is
    load-bearing in `electricalCurrent_antisymm`.
  - **Zero-edge support guard** (negative): an antisymmetric matrix
    carrying current across a zero-conductance pair satisfies
    antisymmetry *and* the unit divergence yet is excluded by `IsFlowOn`
    — the support conjunct is load-bearing, and without it this
    phantom would qualify as a unit flow on an edgeless network.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is fully evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.ElectricalFlow
import Scaffold.QA.SpectralGraph.PotentialSolvability_QA
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## Positive witness 1: the two-vertex edge `0 — 1`
(fixture `edgeAdj` from `PotentialSolvability_QA`)
-/

/-- **Current matrix (edge):** the potential `![1, 0]` induces the
current `!![0, 1; -1, 0]` — unit current `0 → 1`, its negative back,
nothing on the diagonals. Computed entrywise from the definitions. -/
theorem edge_current_matrix_QA :
    electricalCurrent edgeAdj ![1, 0] = Matrix.of !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [electricalCurrent, edgeAdj]

/-- **Divergence (edge):** net outflow `+1` at the source, `-1` at the
sink — computed from the raw definition, independent of the Kirchhoff
bridge. -/
theorem edge_current_divergence_QA :
    flowDivergence (electricalCurrent edgeAdj ![1, 0]) = ![1, -1] := by
  funext i
  fin_cases i <;>
    simp [flowDivergence, electricalCurrent, edgeAdj, Fin.sum_univ_two]

/-- **Interface instantiation (edge):** the Kirchhoff bridge computes
the divergence as the Laplacian action on the potential. -/
theorem edge_divergence_eq_laplacian_QA :
    flowDivergence (electricalCurrent edgeAdj ![1, 0])
      = (laplacian edgeAdj).mulVec ![1, 0] :=
  flowDivergence_electricalCurrent edgeAdj ![1, 0]

/-- **Unit flow (edge):** the potential `![1, 0]` — computed in
`PotentialSolvability_QA` to solve the unit-demand equation — induces
a unit flow, via the step-1 headline theorem. -/
theorem edge_isUnitFlow_QA :
    IsUnitFlow edgeAdj 0 1 (electricalCurrent edgeAdj ![1, 0]) :=
  isUnitFlow_electricalCurrent edgeAdj edgeAdj_isSymm edge_potential_value_QA

/-!
## Positive witness 2: the three-vertex path `0 — 1 — 2`
(fixture `connPathAdj` from `Connectivity_QA`)
-/

/-- **Current matrix (path):** the potential `![1, 0, -1]` induces the
current `!![0, 1, 0; -1, 0, 1; 0, -1, 0]` — one unit flows `0 → 1 → 2`
along the edges, and the non-adjacent pair `(0, 2)` carries nothing. -/
theorem path_current_matrix_QA :
    electricalCurrent connPathAdj ![1, 0, -1]
      = Matrix.of !![0, 1, 0; -1, 0, 1; 0, -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [electricalCurrent, connPathAdj]

/-- **Support guard (positive form):** no current on the
zero-conductance pair `(0, 2)` — the flow routes along edges only. -/
theorem path_current_nonedge_zero_QA :
    electricalCurrent connPathAdj ![1, 0, -1] 0 2 = 0 := by
  simp [electricalCurrent, connPathAdj]

/-- **Divergence (path):** net outflow `+1` at `0`, `0` at the
internal vertex `1` (in equals out — Kirchhoff conservation away from
source and sink), `-1` at `2`. Computed from the raw definition. -/
theorem path_current_divergence_QA :
    flowDivergence (electricalCurrent connPathAdj ![1, 0, -1])
      = ![1, 0, -1] := by
  funext i
  fin_cases i <;>
    simp [flowDivergence, electricalCurrent, connPathAdj, Fin.sum_univ_three]

/-- **Internal-vertex conservation (path):** the middle vertex's
divergence is exactly `0` — the conservation law that makes the
current a *routing* of the unit demand rather than a source or sink of
its own. -/
theorem path_internal_kirchhoff_QA :
    flowDivergence (electricalCurrent connPathAdj ![1, 0, -1]) 1 = 0 := by
  simp [flowDivergence, electricalCurrent, connPathAdj, Fin.sum_univ_three]

/-- **Unit flow (path):** the endpoint potential `![1, 0, -1]` (computed
in `PotentialSolvability_QA` to solve `L *ᵥ f = e 0 − e 2`) induces a
unit flow from `0` to `2`. -/
theorem path_isUnitFlow_QA :
    IsUnitFlow connPathAdj 0 2 (electricalCurrent connPathAdj ![1, 0, -1]) :=
  isUnitFlow_electricalCurrent connPathAdj connPathAdj_isSymm
    path_potential_value_QA

/-!
## Negative witness 1: symmetry is load-bearing in
`electricalCurrent_antisymm`

The asymmetric weight matrix `!![0, 2; 1, 0]` (conductance `2` one way,
`1` the other) with potential `![1, 0]`: the forward current is `2`,
the backward current `-1`, and `2 ≠ 1`, so the current is not
antisymmetric — `A.IsSymm` cannot be dropped.
-/

/-- Asymmetric two-vertex weights: conductance `2` from `0` to `1`,
conductance `1` back. -/
def asymWAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 2; 1, 0]

theorem asymWAdj_not_isSymm : ¬ asymWAdj.IsSymm := by
  intro h
  have h01 := h.apply 0 1
  simp [asymWAdj] at h01

/-- The two current entries computed from the definitions: forward
`2`, backward `-1`. -/
theorem asymWAdj_current_entries_QA :
    electricalCurrent asymWAdj ![1, 0] 0 1 = 2
      ∧ electricalCurrent asymWAdj ![1, 0] 1 0 = -1 := by
  constructor <;> simp [electricalCurrent, asymWAdj]

/-- **Symmetry guard:** on the asymmetric network the electrical
current is *not* antisymmetric — the hypothesis of
`electricalCurrent_antisymm` is load-bearing, witnessed numerically by
`2 ≠ 1`. -/
theorem asymWAdj_current_not_antisymm_QA :
    ¬ ∀ i j, electricalCurrent asymWAdj ![1, 0] i j
      = -electricalCurrent asymWAdj ![1, 0] j i := by
  intro h
  have h01 := h 0 1
  obtain ⟨hfwd, hbwd⟩ := asymWAdj_current_entries_QA
  rw [hfwd, hbwd] at h01
  norm_num at h01

/-!
## Negative witness 2: the zero-conductance support guard

On the edgeless network (`0` matrix), the antisymmetric matrix
`!![0, 1; -1, 0]` carries one unit of current across the
zero-conductance pair `(0, 1)`. It is antisymmetric and even has the
unit-demand divergence `e 0 − e 1` — every `IsUnitFlow` conjunct except
support. `IsFlowOn` excludes it: current may not ride a zero-weight
pair. This is the step-1 form of the proposal's zero-edge trap; the
energy-level refutation (this phantom would dissipate zero energy and
break Thomson's principle) is deferred to step 2, where `flowEnergy`
is defined.
-/

/-- The edgeless two-vertex network. -/
def zeroWAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 0; 0, 0]

/-- A phantom flow: antisymmetric, carrying one unit across the
zero-conductance pair `(0, 1)`. -/
def phantomFlow : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 1; -1, 0]

theorem phantomFlow_antisymm_QA :
    ∀ i j, phantomFlow i j = -phantomFlow j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [phantomFlow]

/-- The phantom even has the unit-demand divergence — it routes one
unit from `0` to `1` in the divergence sense. -/
theorem phantomFlow_divergence_QA :
    flowDivergence phantomFlow = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [flowDivergence, phantomFlow, Fin.sum_univ_two]

/-- **Zero-edge support guard:** the phantom is *not* a flow on the
edgeless network — the support conjunct of `IsFlowOn` is load-bearing.
Dropping it would admit a unit flow on a network with no edges at
all. -/
theorem phantomFlow_not_isFlowOn_QA :
    ¬ IsFlowOn zeroWAdj phantomFlow := by
  rintro ⟨-, hsupp⟩
  have h01 : zeroWAdj 0 1 = 0 := by simp [zeroWAdj]
  exact absurd (hsupp 0 1 h01) (by simp [phantomFlow])

/-- Consequently the phantom is not a unit flow, despite satisfying
every other unit-flow condition. -/
theorem phantomFlow_not_isUnitFlow_QA :
    ¬ IsUnitFlow zeroWAdj 0 1 phantomFlow := by
  rintro ⟨hflow, -⟩
  exact phantomFlow_not_isFlowOn_QA hflow

end SpectralGraphTheory.QA
