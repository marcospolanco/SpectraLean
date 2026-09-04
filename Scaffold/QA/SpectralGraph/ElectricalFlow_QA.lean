/-
  ElectricalFlow_QA.lean

  Purpose
  -------
  QA for `Scaffold.Mathlib.GraphTheory.ElectricalFlow` — proposal
  `proposals/electrical-flow-routing.md`. Step 1 (the electrical
  current, divergence, flow predicates, and the Kirchhoff bridge),
  step 2 (flow energy: the agreement with the Dirichlet energy and the
  effective resistance it routes), step 3 (Thomson's principle:
  attainment at the current, a strict competitor, and the superposition
  decomposition on the triangle), step 4 (Rayleigh monotonicity in
  conductance form: the capacity-increase fixture and the orientation
  guard), and step 5 (the ICP capacity-reinforcement example: the
  `toWAdj` path network with one link reinforced, the decrease computed
  and certified strict).

  Witness plan (proposal QA items 1, 2, 3, 4, 5, 6):

  - **Single edge** (`K₂`): the current matrix, its divergence, and
    the unit-flow instantiation (step 1); the flow energy computed from
    the raw definitions, its agreement with the independently computed
    Dirichlet energy, and its equality with the pinned resistance
    (step 2).
  - **Path** (`0 — 1 — 2`): the unit flow through two edges with the
    internal vertex's divergence computed to `0` (step 1); the energy
    computed to `2` from the raw definitions, cross-checked against
    the pinned Dirichlet energy and resistance values (step 2).
  - **Double-counting guard** (negative): the raw ordered-pair energy
    sum computes to exactly `2` on the unit edge while the energy and
    the Dirichlet energy are `1` — omitting `flowEnergy`'s mandatory
    `1/2` factor would break the agreement numerically.
  - **Negative-conductance witness** (statement shape): on a symmetric
    negative-weight network the agreement theorem still instantiates
    (its hypothesis set is exactly symmetry) while the energy is
    `-1 < 0` — `flowEnergy_nonneg`'s nonnegativity hypothesis is
    load-bearing.
  - **Symmetry guard** (negative): an asymmetric weight matrix makes
    the electrical current fail antisymmetry — `A.IsSymm` is
    load-bearing in `electricalCurrent_antisymm`.
  - **Zero-energy competitor** (negative, energy level): on a real
    edge plus an isolated vertex, an antisymmetric unit-divergence
    phantom routes the unit through zero-conductance pairs and
    dissipates `0 < 1` = the real edge's resistance — every unit-flow
    condition except `IsFlowOn`'s support conjunct, whose removal
    would make Thomson's principle (step 3) assert `1 ≤ 0` here. The
    step-1 phantom on the edgeless network gets its deferred energy
    pinning (`0`) in the same section.

  Step 4 witnesses (the proposal's QA item 2 plus its orientation
  calibration):

  - **Capacity increase (edge):** the unit edge `edgeAdj` against the
    conductance-`2` edge `edge2Adj` — resistance certified to decrease
    `1 → 1/2`, Rayleigh monotonicity instantiated, the decrease
    certified *strict*, and the **orientation guard**: the reverse
    inequality `1 ≤ 1/2` refuted numerically (weights are conductances;
    a resistance-direction statement would be false here).
  - **Competitor transfer (edge):** the `edgeAdj`-electrical current is
    a unit flow on `edge2Adj` (flow-space growth + Kirchhoff), and its
    `edge2Adj`-energy computes to `1/2 ≤ 1` = its `edgeAdj`-energy —
    the comparison half instantiated at computed values.
  - **Partial increase (triangle):** doubling one edge of `K₃`
    (conductance `2` on `0 — 1`, all else equal) strictly decreases the
    resistance `2/3 → 2/5` — the theorem instantiated at a network
    where `A < B` on exactly one undirected edge, with the new
    resistance computed from an independent potential witness.

  Step 5 witnesses (the proposal's ICP proof example — the release's
  short demonstration):

  - **Capacity reinforcement (path, via `SimpleGraph.toWAdj`):** the
    Mathlib `Fin 3` path graph enters through the adapter;
    `increaseConductance … 0 1 1` computes to exactly the concrete
    doubled-path matrix; the reinforced endpoint resistance is pinned
    at `3/2` from an independent potential witness; the one-hypothesis
    reinforcement theorem instantiates (only the original network's
    connectivity hypothesized); and the certified decrease is strict,
    `3/2 < 2` against the adapter-bridged pinned value.

  2026-09-04 addition — the adversarial fence audit (proposal
  `adversarial-fences-electrical-flow-family.md`): the
  hypothesis-necessity pass over every public theorem of
  `ElectricalFlow.lean`, each load-bearing hypothesis closed with a
  fence (negated conclusion at a fixture) plus isolation companion —
  the method of `governance/ADVERSARIAL_REVIEW.md`.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is fully evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.ElectricalFlow
import Scaffold.QA.SpectralGraph.PotentialSolvability_QA
import Scaffold.QA.SpectralGraph.EffectiveResistance_QA
import Scaffold.QA.SpectralGraph.SimpleGraphAdapter_QA
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

/-!
## Flow energy (proposal step 2): values and agreements
-/

/-- **Flow energy (edge):** the unit current on `K₂` dissipates
energy `1`, computed from the raw definitions (both ordered pairs of
the undirected edge contribute `1`, halved) — independent of any
theorem. -/
theorem edge_flowEnergy_value_QA :
    flowEnergy edgeAdj (electricalCurrent edgeAdj ![1, 0]) = 1 := by
  simp [flowEnergy, electricalCurrent, edgeAdj, Fin.sum_univ_two]

/-- **Agreement (edge):** the theorem route equates the current's
energy with the Dirichlet energy of its potential. -/
theorem edge_flowEnergy_agreement_QA :
    flowEnergy edgeAdj (electricalCurrent edgeAdj ![1, 0])
      = quadForm (laplacian edgeAdj) ![1, 0] :=
  flowEnergy_electricalCurrent edgeAdj edgeAdj_isSymm ![1, 0]

/-- **Cross-check (edge):** the theorem-agreed value is `1` on both
sides — the raw energy computation (`edge_flowEnergy_value_QA`), the
independently computed Dirichlet energy (`edge_energy_e0_QA`), and the
pinned resistance (`edge_effectiveResistance_eq_one_QA`) all meet at
the same number. -/
theorem edge_flowEnergy_agreed_value_QA :
    flowEnergy edgeAdj (electricalCurrent edgeAdj ![1, 0]) = 1
      ∧ quadForm (laplacian edgeAdj) ![1, 0] = 1
      ∧ effectiveResistance edgeAdj 0 1 = 1 :=
  ⟨edge_flowEnergy_value_QA, edge_energy_e0_QA,
    edge_effectiveResistance_eq_one_QA⟩

/-- **Energy = resistance (edge):** the step-2 headline instantiated —
the energy dissipated by a unit-demand current is the resistance it
routes. -/
theorem edge_flowEnergy_eq_resistance_QA :
    flowEnergy edgeAdj (electricalCurrent edgeAdj ![1, 0])
      = effectiveResistance edgeAdj 0 1 :=
  flowEnergy_electricalCurrent_eq_effectiveResistance edgeAdj
    edgeAdj_isSymm edgeAdj_nonneg edge_supportGraph_connected
    edge_potential_value_QA

/-- **Nonnegativity interface instantiation (edge).** -/
theorem edge_flowEnergy_nonneg_QA :
    0 ≤ flowEnergy edgeAdj (electricalCurrent edgeAdj ![1, 0]) :=
  flowEnergy_nonneg edgeAdj edgeAdj_nonneg _

/-- **Flow energy (path):** the unit current through the two-edge path
dissipates energy `2` — both edges carry `1`, both ordered pairs of
each edge contribute, the `1/2` halves back to `2`. Computed from the
raw definitions, exercising the sum over four nonzero ordered pairs. -/
theorem path_flowEnergy_value_QA :
    flowEnergy connPathAdj (electricalCurrent connPathAdj ![1, 0, -1])
      = 2 := by
  simp [flowEnergy, electricalCurrent, connPathAdj, Fin.sum_univ_three]
  norm_num

/-- **Energy = resistance (path):** the step-2 headline instantiated on
the path, series edges adding. -/
theorem path_flowEnergy_eq_resistance_QA :
    flowEnergy connPathAdj (electricalCurrent connPathAdj ![1, 0, -1])
      = effectiveResistance connPathAdj 0 2 :=
  flowEnergy_electricalCurrent_eq_effectiveResistance connPathAdj
    connPathAdj_isSymm connPathAdj_nonneg connPath_supportGraph_connected
    path_potential_value_QA

/-- **Cross-check (path):** three independent routes to `2` — the raw
energy computation, the pinned Dirichlet energy
(`path_energy_value_QA`), and the pinned resistance
(`path_effectiveResistance_eq_two_QA`). -/
theorem path_flowEnergy_agreed_value_QA :
    flowEnergy connPathAdj (electricalCurrent connPathAdj ![1, 0, -1])
      = 2
      ∧ quadForm (laplacian connPathAdj) ![1, 0, -1] = 2
      ∧ effectiveResistance connPathAdj 0 2 = 2 :=
  ⟨path_flowEnergy_value_QA, path_energy_value_QA,
    path_effectiveResistance_eq_two_QA⟩

/-!
## Negative witness 3: the double-counting guard

The raw ordered-pair energy sum on the unit edge computes to `2` while
the energy and the Dirichlet energy are `1`: omitting `flowEnergy`'s
`1/2` factor would make the agreement
`flowEnergy A (electricalCurrent A f) = quadForm (laplacian A) f`
assert `2 = 1` on this fixture. The factor is mandatory, not cosmetic
(proposal QA item 4).
-/

/-- **Raw ordered-pair sum (edge):** the *unhalved* ordered-pair energy
sum of the unit current — both entries `(0,1)` and `(1,0)` contribute
`1`. Computed from the raw definitions. -/
theorem edge_raw_pair_sum_two_QA :
    (∑ i, ∑ j, if edgeAdj i j = 0 then (0 : ℝ)
      else electricalCurrent edgeAdj ![1, 0] i j ^ 2 / edgeAdj i j)
      = 2 := by
  simp [electricalCurrent, edgeAdj, Fin.sum_univ_two]
  norm_num

/-- **The double-counting guard:** the raw ordered-pair sum is exactly
twice the flow energy, and the unhalved value `2` differs from the
Dirichlet energy `1` — the `1/2` factor is exactly what makes the
energy agreement true. -/
theorem edge_double_counting_guard_QA :
    (∑ i, ∑ j, if edgeAdj i j = 0 then (0 : ℝ)
      else electricalCurrent edgeAdj ![1, 0] i j ^ 2 / edgeAdj i j)
      = 2 * flowEnergy edgeAdj (electricalCurrent edgeAdj ![1, 0])
      ∧ (2 : ℝ) ≠ quadForm (laplacian edgeAdj) ![1, 0] := by
  refine ⟨?_, ?_⟩
  · rw [edge_raw_pair_sum_two_QA, edge_flowEnergy_value_QA]
    norm_num
  · rw [edge_energy_e0_QA]
    norm_num

/-!
## Negative witness 4: the statement shape — symmetry only, and
nonnegativity load-bearing where it *is* hypothesized

The symmetric negative-weight network `!![0, -1; -1, 0]` (conductance
`-1`: unphysical, but symmetry is all `flowEnergy_electricalCurrent`
assumes). The agreement still instantiates — both sides compute to
`-1` — while `flowEnergy_nonneg` fails on the same fixture: the two
theorems' hypothesis sets are witnessed to be exactly what they say.
-/

/-- Symmetric negative weights: conductance `-1` in both directions. -/
def negWAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, -1; -1, 0]

theorem negWAdj_isSymm : negWAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [negWAdj]

/-- The nonnegativity hypothesis genuinely fails on this fixture. -/
theorem negWAdj_not_nonneg : ¬ ∀ i j, 0 ≤ negWAdj i j := by
  intro h
  have h01 := h 0 1
  simp only [negWAdj] at h01
  norm_num at h01

/-- **Energy value (negative weights):** the unit current dissipates
`-1` — a square over a negative conductance. Computed from the raw
definitions. -/
theorem negWAdj_flowEnergy_value_QA :
    flowEnergy negWAdj (electricalCurrent negWAdj ![1, 0]) = -1 := by
  simp [flowEnergy, electricalCurrent, negWAdj, Fin.sum_univ_two]

/-- **Agreement still holds (statement-shape witness):** the theorem
route applies with symmetry only — both sides compute to `-1`. -/
theorem negWAdj_flowEnergy_agreement_QA :
    flowEnergy negWAdj (electricalCurrent negWAdj ![1, 0])
      = quadForm (laplacian negWAdj) ![1, 0] :=
  flowEnergy_electricalCurrent negWAdj negWAdj_isSymm ![1, 0]

/-- **Nonnegativity is load-bearing:** on the same fixture the energy
is `-1 < 0`, so `flowEnergy_nonneg` fails without its nonnegative
conductances hypothesis. -/
theorem negWAdj_flowEnergy_not_nonneg_QA :
    ¬ 0 ≤ flowEnergy negWAdj (electricalCurrent negWAdj ![1, 0]) := by
  rw [negWAdj_flowEnergy_value_QA]
  norm_num

/-!
## Negative witness 5: the zero-energy competitor (energy level)

The step-1 phantom's deferred energy pinning, and its Thomson-breaking
refinement. On the cheat network — one real conductance-`1` edge
`0 — 1`, vertex `2` isolated — the phantom `cheatFlow` routes the unit
demand `0 → 2 → 1` entirely through zero-conductance pairs: it is
antisymmetric, has exactly the unit divergence, and dissipates *zero*
energy, while the resistance from `0` to `1` is `1`. It fails only
`IsFlowOn`'s support conjunct. This is why that conjunct is
load-bearing for the variational theory (proposal step 3): over
flows-satisfying-everything-except-support, Thomson's principle
`effectiveResistance ≤ flowEnergy θ` would assert `1 ≤ 0` here.
-/

/-- The step-1 phantom's energy on the edgeless network, pinned: every
ordered pair is zero-conductance, so the phantom dissipates nothing —
the deferred step-1 energy computation. On this degenerate network
resistance is the junk fallback `0`, so nothing breaks *here*; the
cheat fixture below breaks the real thing. -/
theorem phantom_flowEnergy_zero_QA :
    flowEnergy zeroWAdj phantomFlow = 0 := by
  simp [flowEnergy, zeroWAdj, Fin.sum_univ_two]

/-- The cheat network: one real conductance-`1` edge `0 — 1`, vertex
`2` isolated. Written entrywise (the repo's pattern for fixtures with
all-zero rows, which the matrix notation's zero-function normalization
would otherwise leave as `vecTail` leftovers). -/
def cheatWAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then (1 : ℝ) else 0

theorem cheatWAdj_isSymm : cheatWAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [cheatWAdj]

theorem cheatWAdj_nonneg : ∀ i j, 0 ≤ cheatWAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [cheatWAdj]

/-- Vertices `0` and `1` are adjacent in the support graph — the real
edge — so the resistance between them is meaningful despite the
isolated vertex. -/
theorem cheatWAdj_reachable :
    (supportGraph cheatWAdj cheatWAdj_isSymm).Reachable 0 1 :=
  (supportGraph_adj.2 ⟨by decide, by simp [cheatWAdj]⟩).reachable

/-- The phantom: routes the unit demand `0 → 2 → 1` — one unit across
each zero-conductance pair, nothing on the real edge. -/
def cheatFlow : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 0, 1; 0, 0, -1; -1, 1, 0]

theorem cheatFlow_antisymm_QA :
    ∀ i j, cheatFlow i j = -cheatFlow j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [cheatFlow]

/-- The phantom has exactly the unit-demand divergence: `+1` at `0`,
`-1` at `1`, `0` at the pass-through vertex `2`. -/
theorem cheatFlow_divergence_QA :
    flowDivergence cheatFlow = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [flowDivergence, cheatFlow, Fin.sum_univ_three]

/-- **Zero energy:** all current rides zero-conductance pairs (the
real edge carries nothing), so the phantom dissipates nothing — the
free route the support conjunct exists to close. -/
theorem cheatFlow_energy_zero_QA :
    flowEnergy cheatWAdj cheatFlow = 0 := by
  simp [flowEnergy, cheatWAdj, cheatFlow, Fin.sum_univ_three]

/-- The phantom is excluded by the support conjunct: it carries
current across the zero-conductance pair `(0, 2)`. -/
theorem cheatFlow_not_isFlowOn_QA :
    ¬ IsFlowOn cheatWAdj cheatFlow := by
  rintro ⟨-, hsupp⟩
  have h02 : cheatWAdj 0 2 = 0 := by simp [cheatWAdj]
  exact absurd (hsupp 0 2 h02) (by simp [cheatFlow])

/-- **The real resistance is `1`:** the potential `![1, 0, 0]` solves
the unit demand across the real edge (the isolated vertex is
irrelevant to it), and reachability pins the value. -/
theorem cheat_resistance_one_QA :
    effectiveResistance cheatWAdj 0 1 = 1 := by
  have hpot : (laplacian cheatWAdj).mulVec ![1, 0, 0]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
    funext i
    fin_cases i <;>
      simp [laplacian, degreeMatrix, deg, cheatWAdj, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_three]
  exact effectiveResistance_eq_of_reachable cheatWAdj cheatWAdj_isSymm
    cheatWAdj_nonneg cheatWAdj_reachable
    ⟨![1, 0, 0], hpot, by norm_num [Matrix.cons_val']⟩

/-- **The zero-energy competitor, composed (support is load-bearing at
the energy level):** the phantom satisfies antisymmetry and the unit
divergence, its energy `0` is strictly below the resistance `1` it
would compete against, and it is excluded by `IsFlowOn` alone. Without
the support conjunct, Thomson's principle (step 3) would assert
`1 ≤ 0` on this fixture. -/
theorem cheat_support_load_bearing_QA :
    (∀ i j, cheatFlow i j = -cheatFlow j i)
      ∧ flowDivergence cheatFlow = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ)
      ∧ flowEnergy cheatWAdj cheatFlow < effectiveResistance cheatWAdj 0 1
      ∧ ¬ IsFlowOn cheatWAdj cheatFlow :=
  ⟨cheatFlow_antisymm_QA, cheatFlow_divergence_QA, by
    rw [cheatFlow_energy_zero_QA, cheat_resistance_one_QA]
    norm_num, cheatFlow_not_isFlowOn_QA⟩

/-!
## Thomson's principle (proposal step 3): attainment, a strict
## competitor, and the superposition decomposition

Witness plan for step 3 (the negative witnesses its statement needs —
the zero-energy competitor excluded by support, the double-counting
factor — are the step-2 fixtures above, referenced below):

- **Attainment (edge):** the theorem's bound instantiated at the
  electrical current itself, where both sides pin to `1` — the minimum
  is achieved by the current, which is step 2's identity.
- **Attainment with a split current (triangle `K₃`):** the smallest
  network with two parallel routes. The unit-demand potential
  `![1, 1/3, 2/3]` solves `L *ᵥ f = e 0 − e 1`, the resistance is
  `2/3`, and the electrical current — which *splits* (`2/3` on the
  direct edge, `1/3` on each path edge) — dissipates exactly `2/3`,
  computed from the raw definitions.
- **Strict competitor (triangle):** the detour unit flow routes the
  whole unit around the two-edge path `0 → 2 → 1`, carrying nothing on
  the direct edge. It is a valid `IsUnitFlow` (antisymmetric, supported,
  correct divergence — all computed), dissipates `2` (computed from the
  raw `flowEnergy`), and Thomson instantiates as the strict bound
  `2/3 < 2` — the electrical current strictly beats the detour, so the
  inequality is not vacuous.
- **Superposition decomposition (triangle):** the difference flow
  `detour − current` is divergence-free (both are unit flows), and the
  integration-by-parts lemma decomposes `2 = 2/3 + 4/3` — the detour's
  energy into the current's plus the difference's, with all three
  values computed independently from the raw definitions.
-/

/-- The unit triangle `K₃`: three vertices, unit conductances — the
smallest network on which two distinct routes between a pair exist, so
unit flows are non-unique and Thomson's minimizer has a genuine
competitor. Entrywise definition (the repo's fixture pattern; the matrix
notation's zero-function normalization leaves `vecTail` leftovers
otherwise). -/
def triAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if i = j then 0 else 1

theorem triAdj_isSymm : triAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [triAdj]

theorem triAdj_nonneg : ∀ i j, 0 ≤ triAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [triAdj]

/-- The support graph of the triangle is connected: vertices `1` and
`2` are both adjacent to `0`. -/
theorem tri_supportGraph_connected :
    (supportGraph triAdj triAdj_isSymm).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
      ⟨by decide, by simp [triAdj]⟩ SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 2) (w := 2)
      ⟨by decide, by simp [triAdj]⟩ SimpleGraph.Walk.nil⟩

/-- **Potential value (triangle):** `f = ![1, 1/3, 2/3]` solves the
unit-demand equation `L *ᵥ f = e 0 − e 1`, computed entrywise from the
definitions. The center vertex `2` sits at the average potential
`(1 + 1/3)/2 = 2/3`. -/
theorem tri_potential_value_QA :
    (laplacian triAdj).mulVec ![1, 1/3, 2/3]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, triAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three] <;>
    norm_num

/-- **Resistance value (triangle):** `R 0 1 = 2/3` — the unit edge in
parallel with the two-edge path of resistance `2`, pinned by the
potential witness. -/
theorem tri_resistance_value_QA :
    effectiveResistance triAdj 0 1 = 2 / 3 :=
  effectiveResistance_eq triAdj triAdj_isSymm triAdj_nonneg
    tri_supportGraph_connected
    ⟨![1, 1/3, 2/3], tri_potential_value_QA, by norm_num [Matrix.cons_val']⟩

/-- **The electrical current splits (triangle):** the potential
`![1, 1/3, 2/3]` drives `2/3` across the direct edge and `1/3` across
each path edge, and the dissipated energy is exactly `2/3` — computed
from the raw `flowEnergy` and `electricalCurrent` definitions. On this
network the minimizer is a genuinely split flow. -/
theorem tri_current_energy_QA :
    flowEnergy triAdj (electricalCurrent triAdj ![1, 1/3, 2/3])
      = 2 / 3 := by
  simp [flowEnergy, electricalCurrent, triAdj, Fin.sum_univ_three]
  norm_num

/-- **Attainment (triangle):** the current's energy is exactly the
resistance it routes — the step-2 identity, instantiated on a network
where the current splits. -/
theorem tri_flowEnergy_eq_resistance_QA :
    flowEnergy triAdj (electricalCurrent triAdj ![1, 1/3, 2/3])
      = effectiveResistance triAdj 0 1 :=
  flowEnergy_electricalCurrent_eq_effectiveResistance triAdj
    triAdj_isSymm triAdj_nonneg tri_supportGraph_connected
    tri_potential_value_QA

/-- **Thomson attained at the current (edge):** the bound instantiated
at the electrical current itself, with both sides pinned to `1` —
`edge_effectiveResistance_eq_one_QA` and `edge_flowEnergy_value_QA`
independently. -/
theorem edge_thomson_attained_QA :
    effectiveResistance edgeAdj 0 1
      ≤ flowEnergy edgeAdj (electricalCurrent edgeAdj ![1, 0])
      ∧ effectiveResistance edgeAdj 0 1 = 1
      ∧ flowEnergy edgeAdj (electricalCurrent edgeAdj ![1, 0]) = 1 :=
  ⟨effectiveResistance_le_flowEnergy edgeAdj edgeAdj_isSymm
      edgeAdj_nonneg edge_supportGraph_connected edge_isUnitFlow_QA,
    edge_effectiveResistance_eq_one_QA, edge_flowEnergy_value_QA⟩

/-- The detour flow on the triangle: routes the whole unit around the
two-edge path `0 → 2 → 1`, carrying nothing on the direct edge
`0 — 1`. Entrywise definition for the same fixture-hygiene reason. -/
def detourFlow : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then (1 : ℝ)
    else if (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 2) then (-1 : ℝ) else 0

theorem detourFlow_antisymm_QA :
    ∀ i j, detourFlow i j = -detourFlow j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [detourFlow]

theorem detourFlow_isFlowOn_QA : IsFlowOn triAdj detourFlow :=
  ⟨fun i j => by
      fin_cases i <;> fin_cases j <;> simp [detourFlow],
    fun i j h => by
      fin_cases i <;> fin_cases j <;>
        simp [triAdj, detourFlow] at h ⊢⟩

/-- The detour has exactly the unit-demand divergence: `+1` at `0`,
`-1` at `1`, conservation at `2` — computed from the raw definition. -/
theorem detourFlow_divergence_QA :
    flowDivergence detourFlow = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;> simp [flowDivergence, detourFlow, Fin.sum_univ_three]

theorem detourFlow_isUnitFlow_QA : IsUnitFlow triAdj 0 1 detourFlow :=
  ⟨detourFlow_isFlowOn_QA, detourFlow_divergence_QA⟩

/-- **Detour energy:** the detour dissipates `2` — two unit resistors in
series, the whole current through each — computed from the raw
`flowEnergy` definition over all six nonzero ordered pairs. -/
theorem detour_energy_two_QA : flowEnergy triAdj detourFlow = 2 := by
  simp [flowEnergy, triAdj, detourFlow, Fin.sum_univ_three]
  norm_num

/-- **Thomson instantiated (triangle):** the theorem's bound at the
detour competitor. -/
theorem thomson_detour_QA :
    effectiveResistance triAdj 0 1 ≤ flowEnergy triAdj detourFlow :=
  effectiveResistance_le_flowEnergy triAdj triAdj_isSymm triAdj_nonneg
    tri_supportGraph_connected detourFlow_isUnitFlow_QA

/-- **The bound is strict at the detour:** `2/3 < 2` — the electrical
current strictly beats the detour, so Thomson's inequality is not
vacuous on a network with competing routes. -/
theorem thomson_detour_strict_QA :
    effectiveResistance triAdj 0 1 < flowEnergy triAdj detourFlow := by
  rw [tri_resistance_value_QA, detour_energy_two_QA]
  norm_num

/-- **The difference flow's energy:** the detour minus the electrical
current dissipates `4/3` — computed from the raw definitions
independently of the superposition lemma. -/
theorem detour_minus_current_energy_QA :
    flowEnergy triAdj (detourFlow - electricalCurrent triAdj ![1, 1/3, 2/3])
      = 4 / 3 := by
  simp [flowEnergy, electricalCurrent, detourFlow, triAdj,
    Matrix.sub_apply, Fin.sum_univ_three]
  norm_num

/-- The difference flow is a flow (both summands are), with zero
divergence (both are unit flows of the same demand). -/
theorem detour_minus_current_divergence_zero_QA :
    flowDivergence (detourFlow - electricalCurrent triAdj ![1, 1/3, 2/3])
      = 0 := by
  rw [flowDivergence_sub, detourFlow_divergence_QA,
    flowDivergence_electricalCurrent, tri_potential_value_QA, sub_self]

/-- **The superposition decomposition:** the integration-by-parts lemma
splits the detour's energy into the current's plus the difference's.
All three values are pinned independently above (`2`, `2/3`, `4/3`), and
the composed identity checks `2 = 2/3 + 4/3` — the decomposition
consumes the lemma, the divergence computation, and the potential value,
so an error in any breaks this witness. -/
theorem thomson_split_decomposition_QA :
    flowEnergy triAdj detourFlow = 2 / 3 + 4 / 3 := by
  have h1 :=
    flowEnergy_add_of_flowDivergence_eq_zero triAdj ![1, 1/3, 2/3]
      (isFlowOn_sub triAdj detourFlow_isFlowOn_QA
        (isFlowOn_electricalCurrent triAdj triAdj_isSymm _))
      detour_minus_current_divergence_zero_QA
  have hsum : electricalCurrent triAdj ![1, 1/3, 2/3]
      + (detourFlow - electricalCurrent triAdj ![1, 1/3, 2/3])
      = detourFlow := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply]
    ring
  rw [hsum] at h1
  rw [h1, tri_current_energy_QA, detour_minus_current_energy_QA]

/-!
## Rayleigh monotonicity (proposal step 4): capacity increase,
## competitor transfer, and the orientation guard
-/

/-- The conductance-`2` edge: the capacity-increase fixture of the
proposal's QA item 2 — `edgeAdj` with its single conductance doubled. -/
def edge2Adj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 2; 2, 0]

theorem edge2Adj_isSymm : edge2Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [edge2Adj]

theorem edge2Adj_nonneg : ∀ i j, 0 ≤ edge2Adj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [edge2Adj]

/-- Entrywise `edgeAdj ≤ edge2Adj`: one conductance raised, none
lowered. -/
theorem edge_le_edge2Adj : ∀ i j, edgeAdj i j ≤ edge2Adj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [edgeAdj, edge2Adj]

/-- The conductance-`2` edge is connected. -/
theorem edge2_supportGraph_connected :
    (supportGraph edge2Adj edge2Adj_isSymm).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
      (supportGraph_adj.2 ⟨by decide, by simp [edge2Adj]⟩)
      SimpleGraph.Walk.nil⟩

/-- **Potential value (conductance-`2` edge):** `f = ![1/2, 0]` solves
the unit-demand equation — the voltage drop halves when the conductance
doubles. Computed entrywise from the definitions. -/
theorem edge2_potential_value_QA :
    (laplacian edge2Adj).mulVec ![1/2, 0]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, edge2Adj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_two]

/-- **Resistance value (conductance-`2` edge):** `R 0 1 = 1/2` — the
capacity increase `1 → 2` halves the resistance, pinned by the potential
witness (voltage drop `1/2 − 0`). -/
theorem edge2_resistance_value_QA :
    effectiveResistance edge2Adj 0 1 = 1 / 2 :=
  effectiveResistance_eq edge2Adj edge2Adj_isSymm edge2Adj_nonneg
    edge2_supportGraph_connected
    ⟨![1/2, 0], edge2_potential_value_QA, by norm_num [Matrix.cons_val']⟩

/-- **Rayleigh monotonicity instantiated (QA item 2):** doubling the
only conductance cannot increase the resistance. -/
theorem rayleigh_edge_QA :
    effectiveResistance edge2Adj 0 1 ≤ effectiveResistance edgeAdj 0 1 :=
  effectiveResistance_le_of_le edgeAdj edge2Adj edgeAdj_isSymm
    edgeAdj_nonneg edge_supportGraph_connected edge2Adj_isSymm
    edge2Adj_nonneg edge2_supportGraph_connected edge_le_edge2Adj 0 1

/-- **The decrease is strict and certified:** `1/2 < 1`, from the two
independently pinned resistance values. -/
theorem rayleigh_edge_strict_QA :
    effectiveResistance edge2Adj 0 1 < effectiveResistance edgeAdj 0 1 := by
  rw [edge2_resistance_value_QA, edge_effectiveResistance_eq_one_QA]
  norm_num

/-- **Orientation guard (proposal calibration):** the *reverse*
inequality is false on this fixture — `1 ≤ 1/2` fails numerically.
Weights are conductances, so `R_B ≤ R_A` is the only direction that can
hold; a resistance-direction restatement would be a statement bug, and
this witness would catch it. -/
theorem rayleigh_orientation_guard_QA :
    ¬ (effectiveResistance edgeAdj 0 1
      ≤ effectiveResistance edge2Adj 0 1) := by
  rw [edge_effectiveResistance_eq_one_QA, edge2_resistance_value_QA]
  norm_num

/-- **Competitor transfer:** the `edgeAdj`-electrical current (the unit
flow computed in `edge_current_matrix_QA`) is a valid unit flow on the
doubled network — flow-space growth supplies support, the Kirchhoff
bridge the divergence. This is the interface the headline proof routes
through, instantiated on computed objects. -/
theorem edge_current_isUnitFlow_on_edge2_QA :
    IsUnitFlow edge2Adj 0 1 (electricalCurrent edgeAdj ![1, 0]) :=
  ⟨isFlowOn_of_le (isFlowOn_electricalCurrent edgeAdj edgeAdj_isSymm _)
      edgeAdj_nonneg edge_le_edge2Adj, by
    rw [flowDivergence_electricalCurrent, edge_potential_value_QA]⟩

/-- **Cross-network energy value:** the `edgeAdj`-current dissipates
`1/2` on the doubled network — computed from the raw `flowEnergy`
definition (current `1` across conductance `2`, both ordered pairs,
halved). -/
theorem edge2_crossEnergy_value_QA :
    flowEnergy edge2Adj (electricalCurrent edgeAdj ![1, 0]) = 1 / 2 := by
  simp [flowEnergy, electricalCurrent, edgeAdj, edge2Adj, Fin.sum_univ_two]

/-- **The comparison half instantiated:** `1/2 ≤ 1` — the transferred
competitor's energy on `B` is at most its energy on `A`, with both
sides independently computed (`edge_flowEnergy_value_QA` pins the
`A`-side at `1`). -/
theorem edge_crossEnergy_le_QA :
    flowEnergy edge2Adj (electricalCurrent edgeAdj ![1, 0])
      ≤ flowEnergy edgeAdj (electricalCurrent edgeAdj ![1, 0])
      ∧ flowEnergy edge2Adj (electricalCurrent edgeAdj ![1, 0]) = 1 / 2
      ∧ flowEnergy edgeAdj (electricalCurrent edgeAdj ![1, 0]) = 1 :=
  ⟨flowEnergy_le_of_le
      (isFlowOn_electricalCurrent edgeAdj edgeAdj_isSymm _)
      edgeAdj_nonneg edge_le_edge2Adj,
    edge2_crossEnergy_value_QA, edge_flowEnergy_value_QA⟩

/-!
### Partial increase: doubling one edge of the triangle
-/

/-- The triangle with the direct edge `0 — 1` doubled: conductance `2`
there, unit conductances elsewhere. `triAdj ≤ triDoubledAdj` entrywise
with a strict increase on exactly one undirected edge — the partial
capacity reinforcement. Entrywise definition (fixture-hygiene pattern). -/
def triDoubledAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then (2 : ℝ)
    else if i = j then 0 else 1

theorem triDoubledAdj_isSymm : triDoubledAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [triDoubledAdj]

theorem triDoubledAdj_nonneg : ∀ i j, 0 ≤ triDoubledAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [triDoubledAdj]

/-- One edge raised, none lowered: `triAdj ≤ triDoubledAdj` entrywise. -/
theorem tri_le_triDoubledAdj : ∀ i j, triAdj i j ≤ triDoubledAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [triAdj, triDoubledAdj]

/-- The doubled triangle stays connected. -/
theorem triDoubled_supportGraph_connected :
    (supportGraph triDoubledAdj triDoubledAdj_isSymm).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
      (supportGraph_adj.2 ⟨by decide, by simp [triDoubledAdj]⟩)
      SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 2) (w := 2)
      (supportGraph_adj.2 ⟨by decide, by simp [triDoubledAdj]⟩)
      SimpleGraph.Walk.nil⟩

/-- **Potential value (doubled triangle):** `f = ![2/5, 0, 1/5]` solves
the unit-demand equation `L *ᵥ f = e 0 − e 1` — the center vertex sits
at `(2/5 + 0)/2 = 1/5` by symmetry of its two unit conductances, and
the direct voltage drop is `2/5`. Computed entrywise from the
definitions. -/
theorem triDoubled_potential_value_QA :
    (laplacian triDoubledAdj).mulVec ![2/5, 0, 1/5]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, triDoubledAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three] <;>
    norm_num

/-- **Resistance value (doubled triangle):** `R 0 1 = 2/5` — the direct
conductance-`2` edge (resistance `1/2`) in parallel with the two-edge
path (resistance `2`), and parallel resistances combine as
`(1/2 · 2)/(1/2 + 2) = 2/5`. Pinned here by the potential witness
(voltage drop `2/5 − 0`). -/
theorem triDoubled_resistance_value_QA :
    effectiveResistance triDoubledAdj 0 1 = 2 / 5 :=
  effectiveResistance_eq triDoubledAdj triDoubledAdj_isSymm
    triDoubledAdj_nonneg triDoubled_supportGraph_connected
    ⟨![2/5, 0, 1/5], triDoubled_potential_value_QA,
      by norm_num [Matrix.cons_val']⟩

/-- **Rayleigh monotonicity instantiated (partial increase):** raising
one conductance of a network with competing routes cannot increase the
resistance across it. -/
theorem rayleigh_tri_QA :
    effectiveResistance triDoubledAdj 0 1
      ≤ effectiveResistance triAdj 0 1 :=
  effectiveResistance_le_of_le triAdj triDoubledAdj triAdj_isSymm
    triAdj_nonneg tri_supportGraph_connected triDoubledAdj_isSymm
    triDoubledAdj_nonneg triDoubled_supportGraph_connected
    tri_le_triDoubledAdj 0 1

/-- **Strict partial increase:** `2/5 < 2/3` — reinforcing one edge of
the triangle strictly helps, from the two independently pinned values. -/
theorem rayleigh_tri_strict_QA :
    effectiveResistance triDoubledAdj 0 1
      < effectiveResistance triAdj 0 1 := by
  rw [triDoubled_resistance_value_QA, tri_resistance_value_QA]
  norm_num

/-!
## Capacity reinforcement (proposal step 5): the ICP proof example

The release-facing demonstration: a Mathlib `SimpleGraph` enters
through the `toWAdj` adapter, one link's capacity is reinforced with
`increaseConductance`, and the one-hypothesis theorem certifies the
routing resistance cannot worsen — with the improvement itself computed
numerically from independent potential witnesses.
-/

/-- **Adapter bridge:** the Mathlib path graph's adapter weights are
exactly the `connPathAdj` fixture — the `toWAdj` world and the weighted
fixture world compute the same network, entry for entry. -/
theorem path3_toWAdj_eq_connPathAdj :
    pathGraph3.toWAdj = connPathAdj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SimpleGraph.toWAdj_apply, connPathAdj, pathGraph3]

/-- The reinforced path network as a concrete matrix: the `Fin 3` path
with the `0 — 1` conductance doubled (`1 → 2`), the `1 — 2` link left
alone. -/
def pathDoubledAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 2, 0; 2, 0, 1; 0, 1, 0]

theorem pathDoubledAdj_isSymm : pathDoubledAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [pathDoubledAdj]

theorem pathDoubledAdj_nonneg : ∀ i j, 0 ≤ pathDoubledAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pathDoubledAdj]

/-- **The reinforcement computes:** reinforcing the Mathlib path
graph's `0 — 1` link by `δ = 1` yields exactly the concrete
doubled-path matrix — the ICP operation evaluated on `toWAdj` weights,
entry for entry against the raw `if`-definition. -/
theorem path3_reinforced_eq_pathDoubled_QA :
    increaseConductance pathGraph3.toWAdj 0 1 1 = pathDoubledAdj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [increaseConductance, pathDoubledAdj, SimpleGraph.toWAdj_apply,
      pathGraph3] <;>
    norm_num

/-- The doubled path stays connected: explicit walks to every vertex
through the reinforced `0 — 1` link and the untouched `1 — 2` link
(computed independently of the connectivity adapter the headline
theorem consumes). -/
theorem pathDoubled_supportGraph_connected :
    (supportGraph pathDoubledAdj pathDoubledAdj_isSymm).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
      (supportGraph_adj.2 ⟨by decide, by simp [pathDoubledAdj]⟩)
      SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 2)
      (supportGraph_adj.2 ⟨by decide, by simp [pathDoubledAdj]⟩)
      (SimpleGraph.Walk.cons (u := 1) (v := 2) (w := 2)
        (supportGraph_adj.2 ⟨by decide, by simp [pathDoubledAdj]⟩)
        SimpleGraph.Walk.nil)⟩

/-- **Potential value (reinforced path):** `f = ![1/2, 0, −1]` solves
the unit-demand equation `L *ᵥ f = e 0 − e 2` on the reinforced
network — the reinforced link (conductance `2`) carries the same unit
current at half the voltage drop. Computed entrywise from the
definitions. -/
theorem pathDoubled_potential_value_QA :
    (laplacian pathDoubledAdj).mulVec ![1/2, 0, -1]
      = Pi.single 0 (1 : ℝ) - Pi.single 2 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, pathDoubledAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three]

/-- **Resistance value (reinforced path):** `R 0 2 = 3/2` — the
reinforced link (resistance `1/2`) in series with the untouched link
(resistance `1`), pinned by the potential witness (voltage drop
`1/2 − (−1)`). -/
theorem pathDoubled_resistance_value_QA :
    effectiveResistance pathDoubledAdj 0 2 = 3 / 2 :=
  effectiveResistance_eq pathDoubledAdj pathDoubledAdj_isSymm
    pathDoubledAdj_nonneg pathDoubled_supportGraph_connected
    ⟨![1/2, 0, -1], pathDoubled_potential_value_QA,
      by norm_num [Matrix.cons_val']⟩

/-- **Capacity reinforcement, the ICP proof example (proposal step 5,
headline):** raising the `0 — 1` capacity of the path network from `1`
to `2` cannot increase the end-to-end routing resistance `0 → 2`. The
one-hypothesis form: only the original network's connectivity is
assumed (through the adapter roundtrip it *is* `pathGraph3`'s, already
proved) — the reinforced network's connectivity is derived inside the
theorem. -/
theorem path3_reinforcement_QA :
    effectiveResistance (increaseConductance pathGraph3.toWAdj 0 1 1) 0 2
      ≤ effectiveResistance pathGraph3.toWAdj 0 2 :=
  effectiveResistance_le_increaseConductance pathGraph3.toWAdj
    (SimpleGraph.toWAdj_symm pathGraph3)
    (SimpleGraph.toWAdj_nonneg pathGraph3)
    (by rw [supportGraph_toWAdj_eq_self]; exact path3_connected)
    0 1 0 2 1 zero_le_one

/-- **The certified decrease is strict:** the reinforced endpoint
resistance is `3/2` (independently pinned above) and the original is
`2` (the step-2-era pinned value, reached through the adapter bridge).
Reinforcing one link of a two-link path certifiably lowers the
end-to-end routing resistance. -/
theorem path3_reinforcement_strict_QA :
    effectiveResistance (increaseConductance pathGraph3.toWAdj 0 1 1) 0 2
      < effectiveResistance pathGraph3.toWAdj 0 2 := by
  rw [path3_reinforced_eq_pathDoubled_QA, pathDoubled_resistance_value_QA,
    path3_toWAdj_eq_connPathAdj, path_effectiveResistance_eq_two_QA]
  norm_num

/-!
## Adversarial fence audit (proposal
`adversarial-fences-electrical-flow-family.md`, 2026-09-04)

The hypothesis-necessity pass over `ElectricalFlow.lean`'s public
theorems (the method of `governance/ADVERSARIAL_REVIEW.md`; eighth
application, the electrical cluster's second). Each fence is the
negation of a theorem's conclusion at a concrete instantiation where
exactly one hypothesis is dropped; each isolation companion verifies
every other hypothesis genuine and the dropped one failing. The
Step-0 survey's priced list: 22 fences, the P4 records (the energy
identity's `hnneg`/`hconn` truth-removable given `hA`+`hf`; Thomson's
`hconn` implied by `hθ`; Rayleigh's `hnonnegB` by domination and its
`hconnB` by the connectivity adapter — the review pilot's own
finding), and the structural classifications — all in the proposal.
-/

/-!
### The asymmetric 4-path fixture: the energy agreement's `hA`

`asymPath4Adj` asymmetrically weights only the two end links
(`2/1` and `1/2`); the interior link is symmetric. The unit demand
`e 0 − e 3` is genuinely solvable — `f = ![3/2, 1, 1/2, 0]` — but the
ordered-pair energy `(1/2)∑ A i j (f i − f j)²` and the quadratic form
`fᵀ(D−A)f` differ by exactly the row-sum/column-sum correction
`(1/2)∑ⱼ f j² (rowsum_j − colsum_j) = 1/2`: `1 ≠ 3/2`.
-/

/-- The asymmetric 4-path: end links weighted `2` down / `1` up, the
interior link symmetric unit. The smallest fixture whose demand
potential exists *and* whose row sums differ from its column sums on
the potential's support. Entrywise definition (the repo's `Fin 4`
fixture pattern). -/
def asymPath4Adj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    if (i = 0 ∧ j = 1) ∨ (i = 3 ∧ j = 2) then (2 : ℝ)
    else if (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)
      ∨ (i = 2 ∧ j = 3) then (1 : ℝ) else 0

theorem asymPath4Adj_not_isSymm : ¬ asymPath4Adj.IsSymm := by
  intro h
  have h01 := h.apply 0 1
  simp [asymPath4Adj] at h01

/-- **The demand is genuinely solvable:** `f = ![3/2, 1, 1/2, 0]`
solves `L *ᵥ f = e 0 − e 3` entrywise — the hypothesis the fence
keeps. -/
theorem asymPath4_potential_value_QA :
    (laplacian asymPath4Adj).mulVec ![3 / 2, 1, 1 / 2, 0]
      = Pi.single 0 (1 : ℝ) - Pi.single 3 (1 : ℝ) := by
  funext i
  rw [laplacian_mulVec_apply]
  fin_cases i <;>
    simp [asymPath4Adj, Fin.sum_univ_four, Pi.single_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.head_cons] <;>
    norm_num

/-- **Fixture-local voltage pinning:** every solution `g` of the
demand has voltage difference `g 0 − g 3 = 3/2` — linarith over the
row equations, no symmetry and no reachability needed. This is what
pins the total function on asymmetric input, where no hypothesis-free
uniqueness lemma exists. -/
theorem asymPath4_voltage_fixed_QA {r : ℝ}
    (h : IsEffectiveResistance asymPath4Adj 0 3 r) : r = 3 / 2 := by
  obtain ⟨g, hg, hfr⟩ := h
  have e0 := congrFun hg 0
  have e1 := congrFun hg 1
  have e3 := congrFun hg 3
  rw [laplacian_mulVec_apply] at e0 e1 e3
  simp [asymPath4Adj, Fin.sum_univ_four, Pi.single_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.head_cons] at e0 e1 e3
  linarith

/-- **The resistance, pinned:** `3/2` — the chosen witness's voltage
difference, forced by the fixture-local pinning above. -/
theorem asymPath4_resistance_QA :
    effectiveResistance asymPath4Adj 0 3 = 3 / 2 := by
  have hex : ∃ r : ℝ, IsEffectiveResistance asymPath4Adj 0 3 r :=
    ⟨3 / 2, ![3 / 2, 1, 1 / 2, 0], asymPath4_potential_value_QA,
      by norm_num [Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.head_cons]⟩
  simp only [effectiveResistance, dif_pos hex]
  exact asymPath4_voltage_fixed_QA (Classical.choose_spec hex)

/-- **The ordered-pair energy:** `1`, computed from the raw
definitions. -/
theorem asymPath4_flowEnergy_value_QA :
    flowEnergy asymPath4Adj (electricalCurrent asymPath4Adj ![3 / 2, 1, 1 / 2, 0])
      = 1 := by
  simp [flowEnergy, electricalCurrent, asymPath4Adj, Fin.sum_univ_four]
  norm_num

/-- **The quadratic form:** `3/2` — `f ⬝ᵥ (L *ᵥ f) = f 0 − f 3`, the
solution-level identity's value, computed independently. -/
theorem asymPath4_quadForm_value_QA :
    quadForm (laplacian asymPath4Adj) ![3 / 2, 1, 1 / 2, 0] = 3 / 2 := by
  rw [quadForm, asymPath4_potential_value_QA, Matrix.dotProduct_sub,
    Matrix.dotProduct_single, Matrix.dotProduct_single]
  norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.head_cons]

/-- **Fence (`flowEnergy_electricalCurrent`, `hA`):** the energy
agreement fails on the asymmetric fixture — `1 ≠ 3/2`. Symmetry is
what identifies the quadratic form with the ordered-pair sum (row
sums against column sums); the dropped statement is false. -/
theorem effF_agreement_hA_fence_QA :
    ¬ (flowEnergy asymPath4Adj (electricalCurrent asymPath4Adj ![3 / 2, 1, 1 / 2, 0])
      = quadForm (laplacian asymPath4Adj) ![3 / 2, 1, 1 / 2, 0]) := by
  rw [asymPath4_flowEnergy_value_QA, asymPath4_quadForm_value_QA]
  norm_num

/-- **Isolation:** the theorem's only hypothesis (`hA`) genuinely
fails, and the potential equation is genuinely solved — the failure is
exactly symmetry. -/
theorem effF_agreement_hA_isolation_QA :
    ¬ asymPath4Adj.IsSymm
      ∧ (laplacian asymPath4Adj).mulVec ![3 / 2, 1, 1 / 2, 0]
        = Pi.single 0 (1 : ℝ) - Pi.single 3 (1 : ℝ) :=
  ⟨asymPath4Adj_not_isSymm, asymPath4_potential_value_QA⟩

/-- **Fence (`flowEnergy_electricalCurrent_eq_effectiveResistance`,
`hA`):** the routed energy is `1` against the pinned resistance `3/2`
— the identity fails on asymmetric input even with the demand
genuinely solved. -/
theorem effF_energyIdentity_hA_fence_QA :
    ¬ (flowEnergy asymPath4Adj (electricalCurrent asymPath4Adj ![3 / 2, 1, 1 / 2, 0])
      = effectiveResistance asymPath4Adj 0 3) := by
  rw [asymPath4_flowEnergy_value_QA, asymPath4_resistance_QA]
  norm_num

/-!
### The cyclic phantom: the superposition lemma's support clause
-/

/-- The antisymmetric 3-cycle flow `0 → 1 → 2 → 0`: divergence-free
at every vertex, but it rides every zero-conductance pair of a network
without those edges. -/
def cycleFlow : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, -1; -1, 0, 1; 1, -1, 0]

theorem cycleFlow_antisymm_QA :
    ∀ i j, cycleFlow i j = -cycleFlow j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [cycleFlow]

/-- Divergence-free at every vertex — the hypothesis the fence keeps. -/
theorem cycleFlow_divergence_zero_QA :
    flowDivergence cycleFlow = 0 := by
  funext i
  fin_cases i <;> simp [flowDivergence, cycleFlow, Fin.sum_univ_three]

/-- The cyclic phantom is excluded by support on the cheat network —
it rides the zero-conductance pairs `(0, 2)` and `(1, 2)`. -/
theorem cycleFlow_not_isFlowOn_cheat_QA :
    ¬ IsFlowOn cheatWAdj cycleFlow := by
  rintro ⟨-, hsupp⟩
  have h02 : cheatWAdj 0 2 = 0 := by simp [cheatWAdj]
  exact absurd (hsupp 0 2 h02) (by simp [cycleFlow])

theorem cheat_current_energy_QA :
    flowEnergy cheatWAdj (electricalCurrent cheatWAdj ![1, 0, 0]) = 1 := by
  simp [flowEnergy, electricalCurrent, cheatWAdj, Fin.sum_univ_three]

theorem cycleFlow_energy_QA : flowEnergy cheatWAdj cycleFlow = 1 := by
  simp [flowEnergy, cheatWAdj, cycleFlow, Fin.sum_univ_three]

theorem cheat_plus_cycle_energy_QA :
    flowEnergy cheatWAdj (electricalCurrent cheatWAdj ![1, 0, 0] + cycleFlow)
      = 4 := by
  simp [flowEnergy, electricalCurrent, cheatWAdj, cycleFlow,
    Matrix.add_apply, Fin.sum_univ_three]
  norm_num

/-- **Fence (`flowEnergy_add_of_flowDivergence_eq_zero`, `hd`):**
perturbing the current by the cyclic phantom — divergence-free but
*unsupported* — does not split the energy: `4 ≠ 2 = 1 + 1`. The
integration-by-parts cross term dies only because a flow vanishes on
zero branches; a phantom that rides them leaves it alive. -/
theorem effF_superposition_hd_fence_QA :
    ¬ (flowEnergy cheatWAdj (electricalCurrent cheatWAdj ![1, 0, 0] + cycleFlow)
      = flowEnergy cheatWAdj (electricalCurrent cheatWAdj ![1, 0, 0])
        + flowEnergy cheatWAdj cycleFlow) := by
  rw [cheat_plus_cycle_energy_QA, cheat_current_energy_QA,
    cycleFlow_energy_QA]
  norm_num

/-- **Isolation:** the divergence hypothesis is genuine (`= 0`
pinned), every other flow property holds except support — exactly
`IsFlowOn` fails. -/
theorem effF_superposition_hd_isolation_QA :
    flowDivergence cycleFlow = 0 ∧ ¬ IsFlowOn cheatWAdj cycleFlow :=
  ⟨cycleFlow_divergence_zero_QA, cycleFlow_not_isFlowOn_cheat_QA⟩

/-!
### The doubled current: the superposition lemma's divergence clause
-/

/-- Twice the unit current on the edge: still antisymmetric and
supported (a genuine flow), but its divergence is `[2, −2]`. -/
def doubleCurrent : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 2; -2, 0]

theorem doubleCurrent_isFlowOn_QA :
    IsFlowOn edgeAdj doubleCurrent := by
  refine ⟨fun i j => by
      fin_cases i <;> fin_cases j <;> simp [doubleCurrent],
    fun i j h => by
      fin_cases i <;> fin_cases j <;> simp [edgeAdj] at h <;>
        simp [doubleCurrent]⟩

theorem doubleCurrent_divergence_QA :
    flowDivergence doubleCurrent = ![2, -2] := by
  funext i
  fin_cases i <;> simp [flowDivergence, doubleCurrent, Fin.sum_univ_two]

theorem doubleCurrent_energy_QA :
    flowEnergy edgeAdj doubleCurrent = 4 := by
  simp [flowEnergy, edgeAdj, doubleCurrent, Fin.sum_univ_two]
  norm_num

theorem triple_current_energy_QA :
    flowEnergy edgeAdj (electricalCurrent edgeAdj ![1, 0] + doubleCurrent)
      = 9 := by
  simp [flowEnergy, electricalCurrent, edgeAdj, doubleCurrent,
    Matrix.add_apply, Fin.sum_univ_two]
  norm_num

/-- **Fence (`flowEnergy_add_of_flowDivergence_eq_zero`, `hdiv`):**
perturbing by a genuine flow with *nonzero* divergence does not split
the energy either: `9 ≠ 5 = 1 + 4`. -/
theorem effF_superposition_hdiv_fence_QA :
    ¬ (flowEnergy edgeAdj (electricalCurrent edgeAdj ![1, 0] + doubleCurrent)
      = flowEnergy edgeAdj (electricalCurrent edgeAdj ![1, 0])
        + flowEnergy edgeAdj doubleCurrent) := by
  rw [triple_current_energy_QA, edge_flowEnergy_value_QA,
    doubleCurrent_energy_QA]
  norm_num

/-- **Isolation:** `doubleCurrent` is a genuine flow on the edge
(antisymmetric, supported); only the divergence clause fails. -/
theorem effF_superposition_hdiv_isolation_QA :
    IsFlowOn edgeAdj doubleCurrent ∧ flowDivergence doubleCurrent ≠ 0 :=
  ⟨doubleCurrent_isFlowOn_QA, by
    rw [doubleCurrent_divergence_QA]
    intro h
    have := congrFun h 0
    norm_num at this⟩

/-!
### The both-negative-edges route: Thomson's `hnonneg`

On the delivered signed fixture `sgnK4Adj` (symmetric, connected
support — the two clauses the 2026-08-20 witness could not make
genuine), the unit flow `0 → 3 → 1 → 2` rides *both* negative edges:
antisymmetric, supported (negative is not zero), divergence exactly
`e 0 − e 2`, and energy `−1 < 0` — below the delivered junk
resistance `0` between those vertices.
-/

/-- The unit flow `0 → 3 → 1 → 2` on the signed 4-cycle: one unit
across each of the two negative edges and the positive edge `(3, 1)`. -/
def negRouteFlow : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 1) ∨ (i = 1 ∧ j = 2) then (1 : ℝ)
    else if (i = 3 ∧ j = 0) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 1) then (-1 : ℝ) else 0

theorem negRouteFlow_antisymm_QA :
    ∀ i j, negRouteFlow i j = -negRouteFlow j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [negRouteFlow]

theorem negRouteFlow_isFlowOn_QA : IsFlowOn sgnK4Adj negRouteFlow :=
  ⟨negRouteFlow_antisymm_QA, fun i j h => by
    fin_cases i <;> fin_cases j <;> simp [sgnK4Adj] at h <;>
      simp [negRouteFlow]⟩

theorem negRouteFlow_divergence_QA :
    flowDivergence negRouteFlow
      = Pi.single 0 (1 : ℝ) - Pi.single 2 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [flowDivergence, negRouteFlow, Fin.sum_univ_four]

theorem negRouteFlow_isUnitFlow_QA :
    IsUnitFlow sgnK4Adj 0 2 negRouteFlow :=
  ⟨negRouteFlow_isFlowOn_QA, negRouteFlow_divergence_QA⟩

theorem negRouteFlow_energy_QA :
    flowEnergy sgnK4Adj negRouteFlow = -1 := by
  simp [flowEnergy, sgnK4Adj, negRouteFlow, Fin.sum_univ_four]

/-- **Fence (`effectiveResistance_le_flowEnergy`, `hnonneg`):** the
dropped statement reads `0 ≤ −1` — the junk resistance between the
signed fixture's `0` and `2` against the genuinely negative energy of
a genuine unit flow. Nonnegativity is what keeps energies above
resistances. -/
theorem effF_thomson_hnn_fence_QA :
    ¬ (effectiveResistance sgnK4Adj 0 2
      ≤ flowEnergy sgnK4Adj negRouteFlow) := by
  rw [sgnK4_fallback_zero_QA, negRouteFlow_energy_QA]
  norm_num

/-- **Isolation:** every other hypothesis is genuine at the fixture —
symmetry and connectivity delivered, the unit-flow property pinned
here — and nonnegativity fails, delivered. -/
theorem effF_thomson_hnn_isolation_QA :
    sgnK4Adj.IsSymm
      ∧ (supportGraph sgnK4Adj sgnK4Adj_isSymm).Connected
      ∧ IsUnitFlow sgnK4Adj 0 2 negRouteFlow
      ∧ ¬ (∀ i j : Fin 4, 0 ≤ sgnK4Adj i j) :=
  ⟨sgnK4Adj_isSymm, sgnK4_supportGraph_connected,
    negRouteFlow_isUnitFlow_QA, sgnK4Adj_not_nonneg⟩

/-!
### Flow-space transfer (`isFlowOn_of_le`): nonnegativity and
### domination
-/

/-- The phantom *is* a flow on the negative-conductance network: its
only zero entries are diagonal, and the phantom carries nothing
there. -/
theorem phantom_isFlowOn_negWAdj_QA : IsFlowOn negWAdj phantomFlow :=
  ⟨phantomFlow_antisymm_QA, fun i j h => by
    fin_cases i <;> fin_cases j <;> simp [negWAdj] at h <;>
      simp [phantomFlow]⟩

theorem negWAdj_le_zeroWAdj : ∀ i j, negWAdj i j ≤ zeroWAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [negWAdj, zeroWAdj]

/-- **Fence (`isFlowOn_of_le`, `hnonneg`):** transferring the phantom
from the signed network into the dominating-but-zeroed network fails
— the conclusion is the delivered `phantomFlow_not_isFlowOn_QA`. A
zero of `B` above a *negative* entry of `A` is not a support edge,
and the flow space does not transfer. -/
theorem effF_flowSpace_hnn_fence_QA : ¬ IsFlowOn zeroWAdj phantomFlow :=
  phantomFlow_not_isFlowOn_QA

/-- **Isolation:** the phantom genuinely flows on `negWAdj`, the
domination `negWAdj ≤ zeroWAdj` is genuine, nonnegativity of `A`
fails (delivered). -/
theorem effF_flowSpace_hnn_isolation_QA :
    IsFlowOn negWAdj phantomFlow
      ∧ (∀ i j, negWAdj i j ≤ zeroWAdj i j)
      ∧ ¬ (∀ i j, 0 ≤ negWAdj i j) :=
  ⟨phantom_isFlowOn_negWAdj_QA, negWAdj_le_zeroWAdj, negWAdj_not_nonneg⟩

/-- **Fence (`isFlowOn_of_le`, `hle`):** without domination the
conclusion fails for a genuine flow — the edge current carries `1`
across the zero network's zero-conductance pair. -/
theorem effF_flowSpace_hle_fence_QA :
    ¬ IsFlowOn zeroWAdj (electricalCurrent edgeAdj ![1, 0]) := by
  rintro ⟨-, hsupp⟩
  have h01 : zeroWAdj 0 1 = 0 := by simp [zeroWAdj]
  exact absurd (hsupp 0 1 h01) (by simp [electricalCurrent, edgeAdj])

/-- **Isolation:** the current is a genuine flow on `edgeAdj`
(delivered engine), `edgeAdj` is nonnegative, and the domination
`edgeAdj ≤ zeroWAdj` genuinely fails. -/
theorem effF_flowSpace_hle_isolation_QA :
    IsFlowOn edgeAdj (electricalCurrent edgeAdj ![1, 0])
      ∧ (∀ i j, 0 ≤ edgeAdj i j)
      ∧ ¬ (∀ i j, edgeAdj i j ≤ zeroWAdj i j) :=
  ⟨isFlowOn_electricalCurrent edgeAdj edgeAdj_isSymm _, edgeAdj_nonneg,
    by
    intro h
    have h01 := h 0 1
    simp [edgeAdj, zeroWAdj] at h01
    norm_num at h01⟩

/-!
### Energy comparison (`flowEnergy_le_of_le`): support, sign,
### domination
-/

theorem phantom_energy_edge_QA :
    flowEnergy edgeAdj phantomFlow = 1 := by
  simp [flowEnergy, edgeAdj, phantomFlow, Fin.sum_univ_two]

theorem phantom_energy_negWAdj_QA :
    flowEnergy negWAdj phantomFlow = -1 := by
  simp [flowEnergy, negWAdj, phantomFlow, Fin.sum_univ_two]

theorem zeroWAdj_le_edgeAdj : ∀ i j, zeroWAdj i j ≤ edgeAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [zeroWAdj, edgeAdj]

theorem negWAdj_le_edgeAdj : ∀ i j, negWAdj i j ≤ edgeAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [negWAdj, edgeAdj]

/-- **Fence (`flowEnergy_le_of_le`, `hθ`):** an unsupported flow's
energy comparison inverts — the phantom dissipates `0` on the edgeless
network (delivered) but `1` on the dominating edge: `1 ≤ 0` is false. -/
theorem effF_energyComp_hθ_fence_QA :
    ¬ (flowEnergy edgeAdj phantomFlow ≤ flowEnergy zeroWAdj phantomFlow) := by
  rw [phantom_energy_edge_QA, phantom_flowEnergy_zero_QA]
  norm_num

/-- **Isolation:** domination and nonnegativity genuine; the flow
hypothesis fails (delivered). -/
theorem effF_energyComp_hθ_isolation_QA :
    (∀ i j, zeroWAdj i j ≤ edgeAdj i j) ∧ (∀ i j, 0 ≤ zeroWAdj i j)
      ∧ ¬ IsFlowOn zeroWAdj phantomFlow :=
  ⟨zeroWAdj_le_edgeAdj, by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [zeroWAdj],
    phantomFlow_not_isFlowOn_QA⟩

/-- **Fence (`flowEnergy_le_of_le`, `hnonneg`):** negative
conductances make the *smaller* network's energy smaller still — the
phantom dissipates `−1` on the signed network against `1` on the
dominating edge: `1 ≤ −1` is false. -/
theorem effF_energyComp_hnn_fence_QA :
    ¬ (flowEnergy edgeAdj phantomFlow ≤ flowEnergy negWAdj phantomFlow) := by
  rw [phantom_energy_edge_QA, phantom_energy_negWAdj_QA]
  norm_num

/-- **Isolation:** the phantom genuinely flows on the signed network,
the domination is genuine, nonnegativity fails. -/
theorem effF_energyComp_hnn_isolation_QA :
    IsFlowOn negWAdj phantomFlow
      ∧ (∀ i j, negWAdj i j ≤ edgeAdj i j)
      ∧ ¬ (∀ i j, 0 ≤ negWAdj i j) :=
  ⟨phantom_isFlowOn_negWAdj_QA, negWAdj_le_edgeAdj, negWAdj_not_nonneg⟩

/-- **Fence (`flowEnergy_le_of_le`, `hle`):** without domination the
comparison inverts — the unit current dissipates `1` on the edge but
`1/2` on the doubled edge (delivered pin): `1 ≤ 1/2` is false. The
orientation guard's numbers at the energy level. -/
theorem effF_energyComp_hle_fence_QA :
    ¬ (flowEnergy edgeAdj (electricalCurrent edgeAdj ![1, 0])
      ≤ flowEnergy edge2Adj (electricalCurrent edgeAdj ![1, 0])) := by
  rw [edge_flowEnergy_value_QA, edge2_crossEnergy_value_QA]
  norm_num

/-- **Isolation:** the current genuinely flows on the doubled network
(delivered transfer), the doubled network is nonnegative, and the
reverse domination genuinely fails. -/
theorem effF_energyComp_hle_isolation_QA :
    IsFlowOn edge2Adj (electricalCurrent edgeAdj ![1, 0])
      ∧ (∀ i j, 0 ≤ edge2Adj i j)
      ∧ ¬ (∀ i j, edge2Adj i j ≤ edgeAdj i j) :=
  ⟨edge_current_isUnitFlow_on_edge2_QA.1, edge2Adj_nonneg, by
    intro h
    have h01 := h 0 1
    simp [edge2Adj, edgeAdj] at h01⟩

/-!
### Rayleigh monotonicity (`effectiveResistance_le_of_le`): the
### sign and connectivity clauses

The signed edge's demand is *genuinely solvable* — the voltage
difference is real and negative (`−1`), not a junk fallback — so the
dropped-`hnonnegA` statement reads `1 ≤ −1` against the delivered
edge resistance `1`.
-/

theorem negWAdj_potential_value_QA :
    (laplacian negWAdj).mulVec ![0, 1]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, negWAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_two]

theorem negWAdj_resistance_value_QA :
    effectiveResistance negWAdj 0 1 = -1 := by
  have hfix : ∀ r : ℝ, IsEffectiveResistance negWAdj 0 1 r → r = -1 := by
    rintro r ⟨g, hg, hfr⟩
    have e0 := congrFun hg 0
    simp [laplacian, degreeMatrix, deg, negWAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_two, Pi.single_apply] at e0
    linarith
  have hex : ∃ r : ℝ, IsEffectiveResistance negWAdj 0 1 r :=
    ⟨-1, ![0, 1], negWAdj_potential_value_QA,
      by norm_num [Matrix.cons_val']⟩
  simp only [effectiveResistance, dif_pos hex]
  exact hfix _ (Classical.choose_spec hex)

/-- **Fence (`effectiveResistance_le_of_le`, `hnonnegA`):** the signed
network's genuine negative resistance `−1` sits below the dominating
edge's `1`: `1 ≤ −1` is false. -/
theorem effF_rayleigh_hnnA_fence_QA :
    ¬ (effectiveResistance edgeAdj 0 1 ≤ effectiveResistance negWAdj 0 1) := by
  rw [edge_effectiveResistance_eq_one_QA, negWAdj_resistance_value_QA]
  norm_num

/-- **Isolation:** symmetry of both networks, nonnegativity of `B`,
connectivity of both support graphs, and the domination are all
genuine; only `A`'s nonnegativity fails. -/
theorem effF_rayleigh_hnnA_isolation_QA :
    negWAdj.IsSymm ∧ (∀ i j, negWAdj i j ≤ edgeAdj i j)
      ∧ edgeAdj.IsSymm ∧ (∀ i j, 0 ≤ edgeAdj i j)
      ∧ (supportGraph edgeAdj edgeAdj_isSymm).Connected
      ∧ ¬ (∀ i j, 0 ≤ negWAdj i j) :=
  ⟨negWAdj_isSymm, negWAdj_le_edgeAdj, edgeAdj_isSymm, edgeAdj_nonneg,
    edge_supportGraph_connected, negWAdj_not_nonneg⟩

/-!
The connectivity clause: the cheat network's isolated vertex makes
the cross demand unsolvable (row `2` is identically zero), so the
total function takes its junk `0` there while the dominating path's
resistance is the delivered `2`.
-/

theorem cheat_no_resistance02_QA :
    ¬ ∃ r : ℝ, IsEffectiveResistance cheatWAdj 0 2 r := by
  rintro ⟨r, f, hf, -⟩
  have e2 := congrFun hf 2
  simp [laplacian, degreeMatrix, deg, cheatWAdj, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_three, Pi.single_apply] at e2

theorem cheat_resistance02_zero_QA :
    effectiveResistance cheatWAdj 0 2 = 0 :=
  effectiveResistance_eq_zero_of_not_exists cheatWAdj 0 2
    cheat_no_resistance02_QA

theorem cheat_le_path : ∀ i j, cheatWAdj i j ≤ connPathAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [cheatWAdj, connPathAdj]

/-- **Fence (`effectiveResistance_le_of_le`, `hconnA`):** dominating a
*disconnected* network cannot certify the resistance bound — the junk
`0` between disconnected vertices sits below the dominating path's
`2`: `2 ≤ 0` is false. -/
theorem effF_rayleigh_hconn_fence_QA :
    ¬ (effectiveResistance connPathAdj 0 2
      ≤ effectiveResistance cheatWAdj 0 2) := by
  rw [path_effectiveResistance_eq_two_QA, cheat_resistance02_zero_QA]
  norm_num

/-- Row and column `2` of the cheat network are identically zero —
the isolated vertex. -/
theorem cheatWAdj_row2_zero : ∀ x : Fin 3, cheatWAdj 2 x = 0 := by
  intro x
  fin_cases x <;> simp [cheatWAdj]

theorem cheatWAdj_col2_zero : ∀ x : Fin 3, cheatWAdj x 2 = 0 := by
  intro x
  fin_cases x <;> simp [cheatWAdj]

/-- No positive entry of the cheat network touches the isolated
vertex — row or column. -/
theorem cheat_pos_touching2_false {x : Fin 3}
    (h : 0 < cheatWAdj 2 x ∨ 0 < cheatWAdj x 2) : False := by
  rcases h with h | h
  · rw [cheatWAdj_row2_zero x] at h; norm_num at h
  · rw [cheatWAdj_col2_zero x] at h; norm_num at h

/-- Support-graph walks of the cheat network never change block: a
walk touching the isolated vertex `2` anywhere would need an adjacent
positive entry, and row/column `2` is zero. -/
theorem cheat_walk_blocks {u v : Fin 3}
    (w : (supportGraph cheatWAdj cheatWAdj_isSymm).Walk u v) :
    (u = 2 ↔ v = 2) := by
  induction w with
  | nil => rfl
  | cons hadj _ ih =>
    have hpos := (supportGraph_adj.1 hadj).2
    have hpossymm := (supportGraph_adj.1 hadj.symm).2
    exact iff_of_false
      (fun h => cheat_pos_touching2_false (Or.inl (h ▸ hpos)))
      (fun hw => by
        have h2 := hpossymm
        rw [ih.mpr hw] at h2
        exact cheat_pos_touching2_false (Or.inl h2))

theorem cheatWAdj_not_connected :
    ¬ (supportGraph cheatWAdj cheatWAdj_isSymm).Connected := by
  intro h
  obtain ⟨w⟩ := h 2 0
  have hb := cheat_walk_blocks w
  rw [show (2 : Fin 3) = 2 from rfl] at hb
  exact absurd (hb.mp rfl) (by decide)

/-- **Isolation:** every hypothesis of the monotonicity theorem is
genuine at the pair (`A = cheatWAdj`, `B = connPathAdj`) except `A`'s
connectivity — the isolated vertex is exactly the failure. -/
theorem effF_rayleigh_hconn_isolation_QA :
    cheatWAdj.IsSymm ∧ (∀ i j, 0 ≤ cheatWAdj i j)
      ∧ connPathAdj.IsSymm ∧ (∀ i j, 0 ≤ connPathAdj i j)
      ∧ (supportGraph connPathAdj connPathAdj_isSymm).Connected
      ∧ (∀ i j, cheatWAdj i j ≤ connPathAdj i j)
      ∧ ¬ (supportGraph cheatWAdj cheatWAdj_isSymm).Connected :=
  ⟨cheatWAdj_isSymm, cheatWAdj_nonneg, connPathAdj_isSymm,
    connPathAdj_nonneg, connPath_supportGraph_connected, cheat_le_path,
    cheatWAdj_not_connected⟩

/-!
### Support-graph monotonicity (`supportGraph_le_of_le`): domination
-/

/-- **Fence (`supportGraph_le_of_le`, `hle`):** without domination the
support containment fails — the path's edge `{1, 2}` is lost in the
cheat network. -/
theorem effF_supportMono_hle_fence_QA :
    ¬ (supportGraph connPathAdj connPathAdj_isSymm
      ≤ supportGraph cheatWAdj cheatWAdj_isSymm) := by
  intro h
  have hpadj : (supportGraph connPathAdj connPathAdj_isSymm).Adj 1 2 :=
    supportGraph_adj.2 ⟨by decide, by simp [connPathAdj]⟩
  have hadj := h hpadj
  have h12 := (supportGraph_adj.1 hadj).2
  rw [cheatWAdj_col2_zero 1] at h12
  norm_num at h12

theorem effF_supportMono_hle_isolation_QA :
    connPathAdj.IsSymm ∧ cheatWAdj.IsSymm
      ∧ ¬ (∀ i j, connPathAdj i j ≤ cheatWAdj i j) :=
  ⟨connPathAdj_isSymm, cheatWAdj_isSymm, by
    intro h
    have h12 := h 1 2
    simp [connPathAdj, cheatWAdj] at h12
    norm_num at h12⟩

/-!
### Connectivity growth (`supportGraph_connected_of_le`): both
### clauses
-/

/-- **Fence (`supportGraph_connected_of_le`, `hconn`):** with `B = A`
the domination is trivially genuine and the conclusion is exactly the
delivered disconnectedness of the two-block fixture. -/
theorem effF_supportConn_hconn_fence_QA :
    ¬ (supportGraph connDiscAdj connDiscAdj_isSymm).Connected :=
  connDisc_not_connected_QA

theorem effF_supportConn_hconn_isolation_QA :
    connDiscAdj.IsSymm ∧ connDiscAdj.IsSymm
      ∧ (∀ i j, connDiscAdj i j ≤ connDiscAdj i j) :=
  ⟨connDiscAdj_isSymm, connDiscAdj_isSymm, fun _ _ => le_refl _⟩

/-- **Fence (`supportGraph_connected_of_le`, `hle`):** the connected
path network dominating nothing — the cheat network does not dominate
it — leaves the conclusion false: the cheat support graph is
disconnected. -/
theorem effF_supportConn_hle_fence_QA :
    ¬ (supportGraph cheatWAdj cheatWAdj_isSymm).Connected :=
  cheatWAdj_not_connected

theorem effF_supportConn_hle_isolation_QA :
    (supportGraph connPathAdj connPathAdj_isSymm).Connected
      ∧ ¬ (∀ i j, connPathAdj i j ≤ cheatWAdj i j) :=
  ⟨connPath_supportGraph_connected, by
    intro h
    have h12 := h 1 2
    simp [connPathAdj, cheatWAdj] at h12
    norm_num at h12⟩

/-!
### Capacity reinforcement: the entry lemmas
-/

/-- **Fence (`le_increaseConductance`, `hδ`):** a negative
reinforcement *lowers* the reinforced entry — `1 ≤ 0` is false. -/
theorem effF_leInc_hδ_fence_QA :
    ¬ (edgeAdj 0 1 ≤ increaseConductance edgeAdj 0 1 (-1) 0 1) := by
  rw [increaseConductance_apply_of_reinforced (Or.inl ⟨rfl, rfl⟩)]
  simp [edgeAdj]

theorem effF_leInc_hδ_isolation_QA : ¬ (0 ≤ (-1 : ℝ)) := by norm_num

/-- **Fence (`increaseConductance_isSymm`, `hA`):** reinforcing an
asymmetric network's pair raises both ordered entries by the same
`δ` but from unequal bases — `3 ≠ 2`, still asymmetric. -/
theorem effF_incSymm_hA_fence_QA :
    ¬ (increaseConductance asymWAdj 0 1 1).IsSymm := by
  intro h
  have h01 := h.apply 0 1
  rw [increaseConductance_apply_of_reinforced (Or.inl ⟨rfl, rfl⟩),
    increaseConductance_apply_of_reinforced (Or.inr ⟨rfl, rfl⟩)] at h01
  simp [asymWAdj] at h01

theorem effF_incSymm_hA_isolation_QA : ¬ asymWAdj.IsSymm :=
  asymWAdj_not_isSymm

/-- **Fence (`increaseConductance_nonneg`, `hnonneg`):** raising a
negative conductance by less than its magnitude stays negative —
`−1 + 1/2 < 0`. -/
theorem effF_incNonneg_hnn_fence_QA :
    ¬ (∀ k l, 0 ≤ increaseConductance negWAdj 0 1 (1 / 2) k l) := by
  intro h
  have h01 := h 0 1
  rw [increaseConductance_apply_of_reinforced (Or.inl ⟨rfl, rfl⟩)] at h01
  simp [negWAdj] at h01
  norm_num at h01

/-- **Fence (`increaseConductance_nonneg`, `hδ`):** reinforcing by a
negative `δ` can push a positive conductance below zero — `1 − 2 < 0`. -/
theorem effF_incNonneg_hδ_fence_QA :
    ¬ (∀ k l, 0 ≤ increaseConductance edgeAdj 0 1 (-2) k l) := by
  intro h
  have h01 := h 0 1
  rw [increaseConductance_apply_of_reinforced (Or.inl ⟨rfl, rfl⟩)] at h01
  simp [edgeAdj] at h01

theorem effF_incNonneg_isolation_QA :
    ¬ (∀ k l : Fin 2, 0 ≤ negWAdj k l) ∧ ¬ (0 ≤ (-2 : ℝ)) := by
  refine ⟨negWAdj_not_nonneg, ?_⟩
  norm_num

/-!
### The reinforcement headline: `hδ` and `hconn`
-/

/-- The conductance-`1/2` edge: the unit edge reinforced by `−1/2`. -/
noncomputable def halfEdgeAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 1/2; 1/2, 0]

theorem halfEdgeAdj_isSymm : halfEdgeAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [halfEdgeAdj]

theorem halfEdgeAdj_nonneg : ∀ i j, 0 ≤ halfEdgeAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [halfEdgeAdj]

theorem halfEdge_supportGraph_connected :
    (supportGraph halfEdgeAdj halfEdgeAdj_isSymm).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
      (supportGraph_adj.2 ⟨by decide, by simp [halfEdgeAdj]⟩)
      SimpleGraph.Walk.nil⟩

theorem halfEdge_potential_value_QA :
    (laplacian halfEdgeAdj).mulVec ![2, 0]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, halfEdgeAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_two]

theorem halfEdge_resistance_value_QA :
    effectiveResistance halfEdgeAdj 0 1 = 2 :=
  effectiveResistance_eq halfEdgeAdj halfEdgeAdj_isSymm halfEdgeAdj_nonneg
    halfEdge_supportGraph_connected
    ⟨![2, 0], halfEdge_potential_value_QA,
      by norm_num [Matrix.cons_val']⟩

theorem edge_reinforce_neg_half_eq_halfEdge_QA :
    increaseConductance edgeAdj 0 1 (-1/2) = halfEdgeAdj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [increaseConductance, halfEdgeAdj, edgeAdj] <;>
    norm_num

/-- **Fence (`effectiveResistance_le_increaseConductance`, `hδ`):** a
negative reinforcement *raises* the resistance — the conductance-`1/2`
edge's resistance is genuinely `2`, above the original `1`: the
dropped statement reads `2 ≤ 1`. -/
theorem effF_reinforce_hδ_fence_QA :
    ¬ (effectiveResistance (increaseConductance edgeAdj 0 1 (-1/2)) 0 1
      ≤ effectiveResistance edgeAdj 0 1) := by
  rw [edge_reinforce_neg_half_eq_halfEdge_QA, halfEdge_resistance_value_QA,
    edge_effectiveResistance_eq_one_QA]
  norm_num

theorem effF_reinforce_hδ_isolation_QA :
    edgeAdj.IsSymm ∧ (∀ i j, 0 ≤ edgeAdj i j)
      ∧ (supportGraph edgeAdj edgeAdj_isSymm).Connected
      ∧ ¬ (0 ≤ (-1/2 : ℝ)) := by
  refine ⟨edgeAdj_isSymm, edgeAdj_nonneg, edge_supportGraph_connected, ?_⟩
  norm_num

theorem cheat_reinforce_eq_path_QA :
    increaseConductance cheatWAdj 1 2 1 = connPathAdj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [increaseConductance, connPathAdj, cheatWAdj]

/-- **Fence (`effectiveResistance_le_increaseConductance`, `hconn`):**
reinforcing a *disconnected* network can connect it — the reinforced
cheat network is exactly the path, whose cross resistance `2` sits
above the junk `0` of the isolated pair: `2 ≤ 0` is false. The
one-hypothesis ICP form genuinely needs the original connectivity. -/
theorem effF_reinforce_hconn_fence_QA :
    ¬ (effectiveResistance (increaseConductance cheatWAdj 1 2 1) 0 2
      ≤ effectiveResistance cheatWAdj 0 2) := by
  rw [cheat_reinforce_eq_path_QA, path_effectiveResistance_eq_two_QA,
    cheat_resistance02_zero_QA]
  norm_num

theorem effF_reinforce_hconn_isolation_QA :
    cheatWAdj.IsSymm ∧ (∀ i j, 0 ≤ cheatWAdj i j)
      ∧ (0 ≤ (1 : ℝ))
      ∧ ¬ (supportGraph cheatWAdj cheatWAdj_isSymm).Connected :=
  ⟨cheatWAdj_isSymm, cheatWAdj_nonneg, zero_le_one, cheatWAdj_not_connected⟩

/-!
### The flow-predicate engine's `hA` (derived from the delivered
### witness)
-/

/-- **Fence (`isFlowOn_electricalCurrent`, `hA`):** on the asymmetric
network the current is not a flow — `IsFlowOn`'s first conjunct is
antisymmetry, refuted by the delivered witness. -/
theorem effF_isFlowOn_hA_fence_QA :
    ¬ IsFlowOn asymWAdj (electricalCurrent asymWAdj ![1, 0]) := by
  rintro ⟨hanti, -⟩
  exact asymWAdj_current_not_antisymm_QA hanti

end SpectralGraphTheory.QA
