/-
  ElectricalFlow_QA.lean

  Purpose
  -------
  QA for `Scaffold.Mathlib.GraphTheory.ElectricalFlow` — proposal
  `proposals/electrical-flow-routing.md`. Step 1 (the electrical
  current, divergence, flow predicates, and the Kirchhoff bridge),
  step 2 (flow energy: the agreement with the Dirichlet energy and the
  effective resistance it routes), and step 3 (Thomson's principle:
  attainment at the current, a strict competitor, and the superposition
  decomposition on the triangle).

  Witness plan (proposal QA items 1, 3, 4, 5, 6):

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

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is fully evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.ElectricalFlow
import Scaffold.QA.SpectralGraph.PotentialSolvability_QA
import Scaffold.QA.SpectralGraph.EffectiveResistance_QA
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

end SpectralGraphTheory.QA
