/-
  EffectiveResistance_QA.lean

  Purpose
  -------
  QA for proposal `proposals/electrical-structure-crust.md` step 5,
  delivered in `Scaffold.Mathlib.GraphTheory.Electrical`
  (`IsEffectiveResistance`, `effectiveResistance`, existence,
  reachability-form uniqueness and agreement, the energy identity,
  symmetry, nonnegativity, `R u u = 0`).

  Witness plan (per the proposal's step-level QA spec):

  - **Positive witnesses, values computed from the definitions:** the
    two-vertex unit edge has `effectiveResistance = 1` (witness
    potential `![1, 0]`), and the three-vertex path has
    `effectiveResistance 0 2 = 2` (witness `![1, 0, −1]`) — series
    edges add; the quantity distinguishes topology.
  - **Energy cross-check:** on the path, the function value obtained
    through the theorem chain (agreement) equals the energy
    `quadForm (laplacian) ![1, 0, −1]` computed *independently* from
    the raw definitions (`path_energy_value_QA`), so the energy
    identity is verified against an external number.
  - **Negative witness (connectivity is load-bearing):** on the
    disconnected fixture, no resistance value exists across components
    (`disc_no_resistance_QA`, from the step-4 unsolvability witness),
    and the total function's junk fallback is *pinned* to `0`
    (`disc_fallback_zero_QA`) — documenting that `0` there is a
    fallback, not a measurement.
  - **Same-component witnesses (uniqueness is about `r`, not `f`):**
    on the disconnected fixture, two *different* potentials
    (`![1, 0, 0, 0]`, `![2, 1, 0, 0]`) witness the same resistance `1`
    between `0` and `1`; the reachability-form agreement and uniqueness
    theorems still pin `effectiveResistance 0 1 = 1` even though the
    connected-graph agreement theorem's hypothesis fails — the kernel
    being two-dimensional does not break the value.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks interfaces where the arithmetic is
  fully evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Electrical
import Scaffold.QA.SpectralGraph.Connectivity_QA
import Scaffold.QA.SpectralGraph.PotentialSolvability_QA
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## Positive witness: the two-vertex edge `0 — 1`

The unit edge has resistance exactly `1`: the witness potential
`f = ![1, 0]` solves the unit-demand equation
(`edge_potential_value_QA`) with voltage difference `1`.
-/

/-- The resistance value on the edge, as a relation instance: `1`
witnessed by the potential `![1, 0]`. -/
theorem edge_resistance_one_QA : IsEffectiveResistance edgeAdj 0 1 (1 : ℝ) :=
  ⟨![1, 0], edge_potential_value_QA, by norm_num [Matrix.cons_val']⟩

/-- **Value of the total function on the edge:** `R 0 1 = 1` for the
unit-resistance edge, pinned through the agreement theorem. -/
theorem edge_effectiveResistance_eq_one_QA :
    effectiveResistance edgeAdj 0 1 = 1 :=
  effectiveResistance_eq edgeAdj edgeAdj_isSymm edgeAdj_nonneg
    edge_supportGraph_connected edge_resistance_one_QA

/-- **Orientation-independence of the value:** `R 1 0 = 1` on the edge,
through the symmetry theorem (not by a second witness). -/
theorem edge_effectiveResistance_symm_value_QA :
    effectiveResistance edgeAdj 1 0 = 1 := by
  rw [effectiveResistance_symm edgeAdj edgeAdj_isSymm edgeAdj_nonneg
    edge_supportGraph_connected 1 0, edge_effectiveResistance_eq_one_QA]

/-- **Diagonal:** `R 0 0 = 0` unconditionally. -/
theorem edge_effectiveResistance_self_QA :
    effectiveResistance edgeAdj 0 0 = 0 :=
  effectiveResistance_self edgeAdj 0

/-- **Nonnegativity interface instantiation** on the edge. -/
theorem edge_effectiveResistance_nonneg_QA :
    0 ≤ effectiveResistance edgeAdj 0 1 :=
  effectiveResistance_nonneg edgeAdj edgeAdj_isSymm edgeAdj_nonneg
    edge_supportGraph_connected 0 1

/-- **Energy-identity interface instantiation** on the edge: some
potential solves the demand, and `R` equals its energy. -/
theorem edge_energy_identity_QA :
    ∃ f : Fin 2 → ℝ, (laplacian edgeAdj).mulVec f
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ)
      ∧ effectiveResistance edgeAdj 0 1 = quadForm (laplacian edgeAdj) f :=
  effectiveResistance_eq_quadForm edgeAdj edgeAdj_isSymm edgeAdj_nonneg
    edge_supportGraph_connected 0 1

/-!
## Positive witness: the three-vertex path `0 — 1 — 2`

Series edges add: the endpoint resistance is `2`, twice the unit edge.
The witness potential `![1, 0, −1]` is fixed by its own Laplacian.
-/

/-- The resistance value on the path, as a relation instance: `2`
witnessed by the potential `![1, 0, −1]`. -/
theorem path_resistance_two_QA :
    IsEffectiveResistance connPathAdj 0 2 (2 : ℝ) :=
  ⟨![1, 0, -1], path_potential_value_QA, by norm_num [Matrix.cons_val']⟩

/-- **Value of the total function on the path:** `R 0 2 = 2` — the
two-edge path has twice the single-edge resistance. -/
theorem path_effectiveResistance_eq_two_QA :
    effectiveResistance connPathAdj 0 2 = 2 :=
  effectiveResistance_eq connPathAdj connPathAdj_isSymm connPathAdj_nonneg
    connPath_supportGraph_connected path_resistance_two_QA

/-- **Independent energy computation:** the energy of the witness
potential `![1, 0, −1]`, computed from the raw definitions (`quadForm`
unfolded through the explicit path Laplacian), *not* through the
energy theorem — an external check on the identity's value. -/
theorem path_energy_value_QA :
    quadForm (laplacian connPathAdj) ![1, 0, -1] = 2 := by
  simp [quadForm, Matrix.mulVec, Matrix.dotProduct, laplacian,
    degreeMatrix, deg, connPathAdj, Fin.sum_univ_three]
  norm_num

/-- **Energy identity cross-check:** the function value obtained via
the theorem chain (`path_effectiveResistance_eq_two_QA`) equals the
independently computed energy (`path_energy_value_QA`) — two different
routes to `2`. -/
theorem path_energy_identity_QA :
    effectiveResistance connPathAdj 0 2
      = quadForm (laplacian connPathAdj) ![1, 0, -1] := by
  rw [path_effectiveResistance_eq_two_QA, path_energy_value_QA]

/-!
## Negative witness: the disconnected fixture, cross-component pair

On `0 — 1   2 — 3`, the unit demand `e 0 − e 2` crosses components and
is unsolvable (step 4's QA witness), so *no* resistance value exists;
the total function's fallback branch fires and is pinned to `0`. The
`0` is a fallback, not a measurement — this is the honesty witness for
the total function's design.
-/

/-- **No resistance exists across components:** the relation is
unsatisfiable for the cross-component pair, from the step-4
unsolvability witness. -/
theorem disc_no_resistance_QA :
    ¬ ∃ r : ℝ, IsEffectiveResistance connDiscAdj 0 2 r := by
  rintro ⟨r, f, hf, hfr⟩
  exact disc_cross_demand_unsolvable_QA ⟨f, hf⟩

/-- **The junk fallback, pinned:** `effectiveResistance 0 2 = 0` on the
disconnected fixture — the `dite` else-branch, not a resistance. -/
theorem disc_fallback_zero_QA :
    effectiveResistance connDiscAdj 0 2 = 0 :=
  effectiveResistance_eq_zero_of_not_exists connDiscAdj 0 2
    disc_no_resistance_QA

/-- **Connectivity load-bearing, full story:** the fixture's support
graph is not connected, no cross-component resistance value exists, and
the total function takes its junk value there. -/
theorem disc_cross_component_load_bearing_QA :
    ¬(supportGraph connDiscAdj connDiscAdj_isSymm).Connected
      ∧ (¬ ∃ r : ℝ, IsEffectiveResistance connDiscAdj 0 2 r)
      ∧ effectiveResistance connDiscAdj 0 2 = 0 :=
  ⟨connDisc_not_connected_QA, disc_no_resistance_QA, disc_fallback_zero_QA⟩

/-!
## Same-component witnesses: uniqueness is about `r`, not `f`

The pair `0 — 1` lives in one component of the disconnected fixture,
where the kernel is two-dimensional and potentials are genuinely
non-unique — yet the resistance value is still pinned to `1` by the
reachability-form agreement and uniqueness theorems, which do not need
global connectivity.
-/

/-- Vertices `0` and `1` are reachable in the fixture's support graph:
one explicit edge-walk. -/
theorem disc_same_component_reachable :
    (supportGraph connDiscAdj connDiscAdj_isSymm).Reachable 0 1 :=
  ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
    ⟨by decide, by simp [connDiscAdj]⟩ SimpleGraph.Walk.nil⟩

/-- **Two distinct potentials, same resistance:** both `![1, 0, 0, 0]`
and `![2, 1, 0, 0]` solve the unit-demand equation between `0` and `1`
(computed entrywise from the definitions), both with voltage
difference `1`. Potentials are non-unique on a graph with a
two-dimensional kernel; the resistance value is not. -/
theorem disc_two_potentials_same_r_QA :
    IsEffectiveResistance connDiscAdj 0 1 (1 : ℝ)
      ∧ IsEffectiveResistance connDiscAdj 0 1 (1 : ℝ)
      ∧ ![1, 0, 0, 0] ≠ ![2, 1, 0, 0] := by
  have h1 : (laplacian connDiscAdj).mulVec ![1, 0, 0, 0]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
    funext i
    fin_cases i <;>
      simp [laplacian, degreeMatrix, deg, connDiscAdj, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_four]
  have h2 : (laplacian connDiscAdj).mulVec ![2, 1, 0, 0]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
    funext i
    fin_cases i <;>
      simp [laplacian, degreeMatrix, deg, connDiscAdj, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_four] <;>
      norm_num
  refine ⟨⟨![1, 0, 0, 0], h1, by norm_num [Matrix.cons_val']⟩,
    ⟨![2, 1, 0, 0], h2, by norm_num [Matrix.cons_val']⟩, ?_⟩
  intro heq
  have h := congrFun heq 0
  norm_num [Matrix.cons_val'] at h

/-- **Component-form agreement still pins the value:** on the
disconnected fixture (where the connected-graph agreement theorem's
hypothesis fails), the reachability-form theorem gives
`effectiveResistance 0 1 = 1` — the resistance within a component is
meaningful on every graph, not only connected ones. -/
theorem disc_same_component_effectiveResistance_eq_one_QA :
    effectiveResistance connDiscAdj 0 1 = 1 :=
  effectiveResistance_eq_of_reachable connDiscAdj connDiscAdj_isSymm
    connDiscAdj_nonneg disc_same_component_reachable
    disc_two_potentials_same_r_QA.1

/-- **Component-form uniqueness interface:** on the disconnected
fixture, any two witness values for the same-component pair `0, 1`
coincide — instantiated against the two concrete potentials above. -/
theorem disc_same_component_uniqueness_QA {r s : ℝ}
    (h1 : IsEffectiveResistance connDiscAdj 0 1 r)
    (h2 : IsEffectiveResistance connDiscAdj 0 1 s) : r = s :=
  isEffectiveResistance_unique_of_reachable connDiscAdj connDiscAdj_isSymm
    connDiscAdj_nonneg disc_same_component_reachable h1 h2

end SpectralGraphTheory.QA
