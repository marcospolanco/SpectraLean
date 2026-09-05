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

  - **One-sided Dirichlet bound (step 6):** equality is *attained* at
    the harmonic potential on both connected fixtures (edge: `1/1 = 1`;
    path: `4/2 = 2` — values computed from the raw definitions); a
    non-harmonic test potential on the path gives a *strict* bound
    (`1 < 2`); the reverse (upper-bound) inequality is **refuted
    numerically** on the same fixture (`2 ≤ 1` is false), witnessing
    that the one-sided form is forced — the other direction genuinely
    needs the attained-supremum Dirichlet principle, which stays
    deferred; and on the disconnected fixture a component indicator has
    zero energy but nonzero voltage difference, so the `0 <` energy
    guard excludes exactly the vectors for which the bound would
    degenerate (`1 / 0 = 0` junk on both sides).

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks interfaces where the arithmetic is
  fully evaluated.

  Since 2026-09-04 this file also carries the effective-resistance core
  family's adversarial fence audit (`AdversarialFences`,
  `proposals/adversarial-fences-effective-resistance-family.md`):
  hypothesis-form negative witnesses plus isolation companions for the
  pre-discipline QA's unfenced load-bearing clauses.

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
theorem edge_resistance_one_QA : IsEffectiveResistance psEdgeAdj 0 1 (1 : ℝ) :=
  ⟨![1, 0], edge_potential_value_QA, by norm_num [Matrix.cons_val']⟩

/-- **Value of the total function on the edge:** `R 0 1 = 1` for the
unit-resistance edge, pinned through the agreement theorem. -/
theorem edge_effectiveResistance_eq_one_QA :
    effectiveResistance psEdgeAdj 0 1 = 1 :=
  effectiveResistance_eq psEdgeAdj psEdgeAdj_isSymm psEdgeAdj_nonneg
    edge_supportGraph_connected edge_resistance_one_QA

/-- **Orientation-independence of the value:** `R 1 0 = 1` on the edge,
through the symmetry theorem (not by a second witness). -/
theorem edge_effectiveResistance_symm_value_QA :
    effectiveResistance psEdgeAdj 1 0 = 1 := by
  rw [effectiveResistance_symm psEdgeAdj psEdgeAdj_isSymm psEdgeAdj_nonneg
    edge_supportGraph_connected 1 0, edge_effectiveResistance_eq_one_QA]

/-- **Diagonal:** `R 0 0 = 0` unconditionally. -/
theorem edge_effectiveResistance_self_QA :
    effectiveResistance psEdgeAdj 0 0 = 0 :=
  effectiveResistance_self psEdgeAdj 0

/-- **Nonnegativity interface instantiation** on the edge. -/
theorem edge_effectiveResistance_nonneg_QA :
    0 ≤ effectiveResistance psEdgeAdj 0 1 :=
  effectiveResistance_nonneg psEdgeAdj psEdgeAdj_isSymm psEdgeAdj_nonneg
    edge_supportGraph_connected 0 1

/-- **Energy-identity interface instantiation** on the edge: some
potential solves the demand, and `R` equals its energy. -/
theorem edge_energy_identity_QA :
    ∃ f : Fin 2 → ℝ, (laplacian psEdgeAdj).mulVec f
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ)
      ∧ effectiveResistance psEdgeAdj 0 1 = quadForm (laplacian psEdgeAdj) f :=
  effectiveResistance_eq_quadForm psEdgeAdj psEdgeAdj_isSymm psEdgeAdj_nonneg
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

/-!
## The one-sided Dirichlet bound (proposal step 6)

`effectiveResistance_ge_sq_div_quadForm`:
`(f u − f v)² / quadForm (laplacian A) f ≤ R u v` for any test
potential `f` of positive energy. Witnesses: equality attained at the
harmonic potentials (both connected fixtures), strictness at a
non-harmonic potential, a numerical refutation of the reverse
inequality (one-sidedness is forced), and the disconnected guard
witness for the `0 <` energy hypothesis.
-/

/-- **Independent energy computation (edge):** the energy of `![1, 0]`
— computed from the raw definitions, not through any theorem — is `1`
(the voltage difference it realizes). -/
theorem edge_energy_e0_QA : quadForm (laplacian psEdgeAdj) ![1, 0] = 1 := by
  simp [quadForm, Matrix.mulVec, Matrix.dotProduct, laplacian,
    degreeMatrix, deg, psEdgeAdj, Fin.sum_univ_two]

/-- **Independent energy computation (path):** the energy of the
non-harmonic test potential `![1, 0, 0]`, computed from the raw
definitions, is `1`. -/
theorem path_energy_e00_QA :
    quadForm (laplacian connPathAdj) ![1, 0, 0] = 1 := by
  simp [quadForm, Matrix.mulVec, Matrix.dotProduct, laplacian,
    degreeMatrix, deg, connPathAdj, Fin.sum_univ_three]

/-- **The bound is attained at the harmonic potential (edge):** the test
potential `![1, 0]` — itself a solution of the unit-demand equation —
gives `1 ^ 2 / 1 = 1 = R 0 1`, computed from the independent energy
(`edge_energy_e0_QA`) and the pinned resistance value. Equality, not
just the inequality. -/
theorem edge_bound_attained_QA :
    (![1, 0] 0 - ![1, 0] 1) ^ 2 / quadForm (laplacian psEdgeAdj) ![1, 0]
      = effectiveResistance psEdgeAdj 0 1 := by
  rw [edge_energy_e0_QA, edge_effectiveResistance_eq_one_QA]
  norm_num [Matrix.cons_val']

/-- **Interface instantiation (edge):** the theorem applies at
`f = ![1, 0]` with the positivity hypothesis discharged by the
independent energy computation. -/
theorem edge_bound_QA :
    (![1, 0] 0 - ![1, 0] 1) ^ 2 / quadForm (laplacian psEdgeAdj) ![1, 0]
      ≤ effectiveResistance psEdgeAdj 0 1 :=
  effectiveResistance_ge_sq_div_quadForm psEdgeAdj psEdgeAdj_isSymm
    psEdgeAdj_nonneg edge_supportGraph_connected 0 1 ![1, 0]
    (by rw [edge_energy_e0_QA]; norm_num)

/-- **The bound is attained at the harmonic potential (path):** the
witness `![1, 0, −1]` of `path_resistance_two_QA` gives
`(1 − (−1))² / 2 = 4 / 2 = 2 = R 0 2`. -/
theorem path_bound_attained_QA :
    (![1, 0, -1] 0 - ![1, 0, -1] 2) ^ 2
      / quadForm (laplacian connPathAdj) ![1, 0, -1]
      = effectiveResistance connPathAdj 0 2 := by
  rw [path_energy_value_QA, path_effectiveResistance_eq_two_QA]
  norm_num [Matrix.cons_val']

/-- **Strictness at a non-harmonic potential:** the test potential
`![1, 0, 0]` (not a multiple of the harmonic one) gives `1 ^ 2 / 1 = 1`,
strictly below `R 0 2 = 2` — the bound is not vacuous and not always
tight. -/
theorem path_bound_strict_QA :
    (![1, 0, 0] 0 - ![1, 0, 0] 2) ^ 2
      / quadForm (laplacian connPathAdj) ![1, 0, 0]
      < effectiveResistance connPathAdj 0 2 := by
  rw [path_energy_e00_QA, path_effectiveResistance_eq_two_QA]
  norm_num [Matrix.cons_val']

/-- **Interface instantiation (path, non-harmonic):** the theorem
applies at `f = ![1, 0, 0]`. -/
theorem path_bound_nonharmonic_QA :
    (![1, 0, 0] 0 - ![1, 0, 0] 2) ^ 2
      / quadForm (laplacian connPathAdj) ![1, 0, 0]
      ≤ effectiveResistance connPathAdj 0 2 :=
  effectiveResistance_ge_sq_div_quadForm connPathAdj connPathAdj_isSymm
    connPathAdj_nonneg connPath_supportGraph_connected 0 2 ![1, 0, 0]
    (by rw [path_energy_e00_QA]; norm_num)

/-- **Negative witness — the reverse inequality is false:** the
upper-bound reading `R 0 2 ≤ (f 0 − f 2)² / energy f` at the same
non-harmonic potential evaluates to `2 ≤ 1`, refuted numerically. The
one-sided form is forced: the other direction genuinely requires the
attained-supremum Dirichlet principle, which the proposal keeps
deferred. -/
theorem path_bound_reverse_refuted_QA :
    ¬ (effectiveResistance connPathAdj 0 2
        ≤ (![1, 0, 0] 0 - ![1, 0, 0] 2) ^ 2
          / quadForm (laplacian connPathAdj) ![1, 0, 0]) := by
  rw [path_effectiveResistance_eq_two_QA, path_energy_e00_QA]
  norm_num [Matrix.cons_val']

/-- **The `0 <` energy guard is load-bearing (disconnected witness).**
The component indicator `![1, 1, 0, 0]` has *zero* energy (it is in the
Laplacian kernel, `connDisc_indicator_in_kernel_QA`) yet nonzero
voltage difference across components, `f 0 − f 2 = 1`. The unguarded
ratio degenerates to `1 / 0 = 0` while the resistance function reads
its junk fallback `0` — both sides junk, the bound vacuous. On a
connected graph, zero energy forces `f u = f v` (PSD and the kernel
characterization), so the hypothesis `0 < quadForm … f` excludes
exactly the degenerate test potentials; disconnected, that exclusion
fails. -/
theorem disc_zero_energy_guard_QA :
    quadForm (laplacian connDiscAdj) ![1, 1, 0, 0] = 0
      ∧ (![1, 1, 0, 0] 0 - ![1, 1, 0, 0] 2) ^ 2
          / quadForm (laplacian connDiscAdj) ![1, 1, 0, 0] = 0
      ∧ effectiveResistance connDiscAdj 0 2 = 0 := by
  refine ⟨?_, ?_, disc_fallback_zero_QA⟩
  · rw [quadForm, connDisc_indicator_in_kernel_QA, Matrix.dotProduct_zero]
  · rw [quadForm, connDisc_indicator_in_kernel_QA,
      Matrix.dotProduct_zero, div_zero]

/-!
## Adversarial fences (proposal `adversarial-fences-effective-resistance-family.md`)

Hypothesis-form negative witnesses for the clauses of
`Scaffold.Mathlib.GraphTheory.Electrical` that had no negative witness
anywhere in the repository (per the audit method of
`governance/ADVERSARIAL_REVIEW.md`): the existence-flavored statements'
`hnonneg` at a rank-1 signed fixture whose connected positive support
coexists with a three-dimensional Laplacian kernel; both confinement
halves' `hconn` at the free-constant-on-a-foreign-component mechanism;
the Dirichlet bound's `hconn` at the junk fallback; and the metric
residuals' `hconn` corners — plus the Cauchy–Schwarz and polarization
engines' `hA` at an asymmetric nonnegative fixture (their statements
never mention `supportGraph`, so symmetry is genuinely fenceable there).
Screened (already fenced by delivered witnesses): the min half's
`hnonneg` (`signed_confine_refuted_QA`), existence's `hconn`
(`disc_no_resistance_QA`), the Dirichlet `hpos` guard
(`disc_zero_energy_guard_QA`), the triangle's and positivity's `hnonneg`
(`signed_triangle_refuted_QA`, `signed_pos_refuted_QA` — the latter two
live in `ResistanceMetric_QA.lean`, as do this audit's signed-fixture
engine fences). Recorded non-fenceables with mechanisms live in the
proposal.

Entrywise Laplacian arithmetic on fixtures is routed through the shelf's
`laplacian_mulVec_apply` (the diffusion form) rather than through
`degreeMatrix`, whose dependent `if h : i = j` does not decide inside a
summation over a variable index.
-/

/-- **Computation helper**: the energy of a potential against any
adjacency (symmetric or not), in diffusion form — `quadForm` unfolded
one `mulVec` entry at a time through `laplacian_mulVec_apply`. -/
theorem ecf_quadForm_lap {V : Type} [Fintype V] [DecidableEq V]
    (A : WAdj (V := V)) (f : V → ℝ) :
    quadForm (laplacian A) f = ∑ i, f i * ∑ j, A i j * (f i - f j) := by
  simp only [quadForm, Matrix.dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [laplacian_mulVec_apply]

/-- **Computation helper**: the Laplacian bilinear cross term in
diffusion form. -/
theorem ecf_dot_lap {V : Type} [Fintype V] [DecidableEq V]
    (A : WAdj (V := V)) (f g : V → ℝ) :
    Matrix.dotProduct f (laplacian A *ᵥ g)
      = ∑ i, f i * ∑ j, A i j * (g i - g j) := by
  simp only [Matrix.dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [laplacian_mulVec_apply]

/-! ### The asymmetric engine fixture `ecAsymAdj`: the engines' `hA` fences -/

/-- The asymmetric nonnegative fixture: row sums `(2, 1)`, so the
Laplacian `!![2, -2; -1, 1]` is asymmetric — symmetry is a genuine,
freely-stateable hypothesis for the Cauchy–Schwarz and polarization
engines, whose statements never mention `supportGraph`. -/
def ecAsymAdj : Matrix (Fin 2) (Fin 2) ℝ := !![0, 2; 1, 0]

theorem ecAsymAdj_not_isSymm : ¬ ecAsymAdj.IsSymm := by
  intro h
  have h01 := h.apply 0 1
  simp only [ecAsymAdj] at h01
  norm_num at h01

theorem ecAsymAdj_nonneg : ∀ i j, 0 ≤ ecAsymAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [ecAsymAdj]

theorem ecAsym_quadForm_56 :
    quadForm (laplacian ecAsymAdj) (![5, 6] : Fin 2 → ℝ) = -4 := by
  rw [ecf_quadForm_lap]
  simp only [Fin.sum_univ_two, ecAsymAdj, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  norm_num

theorem ecAsym_quadForm_10 :
    quadForm (laplacian ecAsymAdj) (![1, 0] : Fin 2 → ℝ) = 2 := by
  rw [ecf_quadForm_lap]
  simp only [Fin.sum_univ_two, ecAsymAdj, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  norm_num

theorem ecAsym_cross_56_10 :
    Matrix.dotProduct (![5, 6] : Fin 2 → ℝ)
      (laplacian ecAsymAdj *ᵥ (![1, 0] : Fin 2 → ℝ)) = 4 := by
  rw [ecf_dot_lap]
  simp only [Fin.sum_univ_two, ecAsymAdj, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  norm_num

theorem ecAsym_cross_10_56 :
    Matrix.dotProduct (![1, 0] : Fin 2 → ℝ)
      (laplacian ecAsymAdj *ᵥ (![5, 6] : Fin 2 → ℝ)) = -2 := by
  rw [ecf_dot_lap]
  simp only [Fin.sum_univ_two, ecAsymAdj, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  norm_num

theorem ecAsym_quadForm_sub :
    quadForm (laplacian ecAsymAdj)
      ((![1, 0] : Fin 2 → ℝ) - (1 : ℝ) • (![5, 6] : Fin 2 → ℝ)) = -4 := by
  rw [ecf_quadForm_lap]
  simp only [Fin.sum_univ_two, ecAsymAdj, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Pi.sub_apply, smul_eq_mul]
  norm_num

/-- **Fence (`laplacian_cauchy_schwarz`, `hA`)**: at the nonnegative
asymmetric fixture the cross term squared is `16` while the right side is
`(-4) * 2 = -8` — the semidefinite Cauchy–Schwarz engine's symmetry
hypothesis is load-bearing, and being statement-free of `supportGraph`
it is genuinely fenceable. -/
theorem ecF_cauchy_schwarz_hA_fence_QA :
    ¬ (Matrix.dotProduct (![5, 6] : Fin 2 → ℝ)
          (laplacian ecAsymAdj *ᵥ (![1, 0] : Fin 2 → ℝ)) ^ 2
        ≤ quadForm (laplacian ecAsymAdj) (![5, 6] : Fin 2 → ℝ)
          * quadForm (laplacian ecAsymAdj) (![1, 0] : Fin 2 → ℝ)) := by
  rw [ecAsym_cross_56_10, ecAsym_quadForm_56, ecAsym_quadForm_10]
  norm_num

theorem ecF_cauchy_schwarz_hA_isolation_QA :
    (∀ i j, 0 ≤ ecAsymAdj i j) ∧ ¬ ecAsymAdj.IsSymm :=
  ⟨ecAsymAdj_nonneg, ecAsymAdj_not_isSymm⟩

/-- **Fence (`quadForm_laplacian_sub_smul`, `hA`)**: at the same fixture
with `f = ![1, 0]`, `g = ![5, 6]`, `t = 1` the polarization identity
reads `-4 = 2` — the reciprocity-based expansion needs symmetry. -/
theorem ecF_polarization_hA_fence_QA :
    ¬ (quadForm (laplacian ecAsymAdj)
          ((![1, 0] : Fin 2 → ℝ) - (1 : ℝ) • (![5, 6] : Fin 2 → ℝ))
        = quadForm (laplacian ecAsymAdj) (![1, 0] : Fin 2 → ℝ)
          - 2 * (1 : ℝ)
            * Matrix.dotProduct (![1, 0] : Fin 2 → ℝ)
              (laplacian ecAsymAdj *ᵥ (![5, 6] : Fin 2 → ℝ))
          + (1 : ℝ) * (1 : ℝ)
            * quadForm (laplacian ecAsymAdj) (![5, 6] : Fin 2 → ℝ)) := by
  rw [ecAsym_quadForm_sub, ecAsym_quadForm_10, ecAsym_cross_10_56,
    ecAsym_quadForm_56]
  norm_num

/-! ### The rank-1 signed fixture `sgnK4Adj`: the existence layer's `hnn` fences -/

/-- The signed 4-cycle-plus-diagonals fixture: positive edges
`(0,1), (0,2), (1,3), (2,3)` (the support, a connected 4-cycle
`1 — 0 — 2 — 3 — 1`), negative edges `(0,3), (1,2)`, every degree
exactly `1`. Its Laplacian has rank 1 and a three-dimensional kernel
(spanned by `1`, `![1,1,-1,-1]`, `![1,-1,1,-1]`): connected support does
*not* imply demand solvability once signs enter, so the
existence-flavored statements' nonnegativity hypothesis is load-bearing. -/
def sgnK4Adj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
      (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then (1 : ℝ)
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then (-1 : ℝ)
    else 0

theorem sgnK4Adj_isSymm : sgnK4Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [sgnK4Adj]

theorem sgnK4Adj_not_nonneg : ¬ (∀ i j : Fin 4, 0 ≤ sgnK4Adj i j) := by
  intro h
  have h03 : (0 : ℝ) ≤ sgnK4Adj 0 3 := h 0 3
  have e : sgnK4Adj 0 3 = -1 := by simp [sgnK4Adj]
  rw [e] at h03
  norm_num at h03

/-- The support graph of the signed fixture is connected: both other
vertices are reachable from `0` along positive edges (the support is the
4-cycle `1 — 0 — 2 — 3 — 1`; the two negative edges contribute
nothing). -/
theorem sgnK4_supportGraph_connected :
    (supportGraph sgnK4Adj sgnK4Adj_isSymm).Connected := by
  have hfrom0 : ∀ v : Fin 4,
      (supportGraph sgnK4Adj sgnK4Adj_isSymm).Reachable 0 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
        ⟨by decide, by simp [sgnK4Adj]⟩ SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 2) (w := 2)
        ⟨by decide, by simp [sgnK4Adj]⟩ SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 3)
        ⟨by decide, by simp [sgnK4Adj]⟩
        (SimpleGraph.Walk.cons (u := 1) (v := 3) (w := 3)
          ⟨by decide, by simp [sgnK4Adj]⟩ SimpleGraph.Walk.nil)⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, hfrom0⟩

theorem sgnK4_fence_isolation_QA :
    sgnK4Adj.IsSymm ∧ (supportGraph sgnK4Adj sgnK4Adj_isSymm).Connected
      ∧ ¬ (∀ i j : Fin 4, 0 ≤ sgnK4Adj i j) :=
  ⟨sgnK4Adj_isSymm, sgnK4_supportGraph_connected, sgnK4Adj_not_nonneg⟩

/-- A second kernel vector: the sign pattern `![1, 1, -1, -1]` lies in
the Laplacian kernel alongside the constants — the rank-1 certificate. -/
theorem sgnK4_kernel :
    (laplacian sgnK4Adj).mulVec (![1, 1, -1, -1] : Fin 4 → ℝ) = 0 := by
  funext i
  rw [laplacian_mulVec_apply]
  fin_cases i <;>
    simp [sgnK4Adj, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val', Matrix.head_cons]

/-- The demand `e 0 − e 2` is unsolvable on the signed fixture: the
kernel vector above certifies it (its pairing with the demand is
`2 ≠ 0`). -/
theorem sgnK4_demand02_unsolvable_QA :
    ¬ ∃ f : Fin 4 → ℝ, (laplacian sgnK4Adj).mulVec f
      = Pi.single 0 (1 : ℝ) - Pi.single 2 (1 : ℝ) := by
  rintro ⟨f, hf⟩
  have h0 : Matrix.dotProduct (![1, 1, -1, -1] : Fin 4 → ℝ)
      ((laplacian sgnK4Adj).mulVec f) = 0 :=
    dotProduct_eq_zero_of_laplacian_mulVec_eq_zero sgnK4Adj sgnK4Adj_isSymm
      sgnK4_kernel
  rw [hf, Matrix.dotProduct_sub, Matrix.dotProduct_single,
    Matrix.dotProduct_single] at h0
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.head_cons] at h0

/-- **Fence (`exists_isEffectiveResistance`, `hnonneg`)**: symmetric with
connected support, yet no resistance value exists between `0` and `2` —
the existence theorem's nonnegativity hypothesis is load-bearing (the
junk-free statement would demand a witness for an unsolvable equation). -/
theorem sgnK4F_exists_hnn_fence_QA :
    ¬ (∃ r : ℝ, IsEffectiveResistance sgnK4Adj 0 2 r) := by
  rintro ⟨r, f, hf, hfr⟩
  exact sgnK4_demand02_unsolvable_QA ⟨f, hf⟩

/-- The total function's junk fallback on the signed fixture, pinned. -/
theorem sgnK4_fallback_zero_QA :
    effectiveResistance sgnK4Adj 0 2 = 0 :=
  effectiveResistance_eq_zero_of_not_exists sgnK4Adj 0 2
    sgnK4F_exists_hnn_fence_QA

/-- **Fence (`effectiveResistance_eq_quadForm`, `hnonneg`)**: the
energy-identity existence statement fails at the same fixture for the
same mechanism — no potential solves the demand, so no energy identity
can hold. -/
theorem sgnK4F_energy_hnn_fence_QA :
    ¬ (∃ f : Fin 4 → ℝ, (laplacian sgnK4Adj).mulVec f
        = Pi.single 0 (1 : ℝ) - Pi.single 2 (1 : ℝ)
        ∧ effectiveResistance sgnK4Adj 0 2
          = quadForm (laplacian sgnK4Adj) f) := by
  rintro ⟨f, hf, _⟩
  exact sgnK4_demand02_unsolvable_QA ⟨f, hf⟩

/-! ### The disconnected fixture: confinement, Dirichlet, and metric `hconn` fences -/

/-- The `e 0 − e 1` demand on the disconnected fixture is solved by
`![1, 0, 7, 7]` — the foreign component `{2, 3}` is free to sit at any
constant, here `7`, strictly above both boundary values. -/
theorem disc_demand01_seven_QA :
    (laplacian connDiscAdj).mulVec ![1, 0, 7, 7]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  rw [laplacian_mulVec_apply]
  fin_cases i <;>
    simp [connDiscAdj, Fin.sum_univ_four, Pi.single_apply, Pi.sub_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.head_cons]

/-- The min-side twin: the foreign constant `-7` sits strictly below
both boundary values. -/
theorem disc_demand01_negseven_QA :
    (laplacian connDiscAdj).mulVec ![1, 0, -7, -7]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  rw [laplacian_mulVec_apply]
  fin_cases i <;>
    simp [connDiscAdj, Fin.sum_univ_four, Pi.single_apply, Pi.sub_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.head_cons]

/-- **Fence (`laplacian_mulVec_eq_single_sub_single_le_max`, `hconn`)**:
a genuine solution of a genuine same-component demand on the symmetric
nonnegative disconnected fixture takes the foreign-component value `7`
above its boundary maximum `max 1 0 = 1` — the flood argument needs the
walk from the max-point to reach the boundary, which connectivity alone
supplies. -/
theorem discF_confinement_max_hconn_fence_QA :
    ¬ ((laplacian connDiscAdj).mulVec ![1, 0, 7, 7]
        = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ)
        → (![1, 0, 7, 7] : Fin 4 → ℝ) 2
          ≤ max ((![1, 0, 7, 7] : Fin 4 → ℝ) 0) ((![1, 0, 7, 7] : Fin 4 → ℝ) 1)) := by
  intro h
  have hcon := h disc_demand01_seven_QA
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.head_cons] at hcon

/-- **Fence (`laplacian_mulVec_eq_single_sub_single_min_le`, `hconn`)**:
the min-side twin at the foreign constant `-7`. -/
theorem discF_confinement_min_hconn_fence_QA :
    ¬ ((laplacian connDiscAdj).mulVec ![1, 0, -7, -7]
        = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ)
        → min ((![1, 0, -7, -7] : Fin 4 → ℝ) 0) ((![1, 0, -7, -7] : Fin 4 → ℝ) 1)
          ≤ (![1, 0, -7, -7] : Fin 4 → ℝ) 2) := by
  intro h
  have hcon := h disc_demand01_negseven_QA
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.head_cons] at hcon

/-- Independent energy computation: the indicator `![1, 0, 0, 0]` has
energy exactly `1` on the disconnected fixture (one unit edge leaves
vertex `0`). -/
theorem disc_energy_e0_four_QA :
    quadForm (laplacian connDiscAdj) (![1, 0, 0, 0] : Fin 4 → ℝ) = 1 := by
  rw [ecf_quadForm_lap]
  simp [Fin.sum_univ_four, connDiscAdj, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.head_cons]

/-- **Fence (`effectiveResistance_ge_sq_div_quadForm`, `hconn`)**: at
the cross-component pair `(0, 2)` the test potential `e 0` has genuine
positive energy `1` and voltage difference `1`, so the dropped-bound
reads `1 / 1 = 1 ≤ R 0 2 = 0` — the junk fallback cannot bound a genuine
Dirichlet ratio. -/
theorem discF_dirichlet_hconn_fence_QA :
    ¬ (0 < quadForm (laplacian connDiscAdj) (![1, 0, 0, 0] : Fin 4 → ℝ)
        → ((![1, 0, 0, 0] : Fin 4 → ℝ) 0 - (![1, 0, 0, 0] : Fin 4 → ℝ) 2) ^ 2
          / quadForm (laplacian connDiscAdj) (![1, 0, 0, 0] : Fin 4 → ℝ)
          ≤ effectiveResistance connDiscAdj 0 2) := by
  intro h
  have hcon := h (by rw [disc_energy_e0_four_QA]; norm_num)
  rw [disc_energy_e0_four_QA, disc_fallback_zero_QA] at hcon
  norm_num [Matrix.cons_val_zero, Matrix.cons_val', Matrix.head_cons] at hcon

/-- The mirrored cross-component demand `e 2 − e 1` is unsolvable too
(the component indicator pairing is `-1 ≠ 0`). -/
theorem disc_no_resistance_21_QA :
    ¬ ∃ r : ℝ, IsEffectiveResistance connDiscAdj 2 1 r := by
  rintro ⟨r, f, hf, hfr⟩
  have h0 : Matrix.dotProduct (![1, 1, 0, 0] : Fin 4 → ℝ)
      ((laplacian connDiscAdj).mulVec f) = 0 :=
    dotProduct_eq_zero_of_laplacian_mulVec_eq_zero connDiscAdj
      connDiscAdj_isSymm connDisc_indicator_in_kernel_QA
  rw [hf, Matrix.dotProduct_sub, Matrix.dotProduct_single,
    Matrix.dotProduct_single] at h0
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.head_cons] at h0

theorem disc_fallback_21_zero_QA :
    effectiveResistance connDiscAdj 2 1 = 0 :=
  effectiveResistance_eq_zero_of_not_exists connDiscAdj 2 1
    disc_no_resistance_21_QA

/-- **Fence (`effectiveResistance_le_add`, `hconn`)**: routing the edge
`0 — 1` through a foreign-component middle vertex reads
`1 ≤ R 0 2 + R 2 1 = 0 + 0` — both detour terms are junk fallbacks, and
the junk is not a metric. -/
theorem discF_triangle_hconn_fence_QA :
    ¬ (effectiveResistance connDiscAdj 0 1
        ≤ effectiveResistance connDiscAdj 0 2
          + effectiveResistance connDiscAdj 2 1) := by
  rw [disc_same_component_effectiveResistance_eq_one_QA, disc_fallback_zero_QA,
    disc_fallback_21_zero_QA]
  norm_num

/-- **Fence (`effectiveResistance_pos_of_ne`, `hconn`)**: distinct
cross-component vertices have `R 0 2 = 0` — the junk fallback is not
positive. -/
theorem discF_pos_hconn_fence_QA :
    ¬ ((0 : Fin 4) ≠ 2 → 0 < effectiveResistance connDiscAdj 0 2) := by
  intro h
  have h0 := h (by decide)
  rw [disc_fallback_zero_QA] at h0
  norm_num at h0

/-- **Fence (`effectiveResistance_eq_zero_iff`, `hconn`)**: the
definiteness residual's forward direction fails across components —
`R 0 2 = 0` at `0 ≠ 2`, so the iff identifies distinct vertices. -/
theorem discF_definiteness_hconn_fence_QA :
    ¬ (effectiveResistance connDiscAdj 0 2 = 0 ↔ (0 : Fin 4) = 2) := by
  intro h
  have h0 := h.1 disc_fallback_zero_QA
  exact absurd h0 (by decide)

end SpectralGraphTheory.QA
