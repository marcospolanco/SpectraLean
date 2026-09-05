/-
  Exhaustive_QA.lean

  Purpose
  -------
  Falsification-style QA for the SGT center, the assurance lever named by
  the SGT radar (QA axis: coverage previously skewed to degenerate
  single-cut instantiations, mostly by *applying* the general theorem
  under test).

  What distinguishes this module from the sibling QA files:

  - *Exhaustive sweeps with kernel-checked coverage.* Every cut of the
    three-vertex path (8 subsets) and of the four-cycle (16 subsets) is
    enumerated, and the enumeration is proved complete against
    `Finset.univ.powerset` by `decide` — so "exhaustive" is a verified
    claim, not a comment.
  - *Computation from the definitions.* Each table entry unfolds
    `boundary`/`vol`/`conductance` on a concrete cut and evaluates the
    arithmetic; the general theorems (`boundary_compl`, `vol_compl`,
    `walkTransitionMatrix_row_sum`, …) are not invoked on the path from
    definition to value. A mis-defined operator that is self-consistent
    with its own theorem family would be caught here by a wrong value.
  - *Negative witnesses.* Checks that the interfaces *separate*
    genuinely different inputs (adjacent- vs opposite-pair conductance
    `1/2` vs `1` on the cycle; Rayleigh `8/3` vs `0` on the path), and
    that a hypothesis is load-bearing (an asymmetric two-vertex weight
    on which cut duality genuinely fails, `2 ≠ 1`).

  - *Witness-layer reconciliation (2026-09-05).* The `WitnessFences`
    section below brings the file's one free-form load-bearing witness
    (`asym_boundary_not_dual_QA`, delivered 2026-08-17 before the
    per-clause fence discipline existed) into that discipline: the
    `boundary_compl` fence's proof *consumes* the free-form witness as
    its engine, and the sibling `conductance_compl` clause is fenced at
    the same fixture, completing the cut-duality pair's coverage at
    this file's own layer (both clauses are also fenced at `dirB` in
    `Spectral_QA.lean`'s Step-1 section — independent fixture,
    independent proof route).

  Fixtures are declared under fresh names rather than imported from
  sibling QA modules, keeping this module independently elaborable.
  QA-to-QA imports are no longer forbidden repository-wide (the
  2026-09-05 `edgeAdj` lattice repair made the shared
  `SpectralGraphTheory.QA` namespace co-import-safe at that name, and
  residual same-named QA fixtures are tracked by
  `scripts/check_qa_name_uniqueness.py`, renamed on demand per that
  repair's recipe) — but this file needs none.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks interfaces; it does not prove any
  axiom's truth.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Normalized
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## The three-vertex path `0 — 1 — 2` (fixture)
-/

/-- Adjacency of the path `0 — 1 — 2` on `Fin 3`: symmetric, unit
weights, degrees (1, 2, 1). -/
def exhPathAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 0; 1, 0, 1; 0, 1, 0]

theorem exhPathAdj_isSymm : exhPathAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [exhPathAdj]

theorem exhPathAdj_deg_zero : deg exhPathAdj 0 = 1 := by
  simp only [deg, exhPathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem exhPathAdj_deg_one : deg exhPathAdj 1 = 2 := by
  simp only [deg, exhPathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem exhPathAdj_deg_two : deg exhPathAdj 2 = 1 := by
  simp only [deg, exhPathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

/-!
## Kernel-checked cut enumeration on `Fin 3`
-/

/-- The eight listed cuts are *exactly* the subsets of `Fin 3` — decided
by the kernel. This is the coverage certificate for every sweep below. -/
theorem cuts3_eq :
    (Finset.univ.powerset : Finset (Finset (Fin 3)))
      = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, Finset.univ} := by
  decide

/-- Complement facts for `Fin 3`, each decided by the kernel. Made
local simp facts so that every concrete-complement form appearing in a
cut computation normalizes to an explicit set. -/
theorem compl0 : ({0} : Finset (Fin 3))ᶜ = {1, 2} := by decide

theorem compl1 : ({1} : Finset (Fin 3))ᶜ = {0, 2} := by decide

theorem compl2 : ({2} : Finset (Fin 3))ᶜ = {0, 1} := by decide

theorem compl01 : ({0, 1} : Finset (Fin 3))ᶜ = {2} := by decide

theorem compl02 : ({0, 2} : Finset (Fin 3))ᶜ = {1} := by decide

theorem compl12 : ({1, 2} : Finset (Fin 3))ᶜ = {0} := by decide

attribute [local simp] compl0 compl1 compl2 compl01 compl02 compl12

/-!
## The path boundary table: every cut, computed from the definition

  Expected values (edges counted from `S` to `Sᶜ`): the empty and full
  cuts have no boundary; an end singleton cuts one edge; the center
  singleton cuts two; a two-vertex side cuts the edges its complement
  does not.
-/

theorem exh_boundary_empty : boundary exhPathAdj ∅ = 0 := by
  simp [boundary]

theorem exh_boundary_univ : boundary exhPathAdj Finset.univ = 0 := by
  simp [boundary]

theorem exh_boundary_0 : boundary exhPathAdj {0} = 1 := by
  simp [boundary, exhPathAdj]

theorem exh_boundary_1 : boundary exhPathAdj {1} = 2 := by
  simp [boundary, exhPathAdj]
  norm_num

theorem exh_boundary_2 : boundary exhPathAdj {2} = 1 := by
  simp [boundary, exhPathAdj]

theorem exh_boundary_01 : boundary exhPathAdj {0, 1} = 1 := by
  simp [boundary, exhPathAdj]

theorem exh_boundary_02 : boundary exhPathAdj {0, 2} = 2 := by
  simp [boundary, exhPathAdj]
  norm_num

theorem exh_boundary_12 : boundary exhPathAdj {1, 2} = 1 := by
  simp [boundary, exhPathAdj]

/-!
## The path volume table: every cut, computed from the definition
-/

theorem exh_vol_empty : vol exhPathAdj ∅ = 0 := by
  simp [vol]

theorem exh_vol_univ : vol exhPathAdj Finset.univ = 4 := by
  simp only [vol, Fin.sum_univ_three, exhPathAdj_deg_zero,
    exhPathAdj_deg_one, exhPathAdj_deg_two]
  norm_num

theorem exh_vol_0 : vol exhPathAdj {0} = 1 := by
  simp [vol, exhPathAdj_deg_zero]

theorem exh_vol_1 : vol exhPathAdj {1} = 2 := by
  simp [vol, exhPathAdj_deg_one]

theorem exh_vol_2 : vol exhPathAdj {2} = 1 := by
  simp [vol, exhPathAdj_deg_two]

theorem exh_vol_01 : vol exhPathAdj {0, 1} = 3 := by
  simp [vol, exhPathAdj_deg_zero, exhPathAdj_deg_one]
  norm_num

theorem exh_vol_02 : vol exhPathAdj {0, 2} = 2 := by
  simp [vol, exhPathAdj_deg_zero, exhPathAdj_deg_two]
  norm_num

theorem exh_vol_12 : vol exhPathAdj {1, 2} = 3 := by
  simp [vol, exhPathAdj_deg_one, exhPathAdj_deg_two]
  norm_num

/-!
## Exhaustive duality on the path, recomposed from the tables

  Each of the eight cuts is checked against its complement using only
  the independently computed table entries above — `boundary_compl` and
  `vol_compl` are never invoked, so a definition whose two sides
  disagree at any cut fails here.
-/

theorem exh_boundary_duality_QA :
    ∀ S ∈ (Finset.univ.powerset : Finset (Finset (Fin 3))),
      boundary exhPathAdj S = boundary exhPathAdj Sᶜ := by
  intro S hS
  rw [cuts3_eq] at hS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [Finset.compl_empty, exh_boundary_empty, exh_boundary_univ]
  · rw [compl0, exh_boundary_0, exh_boundary_12]
  · rw [compl1, exh_boundary_1, exh_boundary_02]
  · rw [compl2, exh_boundary_2, exh_boundary_01]
  · rw [compl01, exh_boundary_01, exh_boundary_2]
  · rw [compl02, exh_boundary_02, exh_boundary_1]
  · rw [compl12, exh_boundary_12, exh_boundary_0]
  · rw [Finset.compl_univ, exh_boundary_univ, exh_boundary_empty]

theorem exh_vol_complementarity_QA :
    ∀ S ∈ (Finset.univ.powerset : Finset (Finset (Fin 3))),
      vol exhPathAdj S + vol exhPathAdj Sᶜ = 4 := by
  intro S hS
  rw [cuts3_eq] at hS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [Finset.compl_empty]; norm_num [exh_vol_empty, exh_vol_univ]
  · rw [compl0]; norm_num [exh_vol_0, exh_vol_12]
  · rw [compl1]; norm_num [exh_vol_1, exh_vol_02]
  · rw [compl2]; norm_num [exh_vol_2, exh_vol_01]
  · rw [compl01]; norm_num [exh_vol_01, exh_vol_2]
  · rw [compl02]; norm_num [exh_vol_02, exh_vol_1]
  · rw [compl12]; norm_num [exh_vol_12, exh_vol_0]
  · rw [Finset.compl_univ]; norm_num [exh_vol_univ, exh_vol_empty]

/-!
## Conductance on the path

  Every nonempty proper cut of the path has conductance `1` (each cut
  side meets the rest across its full smaller-side volume). The two
  shape-distinct cases are computed: the end singleton and the center
  singleton.
-/

theorem exh_conductance_0 : conductance exhPathAdj {0} = 1 := by
  rw [conductance, exh_boundary_0, compl0, exh_vol_0, exh_vol_12,
    min_eq_left (by norm_num : (1 : ℝ) ≤ 3)]
  norm_num

theorem exh_conductance_1 : conductance exhPathAdj {1} = 1 := by
  rw [conductance, exh_boundary_1, compl1, exh_vol_1, exh_vol_02, min_self]
  norm_num

/-- The path's cut interface separates the center from the ends: the
two boundary values computed above are genuinely different. -/
theorem exh_boundary_separates_QA :
    boundary exhPathAdj {0} ≠ boundary exhPathAdj {1} := by
  rw [exh_boundary_0, exh_boundary_1]
  norm_num

/-!
## The four-cycle `0 — 1 — 2 — 3 — 0` (fixture)

  A non-degenerate second fixture: 2-regular, connected, and with two
  genuinely different cut shapes (adjacent pairs cut two edges,
  opposite pairs cut four).
-/

/-- Adjacency of the cycle `C₄` on `Fin 4`: symmetric, unit weights,
all degrees `2`. -/
def cycleAdj4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0]

theorem cycleAdj4_isSymm : cycleAdj4.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [cycleAdj4]

theorem cycleAdj4_deg (i : Fin 4) : deg cycleAdj4 i = 2 := by
  fin_cases i <;>
    simp only [deg, cycleAdj4, Matrix.of_apply, Fin.sum_univ_four] <;>
    norm_num

/-- The sixteen listed cuts are *exactly* the subsets of `Fin 4` —
decided by the kernel. -/
theorem cuts4_eq :
    (Finset.univ.powerset : Finset (Finset (Fin 4)))
      = {∅, {0}, {1}, {2}, {3}, {0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3},
         {2, 3}, {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3},
         Finset.univ} := by
  decide

/-- Complement facts for `Fin 4`, each decided by the kernel; local
simp facts so that concrete complements normalize to explicit sets. -/
theorem complc_0 : ({0} : Finset (Fin 4))ᶜ = {1, 2, 3} := by decide

theorem complc_1 : ({1} : Finset (Fin 4))ᶜ = {0, 2, 3} := by decide

theorem complc_2 : ({2} : Finset (Fin 4))ᶜ = {0, 1, 3} := by decide

theorem complc_3 : ({3} : Finset (Fin 4))ᶜ = {0, 1, 2} := by decide

theorem complc_01 : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide

theorem complc_02 : ({0, 2} : Finset (Fin 4))ᶜ = {1, 3} := by decide

theorem complc_03 : ({0, 3} : Finset (Fin 4))ᶜ = {1, 2} := by decide

theorem complc_12 : ({1, 2} : Finset (Fin 4))ᶜ = {0, 3} := by decide

theorem complc_13 : ({1, 3} : Finset (Fin 4))ᶜ = {0, 2} := by decide

theorem complc_23 : ({2, 3} : Finset (Fin 4))ᶜ = {0, 1} := by decide

theorem complc_012 : ({0, 1, 2} : Finset (Fin 4))ᶜ = {3} := by decide

theorem complc_013 : ({0, 1, 3} : Finset (Fin 4))ᶜ = {2} := by decide

theorem complc_023 : ({0, 2, 3} : Finset (Fin 4))ᶜ = {1} := by decide

theorem complc_123 : ({1, 2, 3} : Finset (Fin 4))ᶜ = {0} := by decide

attribute [local simp] complc_0 complc_1 complc_2 complc_3 complc_01
  complc_02 complc_03 complc_12 complc_13 complc_23 complc_012 complc_013
  complc_023 complc_123

/-!
## The cycle boundary table: every cut, computed from the definition
-/

theorem cyc_boundary_empty : boundary cycleAdj4 ∅ = 0 := by
  simp [boundary]

theorem cyc_boundary_univ : boundary cycleAdj4 Finset.univ = 0 := by
  simp [boundary]

theorem cyc_boundary_0 : boundary cycleAdj4 {0} = 2 := by
  simp [boundary, cycleAdj4]
  norm_num

theorem cyc_boundary_1 : boundary cycleAdj4 {1} = 2 := by
  simp [boundary, cycleAdj4]
  norm_num

theorem cyc_boundary_2 : boundary cycleAdj4 {2} = 2 := by
  simp [boundary, cycleAdj4]
  norm_num

theorem cyc_boundary_3 : boundary cycleAdj4 {3} = 2 := by
  simp [boundary, cycleAdj4]
  norm_num

theorem cyc_boundary_01 : boundary cycleAdj4 {0, 1} = 2 := by
  simp [boundary, cycleAdj4]
  norm_num

theorem cyc_boundary_02 : boundary cycleAdj4 {0, 2} = 4 := by
  simp [boundary, cycleAdj4]
  norm_num

theorem cyc_boundary_03 : boundary cycleAdj4 {0, 3} = 2 := by
  simp [boundary, cycleAdj4]
  norm_num

theorem cyc_boundary_12 : boundary cycleAdj4 {1, 2} = 2 := by
  simp [boundary, cycleAdj4]
  norm_num

theorem cyc_boundary_13 : boundary cycleAdj4 {1, 3} = 4 := by
  simp [boundary, cycleAdj4]
  norm_num

theorem cyc_boundary_23 : boundary cycleAdj4 {2, 3} = 2 := by
  simp [boundary, cycleAdj4]
  norm_num

theorem cyc_boundary_012 : boundary cycleAdj4 {0, 1, 2} = 2 := by
  simp [boundary, cycleAdj4]
  norm_num

theorem cyc_boundary_013 : boundary cycleAdj4 {0, 1, 3} = 2 := by
  simp [boundary, cycleAdj4]
  norm_num

theorem cyc_boundary_023 : boundary cycleAdj4 {0, 2, 3} = 2 := by
  simp [boundary, cycleAdj4]
  norm_num

theorem cyc_boundary_123 : boundary cycleAdj4 {1, 2, 3} = 2 := by
  simp [boundary, cycleAdj4]
  norm_num

/-!
## Exhaustive duality on the cycle, recomposed from the table
-/

theorem cyc_boundary_duality_QA :
    ∀ S ∈ (Finset.univ.powerset : Finset (Finset (Fin 4))),
      boundary cycleAdj4 S = boundary cycleAdj4 Sᶜ := by
  intro S hS
  rw [cuts4_eq] at hS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [Finset.compl_empty, cyc_boundary_empty, cyc_boundary_univ]
  · rw [complc_0, cyc_boundary_0, cyc_boundary_123]
  · rw [complc_1, cyc_boundary_1, cyc_boundary_023]
  · rw [complc_2, cyc_boundary_2, cyc_boundary_013]
  · rw [complc_3, cyc_boundary_3, cyc_boundary_012]
  · rw [complc_01, cyc_boundary_01, cyc_boundary_23]
  · rw [complc_02, cyc_boundary_02, cyc_boundary_13]
  · rw [complc_03, cyc_boundary_03, cyc_boundary_12]
  · rw [complc_12, cyc_boundary_12, cyc_boundary_03]
  · rw [complc_13, cyc_boundary_13, cyc_boundary_02]
  · rw [complc_23, cyc_boundary_23, cyc_boundary_01]
  · rw [complc_012, cyc_boundary_012, cyc_boundary_3]
  · rw [complc_013, cyc_boundary_013, cyc_boundary_2]
  · rw [complc_023, cyc_boundary_023, cyc_boundary_1]
  · rw [complc_123, cyc_boundary_123, cyc_boundary_0]
  · rw [Finset.compl_univ, cyc_boundary_univ, cyc_boundary_empty]

/-!
## Conductance separates cut shapes on the cycle

  The two pair-cut shapes of `C₄` have genuinely different conductance:
  an adjacent pair cuts two edges over volume four (`1/2`), an opposite
  pair cuts four edges over volume four (`1`). A conductance definition
  collapsed to a constant would fail here.
-/

theorem cyc_vol_01 : vol cycleAdj4 {0, 1} = 4 := by
  simp [vol, cycleAdj4_deg]
  norm_num

theorem cyc_vol_02 : vol cycleAdj4 {0, 2} = 4 := by
  simp [vol, cycleAdj4_deg]
  norm_num

theorem cyc_vol_13 : vol cycleAdj4 {1, 3} = 4 := by
  simp [vol, cycleAdj4_deg]
  norm_num

theorem cyc_vol_23 : vol cycleAdj4 {2, 3} = 4 := by
  simp [vol, cycleAdj4_deg]
  norm_num

theorem cyc_conductance_01 : conductance cycleAdj4 {0, 1} = 1 / 2 := by
  rw [conductance, cyc_boundary_01, complc_01, cyc_vol_01, cyc_vol_23,
    min_self]
  norm_num

theorem cyc_conductance_02 : conductance cycleAdj4 {0, 2} = 1 := by
  rw [conductance, cyc_boundary_02, complc_02, cyc_vol_02, cyc_vol_13,
    min_self]
  norm_num

/-- Negative witness: the conductance interface distinguishes the
adjacent-pair cut from the opposite-pair cut on the same graph. -/
theorem cyc_conductance_separates_QA :
    conductance cycleAdj4 {0, 1} ≠ conductance cycleAdj4 {0, 2} := by
  rw [cyc_conductance_01, cyc_conductance_02]
  norm_num

/-- Duality of conductance computed on data: both sides of the
adjacent-pair cut evaluate to `1/2` independently. -/
theorem cyc_conductance_compl_QA :
    conductance cycleAdj4 {0, 1} = 1 / 2
      ∧ conductance cycleAdj4 ({0, 1} : Finset (Fin 4))ᶜ = 1 / 2 := by
  refine ⟨cyc_conductance_01, ?_⟩
  rw [conductance, complc_01, cyc_boundary_23, cyc_vol_23, complc_23,
    cyc_vol_01, min_self]
  norm_num

/-!
## Load-bearing-hypothesis witness: duality fails without symmetry
-/

/-- An asymmetric two-vertex weight: `A 0 1 = 2`, `A 1 0 = 1`. -/
def asymAdj2 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 2; 1, 0]

theorem compl2_0 : ({0} : Finset (Fin 2))ᶜ = {1} := by decide

theorem compl2_1 : ({1} : Finset (Fin 2))ᶜ = {0} := by decide

attribute [local simp] compl2_0 compl2_1

/-- Both boundary sides of the asymmetric cut compute independently. -/
theorem asym_boundary_sides :
    boundary asymAdj2 {0} = 2
      ∧ boundary asymAdj2 ({0} : Finset (Fin 2))ᶜ = 1 := by
  refine ⟨?_, ?_⟩ <;> simp [boundary, asymAdj2]

/-- Negative witness: `boundary_compl`'s symmetry hypothesis is
load-bearing — on this asymmetric weight the two sides of the would-be
duality compute to different values (`2 ≠ 1`), so the duality cannot
hold unconditionally. -/
theorem asym_boundary_not_dual_QA :
    boundary asymAdj2 {0} ≠ boundary asymAdj2 ({0} : Finset (Fin 2))ᶜ := by
  rw [asym_boundary_sides.1, asym_boundary_sides.2]
  norm_num

/-!
## Rayleigh separation on the path
-/

/-- The alternating vector `(1, -1, 1)` on the path. -/
def exhAltVec : Fin 3 → ℝ :=
  ![1, -1, 1]

theorem exhAltVec_ne_zero : exhAltVec ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [exhAltVec] at h0

theorem exhAltVec_dot : Matrix.dotProduct exhAltVec exhAltVec = 3 := by
  simp only [Matrix.dotProduct, exhAltVec, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Fin.sum_univ_three]
  norm_num

/-- The Laplacian quadratic form at the alternating vector computes to
`8`: the Dirichlet identity (proved in the center) reduces it to the
edge-difference sum, every term of which evaluates numerically —
`1·(1-(-1))²` across each of the four directed path edges, halved. -/
theorem exh_quadForm_alt : quadForm (laplacian exhPathAdj) exhAltVec = 8 := by
  rw [laplacian_quadForm exhPathAdj exhPathAdj_isSymm exhAltVec]
  simp only [exhPathAdj, exhAltVec, Matrix.of_apply, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

/-- The Rayleigh quotient of the alternating vector computes to `8/3`. -/
theorem exh_rayleigh_alt : rayleigh (laplacian exhPathAdj) exhAltVec = 8 / 3 := by
  simp only [rayleigh, if_neg exhAltVec_ne_zero, exh_quadForm_alt,
    exhAltVec_dot]

/-- The Rayleigh quotient at the constant vector is `0`: the kernel
theorem (proved in the center) kills `L *ᵥ 1`, and the denominator
evaluates to `3`. -/
theorem exh_rayleigh_ones : rayleigh (laplacian exhPathAdj) onesVec = 0 := by
  have hne : (onesVec : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [onesVec] at h0
  have hker : (laplacian exhPathAdj).mulVec onesVec = 0 :=
    laplacian_ones_in_kernel exhPathAdj
  simp only [rayleigh, if_neg hne, quadForm, hker, Matrix.dotProduct_zero]
  norm_num [onesVec, Matrix.dotProduct, Fin.sum_univ_three]

/-- Negative witness: the Rayleigh interface separates vectors — the
alternating vector's quotient `8/3` differs from the constant vector's
`0`. A degenerate (e.g. constant) `rayleigh` definition would fail. -/
theorem exh_rayleigh_separates_QA :
    rayleigh (laplacian exhPathAdj) exhAltVec
      ≠ rayleigh (laplacian exhPathAdj) onesVec := by
  rw [exh_rayleigh_alt, exh_rayleigh_ones]
  norm_num

/-!
## Walk row-stochasticity computed, not theorem-applied

  Each row sum of `walkTransitionMatrix` on the path is evaluated from
  the definition (`P i j = (deg i)⁻¹ * A i j`), independently of
  `walkTransitionMatrix_row_sum`.
-/

theorem exh_walk_row_zero :
    ∑ j, walkTransitionMatrix exhPathAdj 0 j = 1 := by
  have hrow : ∀ j, walkTransitionMatrix exhPathAdj 0 j
      = (1 : ℝ)⁻¹ * exhPathAdj 0 j := by
    intro j
    simp only [walkTransitionMatrix, Matrix.diagonal_mul, exhPathAdj_deg_zero]
  simp only [hrow, Fin.sum_univ_three]
  norm_num [exhPathAdj, Matrix.of_apply]

theorem exh_walk_row_one :
    ∑ j, walkTransitionMatrix exhPathAdj 1 j = 1 := by
  have hrow : ∀ j, walkTransitionMatrix exhPathAdj 1 j
      = (2 : ℝ)⁻¹ * exhPathAdj 1 j := by
    intro j
    simp only [walkTransitionMatrix, Matrix.diagonal_mul, exhPathAdj_deg_one]
  simp only [hrow, Fin.sum_univ_three]
  norm_num [exhPathAdj, Matrix.of_apply]

theorem exh_walk_row_two :
    ∑ j, walkTransitionMatrix exhPathAdj 2 j = 1 := by
  have hrow : ∀ j, walkTransitionMatrix exhPathAdj 2 j
      = (1 : ℝ)⁻¹ * exhPathAdj 2 j := by
    intro j
    simp only [walkTransitionMatrix, Matrix.diagonal_mul, exhPathAdj_deg_two]
  simp only [hrow, Fin.sum_univ_three]
  norm_num [exhPathAdj, Matrix.of_apply]

/-!
## Witness-layer reconciliation (2026-09-05)

  The standing audit remainder (`proposals/qa-name-collision-guard.md`,
  Part B): this file's one free-form load-bearing witness —
  `asym_boundary_not_dual_QA`, delivered 2026-08-17, weeks before the
  per-clause fence discipline existed — is reconciled into that
  discipline here. The `boundary_compl` fence below consumes the
  free-form witness as its proof engine (the reconciliation proper);
  the sibling `conductance_compl` clause is fenced at the same
  `asymAdj2` fixture through pinned conductance values, completing the
  cut-duality pair's coverage at this file's own layer. The other
  negative-flavored checks above are classified, not converted: the
  three `*_separates_QA` theorems are interface-separation checks
  (positive computations that distinct inputs evaluate distinctly —
  they falsify a *collapsed* definition, not a dropped hypothesis), so
  they have no per-clause fence form.

  Clause-surface context: every other hypothesis-bearing statement this
  file computes from is fenced at its home QA file — the duality pair
  also at `dirB` (`Spectral_QA.lean`, Step 1), the walk layer's `hd`
  clauses at `nfIso`/`nfNegEdge` (`Normalized_QA.lean`, section C),
  `laplacian_quadForm`'s `hA`/`hnn` at `dirA`/`sfNegEdge`
  (`Spectral_QA.lean`, Step 1). The fences below are independent
  second fixtures with independent proof routes; `vol_compl`,
  `boundary_empty`/`_univ`, `walkTransitionMatrix_apply`, and
  `laplacian_ones_in_kernel` are hypothesis-free (nothing to fence).

  All proofs are real Lean proofs (no `sorry`/`admit`); `#print axioms`
  on every declaration below reads exactly `propext,
  Classical.choice, Quot.sound` (theorem instantiations of an
  all-proved shelf; no `-- @refutes` tags — nothing admitted consumed).
-/

/-- Entry pin: the forward arc carries weight `2`. -/
theorem exhAsym_01 : asymAdj2 0 1 = 2 := rfl

/-- Entry pin: the return arc carries weight `1`. -/
theorem exhAsym_10 : asymAdj2 1 0 = 1 := rfl

/-- Isolation for the duality fences: `asymAdj2` is genuinely outside
the dropped symmetric cone (`2 ≠ 1` at the off-diagonal pair), so the
fences below kill the clause, not an accidental corner inside it. -/
theorem exhAsym_not_isSymm : ¬ asymAdj2.IsSymm := by
  intro h
  have h01 := h.apply 0 1
  rw [exhAsym_01, exhAsym_10] at h01
  norm_num at h01

/-- Degree pin: the asymmetric two-network has degrees `(2, 1)`. -/
theorem exhAsym_deg_zero : deg asymAdj2 0 = 2 := by
  simp only [deg, asymAdj2, Matrix.of_apply, Fin.sum_univ_two]
  norm_num

/-- Degree pin. -/
theorem exhAsym_deg_one : deg asymAdj2 1 = 1 := by
  simp only [deg, asymAdj2, Matrix.of_apply, Fin.sum_univ_two]
  norm_num

/-- Volume pin: `vol {0} = 2`. -/
theorem exhAsym_vol_zero : vol asymAdj2 ({0} : Finset (Fin 2)) = 2 := by
  simp only [vol, Finset.sum_singleton, exhAsym_deg_zero]

/-- Volume pin: `vol {1} = 1`. -/
theorem exhAsym_vol_one : vol asymAdj2 ({1} : Finset (Fin 2)) = 1 := by
  simp only [vol, Finset.sum_singleton, exhAsym_deg_one]

/-- Boundary pin at the `{1}` cut: the free-form witness's complement
side (`boundary {0}ᶜ = 1`), transferred to the singleton form through
the decided complement fact. -/
theorem exhAsym_boundary_one : boundary asymAdj2 ({1} : Finset (Fin 2)) = 1 := by
  rw [← compl2_0]
  exact asym_boundary_sides.2

/-- Conductance of the `{0}` cut: `2 / min(2, 1) = 2`. -/
theorem exhAsym_conductance_zero :
    conductance asymAdj2 ({0} : Finset (Fin 2)) = 2 := by
  rw [conductance, asym_boundary_sides.1, exhAsym_vol_zero, compl2_0,
    exhAsym_vol_one, min_eq_right (by norm_num : (1 : ℝ) ≤ 2)]
  norm_num

/-- Conductance of the complementary `{1}` cut: `1 / min(1, 2) = 1`. -/
theorem exhAsym_conductance_one :
    conductance asymAdj2 ({1} : Finset (Fin 2)) = 1 := by
  rw [conductance, compl2_1, exhAsym_boundary_one, exhAsym_vol_one,
    exhAsym_vol_zero, min_eq_left (by norm_num : (1 : ℝ) ≤ 2)]
  norm_num

/-- Conductance of the complement cut, pinned for the fence below. -/
theorem exhAsym_conductance_compl :
    conductance asymAdj2 ({0} : Finset (Fin 2))ᶜ = 1 := by
  rw [compl2_0]
  exact exhAsym_conductance_one

/-- **Fence (`hA` clause of `boundary_compl`) — reconciliation.**
Dropping the symmetric cone is refuted at this file's own asymmetric
fixture, `S = {0}`: the two directions of the cut carry different
weight, `2 ≠ 1`. The proof *consumes* the 2026-08-17 free-form
witness `asym_boundary_not_dual_QA` as its engine — the witness is now
inside the per-clause discipline. Isolation: `exhAsym_not_isSymm`;
kept clauses: none (the theorem's only hypothesis is the dropped
one). -/
theorem exh_boundary_compl_hA_fence_QA :
    ¬ ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (S : Finset (Fin 2)),
      boundary A S = boundary A Sᶜ := by
  intro h
  exact asym_boundary_not_dual_QA (h asymAdj2 {0})

/-- **Fence (`hA` clause of `conductance_compl`).** The sibling duality
statement fails at the same fixture through the pinned conductance
values: `conductance {0} = 2 ≠ 1 = conductance {0}ᶜ` — cut
canonicalization needs symmetry at the conductance level too, not just
the boundary level. Isolation: `exhAsym_not_isSymm`. -/
theorem exh_conductance_compl_hA_fence_QA :
    ¬ ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (S : Finset (Fin 2)),
      conductance A S = conductance A Sᶜ := by
  intro h
  have h1 := h asymAdj2 {0}
  rw [exhAsym_conductance_zero, exhAsym_conductance_compl] at h1
  norm_num at h1

/-- Packaged isolation for the walk row-sum layer: the path sits
inside the `hd : ∀ i, 0 < deg A i` cone (degrees `(1, 2, 1)`), so the
three `exh_walk_row_*` computations above are genuine positive
instances of `walkTransitionMatrix_row_sum` — positive-side
companions to `Normalized_QA.lean`'s C1 fence, which kills the dropped
statement at a zero-degree fixture outside the cone. -/
theorem exhPathAdj_deg_pos : ∀ i, 0 < deg exhPathAdj i := by
  intro i
  fin_cases i <;>
    simp [exhPathAdj_deg_zero, exhPathAdj_deg_one, exhPathAdj_deg_two]

end SpectralGraphTheory.QA
