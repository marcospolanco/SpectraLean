/-
  IrreducibleStationary_QA.lean

  QA for `Scaffold.Mathlib.GraphTheory.IrreducibleStationary`
  (`proposals/irreducible-stationary-distributions.md`) — the first
  theorem consumer of the admitted `perron_frobenius` axiom. The QA
  obligations are the proposal's three mandated witnesses:

  1. *The asymmetric directed fixture* — the star
     `A₃ = !![0,1,1; 1,0,0; 1,0,0]` on `Fin 3` (on two vertices row
     normalization always symmetrizes an irreducible walk, so a
     genuinely directed witness needs three). All four hypotheses
     hand-verified; the `∃!` instantiated; the hand value
     `(1/2, 1/4, 1/4)` verified **completely raw** (all three
     predicates by hand matrix arithmetic against pinned walk
     entries), and the uniqueness clause *identified against* it:
     every stationary distribution of `A₃`, however produced, equals
     the hand value.

  2. *The symmetric-cone agreement* — on the edge `K₂`, the
     Perron–Frobenius-unique stationary distribution equals
     `stationaryVec` (the degree/volume combinatorial formula). Two
     independent API paths to one value: the axiom route's `∃!`
     versus the shelf's `stationaryVec_pos`/`sum_stationaryVec`/
     `walk_isStationary` (proved from detailed balance, no
     Perron–Frobenius anywhere in that chain). A disagreement would
     falsify one of the two routes.

  3. *The reducibility fence* — two disjoint edges on `Fin 4`: the
     hypothesis-free `∃!` conclusion is **refuted in proved form**
     (two distinct stationary distributions exhibited, nonnegativity
     and positive degrees verified intact), and the scale-uniqueness
     theorem's hypothesis-free form is refuted on the same fixture
     (the two witnesses are provably not positive scalar multiples).
     Irreducibility is thereby exercised as a fence, not decoration.

  All fixtures are rational, so every quantity is pinned by
  `norm_num`-class arithmetic. The axiom-consuming declarations below
  inherit `perron_frobenius` (checked by `#print axioms`); the raw
  entry/predicate lemmas do not.

  Pin-technique notes (the run's recorded traps): entry and degree
  lemmas at *literal* indices match `simp only`/`rw` freely, but under
  `fin_cases` the substituted indices match only `simp [lemma]` at
  predicate level — so every finite sum is evaluated through literal
  component lemmas and assembled by `funext` + `fin_cases` + `exact`
  (defeq-closed), never through a sum-unfolding simp under `fin_cases`.
-/

import Scaffold.Mathlib.GraphTheory.IrreducibleStationary
import Scaffold.Mathlib.GraphTheory.Mixing
import Mathlib.Data.Matrix.Notation

open scoped Matrix

open Matrix

namespace Scaffold.QA.SpectralGraph

open SpectralGraphTheory

/-! ### The asymmetric directed star on `Fin 3` -/

/-- The asymmetric witness: arcs `0 → 1`, `0 → 2` and back `1 → 0`,
`2 → 0` — strongly connected, not symmetrizable by row normalization
(the walk is the `0`-rooted star with return arcs; stationary mass
`(1/2, 1/4, 1/4)`, not uniform). -/
def A3 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of !![0, 1, 1; 1, 0, 0; 1, 0, 0]

theorem A3_00 : A3 0 0 = 0 := rfl
theorem A3_01 : A3 0 1 = 1 := rfl
theorem A3_02 : A3 0 2 = 1 := rfl
theorem A3_10 : A3 1 0 = 1 := rfl
theorem A3_11 : A3 1 1 = 0 := rfl
theorem A3_12 : A3 1 2 = 0 := rfl
theorem A3_20 : A3 2 0 = 1 := rfl
theorem A3_21 : A3 2 1 = 0 := rfl
theorem A3_22 : A3 2 2 = 0 := rfl

/-- Nonnegativity of the asymmetric fixture, entrywise. -/
theorem A3_nonneg_QA : ∀ i j, 0 ≤ A3 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [A3_00, A3_01, A3_02, A3_10, A3_11,
    A3_12, A3_20, A3_21, A3_22]

/-- Out-degrees of the asymmetric fixture: `deg = (2, 1, 1)`. -/
theorem A3_deg_0 : deg A3 0 = 2 := by
  simp only [deg, Fin.sum_univ_three, A3_00, A3_01, A3_02]
  norm_num
theorem A3_deg_1 : deg A3 1 = 1 := by
  simp only [deg, Fin.sum_univ_three, A3_10, A3_11, A3_12]
  norm_num
theorem A3_deg_2 : deg A3 2 = 1 := by
  simp only [deg, Fin.sum_univ_three, A3_20, A3_21, A3_22]
  norm_num

theorem A3_deg_QA : ∀ i, 0 < deg A3 i := by
  intro i
  fin_cases i <;> simp [A3_deg_0, A3_deg_1, A3_deg_2]

/-- The fixture is irreducible: every vertex reaches the hub `0` and
the hub reaches every vertex — all nine pairs by reflexivity, one
arc, or two arcs through the hub. -/
theorem A3_irreducible_QA : A3.IsIrreducible := by
  have h01 : Relation.ReflTransGen (fun a b => 0 < A3 a b) 0 1 :=
    .single (by rw [A3_01]; norm_num)
  have h02 : Relation.ReflTransGen (fun a b => 0 < A3 a b) 0 2 :=
    .single (by rw [A3_02]; norm_num)
  have h10 : Relation.ReflTransGen (fun a b => 0 < A3 a b) 1 0 :=
    .single (by rw [A3_10]; norm_num)
  have h20 : Relation.ReflTransGen (fun a b => 0 < A3 a b) 2 0 :=
    .single (by rw [A3_20]; norm_num)
  intro i j
  fin_cases i <;> fin_cases j <;> first
    | exact Relation.ReflTransGen.refl
    | exact h01
    | exact h02
    | exact h10
    | exact h20
    | exact h10.trans h02
    | exact h20.trans h01

theorem A3_ex_QA : ∃ i j, 0 < A3 i j := ⟨0, 1, by rw [A3_01]; norm_num⟩

/-- The walk of the fixture: `P 0 1 = P 0 2 = 1/2`, `P 1 0 = P 2 0 = 1`,
all other entries zero — the row-normalized asymmetric star. -/
theorem A3P_01 : walkTransitionMatrix A3 0 1 = 1 / 2 := by
  rw [walkTransitionMatrix_apply, A3_deg_0, A3_01]; norm_num
theorem A3P_02 : walkTransitionMatrix A3 0 2 = 1 / 2 := by
  rw [walkTransitionMatrix_apply, A3_deg_0, A3_02]; norm_num
theorem A3P_10 : walkTransitionMatrix A3 1 0 = 1 := by
  rw [walkTransitionMatrix_apply, A3_deg_1, A3_10]; norm_num
theorem A3P_20 : walkTransitionMatrix A3 2 0 = 1 := by
  rw [walkTransitionMatrix_apply, A3_deg_2, A3_20]; norm_num
theorem A3P_00 : walkTransitionMatrix A3 0 0 = 0 := by
  rw [walkTransitionMatrix_apply, A3_deg_0, A3_00]; norm_num
theorem A3P_11 : walkTransitionMatrix A3 1 1 = 0 := by
  rw [walkTransitionMatrix_apply, A3_deg_1, A3_11]; norm_num
theorem A3P_12 : walkTransitionMatrix A3 1 2 = 0 := by
  rw [walkTransitionMatrix_apply, A3_deg_1, A3_12]; norm_num
theorem A3P_21 : walkTransitionMatrix A3 2 1 = 0 := by
  rw [walkTransitionMatrix_apply, A3_deg_2, A3_21]; norm_num
theorem A3P_22 : walkTransitionMatrix A3 2 2 = 0 := by
  rw [walkTransitionMatrix_apply, A3_deg_2, A3_22]; norm_num

/-- The hand-computed stationary distribution of the asymmetric star:
mass `1/2` at the hub, `1/4` at each leaf. -/
noncomputable def pi3 : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]

theorem pi3_0 : pi3 0 = 1 / 2 := rfl
theorem pi3_1 : pi3 1 = 1 / 4 := rfl
theorem pi3_2 : pi3 2 = 1 / 4 := rfl

/-- **The raw route, part 1:** the hand value is nonnegative. -/
theorem pi3_nonneg_QA : ∀ i, 0 ≤ pi3 i := by
  intro i; fin_cases i <;> simp [pi3_0, pi3_1, pi3_2]

/-- **The raw route, part 2:** the hand value sums to one. -/
theorem pi3_sum_QA : ∑ i, pi3 i = 1 := by
  simp only [Fin.sum_univ_three, pi3_0, pi3_1, pi3_2]
  norm_num

/-- **The raw route, part 3, coordinate 0:** hub mass stays at the hub
— `1/4 + 1/4 = 1/2` against the pinned walk column. -/
theorem pi3_stat_0 : (pi3 ᵥ* walkTransitionMatrix A3) 0 = pi3 0 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three, pi3_0,
    pi3_1, pi3_2, A3P_00, A3P_10, A3P_20]
  norm_num

/-- **The raw route, part 3, coordinate 1:** leaf 1's mass flows
`1/2 · 1/2 = 1/4`. -/
theorem pi3_stat_1 : (pi3 ᵥ* walkTransitionMatrix A3) 1 = pi3 1 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three, pi3_0,
    pi3_1, pi3_2, A3P_01, A3P_11, A3P_21]
  norm_num

/-- **The raw route, part 3, coordinate 2:** leaf 2 mirrors leaf 1. -/
theorem pi3_stat_2 : (pi3 ᵥ* walkTransitionMatrix A3) 2 = pi3 2 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three, pi3_0,
    pi3_1, pi3_2, A3P_02, A3P_12, A3P_22]
  norm_num

/-- **The raw route, assembled:** the hand value is stationary —
direct entrywise arithmetic against the pinned walk entries, no
Perron–Frobenius, no theorem, just the defining sums. -/
theorem pi3_stationary_raw_QA : pi3 ᵥ* walkTransitionMatrix A3 = pi3 := by
  funext j
  fin_cases j
  · exact pi3_stat_0
  · exact pi3_stat_1
  · exact pi3_stat_2

/-- **The theorem route:** the `∃!` instantiated on the fixture
(conditional on `perron_frobenius`). -/
theorem A3_existsUnique_stationary_QA :
    ∃! π : Fin 3 → ℝ, (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧
      π ᵥ* walkTransitionMatrix A3 = π :=
  existsUnique_stationaryVec_of_irreducible A3 A3_nonneg_QA A3_irreducible_QA
    A3_ex_QA A3_deg_QA

/-- **The identification (the load-bearing join):** every stationary
distribution of the asymmetric fixture — however produced — equals the
hand value. Composes the theorem's uniqueness clause with the raw
route's predicate verification: the raw route proves the predicate
satisfiable, the theorem route proves at most one distribution exists,
and together they pin the value exactly. -/
theorem A3_stationary_eq_hand_QA (π : Fin 3 → ℝ)
    (hπnn : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπs : π ᵥ* walkTransitionMatrix A3 = π) : π = pi3 := by
  obtain ⟨τ, -, huniq⟩ := A3_existsUnique_stationary_QA
  rw [huniq π ⟨hπnn, hπsum, hπs⟩, huniq pi3 ⟨pi3_nonneg_QA, pi3_sum_QA,
    pi3_stationary_raw_QA⟩]

theorem pi3_ne_zero_QA : pi3 ≠ 0 := by
  intro h
  have hsum := pi3_sum_QA
  rw [h] at hsum
  simp at hsum

/-- **Full support instantiated:** the strictly-positive conclusion of
`stationaryVec_pos_of_irreducible` reads exactly the hand values at
every vertex of the fixture. -/
theorem A3_full_support_QA : ∀ i, 0 < pi3 i :=
  stationaryVec_pos_of_irreducible A3 A3_nonneg_QA A3_irreducible_QA
    A3_ex_QA A3_deg_QA pi3_nonneg_QA pi3_ne_zero_QA pi3_stationary_raw_QA

/-! ### The symmetric-cone agreement on `K₂` -/

/-- The undirected edge: on the symmetric cone both routes must agree. -/
def A2 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of !![0, 1; 1, 0]

theorem A2_nonneg_QA : ∀ i j, 0 ≤ A2 i j := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [A2]

theorem A2_deg_QA : ∀ i, 0 < deg A2 i := by
  intro i; fin_cases i <;> simp [deg, A2, Fin.sum_univ_two]

theorem A2_symm_QA : A2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [A2]

theorem A2_irreducible_QA : A2.IsIrreducible := by
  have h01 : Relation.ReflTransGen (fun a b => 0 < A2 a b) 0 1 :=
    .single (by simp [A2])
  have h10 : Relation.ReflTransGen (fun a b => 0 < A2 a b) 1 0 :=
    .single (by simp [A2])
  intro i j
  fin_cases i <;> fin_cases j <;> first
    | exact Relation.ReflTransGen.refl
    | exact h01
    | exact h10

theorem A2_ex_QA : ∃ i j, 0 < A2 i j := ⟨0, 1, by simp [A2]⟩

/-- **The agreement:** the Perron–Frobenius-unique stationary
distribution of the edge equals the shelf's combinatorial
`stationaryVec` (degree over volume). The predicate for
`stationaryVec A2` is supplied entirely by the shelf's detailed-balance
chain — `stationaryVec_pos`, `sum_stationaryVec`, `walk_isStationary`
(its stationary form flipped to `vecMul` through
`Matrix.mulVec_transpose`) — none of which touches
Perron–Frobenius; the uniqueness is the axiom route's. Two independent
API paths, one value. -/
theorem A2_stationary_eq_stationaryVec_QA (π : Fin 2 → ℝ)
    (hπnn : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπs : π ᵥ* walkTransitionMatrix A2 = π) :
    π = stationaryVec A2 := by
  have hsvnn : ∀ i, 0 ≤ stationaryVec A2 i := fun i =>
    le_of_lt (stationaryVec_pos A2 A2_deg_QA i)
  have hsvsum : ∑ i, stationaryVec A2 i = 1 :=
    sum_stationaryVec A2 A2_deg_QA
  have hsvs : stationaryVec A2 ᵥ* walkTransitionMatrix A2
      = stationaryVec A2 :=
    (Matrix.mulVec_transpose _ _).symm.trans
      (walk_isStationary A2 A2_symm_QA A2_deg_QA)
  obtain ⟨τ, -, huniq⟩ := existsUnique_stationaryVec_of_irreducible A2
    A2_nonneg_QA A2_irreducible_QA A2_ex_QA A2_deg_QA
  rw [huniq π ⟨hπnn, hπsum, hπs⟩,
    huniq (stationaryVec A2) ⟨hsvnn, hsvsum, hsvs⟩]

/-- The combinatorial stationary vector of the edge, coordinate 0,
through its own definition. -/
theorem A2_sv_0 : stationaryVec A2 0 = 1 / 2 := by
  simp only [stationaryVec, vol, deg, A2, Fin.sum_univ_two]
  norm_num

/-- The combinatorial stationary vector of the edge, coordinate 1. -/
theorem A2_sv_1 : stationaryVec A2 1 = 1 / 2 := by
  simp only [stationaryVec, vol, deg, A2, Fin.sum_univ_two]
  norm_num

/-- The combinatorial route's value pinned: `(1/2, 1/2)`. Together with
the identification above, the axiom route's unique distribution is
pinned to the same value by both routes. -/
theorem A2_stationaryVec_eq_half_QA : stationaryVec A2 = ![1 / 2, 1 / 2] := by
  funext i
  fin_cases i
  · exact A2_sv_0
  · exact A2_sv_1

/-! ### The reducibility fence: two disjoint edges on `Fin 4` -/

/-- The reducible fixture: two disjoint undirected edges. Degrees are
all `1` and the walk is the fixture itself; stationary mass can live
in either block independently. -/
def A4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

theorem A4_00 : A4 0 0 = 0 := rfl
theorem A4_01 : A4 0 1 = 1 := rfl
theorem A4_02 : A4 0 2 = 0 := rfl
theorem A4_03 : A4 0 3 = 0 := rfl
theorem A4_10 : A4 1 0 = 1 := rfl
theorem A4_11 : A4 1 1 = 0 := rfl
theorem A4_12 : A4 1 2 = 0 := rfl
theorem A4_13 : A4 1 3 = 0 := rfl
theorem A4_20 : A4 2 0 = 0 := rfl
theorem A4_21 : A4 2 1 = 0 := rfl
theorem A4_22 : A4 2 2 = 0 := rfl
theorem A4_23 : A4 2 3 = 1 := rfl
theorem A4_30 : A4 3 0 = 0 := rfl
theorem A4_31 : A4 3 1 = 0 := rfl
theorem A4_32 : A4 3 2 = 1 := rfl
theorem A4_33 : A4 3 3 = 0 := rfl

theorem A4_nonneg_QA : ∀ i j, 0 ≤ A4 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [A4_00, A4_01, A4_02, A4_03, A4_10,
    A4_11, A4_12, A4_13, A4_20, A4_21, A4_22, A4_23, A4_30, A4_31, A4_32,
    A4_33]

/-- Every hypothesis of the delivered theorems except irreducibility
holds on the fixture: positive out-degrees (all `1`). -/
theorem A4_deg_0 : deg A4 0 = 1 := by
  simp only [deg, Fin.sum_univ_four, A4_00, A4_01, A4_02, A4_03]
  norm_num
theorem A4_deg_1 : deg A4 1 = 1 := by
  simp only [deg, Fin.sum_univ_four, A4_10, A4_11, A4_12, A4_13]
  norm_num
theorem A4_deg_2 : deg A4 2 = 1 := by
  simp only [deg, Fin.sum_univ_four, A4_20, A4_21, A4_22, A4_23]
  norm_num
theorem A4_deg_3 : deg A4 3 = 1 := by
  simp only [deg, Fin.sum_univ_four, A4_30, A4_31, A4_32, A4_33]
  norm_num

theorem A4_deg_QA : ∀ i, 0 < deg A4 i := by
  intro i
  fin_cases i <;> simp [A4_deg_0, A4_deg_1, A4_deg_2, A4_deg_3]

theorem A4_deg_one (i : Fin 4) : deg A4 i = 1 := by
  fin_cases i <;> simp [A4_deg_0, A4_deg_1, A4_deg_2, A4_deg_3]

/-- The walk of the reducible fixture is the fixture itself (degrees
`1`: row normalization does nothing), so the block structure is the
walk. -/
theorem A4P_eq (i j : Fin 4) : walkTransitionMatrix A4 i j = A4 i j := by
  rw [walkTransitionMatrix_apply, A4_deg_one i, inv_one, one_mul]

/-- First stationary witness: all mass in the first block. -/
noncomputable def pi4a : Fin 4 → ℝ := ![1 / 2, 1 / 2, 0, 0]

/-- Second stationary witness: all mass in the second block. -/
noncomputable def pi4b : Fin 4 → ℝ := ![0, 0, 1 / 2, 1 / 2]

theorem pi4a_0 : pi4a 0 = 1 / 2 := rfl
theorem pi4a_1 : pi4a 1 = 1 / 2 := rfl
theorem pi4a_2 : pi4a 2 = 0 := rfl
theorem pi4a_3 : pi4a 3 = 0 := rfl
theorem pi4b_0 : pi4b 0 = 0 := rfl
theorem pi4b_1 : pi4b 1 = 0 := rfl
theorem pi4b_2 : pi4b 2 = 1 / 2 := rfl
theorem pi4b_3 : pi4b 3 = 1 / 2 := rfl

theorem pi4a_stat_0 : (pi4a ᵥ* walkTransitionMatrix A4) 0 = pi4a 0 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_four, A4P_eq,
    pi4a_0, pi4a_1, pi4a_2, pi4a_3, A4_00, A4_10, A4_20, A4_30]
  norm_num
theorem pi4a_stat_1 : (pi4a ᵥ* walkTransitionMatrix A4) 1 = pi4a 1 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_four, A4P_eq,
    pi4a_0, pi4a_1, pi4a_2, pi4a_3, A4_01, A4_11, A4_21, A4_31]
  norm_num
theorem pi4a_stat_2 : (pi4a ᵥ* walkTransitionMatrix A4) 2 = pi4a 2 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_four, A4P_eq,
    pi4a_0, pi4a_1, pi4a_2, pi4a_3, A4_02, A4_12, A4_22, A4_32]
  norm_num
theorem pi4a_stat_3 : (pi4a ᵥ* walkTransitionMatrix A4) 3 = pi4a 3 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_four, A4P_eq,
    pi4a_0, pi4a_1, pi4a_2, pi4a_3, A4_03, A4_13, A4_23, A4_33]
  norm_num

theorem pi4b_stat_0 : (pi4b ᵥ* walkTransitionMatrix A4) 0 = pi4b 0 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_four, A4P_eq,
    pi4b_0, pi4b_1, pi4b_2, pi4b_3, A4_00, A4_10, A4_20, A4_30]
  norm_num
theorem pi4b_stat_1 : (pi4b ᵥ* walkTransitionMatrix A4) 1 = pi4b 1 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_four, A4P_eq,
    pi4b_0, pi4b_1, pi4b_2, pi4b_3, A4_01, A4_11, A4_21, A4_31]
  norm_num
theorem pi4b_stat_2 : (pi4b ᵥ* walkTransitionMatrix A4) 2 = pi4b 2 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_four, A4P_eq,
    pi4b_0, pi4b_1, pi4b_2, pi4b_3, A4_02, A4_12, A4_22, A4_32]
  norm_num
theorem pi4b_stat_3 : (pi4b ᵥ* walkTransitionMatrix A4) 3 = pi4b 3 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_four, A4P_eq,
    pi4b_0, pi4b_1, pi4b_2, pi4b_3, A4_03, A4_13, A4_23, A4_33]
  norm_num

/-- **The raw route, witness 1:** nonnegative, mass one, and stationary
by direct entrywise arithmetic. -/
theorem pi4a_pred_QA : (∀ i, 0 ≤ pi4a i) ∧ (∑ i, pi4a i = 1) ∧
    pi4a ᵥ* walkTransitionMatrix A4 = pi4a := by
  refine ⟨by intro i; fin_cases i <;> simp [pi4a_0, pi4a_1, pi4a_2, pi4a_3],
    by simp only [Fin.sum_univ_four, pi4a_0, pi4a_1, pi4a_2, pi4a_3]; norm_num,
    ?_⟩
  funext j
  fin_cases j
  · exact pi4a_stat_0
  · exact pi4a_stat_1
  · exact pi4a_stat_2
  · exact pi4a_stat_3

/-- **The raw route, witness 2:** the same three predicates, all mass
in the second block. -/
theorem pi4b_pred_QA : (∀ i, 0 ≤ pi4b i) ∧ (∑ i, pi4b i = 1) ∧
    pi4b ᵥ* walkTransitionMatrix A4 = pi4b := by
  refine ⟨by intro i; fin_cases i <;> simp [pi4b_0, pi4b_1, pi4b_2, pi4b_3],
    by simp only [Fin.sum_univ_four, pi4b_0, pi4b_1, pi4b_2, pi4b_3]; norm_num,
    ?_⟩
  funext j
  fin_cases j
  · exact pi4b_stat_0
  · exact pi4b_stat_1
  · exact pi4b_stat_2
  · exact pi4b_stat_3

theorem pi4a_ne_zero_QA : pi4a ≠ 0 := by
  intro h
  have hsum := pi4a_pred_QA.2.1
  rw [h] at hsum
  simp at hsum

theorem pi4b_ne_zero_QA : pi4b ≠ 0 := by
  intro h
  have hsum := pi4b_pred_QA.2.1
  rw [h] at hsum
  simp at hsum

/-- The two witnesses are distinct distributions. -/
theorem pi4a_ne_pi4b_QA : pi4a ≠ pi4b := by
  intro h
  have h0 : pi4a 0 = pi4b 0 := congrFun h 0
  rw [pi4a_0, pi4b_0] at h0
  norm_num at h0

/-- **The fence, part 1 (the `∃!` refuted):** the hypothesis-free
conclusion of `existsUnique_stationaryVec_of_irreducible` is false on
the reducible fixture — two distinct stationary distributions exist,
with nonnegativity and positive degrees verified intact, so the
falsity is attributable to the dropped irreducibility hypothesis
alone. -/
theorem A4_existsUnique_refuted_QA :
    ¬ ∃! π : Fin 4 → ℝ, (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧
      π ᵥ* walkTransitionMatrix A4 = π := by
  intro h
  obtain ⟨τ, -, huniq⟩ := h
  exact pi4a_ne_pi4b_QA
    ((huniq pi4a pi4a_pred_QA).trans (huniq pi4b pi4b_pred_QA).symm)

/-- **The fence, part 2 (scale uniqueness refuted):** the
hypothesis-free conclusion of `stationaryVec_smul_of_irreducible` is
false on the same fixture — the two stationary distributions are
provably not related by a positive scalar (matching them at the `0`
coordinate forces the scalar to `0`, against its positivity). -/
theorem A4_smul_unique_refuted_QA :
    ¬ ∀ (σ τ : Fin 4 → ℝ), (∀ i, 0 ≤ σ i) → σ ≠ 0 →
      σ ᵥ* walkTransitionMatrix A4 = σ → (∀ i, 0 ≤ τ i) → τ ≠ 0 →
      τ ᵥ* walkTransitionMatrix A4 = τ → ∃ c : ℝ, 0 < c ∧ τ = c • σ := by
  intro h
  obtain ⟨c, hc, heq⟩ := h pi4a pi4b pi4a_pred_QA.1 pi4a_ne_zero_QA
    pi4a_pred_QA.2.2 pi4b_pred_QA.1 pi4b_ne_zero_QA pi4b_pred_QA.2.2
  have h0 : c * (1 / 2) = 0 := by
    have h00 := congrFun heq 0
    rw [pi4b_0, Pi.smul_apply, smul_eq_mul, pi4a_0] at h00
    exact h00.symm
  have hpos : 0 < c * (1 / 2) := by positivity
  linarith

end Scaffold.QA.SpectralGraph
