/-
  IrreducibleStationary_QA.lean

  QA for `Scaffold.Mathlib.GraphTheory.IrreducibleStationary`
  (`proposals/irreducible-stationary-distributions.md`; the theorem
  layer was re-proved without axiom contact 2026-09-02 by
  `proposals/cesaro-stationary-existence.md`). The QA obligations are
  the original proposal's three mandated witnesses:

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
  `norm_num`-class arithmetic. Since the 2026-09-02 Cesàro re-proof no
  declaration below consumes `perron_frobenius` (checked by
  `#print axioms`); the raw entry/predicate lemmas never did. The
  Section E mechanism lemmas pin the new engine's behavior: the
  orbit/oscillation pins, the one-period Cesàro mean exactly
  stationary, the power-positivity instances, the engine-output
  identification, the min-ratio scalar, and the reducible-input
  existence instantiation.

  4. *The adversarial fence audit* (2026-09-05,
     `proposals/adversarial-fences-irreducible-stationary-family.md`):
     the `AdversarialFences` section below closes the shelf's entire
     clause surface with per-clause hypothesis-form fences — the two
     refutations in item 3 above are hypothesis-free and proved only
     that *some* hypothesis is load-bearing. All 256 of its
     declarations are at the standard three axioms.

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

/-! ### Section E: the Cesàro engine's mechanism

The new engine's behavior pinned on the asymmetric star (the Section A
fixture): the orbit of `1` and its oscillation, the one-period Cesàro
mean exactly stationary (the engine's whole point — the powers
oscillate forever, the average over a period does not move at all),
power positivity at the pinned return arc, the engine's output
identified against the hand value, the min-ratio scalar pinned
exactly, and existence instantiated on the reducible fixture where
uniqueness and positivity provably fail. -/

/-- The orbit's first step, entry 0, raw. -/
theorem A3g1_0 : ((1 : Fin 3 → ℝ) ᵥ* walkTransitionMatrix A3) 0 = 2 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Pi.one_apply, Fin.sum_univ_three,
    A3P_00, A3P_10, A3P_20]
  norm_num

/-- The orbit's first step, entry 1, raw. -/
theorem A3g1_1 : ((1 : Fin 3 → ℝ) ᵥ* walkTransitionMatrix A3) 1 = 1 / 2 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Pi.one_apply, Fin.sum_univ_three,
    A3P_01, A3P_11, A3P_21]
  norm_num

/-- The orbit's first step, entry 2, raw. -/
theorem A3g1_2 : ((1 : Fin 3 → ℝ) ᵥ* walkTransitionMatrix A3) 2 = 1 / 2 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Pi.one_apply, Fin.sum_univ_three,
    A3P_02, A3P_12, A3P_22]
  norm_num

/-- **The orbit's first step, assembled**: the walk's column sums. -/
theorem A3_orbit_step_QA :
    ((1 : Fin 3 → ℝ) ᵥ* walkTransitionMatrix A3) = ![2, 1 / 2, 1 / 2] := by
  funext j
  fin_cases j
  · exact A3g1_0
  · exact A3g1_1
  · exact A3g1_2

theorem A3g2_0 : ((1 : Fin 3 → ℝ) ᵥ* (walkTransitionMatrix A3 ^ 2)) 0 = 1 := by
  rw [pow_two, ← vecMul_mul, A3_orbit_step_QA]
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    A3P_00, A3P_10, A3P_20]
  norm_num

theorem A3g2_1 : ((1 : Fin 3 → ℝ) ᵥ* (walkTransitionMatrix A3 ^ 2)) 1 = 1 := by
  rw [pow_two, ← vecMul_mul, A3_orbit_step_QA]
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    A3P_01, A3P_11, A3P_21]
  norm_num

theorem A3g2_2 : ((1 : Fin 3 → ℝ) ᵥ* (walkTransitionMatrix A3 ^ 2)) 2 = 1 := by
  rw [pow_two, ← vecMul_mul, A3_orbit_step_QA]
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    A3P_02, A3P_12, A3P_22]
  norm_num

/-- **The orbit's second step, assembled**: after one period the orbit
of `1` returns to `1`. -/
theorem A3_orbit_two_QA :
    ((1 : Fin 3 → ℝ) ᵥ* (walkTransitionMatrix A3 ^ 2)) = 1 := by
  funext j
  fin_cases j
  · exact A3g2_0
  · exact A3g2_1
  · exact A3g2_2

/-- **The orbit provably oscillates** — the raw walk's orbit of `1` is
genuinely period-two, so the engine's input sequence never converges;
only its averages do (the finite-chain echo of `DirectedMixing_QA`'s
`P2_no_limit`). -/
theorem A3_orbit_oscillates_QA :
    ((1 : Fin 3 → ℝ) ᵥ* walkTransitionMatrix A3)
      ≠ ((1 : Fin 3 → ℝ) ᵥ* (walkTransitionMatrix A3 ^ 2)) := by
  intro h
  have h0 := congrFun h 0
  rw [A3_orbit_step_QA, A3_orbit_two_QA, Pi.one_apply] at h0
  simp only [Matrix.cons_val_zero] at h0
  norm_num at h0

/-- **The Cesàro mean over one full period is exactly stationary** on
the periodic fixture — the engine's mechanism in one line: the powers
oscillate forever (the fence above), the average over a period does
not move at all. -/
theorem A3_mean_period_stationary_QA :
    (((2 : ℕ) : ℝ)⁻¹ • ((1 : Fin 3 → ℝ) + (1 : Fin 3 → ℝ) ᵥ* walkTransitionMatrix A3)) ᵥ*
        walkTransitionMatrix A3
      = ((2 : ℕ) : ℝ)⁻¹ • ((1 : Fin 3 → ℝ) + (1 : Fin 3 → ℝ) ᵥ* walkTransitionMatrix A3) := by
  have hstep : ((1 : Fin 3 → ℝ) ᵥ* walkTransitionMatrix A3) ᵥ* walkTransitionMatrix A3
      = (1 : Fin 3 → ℝ) := by
    rw [vecMul_mul, ← pow_two]
    exact A3_orbit_two_QA
  rw [Matrix.vecMul_smul, Matrix.add_vecMul, hstep]
  congr 1
  exact add_comm _ _

/-- The mean's entry values, raw. -/
theorem A3mean_0 :
    (((2 : ℕ) : ℝ)⁻¹ • ((1 : Fin 3 → ℝ) + (1 : Fin 3 → ℝ) ᵥ* walkTransitionMatrix A3)) 0
      = 3 / 2 := by
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.one_apply, A3g1_0]
  norm_num

theorem A3mean_1 :
    (((2 : ℕ) : ℝ)⁻¹ • ((1 : Fin 3 → ℝ) + (1 : Fin 3 → ℝ) ᵥ* walkTransitionMatrix A3)) 1
      = 3 / 4 := by
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.one_apply, A3g1_1]
  norm_num

theorem A3mean_2 :
    (((2 : ℕ) : ℝ)⁻¹ • ((1 : Fin 3 → ℝ) + (1 : Fin 3 → ℝ) ᵥ* walkTransitionMatrix A3)) 2
      = 3 / 4 := by
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.one_apply, A3g1_2]
  norm_num

theorem pi3x3_0 : ((3 : ℝ) • pi3) 0 = 3 / 2 := by
  simp only [Pi.smul_apply, smul_eq_mul, pi3_0]; norm_num
theorem pi3x3_1 : ((3 : ℝ) • pi3) 1 = 3 / 4 := by
  simp only [Pi.smul_apply, smul_eq_mul, pi3_1]; norm_num
theorem pi3x3_2 : ((3 : ℝ) • pi3) 2 = 3 / 4 := by
  simp only [Pi.smul_apply, smul_eq_mul, pi3_2]; norm_num

/-- **The mean's value**: exactly three times the hand-verified
stationary distribution (mass `3 = card (Fin 3)`, the engine's
normalization of the orbit of `1`). -/
theorem A3_mean_val_QA :
    ((2 : ℕ) : ℝ)⁻¹ • ((1 : Fin 3 → ℝ) + (1 : Fin 3 → ℝ) ᵥ* walkTransitionMatrix A3)
      = (3 : ℝ) • pi3 := by
  funext j
  fin_cases j
  · exact A3mean_0.trans pi3x3_0.symm
  · exact A3mean_1.trans pi3x3_1.symm
  · exact A3mean_2.trans pi3x3_2.symm

/-- **Power positivity instantiated, the pinned return arc**: the
leaf's return needs the second power, pinned raw at the exact entry
`(P²) 1 1 = 1/2`. -/
theorem A3_pow_pos_return_QA : 0 < (walkTransitionMatrix A3 ^ 2) 1 1 := by
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_three,
    A3P_10, A3P_11, A3P_12, A3P_01, A3P_11, A3P_21]
  norm_num

/-- **Power positivity, the existence form**: every pair joined by
some strictly-positive power on the irreducible fixture. -/
theorem A3_pow_pos_QA (i j : Fin 3) :
    ∃ m : ℕ, 0 < (walkTransitionMatrix A3 ^ m) i j :=
  exists_pow_pos_of_isIrreducible
    (walkTransitionMatrix_nonneg A3 A3_nonneg_QA A3_deg_QA)
    (walkTransitionMatrix_isIrreducible A3 A3_irreducible_QA A3_deg_QA) i j

/-- **The engine's output identified**: every nonnegative mass-three
stationary vector of the fixture is exactly three times the hand
value. -/
theorem A3_engine_identified_QA (σ : Fin 3 → ℝ) (hσnn : ∀ i, 0 ≤ σ i)
    (hσmass : ∑ i, σ i = 3) (hσs : σ ᵥ* walkTransitionMatrix A3 = σ) :
    σ = (3 : ℝ) • pi3 := by
  have hνsum : ∑ i, ((3 : ℝ)⁻¹ • σ) i = 1 := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [hσmass, inv_mul_cancel₀ (by norm_num : ((3 : ℝ) ≠ 0))]
  have hνstat : ((3 : ℝ)⁻¹ • σ) ᵥ* walkTransitionMatrix A3 = (3 : ℝ)⁻¹ • σ := by
    rw [Matrix.vecMul_smul, hσs]
  have hνeq : (3 : ℝ)⁻¹ • σ = pi3 :=
    A3_stationary_eq_hand_QA _
      (fun i => mul_nonneg (inv_nonneg.mpr (by norm_num)) (hσnn i)) hνsum hνstat
  have hback : σ = (3 : ℝ) • ((3 : ℝ)⁻¹ • σ) := by
    rw [smul_smul, mul_inv_cancel₀ (by norm_num : ((3 : ℝ) ≠ 0)), one_smul]
  rw [hback, hνeq]

/-- **The min-ratio clause pinned**: two stationary multiples, the
produced scalar is exactly the ratio `1/4`. -/
theorem A3_smul_ratio_QA :
    ∃ c : ℝ, 0 < c ∧ (3 : ℝ) • pi3 = c • ((12 : ℝ) • pi3) ∧ c = 1 / 4 := by
  have hstat : ∀ k : ℝ, (k • pi3) ᵥ* walkTransitionMatrix A3 = k • pi3 := fun k => by
    rw [Matrix.vecMul_smul, pi3_stationary_raw_QA]
  have hnn : ∀ k : ℝ, 0 < k → ∀ i, 0 ≤ (k • pi3) i := fun k hk i => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (le_of_lt hk) (pi3_nonneg_QA i)
  have hne : ∀ k : ℝ, 0 < k → (k • pi3) ≠ 0 := by
    intro k hk h
    have h0 : pi3 0 = 0 := by
      have happ : (k • pi3) 0 = 0 := congrFun h 0
      simp only [Pi.smul_apply, smul_eq_mul] at happ
      exact (mul_eq_zero.mp happ).resolve_left (fun hk0 => absurd hk0 (ne_of_gt hk))
    rw [pi3_0] at h0
    norm_num at h0
  obtain ⟨c, hc, heq⟩ := stationaryVec_smul_of_irreducible A3 A3_nonneg_QA
    A3_irreducible_QA A3_ex_QA A3_deg_QA
    (hnn 12 (by norm_num)) (hne 12 (by norm_num)) (hstat 12)
    (hnn 3 (by norm_num)) (hne 3 (by norm_num)) (hstat 3)
  refine ⟨c, hc, heq, ?_⟩
  have h0 : (3 : ℝ) * pi3 0 = c * (12 * pi3 0) := by
    have happ := congrFun heq 0
    simp only [Pi.smul_apply, smul_eq_mul] at happ
    exact happ
  rw [pi3_0] at h0
  norm_num at h0
  linarith

/-- **The existence engine needs no irreducibility**: it instantiates
unconditionally on the reducible two-block fixture — where uniqueness
and positivity provably fail (the fences above) — the honest scope
pin: existence is strictly weaker than what irreducibility buys. -/
theorem A4_engine_existence_QA :
    ∃ σ : Fin 4 → ℝ, (∀ i, 0 ≤ σ i) ∧ (∑ i, σ i = 4) ∧
      σ ᵥ* walkTransitionMatrix A4 = σ :=
  exists_nonneg_stationary_of_row_stochastic
    (walkTransitionMatrix_nonneg A4 A4_nonneg_QA A4_deg_QA)
    (fun i => walkTransitionMatrix_row_sum A4 A4_deg_QA i)

/-! ### AdversarialFences: the adversarial fence audit

The audit method's twenty-first application
(`proposals/adversarial-fences-irreducible-stationary-family.md`,
2026-09-05): per-clause hypothesis-form fences over the shelf's entire
theorem surface — the two delivered refutations above are
hypothesis-free (they drop the whole stack at `A4`), so until this
section no per-clause necessity information existed anywhere. Each
fence states the theorem's conclusion with exactly one clause dropped
and refutes it at a fixture where every kept clause is genuine
(isolation companions pin the dropped clause's genuine failure);
`#print axioms` on every declaration below reads exactly `propext,
Classical.choice, Quot.sound` — theorem instantiations of an
all-proved shelf, nothing admitted consumed, no `-- @refutes` tags.

Headline mechanisms, each a first witness of its class:

- the Krylov–Bogoliubov cluster lemma's `hgnn` falls to the
  Jordan-block fixture `jordanM = !![0, 1; -1, 2]]` — the mass-constant
  orbit `jg s = ![2 - s, s - 1]` escapes the simplex entrywise, which
  is exactly where the telescoping defect bound `|g 0 j| ≤ m` needed
  nonnegativity;
- the `hnn` clauses of the whole walk-level stationary family fall to
  three complementary signed fixtures: `wpNegAdj` (one-dimensional
  mixed-sign fixed space — no positive fixed vector), `smNegAdj`
  (two-dimensional fixed space meeting the nonneg cone in a wedge — two
  nonneg stationary rays that are not multiples, and a whole segment of
  mass-one distributions), and `spNegAdj` (nonneg stationary mass
  vanishing on strong support through signed cancellation);
- `exists_pow_pos_of_isIrreducible`'s `hnn` falls to the rank-one
  fixture `ppNegM` (`M² = 8 • M`): every power is a positive scalar
  multiple of `M`, so the pair `(1, 2)` entry keeps its sign forever —
  cancellation cannot flip it (impossible on `Fin 2`, where strong
  connectivity forces both off-diagonal arcs positive);
- the `hdeg`/`hex` clauses are truth-removable and delivered as proved
  strengthening companions: `deg_pos_of_nonneg_irreducible` derives
  `hdeg` from `hnn + hirr + hex` (first-arc route), and
  `exists_pos_entry_of_deg_pos` derives `hex` from one positive row sum
  alone — with `exists_walkPerronVector_of_hex` restating the existence
  theorem at the strictly weaker hypothesis set.
-/

section AdversarialFences

/-! #### Generic ReflTransGen helpers -/

/-- A relation whose every step is a self-loop has reflexive-transitive
closures that never move: the closure of a self-only relation is the
identity. Generic support for the identity-matrix reducibility
witnesses. -/
theorem rtg_eq_of_self {α : Type} {r : α → α → Prop} (h : ∀ a b, r a b → a = b)
    {a b : α} (hrtg : Relation.ReflTransGen r a b) : a = b := by
  induction hrtg with
  | refl => rfl
  | @tail c d _ hstep ih => exact ih.trans (h _ _ hstep)

/-- A nontrivial reachability starts with a first arc: if `i` reaches a
*distinct* `j`, some single step leaves `i`. Generic support for the
`hdeg`-derivation strengthening (`deg_pos_of_nonneg_irreducible`). -/
theorem exists_arc_of_rtg {α : Type} {r : α → α → Prop} {i j : α}
    (h : Relation.ReflTransGen r i j) (hij : i ≠ j) : ∃ b, r i b := by
  rcases h.cases_head with h' | ⟨c, hc, -⟩
  · exact absurd h' hij
  · exact ⟨c, hc⟩

/-- A positive entry of the identity forces the index pair to coincide. -/
theorem one2_entry_pos_self (a b : Fin 2)
    (hab : 0 < (1 : Matrix (Fin 2) (Fin 2) ℝ) a b) : a = b := by
  simp only [Matrix.one_apply] at hab
  split_ifs at hab with h
  · exact h
  · exact absurd hab (by norm_num)

/-! #### A1/A2: the identity fixtures -/

/-- **Fence (`h` clause of `isIrreducible_transpose`).** Dropping
irreducibility is refuted at the identity matrix: the transpose of the
identity is the identity, whose only arcs are self-loops, so vertex `0`
cannot reach vertex `1`. -/
theorem isIrreducible_transpose_h_fence_QA :
    ¬ ∀ M : Matrix (Fin 2) (Fin 2) ℝ, Mᵀ.IsIrreducible := by
  intro h
  have h1 := h (1 : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Matrix.transpose_one] at h1
  have h01 : (0 : Fin 2) = 1 := rtg_eq_of_self one2_entry_pos_self (h1 0 1)
  exact absurd h01 (by decide)

/-- The degrees of the `Fin 2` identity are all `1`. -/
theorem id2_deg_one (i : Fin 2) : deg (1 : Matrix (Fin 2) (Fin 2) ℝ) i = 1 := by
  fin_cases i <;> simp [deg, Fin.sum_univ_two, Matrix.one_apply]

/-- **Fence (`hirr` clause of `walkTransitionMatrix_isIrreducible`).**
Dropping irreducibility is refuted at the identity (degrees `1`, so the
walk is the identity itself): reducibility survives normalization
verbatim. -/
theorem walkTransitionMatrix_isIrreducible_hirr_fence_QA :
    ¬ ∀ A : Matrix (Fin 2) (Fin 2) ℝ, (∀ i, 0 < deg A i) →
      (walkTransitionMatrix A).IsIrreducible := by
  intro h
  have hdeg1 : ∀ i, 0 < deg (1 : Matrix (Fin 2) (Fin 2) ℝ) i :=
    fun i => by rw [id2_deg_one]; norm_num
  have h1 := h 1 hdeg1
  have hP : walkTransitionMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    ext i j
    rw [walkTransitionMatrix_apply, id2_deg_one, inv_one, one_mul]
  rw [hP] at h1
  have h01 : (0 : Fin 2) = 1 := rtg_eq_of_self one2_entry_pos_self (h1 0 1)
  exact absurd h01 (by decide)

/-! #### A3: the zero-degree signed fixture `zdAdj` -/

/-- The `hdeg` breaker: strong positive arcs with a canceling negative
diagonal — irreducibility genuine, `deg 0 = 0`, and the junk `0⁻¹ = 0`
zeroes the walk's row `0`. -/
def zdAdj : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of !![-1, 1; 1, 1]

theorem zdAdj_00 : zdAdj 0 0 = -1 := rfl
theorem zdAdj_01 : zdAdj 0 1 = 1 := rfl
theorem zdAdj_10 : zdAdj 1 0 = 1 := rfl
theorem zdAdj_11 : zdAdj 1 1 = 1 := rfl

/-- Isolation: irreducibility is genuine — both off-diagonal arcs. -/
theorem zdAdj_irreducible_QA : zdAdj.IsIrreducible := by
  have h01 : Relation.ReflTransGen (fun a b => 0 < zdAdj a b) 0 1 :=
    .single (by rw [zdAdj_01]; norm_num)
  have h10 : Relation.ReflTransGen (fun a b => 0 < zdAdj a b) 1 0 :=
    .single (by rw [zdAdj_10]; norm_num)
  intro i j
  fin_cases i <;> fin_cases j <;> first
    | exact Relation.ReflTransGen.refl
    | exact h01
    | exact h10

/-- The degrees: `(0, 2)` — the canceling row. -/
theorem zdAdj_deg_0 : deg zdAdj 0 = 0 := by
  simp only [deg, Fin.sum_univ_two, zdAdj_00, zdAdj_01]
  ring

theorem zdAdj_deg_1 : deg zdAdj 1 = 2 := by
  simp only [deg, Fin.sum_univ_two, zdAdj_10, zdAdj_11]
  norm_num

/-- Isolation: the dropped clause genuinely fails (`deg 0 = 0`). -/
theorem zdAdj_not_deg_pos : ¬ ∀ i, 0 < deg zdAdj i := by
  intro h
  have h0 := h 0
  rw [zdAdj_deg_0] at h0
  exact absurd h0 (by norm_num)

/-- The junk zeroing: the walk's row `0` is identically zero. -/
theorem zdAdj_P_row_zero (c : Fin 2) : walkTransitionMatrix zdAdj 0 c = 0 := by
  simp only [walkTransitionMatrix_apply, zdAdj_deg_0]
  norm_num

/-- **Fence (`hdeg` clause of `walkTransitionMatrix_isIrreducible`).**
Dropping positive degrees is refuted at `zdAdj`: irreducibility is
genuine, but the junk `0⁻¹ = 0` zeroes the walk's row `0`, so no arc
ever leaves vertex `0`. -/
theorem walkTransitionMatrix_isIrreducible_hdeg_fence_QA :
    ¬ ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.IsIrreducible →
      (walkTransitionMatrix A).IsIrreducible := by
  intro h
  have h1 := h zdAdj zdAdj_irreducible_QA
  rcases (h1 0 1).cases_head with h01 | ⟨c, hc, -⟩
  · exact absurd h01 (by decide)
  · rw [zdAdj_P_row_zero] at hc
    exact absurd hc (by norm_num)

/-! #### A5–A7: the row-action lemmas -/

/-- **Fence (`hrow` clause of `sum_vecMul_eq_of_row_sum`).** Dropping
row-stochasticity is refuted at the zero matrix: mass is annihilated
(`0 ≠ 1`). -/
theorem sum_vecMul_eq_of_row_sum_hrow_fence_QA :
    ¬ ∀ (M : Matrix (Fin 1) (Fin 1) ℝ) (v : Fin 1 → ℝ),
      ∑ j, (v ᵥ* M) j = ∑ j, v j := by
  intro h
  have h1 := h (0 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Fin 1 → ℝ)
  simp only [Matrix.vecMul, Matrix.dotProduct, Matrix.zero_apply,
    Fin.sum_univ_one, Pi.one_apply] at h1
  norm_num at h1

/-- **Fence (`hrow` clause of `pow_row_sum`).** Same fixture at
`t = 1`: the zero power row sums to `0 ≠ 1`. -/
theorem pow_row_sum_hrow_fence_QA :
    ¬ ∀ (M : Matrix (Fin 1) (Fin 1) ℝ) (t : ℕ) (i : Fin 1),
      ∑ j, (M ^ t) i j = 1 := by
  intro h
  have h1 := h (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 0
  rw [pow_one] at h1
  simp [Matrix.zero_apply] at h1

/-- **Fence (`hnn` clause of `pow_entry_nonneg`).** Dropping
nonnegativity is refuted at `-1 • 1`, `t = 1`: the entry is `-1`. -/
theorem pow_entry_nonneg_hnn_fence_QA :
    ¬ ∀ (M : Matrix (Fin 1) (Fin 1) ℝ) (t : ℕ) (i j : Fin 1),
      0 ≤ (M ^ t) i j := by
  intro h
  have h1 := h ((-1 : ℝ) • 1 : Matrix (Fin 1) (Fin 1) ℝ) 1 0 0
  rw [pow_one, Matrix.smul_apply, Matrix.one_apply, if_pos rfl] at h1
  norm_num at h1

/-! #### A8/A9: the `pow_entry_le_one` pair -/

/-- The `hnn` breaker: row sums `1` genuine, the negative entry off to
the side — the `(0,0)` entry `2 > 1` at `t = 1`. -/
def leOneA : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of !![2, -1; 0, 1]

theorem leOneA_00 : leOneA 0 0 = 2 := rfl
theorem leOneA_01 : leOneA 0 1 = -1 := rfl
theorem leOneA_10 : leOneA 1 0 = 0 := rfl
theorem leOneA_11 : leOneA 1 1 = 1 := rfl

/-- Isolation: the kept `hrow` clause is genuine. -/
theorem leOneA_row_sum (i : Fin 2) : ∑ j, leOneA i j = 1 := by
  fin_cases i
  · simp [Fin.sum_univ_two, leOneA_00, leOneA_01]; norm_num
  · simp [Fin.sum_univ_two, leOneA_10, leOneA_11]

/-- **Fence (`hnn` clause of `pow_entry_le_one`).** -/
theorem pow_entry_le_one_hnn_fence_QA :
    ¬ ∀ (M : Matrix (Fin 2) (Fin 2) ℝ), (∀ i, ∑ j, M i j = 1) →
      ∀ (t : ℕ) (i j : Fin 2), (M ^ t) i j ≤ 1 := by
  intro h
  have h1 := h leOneA leOneA_row_sum 1 0 0
  rw [pow_one, leOneA_00] at h1
  norm_num at h1

/-- The `hrow` breaker: nonnegative genuine, the row sum `2 ≠ 1`. -/
def leOneB : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of !![0, 2; 0, 0]

theorem leOneB_00 : leOneB 0 0 = 0 := rfl
theorem leOneB_01 : leOneB 0 1 = 2 := rfl
theorem leOneB_10 : leOneB 1 0 = 0 := rfl
theorem leOneB_11 : leOneB 1 1 = 0 := rfl

/-- Isolation: the kept `hnn` clause is genuine. -/
theorem leOneB_nonneg (i j : Fin 2) : 0 ≤ leOneB i j := by
  fin_cases i <;> fin_cases j <;> simp [leOneB_00, leOneB_01, leOneB_10, leOneB_11]

/-- **Fence (`hrow` clause of `pow_entry_le_one`).** -/
theorem pow_entry_le_one_hrow_fence_QA :
    ¬ ∀ (M : Matrix (Fin 2) (Fin 2) ℝ), (∀ i j, 0 ≤ M i j) →
      ∀ (t : ℕ) (i j : Fin 2), (M ^ t) i j ≤ 1 := by
  intro h
  have h1 := h leOneB leOneB_nonneg 1 0 1
  rw [pow_one, leOneB_01] at h1
  norm_num at h1

/-! #### B1: the nilpotent fixture `nilM` -/

/-- The `hirr` breaker: nonnegative with vertex `1` stranded — no power
ever carries mass from `1` to `0`. -/
def nilM : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of !![0, 1; 0, 0]

theorem nilM_00 : nilM 0 0 = 0 := rfl
theorem nilM_01 : nilM 0 1 = 1 := rfl
theorem nilM_10 : nilM 1 0 = 0 := rfl
theorem nilM_11 : nilM 1 1 = 0 := rfl

/-- Isolation: the kept `hnn` clause is genuine. -/
theorem nilM_nonneg (i j : Fin 2) : 0 ≤ nilM i j := by
  fin_cases i <;> fin_cases j <;> simp [nilM_00, nilM_01, nilM_10, nilM_11]

/-- Isolation: the dropped clause genuinely fails (vertex `1` has no
outgoing arc — a zero row). -/
theorem nilM_not_irreducible : ¬ nilM.IsIrreducible := by
  intro h
  rcases (h 1 0).cases_head with h10 | ⟨c, hc, -⟩
  · exact absurd h10 (by decide)
  · fin_cases c <;> simp [nilM_10, nilM_11] at hc

/-- Every positive power's `(1, 0)` entry is zero: the whole first
column of `nilM` is zero, so every product's row-`1` contribution
through it vanishes. -/
theorem nilM_pow_succ_10 (k : ℕ) : (nilM ^ (k + 1)) 1 0 = 0 := by
  rw [pow_succ, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  fin_cases l <;> simp [nilM_00, nilM_10]

/-- **Fence (`hirr` clause of `exists_pow_pos_of_isIrreducible`).** -/
theorem exists_pow_pos_hirr_fence_QA :
    ¬ ∀ (M : Matrix (Fin 2) (Fin 2) ℝ), (∀ i j, 0 ≤ M i j) →
      ∀ (i j : Fin 2), ∃ m : ℕ, 0 < (M ^ m) i j := by
  intro h
  obtain ⟨m, hm⟩ := h nilM nilM_nonneg 1 0
  obtain _ | k := m
  · rw [pow_zero] at hm; simp [Matrix.one_apply] at hm
  · rw [nilM_pow_succ_10] at hm; norm_num at hm

/-! #### B2: the rank-one power-sign fixture `ppNegM` -/

/-- The `hnn` breaker for power positivity: the rank-one matrix
`u ⊗ v` with `u = (1, -1, 1)`, `v = (-1, 1, 10)` — irreducible through
five positive arcs, but `M² = 8 • M`, so every power is a positive
scalar times `M` and the pair `(1, 2)` entry stays negative forever. -/
def ppNegM : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of !![-1, 1, 10; 1, -1, -10; -1, 1, 10]

theorem ppNegM_00 : ppNegM 0 0 = -1 := rfl
theorem ppNegM_01 : ppNegM 0 1 = 1 := rfl
theorem ppNegM_02 : ppNegM 0 2 = 10 := rfl
theorem ppNegM_10 : ppNegM 1 0 = 1 := rfl
theorem ppNegM_11 : ppNegM 1 1 = -1 := rfl
theorem ppNegM_12 : ppNegM 1 2 = -10 := rfl
theorem ppNegM_20 : ppNegM 2 0 = -1 := rfl
theorem ppNegM_21 : ppNegM 2 1 = 1 := rfl
theorem ppNegM_22 : ppNegM 2 2 = 10 := rfl

/-- Isolation: the dropped clause genuinely fails. -/
theorem ppNegM_not_nonneg : ¬ ∀ i j, 0 ≤ ppNegM i j := by
  intro h
  have h00 := h 0 0
  rw [ppNegM_00] at h00
  exact absurd h00 (by norm_num)

/-- Isolation: irreducibility is genuine — arcs `0→1, 0→2, 1→0, 2→1,
2→2` make the support digraph strongly connected. -/
theorem ppNegM_irreducible_QA : ppNegM.IsIrreducible := by
  have h01 : Relation.ReflTransGen (fun a b => 0 < ppNegM a b) 0 1 :=
    .single (by rw [ppNegM_01]; norm_num)
  have h02 : Relation.ReflTransGen (fun a b => 0 < ppNegM a b) 0 2 :=
    .single (by rw [ppNegM_02]; norm_num)
  have h10 : Relation.ReflTransGen (fun a b => 0 < ppNegM a b) 1 0 :=
    .single (by rw [ppNegM_10]; norm_num)
  have h21 : Relation.ReflTransGen (fun a b => 0 < ppNegM a b) 2 1 :=
    .single (by rw [ppNegM_21]; norm_num)
  intro i j
  fin_cases i <;> fin_cases j <;> first
    | exact Relation.ReflTransGen.refl
    | exact h01
    | exact h02
    | exact h10
    | exact h21
    | exact h10.trans h01
    | exact h10.trans h02
    | exact h21.trans h10

/-- The rank-one square identity, entry `(0,0)`: `M² = 8 • M` (the
contraction `v ⬝ᵥ u = 8`). -/
theorem ppNegM_sq_00 : (ppNegM ^ 2) 0 0 = (8 : ℝ) * ppNegM 0 0 := by
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_three,
    ppNegM_00, ppNegM_01, ppNegM_02, ppNegM_10, ppNegM_11, ppNegM_12,
    ppNegM_20, ppNegM_21, ppNegM_22]
  norm_num

theorem ppNegM_sq_01 : (ppNegM ^ 2) 0 1 = (8 : ℝ) * ppNegM 0 1 := by
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_three,
    ppNegM_00, ppNegM_01, ppNegM_02, ppNegM_10, ppNegM_11, ppNegM_12,
    ppNegM_20, ppNegM_21, ppNegM_22]
  norm_num

theorem ppNegM_sq_02 : (ppNegM ^ 2) 0 2 = (8 : ℝ) * ppNegM 0 2 := by
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_three,
    ppNegM_00, ppNegM_01, ppNegM_02, ppNegM_10, ppNegM_11, ppNegM_12,
    ppNegM_20, ppNegM_21, ppNegM_22]
  norm_num

theorem ppNegM_sq_10 : (ppNegM ^ 2) 1 0 = (8 : ℝ) * ppNegM 1 0 := by
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_three,
    ppNegM_00, ppNegM_01, ppNegM_02, ppNegM_10, ppNegM_11, ppNegM_12,
    ppNegM_20, ppNegM_21, ppNegM_22]
  norm_num

theorem ppNegM_sq_11 : (ppNegM ^ 2) 1 1 = (8 : ℝ) * ppNegM 1 1 := by
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_three,
    ppNegM_00, ppNegM_01, ppNegM_02, ppNegM_10, ppNegM_11, ppNegM_12,
    ppNegM_20, ppNegM_21, ppNegM_22]
  norm_num

theorem ppNegM_sq_12 : (ppNegM ^ 2) 1 2 = (8 : ℝ) * ppNegM 1 2 := by
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_three,
    ppNegM_00, ppNegM_01, ppNegM_02, ppNegM_10, ppNegM_11, ppNegM_12,
    ppNegM_20, ppNegM_21, ppNegM_22]
  norm_num

theorem ppNegM_sq_20 : (ppNegM ^ 2) 2 0 = (8 : ℝ) * ppNegM 2 0 := by
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_three,
    ppNegM_00, ppNegM_01, ppNegM_02, ppNegM_10, ppNegM_11, ppNegM_12,
    ppNegM_20, ppNegM_21, ppNegM_22]
  norm_num

theorem ppNegM_sq_21 : (ppNegM ^ 2) 2 1 = (8 : ℝ) * ppNegM 2 1 := by
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_three,
    ppNegM_00, ppNegM_01, ppNegM_02, ppNegM_10, ppNegM_11, ppNegM_12,
    ppNegM_20, ppNegM_21, ppNegM_22]
  norm_num

theorem ppNegM_sq_22 : (ppNegM ^ 2) 2 2 = (8 : ℝ) * ppNegM 2 2 := by
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_three,
    ppNegM_00, ppNegM_01, ppNegM_02, ppNegM_10, ppNegM_11, ppNegM_12,
    ppNegM_20, ppNegM_21, ppNegM_22]
  norm_num

/-- The rank-one square identity assembled. -/
theorem ppNegM_sq : ppNegM ^ 2 = (8 : ℝ) • ppNegM := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · exact ppNegM_sq_00
  · exact ppNegM_sq_01
  · exact ppNegM_sq_02
  · exact ppNegM_sq_10
  · exact ppNegM_sq_11
  · exact ppNegM_sq_12
  · exact ppNegM_sq_20
  · exact ppNegM_sq_21
  · exact ppNegM_sq_22

/-- Every positive power is a positive scalar times `M`. -/
theorem ppNegM_pow_succ (k : ℕ) : ppNegM ^ (k + 1) = (8 : ℝ) ^ k • ppNegM := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, smul_mul_assoc, ← pow_two, ppNegM_sq, smul_smul, ← pow_succ]

/-- The pair `(1, 2)` entry is negative at every positive power. -/
theorem ppNegM_pow_12_neg (k : ℕ) : (ppNegM ^ (k + 1)) 1 2 < 0 := by
  have h8 : (0 : ℝ) < (8 : ℝ) ^ k := by positivity
  have hmul := mul_neg_of_pos_of_neg h8 (by norm_num : (-10 : ℝ) < 0)
  rw [ppNegM_pow_succ, Matrix.smul_apply, smul_eq_mul, ppNegM_12]
  exact hmul

/-- **Fence (`hnn` clause of `exists_pow_pos_of_isIrreducible`).** The
power entries have `m`-constant sign — cancellation cannot flip them —
so the pair `(1, 2)` never goes positive. -/
theorem exists_pow_pos_hnn_fence_QA :
    ¬ ∀ (M : Matrix (Fin 3) (Fin 3) ℝ), M.IsIrreducible →
      ∀ (i j : Fin 3), ∃ m : ℕ, 0 < (M ^ m) i j := by
  intro h
  obtain ⟨m, hm⟩ := h ppNegM ppNegM_irreducible_QA 1 2
  obtain _ | k := m
  · rw [pow_zero] at hm; simp [Matrix.one_apply] at hm
  · exact absurd hm (not_lt.mpr (le_of_lt (ppNegM_pow_12_neg k)))

/-! #### C2: the Jordan-block fixture `jordanM` -/

/-- The `hgnn` breaker for the cluster lemma: a single eigenvalue `1`
with a nontrivial Jordan block — the mass-constant orbit
`![2-s, s-1]` escapes the simplex entrywise. -/
def jordanM : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of !![0, 1; -1, 2]

theorem jordanM_00 : jordanM 0 0 = 0 := rfl
theorem jordanM_01 : jordanM 0 1 = 1 := rfl
theorem jordanM_10 : jordanM 1 0 = -1 := rfl
theorem jordanM_11 : jordanM 1 1 = 2 := rfl

/-- Isolation: the kept `hrow` clauses are genuine (row-stochastic). -/
theorem jordanM_row_sum (i : Fin 2) : ∑ j, jordanM i j = 1 := by
  fin_cases i
  · simp [Fin.sum_univ_two, jordanM_00, jordanM_01]
  · simp [Fin.sum_univ_two, jordanM_10, jordanM_11]; norm_num

/-- The escaping orbit: mass `1` constant by construction. -/
def jg : ℕ → (Fin 2 → ℝ) := fun s => ![2 - (s : ℝ), (s : ℝ) - 1]

/-- The escaping orbit's entries. -/
theorem jg_0 (s : ℕ) : jg s 0 = 2 - (s : ℝ) := rfl
theorem jg_1 (s : ℕ) : jg s 1 = (s : ℝ) - 1 := rfl

theorem jg_mass (s : ℕ) : ∑ i, jg s i = 1 := by
  simp only [Fin.sum_univ_two, jg_0, jg_1]
  ring

theorem jg_step_0 (s : ℕ) : (jg s ᵥ* jordanM) 0 = jg (s + 1) 0 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, jordanM_00,
    jordanM_10, jg_0, jg_1]
  push_cast
  ring

theorem jg_step_1 (s : ℕ) : (jg s ᵥ* jordanM) 1 = jg (s + 1) 1 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, jordanM_01,
    jordanM_11, jg_0, jg_1]
  push_cast
  ring

theorem jg_step (s : ℕ) : jg s ᵥ* jordanM = jg (s + 1) := by
  funext j
  fin_cases j
  · exact jg_step_0 s
  · exact jg_step_1 s

/-- Isolation: the dropped clause genuinely fails — the orbit's first
vector has a negative entry. -/
theorem jg_not_nonneg : ¬ ∀ s i, 0 ≤ jg s i := by
  intro h
  have h01 := h 0 1
  rw [jg_1, Nat.cast_zero] at h01
  norm_num at h01

/-- The stationary line: every nonneg stationary vector of `jordanM` is
zero (the fixed space is `ℝ • ![1, -1]`, mass `0`). -/
theorem jordanM_nonneg_fixed_eq_zero (σ : Fin 2 → ℝ) (hσnn : ∀ i, 0 ≤ σ i)
    (hσs : σ ᵥ* jordanM = σ) : σ = 0 := by
  have h0 : σ 1 = -σ 0 := by
    have hh := congrFun hσs 0
    simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, jordanM_00,
      jordanM_10, zero_mul] at hh
    linarith
  funext i
  fin_cases i
  · show σ 0 = 0
    have h1 := hσnn 1
    have h2 := hσnn 0
    linarith
  · show σ 1 = 0
    have h1 := hσnn 1
    have h2 := hσnn 0
    linarith

/-- **Fence (`hgnn` clause of `exists_cluster_stationary_of_orbit`).**
The mass-constant, dynamics-following orbit `jg` has a negative entry,
and the conclusion dies: the stationary line has no nonneg member of
mass `1`. The mechanism: the telescoping defect bound `|g 0 j| ≤ m` is
exactly what nonnegativity supplied; the Jordan orbit escapes it. -/
theorem exists_cluster_hgnn_fence_QA :
    ¬ ∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (m : ℝ) (g : ℕ → (Fin 2 → ℝ)),
      0 ≤ m → (∀ s, ∑ i, g s i = m) → (∀ s, g s ᵥ* M = g (s + 1)) →
      ∃ σ : Fin 2 → ℝ, (∀ i, 0 ≤ σ i) ∧ (∑ i, σ i = m) ∧ σ ᵥ* M = σ := by
  intro h
  obtain ⟨σ, hσnn, hσsum, hσs⟩ :=
    h jordanM 1 jg (by norm_num : (0 : ℝ) ≤ 1)
      (fun s => jg_mass s) (fun s => jg_step s)
  rw [jordanM_nonneg_fixed_eq_zero σ hσnn hσs] at hσsum
  simp at hσsum

/-! #### C3/C4/D2: the doubling fixture `(2 : ℝ) • 1` on `Fin 1` -/

theorem twoOne_nonneg (i j : Fin 1) :
    0 ≤ ((2 : ℝ) • 1 : Matrix (Fin 1) (Fin 1) ℝ) i j := by
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> norm_num

/-- Scalar-on-matrix `vecMul` commutes with the scalar. -/
theorem vecMul_smul_matrix (b : ℝ) (M : Matrix (Fin 1) (Fin 1) ℝ) (v : Fin 1 → ℝ) :
    v ᵥ* (b • M) = b • (v ᵥ* M) := by
  funext j
  simp only [Matrix.vecMul, Matrix.dotProduct, Matrix.smul_apply, smul_eq_mul,
    Pi.smul_apply, Finset.mul_sum, mul_assoc]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The single entry of the `Fin 1` identity. -/
theorem one11_entry : (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = 1 := rfl

theorem twoOne_fixed_eq_zero (σ : Fin 1 → ℝ)
    (hσs : σ ᵥ* ((2 : ℝ) • 1 : Matrix (Fin 1) (Fin 1) ℝ) = σ) : σ = 0 := by
  have hh := congrFun hσs 0
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_one, Matrix.smul_apply,
    smul_eq_mul, one11_entry] at hh
  norm_num at hh
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  show σ 0 = 0
  linarith

/-- The growing orbit (masses `2^(s+1) ≠ 1`). -/
def cg : ℕ → (Fin 1 → ℝ) := fun s _ => (2 : ℝ) ^ (s + 1)

theorem cg_nonneg (s : ℕ) (i : Fin 1) : 0 ≤ cg s i := pow_nonneg (by norm_num) _

theorem cg_step (s : ℕ) :
    cg s ᵥ* ((2 : ℝ) • 1 : Matrix (Fin 1) (Fin 1) ℝ) = cg (s + 1) := by
  rw [vecMul_smul_matrix, Matrix.vecMul_one]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, cg, pow_succ]
  ring

/-- Isolation: the dropped `hgsum` clause genuinely fails at `s = 0`
(`∑ = 2 ≠ 1`). -/
theorem cg_not_mass_one : ¬ ∀ s, ∑ i, cg s i = 1 := by
  intro h
  have h0 := h 0
  simp only [Fin.sum_univ_one, cg, pow_one] at h0
  norm_num at h0

/-- The constant orbit (masses constant `1`, but not following the
dynamics). -/
def dg : ℕ → (Fin 1 → ℝ) := fun _ _ => 1

theorem dg_nonneg (s : ℕ) (i : Fin 1) : 0 ≤ dg s i := by simp [dg]

theorem dg_mass (s : ℕ) : ∑ i, dg s i = 1 := by
  simp only [Fin.sum_univ_one, dg]

/-- Isolation: the dropped `hgstep` clause genuinely fails (`2 ≠ 1`). -/
theorem dg_not_step :
    ¬ ∀ s, dg s ᵥ* ((2 : ℝ) • 1 : Matrix (Fin 1) (Fin 1) ℝ) = dg (s + 1) := by
  intro h
  have h0 := h 0
  rw [vecMul_smul_matrix, Matrix.vecMul_one] at h0
  have h00 := congrFun h0 0
  simp only [Pi.smul_apply, smul_eq_mul, dg, Pi.one_apply] at h00
  norm_num at h00

/-- **Fence (`hgsum` clause of `exists_cluster_stationary_of_orbit`).** -/
theorem exists_cluster_hgsum_fence_QA :
    ¬ ∀ (M : Matrix (Fin 1) (Fin 1) ℝ) (m : ℝ) (g : ℕ → (Fin 1 → ℝ)),
      0 ≤ m → (∀ s i, 0 ≤ g s i) → (∀ s, g s ᵥ* M = g (s + 1)) →
      ∃ σ : Fin 1 → ℝ, (∀ i, 0 ≤ σ i) ∧ (∑ i, σ i = m) ∧ σ ᵥ* M = σ := by
  intro h
  obtain ⟨σ, -, hσsum, hσs⟩ :=
    h ((2 : ℝ) • 1) 1 cg (by norm_num : (0 : ℝ) ≤ 1)
      (fun s i => cg_nonneg s i) (fun s => cg_step s)
  have h0 := twoOne_fixed_eq_zero σ hσs
  rw [h0] at hσsum
  simp at hσsum

/-- **Fence (`hgstep` clause of `exists_cluster_stationary_of_orbit`).** -/
theorem exists_cluster_hgstep_fence_QA :
    ¬ ∀ (M : Matrix (Fin 1) (Fin 1) ℝ) (m : ℝ) (g : ℕ → (Fin 1 → ℝ)),
      0 ≤ m → (∀ s i, 0 ≤ g s i) → (∀ s, ∑ i, g s i = m) →
      ∃ σ : Fin 1 → ℝ, (∀ i, 0 ≤ σ i) ∧ (∑ i, σ i = m) ∧ σ ᵥ* M = σ := by
  intro h
  obtain ⟨σ, -, hσsum, hσs⟩ :=
    h ((2 : ℝ) • 1) 1 dg (by norm_num : (0 : ℝ) ≤ 1)
      (fun s i => dg_nonneg s i) (fun s => dg_mass s)
  have h0 := twoOne_fixed_eq_zero σ hσs
  rw [h0] at hσsum
  simp at hσsum

/-- **Fence (`hrow` clause of `exists_nonneg_stationary_of_row_stochastic`).** -/
theorem exists_nonneg_stationary_hrow_fence_QA :
    ¬ ∀ (M : Matrix (Fin 1) (Fin 1) ℝ), (∀ i j, 0 ≤ M i j) →
      ∃ σ : Fin 1 → ℝ, (∀ i, 0 ≤ σ i) ∧ (∑ i, σ i = Fintype.card (Fin 1)) ∧
        σ ᵥ* M = σ := by
  intro h
  obtain ⟨σ, -, hσsum, hσs⟩ := h ((2 : ℝ) • 1) (fun i j => twoOne_nonneg i j)
  have h0 := twoOne_fixed_eq_zero σ hσs
  rw [h0, Fintype.card_fin] at hσsum
  simp at hσsum

/-! #### D1: the Jordan fixture again, at row-stochasticity -/

/-- **Fence (`hnn` clause of `exists_nonneg_stationary_of_row_stochastic`).**
The Jordan block is row-stochastic (kept clause genuine) with a
negative entry, and its stationary line `ℝ • ![1, -1]` has no nonneg
member of mass `2`. -/
theorem exists_nonneg_stationary_hnn_fence_QA :
    ¬ ∀ (M : Matrix (Fin 2) (Fin 2) ℝ), (∀ i, ∑ j, M i j = 1) →
      ∃ σ : Fin 2 → ℝ, (∀ i, 0 ≤ σ i) ∧ (∑ i, σ i = Fintype.card (Fin 2)) ∧
        σ ᵥ* M = σ := by
  intro h
  obtain ⟨σ, hσnn, hσsum, hσs⟩ := h jordanM (fun i => jordanM_row_sum i)
  have h0 := jordanM_nonneg_fixed_eq_zero σ hσnn hσs
  rw [h0, Fintype.card_fin] at hσsum
  simp at hσsum

/-! #### E3/E4: the `hdeg`/`hex` derivation strengthenings -/

/-- **Strengthening (the `hex`-derivation half of the E4 pair).** A
positive row sum of a nonnegative matrix has a positive summand —
`hnn` plus one positive degree already supplies `hex`; irreducibility
is not needed. -/
theorem exists_pos_entry_of_deg_pos {V : Type} [Fintype V] (A : Matrix V V ℝ)
    (i : V) (hi : 0 < deg A i) :
    ∃ j : V, 0 < A i j := by
  by_contra hcon
  push_neg at hcon
  have hsum : ∑ j, A i j ≤ 0 := Finset.sum_nonpos (fun j _ => hcon j)
  unfold deg at hi
  linarith

/-- **Strengthening (the `hdeg`-derivation half of the E3 pair).**
`hnn + hirr + hex` already force every degree positive: a first arc out
of `i` exists (unless `i` is alone, where `hex` supplies the loop), and
nonnegativity makes its weight a lower bound for the row sum. -/
theorem deg_pos_of_nonneg_irreducible {V : Type} [Fintype V] (A : Matrix V V ℝ)
    (hnn : ∀ i j, 0 ≤ A i j) (hirr : A.IsIrreducible) (hex : ∃ i j, 0 < A i j) :
    ∀ i, 0 < deg A i := by
  intro i
  by_cases hsub : Subsingleton V
  · obtain ⟨k, l, hkl⟩ := hex
    have hki : k = i := Subsingleton.elim k i
    have hli : l = i := Subsingleton.elim l i
    rw [hki, hli] at hkl
    have hdeg : deg A i = A i i := by
      unfold deg
      rw [Finset.sum_eq_single i
        (fun j _ hij => absurd (Subsingleton.elim j i) hij)
        (fun hmem => absurd hmem (not_not.mpr (Finset.mem_univ i)))]
    rw [hdeg]
    exact hkl
  · obtain ⟨j, hjne⟩ : ∃ j : V, j ≠ i := by
      by_contra hcon
      push_neg at hcon
      exact hsub ⟨fun a b => (hcon a).trans (hcon b).symm⟩
    obtain ⟨b, hb⟩ := exists_arc_of_rtg (hirr i j) (Ne.symm hjne)
    have hle : A i b ≤ ∑ k, A i k :=
      Finset.single_le_sum (fun k _ => hnn i k) (Finset.mem_univ b)
    unfold deg
    linarith

/-- **The restated existence theorem at the strictly weaker hypothesis
set** — `hdeg` derived, never hypothesized. Together with
`exists_pos_entry_of_deg_pos` this is the E3/E4 strengthening pair:
`hdeg` and `hex` are each derivable from the other three clauses. -/
theorem exists_walkPerronVector_of_hex {V : Type} [Fintype V] [DecidableEq V]
    (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j) (hirr : A.IsIrreducible)
    (hex : ∃ i j, 0 < A i j) :
    ∃ v : V → ℝ, (∀ i, 0 < v i) ∧ (walkTransitionMatrix A)ᵀ *ᵥ v = v ∧
      ∀ y : V → ℝ, (∀ i, 0 ≤ y i) → y ≠ 0 →
        (walkTransitionMatrix A)ᵀ *ᵥ y = y → ∃ c : ℝ, 0 < c ∧ y = c • v :=
  exists_walkPerronVector A hnn hirr hex
    (deg_pos_of_nonneg_irreducible A hnn hirr hex)

/-! #### E1/E5: the signed star fixture `wpNegAdj` -/

/-- The `hnn` breaker for the walk-level existence family: degrees all
`1` (so the walk is the matrix itself), irreducible through positive
arcs, `hex` genuine — and the stationary space is exactly
`ℝ • ![1, -1, 0]`, with no strictly positive member. -/
noncomputable def wpNegAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![-1/2, 1, 1/2; -3/2, 2, 1/2; 1/4, 1/4, 1/2]

theorem wpNegAdj_00 : wpNegAdj 0 0 = -1/2 := rfl
theorem wpNegAdj_01 : wpNegAdj 0 1 = 1 := rfl
theorem wpNegAdj_02 : wpNegAdj 0 2 = 1/2 := rfl
theorem wpNegAdj_10 : wpNegAdj 1 0 = -3/2 := rfl
theorem wpNegAdj_11 : wpNegAdj 1 1 = 2 := rfl
theorem wpNegAdj_12 : wpNegAdj 1 2 = 1/2 := rfl
theorem wpNegAdj_20 : wpNegAdj 2 0 = 1/4 := rfl
theorem wpNegAdj_21 : wpNegAdj 2 1 = 1/4 := rfl
theorem wpNegAdj_22 : wpNegAdj 2 2 = 1/2 := rfl

theorem wpNegAdj_deg_0 : deg wpNegAdj 0 = 1 := by
  simp only [deg, Fin.sum_univ_three, wpNegAdj_00, wpNegAdj_01, wpNegAdj_02]; norm_num
theorem wpNegAdj_deg_1 : deg wpNegAdj 1 = 1 := by
  simp only [deg, Fin.sum_univ_three, wpNegAdj_10, wpNegAdj_11, wpNegAdj_12]; norm_num
theorem wpNegAdj_deg_2 : deg wpNegAdj 2 = 1 := by
  simp only [deg, Fin.sum_univ_three, wpNegAdj_20, wpNegAdj_21, wpNegAdj_22]; norm_num

theorem wpNegAdj_deg (i : Fin 3) : deg wpNegAdj i = 1 := by
  fin_cases i <;> simp [wpNegAdj_deg_0, wpNegAdj_deg_1, wpNegAdj_deg_2]

theorem wpNegAdj_deg_QA : ∀ i, 0 < deg wpNegAdj i := by
  intro i; rw [wpNegAdj_deg i]; norm_num

/-- The walk is the matrix itself (degrees `1`). -/
theorem wpNegP_eq (i j : Fin 3) :
    walkTransitionMatrix wpNegAdj i j = wpNegAdj i j := by
  rw [walkTransitionMatrix_apply, wpNegAdj_deg i, inv_one, one_mul]

/-- Isolation: irreducibility is genuine. -/
theorem wpNegAdj_irreducible_QA : wpNegAdj.IsIrreducible := by
  have h01 : Relation.ReflTransGen (fun a b => 0 < wpNegAdj a b) 0 1 :=
    .single (by rw [wpNegAdj_01]; norm_num)
  have h02 : Relation.ReflTransGen (fun a b => 0 < wpNegAdj a b) 0 2 :=
    .single (by rw [wpNegAdj_02]; norm_num)
  have h12 : Relation.ReflTransGen (fun a b => 0 < wpNegAdj a b) 1 2 :=
    .single (by rw [wpNegAdj_12]; norm_num)
  have h20 : Relation.ReflTransGen (fun a b => 0 < wpNegAdj a b) 2 0 :=
    .single (by rw [wpNegAdj_20]; norm_num)
  have h21 : Relation.ReflTransGen (fun a b => 0 < wpNegAdj a b) 2 1 :=
    .single (by rw [wpNegAdj_21]; norm_num)
  intro i j
  fin_cases i <;> fin_cases j <;> first
    | exact Relation.ReflTransGen.refl
    | exact h01
    | exact h02
    | exact h12
    | exact h20
    | exact h21
    | exact h12.trans h20

theorem wpNegAdj_ex_QA : ∃ i j, 0 < wpNegAdj i j := ⟨0, 1, by rw [wpNegAdj_01]; norm_num⟩

/-- Isolation: the dropped clause genuinely fails. -/
theorem wpNegAdj_not_nonneg : ¬ ∀ i j, 0 ≤ wpNegAdj i j := by
  intro h
  have h10 := h 1 0
  rw [wpNegAdj_10] at h10
  exact absurd h10 (by norm_num)

/-- The fixed-space consequence: every stationary vector of the walk
satisfies `σ 1 = -σ 0` (the stationary space is `ℝ • ![1, -1, 0]`). -/
theorem wpNegAdj_fixed_neg (σ : Fin 3 → ℝ)
    (hσs : σ ᵥ* walkTransitionMatrix wpNegAdj = σ) : σ 1 = -σ 0 := by
  have hP : walkTransitionMatrix wpNegAdj = wpNegAdj :=
    Matrix.ext fun i j => wpNegP_eq i j
  rw [hP] at hσs
  have h1 := congrFun hσs 1
  have h2 := congrFun hσs 2
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three,
    wpNegAdj_01, wpNegAdj_11, wpNegAdj_21, wpNegAdj_02, wpNegAdj_12, wpNegAdj_22] at h1 h2
  -- h1 : σ 0 + 2 σ 1 + σ 2 / 4 = σ 1;  h2 : (σ 0 + σ 1 + σ 2) / 2 = σ 2
  have e2 : σ 0 + σ 1 = σ 2 := by linarith
  linarith

/-- **Fence (`hnn` clause of `exists_walkPerronVector`).** The walk has
no strictly positive fixed vector at all: the stationary line is
`ℝ • ![1, -1, 0]`. -/
theorem exists_walkPerronVector_hnn_fence_QA :
    ¬ ∀ (A : Matrix (Fin 3) (Fin 3) ℝ), A.IsIrreducible → (∃ i j, 0 < A i j) →
      (∀ i, 0 < deg A i) →
      ∃ v : Fin 3 → ℝ, (∀ i, 0 < v i) ∧
        (walkTransitionMatrix A)ᵀ *ᵥ v = v ∧
        ∀ y : Fin 3 → ℝ, (∀ i, 0 ≤ y i) → y ≠ 0 →
          (walkTransitionMatrix A)ᵀ *ᵥ y = y → ∃ c : ℝ, 0 < c ∧ y = c • v := by
  intro h
  obtain ⟨v, hvpos, hvT, -⟩ :=
    h wpNegAdj wpNegAdj_irreducible_QA wpNegAdj_ex_QA wpNegAdj_deg_QA
  have hvs : v ᵥ* walkTransitionMatrix wpNegAdj = v :=
    (Matrix.mulVec_transpose _ _).symm.trans hvT
  have h1 := wpNegAdj_fixed_neg v hvs
  have hp0 := hvpos 0
  have hp1 := hvpos 1
  linarith

/-- **Fence (`hnn` clause of `exists_stationaryVec_of_irreducible`).** -/
theorem exists_stationaryVec_hnn_fence_QA :
    ¬ ∀ (A : Matrix (Fin 3) (Fin 3) ℝ), A.IsIrreducible → (∃ i j, 0 < A i j) →
      (∀ i, 0 < deg A i) →
      ∃ π : Fin 3 → ℝ, (∀ i, 0 < π i) ∧ (∑ i, π i = 1) ∧
        π ᵥ* walkTransitionMatrix A = π := by
  intro h
  obtain ⟨π, hπpos, -, hπs⟩ :=
    h wpNegAdj wpNegAdj_irreducible_QA wpNegAdj_ex_QA wpNegAdj_deg_QA
  have h1 := wpNegAdj_fixed_neg π hπs
  have hp0 := hπpos 0
  have hp1 := hπpos 1
  linarith

/-! #### E2: the reducible two-block fixture `A4` (delivered) -/

/-- **Fence (`hirr` clause of `exists_walkPerronVector`)** — the
delivered hypothesis-free refutation reconciled into the fence
discipline: at the two-block fixture, nonnegativity, the positive entry
and the degrees are all genuine, and the uniqueness clause dies on the
two block-supported stationary distributions. -/
theorem exists_walkPerronVector_hirr_fence_QA :
    ¬ ∀ (A : Matrix (Fin 4) (Fin 4) ℝ), (∀ i j, 0 ≤ A i j) → (∃ i j, 0 < A i j) →
      (∀ i, 0 < deg A i) →
      ∃ v : Fin 4 → ℝ, (∀ i, 0 < v i) ∧
        (walkTransitionMatrix A)ᵀ *ᵥ v = v ∧
        ∀ y : Fin 4 → ℝ, (∀ i, 0 ≤ y i) → y ≠ 0 →
          (walkTransitionMatrix A)ᵀ *ᵥ y = y → ∃ c : ℝ, 0 < c ∧ y = c • v := by
  intro h
  obtain ⟨v, hvpos, hvT, huniq⟩ :=
    h A4 A4_nonneg_QA ⟨0, 1, by rw [A4_01]; norm_num⟩ A4_deg_QA
  have hTa : (walkTransitionMatrix A4)ᵀ *ᵥ pi4a = pi4a := by
    rw [Matrix.mulVec_transpose]; exact pi4a_pred_QA.2.2
  have hTb : (walkTransitionMatrix A4)ᵀ *ᵥ pi4b = pi4b := by
    rw [Matrix.mulVec_transpose]; exact pi4b_pred_QA.2.2
  obtain ⟨c₁, hc₁, h1⟩ := huniq pi4a pi4a_pred_QA.1 pi4a_ne_zero_QA hTa
  obtain ⟨c₂, hc₂, h2⟩ := huniq pi4b pi4b_pred_QA.1 pi4b_ne_zero_QA hTb
  have hcontra : pi4b = (c₂ / c₁) • pi4a := by
    rw [h2, h1, smul_smul, div_mul_cancel₀ _ (ne_of_gt hc₁)]
  have h00 := congrFun hcontra 0
  simp only [pi4b_0, Pi.smul_apply, smul_eq_mul, pi4a_0] at h00
  have hrw : (c₂ / c₁) * (1 / 2 : ℝ) = 0 := h00.symm
  have hzero : c₂ / c₁ = 0 := by
    rcases mul_eq_zero.mp hrw with h' | h'
    · exact h'
    · exact absurd h' (by norm_num)
  have hcc : c₂ = (c₂ / c₁) * c₁ := (div_mul_cancel₀ c₂ (ne_of_gt hc₁)).symm
  rw [hzero, zero_mul] at hcc
  exact absurd hcc (by linarith)

/-! #### E6/E14: the transient fixture `transientAdj` -/

/-- The `hirr` breaker for the walk-level statements: nonnegative,
degrees `(1, 2)`, positive entry genuine — vertex `0` is transient, so
every stationary vector vanishes at `0`. -/
def transientAdj : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of !![0, 1; 0, 2]

theorem transientAdj_00 : transientAdj 0 0 = 0 := rfl
theorem transientAdj_01 : transientAdj 0 1 = 1 := rfl
theorem transientAdj_10 : transientAdj 1 0 = 0 := rfl
theorem transientAdj_11 : transientAdj 1 1 = 2 := rfl

theorem transientAdj_nonneg (i j : Fin 2) : 0 ≤ transientAdj i j := by
  fin_cases i <;> fin_cases j <;>
    simp [transientAdj_00, transientAdj_01, transientAdj_10, transientAdj_11]

theorem transientAdj_deg_0 : deg transientAdj 0 = 1 := by
  simp only [deg, Fin.sum_univ_two, transientAdj_00, transientAdj_01]; norm_num
theorem transientAdj_deg_1 : deg transientAdj 1 = 2 := by
  simp only [deg, Fin.sum_univ_two, transientAdj_10, transientAdj_11]; norm_num

theorem transientAdj_deg_QA : ∀ i, 0 < deg transientAdj i := by
  intro i
  fin_cases i <;> simp [transientAdj_deg_0, transientAdj_deg_1]

theorem transientAdj_ex_QA : ∃ i j, 0 < transientAdj i j :=
  ⟨0, 1, by rw [transientAdj_01]; norm_num⟩

/-- The only positive entry of row `1` is the self-loop (column `1`). -/
theorem transientAdj_row1_pos_iff (c : Fin 2) :
    0 < transientAdj 1 c ↔ c = 1 := by
  fin_cases c <;> simp [transientAdj_10, transientAdj_11]

/-- Everything reachable from vertex `1` stays at vertex `1` (the only
positive entry of row `1` is the self-loop). -/
theorem transientAdj_not_rtg_10 :
    ¬ Relation.ReflTransGen (fun a b => 0 < transientAdj a b) 1 0 := by
  intro h
  have hkey : ∀ j : Fin 2, Relation.ReflTransGen (fun a b => 0 < transientAdj a b) 1 j →
      j = 1 := by
    intro j hj
    induction hj with
    | refl => rfl
    | @tail b c _ hstep ih =>
        have hb1 : b = 1 := ih
        rw [hb1] at hstep
        exact (transientAdj_row1_pos_iff c).mp hstep
  exact absurd (hkey 0 h) (by decide)

/-- Isolation: the dropped clause genuinely fails (no arc returns from
vertex `1` to vertex `0`). -/
theorem transientAdj_not_irreducible : ¬ transientAdj.IsIrreducible :=
  fun h => transientAdj_not_rtg_10 (h 1 0)

/-- **Fence (`hirr` clause of `exists_stationaryVec_of_irreducible`).**
Every stationary vector of the transient walk has `π 0 = 0` — the walk
column `0` is zero — against strict positivity. -/
theorem exists_stationaryVec_hirr_fence_QA :
    ¬ ∀ (A : Matrix (Fin 2) (Fin 2) ℝ), (∀ i j, 0 ≤ A i j) → (∃ i j, 0 < A i j) →
      (∀ i, 0 < deg A i) →
      ∃ π : Fin 2 → ℝ, (∀ i, 0 < π i) ∧ (∑ i, π i = 1) ∧
        π ᵥ* walkTransitionMatrix A = π := by
  intro h
  obtain ⟨π, hπpos, -, hπs⟩ :=
    h transientAdj transientAdj_nonneg transientAdj_ex_QA transientAdj_deg_QA
  have h0 := congrFun hπs 0
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two,
    transientAdj_deg_0, transientAdj_deg_1] at h0
  rw [walkTransitionMatrix_apply, transientAdj_deg_0, inv_one, one_mul,
    transientAdj_00, walkTransitionMatrix_apply, transientAdj_deg_1,
    transientAdj_10] at h0
  -- h0 : π 0 * 0 + π 1 * 0 = π 0
  simp only [mul_zero, add_zero] at h0
  have hp0 := hπpos 0
  linarith

/-- The witness for the positivity fence: stationary, nonnegative,
nonzero — and vanishing at the transient vertex. -/
def trSig : Fin 2 → ℝ := ![0, 1]

theorem trSig_0 : trSig 0 = 0 := rfl
theorem trSig_1 : trSig 1 = 1 := rfl

theorem trSig_nonneg (i : Fin 2) : 0 ≤ trSig i := by
  fin_cases i <;> simp [trSig_0, trSig_1]

theorem trSig_ne_zero : trSig ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  rw [trSig_1] at h1
  simp at h1

theorem trSig_stationary : trSig ᵥ* walkTransitionMatrix transientAdj = trSig := by
  have h01 : (trSig ᵥ* walkTransitionMatrix transientAdj) 0 = trSig 0 := by
    simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two,
      walkTransitionMatrix_apply, transientAdj_deg_0, transientAdj_deg_1,
      transientAdj_00, transientAdj_10, trSig_0, trSig_1]
    norm_num
  have h11 : (trSig ᵥ* walkTransitionMatrix transientAdj) 1 = trSig 1 := by
    simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two,
      walkTransitionMatrix_apply, transientAdj_deg_0, transientAdj_deg_1,
      transientAdj_01, transientAdj_11, trSig_0, trSig_1]
    norm_num
  funext j
  fin_cases j
  · exact h01
  · exact h11

/-- **Fence (`hirr` clause of `stationaryVec_pos_of_irreducible`).** The
witness `![0, 1]` is stationary, nonnegative, nonzero — and vanishes
at the transient vertex. -/
theorem stationaryVec_pos_hirr_fence_QA :
    ¬ ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (σ : Fin 2 → ℝ), (∀ i j, 0 ≤ A i j) →
      (∃ i j, 0 < A i j) → (∀ i, 0 < deg A i) → (∀ i, 0 ≤ σ i) → σ ≠ 0 →
      σ ᵥ* walkTransitionMatrix A = σ → ∀ i, 0 < σ i := by
  intro h
  have h1 := h transientAdj trSig transientAdj_nonneg transientAdj_ex_QA
    transientAdj_deg_QA trSig_nonneg trSig_ne_zero trSig_stationary 0
  rw [trSig_0] at h1
  exact absurd h1 (by norm_num)

/-! #### E10/E13: the two-plane fixture `smNegAdj` -/

/-- The `hnn` breaker for scale-uniqueness and distribution-uniqueness:
`1 + u ⊗ v` with `u = (1, -1, 1)`, `v = (1, 1, -1)` — irreducible,
degrees `1`, and the fixed space is the two-plane `σ ⬝ᵥ u = 0`, which
meets the nonnegative cone in the wedge `σ 0 + σ 2 = σ 1`. -/
def smNegAdj : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of !![2, 1, -2; -1, 0, 2; 1, 1, -1]

theorem smNegAdj_00 : smNegAdj 0 0 = 2 := rfl
theorem smNegAdj_01 : smNegAdj 0 1 = 1 := rfl
theorem smNegAdj_02 : smNegAdj 0 2 = -2 := rfl
theorem smNegAdj_10 : smNegAdj 1 0 = -1 := rfl
theorem smNegAdj_11 : smNegAdj 1 1 = 0 := rfl
theorem smNegAdj_12 : smNegAdj 1 2 = 2 := rfl
theorem smNegAdj_20 : smNegAdj 2 0 = 1 := rfl
theorem smNegAdj_21 : smNegAdj 2 1 = 1 := rfl
theorem smNegAdj_22 : smNegAdj 2 2 = -1 := rfl

theorem smNegAdj_deg_0 : deg smNegAdj 0 = 1 := by
  simp only [deg, Fin.sum_univ_three, smNegAdj_00, smNegAdj_01, smNegAdj_02]; norm_num
theorem smNegAdj_deg_1 : deg smNegAdj 1 = 1 := by
  simp only [deg, Fin.sum_univ_three, smNegAdj_10, smNegAdj_11, smNegAdj_12]; norm_num
theorem smNegAdj_deg_2 : deg smNegAdj 2 = 1 := by
  simp only [deg, Fin.sum_univ_three, smNegAdj_20, smNegAdj_21, smNegAdj_22]; norm_num

theorem smNegAdj_deg (i : Fin 3) : deg smNegAdj i = 1 := by
  fin_cases i <;> simp [smNegAdj_deg_0, smNegAdj_deg_1, smNegAdj_deg_2]

theorem smNegAdj_deg_QA : ∀ i, 0 < deg smNegAdj i := by
  intro i; rw [smNegAdj_deg i]; norm_num

/-- The walk is the matrix itself (degrees `1`). -/
theorem smNegP_eq (i j : Fin 3) :
    walkTransitionMatrix smNegAdj i j = smNegAdj i j := by
  rw [walkTransitionMatrix_apply, smNegAdj_deg i, inv_one, one_mul]

/-- Isolation: irreducibility is genuine — arcs `0→0, 0→1, 1→2, 2→0,
2→1` make the support digraph strongly connected. -/
theorem smNegAdj_irreducible_QA : smNegAdj.IsIrreducible := by
  have h00 : Relation.ReflTransGen (fun a b => 0 < smNegAdj a b) 0 0 :=
    .single (by rw [smNegAdj_00]; norm_num)
  have h01 : Relation.ReflTransGen (fun a b => 0 < smNegAdj a b) 0 1 :=
    .single (by rw [smNegAdj_01]; norm_num)
  have h12 : Relation.ReflTransGen (fun a b => 0 < smNegAdj a b) 1 2 :=
    .single (by rw [smNegAdj_12]; norm_num)
  have h20 : Relation.ReflTransGen (fun a b => 0 < smNegAdj a b) 2 0 :=
    .single (by rw [smNegAdj_20]; norm_num)
  have h21 : Relation.ReflTransGen (fun a b => 0 < smNegAdj a b) 2 1 :=
    .single (by rw [smNegAdj_21]; norm_num)
  intro i j
  fin_cases i <;> fin_cases j <;> first
    | exact h00
    | exact h01
    | exact h12
    | exact h20
    | exact h21
    | exact Relation.ReflTransGen.refl
    | exact h01.trans h12
    | exact h12.trans h20

theorem smNegAdj_ex_QA : ∃ i j, 0 < smNegAdj i j := ⟨0, 0, by rw [smNegAdj_00]; norm_num⟩

/-- Isolation: the dropped clause genuinely fails. -/
theorem smNegAdj_not_nonneg : ¬ ∀ i j, 0 ≤ smNegAdj i j := by
  intro h
  have h02 := h 0 2
  rw [smNegAdj_02] at h02
  exact absurd h02 (by norm_num)

/-- First wedge witness: nonneg, nonzero, stationary. -/
def smSig : Fin 3 → ℝ := ![1, 1, 0]

theorem smSig_0 : smSig 0 = 1 := rfl
theorem smSig_1 : smSig 1 = 1 := rfl
theorem smSig_2 : smSig 2 = 0 := rfl

/-- Second wedge witness: a different ray of the same wedge. -/
def smTau : Fin 3 → ℝ := ![0, 1, 1]

theorem smTau_0 : smTau 0 = 0 := rfl
theorem smTau_1 : smTau 1 = 1 := rfl
theorem smTau_2 : smTau 2 = 1 := rfl

theorem smSig_nonneg (i : Fin 3) : 0 ≤ smSig i := by
  fin_cases i <;> simp [smSig_0, smSig_1, smSig_2]

theorem smSig_ne_zero : smSig ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [smSig_0] at h0
  simp at h0

theorem smTau_nonneg (i : Fin 3) : 0 ≤ smTau i := by
  fin_cases i <;> simp [smTau_0, smTau_1, smTau_2]

theorem smTau_ne_zero : smTau ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  rw [smTau_1] at h1
  simp at h1

theorem smSig_stationary : smSig ᵥ* walkTransitionMatrix smNegAdj = smSig := by
  have h0 : (smSig ᵥ* walkTransitionMatrix smNegAdj) 0 = smSig 0 := by
    simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three, smNegP_eq,
      smNegAdj_00, smNegAdj_10, smNegAdj_20, smSig_0, smSig_1, smSig_2]
    norm_num
  have h1 : (smSig ᵥ* walkTransitionMatrix smNegAdj) 1 = smSig 1 := by
    simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three, smNegP_eq,
      smNegAdj_01, smNegAdj_11, smNegAdj_21, smSig_0, smSig_1, smSig_2]
    norm_num
  have h2 : (smSig ᵥ* walkTransitionMatrix smNegAdj) 2 = smSig 2 := by
    simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three, smNegP_eq,
      smNegAdj_02, smNegAdj_12, smNegAdj_22, smSig_0, smSig_1, smSig_2]
    norm_num
  funext j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

theorem smTau_stationary : smTau ᵥ* walkTransitionMatrix smNegAdj = smTau := by
  have h0 : (smTau ᵥ* walkTransitionMatrix smNegAdj) 0 = smTau 0 := by
    simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three, smNegP_eq,
      smNegAdj_00, smNegAdj_10, smNegAdj_20, smTau_0, smTau_1, smTau_2]
    norm_num
  have h1 : (smTau ᵥ* walkTransitionMatrix smNegAdj) 1 = smTau 1 := by
    simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three, smNegP_eq,
      smNegAdj_01, smNegAdj_11, smNegAdj_21, smTau_0, smTau_1, smTau_2]
    norm_num
  have h2 : (smTau ᵥ* walkTransitionMatrix smNegAdj) 2 = smTau 2 := by
    simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three, smNegP_eq,
      smNegAdj_02, smNegAdj_12, smNegAdj_22, smTau_0, smTau_1, smTau_2]
    norm_num
  funext j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

/-- **Fence (`hnn` clause of `stationaryVec_smul_of_irreducible`).** On
the one-dimensional signed fixtures the nonneg stationary cone is a
single ray and the conclusion survives; here the fixed space is a
two-plane meeting the cone in a wedge, and the two wedge rays are not
positive multiples. -/
theorem stationaryVec_smul_hnn_fence_QA :
    ¬ ∀ (A : Matrix (Fin 3) (Fin 3) ℝ) (σ τ : Fin 3 → ℝ), A.IsIrreducible →
      (∃ i j, 0 < A i j) → (∀ i, 0 < deg A i) → (∀ i, 0 ≤ σ i) → σ ≠ 0 →
      σ ᵥ* walkTransitionMatrix A = σ → (∀ i, 0 ≤ τ i) → τ ≠ 0 →
      τ ᵥ* walkTransitionMatrix A = τ → ∃ c : ℝ, 0 < c ∧ τ = c • σ := by
  intro h
  obtain ⟨c, hc, heq⟩ :=
    h smNegAdj smSig smTau smNegAdj_irreducible_QA smNegAdj_ex_QA smNegAdj_deg_QA
      smSig_nonneg smSig_ne_zero smSig_stationary smTau_nonneg smTau_ne_zero
      smTau_stationary
  have h00 := congrFun heq 0
  simp only [smTau_0, Pi.smul_apply, smul_eq_mul, smSig_0, one_mul] at h00
  exact absurd hc (by linarith)

/-- The two mass-one wedge distributions. -/
noncomputable def smPiA : Fin 3 → ℝ := ![1/2, 1/2, 0]
noncomputable def smPiB : Fin 3 → ℝ := ![0, 1/2, 1/2]

theorem smPiA_0 : smPiA 0 = 1/2 := rfl
theorem smPiA_1 : smPiA 1 = 1/2 := rfl
theorem smPiA_2 : smPiA 2 = 0 := rfl
theorem smPiB_0 : smPiB 0 = 0 := rfl
theorem smPiB_1 : smPiB 1 = 1/2 := rfl
theorem smPiB_2 : smPiB 2 = 1/2 := rfl

theorem smPiA_pred : (∀ i, 0 ≤ smPiA i) ∧ (∑ i, smPiA i = 1) ∧
    smPiA ᵥ* walkTransitionMatrix smNegAdj = smPiA := by
  refine ⟨fun i => by fin_cases i <;> simp [smPiA_0, smPiA_1, smPiA_2], ?_, ?_⟩
  · simp only [Fin.sum_univ_three, smPiA_0, smPiA_1, smPiA_2]
    norm_num
  · have hsmul : smPiA = (1/2 : ℝ) • smSig := by
      funext i
      fin_cases i <;> simp [smPiA_0, smPiA_1, smPiA_2, smSig_0, smSig_1, smSig_2]
    rw [hsmul, Matrix.vecMul_smul, smSig_stationary]

theorem smPiB_pred : (∀ i, 0 ≤ smPiB i) ∧ (∑ i, smPiB i = 1) ∧
    smPiB ᵥ* walkTransitionMatrix smNegAdj = smPiB := by
  refine ⟨fun i => by fin_cases i <;> simp [smPiB_0, smPiB_1, smPiB_2], ?_, ?_⟩
  · simp only [Fin.sum_univ_three, smPiB_0, smPiB_1, smPiB_2]
    norm_num
  · have hsmul : smPiB = (1/2 : ℝ) • smTau := by
      funext i
      fin_cases i <;> simp [smPiB_0, smPiB_1, smPiB_2, smTau_0, smTau_1, smTau_2]
    rw [hsmul, Matrix.vecMul_smul, smTau_stationary]

theorem smPiA_ne_smPiB : smPiA ≠ smPiB := by
  intro h
  have h0 := congrFun h 0
  rw [smPiA_0, smPiB_0] at h0
  norm_num at h0

/-- **Fence (`hnn` clause of `existsUnique_stationaryVec_of_irreducible`).**
The wedge's mass-one slice is a whole segment — the stationary
distribution is far from unique. -/
theorem existsUnique_stationaryVec_hnn_fence_QA :
    ¬ ∀ (A : Matrix (Fin 3) (Fin 3) ℝ), A.IsIrreducible → (∃ i j, 0 < A i j) →
      (∀ i, 0 < deg A i) →
      ∃! π : Fin 3 → ℝ, (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧
        π ᵥ* walkTransitionMatrix A = π := by
  intro h
  obtain ⟨τ, -, huniq⟩ :=
    h smNegAdj smNegAdj_irreducible_QA smNegAdj_ex_QA smNegAdj_deg_QA
  exact smPiA_ne_smPiB ((huniq smPiA smPiA_pred).trans (huniq smPiB smPiB_pred).symm)

/-! #### E15: the vanishing-support fixture `spNegAdj` -/

/-- The `hnn` breaker for full support: nonneg stationary mass can
vanish on strong support precisely because signed entries cancel — the
witness `![1, 1, 0]` is stationary through `1·1 + 1·(-1) = 0` in
coordinate `2`. -/
noncomputable def spNegAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![-1, 1, 1; 2, 0, -1; 1/2, 1/4, 1/4]

theorem spNegAdj_00 : spNegAdj 0 0 = -1 := rfl
theorem spNegAdj_01 : spNegAdj 0 1 = 1 := rfl
theorem spNegAdj_02 : spNegAdj 0 2 = 1 := rfl
theorem spNegAdj_10 : spNegAdj 1 0 = 2 := rfl
theorem spNegAdj_11 : spNegAdj 1 1 = 0 := rfl
theorem spNegAdj_12 : spNegAdj 1 2 = -1 := rfl
theorem spNegAdj_20 : spNegAdj 2 0 = 1/2 := rfl
theorem spNegAdj_21 : spNegAdj 2 1 = 1/4 := rfl
theorem spNegAdj_22 : spNegAdj 2 2 = 1/4 := rfl

theorem spNegAdj_deg_0 : deg spNegAdj 0 = 1 := by
  simp only [deg, Fin.sum_univ_three, spNegAdj_00, spNegAdj_01, spNegAdj_02]; norm_num
theorem spNegAdj_deg_1 : deg spNegAdj 1 = 1 := by
  simp only [deg, Fin.sum_univ_three, spNegAdj_10, spNegAdj_11, spNegAdj_12]; norm_num
theorem spNegAdj_deg_2 : deg spNegAdj 2 = 1 := by
  simp only [deg, Fin.sum_univ_three, spNegAdj_20, spNegAdj_21, spNegAdj_22]; norm_num

theorem spNegAdj_deg (i : Fin 3) : deg spNegAdj i = 1 := by
  fin_cases i <;> simp [spNegAdj_deg_0, spNegAdj_deg_1, spNegAdj_deg_2]

theorem spNegAdj_deg_QA : ∀ i, 0 < deg spNegAdj i := by
  intro i; rw [spNegAdj_deg i]; norm_num

/-- The walk is the matrix itself (degrees `1`). -/
theorem spNegP_eq (i j : Fin 3) :
    walkTransitionMatrix spNegAdj i j = spNegAdj i j := by
  rw [walkTransitionMatrix_apply, spNegAdj_deg i, inv_one, one_mul]

/-- Isolation: irreducibility is genuine. -/
theorem spNegAdj_irreducible_QA : spNegAdj.IsIrreducible := by
  have h01 : Relation.ReflTransGen (fun a b => 0 < spNegAdj a b) 0 1 :=
    .single (by rw [spNegAdj_01]; norm_num)
  have h02 : Relation.ReflTransGen (fun a b => 0 < spNegAdj a b) 0 2 :=
    .single (by rw [spNegAdj_02]; norm_num)
  have h10 : Relation.ReflTransGen (fun a b => 0 < spNegAdj a b) 1 0 :=
    .single (by rw [spNegAdj_10]; norm_num)
  have h20 : Relation.ReflTransGen (fun a b => 0 < spNegAdj a b) 2 0 :=
    .single (by rw [spNegAdj_20]; norm_num)
  have h21 : Relation.ReflTransGen (fun a b => 0 < spNegAdj a b) 2 1 :=
    .single (by rw [spNegAdj_21]; norm_num)
  intro i j
  fin_cases i <;> fin_cases j <;> first
    | exact Relation.ReflTransGen.refl
    | exact h01
    | exact h02
    | exact h10
    | exact h20
    | exact h21
    | exact h01.trans h10
    | exact h10.trans h01
    | exact h10.trans h02

theorem spNegAdj_ex_QA : ∃ i j, 0 < spNegAdj i j := ⟨0, 1, by rw [spNegAdj_01]; norm_num⟩

/-- Isolation: the dropped clause genuinely fails. -/
theorem spNegAdj_not_nonneg : ¬ ∀ i j, 0 ≤ spNegAdj i j := by
  intro h
  have h00 := h 0 0
  rw [spNegAdj_00] at h00
  exact absurd h00 (by norm_num)

/-- The vanishing witness. -/
def spSig : Fin 3 → ℝ := ![1, 1, 0]

theorem spSig_0 : spSig 0 = 1 := rfl
theorem spSig_1 : spSig 1 = 1 := rfl
theorem spSig_2 : spSig 2 = 0 := rfl

theorem spSig_nonneg (i : Fin 3) : 0 ≤ spSig i := by
  fin_cases i <;> simp [spSig_0, spSig_1, spSig_2]

theorem spSig_ne_zero : spSig ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [spSig_0] at h0
  simp at h0

theorem spSig_stationary : spSig ᵥ* walkTransitionMatrix spNegAdj = spSig := by
  have h0 : (spSig ᵥ* walkTransitionMatrix spNegAdj) 0 = spSig 0 := by
    simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three, spNegP_eq,
      spNegAdj_00, spNegAdj_10, spNegAdj_20, spSig_0, spSig_1, spSig_2]
    norm_num
  have h1 : (spSig ᵥ* walkTransitionMatrix spNegAdj) 1 = spSig 1 := by
    simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three, spNegP_eq,
      spNegAdj_01, spNegAdj_11, spNegAdj_21, spSig_0, spSig_1, spSig_2]
    norm_num
  have h2 : (spSig ᵥ* walkTransitionMatrix spNegAdj) 2 = spSig 2 := by
    simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three, spNegP_eq,
      spNegAdj_02, spNegAdj_12, spNegAdj_22, spSig_0, spSig_1, spSig_2]
    norm_num
  funext j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

/-- **Fence (`hnn` clause of `stationaryVec_pos_of_irreducible`).** The
witness is stationary, nonnegative, nonzero — and vanishes at vertex
`2`, which strong connectivity genuinely reaches. -/
theorem stationaryVec_pos_hnn_fence_QA :
    ¬ ∀ (A : Matrix (Fin 3) (Fin 3) ℝ) (σ : Fin 3 → ℝ), A.IsIrreducible →
      (∃ i j, 0 < A i j) → (∀ i, 0 < deg A i) → (∀ i, 0 ≤ σ i) → σ ≠ 0 →
      σ ᵥ* walkTransitionMatrix A = σ → ∀ i, 0 < σ i := by
  intro h
  have h1 := h spNegAdj spSig spNegAdj_irreducible_QA spNegAdj_ex_QA
    spNegAdj_deg_QA spSig_nonneg spSig_ne_zero spSig_stationary 2
  rw [spSig_2] at h1
  exact absurd h1 (by norm_num)

/-! #### E7–E9/E16: the σ/τ clause fences at the delivered edge `A2` -/

/-- The edge's entries (the delivered `A2` fixture, pinned here for the
fence computations). -/
theorem A2_00 : A2 0 0 = 0 := rfl
theorem A2_01 : A2 0 1 = 1 := rfl
theorem A2_10 : A2 1 0 = 1 := rfl
theorem A2_11 : A2 1 1 = 0 := rfl

theorem A2_deg_one (i : Fin 2) : deg A2 i = 1 := by
  fin_cases i <;> simp [deg, Fin.sum_univ_two, A2_00, A2_01, A2_10, A2_11]

/-- The walk is the edge itself (degrees `1`). -/
theorem A2P_eq (i j : Fin 2) : walkTransitionMatrix A2 i j = A2 i j := by
  rw [walkTransitionMatrix_apply, A2_deg_one, inv_one, one_mul]

/-- The swap: acting by the edge exchanges the two coordinates. -/
theorem A2_vecMul_swap (v : Fin 2 → ℝ) :
    v ᵥ* walkTransitionMatrix A2 = ![v 1, v 0] := by
  have h0 : (v ᵥ* walkTransitionMatrix A2) 0 = v 1 := by
    simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, A2P_eq,
      A2_00, A2_10]
    ring
  have h1 : (v ᵥ* walkTransitionMatrix A2) 1 = v 0 := by
    simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, A2P_eq,
      A2_01, A2_11]
    ring
  funext j
  fin_cases j
  · exact h0
  · exact h1

/-- The signed stationary witness (nonneg fails). -/
def a2Signed : Fin 2 → ℝ := ![-1, -1]

theorem a2Signed_0 : a2Signed 0 = -1 := rfl
theorem a2Signed_1 : a2Signed 1 = -1 := rfl

theorem a2Signed_ne_zero : a2Signed ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [a2Signed_0] at h0
  simp at h0

theorem a2Signed_stationary : a2Signed ᵥ* walkTransitionMatrix A2 = a2Signed := by
  rw [A2_vecMul_swap]
  funext j
  fin_cases j <;> simp [a2Signed_0, a2Signed_1]

/-- The uniform stationary witness. -/
def a2one : Fin 2 → ℝ := ![1, 1]

theorem a2one_0 : a2one 0 = 1 := rfl
theorem a2one_1 : a2one 1 = 1 := rfl

theorem a2one_nonneg (i : Fin 2) : 0 ≤ a2one i := by
  fin_cases i <;> simp [a2one_0, a2one_1]

theorem a2one_ne_zero : a2one ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [a2one_0] at h0
  simp at h0

theorem a2one_stationary : a2one ᵥ* walkTransitionMatrix A2 = a2one := by
  rw [A2_vecMul_swap]
  funext j
  fin_cases j <;> simp [a2one_0, a2one_1]

/-- The non-stationary witness (stationarity of `σ` fails). -/
def a2e0 : Fin 2 → ℝ := ![1, 0]

theorem a2e0_0 : a2e0 0 = 1 := rfl
theorem a2e0_1 : a2e0 1 = 0 := rfl

theorem a2e0_nonneg (i : Fin 2) : 0 ≤ a2e0 i := by
  fin_cases i <;> simp [a2e0_0, a2e0_1]

theorem a2e0_ne_zero : a2e0 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [a2e0_0] at h0
  simp at h0

/-- Isolation: the dropped clause genuinely fails (the swap moves
`![1, 0]` to `![0, 1]`). -/
theorem a2e0_not_stationary : a2e0 ᵥ* walkTransitionMatrix A2 ≠ a2e0 := by
  rw [A2_vecMul_swap]
  intro heq
  have h1 := congrFun heq 1
  simp only [Matrix.cons_val_one, Matrix.head_cons, a2e0_1, a2e0_0] at h1
  norm_num at h1

theorem a2zero_stationary :
    (0 : Fin 2 → ℝ) ᵥ* walkTransitionMatrix A2 = 0 := by
  rw [A2_vecMul_swap]
  funext j
  fin_cases j <;> simp

/-- **Fence (`hσ` clause of `stationaryVec_smul_of_irreducible`).** The
signed stationary vector is not nonnegative, and the positive-multiple
conclusion dies at the sign. -/
theorem stationaryVec_smul_hσ_fence_QA :
    ¬ ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (σ τ : Fin 2 → ℝ), (∀ i j, 0 ≤ A i j) →
      A.IsIrreducible → (∃ i j, 0 < A i j) → (∀ i, 0 < deg A i) → σ ≠ 0 →
      σ ᵥ* walkTransitionMatrix A = σ → (∀ i, 0 ≤ τ i) → τ ≠ 0 →
      τ ᵥ* walkTransitionMatrix A = τ → ∃ c : ℝ, 0 < c ∧ τ = c • σ := by
  intro h
  obtain ⟨c, hc, heq⟩ :=
    h A2 a2Signed a2one A2_nonneg_QA A2_irreducible_QA A2_ex_QA A2_deg_QA
      a2Signed_ne_zero a2Signed_stationary a2one_nonneg a2one_ne_zero
      a2one_stationary
  have h0 := congrFun heq 0
  simp only [a2one_0, Pi.smul_apply, smul_eq_mul, a2Signed_0] at h0
  have : c = -1 := by linarith
  linarith

/-- **Fence (`hσ0` clause).** The zero vector is stationary but kills
the multiple. -/
theorem stationaryVec_smul_hσ0_fence_QA :
    ¬ ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (σ τ : Fin 2 → ℝ), (∀ i j, 0 ≤ A i j) →
      A.IsIrreducible → (∃ i j, 0 < A i j) → (∀ i, 0 < deg A i) →
      (∀ i, 0 ≤ σ i) → σ ᵥ* walkTransitionMatrix A = σ → (∀ i, 0 ≤ τ i) → τ ≠ 0 →
      τ ᵥ* walkTransitionMatrix A = τ → ∃ c : ℝ, 0 < c ∧ τ = c • σ := by
  intro h
  obtain ⟨c, hc, heq⟩ :=
    h A2 0 a2one A2_nonneg_QA A2_irreducible_QA A2_ex_QA A2_deg_QA
      (fun i => le_refl 0) a2zero_stationary a2one_nonneg a2one_ne_zero
      a2one_stationary
  have h0 := congrFun heq 0
  simp only [a2one_0, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul] at h0
  norm_num at h0

/-- **Fence (`hσs` clause).** The non-stationary witness. -/
theorem stationaryVec_smul_hσs_fence_QA :
    ¬ ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (σ τ : Fin 2 → ℝ), (∀ i j, 0 ≤ A i j) →
      A.IsIrreducible → (∃ i j, 0 < A i j) → (∀ i, 0 < deg A i) →
      (∀ i, 0 ≤ σ i) → σ ≠ 0 → (∀ i, 0 ≤ τ i) → τ ≠ 0 →
      τ ᵥ* walkTransitionMatrix A = τ → ∃ c : ℝ, 0 < c ∧ τ = c • σ := by
  intro h
  obtain ⟨c, hc, heq⟩ :=
    h A2 a2e0 a2one A2_nonneg_QA A2_irreducible_QA A2_ex_QA A2_deg_QA
      a2e0_nonneg a2e0_ne_zero a2one_nonneg a2one_ne_zero a2one_stationary
  have h1 := congrFun heq 1
  simp only [a2one_1, Pi.smul_apply, smul_eq_mul, a2e0_1] at h1
  have : c * (1 : ℝ) = 0 := by linarith
  have : c = 0 := by linarith
  linarith

/-- **Fence (`hτ` clause).** -/
theorem stationaryVec_smul_hτ_fence_QA :
    ¬ ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (σ τ : Fin 2 → ℝ), (∀ i j, 0 ≤ A i j) →
      A.IsIrreducible → (∃ i j, 0 < A i j) → (∀ i, 0 < deg A i) → (∀ i, 0 ≤ σ i) →
      σ ≠ 0 → σ ᵥ* walkTransitionMatrix A = σ → τ ≠ 0 →
      τ ᵥ* walkTransitionMatrix A = τ → ∃ c : ℝ, 0 < c ∧ τ = c • σ := by
  intro h
  obtain ⟨c, hc, heq⟩ :=
    h A2 a2one a2Signed A2_nonneg_QA A2_irreducible_QA A2_ex_QA A2_deg_QA
      a2one_nonneg a2one_ne_zero a2one_stationary a2Signed_ne_zero
      a2Signed_stationary
  have h0 := congrFun heq 0
  simp only [a2Signed_0, Pi.smul_apply, smul_eq_mul, a2one_0, one_mul] at h0
  have : c = -1 := by linarith
  linarith

/-- **Fence (`hτ0` clause).** -/
theorem stationaryVec_smul_hτ0_fence_QA :
    ¬ ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (σ τ : Fin 2 → ℝ), (∀ i j, 0 ≤ A i j) →
      A.IsIrreducible → (∃ i j, 0 < A i j) → (∀ i, 0 < deg A i) → (∀ i, 0 ≤ σ i) →
      σ ≠ 0 → σ ᵥ* walkTransitionMatrix A = σ → (∀ i, 0 ≤ τ i) →
      τ ᵥ* walkTransitionMatrix A = τ → ∃ c : ℝ, 0 < c ∧ τ = c • σ := by
  intro h
  obtain ⟨c, hc, heq⟩ :=
    h A2 a2one 0 A2_nonneg_QA A2_irreducible_QA A2_ex_QA A2_deg_QA
      a2one_nonneg a2one_ne_zero a2one_stationary (fun i => le_refl 0)
      a2zero_stationary
  have h0 := congrFun heq 0
  simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, a2one_0, one_mul,
    mul_one] at h0
  linarith

/-- **Fence (`hτs` clause).** -/
theorem stationaryVec_smul_hτs_fence_QA :
    ¬ ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (σ τ : Fin 2 → ℝ), (∀ i j, 0 ≤ A i j) →
      A.IsIrreducible → (∃ i j, 0 < A i j) → (∀ i, 0 < deg A i) → (∀ i, 0 ≤ σ i) →
      σ ≠ 0 → σ ᵥ* walkTransitionMatrix A = σ → (∀ i, 0 ≤ τ i) → τ ≠ 0 →
      ∃ c : ℝ, 0 < c ∧ τ = c • σ := by
  intro h
  obtain ⟨c, hc, heq⟩ :=
    h A2 a2one a2e0 A2_nonneg_QA A2_irreducible_QA A2_ex_QA A2_deg_QA
      a2one_nonneg a2one_ne_zero a2one_stationary a2e0_nonneg a2e0_ne_zero
  have h1 := congrFun heq 1
  simp only [a2e0_1, Pi.smul_apply, smul_eq_mul, a2one_1, mul_one] at h1
  linarith

/-- **Fence (`hσ` clause of `stationaryVec_pos_of_irreducible`).** -/
theorem stationaryVec_pos_hσ_fence_QA :
    ¬ ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (σ : Fin 2 → ℝ), (∀ i j, 0 ≤ A i j) →
      A.IsIrreducible → (∃ i j, 0 < A i j) → (∀ i, 0 < deg A i) → σ ≠ 0 →
      σ ᵥ* walkTransitionMatrix A = σ → ∀ i, 0 < σ i := by
  intro h
  have h1 := h A2 a2Signed A2_nonneg_QA A2_irreducible_QA A2_ex_QA A2_deg_QA
    a2Signed_ne_zero a2Signed_stationary 0
  rw [a2Signed_0] at h1
  exact absurd h1 (by norm_num)

/-- **Fence (`hσ0` clause).** -/
theorem stationaryVec_pos_hσ0_fence_QA :
    ¬ ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (σ : Fin 2 → ℝ), (∀ i j, 0 ≤ A i j) →
      A.IsIrreducible → (∃ i j, 0 < A i j) → (∀ i, 0 < deg A i) →
      (∀ i, 0 ≤ σ i) → σ ᵥ* walkTransitionMatrix A = σ → ∀ i, 0 < σ i := by
  intro h
  have h1 := h A2 0 A2_nonneg_QA A2_irreducible_QA A2_ex_QA A2_deg_QA
    (fun i => le_refl 0) a2zero_stationary 0
  exact absurd h1 (by norm_num)

/-- **Fence (`hσs` clause).** -/
theorem stationaryVec_pos_hσs_fence_QA :
    ¬ ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (σ : Fin 2 → ℝ), (∀ i j, 0 ≤ A i j) →
      A.IsIrreducible → (∃ i j, 0 < A i j) → (∀ i, 0 < deg A i) →
      (∀ i, 0 ≤ σ i) → σ ≠ 0 → ∀ i, 0 < σ i := by
  intro h
  have h1 := h A2 a2e0 A2_nonneg_QA A2_irreducible_QA A2_ex_QA A2_deg_QA
    a2e0_nonneg a2e0_ne_zero 1
  rw [a2e0_1] at h1
  exact absurd h1 (by norm_num)

/-! #### E11/E12: the reducibility reconciliations at `A4` -/

/-- **Fence (`hirr` clause of `existsUnique_stationaryVec_of_irreducible`)** —
the delivered hypothesis-free refutation restated in hypothesis form:
with nonnegativity, the positive entry and the degrees all genuine, the
`∃!` dies on the two block-supported stationary distributions. -/
theorem existsUnique_stationaryVec_hirr_fence_QA :
    ¬ ∀ (A : Matrix (Fin 4) (Fin 4) ℝ), (∀ i j, 0 ≤ A i j) → (∃ i j, 0 < A i j) →
      (∀ i, 0 < deg A i) →
      ∃! π : Fin 4 → ℝ, (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧
        π ᵥ* walkTransitionMatrix A = π := by
  intro h
  obtain ⟨τ, -, huniq⟩ :=
    h A4 A4_nonneg_QA ⟨0, 1, by rw [A4_01]; norm_num⟩ A4_deg_QA
  exact pi4a_ne_pi4b_QA ((huniq pi4a pi4a_pred_QA).trans (huniq pi4b pi4b_pred_QA).symm)

/-- **Fence (`hirr` clause of `stationaryVec_smul_of_irreducible`)** —
the delivered hypothesis-free refutation restated in hypothesis form. -/
theorem stationaryVec_smul_hirr_fence_QA :
    ¬ ∀ (A : Matrix (Fin 4) (Fin 4) ℝ) (σ τ : Fin 4 → ℝ), (∀ i j, 0 ≤ A i j) →
      (∃ i j, 0 < A i j) → (∀ i, 0 < deg A i) → (∀ i, 0 ≤ σ i) → σ ≠ 0 →
      σ ᵥ* walkTransitionMatrix A = σ → (∀ i, 0 ≤ τ i) → τ ≠ 0 →
      τ ᵥ* walkTransitionMatrix A = τ → ∃ c : ℝ, 0 < c ∧ τ = c • σ := by
  intro h
  obtain ⟨c, hc, heq⟩ :=
    h A4 pi4a pi4b A4_nonneg_QA ⟨0, 1, by rw [A4_01]; norm_num⟩ A4_deg_QA
      pi4a_pred_QA.1 pi4a_ne_zero_QA pi4a_pred_QA.2.2 pi4b_pred_QA.1
      pi4b_ne_zero_QA pi4b_pred_QA.2.2
  have h0 := congrFun heq 0
  simp only [pi4b_0, Pi.smul_apply, smul_eq_mul, pi4a_0] at h0
  have hpos : 0 < c * (1 / 2 : ℝ) := by positivity
  linarith

end AdversarialFences

/-! ## The irreducible pair's structural pins
(`proposals/heat-irreducible-pairs-pins.md`)

The consumption census (`wip/census_20260907_post10.txt`, inert set 25)
leaves `isIrreducible_transpose` and `pow_entry_le_one` never consumed.
This section pins both on GENUINELY DIRECTED input — the walk
transition matrix of the `A3` star, asymmetric even though `A3` itself
is symmetric (the rows are scaled by different reciprocals).
-/

section StructuralPins

theorem A3P_nonneg : ∀ i j, 0 ≤ walkTransitionMatrix A3 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [walkTransitionMatrix_apply, A3_01, A3_02, A3_10, A3_20,
      A3_00, A3_11, A3_12, A3_21, A3_22, A3_deg_0, A3_deg_1, A3_deg_2]

theorem A3PT_nonneg : ∀ i j, 0 ≤ (walkTransitionMatrix A3)ᵀ i j := by
  intro i j
  rw [Matrix.transpose_apply]
  exact A3P_nonneg j i

/-- **Route A — the transpose's irreducibility THROUGH the theorem
chain**: `A3`'s irreducibility transfers to the walk matrix by the
shelf lemma, then to the transpose by the never-consumed theorem. -/
theorem isp_transpose_irreducible_pin_QA :
    (walkTransitionMatrix A3)ᵀ.IsIrreducible :=
  isIrreducible_transpose
    (walkTransitionMatrix_isIrreducible A3 A3_irreducible_QA A3_deg_QA)

/-- **Route B — the same fact raw**, by explicit paths in the
arc-reversal digraph: every vertex reaches and is reached from the hub
`0` (the transpose's arcs are `0→1`, `0→2` at weight `1` and
`1→0`, `2→0` at weight `1/2` — the raw `A3P_*` entries read through
`Matrix.transpose_apply`). Two routes, one fact. -/
theorem isp_transpose_irreducible_raw_QA :
    (walkTransitionMatrix A3)ᵀ.IsIrreducible := by
  have hT01 : 0 < (walkTransitionMatrix A3)ᵀ (0 : Fin 3) 1 := by
    rw [Matrix.transpose_apply, A3P_10]; norm_num
  have hT02 : 0 < (walkTransitionMatrix A3)ᵀ (0 : Fin 3) 2 := by
    rw [Matrix.transpose_apply, A3P_20]; norm_num
  have hT10 : 0 < (walkTransitionMatrix A3)ᵀ (1 : Fin 3) 0 := by
    rw [Matrix.transpose_apply, A3P_01]; norm_num
  have hT20 : 0 < (walkTransitionMatrix A3)ᵀ (2 : Fin 3) 0 := by
    rw [Matrix.transpose_apply, A3P_02]; norm_num
  intro i j
  fin_cases i
  · fin_cases j
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head hT01 Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head hT02 Relation.ReflTransGen.refl
  · fin_cases j
    · exact Relation.ReflTransGen.head hT10 Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head hT10
        (Relation.ReflTransGen.head hT02 Relation.ReflTransGen.refl)
  · fin_cases j
    · exact Relation.ReflTransGen.head hT20 Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head hT20
        (Relation.ReflTransGen.head hT01 Relation.ReflTransGen.refl)
    · exact Relation.ReflTransGen.refl

/-- **The power-positivity corollary THROUGH the chain** (transpose →
power positivity), on genuinely directed input — the transpose's
irreducibility consumed onward, not left as an inert conclusion. -/
theorem isp_transpose_pow_pos_pin_QA :
    ∃ m : ℕ, 0 < ((walkTransitionMatrix A3)ᵀ ^ m) (0 : Fin 3) 1 :=
  exists_pow_pos_of_isIrreducible A3PT_nonneg
    isp_transpose_irreducible_pin_QA 0 1

/-- The raw witness: the transpose's `(0, 1)` entry is exactly the
walk's `(1, 0)` entry `1` — the existential satisfied at `m = 1`, so
the chain's conclusion is non-vacuous at a pinned value. -/
theorem isp_transpose_entry_one_QA :
    ((walkTransitionMatrix A3)ᵀ ^ 1) (0 : Fin 3) 1 = 1 := by
  rw [pow_one, Matrix.transpose_apply, A3P_10]

/-- **The `[0, 1]` power-entry bound attained with equality**: the
star's two-step return `(P²) 0 0 = 1 ≤ 1` THROUGH the theorem — the
bound sharp at a stochastic power entry that genuinely reaches `1`. -/
theorem isp_pow_entry_le_one_attained_QA :
    (walkTransitionMatrix A3 ^ 2) (0 : Fin 3) 0 ≤ 1 :=
  pow_entry_le_one (walkTransitionMatrix A3) A3P_nonneg
    (fun i => walkTransitionMatrix_row_sum A3 A3_deg_QA i) 2 0 0

theorem isp_P2_00_eq_one_QA :
    (walkTransitionMatrix A3 ^ 2) (0 : Fin 3) 0 = 1 := by
  rw [pow_two, Matrix.mul_apply]
  simp only [A3P_00, A3P_10, A3P_20, A3P_01, A3P_02, A3P_11, A3P_12,
    A3P_21, A3P_22, Fin.sum_univ_three]
  norm_num

end StructuralPins

end Scaffold.QA.SpectralGraph
