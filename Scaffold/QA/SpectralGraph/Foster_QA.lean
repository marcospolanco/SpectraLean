/-
  Foster_QA.lean

  QA for `Scaffold.Mathlib.GraphTheory.Foster` (proposal
  `spectral-graph-sparsification.md`, Phase A acceptance item 3):
  Foster's theorem instantiated on the four canonical small networks —
  the cliques `K₃` and `K₄` (where the proposal's calibration note
  demands the ordered-pair double-counting factor be tested
  explicitly), the path `P₃`, and the 3-leaf star — with every effective
  resistance pinned by an explicit potential witness and each ordered
  Foster sum computed independently of the theorem from those pinned
  values, then cross-checked against the theorem's `card V - 1`.

  Falsification content, per the load-bearing-growth policy:

  - **The double-counting factor:** on `K₃` the ordered sum computes to
    `4 ≠ 2 = card V - 1` and on `K₄` to `6 ≠ 3 = card V - 1` — the
    undirected statement `∑_{u<v} w_e R_e = n - 1` and the ordered-pair
    Lean statement differ by exactly the theorem's `/ 2`, and a
    statement shape that dropped it (either side) would be refuted by
    these witnesses.
  - **Independent value computation:** every resistance enters the
    ordered sums through a potential witness
    (`laplacian A *ᵥ f = e u − e v`) computed from the raw definitions,
    not through the theorem — the agreement of the two routes is the
    check. On `K₄` the potential `f = (e i − e j)/4` is proved to solve
    the unit demand for *every* pair, so all twelve ordered terms are
    pinned by one general lemma.
  - **Leverage scores:** the `K₃` edge leverage computes to `1/3` and
    the total to `2` (ordered form), the numerical content of
    `sum_leverageScore_eq_two`.
-/

import Scaffold.Mathlib.GraphTheory.Foster

open scoped BigOperators Matrix

namespace SpectralGraphTheory

/-!
## Fixture 1: the triangle `K₃`
-/

/-- The unit triangle `K₃` (entrywise-if fixture pattern; matrix
notation's zero-function normalization leaves `vecTail` leftovers). -/
def fosterTriAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if i = j then 0 else 1

theorem fosterTriAdj_isSymm : fosterTriAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [fosterTriAdj]

theorem fosterTriAdj_nonneg : ∀ i j, 0 ≤ fosterTriAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [fosterTriAdj]

/-- The support graph of the triangle is connected: both other vertices
are adjacent to `0`. -/
theorem fosterTri_connected :
    (supportGraph fosterTriAdj fosterTriAdj_isSymm).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
      ⟨by decide, by simp [fosterTriAdj]⟩ SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 2) (w := 2)
      ⟨by decide, by simp [fosterTriAdj]⟩ SimpleGraph.Walk.nil⟩

/-- `f = ![1, 1/3, 2/3]` solves the `e 0 − e 1` unit demand on `K₃`. -/
theorem fosterTri_pot01 :
    (laplacian fosterTriAdj).mulVec ![1, 1/3, 2/3]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, fosterTriAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three] <;>
    try norm_num

/-- **Triangle resistance:** `R 0 1 = 2/3` — the direct edge in parallel
with the two-edge path of resistance `2` (`1 ⊕ 2 = 2/3`). -/
theorem fosterTri_R01 : effectiveResistance fosterTriAdj 0 1 = 2 / 3 :=
  effectiveResistance_eq fosterTriAdj fosterTriAdj_isSymm fosterTriAdj_nonneg
    fosterTri_connected
    ⟨![1, 1/3, 2/3], fosterTri_pot01, by norm_num [Matrix.cons_val']⟩

/-- `f = ![1/3, 0, -1/3]` solves the `e 0 − e 2` unit demand on `K₃`. -/
theorem fosterTri_pot02 :
    (laplacian fosterTriAdj).mulVec ![1/3, 0, -1/3]
      = Pi.single 0 (1 : ℝ) - Pi.single 2 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, fosterTriAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three] <;>
    try norm_num

theorem fosterTri_R02 : effectiveResistance fosterTriAdj 0 2 = 2 / 3 :=
  effectiveResistance_eq fosterTriAdj fosterTriAdj_isSymm fosterTriAdj_nonneg
    fosterTri_connected
    ⟨![1/3, 0, -1/3], fosterTri_pot02, by norm_num [Matrix.cons_val']⟩

/-- `f = ![0, 1/3, -1/3]` solves the `e 1 − e 2` unit demand on `K₃`. -/
theorem fosterTri_pot12 :
    (laplacian fosterTriAdj).mulVec ![0, 1/3, -1/3]
      = Pi.single 1 (1 : ℝ) - Pi.single 2 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, fosterTriAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three] <;>
    try norm_num

theorem fosterTri_R12 : effectiveResistance fosterTriAdj 1 2 = 2 / 3 :=
  effectiveResistance_eq fosterTriAdj fosterTriAdj_isSymm fosterTriAdj_nonneg
    fosterTri_connected
    ⟨![0, 1/3, -1/3], fosterTri_pot12, by norm_num [Matrix.cons_val']⟩

/-- The reversed-pair values, through `effectiveResistance_symm`. -/
theorem fosterTri_R10 : effectiveResistance fosterTriAdj 1 0 = 2 / 3 := by
  rw [effectiveResistance_symm fosterTriAdj fosterTriAdj_isSymm
    fosterTriAdj_nonneg fosterTri_connected, fosterTri_R01]

theorem fosterTri_R20 : effectiveResistance fosterTriAdj 2 0 = 2 / 3 := by
  rw [effectiveResistance_symm fosterTriAdj fosterTriAdj_isSymm
    fosterTriAdj_nonneg fosterTri_connected, fosterTri_R02]

theorem fosterTri_R21 : effectiveResistance fosterTriAdj 2 1 = 2 / 3 := by
  rw [effectiveResistance_symm fosterTriAdj fosterTriAdj_isSymm
    fosterTriAdj_nonneg fosterTri_connected, fosterTri_R12]

/-- **Triangle Foster sum, computed independently of the theorem:** the
ordered-pair sum is `6 ⬝ (2/3) = 4` — twice the undirected total
`2 = card V − 1`, the double-counting factor made visible. -/
theorem fosterTri_ordered_sum_QA :
    ∑ i, ∑ j, fosterTriAdj i j * effectiveResistance fosterTriAdj i j = 4 := by
  simp only [Fin.sum_univ_three, fosterTri_R01, fosterTri_R02,
    fosterTri_R10, fosterTri_R20, fosterTri_R12, fosterTri_R21]
  simp [fosterTriAdj]
  try norm_num

/-- **Triangle Foster theorem instance:** the ordered sum halved is
`card V − 1 = 2`, reduced numerically. -/
theorem fosterTri_theorem_QA :
    (∑ i, ∑ j, fosterTriAdj i j * effectiveResistance fosterTriAdj i j) / 2 = 2 :=
  (foster_theorem fosterTriAdj fosterTriAdj_isSymm fosterTriAdj_nonneg
    fosterTri_connected).trans (by norm_num)

/-- **Double-counting factor witness (`K₃`):** the ordered sum is `4`,
which is *not* `card V − 1 = 2` — the `/ 2` in `foster_theorem` is
load-bearing, and both routes agree on the halved value. -/
theorem fosterTri_factor_QA :
    (∑ i, ∑ j, fosterTriAdj i j * effectiveResistance fosterTriAdj i j) / 2 = 2
      ∧ ∑ i, ∑ j, fosterTriAdj i j * effectiveResistance fosterTriAdj i j ≠ 2 := by
  refine ⟨fosterTri_theorem_QA, ?_⟩
  rw [fosterTri_ordered_sum_QA]
  norm_num

/-- **Triangle leverage:** the total is exactly `2` in the ordered form
(the theorem's leverage corollary), and a single edge carries `1/3` of
the Foster budget `2`. -/
theorem fosterTri_leverage_sum_QA :
    ∑ i, ∑ j, leverageScore fosterTriAdj i j = 2 :=
  sum_leverageScore_eq_two fosterTriAdj fosterTriAdj_isSymm fosterTriAdj_nonneg
    fosterTri_connected (by decide)

theorem fosterTri_leverage_edge_QA :
    leverageScore fosterTriAdj 0 1 = 1 / 3 := by
  rw [leverageScore, fosterTri_R01]
  simp [fosterTriAdj]
  norm_num

/-!
## Fixture 2: the clique `K₄` — the general-pair potential
-/

/-- The unit clique `K₄`. -/
def fosterK4Adj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => if i = j then 0 else 1

theorem fosterK4Adj_isSymm : fosterK4Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [fosterK4Adj]

theorem fosterK4Adj_nonneg : ∀ i j, 0 ≤ fosterK4Adj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [fosterK4Adj]

theorem fosterK4_connected :
    (supportGraph fosterK4Adj fosterK4Adj_isSymm).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
      ⟨by decide, by simp [fosterK4Adj]⟩ SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 2) (w := 2)
      ⟨by decide, by simp [fosterK4Adj]⟩ SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 3) (w := 3)
      ⟨by decide, by simp [fosterK4Adj]⟩ SimpleGraph.Walk.nil⟩

/-- `K₄`'s Laplacian entrywise: `4` on the diagonal, `-1` off it (every
degree is `3`). Computed by exhaustive cases. -/
theorem fosterK4_laplacian_apply (a b : Fin 4) :
    laplacian fosterK4Adj a b = (if a = b then (4 : ℝ) else 0) - 1 := by
  fin_cases a <;> fin_cases b <;>
    simp [laplacian, degreeMatrix, deg, fosterK4Adj, Fin.sum_univ_four] <;>
    norm_num

/-- The `K₄` Foster potential for the pair `(i, j)`: `(e i − e j)/4`. -/
noncomputable def fosterK4Pot (i j : Fin 4) : Fin 4 → ℝ :=
  Pi.single i (1 / 4 : ℝ) - Pi.single j (1 / 4 : ℝ)

theorem fosterK4Pot_sum (i j : Fin 4) : ∑ b, fosterK4Pot i j b = 0 := by
  simp only [fosterK4Pot, Pi.sub_apply, Pi.single_apply, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

/-- **The general-pair demand equation on `K₄`:** `(e i − e j)/4` solves
the unit demand for *every* pair. The Laplacian acts entrywise as
`4 ⬝ f a − ∑ b, f b` (diagonal `4`, off-diagonal `-1`), and the
potential has total sum `0`. -/
theorem fosterK4Pot_demand (i j : Fin 4) :
    (laplacian fosterK4Adj).mulVec (fosterK4Pot i j)
      = Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ) := by
  funext a
  simp only [Pi.sub_apply, Pi.single_apply]
  have hsplit : ∀ b : Fin 4, laplacian fosterK4Adj a b * fosterK4Pot i j b
      = (if a = b then (4 : ℝ) else 0) * fosterK4Pot i j b
        - fosterK4Pot i j b := by
    intro b
    rw [fosterK4_laplacian_apply, sub_mul, one_mul]
  have hself : ∑ b, (if a = b then (4 : ℝ) else 0) * fosterK4Pot i j b
      = 4 * fosterK4Pot i j a := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  calc (laplacian fosterK4Adj).mulVec (fosterK4Pot i j) a
      = ∑ b, laplacian fosterK4Adj a b * fosterK4Pot i j b := rfl
    _ = ∑ b, ((if a = b then (4 : ℝ) else 0) * fosterK4Pot i j b
          - fosterK4Pot i j b) :=
        Finset.sum_congr rfl fun b _ => hsplit b
    _ = ∑ b, (if a = b then (4 : ℝ) else 0) * fosterK4Pot i j b
          - ∑ b, fosterK4Pot i j b := Finset.sum_sub_distrib
    _ = 4 * fosterK4Pot i j a - ∑ b, fosterK4Pot i j b := by rw [hself]
    _ = 4 * fosterK4Pot i j a - 0 := by rw [fosterK4Pot_sum]
    _ = 4 * fosterK4Pot i j a := sub_zero _
    _ = ((if a = i then (1 : ℝ) else 0) - (if a = j then (1 : ℝ) else 0)) := by
        simp only [fosterK4Pot, Pi.sub_apply, Pi.single_apply]
        split_ifs <;> norm_num

/-- **Every `K₄` pair has resistance `1/2`** (`R_e = 2/n` at `n = 4`),
from the general-pair potential. -/
theorem fosterK4_R_of_ne (i j : Fin 4) (hij : i ≠ j) :
    effectiveResistance fosterK4Adj i j = 1 / 2 := by
  refine effectiveResistance_eq fosterK4Adj fosterK4Adj_isSymm
    fosterK4Adj_nonneg fosterK4_connected
    ⟨fosterK4Pot i j, fosterK4Pot_demand i j, ?_⟩
  have h1 : fosterK4Pot i j i = 1 / 4 := by
    simp only [fosterK4Pot, Pi.sub_apply, Pi.single_apply]
    by_cases h : i = j
    · exact absurd h hij
    · simp [h, Ne.symm h]
      try norm_num
  have h2 : fosterK4Pot i j j = -1 / 4 := by
    simp only [fosterK4Pot, Pi.sub_apply, Pi.single_apply]
    by_cases h : i = j
    · exact absurd h hij
    · simp [h, Ne.symm h]
      try norm_num
  rw [h1, h2]
  norm_num

/-- **`K₄` Foster sum, computed independently of the theorem:** twelve
ordered edges at `1/2` each give `6`. -/
theorem fosterK4_ordered_sum_QA :
    ∑ i, ∑ j, fosterK4Adj i j * effectiveResistance fosterK4Adj i j = 6 := by
  have hpair : ∀ i j : Fin 4,
      fosterK4Adj i j * effectiveResistance fosterK4Adj i j
        = if i = j then 0 else 1 / 2 := by
    intro i j
    by_cases h : i = j
    · simp [fosterK4Adj, h]
    · rw [fosterK4_R_of_ne i j h]
      simp [fosterK4Adj, h]
  simp [Fin.sum_univ_four, hpair]
  norm_num

/-- **`K₄` Foster theorem instance:** `6 / 2 = 3 = card V − 1`. -/
theorem fosterK4_theorem_QA :
    (∑ i, ∑ j, fosterK4Adj i j * effectiveResistance fosterK4Adj i j) / 2 = 3 :=
  (foster_theorem fosterK4Adj fosterK4Adj_isSymm fosterK4Adj_nonneg
    fosterK4_connected).trans (by norm_num)

/-- **Double-counting factor witness (`K₄`):** the ordered sum `6` is
*not* `card V − 1 = 3`. -/
theorem fosterK4_factor_QA :
    (∑ i, ∑ j, fosterK4Adj i j * effectiveResistance fosterK4Adj i j) / 2 = 3
      ∧ ∑ i, ∑ j, fosterK4Adj i j * effectiveResistance fosterK4Adj i j ≠ 3 := by
  refine ⟨fosterK4_theorem_QA, ?_⟩
  rw [fosterK4_ordered_sum_QA]
  norm_num

/-- **`K₄` edge leverage:** one edge carries `1/2 / 3 = 1/6` of the
Foster budget `3`. -/
theorem fosterK4_leverage_edge_QA :
    leverageScore fosterK4Adj 0 1 = 1 / 6 := by
  rw [leverageScore, fosterK4_R_of_ne 0 1 (by decide)]
  simp [fosterK4Adj]
  norm_num

/-!
## Fixture 3: the path `P₃`
-/

/-- The path `0 — 1 — 2`. -/
def fosterPathAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 0; 1, 0, 1; 0, 1, 0]

theorem fosterPathAdj_isSymm : fosterPathAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [fosterPathAdj]

theorem fosterPathAdj_nonneg : ∀ i j, 0 ≤ fosterPathAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [fosterPathAdj]

theorem fosterPath_connected :
    (supportGraph fosterPathAdj fosterPathAdj_isSymm).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨1, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.cons (u := 1) (v := 0) (w := 0)
      ⟨by decide, by simp [fosterPathAdj]⟩ SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 1) (v := 2) (w := 2)
      ⟨by decide, by simp [fosterPathAdj]⟩ SimpleGraph.Walk.nil⟩

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- `f = ![1, 0, 0]` solves the `e 0 − e 1` unit demand on `P₃`. -/
theorem fosterPath_pot01 :
    (laplacian fosterPathAdj).mulVec ![1, 0, 0]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, fosterPathAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three] <;>
    try norm_num

/-- **Path resistance:** `R 0 1 = 1` — a single unit edge. -/
theorem fosterPath_R01 : effectiveResistance fosterPathAdj 0 1 = 1 :=
  effectiveResistance_eq fosterPathAdj fosterPathAdj_isSymm fosterPathAdj_nonneg
    fosterPath_connected
    ⟨![1, 0, 0], fosterPath_pot01, by norm_num [Matrix.cons_val']⟩

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- `f = ![0, 0, -1]` solves the `e 1 − e 2` unit demand on `P₃`. -/
theorem fosterPath_pot12 :
    (laplacian fosterPathAdj).mulVec ![0, 0, -1]
      = Pi.single 1 (1 : ℝ) - Pi.single 2 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, fosterPathAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three] <;>
    try norm_num

theorem fosterPath_R12 : effectiveResistance fosterPathAdj 1 2 = 1 :=
  effectiveResistance_eq fosterPathAdj fosterPathAdj_isSymm fosterPathAdj_nonneg
    fosterPath_connected
    ⟨![0, 0, -1], fosterPath_pot12, by norm_num [Matrix.cons_val']⟩

theorem fosterPath_R10 : effectiveResistance fosterPathAdj 1 0 = 1 := by
  rw [effectiveResistance_symm fosterPathAdj fosterPathAdj_isSymm
    fosterPathAdj_nonneg fosterPath_connected, fosterPath_R01]

theorem fosterPath_R21 : effectiveResistance fosterPathAdj 2 1 = 1 := by
  rw [effectiveResistance_symm fosterPathAdj fosterPathAdj_isSymm
    fosterPathAdj_nonneg fosterPath_connected, fosterPath_R12]

/-- **Path Foster sum, computed independently of the theorem:** the two
edges contribute `1 + 1` in each direction — `4` ordered. Note the
non-edge pair `(0, 2)` (resistance `2`) does *not* appear: its
conductance weight is `0`, exactly as Foster's sum ranges over edges. -/
theorem fosterPath_ordered_sum_QA :
    ∑ i, ∑ j, fosterPathAdj i j * effectiveResistance fosterPathAdj i j = 4 := by
  simp only [Fin.sum_univ_three, fosterPath_R01, fosterPath_R10,
    fosterPath_R12, fosterPath_R21]
  simp [fosterPathAdj]
  try norm_num

theorem fosterPath_theorem_QA :
    (∑ i, ∑ j, fosterPathAdj i j * effectiveResistance fosterPathAdj i j) / 2 = 2 :=
  (foster_theorem fosterPathAdj fosterPathAdj_isSymm fosterPathAdj_nonneg
    fosterPath_connected).trans (by norm_num)

/-!
## Fixture 4: the 3-leaf star (center `0`)
-/

/-- The star with center `0` and leaves `1, 2, 3`. -/
def fosterStarAdj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    if i = j then 0 else if i = 0 ∨ j = 0 then 1 else 0

theorem fosterStarAdj_isSymm : fosterStarAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [fosterStarAdj]

theorem fosterStarAdj_nonneg : ∀ i j, 0 ≤ fosterStarAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [fosterStarAdj]

theorem fosterStar_connected :
    (supportGraph fosterStarAdj fosterStarAdj_isSymm).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
      ⟨by decide, by simp [fosterStarAdj]⟩ SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 2) (w := 2)
      ⟨by decide, by simp [fosterStarAdj]⟩ SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 3) (w := 3)
      ⟨by decide, by simp [fosterStarAdj]⟩ SimpleGraph.Walk.nil⟩

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- `f = ![0, -1, 0, 0]` solves the `e 0 − e 1` unit demand on the star. -/
theorem fosterStar_pot01 :
    (laplacian fosterStarAdj).mulVec ![0, -1, 0, 0]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, fosterStarAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_four] <;>
    try norm_num

/-- **Star resistance, spoke:** `R 0 1 = 1`. -/
theorem fosterStar_R01 : effectiveResistance fosterStarAdj 0 1 = 1 :=
  effectiveResistance_eq fosterStarAdj fosterStarAdj_isSymm fosterStarAdj_nonneg
    fosterStar_connected
    ⟨![0, -1, 0, 0], fosterStar_pot01, by norm_num [Matrix.cons_val']⟩

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem fosterStar_pot02 :
    (laplacian fosterStarAdj).mulVec ![0, 0, -1, 0]
      = Pi.single 0 (1 : ℝ) - Pi.single 2 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, fosterStarAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_four] <;>
    try norm_num

theorem fosterStar_R02 : effectiveResistance fosterStarAdj 0 2 = 1 :=
  effectiveResistance_eq fosterStarAdj fosterStarAdj_isSymm fosterStarAdj_nonneg
    fosterStar_connected
    ⟨![0, 0, -1, 0], fosterStar_pot02, by norm_num [Matrix.cons_val']⟩

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem fosterStar_pot03 :
    (laplacian fosterStarAdj).mulVec ![0, 0, 0, -1]
      = Pi.single 0 (1 : ℝ) - Pi.single 3 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, fosterStarAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_four] <;>
    try norm_num

theorem fosterStar_R03 : effectiveResistance fosterStarAdj 0 3 = 1 :=
  effectiveResistance_eq fosterStarAdj fosterStarAdj_isSymm fosterStarAdj_nonneg
    fosterStar_connected
    ⟨![0, 0, 0, -1], fosterStar_pot03, by norm_num [Matrix.cons_val']⟩

theorem fosterStar_R10 : effectiveResistance fosterStarAdj 1 0 = 1 := by
  rw [effectiveResistance_symm fosterStarAdj fosterStarAdj_isSymm
    fosterStarAdj_nonneg fosterStar_connected, fosterStar_R01]

theorem fosterStar_R20 : effectiveResistance fosterStarAdj 2 0 = 1 := by
  rw [effectiveResistance_symm fosterStarAdj fosterStarAdj_isSymm
    fosterStarAdj_nonneg fosterStar_connected, fosterStar_R02]

theorem fosterStar_R30 : effectiveResistance fosterStarAdj 3 0 = 1 := by
  rw [effectiveResistance_symm fosterStarAdj fosterStarAdj_isSymm
    fosterStarAdj_nonneg fosterStar_connected, fosterStar_R03]

/-- **Star Foster sum, computed independently of the theorem:** the
three spokes contribute `1` each in both directions — `6` ordered. The
leaf-leaf pairs (resistance `2`) have conductance `0` and do not
appear. -/
theorem fosterStar_ordered_sum_QA :
    ∑ i, ∑ j, fosterStarAdj i j * effectiveResistance fosterStarAdj i j = 6 := by
  simp only [Fin.sum_univ_four, fosterStar_R01, fosterStar_R02,
    fosterStar_R03, fosterStar_R10, fosterStar_R20, fosterStar_R30]
  simp [fosterStarAdj]
  try norm_num

theorem fosterStar_theorem_QA :
    (∑ i, ∑ j, fosterStarAdj i j * effectiveResistance fosterStarAdj i j) / 2 = 3 :=
  (foster_theorem fosterStarAdj fosterStarAdj_isSymm fosterStarAdj_nonneg
    fosterStar_connected).trans (by norm_num)

end SpectralGraphTheory
