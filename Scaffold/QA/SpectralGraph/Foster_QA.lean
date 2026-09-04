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

  Adversarial fences (`proposals/adversarial-fences-foster-family.md`,
  2026-09-04): the hypothesis-necessity pass over the four theorems and
  the leverage object — the `hnn`/`hconn` clauses at the delivered
  signed rank-1 and disconnected fixtures, and the `hcard` division-guard
  junk corner at a one-vertex fixture (`FosterFences` section below).
-/

import Scaffold.Mathlib.GraphTheory.Foster
import Scaffold.QA.SpectralGraph.EffectiveResistance_QA

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

/-!
## FosterFences: the adversarial fence audit (proposal `adversarial-fences-foster-family.md`)

The hypothesis-necessity pass over the Foster family: the four theorems
of `Foster.lean` plus the `leverageScore` object. Nine fences at the
delivered signed rank-1 fixture `QA.sgnK4Adj`, the delivered
disconnected fixture `QA.connDiscAdj`, and a new one-vertex fixture
(the leverage division guard's `0/0` junk corner). The four `hA` clauses
are recorded non-fenceable: every statement of the family either
consumes `laplacian_symmetric A hA` in its own conclusion display or
carries `hconn : (supportGraph A hA).Connected`, whose statement itself
consumes the symmetry proof — the same entanglement mechanism the
effective-resistance audit recorded.
-/

/-! ### Generic eigen engines

Three facts at the level of an arbitrary symmetric matrix (no graph
hypotheses): kernel vectors have no component along nonzero-eigenvalue
eigenvectors; a genuine eigenvector is orthogonal to every
zero-eigenvalue eigenvector off its own eigenvalue; and two non-parallel
kernel vectors force at least two zero eigenvalues. All are
`dotProduct_eigvecOf_mulVec` (self-adjointness in coordinates) applied
to the relevant equation, plus the eigenbasis expansion.
-/

/-- **Engine (kernel orthogonality).** If `g` is in the kernel of a
symmetric `L`, then every eigenvector with a nonzero eigenvalue is
orthogonal to `g`: the eigen-equation pairs the zero image against the
eigenvalue-scaled component. -/
theorem ff_eigvec_dotProduct_of_kernel {V : Type} [Fintype V] [DecidableEq V]
    {L : Matrix V V ℝ} (hL : L.IsSymm) {g : V → ℝ}
    (hg : L *ᵥ g = 0) (k : V)
    (hk : eigvalOf L hL k ≠ 0) :
    Matrix.dotProduct (eigvecOf L hL k) g = 0 := by
  have h := dotProduct_eigvecOf_mulVec hL k g
  rw [hg, Matrix.dotProduct_zero] at h
  exact (mul_eq_zero.1 h.symm).resolve_left hk

/-- **Engine (eigenvalue separation).** If `u` is a genuine eigenvector
of a symmetric `L` with eigenvalue `c ≠ 0`, then every zero-eigenvalue
eigenvector is orthogonal to `u`: pairing the eigen-equations gives
`(c − λₖ) (vₖ ⬝ᵥ u) = 0`. -/
theorem ff_eigvec_dotProduct_of_eigen {V : Type} [Fintype V] [DecidableEq V]
    {L : Matrix V V ℝ} (hL : L.IsSymm) {u : V → ℝ} {c : ℝ}
    (hc : c ≠ 0) (hu : L *ᵥ u = c • u) (k : V)
    (hk : eigvalOf L hL k = 0) :
    Matrix.dotProduct (eigvecOf L hL k) u = 0 := by
  have h : eigvalOf L hL k * Matrix.dotProduct (eigvecOf L hL k) u
      = c * Matrix.dotProduct (eigvecOf L hL k) u := by
    rw [← dotProduct_eigvecOf_mulVec hL k u, hu, Matrix.dotProduct_smul,
      smul_eq_mul]
  have h2 : (c - eigvalOf L hL k)
      * Matrix.dotProduct (eigvecOf L hL k) u = 0 := by
    rw [sub_mul, h, sub_self]
  rw [hk, sub_zero] at h2
  exact (mul_eq_zero.1 h2).resolve_left hc

/-- **Engine (the zero-eigenvalue count).** Two non-parallel kernel
vectors of a symmetric matrix force at least two zero eigenvalues: every
kernel vector's eigen-expansion lives on the zero-eigenvalue eigenvectors
(the kernel-orthogonality engine), so a filter of size ≤ 1 would force
the whole kernel onto one line — on which two nonzero vectors are
parallel. This inverts `card_filter_eigvalOf_laplacian_eq_zero`'s own
"at most one index" argument. -/
theorem ff_two_kernel_filter_card_ge_two {V : Type} [Fintype V] [DecidableEq V]
    {L : Matrix V V ℝ} (hL : L.IsSymm) {g₁ g₂ : V → ℝ}
    (h₁ : L *ᵥ g₁ = 0) (h₂ : L *ᵥ g₂ = 0)
    (hne₁ : g₁ ≠ 0) (hne₂ : g₂ ≠ 0)
    (hnp : ¬ ∃ c : ℝ, g₁ = c • g₂) :
    2 ≤ (Finset.univ.filter fun k => eigvalOf L hL k = 0).card := by
  have hexp : ∀ g : V → ℝ, L *ᵥ g = 0 → ∀ a : V, g a
      = ∑ k ∈ Finset.univ.filter fun k => eigvalOf L hL k = 0,
        Matrix.dotProduct (eigvecOf L hL k) g * eigvecOf L hL k a := by
    intro g hg a
    have hkey : ∑ k : V, Matrix.dotProduct (eigvecOf L hL k) g
          * eigvecOf L hL k a
        = ∑ k ∈ Finset.univ.filter fun k => eigvalOf L hL k = 0,
          Matrix.dotProduct (eigvecOf L hL k) g * eigvecOf L hL k a :=
      (Finset.sum_subset (Finset.filter_subset _ Finset.univ)
        fun k _ hk' => by
          have hk : eigvalOf L hL k ≠ 0 := fun h0 =>
            hk' (Finset.mem_filter.2 ⟨Finset.mem_univ k, h0⟩)
          rw [ff_eigvec_dotProduct_of_kernel hL hg k hk, zero_mul]).symm
    rw [← hkey, eigvecOf_expansion_apply hL g a]
  by_contra hlt
  push_neg at hlt
  have hcard : (Finset.univ.filter fun k => eigvalOf L hL k = 0).card = 0 ∨
      (Finset.univ.filter fun k => eigvalOf L hL k = 0).card = 1 := by omega
  rcases hcard with h0 | h1
  · have hempty := Finset.card_eq_zero.1 h0
    exact hne₁ (funext fun a => by
      have hga := hexp g₁ h₁ a
      rw [hempty, Finset.sum_empty] at hga
      simpa using hga)
  · obtain ⟨k₀, hsing⟩ := Finset.card_eq_one.1 h1
    have hg₁ : g₁ = Matrix.dotProduct (eigvecOf L hL k₀) g₁
        • eigvecOf L hL k₀ := by
      funext a
      rw [hexp g₁ h₁ a, hsing, Finset.sum_singleton, Pi.smul_apply,
        smul_eq_mul]
    have hg₂ : g₂ = Matrix.dotProduct (eigvecOf L hL k₀) g₂
        • eigvecOf L hL k₀ := by
      funext a
      rw [hexp g₂ h₂ a, hsing, Finset.sum_singleton, Pi.smul_apply,
        smul_eq_mul]
    have hc₂ : Matrix.dotProduct (eigvecOf L hL k₀) g₂ ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hg₂
      exact hne₂ hg₂
    refine hnp ⟨Matrix.dotProduct (eigvecOf L hL k₀) g₁
      * (Matrix.dotProduct (eigvecOf L hL k₀) g₂)⁻¹, ?_⟩
    funext a
    have e1 : g₁ a = Matrix.dotProduct (eigvecOf L hL k₀) g₁
        * eigvecOf L hL k₀ a := by
      have h := congrFun hg₁ a
      simpa [Pi.smul_apply, smul_eq_mul] using h
    have e2 : g₂ a = Matrix.dotProduct (eigvecOf L hL k₀) g₂
        * eigvecOf L hL k₀ a := by
      have h := congrFun hg₂ a
      simpa [Pi.smul_apply, smul_eq_mul] using h
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [e2, e1]
    field_simp
    ring

/-- **Engine (the spectral sum is strictly positive).** For a symmetric
matrix whose eigenvalues are all nonnegative, the Foster spectral sum
over a coordinate pair `(a, b)` is strictly positive whenever some
genuine eigenvector `u` (eigenvalue `c ≠ 0`) has different coordinates
at `a` and `b`: `u`'s eigen-expansion lives on the nonzero modes (the
separation engine), every nonzero-mode term is nonnegative, and if they
all vanished then every nonzero-mode eigenvector would have equal `a`-
and `b`-coordinates, forcing `u a = u b`. -/
theorem ff_sum_eigbasis_pos {V : Type} [Fintype V] [DecidableEq V]
    {L : Matrix V V ℝ} (hL : L.IsSymm)
    (hpsd : ∀ k : V, 0 ≤ eigvalOf L hL k)
    {u : V → ℝ} {c : ℝ} (hc : c ≠ 0) (hu : L *ᵥ u = c • u)
    (a b : V) (hab : u a ≠ u b) :
    0 < ∑ k, (if eigvalOf L hL k = 0 then (0 : ℝ)
      else (eigvecOf L hL k a - eigvecOf L hL k b) ^ 2
        / eigvalOf L hL k) := by
  have hterm_nonneg : ∀ k : V, 0 ≤ (if eigvalOf L hL k = 0 then (0 : ℝ)
      else (eigvecOf L hL k a - eigvecOf L hL k b) ^ 2
        / eigvalOf L hL k) := by
    intro k
    by_cases hk : eigvalOf L hL k = 0
    · rw [if_pos hk]
    · rw [if_neg hk]
      exact div_nonneg (sq_nonneg _) (hpsd k)
  have hsum_nonneg : 0 ≤ ∑ k ∈ (Finset.univ : Finset V),
      (if eigvalOf L hL k = 0 then (0 : ℝ)
        else (eigvecOf L hL k a - eigvecOf L hL k b) ^ 2
          / eigvalOf L hL k) :=
    Finset.sum_nonneg fun k _ => hterm_nonneg k
  by_contra hlt
  push_neg at hlt
  have hsum0 : ∑ k, (if eigvalOf L hL k = 0 then (0 : ℝ)
      else (eigvecOf L hL k a - eigvecOf L hL k b) ^ 2
        / eigvalOf L hL k) = 0 := le_antisymm hlt hsum_nonneg
  have hterm0 : ∀ k ∈ (Finset.univ : Finset V),
      (if eigvalOf L hL k = 0 then (0 : ℝ)
        else (eigvecOf L hL k a - eigvecOf L hL k b) ^ 2
          / eigvalOf L hL k) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => hterm_nonneg k)).1 hsum0
  have hcoord : ∀ k : V, eigvalOf L hL k ≠ 0 →
      eigvecOf L hL k a = eigvecOf L hL k b := by
    intro k hk
    have h0 := hterm0 k (Finset.mem_univ k)
    rw [if_neg hk] at h0
    have hsq : (eigvecOf L hL k a - eigvecOf L hL k b) ^ 2 = 0 :=
      ((div_eq_zero_iff.1 h0).resolve_right hk)
    exact sub_eq_zero.1 (sq_eq_zero_iff.1 hsq)
  have hexp : u a - u b
      = ∑ k : V, Matrix.dotProduct (eigvecOf L hL k) u
        * (eigvecOf L hL k a - eigvecOf L hL k b) := by
    have ea := eigvecOf_expansion_apply hL u a
    have eb := eigvecOf_expansion_apply hL u b
    rw [← ea, ← eb, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hvanish : ∀ k : V, Matrix.dotProduct (eigvecOf L hL k) u
      * (eigvecOf L hL k a - eigvecOf L hL k b) = 0 := by
    intro k
    by_cases hk : eigvalOf L hL k = 0
    · rw [ff_eigvec_dotProduct_of_eigen hL hc hu k hk, zero_mul]
    · rw [hcoord k hk]; ring
  have hzero : u a - u b = 0 := by
    rw [hexp, Finset.sum_congr rfl fun k _ => hvanish k,
      Finset.sum_const_zero]
  exact hab (sub_eq_zero.1 hzero)

/-! ### The signed rank-1 fixture `sgnK4Adj`: the `hnn` fences

The fixture is delivered (`QA.sgnK4Adj`: symmetric, connected support,
negative entries, Laplacian of rank 1 with the three-dimensional kernel
spanned by `1`, `![1,1,-1,-1]`, `![1,-1,1,-1]`). This audit adds the
second kernel generator's pin, the rank-1 mode's eigen-equation, and the
fixture-local PSD form.
-/

/-- The second kernel generator `![1,-1,1,-1]`, pinned by the same
entrywise computation as the delivered first one. -/
theorem foF_sgnK4_kernel_w2 :
    (laplacian QA.sgnK4Adj).mulVec (![1, -1, 1, -1] : Fin 4 → ℝ) = 0 := by
  funext i
  rw [laplacian_mulVec_apply]
  fin_cases i <;>
    simp [QA.sgnK4Adj, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val', Matrix.head_cons]

/-- The rank-1 mode of the signed fixture: `s = ![1,-1,-1,1]` with
`L *ᵥ s = 4 • s` — the single nonzero eigenvalue is `4`. -/
def foF_sgnMode : Fin 4 → ℝ := ![1, -1, -1, 1]

theorem foF_sgnMode_eigen :
    (laplacian QA.sgnK4Adj).mulVec foF_sgnMode = (4 : ℝ) • foF_sgnMode := by
  funext i
  rw [laplacian_mulVec_apply]
  fin_cases i <;>
    simp [QA.sgnK4Adj, foF_sgnMode, Fin.sum_univ_four, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.head_cons] <;>
    norm_num

/-- The rank-1 structure as a multiplication formula: the Laplacian
acts as `f ↦ (s ⬝ᵥ f) • s`. -/
theorem foF_sgnK4_mulVec (f : Fin 4 → ℝ) :
    (laplacian QA.sgnK4Adj).mulVec f
      = Matrix.dotProduct foF_sgnMode f • foF_sgnMode := by
  funext i
  rw [laplacian_mulVec_apply]
  fin_cases i <;>
    simp [QA.sgnK4Adj, foF_sgnMode, Matrix.dotProduct, Fin.sum_univ_four,
      Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.head_cons] <;>
    ring

/-- The fixture-local SOS identity: the signed Laplacian is PSD with
`quadForm L f = (s ⬝ᵥ f)²` — the rank-1 form. -/
theorem foF_sgnK4_quadForm_eq_sq (f : Fin 4 → ℝ) :
    quadForm (laplacian QA.sgnK4Adj) f
      = Matrix.dotProduct foF_sgnMode f ^ 2 := by
  show Matrix.dotProduct f ((laplacian QA.sgnK4Adj).mulVec f) = _
  rw [foF_sgnK4_mulVec, Matrix.dotProduct_smul, smul_eq_mul,
    Matrix.dotProduct_comm f foF_sgnMode]
  ring

/-- Every eigenvalue of the signed fixture's Laplacian is nonnegative
(the fixture-local PSD form of `laplacian_psd`, which needs nonnegative
weights the fixture does not carry). -/
theorem foF_sgnK4_eigvalOf_nonneg (k : Fin 4) :
    0 ≤ eigvalOf (laplacian QA.sgnK4Adj)
        (laplacian_symmetric QA.sgnK4Adj QA.sgnK4Adj_isSymm) k := by
  rw [← quadForm_eigvecOf_self
      (laplacian_symmetric QA.sgnK4Adj QA.sgnK4Adj_isSymm) k,
    foF_sgnK4_quadForm_eq_sq]
  exact sq_nonneg _

/-- **Fence (`card_filter_eigvalOf_laplacian_eq_zero`, `hnn`)**: at the
signed fixture (symmetric, connected support) the kernel contains the
constants and `![1,1,-1,-1]` — two nonzero non-parallel vectors — so the
zero-eigenvalue count is at least `2`, not `1`. Connectivity does not
keep the count at one once signs enter. -/
theorem foF_sgnK4F_card_filter_hnn_fence_QA :
    ¬ ((Finset.univ.filter fun k =>
        eigvalOf (laplacian QA.sgnK4Adj)
          (laplacian_symmetric QA.sgnK4Adj QA.sgnK4Adj_isSymm) k = 0).card
        = 1) := by
  intro h
  have hne1 : (onesVec (V := Fin 4)) ≠ 0 := by
    intro h0
    have e := congrFun h0 (0 : Fin 4)
    simp [onesVec] at e
  have hne2 : (![1, 1, -1, -1] : Fin 4 → ℝ) ≠ 0 := by
    intro h0
    have e := congrFun h0 (0 : Fin 4)
    simp at e
  have hnp : ¬ ∃ c : ℝ, (onesVec (V := Fin 4))
      = c • (![1, 1, -1, -1] : Fin 4 → ℝ) := by
    rintro ⟨c, hc⟩
    have e0 := congrFun hc (0 : Fin 4)
    have e2 := congrFun hc (2 : Fin 4)
    simp only [onesVec, Matrix.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val', Matrix.head_cons] at e0 e2
    norm_num at e0 e2
    linarith
  have h2 := ff_two_kernel_filter_card_ge_two
    (laplacian_symmetric QA.sgnK4Adj QA.sgnK4Adj_isSymm)
    (laplacian_ones_in_kernel QA.sgnK4Adj) QA.sgnK4_kernel
    hne1 hne2 hnp
  omega

/-- **Every off-diagonal demand is unsolvable on the signed fixture.**
A solvable demand pairs to zero against both kernel generators; the map
`x ↦ (![1,1,-1,-1] x, ![1,-1,1,-1] x)` is injective on `Fin 4`, so the
pair must be diagonal. -/
theorem foF_sgnK4_offdiag_unsolvable_QA (u v : Fin 4) (huv : u ≠ v) :
    ¬ ∃ r : ℝ, IsEffectiveResistance QA.sgnK4Adj u v r := by
  rintro ⟨r, f, hf, -⟩
  have h1 : Matrix.dotProduct (![1, 1, -1, -1] : Fin 4 → ℝ)
      ((laplacian QA.sgnK4Adj).mulVec f) = 0 :=
    dotProduct_eq_zero_of_laplacian_mulVec_eq_zero QA.sgnK4Adj
      QA.sgnK4Adj_isSymm QA.sgnK4_kernel
  rw [hf, Matrix.dotProduct_sub, Matrix.dotProduct_single,
    Matrix.dotProduct_single, mul_one, mul_one] at h1
  have h2 : Matrix.dotProduct (![1, -1, 1, -1] : Fin 4 → ℝ)
      ((laplacian QA.sgnK4Adj).mulVec f) = 0 :=
    dotProduct_eq_zero_of_laplacian_mulVec_eq_zero QA.sgnK4Adj
      QA.sgnK4Adj_isSymm foF_sgnK4_kernel_w2
  rw [hf, Matrix.dotProduct_sub, Matrix.dotProduct_single,
    Matrix.dotProduct_single, mul_one, mul_one] at h2
  fin_cases u <;> fin_cases v <;>
    simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.head_cons] <;>
    (try norm_num at h1) <;> (try norm_num at h2)

theorem foF_sgnK4_effectiveResistance_eq_zero_of_ne (u v : Fin 4)
    (huv : u ≠ v) : effectiveResistance QA.sgnK4Adj u v = 0 :=
  effectiveResistance_eq_zero_of_not_exists QA.sgnK4Adj u v
    (foF_sgnK4_offdiag_unsolvable_QA u v huv)

/-- **The Foster ordered sum at the signed fixture, computed
independently of the theorem:** every resistance in it is zero (the
diagonal unconditionally, the off-diagonal through unsolvability), so
the sum is `0` against the theorem's demanded `card V − 1 = 3`. -/
theorem foF_sgnK4_ordered_sum_zero_QA :
    ∑ i, ∑ j, QA.sgnK4Adj i j * effectiveResistance QA.sgnK4Adj i j
      = 0 := by
  refine Finset.sum_eq_zero fun i _ =>
    Finset.sum_eq_zero fun j _ => ?_
  by_cases hij : i = j
  · rw [hij, effectiveResistance_self, mul_zero]
  · rw [foF_sgnK4_effectiveResistance_eq_zero_of_ne i j hij, mul_zero]

/-- **Fence (`foster_theorem`, `hnn`)**: at the signed fixture
(symmetry and connectivity genuine) the conclusion reads `0 = 3`. -/
theorem foF_sgnK4F_foster_hnn_fence_QA :
    ¬ ((∑ i, ∑ j, QA.sgnK4Adj i j * effectiveResistance QA.sgnK4Adj i j)
        / 2 = ((Fintype.card (Fin 4) : ℝ) - 1)) := by
  intro h
  rw [foF_sgnK4_ordered_sum_zero_QA, Fintype.card_fin] at h
  norm_num at h

/-- **Fence (`effectiveResistance_eq_sum_eigbasis`, `hnn`)**: the
left-hand side is the delivered junk fallback `0`, while the right-hand
side is strictly positive — the rank-1 mode `s = ![1,-1,-1,1]` has
`s 0 − s 2 = 2 ≠ 0`, its eigenvalue `4` is nonzero, and the spectral-sum
engine applies through the fixture-local PSD form. -/
theorem foF_sgnK4F_eigbasis_hnn_fence_QA :
    ¬ (effectiveResistance QA.sgnK4Adj 0 2
      = ∑ k, (if eigvalOf (laplacian QA.sgnK4Adj)
            (laplacian_symmetric QA.sgnK4Adj QA.sgnK4Adj_isSymm) k = 0
          then (0 : ℝ)
          else (eigvecOf (laplacian QA.sgnK4Adj)
              (laplacian_symmetric QA.sgnK4Adj QA.sgnK4Adj_isSymm) k 0
              - eigvecOf (laplacian QA.sgnK4Adj)
                (laplacian_symmetric QA.sgnK4Adj QA.sgnK4Adj_isSymm) k 2) ^ 2
            / eigvalOf (laplacian QA.sgnK4Adj)
              (laplacian_symmetric QA.sgnK4Adj QA.sgnK4Adj_isSymm) k)) := by
  intro h
  rw [QA.sgnK4_fallback_zero_QA] at h
  have hpos := ff_sum_eigbasis_pos
    (laplacian_symmetric QA.sgnK4Adj QA.sgnK4Adj_isSymm)
    foF_sgnK4_eigvalOf_nonneg (c := 4) (by norm_num) foF_sgnMode_eigen
    0 2 (by norm_num [foF_sgnMode, Matrix.cons_val_zero, Matrix.cons_val',
      Matrix.head_cons])
  linarith

/-! ### The disconnected fixture `connDiscAdj`: the `hconn` fences -/

/-- Vertices `2` and `3` are reachable within the second block. -/
theorem foF_disc_reach_2_3 :
    (supportGraph QA.connDiscAdj QA.connDiscAdj_isSymm).Reachable 2 3 :=
  ⟨SimpleGraph.Walk.cons (u := 2) (v := 3) (w := 3)
    ⟨by decide, by simp [QA.connDiscAdj]⟩ SimpleGraph.Walk.nil⟩

theorem foF_disc_reach_3_2 :
    (supportGraph QA.connDiscAdj QA.connDiscAdj_isSymm).Reachable 3 2 :=
  ⟨SimpleGraph.Walk.cons (u := 3) (v := 2) (w := 2)
    ⟨by decide, by simp [QA.connDiscAdj]⟩ SimpleGraph.Walk.nil⟩

theorem foF_disc_reach_1_0 :
    (supportGraph QA.connDiscAdj QA.connDiscAdj_isSymm).Reachable 1 0 :=
  ⟨SimpleGraph.Walk.cons (u := 1) (v := 0) (w := 0)
    ⟨by decide, by simp [QA.connDiscAdj]⟩ SimpleGraph.Walk.nil⟩

/-- **The second block's resistance, pinned by its own witness. -/
theorem foF_disc_R23 : effectiveResistance QA.connDiscAdj 2 3 = 1 := by
  refine effectiveResistance_eq_of_reachable QA.connDiscAdj
    QA.connDiscAdj_isSymm QA.connDiscAdj_nonneg foF_disc_reach_2_3
    ⟨![0, 0, 1, 0], ?_, by norm_num [Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val', Matrix.head_cons]⟩
  funext i
  rw [laplacian_mulVec_apply]
  fin_cases i <;>
    simp [QA.connDiscAdj, Fin.sum_univ_four, Pi.single_apply, Pi.sub_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.head_cons]

theorem foF_disc_R32 : effectiveResistance QA.connDiscAdj 3 2 = 1 := by
  refine effectiveResistance_eq_of_reachable QA.connDiscAdj
    QA.connDiscAdj_isSymm QA.connDiscAdj_nonneg foF_disc_reach_3_2
    ⟨![0, 0, -1, 0], ?_, by norm_num [Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val', Matrix.head_cons]⟩
  funext i
  rw [laplacian_mulVec_apply]
  fin_cases i <;>
    simp [QA.connDiscAdj, Fin.sum_univ_four, Pi.single_apply, Pi.sub_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.head_cons]

theorem foF_disc_R10 : effectiveResistance QA.connDiscAdj 1 0 = 1 := by
  refine effectiveResistance_eq_of_reachable QA.connDiscAdj
    QA.connDiscAdj_isSymm QA.connDiscAdj_nonneg foF_disc_reach_1_0
    ⟨![-1, 0, 0, 0], ?_, by norm_num [Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val', Matrix.head_cons]⟩
  funext i
  rw [laplacian_mulVec_apply]
  fin_cases i <;>
    simp [QA.connDiscAdj, Fin.sum_univ_four, Pi.single_apply, Pi.sub_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.head_cons]

/-- **The Foster ordered sum at the disconnected fixture, computed
independently of the theorem:** the two within-block resistances are
genuinely `1` and every cross-block conductance weight is `0` (no junk
value even enters), so the ordered sum is `4` and the halved sum `2`
against the theorem's demanded `card V − 1 = 3`. -/
theorem foF_disc_ordered_sum_four_QA :
    ∑ i, ∑ j, QA.connDiscAdj i j * effectiveResistance QA.connDiscAdj i j
      = 4 := by
  simp only [Fin.sum_univ_four,
    QA.disc_same_component_effectiveResistance_eq_one_QA, foF_disc_R10,
    foF_disc_R23, foF_disc_R32]
  simp [QA.connDiscAdj]
  norm_num

/-- **Fence (`foster_theorem`, `hconn`)**: at the disconnected fixture
(symmetry and nonnegativity genuine) the conclusion reads `2 = 3` — each
component contributes its own `nᵢ − 1`, and the identity is off by
exactly the missing component count. -/
theorem foF_discF_foster_hconn_fence_QA :
    ¬ ((∑ i, ∑ j, QA.connDiscAdj i j * effectiveResistance QA.connDiscAdj i j)
        / 2 = ((Fintype.card (Fin 4) : ℝ) - 1)) := by
  intro h
  rw [foF_disc_ordered_sum_four_QA, Fintype.card_fin] at h
  norm_num at h

/-- **Fence (`card_filter_eigvalOf_laplacian_eq_zero`, `hconn`)**: the
kernel contains the constants and the component indicator
`![1,1,0,0]` — two nonzero non-parallel vectors — so the zero-eigenvalue
count is at least `2`, not `1`. Each component contributes its own zero
eigenvalue. -/
theorem foF_discF_card_filter_hconn_fence_QA :
    ¬ ((Finset.univ.filter fun k =>
        eigvalOf (laplacian QA.connDiscAdj)
          (laplacian_symmetric QA.connDiscAdj QA.connDiscAdj_isSymm) k = 0).card
        = 1) := by
  intro h
  have hne1 : (onesVec (V := Fin 4)) ≠ 0 := by
    intro h0
    have e := congrFun h0 (0 : Fin 4)
    simp [onesVec] at e
  have hne2 : (![1, 1, 0, 0] : Fin 4 → ℝ) ≠ 0 := by
    intro h0
    have e := congrFun h0 (0 : Fin 4)
    simp at e
  have hnp : ¬ ∃ c : ℝ, (onesVec (V := Fin 4))
      = c • (![1, 1, 0, 0] : Fin 4 → ℝ) := by
    rintro ⟨c, hc⟩
    have e2 := congrFun hc (2 : Fin 4)
    simp only [onesVec, Matrix.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val', Matrix.head_cons] at e2
    norm_num at e2
  have h2 := ff_two_kernel_filter_card_ge_two
    (laplacian_symmetric QA.connDiscAdj QA.connDiscAdj_isSymm)
    (laplacian_ones_in_kernel QA.connDiscAdj)
    QA.connDisc_indicator_in_kernel_QA hne1 hne2 hnp
  omega

/-- The block-antisymmetric mode of the disconnected fixture: a genuine
eigenvector `![1,-1,0,0]` with eigenvalue `2`. -/
theorem foF_disc_mode_eigen :
    (laplacian QA.connDiscAdj).mulVec (![1, -1, 0, 0] : Fin 4 → ℝ)
      = (2 : ℝ) • (![1, -1, 0, 0] : Fin 4 → ℝ) := by
  funext i
  rw [laplacian_mulVec_apply]
  fin_cases i <;>
    simp [QA.connDiscAdj, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.head_cons] <;>
    norm_num

/-- The disconnected fixture is nonnegative, so its Laplacian
eigenvalues are nonnegative through `laplacian_psd`. -/
theorem foF_disc_eigvalOf_nonneg (k : Fin 4) :
    0 ≤ eigvalOf (laplacian QA.connDiscAdj)
        (laplacian_symmetric QA.connDiscAdj QA.connDiscAdj_isSymm) k := by
  rw [← quadForm_eigvecOf_self
    (laplacian_symmetric QA.connDiscAdj QA.connDiscAdj_isSymm) k]
  exact laplacian_psd QA.connDiscAdj QA.connDiscAdj_isSymm
    QA.connDiscAdj_nonneg _

/-- **Fence (`effectiveResistance_eq_sum_eigbasis`, `hconn`)**: the
left-hand side is the delivered junk fallback `0` (the cross-component
demand is unsolvable), while the right-hand side is strictly positive —
the block-antisymmetric mode `![1,-1,0,0]` (eigenvalue `2`, genuine) has
`u 0 − u 2 = 1 ≠ 0`. -/
theorem foF_discF_eigbasis_hconn_fence_QA :
    ¬ (effectiveResistance QA.connDiscAdj 0 2
      = ∑ k, (if eigvalOf (laplacian QA.connDiscAdj)
            (laplacian_symmetric QA.connDiscAdj QA.connDiscAdj_isSymm) k = 0
          then (0 : ℝ)
          else (eigvecOf (laplacian QA.connDiscAdj)
              (laplacian_symmetric QA.connDiscAdj QA.connDiscAdj_isSymm) k 0
              - eigvecOf (laplacian QA.connDiscAdj)
                (laplacian_symmetric QA.connDiscAdj QA.connDiscAdj_isSymm) k 2) ^ 2
            / eigvalOf (laplacian QA.connDiscAdj)
              (laplacian_symmetric QA.connDiscAdj QA.connDiscAdj_isSymm) k)) := by
  intro h
  rw [QA.disc_fallback_zero_QA] at h
  have hpos := ff_sum_eigbasis_pos
    (laplacian_symmetric QA.connDiscAdj QA.connDiscAdj_isSymm)
    foF_disc_eigvalOf_nonneg (c := 2) (by norm_num) foF_disc_mode_eigen
    0 2 (by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.head_cons])
  linarith

/-! ### The leverage layer: the `hcard` junk corner and the two mirrors -/

/-- **Fence (`sum_leverageScore_eq_two`, `hnn`)**: the leverage sum at
the signed fixture is `0/3 = 0`, not `2`. -/
theorem foF_sgnK4F_leverage_hnn_fence_QA :
    ¬ (∑ i, ∑ j, leverageScore QA.sgnK4Adj i j = 2) := by
  intro h
  have hsplit : ∑ i, ∑ j, leverageScore QA.sgnK4Adj i j
      = (∑ i, ∑ j, QA.sgnK4Adj i j
          * effectiveResistance QA.sgnK4Adj i j)
        / (((Fintype.card (Fin 4) : ℝ) - 1)) := by
    simp only [leverageScore, Finset.sum_div, Fintype.card_fin]
  rw [hsplit, foF_sgnK4_ordered_sum_zero_QA, Fintype.card_fin] at h
  norm_num at h

/-- **Fence (`sum_leverageScore_eq_two`, `hconn`)**: the leverage sum at
the disconnected fixture is `4/3`, not `2`. -/
theorem foF_discF_leverage_hconn_fence_QA :
    ¬ (∑ i, ∑ j, leverageScore QA.connDiscAdj i j = 2) := by
  intro h
  have hsplit : ∑ i, ∑ j, leverageScore QA.connDiscAdj i j
      = (∑ i, ∑ j, QA.connDiscAdj i j
          * effectiveResistance QA.connDiscAdj i j)
        / (((Fintype.card (Fin 4) : ℝ) - 1)) := by
    simp only [leverageScore, Finset.sum_div, Fintype.card_fin]
  rw [hsplit, foF_disc_ordered_sum_four_QA, Fintype.card_fin] at h
  norm_num at h

/-- The one-vertex fixture: the zero matrix on `Fin 1` (symmetric,
nonnegative, connected — a single vertex reaches itself). -/
def foF_oneAdj : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => 0

theorem foF_oneAdj_isSymm : foF_oneAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i
  fin_cases j
  simp [foF_oneAdj]

theorem foF_oneAdj_nonneg : ∀ i j, 0 ≤ foF_oneAdj i j := by
  intro i j
  fin_cases i
  fin_cases j
  simp [foF_oneAdj]

theorem foF_one_connected :
    (supportGraph foF_oneAdj foF_oneAdj_isSymm).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩

/-- **The junk `0/0` corner of the leverage object, pinned:** at
`card V = 1` the division guard is literally division by zero, and the
score reads `0` — the value the docstring warns must not be read as a
probability. -/
theorem foF_one_leverage_junk_zero_QA :
    leverageScore foF_oneAdj 0 0 = 0 := by
  simp only [leverageScore, effectiveResistance_self, Fintype.card_fin,
    foF_oneAdj, Matrix.of_apply]
  norm_num

/-- **Fence (`sum_leverageScore_eq_two`, `hcard`)**: at the one-vertex
fixture (symmetry, nonnegativity, and connectivity all genuine) the
cardinality hypothesis fails at `2 ≤ 1` and the conclusion reads
`0 = 2` — the division guard's junk corner. -/
theorem foF_oneF_leverage_hcard_fence_QA :
    ¬ (∑ i, ∑ j, leverageScore foF_oneAdj i j = 2) := by
  intro h
  rw [Fin.sum_univ_one, Fin.sum_univ_one, foF_one_leverage_junk_zero_QA] at h
  norm_num at h

/-! ### Isolation companions -/

/-- **Isolation (`hnn` fences at the signed fixture):** every hypothesis
except nonnegativity is genuine — symmetric, connected support — and the
dropped hypothesis fails. -/
theorem foF_sgnK4_isolation_QA :
    QA.sgnK4Adj.IsSymm ∧ (supportGraph QA.sgnK4Adj QA.sgnK4Adj_isSymm).Connected
      ∧ ¬ (∀ i j : Fin 4, 0 ≤ QA.sgnK4Adj i j) :=
  QA.sgnK4_fence_isolation_QA

/-- **Isolation (`hconn` fences at the disconnected fixture):** every
hypothesis except connectivity is genuine — symmetric, nonnegative —
and the support graph is not connected. -/
theorem foF_disc_isolation_QA :
    QA.connDiscAdj.IsSymm ∧ (∀ i j : Fin 4, 0 ≤ QA.connDiscAdj i j)
      ∧ ¬ (supportGraph QA.connDiscAdj QA.connDiscAdj_isSymm).Connected :=
  ⟨QA.connDiscAdj_isSymm, QA.connDiscAdj_nonneg, QA.connDisc_not_connected_QA⟩

/-- **Isolation (`hcard` fence at the one-vertex fixture):** every
hypothesis except the cardinality bound is genuine — symmetric,
nonnegative, connected — and `2 ≤ card V` fails at `card V = 1`. -/
theorem foF_one_isolation_QA :
    foF_oneAdj.IsSymm ∧ (∀ i j : Fin 1, 0 ≤ foF_oneAdj i j)
      ∧ (supportGraph foF_oneAdj foF_oneAdj_isSymm).Connected
      ∧ ¬ (2 ≤ Fintype.card (Fin 1)) :=
  ⟨foF_oneAdj_isSymm, foF_oneAdj_nonneg, foF_one_connected, by decide⟩

end SpectralGraphTheory
