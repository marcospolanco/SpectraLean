/-
Copyright 2024 Scaffold Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Scaffold.Mathlib.GraphTheory.Spectral
import Scaffold.Mathlib.GraphTheory.Cheeger
import Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Alon–Boppana, Steps 1–5 (program complete): the d-regularity
# interface, the tree-ball, the radial test vector, its energy, the
# two-vector orthogonalization, and the diameter-dependent statement

The home module of the Alon–Boppana program
(`proposals/alon-boppana-bound.md`, adopted 2026-08-26): the lower
companion to the delivered Cheeger/expander toolkit — "how small can
the spectral gap of a d-regular graph possibly be" — via Nilli's
two-edge variational method (Route A), whose linear-algebra engine is
the proved `secondEval_variational`. The program's capstone is
`alonBoppana_nilli` (Step 5): the second eigenvalue of the d-regular
Laplacian `d • 1 − A` is at most `d − (1 + 2k√(d−1))/(k+1)` whenever
two far-apart edges carry full BFS tree balls at radius `k + 1`, with
the classical error shape `alonBoppana_nilli_classical` and the
diameter bookkeeping `alonBoppana_diam_ge` (`k + 1 ≤ ⌊diam/2⌋`, the
honest hypothesis-side reading of `O(1/⌊diam/2⌋)` — the tree-ball
hypothesis is never derived from the diameter).

**The expansion ceiling** (delivered 2026-08-27,
`proposals/ramanujan-expansion-ceiling.md`): the program's first
theorem consumer — `ramanujan_expansion_ceiling` composes
`alonBoppana_nilli_classical` with `Cheeger.lean`'s proved
`cheeger_lower_bound` through the new engine pieces
`secondEval_smul_of_pos` (exact positive scaling, `Spectral.lean`)
and the operator identity `smul_one_sub_eq_smul_regularNormalizedLapla
cian` (`d • 1 − A = d • L_sym` under regularity), yielding the
textbook ceiling `cheegerConstant A ≤ √(2 (1 − 2√(d−1)/d +
2√(d−1)/(d (k+1))))`. Obstruction scope only: the statement bounds how
good an expander any graph satisfying the hypotheses can be; it says
nothing about the ceiling being tight or attained (that is the
separate Ramanujan-graph construction program).

**Step 1** (delivered 2026-08-26): the d-regularity interface in
Scaffold's own idiom, reusing `Cheeger.lean`'s `d : ℝ` hypothesis
pattern rather than importing Mathlib's `ℕ`-valued
`IsRegularOfDegree` into the real-valued center:

* `IsDRegular A d` — every row sum (degree) equals `d`.
* `adjacency_mulVec_onesVec` — the constant vector is an eigenvector
  of the adjacency matrix with eigenvalue `d`, hypothesis-free beyond
  regularity (a row-sum computation).
* `quadForm_le_of_isDRegular` — **AM–GM row-sum domination**
  `xᵀAx ≤ d · (x ⬝ᵥ x)`: per entry `a i j x i x j ≤ a i j (x i² +
  x j²)/2` by AM–GM, and the two halves of the symmetric double sum
  are both `d · ‖x‖²` — the row-sum identity for one half, the
  column-sum identity (symmetry + regularity) for the other.
  Nonnegativity of the weights is load-bearing: it is what lets the
  entrywise AM–GM bound be multiplied through by `a i j`.
* `evals_last_eq_of_isDRegular` — **the top adjacency eigenvalue of a
  d-regular graph is `d`**, from both sides: `d` is an eigenvalue
  (the `onesVec` witness through
  `exists_eigvalOf_eq_of_mulVec_eq_smul`, then
  `eigvalOf_le_evals_last`), and every eigenvalue is dominated by `d`
  (AM–GM domination at the unit eigenvector, then
  `evals_mem_eigvalOf`). A wrong `evals`/`eigvalOf`/`deg` shape breaks
  one of the two halves — the identification is load-bearing on the
  sorted-spectrum API at its extremes.

**Step 2** (this delivery): the tree-ball interface at module level,
per the Step-0 spike's verdict — the BFS level machinery of Nilli's
two-edge method, stated as cardinality equations against
`SimpleGraph.dist` on `supportGraph` rather than any structural
tree-ness predicate:

* `levE`/`levClass`/`ballE` — the level of a vertex from an edge
  (distance to the nearer endpoint), the level classes, and the
  closed balls (the support of the Step-3 test vector).
* `levE_eq_zero_iff` — the junk-zero-honest level-0 form (the `dist`
  trap stated, not hidden); `levE_eq_zero_iff_of_connected` — the
  amortized clean form; `levClass_zero_eq`/`levClass_zero_card` —
  level 0 is exactly the endpoint pair (the `j = 0` cardinality
  equation free of regularity).
* `IsTreeBall` — **the tree-ball predicate**: level `j` carries
  exactly `2 (d−1)^j` vertices for every `j < k`, the count the
  infinite d-regular tree around an edge would have — the working
  hypothesis Nilli's Rayleigh computation actually consumes.
* `ballE_mem_iff`, `ballE_zero`, `ballE_mono`,
  `levClass_pairwise_disjoint`, `ballE_succ_union`,
  `ballE_card_eq_sum` — the ball algebra and the **layer-cake
  cardinality bridge** (ball card = geometric level sum), the
  normalization input the Step-3 test vector's squared norm consumes.
* `distEdge` + `ballE_disjoint_of_lt_distEdge` — the far-apart
  condition and its disjointness theorem (the connected triangle
  inequality at all four endpoint pairings) — the load-bearing
  separation input of Step 4's orthogonalization.

**Step 3, first slice** (this delivery — the proposal prices Step 3 for
sub-decomposition across runs; this is the vector + normalization
half):

* `radialVec` — the radial test vector: on the radius-`k` edge ball,
  the value `ρ ^ levE z` (constant per BFS level, `0` outside), with
  the d-regular-tree normalization carried as the consumer hypothesis
  `ρ ^ 2 = ((d − 1 : ℕ) : ℝ)⁻¹` so the `√` plumbing stays in the
  eventual packaging.
* `radialVec_apply`/`radialVec_of_mem_ballE`/
  `radialVec_eq_zero_of_not_mem_ballE`/`radialVec_left`/
  `radialVec_ne_zero` — the entry, support, and nonvanishing
  interface (the value at the left endpoint is always `1`).
* `sum_ballE_eq_sum_levels` — the **layer-cake sum bridge** (any
  function summed over the ball equals its level-by-level sum), the
  summation form of `ballE_card_eq_sum`.
* `radialVec_dotProduct_self` — **the squared-norm identity**
  `⟨ρ^{lev}, ρ^{lev}⟩ = 2 (k + 1)` under `IsTreeBall` at radius `k+1`:
  the geometric growth of full levels cancels the geometric decay of
  the vector, per level, to exactly `2`. This is the denominator of
  Nilli's Rayleigh quotient, computed exactly — the first theorem
  consumer of the Step-2 level machinery. `1 < d` is load-bearing at
  the cancellation (`mul_inv_cancel₀`); at `d = 1` the identity
  genuinely fails (QA fences it at K₂).

**Step 3, second slice — the energy half** (this delivery): the
numerator of Nilli's Rayleigh quotient, counted from below:

* `levE_le_levE_add_one_of_adj` — **the BFS level function is
  1-Lipschitz along support-graph edges** (both endpoint distances
  move by at most one along an edge; the junk-safe adjacency triangle
  that powers everything below).
* `exists_levE_parent` — **the parent lemma**: every vertex at level
  `≥ 1` has a support-adjacent neighbor exactly one level down, no
  connectivity hypothesis needed. This is the Step-3b spike's answer
  to the recorded hard piece — the cardinality equations give level
  *sizes*, not edge counts, so the numerator is harvested **from
  below**, one parent edge per interior vertex.
* `interiorE` + `interiorE_zero`/`interiorE_succ_union`/
  `sum_interiorE_eq_sum_levels` — the interior (levels `1..k`) and
  its level-sum bridge, the `sum_ballE_eq_sum_levels` pattern at the
  parent-carrying part of the ball.
* `radialVec_quadForm_ge` — **the numerator bound**
  `2 + 4 k (d−1) ρ ≤ xᵀAx`: the edge itself in both orders (≥ 2),
  every level-`j` vertex's parent edge in both orders, each level's
  geometric growth cancelling the vector's decay to exactly
  `2 (d−1) ρ` per level — under the *existing* `IsTreeBall` plus a
  `0`-or-`≥ 1` weight discipline (each parent edge weighs at least
  `1`), distinct endpoints, and a genuine edge. No strengthening of
  the tree-ball predicate.
* `radialVec_rayleigh_ge` — the Rayleigh-quotient corollary joining
  the numerator bound to the delivered denominator identity: Nilli's
  `(1 + 2 k √(d−1)) / (k + 1)` before the Step-5 `√` packaging — the
  interface Step 4's orthogonalization consumes.

Steps 4–5 (the two-vector orthogonalization and the
diameter-dependent single-graph statement) are future steps per the
proposal's one-step-per-run instruction. The
`Mathlib.Combinatorics.SimpleGraph.Metric` import is the Step-0
verdict's explicit-import requirement (`Spectral.lean`'s transitive
imports do not reach `SimpleGraph.dist`).

Everything in this module is proved; no axiom is admitted. The
eventual theorem's statement must respect the proposal's
qualification trap: the honest single-graph form is
diameter-dependent (`λ₂ ≥ 2√(d−1) − O(1/k)` at two edges whose
radius-`k` balls are tree-like and far apart), never an unqualified
`λ₂ ≥ 2√(d−1)`.

Classical background (route provenance only): N. Alon, Eigenvalues and
expanders, Combinatorica 6 (1986) 83–96; A. Nilli, On the second
eigenvalue of a graph, Discrete Math. 91 (1991) 207–210; Hoory,
Linial & Wigderson, Expander graphs and their applications, Bull. AMS
43 (2006) §5.

QA: `Scaffold/QA/SpectralGraph/AlonBoppana_QA.lean` — Step 1: the C₄
and K₂ instances at raw entrywise pins, the P₃ non-regularity fence,
and the nonnegativity fence at the signed 0-regular
`!![1, -1; -1, 1]]`. Step 2: the C₈ full-hypothesis positive (the
tree-ball instance at the antipodal edge, the disjoint antipodal
balls, the layer-cake cardinality by two independent routes), the C₄
wrap-around negative (`IsTreeBall` fails at radius 3 — level 2
demanded nonempty and empty), and the threshold-tightness fence (the
near-antipodal balls at min cross-distance exactly `r + s` provably
intersect). Step 3: the C₈ squared-norm pin `4 = 2 (k+1)` by two
independent routes (the identity through `abC8_isTreeBall` vs raw
per-vertex enumeration through the level-0/level-1 memberships), the
`k = 0` pair (the theorem at `isTreeBall_one_of_connected` vs raw),
and the K₂ `d = 1` degeneracy fence (every input but `1 < d` holds at
`ρ = 0` — junk-admissible through `0⁻¹ = 0` — and the identity fails
at `2 ≠ 4`). Step 3b: the C₈ numerator pin **tight at equality** (the
raw enumeration `6` against the theorem's `2 + 4·1·1·1 = 6`), the
`k = 0` pair both routes, the Rayleigh-quotient instance, and three
hypothesis fences — the P₃ pseudo-edge (`hedge` isolated: the
indicator of `{0, 2}` spans no edge, numerator `0 < 2`), the
half-weight edge (`h01` isolated: numerator `1 < 2`), and the
one-vertex loop with unreachable partner (`hxy` isolated: the junk-zero
vertex fills the level-0 cardinality equation, `IsTreeBall` genuinely
holds, numerator `1 < 2`).

**Step 4** (this delivery): the two-vector orthogonalization and the
Courant–Fischer application — the program's first eigenvalue-level
statement:

* `radialVec_sum_eq` — **the equal-mass lemma**: under `IsTreeBall`,
  the radial vector's total mass is the same function of `(d, ρ, k)`
  for every edge — the level equations again, at odd powers.
* `twoEdgeVec` — Nilli's difference vector `radialVec(x, y) −
  radialVec(u, v)`, orthogonal to `onesVec` by the equal-mass lemma
  (`twoEdgeVec_dotProduct_onesVec`), of squared norm `4 (k+1)` on
  disjoint radius-`k` balls (`twoEdgeVec_dotProduct_self`), with
  cross-support and cross-edge dot products vanishing
  (`radialVec_dotProduct_eq_zero_of_disjoint`,
  `radialVec_cross_dotProduct_eq_zero` — the latter through 3b's own
  level-Lipschitz lemma, `levE_cross_adj_eq_zero`).
* `twoEdgeVec_quadForm_ge` / `twoEdgeVec_rayleigh_ge` — the doubled
  numerator bound `2·(2 + 4k(d−1)ρ)` via the expansion `quadForm_sub`
  (cross terms eliminated), and its Rayleigh-quotient form.
* `twoEdgeVec_secondEval_le` — **the headline**: at `M = d•1 − A`
  (PSD and kernel from the Step-1 regularity facts —
  `quadForm_smul_one_sub`, `smul_one_sub_mulVec_onesVec`,
  `smul_one_sub_isSymm`), `secondEval M ≤ d − (2 + 4k(d−1)ρ)/(2(k+1))`
  through `secondEval_le_rayleigh` — Nilli's quotient installed as an
  eigenvalue bound, the interface Step 5's diameter packaging consumes.

-/

open scoped BigOperators Matrix

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## The d-regularity interface
-/

/-- `d`-regularity as a per-graph hypothesis in the shelf's `d : ℝ`
idiom (the `Cheeger.lean` `regularNormalizedLaplacian A d` pattern):
every row sum of the weighted adjacency matrix equals `d`. Regularity
is a hypothesis of the theorems, not a derived quantity — no new
regularity machinery. -/
def IsDRegular (A : WAdj (V := V)) (d : ℝ) : Prop :=
  ∀ i, deg A i = d

omit [DecidableEq V] in
/-- The constant vector is an eigenvector of a `d`-regular adjacency
matrix, with eigenvalue `d`: a row-sum computation, hypothesis-free
beyond regularity (no symmetry, no nonnegativity). -/
theorem adjacency_mulVec_onesVec {A : WAdj (V := V)} {d : ℝ}
    (hd : IsDRegular A d) :
    A *ᵥ onesVec = d • onesVec := by
  funext i
  simp only [Matrix.mulVec, Matrix.dotProduct, onesVec, mul_one,
    Pi.smul_apply, smul_eq_mul]
  exact hd i

omit [DecidableEq V] in
/-- **AM–GM row-sum domination.** On a symmetric nonnegative
`d`-regular graph, `xᵀAx ≤ d · (x ⬝ᵥ x)` for every `x`. The entrywise
step is AM–GM (`x i * x j ≤ (x i² + x j²)/2`) multiplied through by
the nonnegative `a i j`; the double-sum halves are `d · ‖x‖²` twice —
the row-sum identity for one, the column-sum identity (symmetry
reindexing + regularity) for the other. -/
theorem quadForm_le_of_isDRegular {A : WAdj (V := V)} {d : ℝ}
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : IsDRegular A d)
    (x : V → ℝ) :
    quadForm A x ≤ d * Matrix.dotProduct x x := by
  have ham : ∀ i j, A i j * (x i * x j)
      ≤ A i j * ((x i ^ 2 + x j ^ 2) / 2) := by
    intro i j
    have hexp : (x i - x j) ^ 2 = x i ^ 2 - 2 * x i * x j + x j ^ 2 := by
      ring
    have key : x i * x j ≤ (x i ^ 2 + x j ^ 2) / 2 := by
      linarith [sq_nonneg (x i - x j)]
    exact mul_le_mul_of_nonneg_left key (hnn i j)
  have hsumcol : ∀ j, ∑ i, A i j = d := by
    intro j
    have h1 : ∑ i, A i j = ∑ i, A j i :=
      Finset.sum_congr rfl fun i _ => (hA.apply i j).symm
    rw [h1]
    exact hd j
  have key1 : ∑ i, ∑ j, A i j * x i ^ 2 = d * Matrix.dotProduct x x := by
    have hstep : ∀ i, ∑ j, A i j * x i ^ 2 = deg A i * x i ^ 2 := by
      intro i
      simp only [deg]
      rw [Finset.sum_mul]
    calc ∑ i, ∑ j, A i j * x i ^ 2 = ∑ i, deg A i * x i ^ 2 :=
          Finset.sum_congr rfl fun i _ => hstep i
      _ = ∑ i, d * x i ^ 2 := Finset.sum_congr rfl fun i _ => by rw [hd i]
      _ = d * Matrix.dotProduct x x := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun i _ => pow_two (x i)
  have key2 : ∑ i, ∑ j, A i j * x j ^ 2 = d * Matrix.dotProduct x x := by
    calc ∑ i, ∑ j, A i j * x j ^ 2 = ∑ j, ∑ i, A i j * x j ^ 2 :=
          Finset.sum_comm
      _ = ∑ j, d * x j ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_mul, ← hsumcol j]
      _ = d * Matrix.dotProduct x x := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun i _ => pow_two (x i)
  calc quadForm A x = ∑ i, ∑ j, A i j * (x i * x j) := by
        simp only [quadForm, Matrix.mulVec, Matrix.dotProduct,
          Finset.mul_sum, mul_assoc]
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ i, ∑ j, A i j * ((x i ^ 2 + x j ^ 2) / 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ham i j
    _ = (∑ i, ∑ j, A i j * x i ^ 2 + ∑ i, ∑ j, A i j * x j ^ 2) / 2 := by
        have e1 : ∀ i j, A i j * ((x i ^ 2 + x j ^ 2) / 2)
            = (A i j * x i ^ 2 + A i j * x j ^ 2) / 2 := by
          intro i j; ring
        have ein : ∀ i, ∑ j, (A i j * x i ^ 2 + A i j * x j ^ 2) / 2
            = (∑ j, A i j * x i ^ 2 + ∑ j, A i j * x j ^ 2) / 2 := by
          intro i
          rw [← Finset.sum_div, ← Finset.sum_add_distrib]
        rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
          e1 i j))]
        rw [Finset.sum_congr rfl (fun i _ => ein i), ← Finset.sum_div]
        rw [← Finset.sum_add_distrib]
    _ = (d * Matrix.dotProduct x x + d * Matrix.dotProduct x x) / 2 := by
        rw [key1, key2]
    _ = d * Matrix.dotProduct x x := by ring

/-- **The top adjacency eigenvalue of a `d`-regular graph is `d`.**
Both directions are load-bearing on the spectrum API: `d` is an
eigenvalue — witnessed at `onesVec` through
`exists_eigvalOf_eq_of_mulVec_eq_smul` and then bounded above by the
last sorted entry via `eigvalOf_le_evals_last` — and every eigenvalue
is at most `d` — the AM–GM domination `quadForm_le_of_isDRegular` at
the unit eigenvector whose quadratic form is its eigenvalue
(`quadForm_eigvecOf_self`), transferred to the sorted spectrum via
`evals_mem_eigvalOf`. The cardinality hypothesis supplies the last
index; `1 ≤ card V` also makes `onesVec` nonzero. -/
theorem evals_last_eq_of_isDRegular {A : WAdj (V := V)} {d : ℝ}
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : IsDRegular A d)
    (hcard : 1 ≤ Fintype.card V) :
    evals hA ⟨Fintype.card V - 1, by omega⟩ = d := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi⟩ := evals_mem_eigvalOf hA ⟨Fintype.card V - 1, by omega⟩
    rw [hi, ← quadForm_eigvecOf_self hA i]
    have hun : Matrix.dotProduct (eigvecOf A hA i) (eigvecOf A hA i) = 1 := by
      simpa [Matrix.dotProduct] using eigvecOf_inner A hA i i
    have hdom := quadForm_le_of_isDRegular hA hnn hd (eigvecOf A hA i)
    rw [hun] at hdom
    simpa using hdom
  · have hne : onesVec ≠ (0 : V → ℝ) := by
      obtain ⟨i₀⟩ : Nonempty V :=
        Fintype.card_pos_iff.1 (by omega : 0 < Fintype.card V)
      intro h
      have h1 := congrFun h i₀
      simp [onesVec] at h1
    obtain ⟨i, hi⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul hA hne
      (adjacency_mulVec_onesVec hd)
    exact hi ▸ eigvalOf_le_evals_last hA hcard i

/-!
## Step 2: the tree-ball interface
-/

section TreeBall

/-- BFS level of `z` from the edge with endpoints `x`, `y`: the graph
distance to the nearer endpoint, in the support graph of `A`. This is
the Step-0 verdict's working primitive — everything Nilli's
computation needs of "the ball around the edge `(x, y)` is a tree" is
carried by the level function's cardinality behavior, not by any
structural tree-ness. -/
noncomputable def levE (A : WAdj (V := V)) (hA : A.IsSymm) (x y z : V) : ℕ :=
  min ((supportGraph A hA).dist z x) ((supportGraph A hA).dist z y)

/-- The level-`j` vertex class of the edge `(x, y)`: the vertices at
BFS level exactly `j`. The cardinality equations
`(levClass A hA x y j).card = 2 * (d - 1) ^ j` are the working form of
"the radius-`r` ball around `(x, y)` is a full BFS tree". -/
noncomputable def levClass (A : WAdj (V := V)) (hA : A.IsSymm)
    (x y : V) (j : ℕ) : Finset V :=
  Finset.univ.filter fun z => levE A hA x y z = j

/-- The closed radius-`r` ball around the edge `(x, y)` — the support
of Nilli's test vector (Step 3); two balls being disjoint is the
far-apart condition (see `distEdge`). -/
noncomputable def ballE (A : WAdj (V := V)) (hA : A.IsSymm)
    (x y : V) (r : ℕ) : Finset V :=
  Finset.univ.filter fun z => levE A hA x y z ≤ r

variable {A : WAdj (V := V)} {hA : A.IsSymm}

omit [Fintype V] [DecidableEq V] in
/-- Endpoint symmetry of the level function. -/
theorem levE_comm (x y z : V) :
    levE A hA x y z = levE A hA y x z := by
  simp only [levE, min_comm]

omit [Fintype V] [DecidableEq V] in
/-- The junk-zero-honest form of level 0: `levE z = 0` collects the two
endpoints *and* every vertex unreachable from either endpoint — the
`SimpleGraph.dist` junk-zero trap of the Step-0 verdict, stated so no
consumer can stumble into it silently. On connected input (the
`..._of_connected` form below) it collapses to the two endpoints. -/
theorem levE_eq_zero_iff (x y z : V) :
    levE A hA x y z = 0 ↔
      (z = x ∨ ¬(supportGraph A hA).Reachable z x) ∨
      (z = y ∨ ¬(supportGraph A hA).Reachable z y) := by
  constructor
  · intro h
    rcases (show (supportGraph A hA).dist z x = 0 ∨
        (supportGraph A hA).dist z y = 0 by
          simp only [levE] at h; omega) with h0 | h0
    · exact Or.inl (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 h0)
    · exact Or.inr (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 h0)
  · rintro ((rfl | h) | (rfl | h))
    · simp [levE]
    · simp only [levE]
      have := SimpleGraph.dist_eq_zero_of_not_reachable h
      omega
    · simp [levE]
    · simp only [levE]
      have := SimpleGraph.dist_eq_zero_of_not_reachable h
      omega

omit [Fintype V] [DecidableEq V] in
/-- **Level 0 on connected input** — the amortization the Step-0 spike
priced: one connectivity hypothesis discharges every reachability
refutation, and level 0 is exactly the two (distinct) endpoints. -/
theorem levE_eq_zero_iff_of_connected
    (hconn : (supportGraph A hA).Connected) (hxy : x ≠ y) (z : V) :
    levE A hA x y z = 0 ↔ z = x ∨ z = y := by
  rw [levE_eq_zero_iff]
  constructor
  · rintro ((rfl | h) | (rfl | h))
    · exact Or.inl rfl
    · exact absurd (hconn z x) h
    · exact Or.inr rfl
    · exact absurd (hconn z y) h
  · rintro (rfl | rfl)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)

/-- Level-0 class on connected input is exactly the endpoint pair. -/
theorem levClass_zero_eq
    (hconn : (supportGraph A hA).Connected) (hxy : x ≠ y) :
    levClass A hA x y 0 = insert x (insert y (∅ : Finset V)) := by
  ext z
  simp only [levClass, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [levE_eq_zero_iff_of_connected hconn hxy]
  simp [Finset.mem_insert]

/-- The level-0 cardinality `2 (d−1)⁰ = 2` — the `j = 0` instance of
the tree-ball equations holds on every connected graph at distinct
endpoints, independent of regularity. -/
theorem levClass_zero_card
    (hconn : (supportGraph A hA).Connected) (hxy : x ≠ y) :
    (levClass A hA x y 0).card = 2 := by
  rw [levClass_zero_eq hconn hxy,
    Finset.card_insert_of_not_mem (by simp [Finset.mem_insert, hxy]),
    Finset.card_insert_of_not_mem (Finset.not_mem_empty y)]
  simp

/-- **The tree-ball predicate** (the Step-0 verdict's working form):
the BFS levels of the edge `(x, y)` are *full* up to radius `k` —
level `j` carries exactly `2 (d−1)^j` vertices for every `j < k`, the
count the infinite `d`-regular tree around an edge would have. This
cardinality-equation form is what Nilli's Rayleigh computation actually
consumes; stating tree-ness any more structurally (acyclicity, walk
uniqueness) buys nothing for the computation and costs far more to
discharge. The `d : ℕ` base uses truncated subtraction (`(1 - 1)^j = 0`
for `j ≥ 1` — the perfect-matching case); the join to `IsDRegular`'s
`d : ℝ` idiom is the Step-3–5 packaging. -/
def IsTreeBall (A : WAdj (V := V)) (hA : A.IsSymm) (x y : V) (d k : ℕ) : Prop :=
  ∀ j, j < k → (levClass A hA x y j).card = 2 * (d - 1) ^ j

/-- Level 0 is free: on connected input at distinct endpoints, the
one-level tree-ball predicate holds at every `d`. -/
theorem isTreeBall_one_of_connected
    (hconn : (supportGraph A hA).Connected) (hxy : x ≠ y) (d : ℕ) :
    IsTreeBall A hA x y d 1 := by
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  rw [levClass_zero_card hconn hxy]
  norm_num

omit [DecidableEq V] in
/-- Ball membership unpacked: `z` is in the radius-`r` edge ball
exactly when it is within `r` of either endpoint. -/
theorem ballE_mem_iff {x y z : V} {r : ℕ} :
    z ∈ ballE A hA x y r ↔
      (supportGraph A hA).dist z x ≤ r ∨ (supportGraph A hA).dist z y ≤ r := by
  simp only [ballE, levE, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

omit [DecidableEq V] in
/-- The radius-0 ball is the level-0 class. -/
theorem ballE_zero (x y : V) :
    ballE A hA x y 0 = levClass A hA x y 0 := by
  ext z
  simp only [ballE, levClass, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

omit [DecidableEq V] in
/-- Balls are monotone in the radius. -/
theorem ballE_mono (x y : V) {r s : ℕ} (h : r ≤ s) :
    ballE A hA x y r ⊆ ballE A hA x y s := by
  intro z hz
  simp only [ballE, Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hz.2.trans h⟩

omit [DecidableEq V] in
/-- Level classes are pairwise disjoint: a vertex has exactly one BFS
level. -/
theorem levClass_pairwise_disjoint (x y : V) :
    Pairwise (Disjoint on levClass A hA x y) := by
  intro i j hne
  refine Finset.disjoint_right.mpr fun a ha => ?_
  simp only [levClass, Finset.mem_filter] at ha
  intro hb
  simp only [levClass, Finset.mem_filter] at hb
  have h1 := ha.2
  have h2 := hb.2
  omega

/-- The layer-cake decomposition of the ball: radius `r + 1` is radius
`r` together with the new level `r + 1`. -/
theorem ballE_succ_union (x y : V) (r : ℕ) :
    ballE A hA x y (r + 1) = ballE A hA x y r ∪ levClass A hA x y (r + 1) := by
  ext z
  simp only [ballE, levClass, Finset.mem_filter, Finset.mem_union,
    Finset.mem_univ, true_and]
  omega

/-- **The layer-cake cardinality bridge**: under the full-level
hypothesis, the ball of radius `k` has exactly the geometric level sum
`∑_{j ≤ k} 2 (d−1)^j` — the normalization input the Step-3 test
vector's squared norm consumes (its mass is a level-weighted sum). The
`(k + 1)` form keeps `k` junk-free (at `k = 0` the statement would
conflate `ballE 0` with an empty sum). -/
theorem ballE_card_eq_sum {d : ℕ} {k : ℕ} {x y : V}
    (htb : IsTreeBall A hA x y d (k + 1)) :
    (ballE A hA x y k).card = ∑ j ∈ Finset.range (k + 1), 2 * (d - 1) ^ j := by
  induction k with
  | zero =>
      have h0 := htb 0 (by omega)
      rw [ballE_zero, h0]
      simp [Finset.range_one]
  | succ k ih =>
      have htb' : IsTreeBall A hA x y d (k + 1) := fun j hj => htb j (by omega)
      have hstep := htb (k + 1) (by omega)
      have hdis : Disjoint (ballE A hA x y k) (levClass A hA x y (k + 1)) :=
        Finset.disjoint_right.mpr fun a ha => by
          simp only [levClass, Finset.mem_filter] at ha
          intro hb
          simp only [ballE, Finset.mem_filter] at hb
          have h1 := ha.2
          have h2 := hb.2
          omega
      rw [Finset.range_succ, Finset.sum_insert (by simp), ballE_succ_union,
        Finset.card_union_of_disjoint hdis, ih htb', hstep]
      omega

/-- **Edge distance**: the least graph distance between an endpoint of
`(x, y)` and an endpoint of `(u, v)` — the standard far-apart quantity
of the two-edge method ("two edges at distance `≥ 2k − 1`"). -/
noncomputable def distEdge (A : WAdj (V := V)) (hA : A.IsSymm) (x y u v : V) : ℕ :=
  min (min ((supportGraph A hA).dist x u) ((supportGraph A hA).dist x v))
      (min ((supportGraph A hA).dist y u) ((supportGraph A hA).dist y v))

/-- **The far-apart condition implies ball disjointness**: if every
cross-endpoint distance exceeds `r + s`, the radius-`r` ball of
`(x, y)` and the radius-`s` ball of `(u, v)` are disjoint. The proof
is the connected triangle inequality at all four endpoint pairings — a
shared vertex would sit within `r` of one endpoint and within `s` of
another, bounding the corresponding cross distance by `r + s`. This is
the load-bearing separation input of Step 4's orthogonalization (the
two test vectors must have disjoint support). -/
theorem ballE_disjoint_of_lt_distEdge (x y u v : V) (r s : ℕ)
    (hconn : (supportGraph A hA).Connected)
    (h : r + s < distEdge A hA x y u v) :
    Disjoint (ballE A hA x y r) (ballE A hA u v s) := by
  simp only [distEdge] at h
  have hxu : r + s < (supportGraph A hA).dist x u := by omega
  have hxv : r + s < (supportGraph A hA).dist x v := by omega
  have hyu : r + s < (supportGraph A hA).dist y u := by omega
  have hyv : r + s < (supportGraph A hA).dist y v := by omega
  by_contra hdis
  obtain ⟨z, hz1, hz2⟩ := Finset.not_disjoint_iff.1 hdis
  rw [ballE_mem_iff] at hz1 hz2
  rcases hz1 with hx | hy
  · rw [SimpleGraph.dist_comm] at hx
    rcases hz2 with hu | hv
    · have htri := hconn.dist_triangle (u := x) (v := z) (w := u)
      omega
    · have htri := hconn.dist_triangle (u := x) (v := z) (w := v)
      omega
  · rw [SimpleGraph.dist_comm] at hy
    rcases hz2 with hu | hv
    · have htri := hconn.dist_triangle (u := y) (v := z) (w := u)
      omega
    · have htri := hconn.dist_triangle (u := y) (v := z) (w := v)
      omega

end TreeBall

/-!
## Step 3: the radial test vector and its normalization
-/

section RadialVector

variable {A : WAdj (V := V)} {hA : A.IsSymm}

/-- The radial test vector of Nilli's two-edge method (Step 3): on the
radius-`k` ball of the edge `(x, y)`, the value `ρ ^ levE z` — constant
per BFS level, decaying by the factor `ρ` per level — and `0` outside
the ball. At the d-regular-tree normalization
`ρ ^ 2 = ((d − 1 : ℕ) : ℝ)⁻¹` (carried by consumers as a hypothesis, so
the `√` plumbing stays in the eventual packaging), each level of a
full ball contributes equally to the squared norm — the identity
`radialVec_dotProduct_self` below — which is what makes the
Rayleigh-quotient computation of the remaining Step-3 slices come out
at a `k`-independent scale. -/
noncomputable def radialVec (A : WAdj (V := V)) (hA : A.IsSymm)
    (x y : V) (ρ : ℝ) (k : ℕ) : V → ℝ :=
  fun z => if levE A hA x y z ≤ k then ρ ^ (levE A hA x y z) else 0

omit [DecidableEq V] in
omit [Fintype V] in
/-- Entry form of the radial test vector — the falsifiability anchor. -/
theorem radialVec_apply (x y : V) (ρ : ℝ) (k : ℕ) (z : V) :
    radialVec A hA x y ρ k z
      = if levE A hA x y z ≤ k then ρ ^ (levE A hA x y z) else 0 := rfl

omit [DecidableEq V] in
/-- On the ball, the radial test vector is the pure level power. -/
theorem radialVec_of_mem_ballE {x y : V} {ρ : ℝ} {k : ℕ} {z : V}
    (hz : z ∈ ballE A hA x y k) :
    radialVec A hA x y ρ k z = ρ ^ (levE A hA x y z) := by
  have hz' : levE A hA x y z ≤ k := by
    simp only [ballE, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact hz
  simp only [radialVec, if_pos hz']

omit [DecidableEq V] in
/-- Outside the ball, the radial test vector vanishes — its support is
exactly `ballE`. -/
theorem radialVec_eq_zero_of_not_mem_ballE {x y : V} {ρ : ℝ} {k : ℕ} {z : V}
    (hz : z ∉ ballE A hA x y k) :
    radialVec A hA x y ρ k z = 0 := by
  have hz' : ¬ (levE A hA x y z ≤ k) := by
    intro hle
    exact hz (Finset.mem_filter.2 ⟨Finset.mem_univ z, hle⟩)
  simp only [radialVec, if_neg hz']

omit [DecidableEq V] in
omit [Fintype V] in
/-- The left endpoint carries the value `1` at every radius and every
`ρ` — the always-on seed of the nonvanishing statement. -/
theorem radialVec_left (x y : V) (ρ : ℝ) (k : ℕ) :
    radialVec A hA x y ρ k x = 1 := by
  have h0 : levE A hA x y x = 0 := by simp [levE]
  simp only [radialVec, h0, if_pos (Nat.zero_le k), pow_zero]

omit [DecidableEq V] in
omit [Fintype V] in
/-- The radial test vector is nonzero at every radius and every `ρ`:
its value at the left endpoint is `1`. -/
theorem radialVec_ne_zero (x y : V) (ρ : ℝ) (k : ℕ) :
    radialVec A hA x y ρ k ≠ 0 := by
  intro h
  have h1 := congrFun h x
  rw [radialVec_left] at h1
  simp at h1

/-- **The layer-cake sum bridge**: any function summed over the
radius-`k` edge ball equals its sum over the levels `0..k` — the
summation form of `ballE_card_eq_sum`, at a function rather than a
count. The test vector's squared norm is a level-constant function, so
this is the bridge its normalization computation consumes. -/
theorem sum_ballE_eq_sum_levels (g : V → ℝ) (x y : V) (k : ℕ) :
    ∑ z ∈ ballE A hA x y k, g z
      = ∑ j ∈ Finset.range (k + 1), ∑ z ∈ levClass A hA x y j, g z := by
  induction k with
  | zero =>
      rw [ballE_zero]
      simp [Finset.range_one]
  | succ k ih =>
      have hdis : Disjoint (ballE A hA x y k) (levClass A hA x y (k + 1)) :=
        Finset.disjoint_right.mpr fun a ha => by
          simp only [levClass, Finset.mem_filter] at ha
          intro hb
          simp only [ballE, Finset.mem_filter] at hb
          have h1 := ha.2
          have h2 := hb.2
          omega
      rw [ballE_succ_union, Finset.sum_union hdis, Finset.range_succ,
        Finset.sum_insert (by simp), ih]
      ac_rfl

/-- **The radial test vector's squared norm is `2 (k + 1)`** — the
normalization identity of Nilli's method: under the full-level
hypothesis `IsTreeBall` at radius `k + 1` and the d-regular-tree
normalization `ρ ^ 2 = ((d − 1 : ℕ) : ℝ)⁻¹`, every level `j ≤ k`
carries `2 (d−1)^j` vertices of value-squared `ρ^{2j}`, and the two
geometric factors cancel per level to exactly `2` — the growth of the
levels against the decay of the vector. This is the denominator of the
Rayleigh quotient of the remaining Step-3 slices and Step 4, computed
exactly through `ballE_card_eq_sum`'s level machinery (via the sum
bridge `sum_ballE_eq_sum_levels`). `1 < d` is load-bearing at the
cancellation step (`mul_inv_cancel₀`): at `d = 1` the truncated
`(d−1)^j` kills the level counts while `ρ = 0` remains
junk-admissible (`0⁻¹ = 0` in ℝ), and the identity genuinely fails —
fenced in QA at K₂. -/
theorem radialVec_dotProduct_self {d k : ℕ} {ρ : ℝ} {x y : V}
    (hd1 : 1 < d) (htb : IsTreeBall A hA x y d (k + 1))
    (hrho : ρ ^ 2 = ((d - 1 : ℕ) : ℝ)⁻¹) :
    Matrix.dotProduct (radialVec A hA x y ρ k) (radialVec A hA x y ρ k)
      = 2 * (k + 1) := by
  have hcast_ne : ((d - 1 : ℕ) : ℝ) ≠ 0 := by
    exact mod_cast (show (d - 1 : ℕ) ≠ 0 by omega)
  simp only [Matrix.dotProduct]
  have hzero : ∀ z : V, z ∉ ballE A hA x y k →
      radialVec A hA x y ρ k z * radialVec A hA x y ρ k z = 0 := by
    intro z hz
    rw [radialVec_eq_zero_of_not_mem_ballE hz, zero_mul]
  have hsplit :
      ∑ z : V, radialVec A hA x y ρ k z * radialVec A hA x y ρ k z
        = ∑ z ∈ ballE A hA x y k,
            radialVec A hA x y ρ k z * radialVec A hA x y ρ k z := by
    rw [Finset.sum_subset (Finset.subset_univ _) fun z _ hz => hzero z hz]
  rw [hsplit, sum_ballE_eq_sum_levels]
  have hInner : ∀ j ∈ Finset.range (k + 1),
      (∑ z ∈ levClass A hA x y j,
        radialVec A hA x y ρ k z * radialVec A hA x y ρ k z) = 2 := by
    intro j hj
    have hjk : j ≤ k := by
      simp only [Finset.mem_range] at hj
      omega
    have hval : ∀ z ∈ levClass A hA x y j,
        radialVec A hA x y ρ k z * radialVec A hA x y ρ k z
          = ρ ^ (2 * j) := by
      intro z hz
      simp only [levClass, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      have hmem : z ∈ ballE A hA x y k := by
        simp only [ballE, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [radialVec_of_mem_ballE hmem, hz]
      have h2j : 2 * j = j + j := by omega
      rw [h2j, ← pow_add]
    rw [Finset.sum_congr rfl (fun z hz => hval z hz), Finset.sum_const,
      htb j (by omega), nsmul_eq_mul]
    have hc : ((2 * (d - 1) ^ j : ℕ) : ℝ) = 2 * ((d - 1 : ℕ) : ℝ) ^ j := by
      push_cast
      ring
    rw [hc, pow_mul ρ 2 j, hrho, mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hcast_ne, one_pow, mul_one]
  rw [Finset.sum_congr rfl hInner, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  push_cast
  ring

end RadialVector

/-!
## Step 3, second slice: the energy half of the Rayleigh quotient
-/

section Energy

variable {A : WAdj (V := V)} {hA : A.IsSymm}

/-- Distance is 1-Lipschitz along an adjacency, junk-safe: for adjacent
`u, v`, `dist u w ≤ dist v w + 1` in either reachability regime (the
junk-zero case is discharged by contraposition — a walk from `u`
prefixed by the edge would make `v` reachable). -/
private theorem dist_le_dist_add_one_of_adj {W : Type} [DecidableEq W]
    {G : SimpleGraph W} {u v w : W} (h : G.Adj u v) :
    G.dist u w ≤ G.dist v w + 1 := by
  by_cases hreach : G.Reachable v w
  · obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
    have h2 : G.dist u w ≤ (SimpleGraph.Walk.cons h p).length :=
      SimpleGraph.dist_le _
    simp only [SimpleGraph.Walk.length_cons] at h2
    omega
  · have hj : G.dist v w = 0 := SimpleGraph.dist_eq_zero_of_not_reachable hreach
    by_contra hcon
    have hne : G.dist u w ≠ 0 := by omega
    obtain ⟨q⟩ := SimpleGraph.exists_walk_of_dist_ne_zero hne
    exact hreach ⟨SimpleGraph.Walk.cons h.symm q⟩

omit [Fintype V] in
/-- **The BFS level function is 1-Lipschitz along support-graph
edges.** For a positive-weight pair `u, v`, `levE u ≤ levE v + 1`: both
endpoint distances move by at most one along an edge (the junk-safe
adjacency triangle, at both endpoints), collapsed by `omega` at the
min. -/
theorem levE_le_levE_add_one_of_adj (x y u v : V)
    (hadj : (supportGraph A hA).Adj u v) :
    levE A hA x y u ≤ levE A hA x y v + 1 := by
  have h1 := dist_le_dist_add_one_of_adj (G := supportGraph A hA) (w := x) hadj
  have h2 := dist_le_dist_add_one_of_adj (G := supportGraph A hA) (w := y) hadj
  simp only [levE] at h1 h2 ⊢
  omega

/-- Predecessor extraction: a vertex at distance `≥ 1` from `x` has an
adjacent predecessor one step closer — the head of a shortest walk,
with the distance equality closed by the Lipschitz bound from both
sides. -/
private theorem exists_pred_of_one_le_dist {W : Type} [DecidableEq W]
    {G : SimpleGraph W} {z x : W} (h : 1 ≤ G.dist z x) :
    ∃ p : W, G.Adj z p ∧ G.dist p x + 1 = G.dist z x := by
  have hne : G.dist z x ≠ 0 := by omega
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_dist_ne_zero hne
  cases p with
  | nil =>
      simp only [SimpleGraph.Walk.length_nil] at hp
      omega
  | cons hz p' =>
      rename_i v
      refine ⟨v, hz, ?_⟩
      have hle := SimpleGraph.dist_le p'
      have hlip := dist_le_dist_add_one_of_adj (w := x) hz
      simp only [SimpleGraph.Walk.length_cons] at hp
      omega

omit [Fintype V] in
/-- **The parent lemma**: every vertex at level `≥ 1` has a
support-adjacent neighbor exactly one level down — the BFS parent, the
edge the energy bound harvests. The proof takes the min-attaining
endpoint, extracts the predecessor of a shortest walk, and closes the
level equality by Lipschitz from both sides. No connectivity
hypothesis: positive level already implies reachability from the
endpoint. -/
theorem exists_levE_parent (x y z : V) (hz : 1 ≤ levE A hA x y z) :
    ∃ p : V, 0 < A z p ∧ levE A hA x y p + 1 = levE A hA x y z := by
  have hmin : 1 ≤ (supportGraph A hA).dist z x
      ∧ 1 ≤ (supportGraph A hA).dist z y := by
    simp only [levE] at hz
    omega
  rcases Nat.le_total ((supportGraph A hA).dist z x)
      ((supportGraph A hA).dist z y) with hle | hle
  · obtain ⟨p, hadj, hdist⟩ := exists_pred_of_one_le_dist hmin.1
    refine ⟨p, (supportGraph_adj.1 hadj).2, ?_⟩
    have hl := levE_le_levE_add_one_of_adj x y z p hadj
    simp only [levE] at hl ⊢
    omega
  · obtain ⟨p, hadj, hdist⟩ := exists_pred_of_one_le_dist hmin.2
    refine ⟨p, (supportGraph_adj.1 hadj).2, ?_⟩
    have hl := levE_le_levE_add_one_of_adj x y z p hadj
    simp only [levE] at hl ⊢
    omega

/-- The interior of the radius-`k` edge ball: levels `1` through `k`,
level 0 (the endpoints) excluded — exactly the vertices whose parent
edges the energy bound harvests. -/
noncomputable def interiorE (A : WAdj (V := V)) (hA : A.IsSymm)
    (x y : V) (k : ℕ) : Finset V :=
  Finset.univ.filter fun z => 1 ≤ levE A hA x y z ∧ levE A hA x y z ≤ k

omit [DecidableEq V] in
theorem interiorE_zero (x y : V) : interiorE A hA x y 0 = ∅ := by
  refine Finset.eq_empty_of_forall_not_mem fun z hz => ?_
  simp only [interiorE, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  omega

theorem interiorE_succ_union (x y : V) (k : ℕ) :
    interiorE A hA x y (k + 1)
      = interiorE A hA x y k ∪ levClass A hA x y (k + 1) := by
  ext z
  simp only [interiorE, levClass, Finset.mem_filter, Finset.mem_union,
    Finset.mem_univ, true_and]
  omega

/-- **The interior level-sum bridge**: any function summed over the
interior equals its level-by-level sum over `1..k` — the
`sum_ballE_eq_sum_levels` pattern at the interior (level 0 excluded),
the summation input of the energy bound. -/
theorem sum_interiorE_eq_sum_levels (g : V → ℝ) (x y : V) (k : ℕ) :
    ∑ z ∈ interiorE A hA x y k, g z
      = ∑ j ∈ Finset.Ico 1 (k + 1), ∑ z ∈ levClass A hA x y j, g z := by
  induction k with
  | zero => rw [interiorE_zero]; simp
  | succ k ih =>
      have hdis : Disjoint (interiorE A hA x y k) (levClass A hA x y (k + 1)) :=
        Finset.disjoint_right.mpr fun a ha => by
          simp only [levClass, Finset.mem_filter] at ha
          intro hb
          simp only [interiorE, Finset.mem_filter] at hb
          have h1 := ha.2
          have h2 := hb.2
          omega
      rw [interiorE_succ_union, Finset.sum_union hdis,
        Nat.Ico_succ_right_eq_insert_Ico (by omega),
        Finset.sum_insert (by simp [Finset.mem_Ico])]
      rw [ih]
      ac_rfl

/-- **The energy half of Nilli's Rayleigh quotient — the numerator
bounded from below.** Under the existing tree-ball predicate (levels
full up to radius `k + 1`), the `0`-or-`≥ 1` weight discipline (every
parent edge carries weight at least `1`), distinct endpoints with a
genuine edge between them, and the d-regular-tree normalization, the
radial test vector's adjacency quadratic form is at least
`2 + 4 k (d−1) ρ`: the edge itself contributes `≥ 2` (both orders,
symmetry), and every one of the `2 (d−1)^j` vertices of level `j`
(`1 ≤ j ≤ k`) contributes its parent edge in both orders — a harvest
of selected nonnegative terms of the double sum, each level's
geometric growth cancelling the vector's decay to exactly
`2 (d−1) ρ` per level. With the delivered squared-norm identity as
denominator, this closes the Rayleigh quotient's
`2√(d−1) − O(1/k)` shape (the corollary below). A *lower* bound on
the numerator is all the variational route needs.

The cardinality equations alone give level sizes, not edge counts; the
bound counts parent edges from below (one per interior vertex, the
parent lemma), which is why no strengthening of `IsTreeBall` is
needed — and why the weight discipline is: on fractional weights a
parent edge can be arbitrarily light, and the conclusion fails
(fenced in QA at the half-weight edge), as it does at a pseudo-edge
with `A x y = 0` and at a loop `x = y` whose junk-zero partner fills
the level-0 equation. -/
theorem radialVec_quadForm_ge {d k : ℕ} {ρ : ℝ} {x y : V}
    (h01 : ∀ i j, A i j = 0 ∨ 1 ≤ A i j) (hxy : x ≠ y) (hedge : A x y ≠ 0)
    (hd1 : 1 < d) (htb : IsTreeBall A hA x y d (k + 1))
    (hrho : ρ ^ 2 = ((d - 1 : ℕ) : ℝ) ⁻¹) (hρ : 0 ≤ ρ) :
    2 + 4 * (k : ℝ) * ((d - 1 : ℕ) : ℝ) * ρ
      ≤ quadForm A (radialVec A hA x y ρ k) := by
  classical
  have hcast_ne : ((d - 1 : ℕ) : ℝ) ≠ 0 := by
    exact mod_cast (show (d - 1 : ℕ) ≠ 0 by omega)
  have hnn : ∀ i j, 0 ≤ A i j := by
    intro i j
    rcases h01 i j with h | h
    · simp [h]
    · exact (by norm_num : (0 : ℝ) ≤ 1).trans h
  have hfnn : ∀ z : V, 0 ≤ radialVec A hA x y ρ k z := by
    intro z
    by_cases hle : levE A hA x y z ≤ k
    · simp only [radialVec, if_pos hle]
      exact pow_nonneg hρ _
    · simp only [radialVec, if_neg hle]
      exact le_refl 0
  have hpar : ∀ z : V, ∃ p : V, 1 ≤ levE A hA x y z →
      0 < A z p ∧ levE A hA x y p + 1 = levE A hA x y z := by
    intro z
    by_cases hz : 1 ≤ levE A hA x y z
    · obtain ⟨p, h1, h2⟩ := exists_levE_parent x y z hz
      exact ⟨p, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨z, fun h => absurd h hz⟩
  choose pp hpp using hpar
  have hfx : radialVec A hA x y ρ k x = 1 := radialVec_left x y ρ k
  have hly : levE A hA x y y = 0 := by simp [levE]
  have hfy : radialVec A hA x y ρ k y = 1 := by
    simp only [radialVec, hly, if_pos (Nat.zero_le k), pow_zero]
  have hlx : levE A hA x y x = 0 := by simp [levE]
  have hSmem : ∀ z ∈ interiorE A hA x y k,
      1 ≤ levE A hA x y z ∧ levE A hA x y z ≤ k := by
    intro z hz
    simp only [interiorE, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact hz
  -- (1) the quadratic form as a double sum over all ordered pairs
  have hopen : quadForm A (radialVec A hA x y ρ k)
      = ∑ q ∈ (Finset.univ : Finset (V × V)),
          A q.1 q.2 * radialVec A hA x y ρ k q.1 * radialVec A hA x y ρ k q.2 := by
    simp only [quadForm, Matrix.dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun v _ => by ring
  -- (2) the selection's three blocks are pairwise disjoint
  have hdis12 : Disjoint
      (Finset.image (fun z : V => (z, pp z)) (interiorE A hA x y k))
      (Finset.image (fun z : V => (pp z, z)) (interiorE A hA x y k)) :=
    Finset.disjoint_right.mpr fun q hq2 hq1 => by
      simp only [Finset.mem_image] at hq1 hq2
      obtain ⟨z, hzS, hqz⟩ := hq1
      obtain ⟨z', hzS', hqz'⟩ := hq2
      have heq : (z, pp z) = (pp z', z') := by rw [hqz, hqz']
      rw [Prod.mk.injEq] at heq
      obtain ⟨e1, e2⟩ := heq
      have c1 : levE A hA x y z = levE A hA x y (pp z') := by rw [e1]
      have Ha1 := (hpp z (hSmem z hzS).1).2
      have Ha2 := (hpp z' (hSmem z' hzS').1).2
      rw [e2] at Ha1
      omega
  have hdis3 : Disjoint
      (Finset.image (fun z : V => (z, pp z)) (interiorE A hA x y k) ∪
        Finset.image (fun z : V => (pp z, z)) (interiorE A hA x y k))
      (insert (x, y) (insert (y, x) (∅ : Finset (V × V)))) :=
    Finset.disjoint_right.mpr fun q hqXY hqsel => by
      rcases Finset.mem_union.1 hqsel with hq1 | hq2
      · simp only [Finset.mem_image] at hq1
        obtain ⟨z, hzS, hqz⟩ := hq1
        rw [← hqz] at hqXY
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty,
          or_false, Prod.mk.injEq] at hqXY
        have h1 := (hSmem z hzS).1
        rcases hqXY with ⟨hc, _⟩ | ⟨hc, _⟩
        · rw [hc] at h1
          omega
        · rw [hc] at h1
          omega
      · simp only [Finset.mem_image] at hq2
        obtain ⟨z, hzS, hqz⟩ := hq2
        rw [← hqz] at hqXY
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty,
          or_false, Prod.mk.injEq] at hqXY
        have h1 := (hSmem z hzS).1
        rcases hqXY with ⟨_, hc⟩ | ⟨_, hc⟩
        · rw [hc] at h1
          omega
        · rw [hc] at h1
          omega
  -- (3) the selection's total, block by block
  have himg1sum : ∑ q ∈ Finset.image (fun z : V => (z, pp z)) (interiorE A hA x y k),
          (fun q : V × V => A q.1 q.2 * radialVec A hA x y ρ k q.1
            * radialVec A hA x y ρ k q.2) q
      = ∑ z ∈ interiorE A hA x y k,
          A z (pp z) * radialVec A hA x y ρ k z * radialVec A hA x y ρ k (pp z) :=
    Finset.sum_image fun a _ a' _ h => congrArg Prod.fst h
  have himg2sum : ∑ q ∈ Finset.image (fun z : V => (pp z, z)) (interiorE A hA x y k),
          (fun q : V × V => A q.1 q.2 * radialVec A hA x y ρ k q.1
            * radialVec A hA x y ρ k q.2) q
      = ∑ z ∈ interiorE A hA x y k,
          A (pp z) z * radialVec A hA x y ρ k (pp z) * radialVec A hA x y ρ k z :=
    Finset.sum_image fun a _ a' _ h => congrArg Prod.snd h
  have hxy2sum : ∑ q ∈ insert (x, y) (insert (y, x) (∅ : Finset (V × V))),
          (fun q : V × V => A q.1 q.2 * radialVec A hA x y ρ k q.1
            * radialVec A hA x y ρ k q.2) q
      = A x y * radialVec A hA x y ρ k x * radialVec A hA x y ρ k y
        + A y x * radialVec A hA x y ρ k y * radialVec A hA x y ρ k x := by
    rw [Finset.sum_insert (by simp [Prod.mk.injEq, hxy]),
      Finset.sum_insert (by simp), Finset.sum_empty]
    simp
  have hunion : ∑ q ∈ (Finset.image (fun z : V => (z, pp z)) (interiorE A hA x y k) ∪
          Finset.image (fun z : V => (pp z, z)) (interiorE A hA x y k) ∪
          insert (x, y) (insert (y, x) (∅ : Finset (V × V)))),
          (fun q : V × V => A q.1 q.2 * radialVec A hA x y ρ k q.1
            * radialVec A hA x y ρ k q.2) q
      = 2 * ∑ z ∈ interiorE A hA x y k,
          A z (pp z) * radialVec A hA x y ρ k z * radialVec A hA x y ρ k (pp z)
        + (A x y * radialVec A hA x y ρ k x * radialVec A hA x y ρ k y
          + A y x * radialVec A hA x y ρ k y * radialVec A hA x y ρ k x) := by
    rw [Finset.sum_union hdis3, Finset.sum_union hdis12, himg1sum, himg2sum, hxy2sum]
    have hsym : ∀ z ∈ interiorE A hA x y k,
        A (pp z) z * radialVec A hA x y ρ k (pp z) * radialVec A hA x y ρ k z
          = A z (pp z) * radialVec A hA x y ρ k z * radialVec A hA x y ρ k (pp z) := by
      intro z _
      rw [hA.apply z (pp z)]
      ring
    rw [Finset.sum_congr rfl hsym]
    ring
  -- (4) the selection is a subset: its total is at most the form
  have hsub : ∑ q ∈ (Finset.image (fun z : V => (z, pp z)) (interiorE A hA x y k) ∪
          Finset.image (fun z : V => (pp z, z)) (interiorE A hA x y k) ∪
          insert (x, y) (insert (y, x) (∅ : Finset (V × V)))),
          (fun q : V × V => A q.1 q.2 * radialVec A hA x y ρ k q.1
            * radialVec A hA x y ρ k q.2) q
      ≤ ∑ q ∈ (Finset.univ : Finset (V × V)),
          (fun q : V × V => A q.1 q.2 * radialVec A hA x y ρ k q.1
            * radialVec A hA x y ρ k q.2) q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun q _ _ => mul_nonneg (mul_nonneg (hnn q.1 q.2) (hfnn q.1)) (hfnn q.2))
  rw [← hopen] at hsub
  rw [hunion] at hsub
  rw [hfx, hfy] at hsub
  have hmul11 : ∀ a : ℝ, a * 1 * 1 = a := fun a => by ring
  rw [hmul11 (A x y), hmul11 (A y x)] at hsub
  -- (5) the endpoint pair contributes at least 2
  have hxyge : (2 : ℝ) ≤ A x y + A y x := by
    have hx1 : 1 ≤ A x y := by
      rcases h01 x y with h | h
      · rw [h] at hedge; exact absurd hedge (by simp)
      · exact h
    have hy1 : 1 ≤ A y x := by rw [hA.apply x y]; exact hx1
    linarith
  -- (6) the parent-sum bound, level by level
  have hparbound : (k : ℝ) * (2 * (((d - 1 : ℕ) : ℝ) * ρ))
      ≤ ∑ z ∈ interiorE A hA x y k,
          A z (pp z) * radialVec A hA x y ρ k z * radialVec A hA x y ρ k (pp z) := by
    have hlevel : ∀ j ∈ Finset.Ico 1 (k + 1),
        2 * (((d - 1 : ℕ) : ℝ) ^ j) * ρ ^ (2 * j - 1)
          ≤ ∑ z ∈ levClass A hA x y j, A z (pp z) * radialVec A hA x y ρ k z
            * radialVec A hA x y ρ k (pp z) := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Ico.1 hj).1
      have hjk : j ≤ k := by have := Finset.mem_Ico.1 hj; omega
      have hterm : ∀ z ∈ levClass A hA x y j,
          ρ ^ (2 * j - 1) ≤ A z (pp z) * radialVec A hA x y ρ k z
            * radialVec A hA x y ρ k (pp z) := by
        intro z hz
        have hzj : levE A hA x y z = j := by
          simp only [levClass, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          exact hz
        have hzp : levE A hA x y (pp z) = j - 1 := by
          have h1 := (hpp z (by omega)).2
          omega
        have hzball : z ∈ ballE A hA x y k := by
          simp only [ballE, Finset.mem_filter, Finset.mem_univ, true_and]; omega
        have hpball : pp z ∈ ballE A hA x y k := by
          simp only [ballE, Finset.mem_filter, Finset.mem_univ, true_and]; omega
        have e1 := radialVec_of_mem_ballE (ρ := ρ) hzball
        have e2 := radialVec_of_mem_ballE (ρ := ρ) hpball
        have hge : (1 : ℝ) ≤ A z (pp z) := by
          rcases h01 z (pp z) with h | h
          · have hp := (hpp z (by omega)).1
            rw [h] at hp
            exact absurd hp (by simp)
          · exact h
        have eexp : 2 * j - 1 = j + (j - 1) := by omega
        calc ρ ^ (2 * j - 1) = 1 * (ρ ^ j * ρ ^ (j - 1)) := by
              rw [eexp, pow_add]; ring
          _ ≤ A z (pp z) * (ρ ^ j * ρ ^ (j - 1)) :=
              mul_le_mul_of_nonneg_right hge
                (mul_nonneg (pow_nonneg hρ _) (pow_nonneg hρ _))
          _ = A z (pp z) * radialVec A hA x y ρ k z
              * radialVec A hA x y ρ k (pp z) := by
              rw [e1, e2, hzj, hzp]; ring
      have hconst : (∑ z ∈ levClass A hA x y j, ρ ^ (2 * j - 1))
          = 2 * (((d - 1 : ℕ) : ℝ) ^ j) * ρ ^ (2 * j - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul, htb j (by omega)]
        push_cast
        ring
      rw [← hconst]
      exact Finset.sum_le_sum hterm
    have hcollapse : ∀ j ∈ Finset.Ico 1 (k + 1),
        2 * (((d - 1 : ℕ) : ℝ) ^ j) * ρ ^ (2 * j - 1)
          = 2 * (((d - 1 : ℕ) : ℝ) * ρ) := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Ico.1 hj).1
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      have e1 : ((d - 1 : ℕ) : ℝ) ^ (m + 1)
          = ((d - 1 : ℕ) : ℝ) ^ m * ((d - 1 : ℕ) : ℝ) := pow_succ _ _
      have e2 : ρ ^ (2 * (m + 1) - 1) = (ρ ^ 2) ^ m * ρ := by
        have eexp : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
        rw [eexp, pow_add, pow_mul, pow_one]
      have hreg : 2 * (((d - 1 : ℕ) : ℝ) ^ m * ((d - 1 : ℕ) : ℝ))
            * ((ρ ^ 2) ^ m * ρ)
          = 2 * (((d - 1 : ℕ) : ℝ) * ρ)
            * (((d - 1 : ℕ) : ℝ) ^ m * (ρ ^ 2) ^ m) := by ring
      rw [e1, e2, hreg, ← mul_pow, hrho, mul_inv_cancel₀ hcast_ne, one_pow, mul_one]
    have hcard : ∑ j ∈ Finset.Ico 1 (k + 1), 2 * (((d - 1 : ℕ) : ℝ) * ρ)
        = (k : ℝ) * (2 * (((d - 1 : ℕ) : ℝ) * ρ)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
      simp only [Nat.add_sub_cancel]
    calc (k : ℝ) * (2 * (((d - 1 : ℕ) : ℝ) * ρ))
        = ∑ j ∈ Finset.Ico 1 (k + 1), 2 * (((d - 1 : ℕ) : ℝ) * ρ) := hcard.symm
      _ = ∑ j ∈ Finset.Ico 1 (k + 1),
            2 * (((d - 1 : ℕ) : ℝ) ^ j) * ρ ^ (2 * j - 1) :=
          Finset.sum_congr rfl (fun j hj => (hcollapse j hj).symm)
      _ ≤ ∑ j ∈ Finset.Ico 1 (k + 1), ∑ z ∈ levClass A hA x y j,
            A z (pp z) * radialVec A hA x y ρ k z * radialVec A hA x y ρ k (pp z) :=
          Finset.sum_le_sum hlevel
      _ = ∑ z ∈ interiorE A hA x y k, A z (pp z) * radialVec A hA x y ρ k z
            * radialVec A hA x y ρ k (pp z) :=
          (sum_interiorE_eq_sum_levels _ x y k).symm
  -- (7) the final assembly
  calc 2 + 4 * (k : ℝ) * ((d - 1 : ℕ) : ℝ) * ρ
      = 2 * ((k : ℝ) * (2 * (((d - 1 : ℕ) : ℝ) * ρ))) + 2 := by ring
    _ ≤ 2 * ∑ z ∈ interiorE A hA x y k,
          A z (pp z) * radialVec A hA x y ρ k z * radialVec A hA x y ρ k (pp z)
        + (A x y + A y x) :=
        add_le_add (mul_le_mul_of_nonneg_left hparbound (by norm_num)) hxyge
    _ ≤ quadForm A (radialVec A hA x y ρ k) := hsub

/-- **The Rayleigh-quotient form of the energy bound**: joining the
numerator bound to the delivered squared-norm identity, the radial
test vector's Rayleigh quotient is at least
`(2 + 4 k (d−1) ρ) / (2 (k + 1))` — Nilli's
`(1 + 2 k √(d−1)) / (k + 1)` before the Step-5 `√` packaging. This is
the interface Step 4's orthogonalization consumes. -/
theorem radialVec_rayleigh_ge {d k : ℕ} {ρ : ℝ} {x y : V}
    (h01 : ∀ i j, A i j = 0 ∨ 1 ≤ A i j) (hxy : x ≠ y) (hedge : A x y ≠ 0)
    (hd1 : 1 < d) (htb : IsTreeBall A hA x y d (k + 1))
    (hrho : ρ ^ 2 = ((d - 1 : ℕ) : ℝ) ⁻¹) (hρ : 0 ≤ ρ) :
    (2 + 4 * (k : ℝ) * ((d - 1 : ℕ) : ℝ) * ρ) / (2 * ((k : ℝ) + 1))
      ≤ rayleigh A (radialVec A hA x y ρ k) := by
  have hn : radialVec A hA x y ρ k ≠ 0 := radialVec_ne_zero x y ρ k
  have hq := radialVec_quadForm_ge h01 hxy hedge hd1 htb hrho hρ
  have hd := radialVec_dotProduct_self hd1 htb hrho
  rw [rayleigh, if_neg hn, hd]
  have hpos : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by
    have hk : (0 : ℕ) < k + 1 := by omega
    have hc : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := Nat.cast_pos.2 hk
    have he : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    linarith
  rw [div_le_div_iff_of_pos_right hpos]
  exact hq


end Energy

/-!
## Step 4: the two-vector orthogonalization and the Courant–Fischer application
-/

section TwoEdge

variable {A : WAdj (V := V)} {hA : A.IsSymm}


variable {V : Type} [Fintype V] [DecidableEq V]
variable {A : WAdj (V := V)} {hA : A.IsSymm}

/-! ### The equal-mass lemma -/

theorem radialVec_sum_eq {d k : ℕ} {ρ : ℝ} {x y : V}
    (htb : IsTreeBall A hA x y d (k + 1)) :
    ∑ z, radialVec A hA x y ρ k z
      = ∑ j ∈ Finset.range (k + 1), 2 * (((d - 1 : ℕ) : ℝ) ^ j * ρ ^ j) := by
  have hzero : ∀ z : V, z ∉ ballE A hA x y k → radialVec A hA x y ρ k z = 0 :=
    fun z hz => radialVec_eq_zero_of_not_mem_ballE hz
  rw [← Finset.sum_subset (Finset.subset_univ _) fun z _ hz => hzero z hz,
    sum_ballE_eq_sum_levels]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := by
    simp only [Finset.mem_range] at hj
    omega
  have hval : ∀ z ∈ levClass A hA x y j, radialVec A hA x y ρ k z = ρ ^ j := by
    intro z hz
    have hzl : levE A hA x y z = j := by
      simp only [levClass, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact hz
    have hmem : z ∈ ballE A hA x y k := by
      simp only [ballE, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [radialVec_of_mem_ballE hmem, hzl]
  rw [Finset.sum_congr rfl (fun z hz => hval z hz), Finset.sum_const, htb j (by omega),
    nsmul_eq_mul]
  push_cast
  ring

/-! ### The two-edge vector -/

noncomputable def twoEdgeVec (A : WAdj (V := V)) (hA : A.IsSymm)
    (x y u v : V) (ρ : ℝ) (k : ℕ) : V → ℝ :=
  fun z => radialVec A hA x y ρ k z - radialVec A hA u v ρ k z

omit [Fintype V] in
omit [DecidableEq V] in
theorem twoEdgeVec_apply (x y u v : V) (ρ : ℝ) (k : ℕ) (z : V) :
    twoEdgeVec A hA x y u v ρ k z
      = radialVec A hA x y ρ k z - radialVec A hA u v ρ k z := rfl

theorem twoEdgeVec_dotProduct_onesVec {d k : ℕ} {ρ : ℝ} {x y u v : V}
    (htb1 : IsTreeBall A hA x y d (k + 1)) (htb2 : IsTreeBall A hA u v d (k + 1)) :
    Matrix.dotProduct (twoEdgeVec A hA x y u v ρ k) onesVec = 0 := by
  simp only [Matrix.dotProduct, twoEdgeVec, onesVec, mul_one]
  rw [Finset.sum_sub_distrib, radialVec_sum_eq htb1,
    radialVec_sum_eq htb2]
  simp

omit [DecidableEq V] in
theorem radialVec_dotProduct_eq_zero_of_disjoint {ρ : ℝ} {k : ℕ} {x y u v : V}
    (hdis : Disjoint (ballE A hA x y k) (ballE A hA u v k)) :
    Matrix.dotProduct (radialVec A hA x y ρ k) (radialVec A hA u v ρ k) = 0 := by
  have hterm : ∀ z : V,
      radialVec A hA x y ρ k z * radialVec A hA u v ρ k z = 0 := by
    intro z
    by_cases hz : z ∈ ballE A hA x y k
    · have hz2 : z ∉ ballE A hA u v k := fun hb =>
        Finset.disjoint_right.1 hdis hb hz
      rw [radialVec_eq_zero_of_not_mem_ballE hz2, mul_zero]
    · rw [radialVec_eq_zero_of_not_mem_ballE hz, zero_mul]
  simp only [Matrix.dotProduct]
  exact Finset.sum_eq_zero fun z _ => hterm z

theorem twoEdgeVec_dotProduct_self {d k : ℕ} {ρ : ℝ} {x y u v : V}
    (hd1 : 1 < d) (htb1 : IsTreeBall A hA x y d (k + 1))
    (htb2 : IsTreeBall A hA u v d (k + 1))
    (hrho : ρ ^ 2 = ((d - 1 : ℕ) : ℝ) ⁻¹)
    (hdis : Disjoint (ballE A hA x y k) (ballE A hA u v k)) :
    Matrix.dotProduct (twoEdgeVec A hA x y u v ρ k)
      (twoEdgeVec A hA x y u v ρ k)
      = 4 * ((k : ℝ) + 1) := by
  have h1 := radialVec_dotProduct_self (d := d) (k := k) (ρ := ρ) (x := x) (y := y)
    hd1 htb1 hrho
  have h2 := radialVec_dotProduct_self (d := d) (k := k) (ρ := ρ) (x := u) (y := v)
    hd1 htb2 hrho
  have h3 := radialVec_dotProduct_eq_zero_of_disjoint (ρ := ρ) (k := k)
    (x := x) (y := y) (u := u) (v := v) hdis
  simp only [Matrix.dotProduct, twoEdgeVec]
  have hterm : ∀ z : V,
      (radialVec A hA x y ρ k z - radialVec A hA u v ρ k z) *
        (radialVec A hA x y ρ k z - radialVec A hA u v ρ k z)
      = radialVec A hA x y ρ k z * radialVec A hA x y ρ k z
          - 2 * (radialVec A hA x y ρ k z * radialVec A hA u v ρ k z)
          + radialVec A hA u v ρ k z * radialVec A hA u v ρ k z := by
    intro z; ring
  rw [Finset.sum_congr rfl (fun z _ => hterm z), Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  -- three sums; convert h1 h2 h3 into plain sums
  simp only [Matrix.dotProduct] at h1 h2 h3
  rw [← Finset.mul_sum, h3, mul_zero, sub_zero, h1, h2]
  ring

omit [DecidableEq V] in
theorem twoEdgeVec_ne_zero {ρ : ℝ} {k : ℕ} {x y u v : V}
    (hdis : Disjoint (ballE A hA x y k) (ballE A hA u v k)) :
    twoEdgeVec A hA x y u v ρ k ≠ 0 := by
  intro h
  have hx1 : x ∈ ballE A hA x y k := by
    simp only [ballE, Finset.mem_filter, Finset.mem_univ, true_and]
    have : levE A hA x y x = 0 := by simp [levE]
    omega
  have hx2 : x ∉ ballE A hA u v k := fun hb => Finset.disjoint_right.1 hdis hb hx1
  have h1 : twoEdgeVec A hA x y u v ρ k x = 1 := by
    have hlv : levE A hA x y x = 0 := by simp [levE]
    rw [twoEdgeVec_apply, radialVec_of_mem_ballE hx1, hlv, pow_zero,
      radialVec_eq_zero_of_not_mem_ballE hx2, sub_zero]
  have h0 := congrFun h x
  rw [h1] at h0
  simp at h0

/-! ### The cross-term elimination -/

theorem levE_cross_adj_eq_zero {k : ℕ} {x y u v j i : V}
    (hdis : Disjoint (ballE A hA x y (k + 1)) (ballE A hA u v (k + 1)))
    (hj : j ∈ ballE A hA x y k) (hi : i ∈ ballE A hA u v k)
    (hAdj : (supportGraph A hA).Adj j i) : False := by
  have hjle : levE A hA x y j ≤ k := by
    simp only [ballE, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hj
  have hl := levE_le_levE_add_one_of_adj x y i j hAdj.symm
  have hi1 : i ∈ ballE A hA x y (k + 1) := by
    simp only [ballE, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hi2 : i ∈ ballE A hA u v (k + 1) :=
    ballE_mono u v (Nat.le_succ k) hi
  exact Finset.disjoint_right.1 hdis hi2 hi1

theorem radialVec_cross_dotProduct_eq_zero {k : ℕ} {ρ : ℝ} {x y u v : V}
    (hnn : ∀ i j, 0 ≤ A i j)
    (hdis : Disjoint (ballE A hA x y (k + 1)) (ballE A hA u v (k + 1))) :
    Matrix.dotProduct (radialVec A hA x y ρ k) (A *ᵥ radialVec A hA u v ρ k) = 0 := by
  have hterm : ∀ j i : V,
      radialVec A hA x y ρ k j * (A j i * radialVec A hA u v ρ k i) = 0 := by
    intro j i
    by_cases hj : j ∈ ballE A hA x y k
    · by_cases hi : i ∈ ballE A hA u v k
      · rcases eq_or_ne j i with rfl | hji
        · exact (Finset.disjoint_right.1 hdis
            (ballE_mono u v (Nat.le_succ k) hi) (ballE_mono x y (Nat.le_succ k) hj)).elim
        · have hAi : A j i = 0 := by
            by_contra hAi
            have hpos : 0 < A j i := lt_of_le_of_ne (hnn j i)
              (fun heq => hAi heq.symm)
            exact levE_cross_adj_eq_zero hdis hj hi
              (supportGraph_adj.2 ⟨hji, hpos⟩)
          rw [hAi]
          ring
      · rw [radialVec_eq_zero_of_not_mem_ballE hi]
        ring
    · rw [radialVec_eq_zero_of_not_mem_ballE hj]
      ring
  simp only [Matrix.dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_eq_zero fun j _ =>
    Finset.sum_eq_zero fun i _ => hterm j i


variable {V : Type} [Fintype V] [DecidableEq V]
variable {A : WAdj (V := V)} {hA : A.IsSymm}

/-! ### The quadratic-form expansion of the difference vector -/

omit [DecidableEq V] in
theorem dotProduct_mulVec_symm (hA : A.IsSymm) (a b : V → ℝ) :
    Matrix.dotProduct a (A *ᵥ b) = Matrix.dotProduct b (A *ᵥ a) := by
  have hL : Matrix.dotProduct a (A *ᵥ b)
      = ∑ u, ∑ v, A u v * (a u * b v) := by
    simp only [Matrix.dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  have hR : Matrix.dotProduct b (A *ᵥ a)
      = ∑ u, ∑ v, A u v * (a u * b v) := by
    simp only [Matrix.dotProduct, Matrix.mulVec, Finset.mul_sum]
    have hswap : ∑ u : V, ∑ v : V, b u * (A u v * a v)
        = ∑ u : V, ∑ v : V, b v * (A v u * a u) := by
      rw [Finset.sum_comm]
    rw [hswap]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [hA.apply u v]
    ring
  rw [hL, hR]

omit [DecidableEq V] in
theorem quadForm_sub (hA : A.IsSymm) (f g : V → ℝ) :
    quadForm A (f - g) = quadForm A f
      - 2 * Matrix.dotProduct f (A *ᵥ g) + quadForm A g := by
  simp only [quadForm, Matrix.mulVec_sub]
  rw [Matrix.sub_dotProduct, Matrix.dotProduct_sub, Matrix.dotProduct_sub,
    dotProduct_mulVec_symm hA g f]
  ring

/-! ### The numerator bound -/

theorem twoEdgeVec_quadForm_ge {d k : ℕ} {ρ : ℝ} {x y u v : V}
    (h01 : ∀ i j, A i j = 0 ∨ 1 ≤ A i j)
    (hxy : x ≠ y) (hedge : A x y ≠ 0) (huv : u ≠ v) (hedge2 : A u v ≠ 0)
    (hd1 : 1 < d) (htb1 : IsTreeBall A hA x y d (k + 1))
    (htb2 : IsTreeBall A hA u v d (k + 1))
    (hrho : ρ ^ 2 = ((d - 1 : ℕ) : ℝ) ⁻¹) (hρ : 0 ≤ ρ)
    (hdis : Disjoint (ballE A hA x y (k + 1)) (ballE A hA u v (k + 1))) :
    2 * (2 + 4 * (k : ℝ) * ((d - 1 : ℕ) : ℝ) * ρ)
      ≤ quadForm A (twoEdgeVec A hA x y u v ρ k) := by
  have hnn : ∀ i j, 0 ≤ A i j := by
    intro i j
    rcases h01 i j with h | h
    · simp [h]
    · exact (by norm_num : (0 : ℝ) ≤ 1).trans h
  have hq1 := radialVec_quadForm_ge (d := d) (k := k) (ρ := ρ) (x := x) (y := y)
    h01 hxy hedge hd1 htb1 hrho hρ
  have hq2 := radialVec_quadForm_ge (d := d) (k := k) (ρ := ρ) (x := u) (y := v)
    h01 huv hedge2 hd1 htb2 hrho hρ
  have hcross := radialVec_cross_dotProduct_eq_zero (ρ := ρ) (k := k)
    (x := x) (y := y) (u := u) (v := v) hnn hdis
  have hfun : twoEdgeVec A hA x y u v ρ k
      = radialVec A hA x y ρ k - radialVec A hA u v ρ k := rfl
  rw [hfun, quadForm_sub hA, hcross]
  simp only [mul_zero, sub_zero]
  linarith

theorem twoEdgeVec_rayleigh_ge {d k : ℕ} {ρ : ℝ} {x y u v : V}
    (h01 : ∀ i j, A i j = 0 ∨ 1 ≤ A i j)
    (hxy : x ≠ y) (hedge : A x y ≠ 0) (huv : u ≠ v) (hedge2 : A u v ≠ 0)
    (hd1 : 1 < d) (htb1 : IsTreeBall A hA x y d (k + 1))
    (htb2 : IsTreeBall A hA u v d (k + 1))
    (hrho : ρ ^ 2 = ((d - 1 : ℕ) : ℝ) ⁻¹) (hρ : 0 ≤ ρ)
    (hdisK : Disjoint (ballE A hA x y k) (ballE A hA u v k))
    (hdisK1 : Disjoint (ballE A hA x y (k + 1)) (ballE A hA u v (k + 1))) :
    (2 + 4 * (k : ℝ) * ((d - 1 : ℕ) : ℝ) * ρ) / (2 * ((k : ℝ) + 1))
      ≤ rayleigh A (twoEdgeVec A hA x y u v ρ k) := by
  have hn := twoEdgeVec_ne_zero (ρ := ρ) (k := k) (x := x) (y := y)
    (u := u) (v := v) hdisK
  have hq := twoEdgeVec_quadForm_ge h01 hxy hedge huv hedge2 hd1 htb1 htb2
    hrho hρ hdisK1
  have hdd := twoEdgeVec_dotProduct_self (d := d) (k := k) (ρ := ρ)
    (x := x) (y := y) (u := u) (v := v) hd1 htb1 htb2 hrho hdisK
  rw [rayleigh, if_neg hn, hdd]
  have hpos4 : (0 : ℝ) < 4 * ((k : ℝ) + 1) := by
    have hk : (0 : ℕ) < k + 1 := by omega
    have hc : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := Nat.cast_pos.2 hk
    have he : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    linarith
  have hpos2 : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by linarith
  have key : (2 + 4 * (k : ℝ) * ((d - 1 : ℕ) : ℝ) * ρ) * (4 * ((k : ℝ) + 1))
      ≤ quadForm A (twoEdgeVec A hA x y u v ρ k) * (2 * ((k : ℝ) + 1)) := by
    have hrw : (2 + 4 * (k : ℝ) * ((d - 1 : ℕ) : ℝ) * ρ) * (4 * ((k : ℝ) + 1))
        = (2 * (2 + 4 * (k : ℝ) * ((d - 1 : ℕ) : ℝ) * ρ)) * (2 * ((k : ℝ) + 1)) := by
      ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hq (by linarith)
  exact (div_le_div_iff₀ hpos2 hpos4).2 key

/-! ### The engine layer at `M = d • 1 - A` -/

omit [Fintype V] in
theorem smul_one_sub_isSymm (hA : A.IsSymm) (c : ℝ) :
    (c • (1 : Matrix V V ℝ) - A).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [Matrix.transpose_apply, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : j ≠ i := Ne.symm hij
    rw [if_neg hji, if_neg hij, hA.apply i j]

theorem smul_one_sub_mulVec_onesVec {c : ℝ} (hd : IsDRegular A c) :
    (c • (1 : Matrix V V ℝ) - A) *ᵥ onesVec = 0 := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    adjacency_mulVec_onesVec hd, sub_self]

theorem quadForm_smul_one_sub {c : ℝ} (x : V → ℝ) :
    quadForm (c • (1 : Matrix V V ℝ) - A) x
      = c * Matrix.dotProduct x x - quadForm A x := by
  simp only [quadForm, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
    Matrix.one_mulVec, Matrix.dotProduct_sub, Matrix.dotProduct_smul,
    smul_eq_mul]

/-! ### The headline -/

theorem twoEdgeVec_secondEval_le {d k : ℕ} {ρ : ℝ} {x y u v : V}
    (h01 : ∀ i j, A i j = 0 ∨ 1 ≤ A i j)
    (hd : IsDRegular A ((d : ℕ) : ℝ))
    (hxy : x ≠ y) (hedge : A x y ≠ 0) (huv : u ≠ v) (hedge2 : A u v ≠ 0)
    (hconn : (supportGraph A hA).Connected)
    (hfar : (k + 1) + (k + 1) < distEdge A hA x y u v)
    (hd1 : 1 < d) (htb1 : IsTreeBall A hA x y d (k + 1))
    (htb2 : IsTreeBall A hA u v d (k + 1))
    (hrho : ρ ^ 2 = ((d - 1 : ℕ) : ℝ) ⁻¹) (hρ : 0 ≤ ρ)
    (hcard : 2 ≤ Fintype.card V) :
    secondEval (((d : ℕ) : ℝ) • (1 : Matrix V V ℝ) - A)
        (smul_one_sub_isSymm hA ((d : ℕ) : ℝ)) hcard
      ≤ ((d : ℕ) : ℝ)
          - (2 + 4 * (k : ℝ) * ((d - 1 : ℕ) : ℝ) * ρ) / (2 * ((k : ℝ) + 1)) := by
  have hnn : ∀ i j, 0 ≤ A i j := by
    intro i j
    rcases h01 i j with h | h
    · simp [h]
    · exact (by norm_num : (0 : ℝ) ≤ 1).trans h
  have hdis0 : Disjoint (ballE A hA x y k) (ballE A hA u v k) :=
    ballE_disjoint_of_lt_distEdge x y u v k k hconn (by omega)
  have hdis1 : Disjoint (ballE A hA x y (k + 1)) (ballE A hA u v (k + 1)) :=
    ballE_disjoint_of_lt_distEdge x y u v (k + 1) (k + 1) hconn hfar
  have hne := twoEdgeVec_ne_zero (ρ := ρ) (k := k) (x := x) (y := y)
    (u := u) (v := v) hdis0
  have horth := twoEdgeVec_dotProduct_onesVec (d := d) (k := k) (ρ := ρ)
    (x := x) (y := y) (u := u) (v := v) htb1 htb2
  have hpsd : ∀ z : V → ℝ,
      0 ≤ quadForm (((d : ℕ) : ℝ) • (1 : Matrix V V ℝ) - A) z := by
    intro z
    rw [quadForm_smul_one_sub]
    have hdom := quadForm_le_of_isDRegular hA hnn hd z
    linarith
  have hker := smul_one_sub_mulVec_onesVec hd
  have heng := secondEval_le_rayleigh
    (M := ((d : ℕ) : ℝ) • (1 : Matrix V V ℝ) - A)
    (smul_one_sub_isSymm hA ((d : ℕ) : ℝ)) hpsd hker hcard hne horth
  -- rayleigh M g = d - rayleigh A g
  have hdpos : (0 : ℝ) < Matrix.dotProduct
      (twoEdgeVec A hA x y u v ρ k) (twoEdgeVec A hA x y u v ρ k) := by
    have hdd := twoEdgeVec_dotProduct_self (d := d) (k := k) (ρ := ρ)
      (x := x) (y := y) (u := u) (v := v) hd1 htb1 htb2 hrho hdis0
    have hk : (0 : ℕ) < k + 1 := by omega
    have hc : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := Nat.cast_pos.2 hk
    have he : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hdd]
    linarith
  have hrayM : rayleigh (((d : ℕ) : ℝ) • (1 : Matrix V V ℝ) - A)
      (twoEdgeVec A hA x y u v ρ k)
      = ((d : ℕ) : ℝ) - rayleigh A (twoEdgeVec A hA x y u v ρ k) := by
    have e1 : rayleigh (((d : ℕ) : ℝ) • (1 : Matrix V V ℝ) - A)
        (twoEdgeVec A hA x y u v ρ k)
        = (((d : ℕ) : ℝ) * Matrix.dotProduct
            (twoEdgeVec A hA x y u v ρ k) (twoEdgeVec A hA x y u v ρ k)
            - quadForm A (twoEdgeVec A hA x y u v ρ k))
          / Matrix.dotProduct
            (twoEdgeVec A hA x y u v ρ k) (twoEdgeVec A hA x y u v ρ k) := by
      rw [rayleigh, if_neg hne, quadForm_smul_one_sub]
    have e2 : (((d : ℕ) : ℝ) * Matrix.dotProduct
          (twoEdgeVec A hA x y u v ρ k) (twoEdgeVec A hA x y u v ρ k)
          - quadForm A (twoEdgeVec A hA x y u v ρ k))
        / Matrix.dotProduct
          (twoEdgeVec A hA x y u v ρ k) (twoEdgeVec A hA x y u v ρ k)
        = ((d : ℕ) : ℝ)
          - quadForm A (twoEdgeVec A hA x y u v ρ k)
            / Matrix.dotProduct
              (twoEdgeVec A hA x y u v ρ k) (twoEdgeVec A hA x y u v ρ k) := by
      field_simp [hdpos.ne']
    have e3 : rayleigh A (twoEdgeVec A hA x y u v ρ k)
        = quadForm A (twoEdgeVec A hA x y u v ρ k)
          / Matrix.dotProduct
            (twoEdgeVec A hA x y u v ρ k) (twoEdgeVec A hA x y u v ρ k) := by
      rw [rayleigh, if_neg hne]
    rw [e1, e2, e3]
  have hray := twoEdgeVec_rayleigh_ge h01 hxy hedge huv hedge2 hd1 htb1 htb2
    hrho hρ hdis0 hdis1
  rw [hrayM] at heng
  linarith

end TwoEdge

/-!
## Step 5: the diameter-dependent single-graph statement

The program's packaging step: Nilli's bound with the decay factor
instantiated at its d-regular-tree value `ρ = √(d−1)⁻¹`, the
far-apart-to-diameter bridge, and the honest classical error shape.
The statement form is deliberately hypothesis-carrying — the tree-ball
and far-apart hypotheses are real constraints on a specific graph (the
qualification trap this proposal documents), never derived from the
diameter.
-/

section Packaging

variable {A : WAdj (V := V)} {hA : A.IsSymm}

omit [DecidableEq V] in
/-- The `√` plumbing of the packaging: at the d-regular-tree
normalization `ρ = √((d−1)⁻¹)`, the growth factor `(d−1)` times `ρ` is
exactly the spectral radius `√(d−1)`. Hypothesis-free — at `x ≤ 0`
both `√`-terms are `0`, so the junk cases agree. -/
theorem mul_sqrt_inv_eq_sqrt (x : ℝ) :
    x * Real.sqrt (x ⁻¹) = Real.sqrt x := by
  rw [Real.sqrt_inv, ← div_eq_mul_inv, Real.div_sqrt]

omit [DecidableEq V] in
/-- **The far-apart-to-diameter bridge** (the piece Step 2 priced and
deferred): on connected input every cross-endpoint distance of two
edges is bounded by the support graph's diameter. Mathlib's
`SimpleGraph.dist_le_diam` demands an `ediam ≠ ⊤` supplier; on a
finite connected graph the finiteness-attainment lemma
`exists_edist_eq_ediam_of_finite` exhibits the supremum at an actual
vertex pair, where connectivity supplies `edist_ne_top_iff_reachable`.
This is what converts the two-edge method's separation hypothesis into
the diameter-dependent error term of the classical statement. -/
theorem distEdge_le_diam (x y u v : V)
    (hconn : (supportGraph A hA).Connected) :
    distEdge A hA x y u v ≤ (supportGraph A hA).diam := by
  haveI : Nonempty V := ⟨x⟩
  have hne : (supportGraph A hA).ediam ≠ ⊤ := by
    obtain ⟨p, q, hpq⟩ := (supportGraph A hA).exists_edist_eq_ediam_of_finite
    rw [← hpq]
    exact SimpleGraph.edist_ne_top_iff_reachable.2 (hconn p q)
  have h1 : (supportGraph A hA).dist x u ≤ (supportGraph A hA).diam :=
    (supportGraph A hA).dist_le_diam hne
  have h2 : (supportGraph A hA).dist x v ≤ (supportGraph A hA).diam :=
    (supportGraph A hA).dist_le_diam hne
  have h3 : (supportGraph A hA).dist y u ≤ (supportGraph A hA).diam :=
    (supportGraph A hA).dist_le_diam hne
  have h4 : (supportGraph A hA).dist y v ≤ (supportGraph A hA).diam :=
    (supportGraph A hA).dist_le_diam hne
  simp only [distEdge] at *
  omega

omit [DecidableEq V] in
/-- **The diameter bookkeeping of the two-edge method**: whenever the
far-apart hypothesis holds at radius `k + 1`, the diameter is at least
`2 (k + 1) + 1` — equivalently `k + 1 ≤ ⌊diam/2⌋`. This is the honest
hypothesis-side reading of the classical error term
`O(1/⌊diam/2⌋)`: the diameter bounds the *range* of usable `k` (the
error decreases as `k` grows); it never supplies the tree-ball
hypothesis, which stays a genuine constraint on the specific graph. -/
theorem alonBoppana_diam_ge {k : ℕ} {x y u v : V}
    (hconn : (supportGraph A hA).Connected)
    (hfar : (k + 1) + (k + 1) < distEdge A hA x y u v) :
    2 * (k + 1) + 1 ≤ (supportGraph A hA).diam := by
  have h1 := distEdge_le_diam x y u v hconn
  omega

/-- **Nilli's two-edge bound, the `√`-packaged statement** — the
program's capstone. Under exactly the Step-4 hypotheses, with the
decay factor instantiated at its d-regular-tree value
`ρ = √((d−1)⁻¹)` (the `IsDRegular` `d : ℝ` / `IsTreeBall` `d : ℕ`
join already carried by the interface), the second eigenvalue of the
shifted adjacency operator `d • 1 − A` — the Laplacian of a d-regular
graph — is at most `d − (1 + 2k√(d−1))/(k + 1)`. As `k → ∞` this is
Alon–Boppana's `2√(d−1)` barrier; the error term is explicit and
honest. -/
theorem alonBoppana_nilli {d k : ℕ} {x y u v : V}
    (h01 : ∀ i j, A i j = 0 ∨ 1 ≤ A i j)
    (hd : IsDRegular A ((d : ℕ) : ℝ))
    (hxy : x ≠ y) (hedge : A x y ≠ 0) (huv : u ≠ v) (hedge2 : A u v ≠ 0)
    (hconn : (supportGraph A hA).Connected)
    (hfar : (k + 1) + (k + 1) < distEdge A hA x y u v)
    (hd1 : 1 < d) (htb1 : IsTreeBall A hA x y d (k + 1))
    (htb2 : IsTreeBall A hA u v d (k + 1))
    (hcard : 2 ≤ Fintype.card V) :
    secondEval (((d : ℕ) : ℝ) • (1 : Matrix V V ℝ) - A)
        (smul_one_sub_isSymm hA ((d : ℕ) : ℝ)) hcard
      ≤ ((d : ℕ) : ℝ)
          - (1 + 2 * (k : ℝ) * Real.sqrt ((d - 1 : ℕ) : ℝ)) / ((k : ℝ) + 1) := by
  have hρ : (0 : ℝ) ≤ Real.sqrt (((d - 1 : ℕ) : ℝ) ⁻¹) := Real.sqrt_nonneg _
  have hrho : Real.sqrt (((d - 1 : ℕ) : ℝ) ⁻¹) ^ 2 = ((d - 1 : ℕ) : ℝ) ⁻¹ :=
    Real.sq_sqrt (inv_nonneg.2 (Nat.cast_nonneg _))
  have h := twoEdgeVec_secondEval_le h01 hd hxy hedge huv hedge2 hconn hfar hd1
    htb1 htb2 hrho hρ hcard
  have hkey : ((d - 1 : ℕ) : ℝ) * Real.sqrt (((d - 1 : ℕ) : ℝ) ⁻¹)
      = Real.sqrt ((d - 1 : ℕ) : ℝ) := mul_sqrt_inv_eq_sqrt _
  have hassoc : 2 + 4 * (k : ℝ) * ((d - 1 : ℕ) : ℝ)
        * Real.sqrt (((d - 1 : ℕ) : ℝ) ⁻¹)
      = 2 + 4 * (k : ℝ)
          * (((d - 1 : ℕ) : ℝ) * Real.sqrt (((d - 1 : ℕ) : ℝ) ⁻¹)) := by ring
  rw [hassoc, hkey] at h
  have hk : ((k : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  have hconv : (2 + 4 * (k : ℝ) * Real.sqrt ((d - 1 : ℕ) : ℝ))
        / (2 * ((k : ℝ) + 1))
      = (1 + 2 * (k : ℝ) * Real.sqrt ((d - 1 : ℕ) : ℝ)) / ((k : ℝ) + 1) := by
    field_simp
    ring
  rw [hconv] at h
  exact h

/-- **The classical error shape**: the same statement with the error
term isolated as `2√(d−1)/(k + 1)` — the single-graph, honest form of
`λ₂ ≥ 2√(d−1) − O(1/⌊diam/2⌋)` (in Laplacian form; combine with
`alonBoppana_diam_ge`, which bounds the usable `k` by the diameter).
Weaker than `alonBoppana_nilli` by exactly `1/(k + 1)`, stated at the
shape the literature quotes. -/
theorem alonBoppana_nilli_classical {d k : ℕ} {x y u v : V}
    (h01 : ∀ i j, A i j = 0 ∨ 1 ≤ A i j)
    (hd : IsDRegular A ((d : ℕ) : ℝ))
    (hxy : x ≠ y) (hedge : A x y ≠ 0) (huv : u ≠ v) (hedge2 : A u v ≠ 0)
    (hconn : (supportGraph A hA).Connected)
    (hfar : (k + 1) + (k + 1) < distEdge A hA x y u v)
    (hd1 : 1 < d) (htb1 : IsTreeBall A hA x y d (k + 1))
    (htb2 : IsTreeBall A hA u v d (k + 1))
    (hcard : 2 ≤ Fintype.card V) :
    secondEval (((d : ℕ) : ℝ) • (1 : Matrix V V ℝ) - A)
        (smul_one_sub_isSymm hA ((d : ℕ) : ℝ)) hcard
      ≤ ((d : ℕ) : ℝ) - 2 * Real.sqrt ((d - 1 : ℕ) : ℝ)
          + 2 * Real.sqrt ((d - 1 : ℕ) : ℝ) / ((k : ℝ) + 1) := by
  have h := alonBoppana_nilli h01 hd hxy hedge huv hedge2 hconn hfar hd1
    htb1 htb2 hcard
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  have key : 2 * Real.sqrt ((d - 1 : ℕ) : ℝ)
      - 2 * Real.sqrt ((d - 1 : ℕ) : ℝ) / ((k : ℝ) + 1)
      ≤ (1 + 2 * (k : ℝ) * Real.sqrt ((d - 1 : ℕ) : ℝ)) / ((k : ℝ) + 1) := by
    have h' : (1 + 2 * (k : ℝ) * Real.sqrt ((d - 1 : ℕ) : ℝ)) / ((k : ℝ) + 1)
        - (2 * Real.sqrt ((d - 1 : ℕ) : ℝ)
            - 2 * Real.sqrt ((d - 1 : ℕ) : ℝ) / ((k : ℝ) + 1))
        = 1 / ((k : ℝ) + 1) := by
      field_simp
      ring
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := one_div_pos.2 hk
    linarith
  linarith

end Packaging

/-!
## The expansion ceiling — the Alon–Boppana × Cheeger composition

`proposals/ramanujan-expansion-ceiling.md` (delivered 2026-08-27):
the program's capstone paired with the delivered Cheeger hard
direction, producing the field's actual textbook payoff sentence — an
explicit numerical ceiling on how good an expander any d-regular graph
satisfying Alon–Boppana's hypotheses can be. The two source theorems
live on linearly related operators (`d • 1 − A` vs
`regularNormalizedLaplacian A d`); the join is the exact scaling
engine `secondEval_smul_of_pos` plus one operator identity.

Scope (a hard acceptance-bar item of the proposal, not a style note):
this is the obstruction/ceiling direction only. Nothing here says the
ceiling is *tight* or *attained* by any graph or family — that is the
separate Ramanujan-graph construction/existence program, and no
delivery record, docstring, or summary may describe this result as
showing tightness.
-/
section ExpansionCeiling

variable {A : WAdj (V := V)} {hA : A.IsSymm}

/-- Under `d`-regularity with `d ≠ 0`, the shifted adjacency operator
of the Alon–Boppana statements IS the positive-scaled
regular-normalized Laplacian of the Cheeger statements:
`d • 1 − A = d • L_sym`. The half of the identity not already on file
(`smul_regularNormalizedLaplacian` covers `d • L_sym = laplacian A`)
is that the degree matrix of a regular graph is `d • 1`. -/
theorem smul_one_sub_eq_smul_regularNormalizedLaplacian {d : ℕ}
    (hd : IsDRegular A ((d : ℕ) : ℝ)) (hdne : ((d : ℕ) : ℝ) ≠ 0) :
    ((d : ℕ) : ℝ) • (1 : Matrix V V ℝ) - A
      = ((d : ℕ) : ℝ) • regularNormalizedLaplacian A ((d : ℕ) : ℝ) := by
  rw [smul_regularNormalizedLaplacian A ((d : ℕ) : ℝ) hd hdne,
    show laplacian A = degreeMatrix A - A from rfl]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij
    have hdi : degreeMatrix A i i = ((d : ℕ) : ℝ) := by
      rw [degreeMatrix_diagonal, hd i]
    simp [hdi]
  · rw [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, if_neg hij,
      degreeMatrix_off_diagonal _ hij]
    simp

/-- **The Ramanujan expansion ceiling** — the Alon–Boppana bound
composed with the Cheeger hard direction into an explicit ceiling on
expansion quality: under exactly `alonBoppana_nilli_classical`'s
hypotheses,
`cheegerConstant A ≤ √(2 (1 − 2√(d−1)/d + 2√(d−1)/(d (k+1))))`.

This is the sentence every spectral graph theory course states
immediately after proving Alon–Boppana: no d-regular graph satisfying
these hypotheses can have conductance above this explicit value — the
expansion-obstruction half of the textbook picture. It is *not* a
tightness or attainment claim (see the section scope note).

Route (mechanical, two compositions): the operator identity
transports the Alon–Boppana upper bound on
`secondEval (d • 1 − A)` onto `d • L_sym` (`secondEval_congr`);
`secondEval_smul_of_pos` divides out the `d`, bounding
`secondEval L_sym` by `1 − 2√(d−1)/d + 2√(d−1)/(d (k+1))`; the Cheeger
hard direction `cheegerConstant² / 2 ≤ secondEval L_sym` chains below
it, and `Real.sqrt_le_sqrt` at the nonnegative Cheeger constant takes
the root. Every hypothesis of both source theorems is carried
unchanged; `h01` implies Cheeger's `hnonneg` by cases.

QA: `Scaffold/QA/SpectralGraph/AlonBoppana_QA.lean`'s
`abC8_ceiling_instance` (the C₈ instance at `k = 0`, the ceiling
evaluating numerically to `√2`), `abC8_cheegerConstant_le_quarter`
(the fixture's actual Cheeger constant pinned `≤ 1/4` by the exhibited
half-set cut — the ceiling holds with strict slack, non-vacuous, never
tight), and `abC8_ceiling_improves_arith` (the two-`k` improvement as
arithmetic on the statement's own constants at `d = 2`). -/
theorem ramanujan_expansion_ceiling {d k : ℕ} {x y u v : V}
    (h01 : ∀ i j, A i j = 0 ∨ 1 ≤ A i j)
    (hd : IsDRegular A ((d : ℕ) : ℝ))
    (hxy : x ≠ y) (hedge : A x y ≠ 0) (huv : u ≠ v) (hedge2 : A u v ≠ 0)
    (hconn : (supportGraph A hA).Connected)
    (hfar : (k + 1) + (k + 1) < distEdge A hA x y u v)
    (hd1 : 1 < d) (htb1 : IsTreeBall A hA x y d (k + 1))
    (htb2 : IsTreeBall A hA u v d (k + 1))
    (hcard : 2 ≤ Fintype.card V) :
    cheegerConstant A ≤ Real.sqrt (2 * (1 - 2 * Real.sqrt ((d - 1 : ℕ) : ℝ)
        / ((d : ℕ) : ℝ)
      + 2 * Real.sqrt ((d - 1 : ℕ) : ℝ)
        / (((d : ℕ) : ℝ) * ((k : ℝ) + 1)))) := by
  have hnn : ∀ i j, 0 ≤ A i j := by
    intro i j
    rcases h01 i j with h | h
    · rw [h]
    · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) h
  have hdreal : ∀ i, deg A i = ((d : ℕ) : ℝ) := hd
  have hdpos : (0 : ℝ) < ((d : ℕ) : ℝ) :=
    Nat.cast_pos.2 (by omega)
  have hLsym := regularNormalizedLaplacian_symmetric A hA ((d : ℕ) : ℝ)
  -- the Alon–Boppana side, transported onto the `d • L_sym` spelling
  have hAB0 := alonBoppana_nilli_classical h01 hd hxy hedge huv hedge2 hconn
    hfar hd1 htb1 htb2 hcard
  have hop := smul_one_sub_eq_smul_regularNormalizedLaplacian hd hdpos.ne'
  have hbridge : secondEval (((d : ℕ) : ℝ) • (1 : Matrix V V ℝ) - A)
      (smul_one_sub_isSymm hA ((d : ℕ) : ℝ)) hcard
      = secondEval (((d : ℕ) : ℝ) • regularNormalizedLaplacian A ((d : ℕ) : ℝ))
        (smul_isSymm hLsym ((d : ℕ) : ℝ)) hcard :=
    secondEval_congr _ _ hop hcard
  rw [hbridge] at hAB0
  have hsc : secondEval (((d : ℕ) : ℝ) • regularNormalizedLaplacian A ((d : ℕ) : ℝ))
      (smul_isSymm hLsym ((d : ℕ) : ℝ)) hcard
      = ((d : ℕ) : ℝ) * secondEval (regularNormalizedLaplacian A ((d : ℕ) : ℝ))
          hLsym hcard :=
    secondEval_smul_of_pos hLsym
      (regularNormalizedLaplacian_psd A hA hnn ((d : ℕ) : ℝ) hdreal hdpos)
      (regularNormalizedLaplacian_mulVec_onesVec A ((d : ℕ) : ℝ) hdreal
        hdpos.ne') hcard hdpos
  rw [hsc] at hAB0
  -- the Cheeger side
  have hch := cheeger_lower_bound A hA hnn ((d : ℕ) : ℝ) hdreal hdpos hcard
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  set s := Real.sqrt ((d - 1 : ℕ) : ℝ)
  -- φ² ≤ 2 * (the ceiling's radicand)
  have h2 : cheegerConstant A ^ 2 ≤ 2 * (1 - 2 * s / ((d : ℕ) : ℝ)
      + 2 * s / (((d : ℕ) : ℝ) * ((k : ℝ) + 1))) := by
    have h2lam : 2 * secondEval (regularNormalizedLaplacian A ((d : ℕ) : ℝ))
        hLsym hcard
        ≤ 2 * (((d : ℕ) : ℝ) - 2 * s + 2 * s / ((k : ℝ) + 1))
          / ((d : ℕ) : ℝ) := by
      rw [le_div_iff₀ hdpos]
      calc 2 * secondEval (regularNormalizedLaplacian A ((d : ℕ) : ℝ)) hLsym hcard
            * ((d : ℕ) : ℝ)
          = 2 * (((d : ℕ) : ℝ) * secondEval
              (regularNormalizedLaplacian A ((d : ℕ) : ℝ)) hLsym hcard) := by
              ring
        _ ≤ 2 * (((d : ℕ) : ℝ) - 2 * s + 2 * s / ((k : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hAB0 (by norm_num)
    have hsplit : cheegerConstant A ^ 2
        = 2 * (cheegerConstant A ^ 2 / 2) := by field_simp
    have hident : 2 * (((d : ℕ) : ℝ) - 2 * s + 2 * s / ((k : ℝ) + 1))
        / ((d : ℕ) : ℝ)
        = 2 * (1 - 2 * s / ((d : ℕ) : ℝ)
          + 2 * s / (((d : ℕ) : ℝ) * ((k : ℝ) + 1))) := by
      field_simp
      ring
    rw [hsplit, ← hident]
    exact le_trans (mul_le_mul_of_nonneg_left hch (by norm_num)) h2lam
  -- take the square root
  have hφnn : 0 ≤ cheegerConstant A := cheegerConstant_nonneg A hnn
  rw [← Real.sqrt_sq hφnn]
  exact Real.sqrt_le_sqrt h2

end ExpansionCeiling

section CycleFamily

/-!
## The cycle family: the asymptotic Alon–Boppana corollary

The d-regular family the program's completion note asked for
("needs a named d-regular family with `diam → ∞`"): the cycles
`C_n`, carried by Mathlib's own `SimpleGraph.cycleGraph n` through the
delivered `toWAdj` adapter. The new mathematical content is the exact
cycle distance formula — the walk route up, the integer-potential
route down — from which the tree-ball hypothesis and the far-apart
condition discharge at arbitrary scale, and the two-edge machinery
yields `λ₂(C_{4k+8}) ≤ 1/(k+1) → 0`: the Alon–Boppana error term
attained on the canonical 2-regular family.
-/

/-! ### Cyclic `Fin` arithmetic helpers

`(z - a).val` (cyclic `Fin` subtraction) is a complete invariant of
`z` modulo translation by `a`: it decomposes (`fin_val_decomp`),
injects (`fin_eq_of_val_sub_eq`), and its arithmetic reduces to
`omega`-friendly decompositions through `mod_decomp`. -/

private theorem mod_decomp {n : ℕ} {X c : ℕ} (hc : c < n)
    (h : ∃ q : ℕ, X = c + q * n) : X % n = c := by
  obtain ⟨q, rfl⟩ := h
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

/-- The definitional form of cyclic `Fin` subtraction. -/
private theorem fin_val_sub_eq {n : ℕ} (a b : Fin n) :
    (a - b).val = (n - b.val + a.val) % n := by
  simp [Fin.sub_def]

private theorem fin_val_sub_of_le {n : ℕ} {x y : Fin n} (h : y.val ≤ x.val) :
    (x - y).val = x.val - y.val := by
  have hx := x.isLt
  have hX : ∃ q : ℕ, n - y.val + x.val = (x.val - y.val) + q * n := ⟨1, by omega⟩
  rw [fin_val_sub_eq, mod_decomp (by omega) hX]

/-- Adding then subtracting the same amount on the cycle is the
identity: the decomposition half of the invariant. -/
private theorem fin_val_sub_add_self {n : ℕ} (a : Fin n) {c : ℕ} (hc : c < n) :
    (a + ⟨c, hc⟩ - a).val = c := by
  have ha := a.isLt
  have h1 : (a + ⟨c, hc⟩).val = (a.val + c) % n := by
    simp [Fin.val_add]
  rw [fin_val_sub_eq, h1]
  rcases Nat.lt_or_ge (a.val + c) n with hlt | hge
  · have hX : ∃ q : ℕ, n - a.val + ((a.val + c) % n) = c + q * n := by
      rw [Nat.mod_eq_of_lt hlt]
      exact ⟨1, by omega⟩
    rw [mod_decomp hc hX]
  · rw [Nat.mod_eq_sub_mod hge]
    have hsub : a.val + c - n < n := by omega
    rw [Nat.mod_eq_of_lt hsub]
    have hX : ∃ q : ℕ, n - a.val + (a.val + c - n) = c + q * n := ⟨0, by omega⟩
    rw [mod_decomp hc hX]

/-- Every vertex decomposes through the cyclic difference. -/
private theorem fin_val_decomp {n : ℕ} (a z : Fin n) :
    z = a + ⟨(z - a).val, Fin.isLt _⟩ := by
  have ha := a.isLt
  have hz := z.isLt
  apply Fin.ext
  rw [Fin.val_add, fin_val_sub_eq]
  rcases Nat.lt_or_ge z.val a.val with hlt | hge
  · have hu : n - a.val + z.val < n := by omega
    rw [Nat.mod_eq_of_lt hu]
    have hX : ∃ q : ℕ, a.val + (n - a.val + z.val) = z.val + q * n := ⟨1, by omega⟩
    rw [mod_decomp hz hX]
  · rw [show n - a.val + z.val = n + (z.val - a.val) by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : z.val - a.val < n),
      show a.val + (z.val - a.val) = z.val by omega, Nat.mod_eq_of_lt hz]

/-- The cyclic difference determines the vertex: the injectivity half. -/
private theorem fin_eq_of_val_sub_eq {n : ℕ} {a z w : Fin n}
    (h : (z - a).val = (w - a).val) : z = w := by
  rw [fin_val_decomp a z, fin_val_decomp a w]
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_mk]
  rw [h]

private theorem fin_val_sub_self {n : ℕ} (a : Fin n) : (a - a).val = 0 := by
  have ha := a.isLt
  have hX : ∃ q : ℕ, n - a.val + a.val = 0 + q * n := ⟨1, by omega⟩
  rw [fin_val_sub_eq, mod_decomp (by omega : (0 : ℕ) < n) hX]

/-- The two orientations of the cyclic difference add to `n` (when
nonzero). -/
private theorem fin_val_sub_swap_of_pos {n : ℕ} {a b : Fin n}
    (h : (b - a).val ≠ 0) : (a - b).val = n - (b - a).val := by
  have ha := a.isLt
  have hb := b.isLt
  rcases Nat.lt_or_ge b.val a.val with hlt | hge
  · have hX : ∃ q : ℕ, n - a.val + b.val = (n - a.val + b.val) + q * n :=
      ⟨0, by omega⟩
    have h1 : (b - a).val = n - a.val + b.val :=
      mod_decomp (by omega : n - a.val + b.val < n) hX
    have h2 : (a - b).val = a.val - b.val := fin_val_sub_of_le (by omega)
    rw [h2, h1]
    omega
  · have h1 : (b - a).val = b.val - a.val := fin_val_sub_of_le (by omega)
    have hpos : 0 < b.val - a.val := by rw [← h1]; exact Nat.pos_of_ne_zero h
    have hY : ∃ q : ℕ, n - b.val + a.val = (n - b.val + a.val) + q * n :=
      ⟨0, by omega⟩
    have h2 : (a - b).val = n - b.val + a.val :=
      mod_decomp (by omega : n - b.val + a.val < n) hY
    rw [h2, h1]
    omega

/-- The value of the successor vertex: `1` short of the wrap, `0` at
it. -/
private theorem fin_val_add_one {n : ℕ} [NeZero n] (a : Fin n) :
    (a + 1 : Fin n).val = if a.val + 1 < n then a.val + 1 else 0 := by
  rcases Nat.lt_or_ge (a.val + 1) n with h | h
  · have h1 : (a + 1 : Fin n).val = (a.val + 1) % n := by simp [Fin.val_add]
    rw [h1, Nat.mod_eq_of_lt h, if_pos h]
  · have h1 : (a + 1 : Fin n).val = (a.val + 1) % n := by simp [Fin.val_add]
    have h2 : a.val + 1 = n := by omega
    rw [h1, h2, Nat.mod_self, if_neg (by omega)]

/-- The backward step: `(z − (a+1)).val` from `(z − a).val`. -/
private theorem fin_val_sub_succ {n : ℕ} [NeZero n] (a z : Fin n) :
    (z - (a + 1 : Fin n)).val
      = if (z - a).val = 0 then n - 1 else (z - a).val - 1 := by
  have ha := a.isLt
  have hz := z.isLt
  have hδlt : (z - a).val < n := Fin.isLt _
  obtain ⟨q, hq⟩ : ∃ q : ℕ, n - a.val + z.val = (z - a).val + q * n := by
    obtain ⟨q, hq⟩ : ∃ q : ℕ, (n - a.val + z.val) / n = q := ⟨_, rfl⟩
    have hd := Nat.mod_add_div (n - a.val + z.val) n
    rw [hq, Nat.mul_comm] at hd
    have hsub : (z - a).val = (n - a.val + z.val) % n := fin_val_sub_eq z a
    exact ⟨q, by omega⟩
  rw [fin_val_sub_eq, fin_val_add_one]
  rcases Nat.eq_zero_or_pos (z - a).val with h0 | hpos
  · -- z = a
    have hza : z = a := by
      have : (z - a).val = (a - a).val := by rw [h0, fin_val_sub_self a]
      exact fin_eq_of_val_sub_eq this
    rw [if_pos h0, hza]
    rcases Nat.lt_or_ge (a.val + 1) n with hlt | hge
    · rw [if_pos hlt]
      have hX : ∃ Q : ℕ, n - (a.val + 1) + a.val = (n - 1) + Q * n := ⟨0, by omega⟩
      exact mod_decomp (by omega : n - 1 < n) hX
    · rw [if_neg (by omega)]
      have hX : ∃ Q : ℕ, n - 0 + a.val = (n - 1) + Q * n := ⟨1, by omega⟩
      exact mod_decomp (by omega : n - 1 < n) hX
  · rw [if_neg (by omega : ¬((z - a).val = 0))]
    rcases Nat.lt_or_ge (a.val + 1) n with hlt | hge
    · rw [if_pos hlt]
      have hX : ∃ Q : ℕ, n - (a.val + 1) + z.val = ((z - a).val - 1) + Q * n :=
        ⟨q, by omega⟩
      exact mod_decomp (by omega) hX
    · rw [if_neg (by omega)]
      have hexp : (q + 1) * n = q * n + n := by ring
      have hX : ∃ Q : ℕ, n - 0 + z.val = ((z - a).val - 1) + Q * n :=
        ⟨q + 1, by omega⟩
      exact mod_decomp (by omega) hX

/-! ### The cycle family and its regularity interface -/

/-- The `n`-cycle as a weighted adjacency matrix: Mathlib's
`SimpleGraph.cycleGraph n` through the delivered `toWAdj` adapter —
no duplicated graph model. -/
def cycleAdj (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  SimpleGraph.toWAdj (SimpleGraph.cycleGraph n)

theorem cycleAdj_isSymm (n : ℕ) : (cycleAdj n).IsSymm :=
  SimpleGraph.toWAdj_symm _

theorem cycleAdj_nonneg (n : ℕ) : ∀ i j, 0 ≤ cycleAdj n i j :=
  SimpleGraph.toWAdj_nonneg _

theorem cycleAdj_apply (n : ℕ) (i j : Fin n) :
    cycleAdj n i j = if (SimpleGraph.cycleGraph n).Adj i j then 1 else 0 :=
  SimpleGraph.toWAdj_apply _ i j

/-- Entries are `0` or `1`: the `0`-or-`≥ 1` weight discipline. -/
theorem cycleAdj_h01 (n : ℕ) : ∀ i j, cycleAdj n i j = 0 ∨ 1 ≤ cycleAdj n i j := by
  intro i j
  by_cases h : (SimpleGraph.cycleGraph n).Adj i j
  · rw [cycleAdj_apply, if_pos h]
    exact Or.inr (by norm_num)
  · rw [cycleAdj_apply, if_neg h]
    exact Or.inl rfl

/-- The support graph of the adapter weights is Mathlib's cycle. -/
theorem supportGraph_cycleAdj (n : ℕ) :
    supportGraph (cycleAdj n) (cycleAdj_isSymm n) = SimpleGraph.cycleGraph n :=
  supportGraph_toWAdj_eq_self _

theorem cycleAdj_connected {n : ℕ} (hn : 1 ≤ n) :
    (supportGraph (cycleAdj n) (cycleAdj_isSymm n)).Connected := by
  rw [supportGraph_cycleAdj]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  exact SimpleGraph.cycleGraph_connected

theorem cycleAdj_isDRegular {n : ℕ} (hn : 3 ≤ n) :
    IsDRegular (cycleAdj n) 2 := by
  intro i
  have hdeg : deg (SimpleGraph.toWAdj (SimpleGraph.cycleGraph n)) i
      = ((SimpleGraph.cycleGraph n).degree i : ℝ) := deg_toWAdj _ i
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show cycleAdj (m + 3) = SimpleGraph.toWAdj (SimpleGraph.cycleGraph (m + 3)) from rfl,
    hdeg, SimpleGraph.cycleGraph_degree_three_le]
  norm_num

/-! ### The exact cycle distance formula -/

/-- Consecutive vertices around the cycle are adjacent. -/
private theorem cycleGraph_adj_add_one {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (a : Fin n) :
    (SimpleGraph.cycleGraph n).Adj a (a + 1) := by
  have ha := a.isLt
  rw [SimpleGraph.cycleGraph_adj']
  right
  rw [fin_val_sub_eq, fin_val_add_one]
  rcases Nat.lt_or_ge (a.val + 1) n with hlt | hge
  · rw [if_pos hlt]
    have hX : ∃ q : ℕ, n - a.val + (a.val + 1) = 1 + q * n := ⟨1, by omega⟩
    exact mod_decomp (by omega : (1 : ℕ) < n) hX
  · rw [if_neg (by omega), show n - a.val + 0 = 1 by omega,
      Nat.mod_eq_of_lt (by omega : (1 : ℕ) < n)]

/-- The up-route bound: walking forward is a genuine route, so the
distance to the `c`-steps-forward vertex is at most `c` — by induction
appending one adjacency step at a time. -/
private theorem cycleGraph_dist_le_up {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (hconn : (SimpleGraph.cycleGraph n).Connected) (a : Fin n) :
    ∀ c : ℕ, (hc : c < n) →
      (SimpleGraph.cycleGraph n).dist a (a + ⟨c, by omega⟩) ≤ c := by
  intro c
  induction c with
  | zero =>
    intro _
    have h0 : ∀ P : (0 : ℕ) < n, a + ⟨0, P⟩ = a := by
      intro P
      apply Fin.ext
      have hval := a.isLt
      simp only [Fin.val_add, Fin.val_mk, Nat.add_zero, Nat.mod_eq_of_lt hval]
    rw [h0 _]
    exact le_of_eq (by simp)
  | succ c ih =>
    intro hc
    have hstep : (SimpleGraph.cycleGraph n).Adj (a + ⟨c, by omega⟩)
        (a + ⟨c + 1, by omega⟩) := by
      have h := cycleGraph_adj_add_one hn (a + ⟨c, by omega⟩)
      have hkey : (a + ⟨c, by omega⟩) + 1 = a + ⟨c + 1, by omega⟩ := by
        apply Fin.ext
        have hvo : (1 : Fin n).val = 1 % n := Fin.val_one' n
        have h2 : 2 ≤ n := hn
        have e1 : (1 : Fin n).val = 1 := by
          rw [hvo, Nat.mod_eq_of_lt (by omega : (1 : ℕ) < n)]
        simp only [Fin.val_add, Fin.val_mk, e1, Nat.mod_add_mod, Nat.add_assoc]
      rwa [hkey] at h
    have h1 : (SimpleGraph.cycleGraph n).dist (a + ⟨c, by omega⟩)
        (a + ⟨c + 1, by omega⟩) ≤ 1 :=
      SimpleGraph.dist_le (SimpleGraph.Walk.cons hstep SimpleGraph.Walk.nil)
    have h2 := hconn.dist_triangle (u := a) (v := (a + ⟨c, by omega⟩))
      (w := (a + ⟨c + 1, by omega⟩))
    have h3 := ih (by omega : c < n)
    omega

/-- The distance on the cycle is at most each orientation's step
count. -/
private theorem cycleGraph_dist_le_delta {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (a b : Fin n) :
    (SimpleGraph.cycleGraph n).dist a b ≤ (b - a).val := by
  have hconn : (SimpleGraph.cycleGraph n).Connected := by
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
    exact SimpleGraph.cycleGraph_connected
  have hδlt := (b - a).isLt
  have h := cycleGraph_dist_le_up hn hconn a (b - a).val hδlt
  have hb : a + ⟨(b - a).val, hδlt⟩ = b := (fin_val_decomp a b).symm
  calc (SimpleGraph.cycleGraph n).dist a b
      = (SimpleGraph.cycleGraph n).dist a (a + ⟨(b - a).val, hδlt⟩) := by rw [hb]
    _ ≤ (b - a).val := h

/-- The integer-potential invariant: every walk realizes a residue
representative of `b − start` of absolute value at most its length. -/
private theorem cycle_walk_potential {n : ℕ} [NeZero n] (hn : 2 ≤ n) (b : Fin n) :
    ∀ (a : Fin n) (p : (SimpleGraph.cycleGraph n).Walk a b),
      ∃ s : ℤ, |s| ≤ p.length ∧ ∃ t : ℤ, ((b : ℤ) - (a : ℤ)) = s + (n : ℤ) * t := by
  have stepFac : ∀ u w : Fin n, (w - u).val = 1 →
      ∃ r : ℤ, ((w : ℤ) - (u : ℤ)) = 1 + (n : ℤ) * r := by
    intro u w h
    have hc : ((w - u : Fin n) : ℤ) = (((w : ℤ) - (u : ℤ)) % (n : ℤ)) :=
      Fin.coe_int_sub_eq_mod w u
    have hv : ((w - u : Fin n) : ℤ) = 1 := by exact_mod_cast h
    have hlt : (1 : ℤ) < (n : ℤ) := by
      have := (w - u).isLt
      have h2 : 2 ≤ n := hn
      omega
    rw [hv] at hc
    refine Int.modEq_iff_add_fac.1 ?_
    show (1 : ℤ) % (n : ℤ) = ((w : ℤ) - (u : ℤ)) % (n : ℤ)
    rw [Int.emod_eq_of_lt (by norm_num) (by omega : (1 : ℤ) < (n : ℤ))]
    exact hc
  intro a p
  induction p with
  | nil =>
    refine ⟨0, by simp, 0, by simp⟩
  | @cons u w b hadj tail ih =>
    obtain ⟨s, hslen, t, ht⟩ := ih
    rw [SimpleGraph.cycleGraph_adj'] at hadj
    -- (b − u) = (b − w) + (w − u) in every case; the step contributes ±1
    have hsplit : ((b : ℤ) - (u : ℤ))
        = ((b : ℤ) - (w : ℤ)) + ((w : ℤ) - (u : ℤ)) := by ring
    have habs := abs_le.1 (le_refl (|s|))
    rcases hadj with h | h
    · -- (u − w).val = 1 : the step moves the potential down by 1
      obtain ⟨r, hr⟩ := stepFac w u h
      have hr' : ((w : ℤ) - (u : ℤ)) = (-1 : ℤ) + (n : ℤ) * (-r) := by
        have hwu : ((w : ℤ) - (u : ℤ)) = -(((u : ℤ)) - ((w : ℤ))) := by ring
        rw [hwu, hr]
        ring
      refine ⟨s - 1, ?_, t - r, ?_⟩
      · have hlen : (SimpleGraph.Walk.cons hadj tail).length = tail.length + 1 := rfl
        rw [abs_le]
        constructor <;> linarith
      · rw [hsplit, ht, hr']
        ring
    · -- (w − u).val = 1 : the step moves the potential up by 1
      obtain ⟨r, hr⟩ := stepFac u w h
      refine ⟨s + 1, ?_, t + r, ?_⟩
      · have hlen : (SimpleGraph.Walk.cons hadj tail).length = tail.length + 1 := rfl
        rw [abs_le]
        constructor <;> linarith
      · rw [hsplit, ht, hr]
        ring

/-- **The integer-potential lower bound**: any walk from `a` to `b`
on the cycle is at least the cyclic distance
`min ((b-a).val) (n - (b-a).val)` long. Each step moves the integer
potential `b - start` by `±1` up to a multiple of `n`, so a walk of
length `L` realizes a residue representative of absolute value at
most `L`. -/
private theorem cycleGraph_walk_length_ge {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (a b : Fin n)
    (p : (SimpleGraph.cycleGraph n).Walk a b) :
    min ((b - a).val) (n - (b - a).val) ≤ p.length := by
  have hnpos : (0 : ℤ) < (n : ℤ) := by
    have : 0 < n := NeZero.pos n
    omega
  obtain ⟨s, hslen, t, ht⟩ := cycle_walk_potential hn b a p
  have hcform : ((b : ℤ) - (a : ℤ)) = ((b - a).val : ℤ) ∨
      ((b : ℤ) - (a : ℤ)) = ((b - a).val : ℤ) - (n : ℤ) := by
    rcases Nat.lt_or_ge b.val a.val with hlt | hge
    · have hb := b.isLt
      have ha := a.isLt
      have hX : ∃ q : ℕ, n - a.val + b.val = (n - a.val + b.val) + q * n :=
        ⟨0, by omega⟩
      have h1 : (b - a).val = n - a.val + b.val :=
        mod_decomp (by omega : n - a.val + b.val < n) hX
      rw [h1]
      omega
    · have h1 : (b - a).val = b.val - a.val := fin_val_sub_of_le (by omega)
      rw [h1]
      omega
  have hδlt : (b - a).val < n := Fin.isLt _
  have hδlt' : (((b - a).val : ℤ)) < ((n : ℤ)) := by exact_mod_cast hδlt
  have hprod : ∀ u : ℤ, (1 : ℤ) ≤ u → ((n : ℤ)) ≤ (n : ℤ) * u := by
    intro u _
    have h1 : (n : ℤ) * (u - 1) ≥ 0 := Int.mul_nonneg (by omega) (by omega)
    linarith [show ((n : ℤ)) * u = (n : ℤ) + (n : ℤ) * (u - 1) by ring]
  have hZ : ((min ((b - a).val) (n - (b - a).val) : ℕ) : ℤ) ≤ |s| := by
    have hcast : ((min ((b - a).val) (n - (b - a).val) : ℕ) : ℤ)
        = min ((b - a).val : ℤ) ((n : ℤ) - ((b - a).val : ℤ)) := by
      push_cast [Nat.cast_min, Nat.cast_sub (Nat.le_of_lt hδlt)]
      rfl
    rw [hcast]
    have hminL : min ((b - a).val : ℤ) ((n : ℤ) - ((b - a).val : ℤ))
        ≤ ((b - a).val : ℤ) := Int.min_le_left _ _
    have hminR : min ((b - a).val : ℤ) ((n : ℤ) - ((b - a).val : ℤ))
        ≤ ((n : ℤ) - ((b - a).val : ℤ)) := Int.min_le_right _ _
    have hnt0 : ∀ u : ℤ, u ≤ 0 → (n : ℤ) * u ≤ 0 := by
      intro u _
      have hx0 : (n : ℤ) * (-u) ≥ 0 := Int.mul_nonneg (by omega) (by omega)
      linarith [show (n : ℤ) * u = -((n : ℤ) * (-u)) by ring]
    rcases hcform with hc | hc
    · -- s = δ − n*t
      have hst : s = ((b - a).val : ℤ) - (n : ℤ) * t := by linarith
      rcases lt_or_ge ((n : ℤ) * t) ((b - a).val : ℤ) with h1 | h1
      · -- n*t < δ : t ≤ 0, so n*t ≤ 0 and s = δ − n*t ≥ δ ≥ min
        have ht0 : t ≤ 0 := by
          by_contra hcon
          have hnt1 : (n : ℤ) ≤ (n : ℤ) * t := hprod t (by omega)
          omega
        have hx := hnt0 t ht0
        rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ s)]
        omega
      · -- δ ≤ n*t : s ≤ 0
        rcases lt_trichotomy t 0 with htn | hte | htp
        · -- t < 0 : n*t ≤ 0 ≤ δ ≤ n*t forces δ = 0, and |s| ≥ 0 ≥ min
          have hx := hnt0 t (by omega)
          have hδ0 : ((b - a).val : ℤ) = 0 := by omega
          have hmin0 : min ((b - a).val : ℤ) ((n : ℤ) - ((b - a).val : ℤ))
              ≤ (0 : ℤ) := by
            rw [hδ0]
            exact Int.min_le_left (0 : ℤ) ((n : ℤ) - 0)
          exact le_trans hmin0 (abs_nonneg s)
        · subst hte
          have hz : (n : ℤ) * 0 = 0 := by ring
          have hδ0 : ((b - a).val : ℤ) = 0 := by omega
          have hs0 : s = 0 := by omega
          rw [hs0, abs_zero, hδ0]
          simp
        · have hnt1 : (n : ℤ) ≤ (n : ℤ) * t := hprod t (by omega)
          rw [abs_of_nonpos (by omega : s ≤ 0)]
          omega
    · -- s = δ − n − n*t = δ − n(1+t)
      have hst : s = ((b - a).val : ℤ) - (n : ℤ) - (n : ℤ) * t := by linarith
      have hrew : ((n : ℤ)) * (1 + t) = (n : ℤ) + (n : ℤ) * t := by ring
      rcases lt_or_ge ((n : ℤ) * (1 + t)) ((b - a).val : ℤ) with h1 | h1
      · -- n(1+t) < δ : 1+t ≤ 0, so n(1+t) ≤ 0 and s ≥ δ ≥ min
        have hu0 : 1 + t ≤ 0 := by
          by_contra hcon
          have hnt1 : (n : ℤ) ≤ (n : ℤ) * (1 + t) := hprod (1 + t) (by omega)
          omega
        have hx := hnt0 (1 + t) hu0
        rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ s)]
        omega
      · -- δ ≤ n(1+t) : s ≤ 0
        rcases lt_trichotomy (1 + t) 0 with htn | hte | htp
        · -- 1+t < 0 : forces δ = 0, and |s| ≥ 0 ≥ min
          have hx := hnt0 (1 + t) (by omega)
          have hδ0 : ((b - a).val : ℤ) = 0 := by omega
          have hmin0 : min ((b - a).val : ℤ) ((n : ℤ) - ((b - a).val : ℤ))
              ≤ (0 : ℤ) := by
            rw [hδ0]
            exact Int.min_le_left (0 : ℤ) ((n : ℤ) - 0)
          exact le_trans hmin0 (abs_nonneg s)
        · have hz2 : (n : ℤ) * (1 + t) = 0 := by rw [hte, mul_zero]
          have hδ0 : ((b - a).val : ℤ) = 0 := by omega
          have hs0 : s = 0 := by omega
          rw [hs0, abs_zero, hδ0]
          simp
        · have hnt1 : (n : ℤ) ≤ (n : ℤ) * (1 + t) := hprod (1 + t) (by omega)
          rw [abs_of_nonpos (by omega : s ≤ 0)]
          omega
  exact Nat.cast_le.1 (le_trans hZ hslen)

/-- **The sInf half of the distance formula**: every walk is at least
the cyclic distance long, so the infimum of walk lengths is too. -/
private theorem cycleGraph_dist_ge_min {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (hconn : (SimpleGraph.cycleGraph n).Connected) (a b : Fin n) :
    min ((b - a).val) (n - (b - a).val) ≤ (SimpleGraph.cycleGraph n).dist a b := by
  rw [SimpleGraph.dist_eq_sInf]
  obtain ⟨w⟩ : Nonempty ((SimpleGraph.cycleGraph n).Walk a b) := hconn.preconnected a b
  refine le_csInf ⟨w.length, ⟨w, rfl⟩⟩ ?_
  rintro x ⟨p, rfl⟩
  exact cycleGraph_walk_length_ge hn a b p

/-- **The exact cycle distance**: the BFS distance between two
vertices of the cycle is the shorter of the two orientation step
counts. -/
theorem cycleAdj_dist_eq {n : ℕ} (hn : 2 ≤ n) (a b : Fin n) :
    (supportGraph (cycleAdj n) (cycleAdj_isSymm n)).dist a b
      = min ((b - a).val) (n - (b - a).val) := by
  haveI : NeZero n := ⟨by omega⟩
  have hconn : (SimpleGraph.cycleGraph n).Connected := by
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
    exact SimpleGraph.cycleGraph_connected
  rw [supportGraph_cycleAdj]
  refine le_antisymm ?_ ?_
  · have h1 : (SimpleGraph.cycleGraph n).dist a b ≤ (b - a).val :=
      cycleGraph_dist_le_delta hn a b
    have h2 : (SimpleGraph.cycleGraph n).dist a b ≤ n - (b - a).val := by
      rcases Nat.eq_zero_or_pos (b - a).val with h0 | hpos
      · have hba : b = a := by
          have : (b - a).val = (a - a).val := by rw [h0, fin_val_sub_self a]
          exact fin_eq_of_val_sub_eq this
        rw [hba]
        have hd0 : (SimpleGraph.cycleGraph n).dist a a = 0 := SimpleGraph.dist_self
        have haa : (a - a).val = 0 := fin_val_sub_self a
        omega
      · have hswap : (a - b).val = n - (b - a).val := fin_val_sub_swap_of_pos hpos.ne'
        rw [SimpleGraph.dist_comm, ← hswap]
        exact cycleGraph_dist_le_delta hn b a
    omega
  · exact cycleGraph_dist_ge_min hn hconn a b

/-! ### The tree ball on the cycle -/

/-- A positive cyclic-offset pair carries a genuine edge. -/
private theorem cycleAdj_ne_zero_of_sub_one {n : ℕ} [NeZero n] {a b : Fin n}
    (h : (b - a).val = 1) : cycleAdj n a b ≠ 0 := by
  rw [cycleAdj_apply, if_pos (SimpleGraph.cycleGraph_adj'.2 (Or.inr h))]
  norm_num

/-- The endpoint pair of the base edge. -/
private theorem cycleAdj_edge_zero_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    cycleAdj n ⟨0, by omega⟩ ⟨1, by omega⟩ ≠ 0 := by
  refine cycleAdj_ne_zero_of_sub_one ?_
  have hX : ∃ q : ℕ, n - 0 + 1 = 1 + q * n := ⟨1, by omega⟩
  exact mod_decomp (by omega : (1 : ℕ) < n) hX

/-- **The BFS level formula at a cycle edge**: the level of `z` from
the edge `(a, a+1)` is `0` at the endpoints and
`min ((z−a).val − 1) (n − (z−a).val)` otherwise. -/
theorem cycle_levE_eq {n : ℕ} [NeZero n] (hn : 2 ≤ n) (a z : Fin n) :
    levE (cycleAdj n) (cycleAdj_isSymm n) a (a + 1) z
      = (if (z - a).val = 0 then 0
         else min ((z - a).val - 1) (n - (z - a).val)) := by
  have hda : (supportGraph (cycleAdj n) (cycleAdj_isSymm n)).dist z a
      = min ((a - z).val) (n - (a - z).val) := cycleAdj_dist_eq hn z a
  have hda' : (supportGraph (cycleAdj n) (cycleAdj_isSymm n)).dist z (a + 1)
      = min ((z - (a + 1 : Fin n)).val) (n - (z - (a + 1 : Fin n)).val) := by
    rw [SimpleGraph.dist_comm]
    exact cycleAdj_dist_eq hn (a + 1) z
  -- (a − z).val in terms of δ := (z − a).val
  have hswap : (a - z).val
      = if (z - a).val = 0 then 0 else n - (z - a).val := by
    rcases Nat.eq_zero_or_pos (z - a).val with h0 | hpos
    · rw [if_pos h0]
      have hza : z = a := by
        have : (z - a).val = (a - a).val := by rw [h0, fin_val_sub_self a]
        exact fin_eq_of_val_sub_eq this
      rw [hza, fin_val_sub_self]
    · rw [if_neg (by omega), fin_val_sub_swap_of_pos (by omega)]
  rw [levE, hda, hda', hswap, fin_val_sub_succ a z]
  rcases Nat.eq_zero_or_pos (z - a).val with h0 | hpos
  · rw [if_pos h0, if_pos h0, if_pos h0]
    omega
  · rw [if_neg (by omega : ¬((z - a).val = 0)),
      if_neg (by omega : ¬((z - a).val = 0)), if_neg (by omega : ¬((z - a).val = 0))]
    have hδlt : (z - a).val < n := Fin.isLt _
    omega

/-- **The level class at a cycle edge**: exactly the two vertices at
cyclic offsets `j+1` forward and `j` backward from `a`. -/
theorem cycle_levClass_eq {n : ℕ} [NeZero n] (hn : 2 ≤ n) {j : ℕ} (hj1 : 1 ≤ j)
    (hjn : 2 * (j + 1) < n) (a : Fin n) :
    levClass (cycleAdj n) (cycleAdj_isSymm n) a (a + 1) j
      = insert (a + ⟨j + 1, by omega⟩) (insert (a + ⟨n - j, by omega⟩) ∅) := by
  ext z
  simp only [levClass, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.not_mem_empty, or_false]
  rw [cycle_levE_eq hn a z]
  have hoff : ∀ d : ℕ, (hd : d < n) → (a + ⟨d, hd⟩ - a).val = d :=
    fun d hd => fin_val_sub_add_self a hd
  constructor
  · intro hmem
    rcases Nat.eq_zero_or_pos (z - a).val with h0 | hpos
    · rw [if_pos h0] at hmem
      omega
    · rw [if_neg (by omega : ¬((z - a).val = 0))] at hmem
      rcases Nat.lt_or_ge ((z - a).val) (n - (z - a).val) with hlt | hge
      · have hd : (z - a).val = j + 1 := by omega
        left
        rw [fin_val_decomp a z]
        apply Fin.ext
        rw [Fin.val_add, Fin.val_add, Fin.val_mk, Fin.val_mk, hd]
      · have hd : (z - a).val = n - j := by omega
        right
        rw [fin_val_decomp a z]
        apply Fin.ext
        rw [Fin.val_add, Fin.val_add, Fin.val_mk, Fin.val_mk, hd]
  · rintro (h | h)
    · rw [h, hoff (j + 1) (by omega : (j + 1 : ℕ) < n)]
      rw [if_neg (by omega : ¬((j + 1 : ℕ) = 0))]
      omega
    · rw [h, hoff (n - j) (by omega : (n - j : ℕ) < n)]
      rw [if_neg (by omega : ¬((n - j : ℕ) = 0))]
      omega

/-- **The tree-ball hypothesis on the cycle**: the radius-`(k+1)` ball
around any cycle edge is a full BFS tree whenever `2(k+1) ≤ n` — the
program's structural hypothesis discharging at arbitrary scale. -/
theorem isTreeBall_cycle {n : ℕ} [NeZero n] (hn : 2 ≤ n) {k : ℕ}
    (hk : 2 * (k + 1) < n) (a : Fin n) :
    IsTreeBall (cycleAdj n) (cycleAdj_isSymm n) a (a + 1) 2 (k + 1) := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · have hxy : a ≠ a + 1 := by
      intro hcon
      have hval : a.val = (a + 1 : Fin n).val := congrArg Fin.val hcon
      rw [fin_val_add_one a] at hval
      have ha := a.isLt
      rcases Nat.lt_or_ge (a.val + 1) n with hlt | hge
      · rw [if_pos hlt] at hval
        omega
      · rw [if_neg (by omega)] at hval
        omega
    rw [levClass_zero_card (cycleAdj_connected (by omega)) hxy]
    norm_num
  · have hjn : 2 * (j + 1) < n := by omega
    have hne : (a + ⟨j + 1, by omega⟩ : Fin n) ≠ (a + ⟨n - j, by omega⟩) := by
      intro heq
      have h1 : (a + ⟨j + 1, by omega⟩ - a).val
          = (a + ⟨n - j, by omega⟩ - a).val := by rw [heq]
      rw [fin_val_sub_add_self a (by omega), fin_val_sub_add_self a (by omega)] at h1
      omega
    rw [cycle_levClass_eq hn hj1 hjn a,
      Finset.card_insert_of_not_mem (by simp [hne]),
      Finset.card_insert_of_not_mem (by simp),
      Finset.card_empty]
    norm_num

/-! ### The far-apart edge and the headline theorems -/

/-- **The far-apart condition at the antipodal edge**: on
`C_{4k+8}`, the edges `(0, 1)` and `(2k+4, 2k+5)` are more than
`2(k+1)` apart — the two-edge method's separation hypothesis, with the
family's `4k+8` sizing exactly what buys it. -/
theorem cycleAdj_distEdge_gt (k : ℕ) :
    (k + 1) + (k + 1) < distEdge (cycleAdj (4 * k + 8)) (cycleAdj_isSymm _)
      ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2 * k + 4, by omega⟩ ⟨2 * k + 5, by omega⟩ := by
  have hn : 2 ≤ 4 * k + 8 := by omega
  have hm : (2 * k + 5 : ℕ) < 4 * k + 8 := by omega
  have hδ : ∀ c : ℕ, (hc : c ≤ 2 * k + 5) →
      (⟨c, by omega⟩ - ⟨0, by omega⟩ : Fin (4 * k + 8)).val = c := by
    intro c hc
    rw [fin_val_sub_eq]
    have hX : ∃ q : ℕ, 4 * k + 8 - 0 + c = c + q * (4 * k + 8) := ⟨1, by omega⟩
    exact mod_decomp (by omega) hX
  have hδ' : ∀ c : ℕ, (hc : c ≤ 2 * k + 4) →
      (⟨c + 1, by omega⟩ - ⟨1, by omega⟩ : Fin (4 * k + 8)).val = c := by
    intro c hc
    rw [fin_val_sub_eq]
    have hX : ∃ q : ℕ, 4 * k + 8 - 1 + (c + 1) = c + q * (4 * k + 8) := ⟨1, by omega⟩
    exact mod_decomp (by omega) hX
  have d1 : (supportGraph (cycleAdj (4 * k + 8)) (cycleAdj_isSymm _)).dist
      ⟨0, by omega⟩ ⟨2 * k + 4, by omega⟩ = 2 * k + 4 := by
    rw [cycleAdj_dist_eq hn, hδ (2 * k + 4) (by omega)]
    omega
  have d2 : (supportGraph (cycleAdj (4 * k + 8)) (cycleAdj_isSymm _)).dist
      ⟨1, by omega⟩ ⟨2 * k + 4, by omega⟩ = 2 * k + 3 := by
    rw [cycleAdj_dist_eq hn, hδ' (2 * k + 3) (by omega)]
    omega
  have d3 : (supportGraph (cycleAdj (4 * k + 8)) (cycleAdj_isSymm _)).dist
      ⟨0, by omega⟩ ⟨2 * k + 5, by omega⟩ = 2 * k + 3 := by
    rw [cycleAdj_dist_eq hn, hδ (2 * k + 5) (by omega)]
    omega
  have d4 : (supportGraph (cycleAdj (4 * k + 8)) (cycleAdj_isSymm _)).dist
      ⟨1, by omega⟩ ⟨2 * k + 5, by omega⟩ = 2 * k + 4 := by
    rw [cycleAdj_dist_eq hn, hδ' (2 * k + 4) (by omega)]
    omega
  simp only [distEdge]
  omega

set_option maxHeartbeats 4000000 in
/-- **The Alon–Boppana bound on the cycle family**: `λ₂` of the
`4k+8`-cycle is at most `1/(k+1)` — the Alon–Boppana error term
`d − 2√(d−1) = 0` at `d = 2`, attained with rate `1/(k+1)` on the
canonical family. The tree-ball and far-apart hypotheses of Nilli's
two-edge method discharge at every scale `k`. -/
theorem alonBoppana_cycle (k : ℕ) :
    secondEval (((2 : ℕ) : ℝ) • (1 : Matrix (Fin (4 * k + 8)) (Fin (4 * k + 8)) ℝ)
        - cycleAdj (4 * k + 8))
      (smul_one_sub_isSymm (cycleAdj_isSymm (4 * k + 8)) 2)
      (by rw [Fintype.card_fin]; omega)
      ≤ 1 / ((k : ℝ) + 1) := by
  haveI : NeZero (4 * k + 8) := ⟨by omega⟩
  have hnn : 2 ≤ 4 * k + 8 := by omega
  -- the successor spelling of the far edge's second endpoint
  have hkey : (⟨2 * k + 4, by omega⟩ : Fin (4 * k + 8)) + 1 = ⟨2 * k + 5, by omega⟩ := by
    apply Fin.ext
    have hv1 : (⟨2 * k + 5, by omega⟩ : Fin (4 * k + 8)).val = 2 * k + 5 := rfl
    rw [fin_val_add_one, if_pos (by omega : (2 * k + 4 : ℕ) + 1 < 4 * k + 8)]
  have hedge2 : cycleAdj (4 * k + 8) (⟨2 * k + 4, by omega⟩ :
      Fin (4 * k + 8)) ⟨2 * k + 5, by omega⟩ ≠ 0 := by
    refine cycleAdj_ne_zero_of_sub_one ?_
    rw [fin_val_sub_eq]
    have hX : ∃ q : ℕ, 4 * k + 8 - (2 * k + 4) + (2 * k + 5)
        = 1 + q * (4 * k + 8) := ⟨1, by omega⟩
    exact mod_decomp (by omega : (1 : ℕ) < 4 * k + 8) hX
  have hxy01 : (⟨0, by omega⟩ : Fin (4 * k + 8)) ≠ ⟨1, by omega⟩ := by
    intro hcon
    have hv : (0 : ℕ) = (1 : ℕ) := congrArg Fin.val hcon
    simp only [Fin.val_mk] at hv
    omega
  have huv45 : (⟨2 * k + 4, by omega⟩ : Fin (4 * k + 8)) ≠ ⟨2 * k + 5, by omega⟩ := by
    intro hcon
    have hv : (2 * k + 4 : ℕ) = (2 * k + 5 : ℕ) := congrArg Fin.val hcon
    simp only [Fin.val_mk] at hv
    omega
  have htb2 := isTreeBall_cycle hnn (by omega : 2 * (k + 1) < 4 * k + 8)
    ⟨2 * k + 4, by omega⟩
  rw [hkey] at htb2
  have h := alonBoppana_nilli (d := 2) (k := k)
    (x := ⟨0, by omega⟩) (y := ⟨1, by omega⟩)
    (u := ⟨2 * k + 4, by omega⟩) (v := ⟨2 * k + 5, by omega⟩)
    (cycleAdj_h01 _)
    (cycleAdj_isDRegular (by omega))
    hxy01 (cycleAdj_edge_zero_one hnn)
    huv45 hedge2
    (cycleAdj_connected (by omega))
    (cycleAdj_distEdge_gt k)
    (by norm_num)
    (isTreeBall_cycle hnn (by omega : 2 * (k + 1) < 4 * k + 8) ⟨0, by omega⟩)
    htb2
    (by rw [Fintype.card_fin]; omega)
  have hsqrt : Real.sqrt (((2 - 1 : ℕ) : ℝ)) = 1 := by norm_num
  rw [hsqrt] at h
  simp only [mul_one] at h
  have heq : ((2 : ℕ) : ℝ) - (1 + 2 * (k : ℝ)) / ((k : ℝ) + 1)
      = 1 / ((k : ℝ) + 1) := by
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [heq] at h
  exact h

theorem laplacian_cycleAdj {n : ℕ} (hn : 3 ≤ n) :
    laplacian (cycleAdj n) = (2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - cycleAdj n := by
  have hd := cycleAdj_isDRegular hn
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp [laplacian, degreeMatrix, hd i]
  · simp [laplacian, degreeMatrix, hij]

/-- **The Laplacian form of the cycle bound**: `λ₂(L(C_{4k+8})) ≤
1/(k+1)`. -/
theorem alonBoppana_cycle_laplacian (k : ℕ) :
    secondEval (laplacian (cycleAdj (4 * k + 8)))
      (laplacian_symmetric (cycleAdj (4 * k + 8)) (cycleAdj_isSymm (4 * k + 8)))
      (by simp)
      ≤ 1 / ((k : ℝ) + 1) := by
  rw [secondEval_congr
    (laplacian_symmetric (cycleAdj (4 * k + 8)) (cycleAdj_isSymm (4 * k + 8)))
    (smul_one_sub_isSymm (cycleAdj_isSymm (4 * k + 8)) 2)
    (laplacian_cycleAdj (by omega)) (by simp)]
  exact alonBoppana_cycle k

/-- **The asymptotic Alon–Boppana corollary on the named family**: for
every `ε > 0` there is a cycle whose Laplacian's second eigenvalue is
at most `ε` — the Alon–Boppana error term tends to zero along the
cycle family, the d-regular family with diameter tending to infinity
that the program's completion note asked to be named. -/
theorem alonBoppana_cycle_asymptotic {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, secondEval (laplacian (cycleAdj (4 * k + 8)))
      (laplacian_symmetric (cycleAdj (4 * k + 8)) (cycleAdj_isSymm (4 * k + 8)))
      (by simp)
      ≤ ε := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 / ε ≤ k := ⟨Nat.ceil (1 / ε), Nat.le_ceil _⟩
  refine ⟨k, ?_⟩
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hke : 1 / ε ≤ ((k : ℕ) : ℝ) + 1 :=
    le_trans hk (by exact_mod_cast Nat.le_succ k)
  have h1 : 1 / ((k : ℝ) + 1) ≤ ε := by
    rw [div_le_iff₀ hkpos]
    calc (1 : ℝ) = ε * (1 / ε) := by field_simp
      _ ≤ ε * ((k : ℝ) + 1) := mul_le_mul_of_nonneg_left hke (le_of_lt hε)
  exact le_trans (alonBoppana_cycle_laplacian k) h1

end CycleFamily

end SpectralGraphTheory
