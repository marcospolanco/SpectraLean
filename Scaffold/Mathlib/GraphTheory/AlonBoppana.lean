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
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Alon–Boppana, Steps 1–2: the d-regularity interface and the tree-ball

The home module of the Alon–Boppana program
(`proposals/alon-boppana-bound.md`, adopted 2026-08-26): the lower
companion to the delivered Cheeger/expander toolkit — "how small can
the spectral gap of a d-regular graph possibly be" — via Nilli's
two-edge variational method (Route A), whose linear-algebra engine is
the proved `secondEval_variational`.

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

Steps 3–5 (the radial test vector, the two-vector
orthogonalization, and the diameter-dependent single-graph statement)
are future steps per the proposal's one-step-per-run instruction. The
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
intersect).
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

end SpectralGraphTheory
