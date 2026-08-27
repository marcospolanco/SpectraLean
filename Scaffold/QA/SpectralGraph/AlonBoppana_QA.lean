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
import Scaffold.Mathlib.GraphTheory.AlonBoppana
import Mathlib.Data.Matrix.Notation
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# QA for `GraphTheory.AlonBoppana` (Steps 1–2)

QA obligations for the Alon–Boppana program's first two steps
(`proposals/alon-boppana-bound.md`): instances of the top-eigenvalue
identification at raw, independently computed pins, the two
hypothesis-necessity fences the proposal's QA plan asks of every
statement in this program, and — Step 2 — the tree-ball interface's
positive instance, negative witness, and tightness fence.

## Step 1: the d-regularity interface

- **Fixture `C₄`** (`abC4`, 2-regular): the theorem instance
  `evals ⟨last⟩ = 2`, joined to the raw entrywise eigen-equation
  `A *ᵥ onesVec = 2 • onesVec` computed by `simp`/`norm_num` with no
  theorem input — the theorem's own witness verified independently.
- **Fixture `K₂`** (`abK2`, 1-regular): the instance
  `evals ⟨last⟩ = 1`, again with the raw eigen-equation.
- **The non-regularity fence** (`abP3_onesVec_not_eigvec`): on the
  path `P₃` (degrees `1, 2, 1`) the constant vector is provably *not*
  an adjacency eigenvector, for any eigenvalue `c` — the interface's
  own witness fails when `IsDRegular` does, so the regularity
  hypothesis is load-bearing at `adjacency_mulVec_onesVec` (mirrors
  the standing hypothesis-necessity refutation pattern).
- **The nonnegativity fence** (`abSign2_*`): the signed
  `!![1, -1; -1, 1]]` is symmetric and *0-regular* (both row sums
  `0`) — every hypothesis of
  `quadForm_le_of_isDRegular` except `hnn` holds — and AM–GM
  domination is refuted at `![1, 0]` (`quadForm = 1 > 0`): `hnn` is
  isolated exactly where it enters (the entrywise AM–GM step).

## Step 2: the tree-ball interface

- **The C₈ full-hypothesis positive** (`abC8_*`, the Step-0 verdict's
  smallest full-hypothesis cycle): the tree-ball instance
  `IsTreeBall abC8 .. 0 1 2 2` (levels 0 and 1 of the antipodal edge
  full — level 1 pinned to exactly `{2, 7}` by adjacency-level facts
  only), the **antipodal disjointness** `Disjoint (ballE .. 0 1 1)
  (ballE .. 4 5 1)` through the far-apart theorem at the four
  rfl-verified cross distances ≥ 3, and the **layer-cake cardinality
  by two independent routes** (direct set enumeration of
  `ballE .. 1 = {0, 1, 2, 7}` vs the geometric-sum theorem through
  the tree-ball instance — one number, two constructions).
- **The C₄ wrap-around negative** (`abC4_not_isTreeBall_three`):
  `IsTreeBall` fails at radius 3 — level 2 is demanded at
  `2 (d−1)² = 2` vertices and is *empty* (every C₄ vertex is within
  level 1 of the edge). The fullness equations carry real geometric
  content: they fail exactly when the BFS ball wraps around the
  graph's short diameter — the qualification trap's QA witness.
- **The threshold-tightness fence**
  (`abC8_ballE_intersect_near_antipodal`): at min cross-distance
  exactly `r + s = 2` (the near-antipodal edges `(0, 1)` and
  `(3, 4)`) the radius-1 balls provably *intersect* — vertex `2` sits
  in both — so the strict inequality of
  `ballE_disjoint_of_lt_distEdge` is load-bearing: weakening it to
  `≤` would make the theorem false.

The theorem-shaped witnesses of the proposal's QA plan (a spectral
value near `2√(d−1)`; Q₃'s not-full levels and K₃,₃'s not-far-apart
edges at the eventual theorem's own hypotheses) are Steps 3–5 work:
they pin `λ₂`-vs-`2√(d−1)` itself, which needs the theorem. Fixture
entries at `Fin 8` are evaluated by `rfl` (`abC8_entries`) —
`simp`/`norm_num` cannot chew `vecCons` at `Fin`-literal columns ≥ 4,
a gap recorded from this delivery's spike.
-/

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-! ## The C₄ instance -/

/-- The 4-cycle adjacency (2-regular). -/
def abC4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 1;
     1, 0, 1, 0;
     0, 1, 0, 1;
     1, 0, 1, 0]

theorem abC4_isSymm : abC4.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [abC4]

theorem abC4_nonneg : ∀ i j, 0 ≤ abC4 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [abC4]

theorem abC4_isDRegular : IsDRegular abC4 2 := by
  intro i
  fin_cases i <;> simp [deg, abC4, Fin.sum_univ_four] <;> norm_num

/-- The raw eigen-equation, computed entrywise with no theorem input
(the theorem's own witness, independently verified). -/
theorem abC4_mulVec_onesVec_raw :
    abC4 *ᵥ onesVec = 2 • onesVec := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, onesVec, Fin.sum_univ_four,
      abC4] <;> norm_num

/-- **The theorem instance on `C₄`: the top adjacency eigenvalue is
`2`.** The raw pin above is the independent route. -/
theorem abC4_evals_last :
    evals abC4_isSymm ⟨Fintype.card (Fin 4) - 1, by decide⟩ = 2 :=
  evals_last_eq_of_isDRegular abC4_isSymm abC4_nonneg abC4_isDRegular
    (by decide)

/-! ## The K₂ instance -/

/-- The edge adjacency (1-regular). -/
def abK2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem abK2_isSymm : abK2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [abK2]

theorem abK2_nonneg : ∀ i j, 0 ≤ abK2 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [abK2]

theorem abK2_isDRegular : IsDRegular abK2 1 := by
  intro i
  fin_cases i <;> simp [deg, abK2, Fin.sum_univ_two]

/-- The raw eigen-equation, computed entrywise with no theorem input. -/
theorem abK2_mulVec_onesVec_raw :
    abK2 *ᵥ onesVec = 1 • onesVec := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, onesVec, Fin.sum_univ_two,
      abK2]

/-- **The theorem instance on `K₂`: the top adjacency eigenvalue is
`1`.** -/
theorem abK2_evals_last :
    evals abK2_isSymm ⟨Fintype.card (Fin 2) - 1, by decide⟩ = 1 :=
  evals_last_eq_of_isDRegular abK2_isSymm abK2_nonneg abK2_isDRegular
    (by decide)

/-! ## The non-regularity fence -/

/-- The path adjacency (degrees `1, 2, 1` — not regular). -/
def abP3 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 1, 0, 1; 0, 1, 0]

/-- **The fence**: on `P₃` the constant vector is provably not an
adjacency eigenvector, for any `c` — entries `0` and `1` of the
action read `1` and `2`, so no scalar works. `IsDRegular` is
load-bearing at the interface's own witness. -/
theorem abP3_onesVec_not_eigvec :
    ∀ c : ℝ, abP3 *ᵥ onesVec ≠ c • onesVec := by
  intro c h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.mulVec, Matrix.dotProduct, onesVec, Fin.sum_univ_three,
    Pi.smul_apply, smul_eq_mul, abP3, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at h0 h1
  norm_num at h0 h1
  linarith

/-! ## The nonnegativity fence -/

/-- The signed `2×2` matrix `!![1, -1; -1, 1]]`: symmetric,
0-regular (both row sums `0`), not nonnegative. -/
def abSign2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 1]

theorem abSign2_isSymm : abSign2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [abSign2]

theorem abSign2_isDRegular : IsDRegular abSign2 0 := by
  intro i
  fin_cases i <;> simp [deg, abSign2, Fin.sum_univ_two]

/-- **The fence**: AM–GM domination fails on the signed 0-regular
matrix at `![1, 0]` — `quadForm = 1 > 0 = 0 · dotProduct`. Every
hypothesis of `quadForm_le_of_isDRegular` except `hnn` holds here, so
the nonnegativity hypothesis is isolated exactly where it enters the
entrywise AM–GM step. -/
theorem abSign2_domination_refuted :
    ¬ ∀ x : Fin 2 → ℝ,
      quadForm abSign2 x ≤ 0 * Matrix.dotProduct x x := by
  intro hdom
  have h1 := hdom ![1, 0]
  simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    abSign2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h1
  norm_num at h1

/-! ## Step 2: the C₄ wrap-around negative (levels fill, then stop) -/

/-- Connectivity of C₄ (the Step-0 spike's bundle, now a QA fixture). -/
theorem abC4_supportGraph_connected :
    (supportGraph abC4 abC4_isSymm).Connected := by
  have hfrom0 : ∀ v : Fin 4, (supportGraph abC4 abC4_isSymm).Reachable 0 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
        ⟨by decide, by simp [abC4]⟩ SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 2)
        ⟨by decide, by simp [abC4]⟩
        (SimpleGraph.Walk.cons (u := 1) (v := 2) (w := 2)
          ⟨by decide, by simp [abC4]⟩ SimpleGraph.Walk.nil)⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 3) (w := 3)
        ⟨by decide, by simp [abC4]⟩ SimpleGraph.Walk.nil⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, hfrom0⟩

/-- The general level-0 cardinality lemma consumed on the C₄ fixture. -/
theorem abC4_levClass_zero_card :
    (levClass abC4 abC4_isSymm 0 1 0).card = 2 :=
  levClass_zero_card abC4_supportGraph_connected (by decide)

/-- Every C₄ vertex is within level `1` of the edge `(0, 1)` — the
wrap-around: in a short-diameter graph the levels fill up and then
stop. -/
theorem abC4_levE_le_one (z : Fin 4) : levE abC4 abC4_isSymm 0 1 z ≤ 1 := by
  have h01 : (supportGraph abC4 abC4_isSymm).dist 0 0 = 0 := by simp
  have h11 : (supportGraph abC4 abC4_isSymm).dist 1 1 = 0 := by simp
  have hz : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by
    fin_cases z
    all_goals simp_all
  rcases hz with rfl | rfl | rfl | rfl
  · simp only [levE]; omega
  · simp only [levE]; omega
  · have h : (supportGraph abC4 abC4_isSymm).dist 2 1 = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.2
        (supportGraph_adj.2 ⟨by decide, by simp [abC4]⟩)
    simp only [levE]; omega
  · have h : (supportGraph abC4 abC4_isSymm).dist 3 0 = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.2
        (supportGraph_adj.2 ⟨by decide, by simp [abC4]⟩)
    simp only [levE]; omega

/-- Level 2 of the C₄ edge `(0, 1)` is **empty** — no vertex sits at
min-distance `2` from the edge. -/
theorem abC4_levClass_two_empty :
    levClass abC4 abC4_isSymm 0 1 2 = ∅ := by
  refine Finset.eq_empty_of_forall_not_mem fun z hz => ?_
  simp only [levClass, Finset.mem_filter, Finset.mem_univ] at hz
  have h2 := hz.2
  have := abC4_levE_le_one z
  omega

/-- **The wrap-around fence**: the tree-ball predicate fails on C₄ at
radius `3` — level `2` is demanded at `2 (d−1)² = 2` vertices and is
empty. The fullness equations carry real geometric content: they fail
exactly when the BFS ball wraps around the graph's short diameter. -/
theorem abC4_not_isTreeBall_three : ¬ IsTreeBall abC4 abC4_isSymm 0 1 2 3 := by
  intro h
  have h2 := h 2 (by omega)
  rw [abC4_levClass_two_empty] at h2
  simp at h2

/-! ## Step 2: the C₈ fixture — the smallest full-hypothesis cycle -/

/-- The 8-cycle adjacency. Its `2`-regularity is structurally evident
but is *not* used by this step's obligations (the Step-2 interface
consumes only the level geometry); entries enter through the
rfl-verified `abC8_entries`. -/
def abC8 : Matrix (Fin 8) (Fin 8) ℝ :=
  !![0, 1, 0, 0, 0, 0, 0, 1;
     1, 0, 1, 0, 0, 0, 0, 0;
     0, 1, 0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0, 1, 0;
     0, 0, 0, 0, 0, 1, 0, 1;
     1, 0, 0, 0, 0, 0, 1, 0]

/-- Every C₈ entry is `0` or `1` — evaluation by `rfl` at both
literals, sidestepping the `vecCons`-at-`Fin`-literal gap that blocks
`simp`/`norm_num` at width 8 (columns `≥ 4`). -/
private theorem abC8_entries (i j : Fin 8) :
    abC8 i j = 0 ∨ abC8 i j = 1 := by
  fin_cases i <;> fin_cases j <;> first
    | exact Or.inl rfl
    | exact Or.inr rfl

theorem abC8_nonneg : ∀ i j, 0 ≤ abC8 i j := by
  intro i j
  rcases abC8_entries i j with h | h
  · simp [h]
  · simp [h]

/-- Entry positivity at an edge, by rfl at the adjacent pair. -/
private theorem abC8_pos {i j : Fin 8} (h : abC8 i j = 1) : 0 < abC8 i j := by
  simp [h]

/-- Support-graph adjacency at a positive off-diagonal entry — the
term-typed form the inline walk witnesses need (an anonymous `⟨_, _⟩`
against `Walk.cons`'s still-implicit `G` is unelaborable). -/
private theorem abC8_adj {i j : Fin 8} (hne : i ≠ j) (h : abC8 i j = 1) :
    (supportGraph abC8 abC8_isSymm).Adj i j :=
  supportGraph_adj.2 ⟨hne, abC8_pos h⟩

theorem abC8_isSymm : abC8.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

/-- Connectivity of C₈: every vertex reachable from `0` (the eight
inline walks — the Step-0 spike's pre-named-Adj pattern, the
adjacencies by rfl-verified entries). -/
theorem abC8_supportGraph_connected :
    (supportGraph abC8 abC8_isSymm).Connected := by
  have hfrom0 : ∀ v : Fin 8, (supportGraph abC8 abC8_isSymm).Reachable 0 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
        (abC8_adj (by decide) rfl) SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 2)
        (abC8_adj (by decide) rfl)
        (SimpleGraph.Walk.cons (u := 1) (v := 2) (w := 2)
          (abC8_adj (by decide) rfl) SimpleGraph.Walk.nil)⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 3)
        (abC8_adj (by decide) rfl)
        (SimpleGraph.Walk.cons (u := 1) (v := 2) (w := 3)
          (abC8_adj (by decide) rfl)
          (SimpleGraph.Walk.cons (u := 2) (v := 3) (w := 3)
            (abC8_adj (by decide) rfl) SimpleGraph.Walk.nil))⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 4)
        (abC8_adj (by decide) rfl)
        (SimpleGraph.Walk.cons (u := 1) (v := 2) (w := 4)
          (abC8_adj (by decide) rfl)
          (SimpleGraph.Walk.cons (u := 2) (v := 3) (w := 4)
            (abC8_adj (by decide) rfl)
            (SimpleGraph.Walk.cons (u := 3) (v := 4) (w := 4)
              (abC8_adj (by decide) rfl) SimpleGraph.Walk.nil)))⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 7) (w := 5)
        (abC8_adj (by decide) rfl)
        (SimpleGraph.Walk.cons (u := 7) (v := 6) (w := 5)
          (abC8_adj (by decide) rfl)
          (SimpleGraph.Walk.cons (u := 6) (v := 5) (w := 5)
            (abC8_adj (by decide) rfl) SimpleGraph.Walk.nil))⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 7) (w := 6)
        (abC8_adj (by decide) rfl)
        (SimpleGraph.Walk.cons (u := 7) (v := 6) (w := 6)
          (abC8_adj (by decide) rfl) SimpleGraph.Walk.nil)⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 7) (w := 7)
        (abC8_adj (by decide) rfl) SimpleGraph.Walk.nil⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, hfrom0⟩

private theorem abC8_dist_ne_zero {a b : Fin 8} (hne : a ≠ b) :
    (supportGraph abC8 abC8_isSymm).dist a b ≠ 0 :=
  SimpleGraph.dist_ne_zero_iff_ne_and_reachable.2
    ⟨hne, abC8_supportGraph_connected a b⟩

private theorem abC8_dist_ne_one {a b : Fin 8} (h0 : abC8 a b = 0) :
    (supportGraph abC8 abC8_isSymm).dist a b ≠ 1 := by
  intro h
  have hadj := SimpleGraph.dist_eq_one_iff_adj.1 h
  have := (supportGraph_adj.1 hadj).2
  rw [h0] at this
  simp at this

/-- **Level 1 of the C₈ edge `(0, 1)` is exactly `{2, 7}`** — the
level-1 cardinality equation `2 (d−1)¹ = 2` discharged with
adjacency-level facts only (the two neighbors off the edge); the
min-zero exclusion of the endpoints is the `dist_self` half. -/
theorem abC8_levClass_one_eq :
    levClass abC8 abC8_isSymm 0 1 1
      = insert 7 (insert 2 (∅ : Finset (Fin 8))) := by
  ext z
  simp only [levClass, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.not_mem_empty, or_false]
  have hself0 : (supportGraph abC8 abC8_isSymm).dist 0 0 = 0 := by simp
  have hself1 : (supportGraph abC8 abC8_isSymm).dist 1 1 = 0 := by simp
  have h01 : (supportGraph abC8 abC8_isSymm).dist 0 1 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2
      (supportGraph_adj.2 ⟨by decide, abC8_pos rfl⟩)
  have h10 : (supportGraph abC8 abC8_isSymm).dist 1 0 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2
      (supportGraph_adj.2 ⟨by decide, abC8_pos rfl⟩)
  have h21 : (supportGraph abC8 abC8_isSymm).dist 2 1 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2
      (supportGraph_adj.2 ⟨by decide, abC8_pos rfl⟩)
  have h70 : (supportGraph abC8 abC8_isSymm).dist 7 0 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2
      (supportGraph_adj.2 ⟨by decide, abC8_pos rfl⟩)
  rcases (show z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = 7 by
      fin_cases z
      all_goals simp_all) with h | h | h | h | h | h | h | h
  · rw [h]; unfold levE
    constructor
    · intro hmin; exfalso; omega
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · rw [h]; unfold levE
    constructor
    · intro hmin; exfalso; omega
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · rw [h]
    have hne := abC8_dist_ne_zero (by decide : (2 : Fin 8) ≠ 0)
    unfold levE
    constructor
    · intro _; exact Or.inr rfl
    · intro _; omega
  · rw [h]
    have e0 : abC8 3 0 = 0 := rfl
    have e1 : abC8 3 1 = 0 := rfl
    have hn0 := abC8_dist_ne_zero (by decide : (3 : Fin 8) ≠ 0)
    have hn1 := abC8_dist_ne_zero (by decide : (3 : Fin 8) ≠ 1)
    have ho0 := abC8_dist_ne_one e0
    have ho1 := abC8_dist_ne_one e1
    unfold levE
    constructor
    · intro hmin; exfalso; omega
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · rw [h]
    have e0 : abC8 4 0 = 0 := rfl
    have e1 : abC8 4 1 = 0 := rfl
    have hn0 := abC8_dist_ne_zero (by decide : (4 : Fin 8) ≠ 0)
    have hn1 := abC8_dist_ne_zero (by decide : (4 : Fin 8) ≠ 1)
    have ho0 := abC8_dist_ne_one e0
    have ho1 := abC8_dist_ne_one e1
    unfold levE
    constructor
    · intro hmin; exfalso; omega
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · rw [h]
    have e0 : abC8 5 0 = 0 := rfl
    have e1 : abC8 5 1 = 0 := rfl
    have hn0 := abC8_dist_ne_zero (by decide : (5 : Fin 8) ≠ 0)
    have hn1 := abC8_dist_ne_zero (by decide : (5 : Fin 8) ≠ 1)
    have ho0 := abC8_dist_ne_one e0
    have ho1 := abC8_dist_ne_one e1
    unfold levE
    constructor
    · intro hmin; exfalso; omega
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · rw [h]
    have e0 : abC8 6 0 = 0 := rfl
    have e1 : abC8 6 1 = 0 := rfl
    have hn0 := abC8_dist_ne_zero (by decide : (6 : Fin 8) ≠ 0)
    have hn1 := abC8_dist_ne_zero (by decide : (6 : Fin 8) ≠ 1)
    have ho0 := abC8_dist_ne_one e0
    have ho1 := abC8_dist_ne_one e1
    unfold levE
    constructor
    · intro hmin; exfalso; omega
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · rw [h]
    have hne := abC8_dist_ne_zero (by decide : (7 : Fin 8) ≠ 1)
    unfold levE
    constructor
    · intro _; exact Or.inl rfl
    · intro _; omega

/-- **The C₈ tree-ball instance**: the antipodal edge `(0, 1)` has full
levels `0` and `1` — `IsTreeBall` at `d = 2`, radius `k = 2`, the
Step-0 verdict's smallest full-hypothesis cycle. -/
theorem abC8_isTreeBall : IsTreeBall abC8 abC8_isSymm 0 1 2 2 := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · rw [levClass_zero_card abC8_supportGraph_connected (by decide)]
    norm_num
  · rw [abC8_levClass_one_eq]
    have hcard : (insert 7 (insert 2 (∅ : Finset (Fin 8)))).card = 2 := by
      decide
    rw [hcard]
    norm_num

/-! ## Step 2: the antipodal disjointness and its tightness -/

/-- A connected-graph distance lower bound by short-walk exhaustion —
only lower bounds are ever needed here (the disjointness theorem
consumes `r + s < dist`), and refuting walks of length `≤ 2` needs no
walk witnesses at all: the length-`dist` walk exists, and `≤ 2` pins
its shape. -/
private theorem dist_le_two_cases_of_connected {W : Type} [DecidableEq W]
    {G : SimpleGraph W} (hconn : G.Connected) {a b : W} (h : G.dist a b ≤ 2) :
    a = b ∨ G.Adj a b ∨ ∃ c, G.Adj a c ∧ G.Adj c b := by
  rcases Nat.eq_zero_or_pos (G.dist a b) with h0 | h1
  · rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 h0 with heq | hnr
    · exact Or.inl heq
    · exact absurd (hconn a b) hnr
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_dist_ne_zero (show
      G.dist a b ≠ 0 by omega)
    cases p with
      | nil => exact absurd h1 (by simp)
      | cons hac p' =>
        rename_i v
        cases p' with
          | nil => exact Or.inr (Or.inl hac)
          | cons hac' p'' =>
            cases p'' with
              | nil => exact Or.inr (Or.inr ⟨v, hac, hac'⟩)
              | cons hac'' p''' =>
                simp only [SimpleGraph.Walk.length_cons,
                  SimpleGraph.Walk.length_nil] at hp
                omega

/-- The antipodal cross distances on C₈ are all at least `3` — refuted
by short-walk exhaustion (no common neighbor, no adjacency). -/
private theorem abC8_dist_ge_three (a b : Fin 8)
    (hne : a ≠ b) (hentry : abC8 a b = 0)
    (hncn : ∀ c : Fin 8, abC8 a c = 0 ∨ abC8 c b = 0) :
    3 ≤ (supportGraph abC8 abC8_isSymm).dist a b := by
  by_contra hlt
  have h2 : (supportGraph abC8 abC8_isSymm).dist a b ≤ 2 := by omega
  rcases dist_le_two_cases_of_connected abC8_supportGraph_connected h2
    with heq | hadj | ⟨c, hc1, hc2⟩
  · exact hne heq
  · have := (supportGraph_adj.1 hadj).2
    rw [hentry] at this
    simp at this
  · have e1 := (supportGraph_adj.1 hc1).2
    have e2 := (supportGraph_adj.1 hc2).2
    rcases hncn c with hc | hc
    · rw [hc] at e1; simp at e1
    · rw [hc] at e2; simp at e2

theorem abC8_dist_0_4 : 3 ≤ (supportGraph abC8 abC8_isSymm).dist 0 4 :=
  abC8_dist_ge_three 0 4 (by decide) rfl
    (by intro c; fin_cases c <;> first | exact Or.inl rfl | exact Or.inr rfl)

theorem abC8_dist_0_5 : 3 ≤ (supportGraph abC8 abC8_isSymm).dist 0 5 :=
  abC8_dist_ge_three 0 5 (by decide) rfl
    (by intro c; fin_cases c <;> first | exact Or.inl rfl | exact Or.inr rfl)

theorem abC8_dist_1_4 : 3 ≤ (supportGraph abC8 abC8_isSymm).dist 1 4 :=
  abC8_dist_ge_three 1 4 (by decide) rfl
    (by intro c; fin_cases c <;> first | exact Or.inl rfl | exact Or.inr rfl)

theorem abC8_dist_1_5 : 3 ≤ (supportGraph abC8 abC8_isSymm).dist 1 5 :=
  abC8_dist_ge_three 1 5 (by decide) rfl
    (by intro c; fin_cases c <;> first | exact Or.inl rfl | exact Or.inr rfl)

/-- **The antipodal disjointness instance**: the radius-1 balls of the
antipodal edges `(0, 1)` and `(4, 5)` are disjoint — the far-apart
condition consumed at the Step-0 verdict's exact fixture. -/
theorem abC8_ballE_disjoint_antipodal :
    Disjoint (ballE abC8 abC8_isSymm 0 1 1) (ballE abC8 abC8_isSymm 4 5 1) := by
  refine ballE_disjoint_of_lt_distEdge 0 1 4 5 1 1
    abC8_supportGraph_connected ?_
  have h1 := abC8_dist_0_4
  have h2 := abC8_dist_0_5
  have h3 := abC8_dist_1_4
  have h4 := abC8_dist_1_5
  simp only [distEdge]
  omega

/-- **The threshold-tightness fence**: at min cross-distance exactly
`r + s = 2` (the near-antipodal edges `(0, 1)` and `(3, 4)`) the
radius-1 balls provably *intersect* — vertex `2` sits in both. The
strict inequality of `ballE_disjoint_of_lt_distEdge` is load-bearing:
weakening it to `≤` would make the theorem false. -/
theorem abC8_ballE_intersect_near_antipodal :
    ¬ Disjoint (ballE abC8 abC8_isSymm 0 1 1) (ballE abC8 abC8_isSymm 3 4 1) := by
  intro hdis
  have h21 : (supportGraph abC8 abC8_isSymm).dist 2 1 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2
      (supportGraph_adj.2 ⟨by decide, abC8_pos rfl⟩)
  have h23 : (supportGraph abC8 abC8_isSymm).dist 2 3 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2
      (supportGraph_adj.2 ⟨by decide, abC8_pos rfl⟩)
  have m1 : 2 ∈ ballE abC8 abC8_isSymm 0 1 1 := ballE_mem_iff.2 (Or.inr h21.le)
  have m2 : 2 ∈ ballE abC8 abC8_isSymm 3 4 1 := ballE_mem_iff.2 (Or.inl h23.le)
  exact Finset.disjoint_right.1 hdis m2 m1

/-! ## Step 2: the layer-cake cardinality — two routes, one number -/

/-- The neighbors of `0` on C₈ are exactly `1` and `7` — entry
exhaustion at rfl-verified values. -/
private theorem abC8_neighbor_zero {z : Fin 8} (h : 0 < abC8 z 0) :
    z = 1 ∨ z = 7 := by
  rcases (show z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = 7 by
      fin_cases z
      all_goals simp_all) with hz | hz | hz | hz | hz | hz | hz | hz
  all_goals subst hz
  · exact absurd h (by rw [show abC8 0 0 = 0 from rfl]; simp)
  · exact Or.inl rfl
  · exact absurd h (by rw [show abC8 2 0 = 0 from rfl]; simp)
  · exact absurd h (by rw [show abC8 3 0 = 0 from rfl]; simp)
  · exact absurd h (by rw [show abC8 4 0 = 0 from rfl]; simp)
  · exact absurd h (by rw [show abC8 5 0 = 0 from rfl]; simp)
  · exact absurd h (by rw [show abC8 6 0 = 0 from rfl]; simp)
  · exact Or.inr rfl

/-- The neighbors of `1` on C₈ are exactly `0` and `2`. -/
private theorem abC8_neighbor_one {z : Fin 8} (h : 0 < abC8 z 1) :
    z = 0 ∨ z = 2 := by
  rcases (show z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = 7 by
      fin_cases z
      all_goals simp_all) with hz | hz | hz | hz | hz | hz | hz | hz
  all_goals subst hz
  · exact Or.inl rfl
  · exact absurd h (by rw [show abC8 1 1 = 0 from rfl]; simp)
  · exact Or.inr rfl
  · exact absurd h (by rw [show abC8 3 1 = 0 from rfl]; simp)
  · exact absurd h (by rw [show abC8 4 1 = 0 from rfl]; simp)
  · exact absurd h (by rw [show abC8 5 1 = 0 from rfl]; simp)
  · exact absurd h (by rw [show abC8 6 1 = 0 from rfl]; simp)
  · exact absurd h (by rw [show abC8 7 1 = 0 from rfl]; simp)

/-- The radius-1 ball of the C₈ edge `(0, 1)` is exactly
`{0, 1, 2, 7}` — by direct membership: the level-0 pair from
`dist_self`, the level-1 pair from the neighbor lemmas. -/
theorem abC8_ballE_one_eq :
    ballE abC8 abC8_isSymm 0 1 1 =
      insert 7 (insert 2 (insert 1
        (insert 0 (∅ : Finset (Fin 8))))) := by
  ext z
  rw [ballE_mem_iff]
  simp only [Finset.mem_insert, Finset.not_mem_empty, or_false]
  constructor
  · rintro (hc | hc)
    · rcases (show (supportGraph abC8 abC8_isSymm).dist z 0 = 0 ∨
        (supportGraph abC8 abC8_isSymm).dist z 0 = 1 by omega) with h0 | h1
      · rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 h0
          with heq | hnr
        · exact Or.inr (Or.inr (Or.inr heq))
        · exact absurd (abC8_supportGraph_connected z 0) hnr
      · have hadj := SimpleGraph.dist_eq_one_iff_adj.1 h1
        rcases abC8_neighbor_zero (supportGraph_adj.1 hadj).2 with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inl rfl
    · rcases (show (supportGraph abC8 abC8_isSymm).dist z 1 = 0 ∨
        (supportGraph abC8 abC8_isSymm).dist z 1 = 1 by omega) with h0 | h1
      · rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 h0
          with heq | hnr
        · exact Or.inr (Or.inr (Or.inl heq))
        · exact absurd (abC8_supportGraph_connected z 1) hnr
      · have hadj := SimpleGraph.dist_eq_one_iff_adj.1 h1
        rcases abC8_neighbor_one (supportGraph_adj.1 hadj).2 with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact Or.inr (Or.inl rfl)
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl (by
        have h : (supportGraph abC8 abC8_isSymm).dist 7 0 = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.2
            (supportGraph_adj.2 ⟨by decide, abC8_pos rfl⟩)
        omega)
    · exact Or.inr (by
        have h : (supportGraph abC8 abC8_isSymm).dist 2 1 = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.2
            (supportGraph_adj.2 ⟨by decide, abC8_pos rfl⟩)
        omega)
    · exact Or.inr (by
        have h : (supportGraph abC8 abC8_isSymm).dist 1 1 = 0 := by simp
        omega)
    · exact Or.inl (by
        have h : (supportGraph abC8 abC8_isSymm).dist 0 0 = 0 := by simp
        omega)

/-- Route 1: direct set enumeration (`decide` on the pinned set). -/
theorem abC8_ballE_card_direct :
    (ballE abC8 abC8_isSymm 0 1 1).card = 4 := by
  rw [abC8_ballE_one_eq]
  decide

/-- Route 2: the layer-cake theorem through the tree-ball instance —
the geometric sum `∑_{j ≤ 1} 2 (2−1)^j = 4`. -/
theorem abC8_ballE_card_layer_cake :
    (ballE abC8 abC8_isSymm 0 1 1).card = 4 := by
  rw [ballE_card_eq_sum abC8_isTreeBall]
  norm_num

end SpectralGraphTheory.QA
