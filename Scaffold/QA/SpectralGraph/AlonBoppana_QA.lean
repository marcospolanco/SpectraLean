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
# QA for `GraphTheory.AlonBoppana` (Steps 1–5)

QA obligations for the Alon–Boppana program's first three steps
(`proposals/alon-boppana-bound.md`): instances of the top-eigenvalue
identification at raw, independently computed pins, the two
hypothesis-necessity fences the proposal's QA plan asks of every
statement in this program, — Step 2 — the tree-ball interface's
positive instance, negative witness, and tightness fence, — Step 3
(first slice) — the radial test vector's normalization pinned by two
independent routes and fenced at the `d = 1` degeneracy, and —
Step 3b (second slice) — the energy half's numerator pinned tight by
two independent routes with the three hypothesis fences the
from-below harvest needs.

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

## Step 3: the radial test vector's normalization

- **The C₈ squared-norm pin by two independent routes** at `k = 1`
  (`ρ = 1`, `d = 2`): `abC8_radial_norm_raw` computes
  `⟨ρ^{lev}, ρ^{lev}⟩ = 4` by per-vertex enumeration — every vertex of
  the pinned radius-1 ball `{0, 1, 2, 7}` carries `1`, every vertex
  outside carries `0`, the indicator sum is the set's card by `decide`
  — while `abC8_radial_norm_thm` obtains the same number from
  `radialVec_dotProduct_self` through `abC8_isTreeBall`. A wrong level
  count, a wrong level power, or a wrong normalization constant breaks
  exactly one of the two routes.
- **The `k = 0` pair** (`abC8_radial_norm_k_zero`, `..._raw`): the
  same two routes at the degenerate radius, exercising the theorem's
  `k + 1`-form hypothesis through `isTreeBall_one_of_connected` — that
  Step-2 lemma's first consumer — against the raw enumeration at the
  level-0 pair `{0, 1}`.
- **The `d = 1` degeneracy fence** (`abK2_radial_d1_fence`): every
  input of `radialVec_dotProduct_self` except `1 < d` holds on K₂ at
  `d = 1`, `ρ = 0` — the normalization hypothesis is *junk-satisfiable*
  there because `0⁻¹ = 0` in ℝ — and the identity fails: the vector is
  `![1, 1]` (level 0 carries `ρ^0 = 1` even at `ρ = 0`), so the
  squared norm is `2`, not `2 (k+1) = 4`. `hd1` is load-bearing
  exactly at the cancellation step the module docstring names.

The theorem-shaped witnesses of the proposal's QA plan (a spectral
value near `2√(d−1)`; Q₃'s not-full levels and K₃,₃'s not-far-apart
edges at the eventual theorem's own hypotheses) are the remaining
Step-3 slices' and Steps 4–5's work: they pin `λ₂`-vs-`2√(d−1)`
itself, which needs the energy half and the orthogonalization. Fixture
entries at `Fin 8` are evaluated by `rfl` (`abC8_entries`) —
`simp`/`norm_num` cannot chew `vecCons` at `Fin`-literal columns ≥ 4,
a gap recorded from this delivery's spike.

## Step 3b: the energy half — two routes, one number, and three fences

- **The C₈ numerator pin, tight at equality**
  (`abC8_radial_quadForm_eq_six` vs `abC8_radial_energy_thm`): the
  raw route computes `xᵀAx = 6` by enumeration — the radius-1 ball
  `{0, 1, 2, 7}`'s four restricted row sums `(2, 2, 1, 1)` weighted by
  the indicator entries, every matrix entry by `rfl` — while the
  theorem route reads `2 + 4 k (d−1) ρ = 2 + 4·1·1·1 = 6` through
  `abC8_isTreeBall`. The two routes share no mechanism, and the bound
  is *attained* on the fixture: every term of the harvest is visible
  in the raw number (the edge's `2` and the four level-1 parent edges'
  `4`).
- **The `k = 0` pair both routes** (`abC8_radial_energy_k_zero`,
  `abC8_radial_quadForm_k_zero_raw`): `2 ≤ 2 = 2` at the one-level
  tree ball — `isTreeBall_one_of_connected`'s second consumer.
- **The Rayleigh-quotient instance** (`abC8_radial_rayleigh_thm`):
  `6 / 4 ≤ R`, the corollary joined to the delivered denominator.
- **The pseudo-edge fence** (`abP3_pseudoEdge_fence`, `hedge`
  isolated): on `P₃` at the NON-edge `(0, 2)` — every hypothesis of
  `radialVec_quadForm_ge` holds at `k = 0`, `d = 2`, `ρ = 1` except
  `A x y ≠ 0` — the test vector is the indicator of `{0, 2}`, which
  spans no edge, so the numerator is `0 < 2`.
- **The fractional-weight fence** (`abHalfK2_fractional_fence`, `h01`
  isolated): the edge `K₂` at weight `1/2` — every hypothesis except
  the `0`-or-`≥ 1` weight discipline — the numerator is
  `1/2 + 1/2 = 1 < 2`. A parent edge of fractional weight is exactly
  what the from-below harvest cannot price.
- **The loop fence** (`abLoop2_loop_fence`, `hxy` isolated): the
  one-vertex loop with an unreachable partner at `x = y = 0` — every
  hypothesis except `x ≠ y`; the junk-zero vertex fills the level-0
  cardinality equation so `IsTreeBall` *genuinely holds*, and the
  numerator is the loop's single ordered contribution `1 < 2`. The
  distinct-endpoints hypothesis is what makes the selection's
  `(x, y)` and `(y, x)` two different ordered pairs.

## Step 4: the two-vector orthogonalization (delivered 2026-08-27)

- **The C₈ antipodal-pair positive**: orthogonality by two routes (raw
  `4 − 4 = 0` per-vertex enumeration at the two value oracles vs
  `twoEdgeVec_dotProduct_onesVec`), the norm `8 = 4 (k+1)`, the
  numerator `8` by the `quadForm_sub` decomposition (`6 + 6 − 2·2`,
  the cross's two cross edges explicit), and the headline instance
  `secondEval (2•1 − abC8) ≤ 1` at `k = 0` — the full engine stack on
  a real graph.
- **The `hfar` fence** (`abC8_far_fence`, `k = 1`): both radius-2
  tree balls genuine, `distEdge = 3 < 4`, the norm identity surviving
  while the numerator bound is refuted at `8 < 12` — the far-apart
  threshold isolated at its exact constant.
- **The P₃ overlap fence** (`abP3_overlap_fence`): both one-level
  tree balls hold, the balls share vertex `1`, and the norm identity
  is refuted at `2 ≠ 4` — ball disjointness isolated.

## Step 5: the diameter-dependent packaging and the two Step-4
## residuals

- **The C₈ instances of the packaged statements**
  (`abC8_nilli_instance`, `abC8_nilli_classical_instance`): the
  capstone `alonBoppana_nilli` at `k = 0` gives
  `secondEval (2•1 − C₈) ≤ 2 − (1 + 0)/1 = 1` — the same number as
  Step 4's instance, now through the `√` packaging (`√(2−1) = 1`
  pinned by `norm_num`) — and the classical shape gives the honest
  weak-at-small-`k` reading `≤ 2 − 2 + 2 = 2`: the error term
  swallows the content exactly where the qualification trap says it
  must (small `k`, small diameter).
- **The diameter bookkeeping instance** (`abC8_diam_ge_three`):
  `2 (0+1) + 1 = 3 ≤ diam (supportGraph C₈)` through
  `alonBoppana_diam_ge` — the bridge `distEdge_le_diam` exercised on
  real input, the honest `k + 1 ≤ ⌊diam/2⌋` constraint instantiated.
- **The loop-pair orthogonality fence** (`abP3L_loop_pair_fence`, a
  priced Step-4 residual): the fixture `P₃` plus a loop at vertex `2`.
  The edge `(0, 1)` carries a genuine one-level tree ball; the *loop*
  `(2, 2)` does not — its level-0 class is `{2}` (card `1 ≠ 2`, the
  junk-zero-honest level function collapsing the loop's single
  endpoint) — so `twoEdgeVec_dotProduct_onesVec`'s `htb2` fails, and
  its conclusion fails with it: the difference vector is
  `![1, 1, −1]`, of total mass `1 ≠ 0`. A loop is exactly the
  "edge" the equal-mass lemma's level-counting does not see as two
  endpoints.
- **The independent engine route at the integer witness**
  (`abC8_intWitness_secondEval_le`, the other priced residual): the
  hand vector `![1, 1, 0, −1, −1, −1, 0, 1]` — a globally supported
  integer vector, structurally unlike the radial pair — is orthogonal
  to `onesVec` (raw sum `0`), has squared norm `6` (raw), and
  quadratic form `⟨w, A w⟩ = 8` (raw: the support
  `{0,1,3,4,5,7}`²-filtered double sum, every entry by `rfl`), so
  `secondEval_le_rayleigh` at *this* witness gives
  `secondEval (2•1 − C₈) ≤ (2·6 − 8)/6 = 2/3` — strictly stronger
  than both theorem routes' `≤ 1`, by an independent vector through
  the same engine.
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

/-! ## Step 3: the radial test vector's normalization — two routes, one number -/

/-- Level 0 of the C₈ edge `(0, 1)` is exactly `{0, 1}`, in iff form —
the raw route's membership oracle (from the general connected
level-0 identity). -/
private theorem abC8_levE_zero_iff (z : Fin 8) :
    levE abC8 abC8_isSymm 0 1 z = 0 ↔ z = 0 ∨ z = 1 := by
  constructor
  · intro h
    have hm : z ∈ levClass abC8 abC8_isSymm 0 1 0 := by
      simp only [levClass, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    rw [levClass_zero_eq abC8_supportGraph_connected (by decide)] at hm
    simpa using hm
  · intro h
    have hm : z ∈ levClass abC8 abC8_isSymm 0 1 0 := by
      rw [levClass_zero_eq abC8_supportGraph_connected (by decide)]
      simpa using h
    simpa only [levClass, Finset.mem_filter, Finset.mem_univ, true_and] using hm

/-- Level 1 of the C₈ edge `(0, 1)` is exactly `{2, 7}`, in iff form —
the raw route's membership oracle (from the Step-2 pin). -/
private theorem abC8_levE_one_iff (z : Fin 8) :
    levE abC8 abC8_isSymm 0 1 z = 1 ↔ z = 2 ∨ z = 7 := by
  constructor
  · intro h
    have hm : z ∈ levClass abC8 abC8_isSymm 0 1 1 := by
      simp only [levClass, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    rw [abC8_levClass_one_eq] at hm
    simp only [Finset.mem_insert, Finset.not_mem_empty, or_false] at hm
    rcases hm with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'
  · intro h
    have hm : z ∈ levClass abC8 abC8_isSymm 0 1 1 := by
      rw [abC8_levClass_one_eq]
      simp only [Finset.mem_insert, Finset.not_mem_empty, or_false]
      rcases h with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
    simpa only [levClass, Finset.mem_filter, Finset.mem_univ, true_and] using hm

/-- **Route 1 (raw)**: the squared norm of the radial test vector on
C₈ at `k = 1`, `ρ = 1`, computed by per-vertex enumeration — every
vertex of the radius-1 ball `{0, 1, 2, 7}` carries `ρ^{lev} ·
ρ^{lev} = 1`, every vertex outside carries `0`, and the indicator sum
is the set's card `4` by `decide`. No theorem input: the memberships
come from the level iff oracles, the arithmetic from `decide`. -/
theorem abC8_radial_norm_raw :
    Matrix.dotProduct (radialVec abC8 abC8_isSymm 0 1 1 1)
      (radialVec abC8 abC8_isSymm 0 1 1 1) = 4 := by
  have hin : ∀ z : Fin 8, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 7 →
      levE abC8 abC8_isSymm 0 1 z ≤ 1 := by
    intro z h
    rcases h with rfl | rfl | rfl | rfl
    · exact ((abC8_levE_zero_iff 0).2 (Or.inl rfl)).le.trans (Nat.zero_le 1)
    · exact ((abC8_levE_zero_iff 1).2 (Or.inr rfl)).le.trans (Nat.zero_le 1)
    · exact ((abC8_levE_one_iff 2).2 (Or.inl rfl)).le
    · exact ((abC8_levE_one_iff 7).2 (Or.inr rfl)).le
  have hout : ∀ z : Fin 8, z ≠ 0 → z ≠ 1 → z ≠ 2 → z ≠ 7 →
      2 ≤ levE abC8 abC8_isSymm 0 1 z := by
    intro z h0 h1 h2 h7
    rcases Nat.eq_zero_or_pos (levE abC8 abC8_isSymm 0 1 z) with h | h
    · rcases (abC8_levE_zero_iff z).1 h with h' | h'
      · exact absurd h' h0
      · exact absurd h' h1
    · rcases (show levE abC8 abC8_isSymm 0 1 z = 1 ∨
          2 ≤ levE abC8 abC8_isSymm 0 1 z by omega) with h' | h'
      · rcases (abC8_levE_one_iff z).1 h' with h'' | h''
        · exact absurd h'' h2
        · exact absurd h'' h7
      · exact h'
  have hfilt : ∀ z : Fin 8,
      radialVec abC8 abC8_isSymm 0 1 1 1 z * radialVec abC8 abC8_isSymm 0 1 1 1 z
        = if z ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))
          then (1:ℝ) else 0 := by
    intro z
    by_cases hz : z ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))
    · rw [if_pos hz]
      have hle : levE abC8 abC8_isSymm 0 1 z ≤ 1 := by
        simp only [Finset.mem_insert, Finset.not_mem_empty, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact ((abC8_levE_one_iff 7).2 (Or.inr rfl)).le
        · exact ((abC8_levE_one_iff 2).2 (Or.inl rfl)).le
        · exact ((abC8_levE_zero_iff 1).2 (Or.inr rfl)).le.trans (Nat.zero_le 1)
        · exact ((abC8_levE_zero_iff 0).2 (Or.inl rfl)).le.trans (Nat.zero_le 1)
      simp only [radialVec, if_pos hle, one_pow, one_mul]
    · rw [if_neg hz]
      have hn0 : z ≠ 0 := fun h => hz (by simp [h])
      have hn1 : z ≠ 1 := fun h => hz (by simp [h])
      have hn2 : z ≠ 2 := fun h => hz (by simp [h])
      have hn7 : z ≠ 7 := fun h => hz (by simp [h])
      have h2 := hout z hn0 hn1 hn2 hn7
      simp only [radialVec, if_neg (show ¬ levE abC8 abC8_isSymm 0 1 z ≤ 1 by omega),
        zero_mul]
  simp only [Matrix.dotProduct]
  rw [Finset.sum_congr rfl fun z _ => hfilt z]
  have heq : ∑ z : Fin 8,
      (if z ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))
        then (1:ℝ) else 0)
      = ∑ z ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8))))), (1:ℝ) :=
    (Finset.sum_subset (Finset.subset_univ _)
      (fun z _ hz => if_neg hz)).symm
  rw [heq, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard :
      (insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))).card = 4 := by
    decide
  rw [hcard]
  norm_num

/-- **Route 2 (theorem)**: the same number from the squared-norm
identity through the C₈ tree-ball instance — `2 (k+1) = 4` at `k = 1`,
`d = 2`, `ρ = 1`. The two routes share no mechanism: a wrong level
count, level power, or normalization constant breaks exactly one. -/
theorem abC8_radial_norm_thm :
    Matrix.dotProduct (radialVec abC8 abC8_isSymm 0 1 1 1)
      (radialVec abC8 abC8_isSymm 0 1 1 1) = 4 := by
  have h := radialVec_dotProduct_self (d := 2) (x := 0) (y := 1) (ρ := 1) (k := 1)
    (by norm_num) abC8_isTreeBall (by norm_num)
  norm_num at h
  linarith

/-- Nonvanishing on the fixture, from the endpoint seed. -/
theorem abC8_radial_ne_zero :
    radialVec abC8 abC8_isSymm 0 1 1 1 ≠ 0 :=
  radialVec_ne_zero 0 1 1 1

/-! ### The k = 0 pair — `isTreeBall_one_of_connected`'s first consumer -/

theorem abC8_radial_norm_k_zero :
    Matrix.dotProduct (radialVec abC8 abC8_isSymm 0 1 1 0)
      (radialVec abC8 abC8_isSymm 0 1 1 0) = 2 := by
  have h := radialVec_dotProduct_self (d := 2) (x := 0) (y := 1) (ρ := 1) (k := 0)
    (by norm_num) (isTreeBall_one_of_connected abC8_supportGraph_connected
      (by decide) 2) (by norm_num)
  norm_num at h
  linarith

theorem abC8_radial_norm_k_zero_raw :
    Matrix.dotProduct (radialVec abC8 abC8_isSymm 0 1 1 0)
      (radialVec abC8 abC8_isSymm 0 1 1 0) = 2 := by
  have hfilt : ∀ z : Fin 8,
      radialVec abC8 abC8_isSymm 0 1 1 0 z * radialVec abC8 abC8_isSymm 0 1 1 0 z
        = if z ∈ insert 1 (insert 0 (∅ : Finset (Fin 8))) then (1:ℝ) else 0 := by
    intro z
    by_cases hz : z ∈ insert 1 (insert 0 (∅ : Finset (Fin 8)))
    · rw [if_pos hz]
      have hd : z = 0 ∨ z = 1 := by
        simp only [Finset.mem_insert, Finset.not_mem_empty, or_false] at hz
        rcases hz with h' | h'
        · exact Or.inr h'
        · exact Or.inl h'
      rcases hd with rfl | rfl
      · simp only [radialVec, if_pos (((abC8_levE_zero_iff 0).2 (Or.inl rfl)).le),
          one_pow, one_mul]
      · simp only [radialVec, if_pos (((abC8_levE_zero_iff 1).2 (Or.inr rfl)).le),
          one_pow, one_mul]
    · rw [if_neg hz]
      have hne : ¬ (levE abC8 abC8_isSymm 0 1 z ≤ 0) := by
        intro hle
        have h0 := (abC8_levE_zero_iff z).1 (by omega)
        rcases h0 with h' | h'
        · exact hz (by simp [h'])
        · exact hz (by simp [h'])
      simp only [radialVec, if_neg hne, zero_mul]
  simp only [Matrix.dotProduct]
  rw [Finset.sum_congr rfl fun z _ => hfilt z]
  have heq : ∑ z : Fin 8,
      (if z ∈ insert 1 (insert 0 (∅ : Finset (Fin 8))) then (1:ℝ) else 0)
      = ∑ z ∈ insert 1 (insert 0 (∅ : Finset (Fin 8))), (1:ℝ) :=
    (Finset.sum_subset (Finset.subset_univ _)
      (fun z _ hz => if_neg hz)).symm
  rw [heq, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (insert 1 (insert 0 (∅ : Finset (Fin 8)))).card = 2 := by decide
  rw [hcard]
  norm_num

/-! ### The K₂ d = 1 degeneracy fence -/

theorem abK2_supportGraph_connected :
    (supportGraph abK2 abK2_isSymm).Connected := by
  have hfrom0 : ∀ v : Fin 2, (supportGraph abK2 abK2_isSymm).Reachable 0 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
        (supportGraph_adj.2 ⟨by decide, by simp [abK2]⟩) SimpleGraph.Walk.nil⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, hfrom0⟩

/-- Every K₂ vertex is an endpoint of the edge `(0, 1)`: both levels
are `0`. -/
theorem abK2_levE_zero (z : Fin 2) : levE abK2 abK2_isSymm 0 1 z = 0 := by
  fin_cases z
  · simp [levE]
  · simp [levE]

theorem abK2_levClass_one_empty :
    levClass abK2 abK2_isSymm 0 1 1 = ∅ := by
  refine Finset.eq_empty_of_forall_not_mem fun z hz => ?_
  simp only [levClass, Finset.mem_filter, Finset.mem_univ] at hz
  have := abK2_levE_zero z
  omega

/-- The tree-ball predicate holds on K₂ at `d = 1`, radius `2`: level
0 is the endpoint pair, level 1 is demanded empty (`2 (1−1)¹ = 0`) and
is empty — every vertex is an endpoint. -/
theorem abK2_isTreeBall_d1 : IsTreeBall abK2 abK2_isSymm 0 1 1 2 := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · rw [levClass_zero_card abK2_supportGraph_connected (by decide)]
    norm_num
  · rw [abK2_levClass_one_empty]
    simp

/-- **The `d = 1` fence**: every input of `radialVec_dotProduct_self`
except `1 < d` holds on K₂ at `d = 1`, `ρ = 0` — the normalization
hypothesis is *junk-satisfiable* there because `0⁻¹ = 0` in ℝ — and the
identity fails: the vector is `![1, 1]` (level 0 carries `ρ^0 = 1`
even at `ρ = 0`), so the squared norm is `2`, not `2 (k+1) = 4`. `hd1`
is load-bearing exactly at the cancellation step (`mul_inv_cancel₀`)
the module docstring names. -/
theorem abK2_radial_d1_fence :
    IsTreeBall abK2 abK2_isSymm 0 1 1 2 ∧
      (0 : ℝ) ^ 2 = ((1 - 1 : ℕ) : ℝ)⁻¹ ∧
      Matrix.dotProduct (radialVec abK2 abK2_isSymm 0 1 0 1)
        (radialVec abK2 abK2_isSymm 0 1 0 1) = 2 := by
  refine ⟨abK2_isTreeBall_d1, by norm_num, ?_⟩
  simp only [Matrix.dotProduct, Fin.sum_univ_two]
  have f0 : radialVec abK2 abK2_isSymm 0 1 0 1 0 = 1 := by
    have h0 : levE abK2 abK2_isSymm 0 1 0 = 0 := abK2_levE_zero 0
    simp [radialVec, h0]
  have f1 : radialVec abK2 abK2_isSymm 0 1 0 1 1 = 1 := by
    have h0 : levE abK2 abK2_isSymm 0 1 1 = 0 := abK2_levE_zero 1
    simp [radialVec, h0]
  rw [f0, f1]
  norm_num

/-! ## Step 3b: the energy half — two routes, one number, and three fences -/

/-- The radial vector on C₈ at `k = 1`, `ρ = 1` is the indicator of
the radius-1 ball `{0, 1, 2, 7}`. -/
private theorem abC8_radial_val (z : Fin 8) :
    radialVec abC8 abC8_isSymm 0 1 1 1 z
      = if z ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))
        then (1 : ℝ) else 0 := by
  by_cases hz : z ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))
  · rw [if_pos hz]
    have hle : levE abC8 abC8_isSymm 0 1 z ≤ 1 := by
      simp only [Finset.mem_insert, Finset.not_mem_empty, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact ((abC8_levE_one_iff 7).2 (Or.inr rfl)).le
      · exact ((abC8_levE_one_iff 2).2 (Or.inl rfl)).le
      · exact ((abC8_levE_zero_iff 1).2 (Or.inr rfl)).le.trans (Nat.zero_le 1)
      · exact ((abC8_levE_zero_iff 0).2 (Or.inl rfl)).le.trans (Nat.zero_le 1)
    simp only [radialVec, if_pos hle, one_pow]
  · rw [if_neg hz]
    have h2 : 2 ≤ levE abC8 abC8_isSymm 0 1 z := by
      rcases Nat.eq_zero_or_pos (levE abC8 abC8_isSymm 0 1 z) with h | h
      · rcases (abC8_levE_zero_iff z).1 h with h' | h'
        · exact absurd (by simp [h']) hz
        · exact absurd (by simp [h']) hz
      · rcases (show levE abC8 abC8_isSymm 0 1 z = 1 ∨
            2 ≤ levE abC8 abC8_isSymm 0 1 z by omega) with h' | h'
        · rcases (abC8_levE_one_iff z).1 h' with h'' | h''
          · exact absurd (by simp [h'']) hz
          · exact absurd (by simp [h'']) hz
        · exact h'
    simp only [radialVec, if_neg (show ¬ levE abC8 abC8_isSymm 0 1 z ≤ 1 by omega)]

private theorem abC8_h01 : ∀ i j : Fin 8, abC8 i j = 0 ∨ 1 ≤ abC8 i j := by
  intro i j
  rcases abC8_entries i j with h | h
  · exact Or.inl h
  · exact Or.inr (by simp [h])

private theorem abC8_edge01 : abC8 0 1 ≠ 0 := by
  rw [show abC8 0 1 = (1 : ℝ) from rfl]
  norm_num

/-- **Route 1 (raw)**: the numerator computed by enumeration — the
four in-ball rows' restricted row sums `(2, 2, 1, 1)` weighted by the
indicator entries, all by rfl-verified entries and `decide`-free
arithmetic. No theorem input. -/
theorem abC8_radial_quadForm_eq_six :
    quadForm abC8 (radialVec abC8 abC8_isSymm 0 1 1 1) = 6 := by
  have hrow : ∀ u : Fin 8,
      (∑ v : Fin 8, abC8 u v * radialVec abC8 abC8_isSymm 0 1 1 1 v)
        = abC8 u 7 + abC8 u 2 + abC8 u 1 + abC8 u 0 := by
    intro u
    have hfilt : ∀ v : Fin 8, abC8 u v * radialVec abC8 abC8_isSymm 0 1 1 1 v
        = if v ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))
          then abC8 u v else 0 := by
      intro v
      rw [abC8_radial_val v]
      by_cases hv : v ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))
      · rw [if_pos hv, if_pos hv, mul_one]
      · rw [if_neg hv, if_neg hv, mul_zero]
    rw [Finset.sum_congr rfl (fun v _ => hfilt v)]
    have heq : (∑ v : Fin 8,
        (if v ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))
          then abC8 u v else 0))
      = ∑ v ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8))))), abC8 u v :=
      (Finset.sum_subset (Finset.subset_univ _)
        (fun v _ hv => if_neg hv)).symm
    rw [heq]
    simp [Finset.sum_insert, Finset.sum_singleton]
    ring
  simp only [quadForm, Matrix.dotProduct, Matrix.mulVec]
  have hfilt2 : ∀ u : Fin 8,
      (radialVec abC8 abC8_isSymm 0 1 1 1 u * (abC8 u 7 + abC8 u 2 + abC8 u 1 + abC8 u 0))
        = if u ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))
          then abC8 u 7 + abC8 u 2 + abC8 u 1 + abC8 u 0 else 0 := by
    intro u
    rw [abC8_radial_val u]
    by_cases hu : u ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))
    · rw [if_pos hu, if_pos hu, one_mul]
    · rw [if_neg hu, if_neg hu, zero_mul]
  rw [Finset.sum_congr rfl (fun u _ => by rw [hrow u, hfilt2 u])]
  have heq : (∑ w : Fin 8,
      (if w ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))
        then abC8 w 7 + abC8 w 2 + abC8 w 1 + abC8 w 0 else 0))
    = ∑ w ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8))))),
        (abC8 w 7 + abC8 w 2 + abC8 w 1 + abC8 w 0) :=
    (Finset.sum_subset (Finset.subset_univ _)
      (fun w _ hw => if_neg hw)).symm
  rw [heq]
  simp [Finset.sum_insert, Finset.sum_singleton]
  have e0 : abC8 7 7 = 0 := rfl
  have e1 : abC8 7 2 = 0 := rfl
  have e2 : abC8 7 1 = 0 := rfl
  have e3 : abC8 7 0 = 1 := rfl
  have e4 : abC8 2 7 = 0 := rfl
  have e5 : abC8 2 2 = 0 := rfl
  have e6 : abC8 2 1 = 1 := rfl
  have e7 : abC8 2 0 = 0 := rfl
  have e8 : abC8 1 7 = 0 := rfl
  have e9 : abC8 1 2 = 1 := rfl
  have e10 : abC8 1 1 = 0 := rfl
  have e11 : abC8 1 0 = 1 := rfl
  have e12 : abC8 0 7 = 1 := rfl
  have e13 : abC8 0 2 = 0 := rfl
  have e14 : abC8 0 1 = 1 := rfl
  have e15 : abC8 0 0 = 0 := rfl
  norm_num [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]

/-- **Route 2 (theorem)**: the energy bound through the C₈ tree-ball
instance — `2 + 4 k (d−1) ρ = 2 + 4·1·1·1 = 6`. Joined to the raw
route above, the bound is TIGHT on the fixture. -/
theorem abC8_radial_energy_thm :
    2 + 4 * ((1 : ℕ) : ℝ) * ((2 - 1 : ℕ) : ℝ) * 1
      ≤ quadForm abC8 (radialVec abC8 abC8_isSymm 0 1 1 1) :=
  radialVec_quadForm_ge (d := 2) (k := 1) (ρ := 1) (x := 0) (y := 1)
    abC8_h01 (by decide) abC8_edge01 (by decide) abC8_isTreeBall
    (by norm_num) (by norm_num)

/-- The Rayleigh-quotient corollary on the fixture: `6 / 4 ≤ R`, with
the denominator the delivered `2 (k+1)`. -/
theorem abC8_radial_rayleigh_thm :
    (2 + 4 * ((1 : ℕ) : ℝ) * ((2 - 1 : ℕ) : ℝ) * 1) / (2 * (((1 : ℕ) : ℝ) + 1))
      ≤ rayleigh abC8 (radialVec abC8 abC8_isSymm 0 1 1 1) :=
  radialVec_rayleigh_ge (d := 2) (k := 1) (ρ := 1) (x := 0) (y := 1)
    abC8_h01 (by decide) abC8_edge01 (by decide) abC8_isTreeBall
    (by norm_num) (by norm_num)

/-- The radial vector on C₈ at `k = 0`, `ρ = 1` is the indicator of the
edge pair `{0, 1}`. -/
private theorem abC8_radial_val_k0 (z : Fin 8) :
    radialVec abC8 abC8_isSymm 0 1 1 0 z
      = if z ∈ insert 1 (insert 0 (∅ : Finset (Fin 8))) then (1 : ℝ) else 0 := by
  by_cases hz : z ∈ insert 1 (insert 0 (∅ : Finset (Fin 8)))
  · rw [if_pos hz]
    have hd : z = 0 ∨ z = 1 := by
      simp only [Finset.mem_insert, Finset.not_mem_empty, or_false] at hz
      rcases hz with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
    rcases hd with rfl | rfl
    · simp only [radialVec, if_pos (((abC8_levE_zero_iff 0).2 (Or.inl rfl)).le),
        one_pow]
    · simp only [radialVec, if_pos (((abC8_levE_zero_iff 1).2 (Or.inr rfl)).le),
        one_pow]
  · rw [if_neg hz]
    have h1 : ¬ (levE abC8 abC8_isSymm 0 1 z ≤ 0) := by
      intro hle
      have h0 := (abC8_levE_zero_iff z).1 (by omega)
      rcases h0 with h' | h'
      · exact hz (by simp [h'])
      · exact hz (by simp [h'])
    simp only [radialVec, if_neg h1]

/-- **The `k = 0` theorem route**: `2 ≤ quadForm` at the one-level
tree ball (`isTreeBall_one_of_connected`'s second consumer). -/
theorem abC8_radial_energy_k_zero :
    2 + 4 * ((0 : ℕ) : ℝ) * ((2 - 1 : ℕ) : ℝ) * 1
      ≤ quadForm abC8 (radialVec abC8 abC8_isSymm 0 1 1 0) :=
  radialVec_quadForm_ge (d := 2) (k := 0) (ρ := 1) (x := 0) (y := 1)
    abC8_h01 (by decide) abC8_edge01 (by decide)
    (isTreeBall_one_of_connected abC8_supportGraph_connected (by decide) 2)
    (by norm_num) (by norm_num)

/-- **The `k = 0` raw route**: the numerator computed by enumeration —
the indicator vector on `{0, 1}` against the two directed edges. -/
theorem abC8_radial_quadForm_k_zero_raw :
    quadForm abC8 (radialVec abC8 abC8_isSymm 0 1 1 0) = 2 := by
  simp only [quadForm, Matrix.dotProduct, Matrix.mulVec]
  have hrow : ∀ u : Fin 8,
      (∑ v : Fin 8, abC8 u v * radialVec abC8 abC8_isSymm 0 1 1 0 v)
        = abC8 u 1 + abC8 u 0 := by
    intro u
    have hfilt : ∀ v : Fin 8, abC8 u v * radialVec abC8 abC8_isSymm 0 1 1 0 v
        = if v ∈ insert 1 (insert 0 (∅ : Finset (Fin 8))) then abC8 u v else 0 := by
      intro v
      rw [abC8_radial_val_k0 v]
      by_cases hv : v ∈ insert 1 (insert 0 (∅ : Finset (Fin 8)))
      · rw [if_pos hv, if_pos hv, mul_one]
      · rw [if_neg hv, if_neg hv, mul_zero]
    rw [Finset.sum_congr rfl (fun v _ => hfilt v)]
    have heq : (∑ v : Fin 8,
        (if v ∈ insert 1 (insert 0 (∅ : Finset (Fin 8)))
          then abC8 u v else 0))
      = ∑ v ∈ insert 1 (insert 0 (∅ : Finset (Fin 8))), abC8 u v :=
      (Finset.sum_subset (Finset.subset_univ _)
        (fun v _ hv => if_neg hv)).symm
    rw [heq]
    simp [Finset.sum_insert, Finset.sum_singleton]
  have hfilt2 : ∀ u : Fin 8,
      (radialVec abC8 abC8_isSymm 0 1 1 0 u * (abC8 u 1 + abC8 u 0))
        = if u ∈ insert 1 (insert 0 (∅ : Finset (Fin 8)))
          then abC8 u 1 + abC8 u 0 else 0 := by
    intro u
    rw [abC8_radial_val_k0 u]
    by_cases hu : u ∈ insert 1 (insert 0 (∅ : Finset (Fin 8)))
    · rw [if_pos hu, if_pos hu, one_mul]
    · rw [if_neg hu, if_neg hu, zero_mul]
  rw [Finset.sum_congr rfl (fun u _ => by rw [hrow u, hfilt2 u])]
  have heq : (∑ w : Fin 8,
      (if w ∈ insert 1 (insert 0 (∅ : Finset (Fin 8)))
        then abC8 w 1 + abC8 w 0 else 0))
    = ∑ w ∈ insert 1 (insert 0 (∅ : Finset (Fin 8))),
        (abC8 w 1 + abC8 w 0) :=
    (Finset.sum_subset (Finset.subset_univ _)
      (fun w _ hw => if_neg hw)).symm
  rw [heq]
  simp [Finset.sum_insert, Finset.sum_singleton]
  have e0 : abC8 1 1 = 0 := rfl
  have e1 : abC8 1 0 = 1 := rfl
  have e2 : abC8 0 1 = 1 := rfl
  have e3 : abC8 0 0 = 0 := rfl
  norm_num [e0, e1, e2, e3]

/-! ## The three hypothesis fences -/

/-- **The pseudo-edge fence** (`hedge` load-bearing): the path `P₃` at
the NON-edge `(0, 2)` — every hypothesis of `radialVec_quadForm_ge`
holds at `k = 0`, `d = 2`, `ρ = 1` except `hedge : A x y ≠ 0` — and the
conclusion fails: the test vector is the indicator of `{0, 2}`, which
spans no edge, so the numerator is `0 < 2`. -/
theorem abP3_pseudoEdge_fence :
    IsTreeBall abP3 abP3_isSymm 0 2 2 1 ∧
      ¬ (2 + 4 * ((0 : ℕ) : ℝ) * ((2 - 1 : ℕ) : ℝ) * 1
        ≤ quadForm abP3 (radialVec abP3 abP3_isSymm 0 2 1 0)) := by
  have hisSymm : abP3.IsSymm := by
    refine Matrix.IsSymm.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [abP3]
  have hconn : (supportGraph abP3 hisSymm).Connected := by
    have hfrom0 : ∀ v : Fin 3, (supportGraph abP3 hisSymm).Reachable 0 v := by
      intro v
      fin_cases v
      · exact ⟨SimpleGraph.Walk.nil⟩
      · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
          (supportGraph_adj.2 ⟨by decide, by simp [abP3]⟩) SimpleGraph.Walk.nil⟩
      · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 2)
          (supportGraph_adj.2 ⟨by decide, by simp [abP3]⟩)
          (SimpleGraph.Walk.cons (u := 1) (v := 2) (w := 2)
            (supportGraph_adj.2 ⟨by decide, by simp [abP3]⟩)
            SimpleGraph.Walk.nil)⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    exact ⟨0, hfrom0⟩
  refine ⟨isTreeBall_one_of_connected hconn (by decide) 2, ?_⟩
  have hd0 : (supportGraph abP3 hisSymm).dist 0 0 = 0 := by simp
  have hd2 : (supportGraph abP3 hisSymm).dist 2 2 = 0 := by simp
  have hd10 : (supportGraph abP3 hisSymm).dist 1 0 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2
      (supportGraph_adj.2 ⟨by decide, by simp [abP3]⟩)
  have hd12 : (supportGraph abP3 hisSymm).dist 1 2 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2
      (supportGraph_adj.2 ⟨by decide, by simp [abP3]⟩)
  have f0 : radialVec abP3 hisSymm 0 2 1 0 0 = 1 := by
    have hle : levE abP3 hisSymm 0 2 0 ≤ 0 := by
      simp only [levE]; omega
    simp only [radialVec, if_pos hle, one_pow]
  have f1 : radialVec abP3 hisSymm 0 2 1 0 1 = 0 := by
    have : ¬ (levE abP3 hisSymm 0 2 1 ≤ 0) := by
      simp only [levE]
      omega
    simp only [radialVec, if_neg this]
  have f2 : radialVec abP3 hisSymm 0 2 1 0 2 = 1 := by
    have hle : levE abP3 hisSymm 0 2 2 ≤ 0 := by
      simp only [levE]; omega
    simp only [radialVec, if_pos hle, one_pow]
  have hq : quadForm abP3 (radialVec abP3 hisSymm 0 2 1 0) = 0 := by
    simp only [quadForm, Matrix.dotProduct, Matrix.mulVec, Fin.sum_univ_three,
      f0, f1, f2]
    norm_num [abP3]
  intro hcon
  rw [hq] at hcon
  norm_num at hcon

/-- The edge `K₂` at fractional weight `1/2` — the `h01` fence's
fixture. -/
noncomputable def abHalfK2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1 / 2; 1 / 2, 0]

theorem abHalfK2_isSymm : abHalfK2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [abHalfK2]

theorem abHalfK2_supportGraph_connected :
    (supportGraph abHalfK2 abHalfK2_isSymm).Connected := by
  have hfrom0 : ∀ v : Fin 2, (supportGraph abHalfK2 abHalfK2_isSymm).Reachable 0 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
        (supportGraph_adj.2 ⟨by decide, by simp [abHalfK2]⟩) SimpleGraph.Walk.nil⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, hfrom0⟩

/-- The one-vertex loop with an unreachable partner — the `hxy` fence's
fixture (level 0 collects the endpoint and the junk-zero vertex, so
the cardinality equation `2` genuinely holds). -/
def abLoop2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

theorem abLoop2_isSymm : abLoop2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [abLoop2]

/-- **The fractional-weight fence** (`h01` load-bearing): the edge
`K₂` with weight `1/2` — every hypothesis of `radialVec_quadForm_ge`
holds at `k = 0`, `d = 2`, `ρ = 1` except the weight discipline
`h01` (the weight `1/2` is neither `0` nor `≥ 1`) — and the
conclusion fails: the numerator is `1/2 + 1/2 = 1 < 2`. A parent edge
of fractional weight is exactly what the from-below harvest cannot
price. -/
theorem abHalfK2_fractional_fence :
    IsTreeBall abHalfK2 abHalfK2_isSymm 0 1 2 1 ∧
      ¬ (2 + 4 * ((0 : ℕ) : ℝ) * ((2 - 1 : ℕ) : ℝ) * 1
        ≤ quadForm abHalfK2 (radialVec abHalfK2 abHalfK2_isSymm 0 1 1 0)) := by
  refine ⟨isTreeBall_one_of_connected abHalfK2_supportGraph_connected
    (by decide) 2, ?_⟩
  have hd1 : (supportGraph abHalfK2 abHalfK2_isSymm).dist 1 1 = 0 := by simp
  have f0 : radialVec abHalfK2 abHalfK2_isSymm 0 1 1 0 0 = 1 := by
    have hle : levE abHalfK2 abHalfK2_isSymm 0 1 0 ≤ 0 := by
      simp only [levE]; simp
    simp only [radialVec, if_pos hle, one_pow]
  have f1 : radialVec abHalfK2 abHalfK2_isSymm 0 1 1 0 1 = 1 := by
    have hle : levE abHalfK2 abHalfK2_isSymm 0 1 1 ≤ 0 := by
      simp only [levE, hd1]; omega
    simp only [radialVec, if_pos hle, one_pow]
  have hq : quadForm abHalfK2 (radialVec abHalfK2 abHalfK2_isSymm 0 1 1 0) = 1 := by
    simp only [quadForm, Matrix.dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      f0, f1]
    norm_num [abHalfK2]
  intro hcon
  rw [hq] at hcon
  norm_num at hcon

/-- **The loop fence** (`hxy` load-bearing): the one-vertex loop with
an unreachable partner — every hypothesis of `radialVec_quadForm_ge`
holds at `k = 0`, `d = 2`, `ρ = 1`, `x = y = 0` except `hxy : x ≠ y`
(the level-0 cardinality equation `2` is met by the endpoint *plus the
unreachable junk-zero vertex*, so `IsTreeBall` genuinely holds) — and
the conclusion fails: the numerator is the loop's single contribution
`1 < 2`. The distinct-endpoints hypothesis is what makes the
selection's `(x, y)` and `(y, x)` two different ordered pairs. -/
theorem abLoop2_loop_fence :
    IsTreeBall abLoop2 abLoop2_isSymm 0 0 2 1 ∧
      ¬ (2 + 4 * ((0 : ℕ) : ℝ) * ((2 - 1 : ℕ) : ℝ) * 1
        ≤ quadForm abLoop2 (radialVec abLoop2 abLoop2_isSymm 0 0 1 0)) := by
  refine ⟨?_, ?_⟩
  · intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    have huniv : levClass abLoop2 abLoop2_isSymm 0 0 0 = Finset.univ := by
      ext z
      simp only [levClass, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases (show z = 0 ∨ z = 1 by fin_cases z <;> simp_all) with h | h
      · rw [h]; simp [levE]
      · rw [h]
        have h0 : (supportGraph abLoop2 abLoop2_isSymm).dist 1 0 = 0 :=
          SimpleGraph.dist_eq_zero_of_not_reachable
            (by
              rintro ⟨p⟩
              cases p with
              | @cons _ v2 _ hz _ =>
                  have hpos := (supportGraph_adj.1 hz).2
                  fin_cases v2 <;> simp [abLoop2] at hpos)
        simp [levE, h0]
    rw [huniv]
    simp
  · have f0 : radialVec abLoop2 abLoop2_isSymm 0 0 1 0 0 = 1 := by
      have hle : levE abLoop2 abLoop2_isSymm 0 0 0 ≤ 0 := by
        simp only [levE]; simp
      simp only [radialVec, if_pos hle, one_pow]
    have f1 : radialVec abLoop2 abLoop2_isSymm 0 0 1 0 1 = 1 := by
      have h0 : (supportGraph abLoop2 abLoop2_isSymm).dist 1 0 = 0 :=
        SimpleGraph.dist_eq_zero_of_not_reachable
          (by
            rintro ⟨p⟩
            cases p with
            | @cons _ v2 _ hz _ =>
                have hpos := (supportGraph_adj.1 hz).2
                fin_cases v2 <;> simp [abLoop2] at hpos)
      have hle : levE abLoop2 abLoop2_isSymm 0 0 1 ≤ 0 := by
        simp only [levE, h0]
        omega
      simp only [radialVec, if_pos hle, one_pow]
    have hq : quadForm abLoop2 (radialVec abLoop2 abLoop2_isSymm 0 0 1 0) = 1 := by
      simp only [quadForm, Matrix.dotProduct, Matrix.mulVec, Fin.sum_univ_two,
        f0, f1]
      norm_num [abLoop2]
    intro hcon
    rw [hq] at hcon
    norm_num at hcon

end SpectralGraphTheory.QA

namespace SpectralGraphTheory.QA

/-! ## Step 4: the two-vector orthogonalization — QA

**The C₈ antipodal-pair positive** (`abC8_twoEdge_*`, `abC8_far_fence`,
`abC8_twoEdge_secondEval_thm`): at the edges `(0, 1)` and `(4, 5)` —
`distEdge = 3`, so the far-apart hypothesis holds at `k = 0` — the
two-edge vector's interface is pinned both raw and through the theorems,
and the headline `twoEdgeVec_secondEval_le` lands its first instance.
The equal-mass route is genuinely two-way: the orthogonality
`⟨g, 1⟩ = 0` is computed raw (`4 − 4 = 0` by per-vertex enumeration at
the two value oracles) and by the theorem
(`twoEdgeVec_dotProduct_onesVec` through `IsTreeBall`'s level equations
— level-1 of `(4, 5)` pinned to exactly `{3, 6}` by adjacency-level
facts, the `(0, 1)` pin's mirror). The squared norm at `k = 1` is
`8 = 4 (k+1)` by the theorem through the delivered antipodal ball
disjointness. The numerator is raw by decomposition: `Q(g) = 8` from
`Q(f₁) = 6` (the Step-3b raw pin), `Q(f₂) = 6` (its `(4, 5)` mirror),
and the cross term `⟨f₁, A f₂⟩ = 2` (the two cross edges `(2, 3)` and
`(6, 7)`), joined by the module's own expansion `quadForm_sub`.

**The `hfar` fence** (`abC8_far_fence`): every hypothesis of the
numerator bound holds at `k = 1` — both one-level-deeper tree balls are
genuine on C₈ (levels 0–2 all full) — except the far-apart threshold:
`distEdge = 3 < (k+1) + (k+1) = 4`, and the numerator bound fails at
`8 < 12`: the two radius-`k` balls are still disjoint (the norm identity
survives) but the radius-`(k+1)` balls overlap, and the cross edges
`(2, 3)`/`(6, 7)` are exactly what the from-below harvest cannot price
when the two-edge selection is off. The separation threshold is
load-bearing at its exact constant.

**The overlap fence** (`abP3_overlap_fence`): the P₃ edge pair
`(0, 1)`/`(1, 2)` at `k = 0` — both one-level tree balls hold, but the
radius-0 balls share the vertex `1`, and the norm identity fails at
`2 ≠ 4`: without ball disjointness the two vectors' supports overlap
and the layer-cake norms do not add. Disjointness isolated exactly.

**The headline instance** (`abC8_twoEdge_secondEval_thm`): on the C₈
antipodal pair at `k = 0`, the theorem gives
`secondEval (2•1 − A) ≤ 2 − (2 + 0)/2 = 1` — the first eigenvalue-level
statement of the Alon–Boppana program, at `IsDRegular abC8 2` (row sums
2 by rfl-verified entries) and the engine hypotheses discharged through
the delivered Step-1 facts.
-/

private theorem abC8_deg_two : ∀ i : Fin 8, deg abC8 i = 2 := by
  intro i
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by
      fin_cases i
      all_goals simp_all) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [deg, Fin.sum_univ_eight]
    have e0 : abC8 0 0 = 0 := rfl
    have e1 : abC8 0 1 = 1 := rfl
    have e2 : abC8 0 2 = 0 := rfl
    have e3 : abC8 0 3 = 0 := rfl
    have e4 : abC8 0 4 = 0 := rfl
    have e5 : abC8 0 5 = 0 := rfl
    have e6 : abC8 0 6 = 0 := rfl
    have e7 : abC8 0 7 = 1 := rfl
    simp only [e0, e1, e2, e3, e4, e5, e6, e7]
    norm_num
  · rw [deg, Fin.sum_univ_eight]
    have e0 : abC8 1 0 = 1 := rfl
    have e1 : abC8 1 1 = 0 := rfl
    have e2 : abC8 1 2 = 1 := rfl
    have e3 : abC8 1 3 = 0 := rfl
    have e4 : abC8 1 4 = 0 := rfl
    have e5 : abC8 1 5 = 0 := rfl
    have e6 : abC8 1 6 = 0 := rfl
    have e7 : abC8 1 7 = 0 := rfl
    simp only [e0, e1, e2, e3, e4, e5, e6, e7]
    norm_num
  · rw [deg, Fin.sum_univ_eight]
    have e0 : abC8 2 0 = 0 := rfl
    have e1 : abC8 2 1 = 1 := rfl
    have e2 : abC8 2 2 = 0 := rfl
    have e3 : abC8 2 3 = 1 := rfl
    have e4 : abC8 2 4 = 0 := rfl
    have e5 : abC8 2 5 = 0 := rfl
    have e6 : abC8 2 6 = 0 := rfl
    have e7 : abC8 2 7 = 0 := rfl
    simp only [e0, e1, e2, e3, e4, e5, e6, e7]
    norm_num
  · rw [deg, Fin.sum_univ_eight]
    have e0 : abC8 3 0 = 0 := rfl
    have e1 : abC8 3 1 = 0 := rfl
    have e2 : abC8 3 2 = 1 := rfl
    have e3 : abC8 3 3 = 0 := rfl
    have e4 : abC8 3 4 = 1 := rfl
    have e5 : abC8 3 5 = 0 := rfl
    have e6 : abC8 3 6 = 0 := rfl
    have e7 : abC8 3 7 = 0 := rfl
    simp only [e0, e1, e2, e3, e4, e5, e6, e7]
    norm_num
  · rw [deg, Fin.sum_univ_eight]
    have e0 : abC8 4 0 = 0 := rfl
    have e1 : abC8 4 1 = 0 := rfl
    have e2 : abC8 4 2 = 0 := rfl
    have e3 : abC8 4 3 = 1 := rfl
    have e4 : abC8 4 4 = 0 := rfl
    have e5 : abC8 4 5 = 1 := rfl
    have e6 : abC8 4 6 = 0 := rfl
    have e7 : abC8 4 7 = 0 := rfl
    simp only [e0, e1, e2, e3, e4, e5, e6, e7]
    norm_num
  · rw [deg, Fin.sum_univ_eight]
    have e0 : abC8 5 0 = 0 := rfl
    have e1 : abC8 5 1 = 0 := rfl
    have e2 : abC8 5 2 = 0 := rfl
    have e3 : abC8 5 3 = 0 := rfl
    have e4 : abC8 5 4 = 1 := rfl
    have e5 : abC8 5 5 = 0 := rfl
    have e6 : abC8 5 6 = 1 := rfl
    have e7 : abC8 5 7 = 0 := rfl
    simp only [e0, e1, e2, e3, e4, e5, e6, e7]
    norm_num
  · rw [deg, Fin.sum_univ_eight]
    have e0 : abC8 6 0 = 0 := rfl
    have e1 : abC8 6 1 = 0 := rfl
    have e2 : abC8 6 2 = 0 := rfl
    have e3 : abC8 6 3 = 0 := rfl
    have e4 : abC8 6 4 = 0 := rfl
    have e5 : abC8 6 5 = 1 := rfl
    have e6 : abC8 6 6 = 0 := rfl
    have e7 : abC8 6 7 = 1 := rfl
    simp only [e0, e1, e2, e3, e4, e5, e6, e7]
    norm_num
  · rw [deg, Fin.sum_univ_eight]
    have e0 : abC8 7 0 = 1 := rfl
    have e1 : abC8 7 1 = 0 := rfl
    have e2 : abC8 7 2 = 0 := rfl
    have e3 : abC8 7 3 = 0 := rfl
    have e4 : abC8 7 4 = 0 := rfl
    have e5 : abC8 7 5 = 0 := rfl
    have e6 : abC8 7 6 = 1 := rfl
    have e7 : abC8 7 7 = 0 := rfl
    simp only [e0, e1, e2, e3, e4, e5, e6, e7]
    norm_num


theorem abC8_isDRegular : IsDRegular abC8 2 :=
  fun i => abC8_deg_two i

/-- A two-vertex distance lower bound by refutation: not equal (connected
graphs have no junk-zero distances), not adjacent (zero entry). -/
private theorem abC8_dist_ge_two (a b : Fin 8) (hne : a ≠ b) (hentry : abC8 a b = 0) :
    2 ≤ (supportGraph abC8 abC8_isSymm).dist a b := by
  by_contra hlt
  have h1 : (supportGraph abC8 abC8_isSymm).dist a b ≤ 1 := by omega
  rcases Nat.eq_zero_or_pos
    ((supportGraph abC8 abC8_isSymm).dist a b) with h0 | h0
  · rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 h0 with heq | hnr
    · exact hne heq
    · exact hnr (abC8_supportGraph_connected a b)
  · have hadj := SimpleGraph.dist_eq_one_iff_adj.1 (by omega :
      (supportGraph abC8 abC8_isSymm).dist a b = 1)
    have hpos := (supportGraph_adj.1 hadj).2
    rw [hentry] at hpos
    simp at hpos

theorem abC8_dist_2_4 : 2 ≤ (supportGraph abC8 abC8_isSymm).dist 2 4 :=
  abC8_dist_ge_two 2 4 (by decide) rfl

theorem abC8_dist_2_5 : 2 ≤ (supportGraph abC8 abC8_isSymm).dist 2 5 :=
  abC8_dist_ge_two 2 5 (by decide) rfl

theorem abC8_dist_7_4 : 2 ≤ (supportGraph abC8 abC8_isSymm).dist 7 4 :=
  abC8_dist_ge_two 7 4 (by decide) rfl

theorem abC8_dist_7_5 : 2 ≤ (supportGraph abC8 abC8_isSymm).dist 7 5 :=
  abC8_dist_ge_two 7 5 (by decide) rfl

/-- The radial vector of the antipodal edge `(4, 5)` at `k = 1`, `ρ = 1`
is the indicator of `{3, 4, 5, 6}`. -/
private theorem abC8_radial45_val (z : Fin 8) :
    radialVec abC8 abC8_isSymm 4 5 1 1 z
      = if z ∈ insert 6 (insert 5 (insert 4 (insert 3 (∅ : Finset (Fin 8)))))
        then (1 : ℝ) else 0 := by
  by_cases hz : z ∈ insert 6 (insert 5 (insert 4 (insert 3 (∅ : Finset (Fin 8)))))
  · rw [if_pos hz]
    have hle : levE abC8 abC8_isSymm 4 5 z ≤ 1 := by
      simp only [Finset.mem_insert, Finset.not_mem_empty, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · have hd : (supportGraph abC8 abC8_isSymm).dist 6 5 = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.2
            (supportGraph_adj.2 ⟨by decide, by rw [show abC8 6 5 = 1 from rfl]; norm_num⟩)
        simp only [levE]
        omega
      · simp only [levE]
        have h0 : (supportGraph abC8 abC8_isSymm).dist 5 5 = 0 := by simp
        omega
      · have hd : (supportGraph abC8 abC8_isSymm).dist 4 4 = 0 := by simp
        simp only [levE]
        omega
      · have hd : (supportGraph abC8 abC8_isSymm).dist 3 4 = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.2
            (supportGraph_adj.2 ⟨by decide, by rw [show abC8 3 4 = 1 from rfl]; norm_num⟩)
        simp only [levE]
        omega
    simp only [radialVec, if_pos hle, one_pow]
  · rw [if_neg hz]
    have hge : 2 ≤ levE abC8 abC8_isSymm 4 5 z := by
      have henum : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 7 := by
        by_contra hcon
        push_neg at hcon
        rcases hcon with ⟨h0, h1, h2, h7⟩
        rcases (show z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 by
            fin_cases z
            all_goals simp_all) with h' | h' | h' | h'
        · exact hz (by subst h'; decide)
        · exact hz (by subst h'; decide)
        · exact hz (by subst h'; decide)
        · exact hz (by subst h'; decide)
      rcases henum with rfl | rfl | rfl | rfl
      · simp only [levE]
        have h1 := abC8_dist_0_4
        have h2 := abC8_dist_0_5
        omega
      · simp only [levE]
        have h1 := abC8_dist_1_4
        have h2 := abC8_dist_1_5
        omega
      · simp only [levE]
        have h1 := abC8_dist_2_4
        have h2 := abC8_dist_2_5
        omega
      · simp only [levE]
        have h1 := abC8_dist_7_4
        have h2 := abC8_dist_7_5
        omega
    simp only [radialVec, if_neg (show ¬ levE abC8 abC8_isSymm 4 5 z ≤ 1 by omega)]


theorem abC8_levClass_one_45_eq :
    levClass abC8 abC8_isSymm 4 5 1
      = insert 6 (insert 3 (∅ : Finset (Fin 8))) := by
  ext z
  simp only [levClass, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.not_mem_empty, or_false]
  have hself4 : (supportGraph abC8 abC8_isSymm).dist 4 4 = 0 := by simp
  have hself5 : (supportGraph abC8 abC8_isSymm).dist 5 5 = 0 := by simp
  have h34 : (supportGraph abC8 abC8_isSymm).dist 3 4 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2
      (supportGraph_adj.2 ⟨by decide, by rw [show abC8 3 4 = 1 from rfl]; norm_num⟩)
  have h65 : (supportGraph abC8 abC8_isSymm).dist 6 5 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2
      (supportGraph_adj.2 ⟨by decide, by rw [show abC8 6 5 = 1 from rfl]; norm_num⟩)
  rcases (show z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = 7 by
      fin_cases z
      all_goals simp_all) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [levE]
    have h1 := abC8_dist_0_4
    have h2 := abC8_dist_0_5
    constructor
    · intro hmin; exact absurd hmin (by omega)
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · simp only [levE]
    have h1 := abC8_dist_1_4
    have h2 := abC8_dist_1_5
    constructor
    · intro hmin; exact absurd hmin (by omega)
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · simp only [levE]
    have h1 := abC8_dist_2_4
    have h2 := abC8_dist_2_5
    constructor
    · intro hmin; exact absurd hmin (by omega)
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · simp only [levE]
    have hne := abC8_dist_ne_zero (by decide : (3 : Fin 8) ≠ 5)
    constructor
    · intro _; trivial
    · intro _; omega
  · simp only [levE]
    constructor
    · intro hmin; exact absurd hmin (by omega)
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · simp only [levE]
    constructor
    · intro hmin; exact absurd hmin (by omega)
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · simp only [levE]
    have hne := abC8_dist_ne_zero (by decide : (6 : Fin 8) ≠ 4)
    constructor
    · intro _; trivial
    · intro _; omega
  · simp only [levE]
    have h1 := abC8_dist_7_4
    have h2 := abC8_dist_7_5
    constructor
    · intro hmin; exact absurd hmin (by omega)
    · rintro (h' | h') <;> exact absurd h' (by decide)

theorem abC8_isTreeBall_45 : IsTreeBall abC8 abC8_isSymm 4 5 2 2 := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · rw [levClass_zero_card abC8_supportGraph_connected (by decide)]
    norm_num
  · rw [abC8_levClass_one_45_eq]
    have hcard : (insert 6 (insert 3 (∅ : Finset (Fin 8)))).card = 2 := by
      decide
    rw [hcard]
    norm_num


/-! ### The sums of the two radial vectors (the equal-mass input) -/

private theorem abC8_radial_sum_01 :
    ∑ z, radialVec abC8 abC8_isSymm 0 1 1 1 z = 4 := by
  have hfilt : ∀ z : Fin 8, radialVec abC8 abC8_isSymm 0 1 1 1 z
      = if z ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))
        then (1 : ℝ) else 0 := abC8_radial_val
  rw [Finset.sum_congr rfl fun z _ => hfilt z]
  have heq : ∑ z : Fin 8,
      (if z ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))
        then (1 : ℝ) else 0)
      = ∑ z ∈ insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8))))), (1 : ℝ) :=
    (Finset.sum_subset (Finset.subset_univ _) fun z _ hz => if_neg hz).symm
  rw [heq, Finset.sum_const, nsmul_eq_mul]
  have hcard :
      (insert 7 (insert 2 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))).card = 4 := by
    decide
  rw [hcard]
  norm_num

private theorem abC8_radial_sum_45 :
    ∑ z, radialVec abC8 abC8_isSymm 4 5 1 1 z = 4 := by
  have hfilt : ∀ z : Fin 8, radialVec abC8 abC8_isSymm 4 5 1 1 z
      = if z ∈ insert 6 (insert 5 (insert 4 (insert 3 (∅ : Finset (Fin 8)))))
        then (1 : ℝ) else 0 := abC8_radial45_val
  rw [Finset.sum_congr rfl fun z _ => hfilt z]
  have heq : ∑ z : Fin 8,
      (if z ∈ insert 6 (insert 5 (insert 4 (insert 3 (∅ : Finset (Fin 8)))))
        then (1 : ℝ) else 0)
      = ∑ z ∈ insert 6 (insert 5 (insert 4 (insert 3 (∅ : Finset (Fin 8))))), (1 : ℝ) :=
    (Finset.sum_subset (Finset.subset_univ _) fun z _ hz => if_neg hz).symm
  rw [heq, Finset.sum_const, nsmul_eq_mul]
  have hcard :
      (insert 6 (insert 5 (insert 4 (insert 3 (∅ : Finset (Fin 8)))))).card = 4 := by
    decide
  rw [hcard]
  norm_num

/-! ### The orthogonality — two routes -/

theorem abC8_twoEdge_orth_raw :
    Matrix.dotProduct (twoEdgeVec abC8 abC8_isSymm 0 1 4 5 1 1) onesVec = 0 := by
  simp only [Matrix.dotProduct, twoEdgeVec, onesVec, mul_one,
    Finset.sum_sub_distrib]
  rw [abC8_radial_sum_01, abC8_radial_sum_45]
  norm_num

theorem abC8_twoEdge_orth_thm :
    Matrix.dotProduct (twoEdgeVec abC8 abC8_isSymm 0 1 4 5 1 1) onesVec = 0 :=
  twoEdgeVec_dotProduct_onesVec abC8_isTreeBall abC8_isTreeBall_45

/-! ### The squared norm at k = 1 — two routes -/

private theorem abC8_radial45_norm_raw :
    Matrix.dotProduct (radialVec abC8 abC8_isSymm 4 5 1 1)
      (radialVec abC8 abC8_isSymm 4 5 1 1) = 4 := by
  have hfilt : ∀ z : Fin 8,
      radialVec abC8 abC8_isSymm 4 5 1 1 z
        * radialVec abC8 abC8_isSymm 4 5 1 1 z
      = if z ∈ insert 6 (insert 5 (insert 4 (insert 3 (∅ : Finset (Fin 8)))))
        then (1 : ℝ) else 0 := by
    intro z
    rw [abC8_radial45_val z]
    by_cases hz : z ∈ insert 6 (insert 5 (insert 4 (insert 3 (∅ : Finset (Fin 8)))))
    · rw [if_pos hz]
      norm_num
    · rw [if_neg hz]
      norm_num
  simp only [Matrix.dotProduct]
  rw [Finset.sum_congr rfl fun z _ => hfilt z]
  have heq : ∑ z : Fin 8,
      (if z ∈ insert 6 (insert 5 (insert 4 (insert 3 (∅ : Finset (Fin 8)))))
        then (1 : ℝ) else 0)
      = ∑ z ∈ insert 6 (insert 5 (insert 4 (insert 3 (∅ : Finset (Fin 8))))), (1 : ℝ) :=
    (Finset.sum_subset (Finset.subset_univ _) fun z _ hz => if_neg hz).symm
  rw [heq, Finset.sum_const, nsmul_eq_mul]
  have hcard :
      (insert 6 (insert 5 (insert 4 (insert 3 (∅ : Finset (Fin 8)))))).card = 4 := by
    decide
  rw [hcard]
  norm_num

theorem abC8_twoEdge_norm_thm :
    Matrix.dotProduct (twoEdgeVec abC8 abC8_isSymm 0 1 4 5 1 1)
      (twoEdgeVec abC8 abC8_isSymm 0 1 4 5 1 1) = 8 := by
  have h := twoEdgeVec_dotProduct_self (d := 2) (k := 1) (ρ := 1)
    (x := 0) (y := 1) (u := 4) (v := 5) (by norm_num) abC8_isTreeBall
    abC8_isTreeBall_45 (by norm_num) abC8_ballE_disjoint_antipodal
  norm_num at h ⊢
  linarith


private theorem abC8_rowsum45 (j : Fin 8) :
    (∑ i, abC8 j i * radialVec abC8 abC8_isSymm 4 5 1 1 i)
      = if j = 2 ∨ j = 7 then (1 : ℝ)
        else if j = 4 ∨ j = 5 then (2 : ℝ)
        else if j = 3 ∨ j = 6 then (1 : ℝ) else 0 := by
  have hfilt : ∀ i : Fin 8, abC8 j i
      * radialVec abC8 abC8_isSymm 4 5 1 1 i
      = if i ∈ insert 6 (insert 5 (insert 4 (insert 3 (∅ : Finset (Fin 8)))))
        then abC8 j i else 0 := by
    intro i
    rw [abC8_radial45_val i]
    split_ifs with hi
    · ring
    · ring
  have hsub : (∑ i, abC8 j i * radialVec abC8 abC8_isSymm 4 5 1 1 i)
      = ∑ i ∈ insert 6 (insert 5 (insert 4 (insert 3 (∅ : Finset (Fin 8))))),
          abC8 j i := by
    rw [Finset.sum_congr rfl fun i _ => hfilt i]
    exact (Finset.sum_subset (Finset.subset_univ _)
      (fun i _ hi => if_neg hi)).symm
  rw [hsub]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by
      fin_cases j
      all_goals simp_all) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [Finset.sum_insert, Finset.sum_singleton]
    have e3 : abC8 0 3 = 0 := rfl
    have e4 : abC8 0 4 = 0 := rfl
    have e5 : abC8 0 5 = 0 := rfl
    have e6 : abC8 0 6 = 0 := rfl
    rw [e3, e4, e5, e6]
    norm_num
  · simp [Finset.sum_insert, Finset.sum_singleton]
    have e3 : abC8 1 3 = 0 := rfl
    have e4 : abC8 1 4 = 0 := rfl
    have e5 : abC8 1 5 = 0 := rfl
    have e6 : abC8 1 6 = 0 := rfl
    rw [e3, e4, e5, e6]
    norm_num
  · simp [Finset.sum_insert, Finset.sum_singleton]
    have e3 : abC8 2 3 = 1 := rfl
    have e4 : abC8 2 4 = 0 := rfl
    have e5 : abC8 2 5 = 0 := rfl
    have e6 : abC8 2 6 = 0 := rfl
    rw [e3, e4, e5, e6]
    norm_num
  · simp [Finset.sum_insert, Finset.sum_singleton]
    have e3 : abC8 3 3 = 0 := rfl
    have e4 : abC8 3 4 = 1 := rfl
    have e5 : abC8 3 5 = 0 := rfl
    have e6 : abC8 3 6 = 0 := rfl
    rw [e3, e4, e5, e6]
    norm_num
  · simp [Finset.sum_insert, Finset.sum_singleton]
    have e3 : abC8 4 3 = 1 := rfl
    have e4 : abC8 4 4 = 0 := rfl
    have e5 : abC8 4 5 = 1 := rfl
    have e6 : abC8 4 6 = 0 := rfl
    rw [e3, e4, e5, e6]
    norm_num
  · simp [Finset.sum_insert, Finset.sum_singleton]
    have e3 : abC8 5 3 = 0 := rfl
    have e4 : abC8 5 4 = 1 := rfl
    have e5 : abC8 5 5 = 0 := rfl
    have e6 : abC8 5 6 = 1 := rfl
    rw [e3, e4, e5, e6]
    norm_num
  · simp [Finset.sum_insert, Finset.sum_singleton]
    have e3 : abC8 6 3 = 0 := rfl
    have e4 : abC8 6 4 = 0 := rfl
    have e5 : abC8 6 5 = 1 := rfl
    have e6 : abC8 6 6 = 0 := rfl
    rw [e3, e4, e5, e6]
    norm_num
  · simp [Finset.sum_insert, Finset.sum_singleton]
    have e3 : abC8 7 3 = 0 := rfl
    have e4 : abC8 7 4 = 0 := rfl
    have e5 : abC8 7 5 = 0 := rfl
    have e6 : abC8 7 6 = 1 := rfl
    rw [e3, e4, e5, e6]
    norm_num

/-! ### The cross term and the second numerator — raw -/

theorem abC8_cross_raw :
    Matrix.dotProduct (radialVec abC8 abC8_isSymm 0 1 1 1)
      (abC8 *ᵥ radialVec abC8 abC8_isSymm 4 5 1 1) = 2 := by
  simp only [Matrix.dotProduct, Matrix.mulVec]
  have hterm : ∀ j : Fin 8,
      (radialVec abC8 abC8_isSymm 0 1 1 1 j
        * ∑ i, abC8 j i * radialVec abC8 abC8_isSymm 4 5 1 1 i)
      = if j = 2 ∨ j = 7 then (1 : ℝ) else 0 := by
    intro j
    rw [abC8_rowsum45 j, abC8_radial_val j]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by
        fin_cases j
        all_goals simp_all) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  rw [show ∑ j : Fin 8, (if j = 2 ∨ j = 7 then (1 : ℝ) else 0) = (2 : ℝ) from by
    rw [Fin.sum_univ_eight]
    have h0 : ¬ ((0 : Fin 8) = 2 ∨ (0 : Fin 8) = 7) := by simp
    have h1 : ¬ ((1 : Fin 8) = 2 ∨ (1 : Fin 8) = 7) := by simp
    have h2 : ((2 : Fin 8) = 2 ∨ (2 : Fin 8) = 7) := by simp
    have h3 : ¬ ((3 : Fin 8) = 2 ∨ (3 : Fin 8) = 7) := by simp
    have h4 : ¬ ((4 : Fin 8) = 2 ∨ (4 : Fin 8) = 7) := by simp
    have h5 : ¬ ((5 : Fin 8) = 2 ∨ (5 : Fin 8) = 7) := by simp
    have h6 : ¬ ((6 : Fin 8) = 2 ∨ (6 : Fin 8) = 7) := by simp
    have h7 : ((7 : Fin 8) = 2 ∨ (7 : Fin 8) = 7) := by simp
    rw [if_neg h0, if_neg h1, if_pos h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6,
      if_pos h7]
    norm_num]

theorem abC8_radial45_quadForm_raw :
    quadForm abC8 (radialVec abC8 abC8_isSymm 4 5 1 1) = 6 := by
  simp only [quadForm, Matrix.dotProduct, Matrix.mulVec]
  have hterm : ∀ j : Fin 8,
      (radialVec abC8 abC8_isSymm 4 5 1 1 j
        * ∑ i, abC8 j i * radialVec abC8 abC8_isSymm 4 5 1 1 i)
      = if j = 4 ∨ j = 5 then (2 : ℝ)
        else if j = 3 ∨ j = 6 then (1 : ℝ) else 0 := by
    intro j
    rw [abC8_rowsum45 j, abC8_radial45_val j]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by
        fin_cases j
        all_goals simp_all) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  have hsplit : ∀ j : Fin 8, (if j = 4 ∨ j = 5 then (2 : ℝ)
      else if j = 3 ∨ j = 6 then (1 : ℝ) else 0)
      = 2 * (if j ∈ insert 5 (insert 4 (∅ : Finset (Fin 8))) then (1 : ℝ) else 0)
        + (if j ∈ insert 6 (insert 3 (∅ : Finset (Fin 8))) then (1 : ℝ) else 0) := by
    intro j
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by
        fin_cases j
        all_goals simp_all) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  rw [Finset.sum_congr rfl fun j _ => hterm j,
    Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have c45 :
      (Finset.filter (fun x : Fin 8 => (x : Fin 8) = 5 ∨ (x : Fin 8) = 4)
        Finset.univ).card = 2 := by decide
  have c36 :
      (Finset.filter (fun x : Fin 8 => (x : Fin 8) = 6 ∨ (x : Fin 8) = 3)
        Finset.univ).card = 2 := by decide
  norm_num [c45, c36]

/-! ### The two-edge numerator, raw by decomposition -/

theorem abC8_twoEdge_quadForm_raw :
    quadForm abC8 (twoEdgeVec abC8 abC8_isSymm 0 1 4 5 1 1) = 8 := by
  have hfun : twoEdgeVec abC8 abC8_isSymm 0 1 4 5 1 1
      = radialVec abC8 abC8_isSymm 0 1 1 1
        - radialVec abC8 abC8_isSymm 4 5 1 1 := rfl
  rw [hfun, quadForm_sub abC8_isSymm]
  rw [show Matrix.dotProduct (radialVec abC8 abC8_isSymm 0 1 1 1)
      (abC8 *ᵥ radialVec abC8 abC8_isSymm 4 5 1 1) = 2 from
    abC8_cross_raw]
  rw [abC8_radial_quadForm_eq_six, abC8_radial45_quadForm_raw]
  norm_num


/-! ### The far-apart fence at k = 1 -/

theorem abC8_far_fence :
    IsTreeBall abC8 abC8_isSymm 0 1 2 2 ∧
    IsTreeBall abC8 abC8_isSymm 4 5 2 2 ∧
    ¬ ((1 + 1) + (1 + 1) < distEdge abC8 abC8_isSymm 0 1 4 5) ∧
    ¬ (2 * (2 + 4 * ((1 : ℕ) : ℝ) * ((2 - 1 : ℕ) : ℝ) * 1)
       ≤ quadForm abC8 (twoEdgeVec abC8 abC8_isSymm 0 1 4 5 1 1)) := by
  refine ⟨abC8_isTreeBall, abC8_isTreeBall_45, ?_, ?_⟩
  · have a07 : (supportGraph abC8 abC8_isSymm).Adj 0 7 :=
      supportGraph_adj.2 ⟨by decide, by rw [show abC8 0 7 = 1 from rfl]; norm_num⟩
    have a76 : (supportGraph abC8 abC8_isSymm).Adj 7 6 :=
      supportGraph_adj.2 ⟨by decide, by rw [show abC8 7 6 = 1 from rfl]; norm_num⟩
    have a65 : (supportGraph abC8 abC8_isSymm).Adj 6 5 :=
      supportGraph_adj.2 ⟨by decide, by rw [show abC8 6 5 = 1 from rfl]; norm_num⟩
    have hle := SimpleGraph.dist_le
      (SimpleGraph.Walk.cons (u := 0) (v := 7) (w := 5) a07
        (SimpleGraph.Walk.cons (u := 7) (v := 6) (w := 5) a76
          (SimpleGraph.Walk.cons (u := 6) (v := 5) (w := 5) a65
            SimpleGraph.Walk.nil)))
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hle
    intro h
    simp only [distEdge] at h
    omega
  · intro hle
    rw [abC8_twoEdge_quadForm_raw] at hle
    norm_num at hle

/-! ### The headline instance at k = 0 -/

theorem abC8_twoEdge_secondEval_thm :
    secondEval (((2 : ℕ) : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) - abC8)
      (smul_one_sub_isSymm abC8_isSymm 2) (by decide)
      ≤ (2 : ℝ) - 1 := by
  have hd : IsDRegular abC8 ((2 : ℕ) : ℝ) := abC8_isDRegular
  have hfar : (0 + 1) + (0 + 1) < distEdge abC8 abC8_isSymm 0 1 4 5 := by
    have h1 := abC8_dist_0_4
    have h2 := abC8_dist_0_5
    have h3 := abC8_dist_1_4
    have h4 := abC8_dist_1_5
    simp only [distEdge]
    omega
  have h := twoEdgeVec_secondEval_le (d := 2) (k := 0) (ρ := 1)
    (x := 0) (y := 1) (u := 4) (v := 5) abC8_h01 hd (by decide)
    (by rw [show abC8 0 1 = 1 from rfl]; norm_num) (by decide)
    (by rw [show abC8 4 5 = 1 from rfl]; norm_num)
    abC8_supportGraph_connected hfar (by norm_num)
    (isTreeBall_one_of_connected abC8_supportGraph_connected (by decide) 2)
    (isTreeBall_one_of_connected abC8_supportGraph_connected (by decide) 2)
    (by norm_num) (by norm_num) (by decide)
  norm_num at h ⊢
  linarith


/-! ### The P₃ overlap fence (norm identity) and loop fence (orthogonality) -/

private theorem abP3_isSymm : abP3.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [abP3]

private theorem abP3_conn :
    (supportGraph abP3 abP3_isSymm).Connected := by
  have hfrom0 : ∀ v : Fin 3, (supportGraph abP3 abP3_isSymm).Reachable 0 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
        (supportGraph_adj.2 ⟨by decide, by rw [show abP3 0 1 = 1 from rfl]; norm_num⟩)
        SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 2)
        (supportGraph_adj.2 ⟨by decide, by rw [show abP3 0 1 = 1 from rfl]; norm_num⟩)
        (SimpleGraph.Walk.cons (u := 1) (v := 2) (w := 2)
          (supportGraph_adj.2 ⟨by decide, by rw [show abP3 1 2 = 1 from rfl]; norm_num⟩)
          SimpleGraph.Walk.nil)⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, hfrom0⟩

private theorem abP3_dist_ne_zero {a b : Fin 3} (hne : a ≠ b) :
    (supportGraph abP3 abP3_isSymm).dist a b ≠ 0 :=
  SimpleGraph.dist_ne_zero_iff_ne_and_reachable.2 ⟨hne, abP3_conn a b⟩

private theorem abP3_dist_0_2 : (supportGraph abP3 abP3_isSymm).dist 0 2 = 2 := by
  have h1 : (supportGraph abP3 abP3_isSymm).Adj 0 1 :=
    supportGraph_adj.2 ⟨by decide, by rw [show abP3 0 1 = 1 from rfl]; norm_num⟩
  have h2 : (supportGraph abP3 abP3_isSymm).Adj 1 2 :=
    supportGraph_adj.2 ⟨by decide, by rw [show abP3 1 2 = 1 from rfl]; norm_num⟩
  have hw := SimpleGraph.dist_le
    (SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 2) h1
      (SimpleGraph.Walk.cons (u := 1) (v := 2) (w := 2) h2
        SimpleGraph.Walk.nil))
  simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hw
  have hne : (supportGraph abP3 abP3_isSymm).dist 0 2 ≠ 1 := by
    intro h1'
    have hadj := SimpleGraph.dist_eq_one_iff_adj.1 h1'
    have hpos := (supportGraph_adj.1 hadj).2
    rw [show abP3 0 2 = 0 from rfl] at hpos
    simp at hpos
  rcases Nat.eq_zero_or_pos
    ((supportGraph abP3 abP3_isSymm).dist 0 2) with h0 | h0
  · rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 h0 with heq | hnr
    · exact absurd heq.symm (by decide)
    · exact (hnr (abP3_conn 0 2)).elim
  · omega

private theorem abP3_levE01_0 : levE abP3 abP3_isSymm 0 1 0 = 0 := by
  simp only [levE]
  have h : (supportGraph abP3 abP3_isSymm).dist 0 0 = 0 := by simp
  omega

private theorem abP3_levE01_1 : levE abP3 abP3_isSymm 0 1 1 = 0 := by
  simp only [levE]
  have h : (supportGraph abP3 abP3_isSymm).dist 1 1 = 0 := by simp
  omega

private theorem abP3_levE01_2 : levE abP3 abP3_isSymm 0 1 2 = 1 := by
  simp only [levE]
  have hne0 : (supportGraph abP3 abP3_isSymm).dist 2 0 ≠ 0 :=
    abP3_dist_ne_zero (by decide)
  have h1 : (supportGraph abP3 abP3_isSymm).dist 2 1 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2
      (supportGraph_adj.2 ⟨by decide, by rw [show abP3 2 1 = 1 from rfl]; norm_num⟩)
  omega

private theorem abP3_levE12_0 : levE abP3 abP3_isSymm 1 2 0 = 1 := by
  rw [levE_comm]
  simp only [levE]
  have h2 : (supportGraph abP3 abP3_isSymm).dist 0 2 = 2 := abP3_dist_0_2
  have h1 : (supportGraph abP3 abP3_isSymm).dist 0 1 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2
      (supportGraph_adj.2 ⟨by decide, by rw [show abP3 0 1 = 1 from rfl]; norm_num⟩)
  omega

private theorem abP3_levE12_1 : levE abP3 abP3_isSymm 1 2 1 = 0 := by
  simp only [levE]
  have h : (supportGraph abP3 abP3_isSymm).dist 1 1 = 0 := by simp
  omega

private theorem abP3_levE12_2 : levE abP3 abP3_isSymm 1 2 2 = 0 := by
  simp only [levE]
  have h : (supportGraph abP3 abP3_isSymm).dist 2 2 = 0 := by simp
  omega

/-- **The overlap fence**: the radius-0 balls of the edges `(0, 1)` and
`(1, 2)` share the vertex `1` — both one-level tree balls hold, but the
balls are not disjoint, and the squared-norm identity fails: the
difference vector is `![1, 0, -1]`, of squared norm `2 ≠ 4 (k+1)`. -/
theorem abP3_overlap_fence :
    IsTreeBall abP3 abP3_isSymm 0 1 2 1 ∧
    IsTreeBall abP3 abP3_isSymm 1 2 2 1 ∧
    ¬ Disjoint (ballE abP3 abP3_isSymm 0 1 0) (ballE abP3 abP3_isSymm 1 2 0) ∧
    Matrix.dotProduct (twoEdgeVec abP3 abP3_isSymm 0 1 1 2 1 0)
      (twoEdgeVec abP3 abP3_isSymm 0 1 1 2 1 0) = 2 := by
  refine ⟨isTreeBall_one_of_connected abP3_conn (by decide) 2,
    isTreeBall_one_of_connected abP3_conn (by decide) 2, ?_, ?_⟩
  · intro hdis
    have m1 : (1 : Fin 3) ∈ ballE abP3 abP3_isSymm 0 1 0 := by
      simp only [ballE, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [abP3_levE01_1]
    have m2 : (1 : Fin 3) ∈ ballE abP3 abP3_isSymm 1 2 0 := by
      simp only [ballE, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [abP3_levE12_1]
    exact Finset.disjoint_right.1 hdis m2 m1
  · have v0 : twoEdgeVec abP3 abP3_isSymm 0 1 1 2 1 0 0 = 1 := by
      simp [twoEdgeVec, radialVec, abP3_levE01_0, abP3_levE12_0]
    have v1 : twoEdgeVec abP3 abP3_isSymm 0 1 1 2 1 0 1 = 0 := by
      simp [twoEdgeVec, radialVec, abP3_levE01_1, abP3_levE12_1]
    have v2 : twoEdgeVec abP3 abP3_isSymm 0 1 1 2 1 0 2 = -1 := by
      simp [twoEdgeVec, radialVec, abP3_levE01_2, abP3_levE12_2]
    simp only [Matrix.dotProduct, Fin.sum_univ_three]
    rw [v0, v1, v2]
    norm_num

/-! ## Step 5: the diameter-dependent packaging and the two Step-4
residuals -/

private theorem abC8_far01 :
    (0 + 1) + (0 + 1) < distEdge abC8 abC8_isSymm 0 1 4 5 := by
  have h1 := abC8_dist_0_4
  have h2 := abC8_dist_0_5
  have h3 := abC8_dist_1_4
  have h4 := abC8_dist_1_5
  simp only [distEdge]
  omega

/-- **The capstone instance on `C₈` at `k = 0`**: Nilli's packaged
bound evaluates to `2 − (1 + 2·0·√1)/1 = 1` — the same number as
Step 4's headline instance, now through the `√` packaging. -/
theorem abC8_nilli_instance :
    secondEval (((2 : ℕ) : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) - abC8)
      (smul_one_sub_isSymm abC8_isSymm 2) (by decide)
      ≤ (2 : ℝ) - 1 := by
  have h := alonBoppana_nilli (d := 2) (k := 0) abC8_h01 abC8_isDRegular
    (x := 0) (y := 1) (u := 4) (v := 5) (by decide)
    (by rw [show abC8 0 1 = 1 from rfl]; norm_num) (by decide)
    (by rw [show abC8 4 5 = 1 from rfl]; norm_num)
    abC8_supportGraph_connected abC8_far01 (by norm_num)
    (isTreeBall_one_of_connected abC8_supportGraph_connected (by decide) 2)
    (isTreeBall_one_of_connected abC8_supportGraph_connected (by decide) 2)
    (by decide)
  norm_num at h ⊢
  exact h

/-- **The classical-shape instance on `C₈` at `k = 0`**: the error
term `2√(d−1)/(k+1)` evaluates to `2`, so the bound reads
`secondEval ≤ 2 − 2 + 2 = 2` — the honest weak-at-small-`k` reading
of the qualification trap: at the smallest usable radius the error
swallows the content. -/
theorem abC8_nilli_classical_instance :
    secondEval (((2 : ℕ) : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) - abC8)
      (smul_one_sub_isSymm abC8_isSymm 2) (by decide)
      ≤ (2 : ℝ) - 2 * 1 + 2 * 1 / 1 := by
  have h := alonBoppana_nilli_classical (d := 2) (k := 0) abC8_h01
    abC8_isDRegular (x := 0) (y := 1) (u := 4) (v := 5) (by decide)
    (by rw [show abC8 0 1 = 1 from rfl]; norm_num) (by decide)
    (by rw [show abC8 4 5 = 1 from rfl]; norm_num)
    abC8_supportGraph_connected abC8_far01 (by norm_num)
    (isTreeBall_one_of_connected abC8_supportGraph_connected (by decide) 2)
    (isTreeBall_one_of_connected abC8_supportGraph_connected (by decide) 2)
    (by decide)
  norm_num at h ⊢
  exact h

/-- **The diameter bookkeeping instance**: the far-apart hypothesis at
`k = 0` puts `2 (0+1) + 1 = 3 ≤ diam (supportGraph C₈)` through the
bridge `distEdge_le_diam` — the honest `k + 1 ≤ ⌊diam/2⌋` constraint
on real input (C₈'s actual diameter is `4`). -/
theorem abC8_diam_ge_three :
    (3 : ℕ) ≤ (supportGraph abC8 abC8_isSymm).diam :=
  alonBoppana_diam_ge abC8_supportGraph_connected abC8_far01

/-! ### The loop-pair orthogonality fence -/

/-- The `P₃` fixture plus a loop at vertex `2`: the loop contributes
no support-graph edge, so distances and levels agree with `abP3`'s. -/
def abP3L : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 1, 0, 1; 0, 1, 1]

theorem abP3L_isSymm : abP3L.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [abP3L]

private theorem abP3L_supportGraph_eq :
    supportGraph abP3L abP3L_isSymm = supportGraph abP3 abP3_isSymm := by
  ext i j
  rw [supportGraph_adj, supportGraph_adj]
  fin_cases i <;> fin_cases j <;> simp [abP3L, abP3]

private theorem abP3L_conn :
    (supportGraph abP3L abP3L_isSymm).Connected := by
  rw [abP3L_supportGraph_eq]
  exact abP3_conn

private theorem abP3L_dist_0_2 :
    (supportGraph abP3L abP3L_isSymm).dist 0 2 = 2 := by
  rw [abP3L_supportGraph_eq]
  exact abP3_dist_0_2

private theorem abP3L_dist_1_2 :
    (supportGraph abP3L abP3L_isSymm).dist 1 2 = 1 := by
  rw [abP3L_supportGraph_eq]
  exact SimpleGraph.dist_eq_one_iff_adj.2
    (supportGraph_adj.2 ⟨by decide, by rw [show abP3 1 2 = 1 from rfl]; norm_num⟩)

private theorem abP3L_dist_2_2 :
    (supportGraph abP3L abP3L_isSymm).dist 2 2 = 0 := by
  simp

/-- **The loop-pair orthogonality fence** (a priced Step-4 residual):
the pair `(0, 1)`/`(2, 2)` on `P₃`-plus-loop. The genuine edge's
one-level tree ball holds; the *loop's* does not — its level-0 class
is `{2}`, of cardinality `1 ≠ 2 (d−1)⁰` — and the orthogonality
conclusion fails with it: the difference vector `![1, 1, −1]` has
total mass `1 ≠ 0`. `IsTreeBall` is isolated exactly where
`twoEdgeVec_dotProduct_onesVec` consumes it: a loop is not an edge
with two endpoints. -/
theorem abP3L_loop_pair_fence :
    IsTreeBall abP3L abP3L_isSymm 0 1 2 1 ∧
    ¬ IsTreeBall abP3L abP3L_isSymm 2 2 2 1 ∧
    Matrix.dotProduct (twoEdgeVec abP3L abP3L_isSymm 0 1 2 2 1 0)
      onesVec = 1 := by
  refine ⟨isTreeBall_one_of_connected abP3L_conn (by decide) 2, ?_, ?_⟩
  · intro h
    have hcard := h 0 (by norm_num)
    -- level 0 of the loop edge is exactly {2}, card 1 ≠ 2
    have hlev : ∀ z : Fin 3,
        levE abP3L abP3L_isSymm 2 2 z = 0 ↔ z = 2 := by
      intro z
      have hmin : levE abP3L abP3L_isSymm 2 2 z
          = (supportGraph abP3L abP3L_isSymm).dist z 2 := by
        simp only [levE, min_self]
      rw [hmin]
      constructor
      · intro h0
        rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 h0 with heq | hnr
        · exact heq
        · exact absurd (abP3L_conn z 2) hnr
      · intro hz
        subst hz
        exact SimpleGraph.dist_self
    have hcls : (levClass abP3L abP3L_isSymm 2 2 0)
        = insert 2 (∅ : Finset (Fin 3)) := by
      ext z
      simp only [levClass, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hlev z]
      simp
    rw [hcls,
      Finset.card_insert_of_not_mem (Finset.not_mem_empty 2)] at hcard
    simp at hcard
  · -- the difference vector is ![1, 1, -1]: total mass 1 ≠ 0
    have l0 : levE abP3L abP3L_isSymm 0 1 0 = 0 := by
      rw [show levE abP3L abP3L_isSymm 0 1 0 = levE abP3 abP3_isSymm 0 1 0 from by
        simp only [levE, abP3L_supportGraph_eq]]
      exact abP3_levE01_0
    have l1 : levE abP3L abP3L_isSymm 0 1 1 = 0 := by
      rw [show levE abP3L abP3L_isSymm 0 1 1 = levE abP3 abP3_isSymm 0 1 1 from by
        simp only [levE, abP3L_supportGraph_eq]]
      exact abP3_levE01_1
    have l2 : levE abP3L abP3L_isSymm 0 1 2 = 1 := by
      rw [show levE abP3L abP3L_isSymm 0 1 2 = levE abP3 abP3_isSymm 0 1 2 from by
        simp only [levE, abP3L_supportGraph_eq]]
      exact abP3_levE01_2
    have r0 : levE abP3L abP3L_isSymm 2 2 0 = 2 := by
      simp only [levE, min_self]
      rw [abP3L_dist_0_2]
    have r1 : levE abP3L abP3L_isSymm 2 2 1 = 1 := by
      simp only [levE, min_self]
      rw [abP3L_dist_1_2]
    have r2 : levE abP3L abP3L_isSymm 2 2 2 = 0 := by
      simp only [levE, min_self]
      rw [abP3L_dist_2_2]
    have v0 : twoEdgeVec abP3L abP3L_isSymm 0 1 2 2 1 0 0 = 1 := by
      simp [twoEdgeVec, radialVec, l0, r0]
    have v1 : twoEdgeVec abP3L abP3L_isSymm 0 1 2 2 1 0 1 = 1 := by
      simp [twoEdgeVec, radialVec, l1, r1]
    have v2 : twoEdgeVec abP3L abP3L_isSymm 0 1 2 2 1 0 2 = -1 := by
      simp [twoEdgeVec, radialVec, l2, r2]
    simp only [Matrix.dotProduct, onesVec, Fin.sum_univ_three]
    rw [v0, v1, v2]
    norm_num

/-! ### The independent engine route at the integer witness -/

/-- The integer witness `![1, 1, 0, −1, −1, −1, 0, 1]` on `C₈`: a
globally supported, integer-entry test vector structurally unlike the
radial pair — `+1` on `{0, 1, 7}`, `−1` on `{3, 4, 5}`, `0` off the
support. -/
def abW8 : Fin 8 → ℝ := ![1, 1, 0, -1, -1, -1, 0, 1]

private def abWS : Finset (Fin 8) :=
  insert 7 (insert 5 (insert 4 (insert 3 (insert 1 (insert 0 (∅ : Finset (Fin 8)))))))

private theorem abW8_val (z : Fin 8) :
    abW8 z
      = if z ∈ abWS then (if z = 0 ∨ z = 1 ∨ z = 7 then (1 : ℝ) else (-1 : ℝ))
        else 0 := by
  rcases (show z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = 7 by
      fin_cases z <;> simp_all) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- The witness's squared norm, raw: `⟨w, w⟩ = 6`. -/
theorem abW8_dot_self :
    Matrix.dotProduct abW8 abW8 = 6 := by
  simp only [Matrix.dotProduct, Fin.sum_univ_eight]
  have w0 : abW8 0 = 1 := rfl
  have w1 : abW8 1 = 1 := rfl
  have w2 : abW8 2 = 0 := rfl
  have w3 : abW8 3 = -1 := rfl
  have w4 : abW8 4 = -1 := rfl
  have w5 : abW8 5 = -1 := rfl
  have w6 : abW8 6 = 0 := rfl
  have w7 : abW8 7 = 1 := rfl
  rw [w0, w1, w2, w3, w4, w5, w6, w7]
  norm_num

/-- The witness is orthogonal to `onesVec`, raw: `∑ w = 0`. -/
theorem abW8_orth :
    Matrix.dotProduct abW8 onesVec = 0 := by
  simp only [Matrix.dotProduct, onesVec, Fin.sum_univ_eight, mul_one]
  have w0 : abW8 0 = 1 := rfl
  have w1 : abW8 1 = 1 := rfl
  have w2 : abW8 2 = 0 := rfl
  have w3 : abW8 3 = -1 := rfl
  have w4 : abW8 4 = -1 := rfl
  have w5 : abW8 5 = -1 := rfl
  have w6 : abW8 6 = 0 := rfl
  have w7 : abW8 7 = 1 := rfl
  rw [w0, w1, w2, w3, w4, w5, w6, w7]
  norm_num

/-- The witness's adjacency quadratic form, raw: `⟨w, A w⟩ = 8` — the
support-filtered double sum, every `abC8` entry by `rfl` (the eight
ordered same-sign adjacencies `(0,1)`, `(1,0)`, `(0,7)`, `(7,0)`,
`(3,4)`, `(4,3)`, `(4,5)`, `(5,4)` each contributing `1`). -/
theorem abC8_quadForm_abW8 :
    quadForm abC8 abW8 = 8 := by
  have hrow : ∀ u : Fin 8,
      (∑ v : Fin 8, abC8 u v * abW8 v)
        = ∑ v ∈ abWS,
            abC8 u v * (if v = 0 ∨ v = 1 ∨ v = 7 then (1 : ℝ) else (-1 : ℝ)) := by
    intro u
    have hfilt : ∀ v : Fin 8, abC8 u v * abW8 v
        = if v ∈ abWS
          then abC8 u v * (if v = 0 ∨ v = 1 ∨ v = 7 then (1 : ℝ) else (-1 : ℝ)) else 0 := by
      intro v
      rw [abW8_val v]
      by_cases hv : v ∈ abWS
      · rw [if_pos hv, if_pos hv]
      · rw [if_neg hv, if_neg hv, mul_zero]
    rw [Finset.sum_congr rfl (fun v _ => hfilt v)]
    exact (Finset.sum_subset (Finset.subset_univ _)
      (fun v _ hv => if_neg hv)).symm
  simp only [quadForm, Matrix.dotProduct, Matrix.mulVec]
  rw [Finset.sum_congr rfl (fun u _ => by rw [hrow u])]
  have hfilt2 : ∀ u : Fin 8,
      (abW8 u * ∑ v ∈ abWS,
          abC8 u v * (if v = 0 ∨ v = 1 ∨ v = 7 then (1 : ℝ) else (-1 : ℝ)))
      = if u ∈ abWS
        then abW8 u * ∑ v ∈ abWS,
            abC8 u v * (if v = 0 ∨ v = 1 ∨ v = 7 then (1 : ℝ) else (-1 : ℝ))
        else 0 := by
    intro u
    rw [abW8_val u]
    by_cases hu : u ∈ abWS
    · rw [if_pos hu, if_pos hu]
    · rw [if_neg hu, if_neg hu, zero_mul]
  rw [Finset.sum_congr rfl (fun u _ => hfilt2 u)]
  have houter : (∑ u : Fin 8,
      (if u ∈ abWS
        then abW8 u * ∑ v ∈ abWS,
            abC8 u v * (if v = 0 ∨ v = 1 ∨ v = 7 then (1 : ℝ) else (-1 : ℝ))
        else 0))
      = ∑ u ∈ abWS,
          abW8 u * ∑ v ∈ abWS,
            abC8 u v * (if v = 0 ∨ v = 1 ∨ v = 7 then (1 : ℝ) else (-1 : ℝ)) :=
    (Finset.sum_subset (Finset.subset_univ _)
      (fun u _ hu => if_neg hu)).symm
  rw [houter]
  simp [Finset.sum_insert, Finset.sum_singleton, abWS]
  have w0 : abW8 0 = 1 := rfl
  have w1 : abW8 1 = 1 := rfl
  have w3 : abW8 3 = -1 := rfl
  have w4 : abW8 4 = -1 := rfl
  have w5 : abW8 5 = -1 := rfl
  have w7 : abW8 7 = 1 := rfl
  rw [w0, w1, w3, w4, w5, w7]
  have c70 : abC8 7 0 = 1 := rfl
  have c71 : abC8 7 1 = 0 := rfl
  have c73 : abC8 7 3 = 0 := rfl
  have c74 : abC8 7 4 = 0 := rfl
  have c75 : abC8 7 5 = 0 := rfl
  have c77 : abC8 7 7 = 0 := rfl
  have c50 : abC8 5 0 = 0 := rfl
  have c51 : abC8 5 1 = 0 := rfl
  have c53 : abC8 5 3 = 0 := rfl
  have c54 : abC8 5 4 = 1 := rfl
  have c55 : abC8 5 5 = 0 := rfl
  have c57 : abC8 5 7 = 0 := rfl
  have c40 : abC8 4 0 = 0 := rfl
  have c41 : abC8 4 1 = 0 := rfl
  have c43 : abC8 4 3 = 1 := rfl
  have c44 : abC8 4 4 = 0 := rfl
  have c45 : abC8 4 5 = 1 := rfl
  have c47 : abC8 4 7 = 0 := rfl
  have c30 : abC8 3 0 = 0 := rfl
  have c31 : abC8 3 1 = 0 := rfl
  have c33 : abC8 3 3 = 0 := rfl
  have c34 : abC8 3 4 = 1 := rfl
  have c35 : abC8 3 5 = 0 := rfl
  have c37 : abC8 3 7 = 0 := rfl
  have c10 : abC8 1 0 = 1 := rfl
  have c11 : abC8 1 1 = 0 := rfl
  have c13 : abC8 1 3 = 0 := rfl
  have c14 : abC8 1 4 = 0 := rfl
  have c15 : abC8 1 5 = 0 := rfl
  have c17 : abC8 1 7 = 0 := rfl
  have c00 : abC8 0 0 = 0 := rfl
  have c01 : abC8 0 1 = 1 := rfl
  have c03 : abC8 0 3 = 0 := rfl
  have c04 : abC8 0 4 = 0 := rfl
  have c05 : abC8 0 5 = 0 := rfl
  have c07 : abC8 0 7 = 1 := rfl
  norm_num [c70, c71, c73, c74, c75, c77, c50, c51, c53, c54, c55, c57, c40,
    c41, c43, c44, c45, c47, c30, c31, c33, c34, c35, c37, c10, c11, c13, c14,
    c15, c17, c00, c01, c03, c04, c05, c07]

/-- **The independent engine route** (the other priced Step-4
residual): `secondEval_le_rayleigh` at the integer witness gives
`secondEval (2•1 − C₈) ≤ (2·6 − 8)/6 = 2/3` — strictly stronger than
the radial route's `≤ 1`, through a structurally different test
vector. The raw pins (`abW8_dot_self`, `abC8_quadForm_abW8`,
`abW8_orth`) are computed with no theorem input. -/
theorem abC8_intWitness_secondEval_le :
    secondEval (((2 : ℕ) : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) - abC8)
      (smul_one_sub_isSymm abC8_isSymm 2) (by decide) ≤ 2 / 3 := by
  have hpsd : ∀ z : Fin 8 → ℝ,
      0 ≤ quadForm (((2 : ℕ) : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) - abC8) z := by
    intro z
    rw [quadForm_smul_one_sub]
    have hdom := quadForm_le_of_isDRegular abC8_isSymm abC8_nonneg abC8_isDRegular z
    norm_num
    linarith
  have hker := smul_one_sub_mulVec_onesVec abC8_isDRegular
  have hwne : abW8 ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    rw [show abW8 0 = 1 from rfl] at h0
    simp at h0
  have heng := secondEval_le_rayleigh
    (smul_one_sub_isSymm abC8_isSymm 2) hpsd hker (by decide) hwne abW8_orth
  rw [rayleigh, if_neg hwne, quadForm_smul_one_sub, abW8_dot_self,
    abC8_quadForm_abW8] at heng
  norm_num at heng ⊢
  exact heng

end SpectralGraphTheory.QA
