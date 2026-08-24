/-
  ResistanceMetric_QA.lean

  Purpose
  -------
  QA for the resistance-metric layer of
  `Scaffold.Mathlib.GraphTheory.Electrical` (backlog item 7's named
  residuals, `proposals/resistance-metric.md`, 2026-08-24): the maximum
  principle for unit-demand potentials, the definiteness residual
  `R u v = 0 ↔ u = v`, and the triangle inequality
  `R u w ≤ R u v + R v w`.

  Sections:

  - **The triangle's equality case on the three-vertex path** `0 — 1 — 2`
    (`connPathAdj`, reused from `Connectivity_QA`): the endpoint
    resistance `2` (pinned by the delivered `EffectiveResistance_QA`)
    equals the sum of the two edge resistances `1 + 1` (new witnesses
    `![1,0,0]`, `![0,0,−1]`) — the bound is *attained with equality* at
    the middle vertex, the sharpness witness that would catch a route
    whose constant is off; the degenerate instantiation `v = u` exercises
    the theorem's `u = v` branch.

  - **The strict case on the triangle graph `K₃`** (`fosterTriAdj`,
    reused from `Foster_QA` by QA-to-QA import): `2/3 < 2/3 + 2/3` — the
    honest gap between the two sides, against the equality fixture.

  - **Definiteness and confinement, positive witnesses on the path:** the
    middle potential `![2,1,0]` (the actual unit-current potential for
    the `e₀ − e₂` demand, voltage difference exactly the pinned `R = 2`)
    has its interior value pinned *strictly* between its boundary values,
    with both confinement halves instantiated at every vertex; the `iff`
    is consumed off-diagonal (`R 0 2 ≠ 0` through the forward direction)
    and on the diagonal.

  - **The signed fence** — one fixture fencing the nonnegativity
    hypothesis across all three theorems: `signedAdj` is symmetric, its
    support graph is connected (the path `1—0—2`), but it has a negative
    off-diagonal weight. Entrywise analysis of the demand equations
    yields the solution shape (`f 1 = f 0`, `f 2 = f 0 − 1` for the
    `e₀ − e₁` demand), value-pinning goes through the junk-free branch
    (`dif_pos` + the shape facts — the shelf's uniqueness theorem needs
    the nonnegativity hypothesis that fails here), and then:
    `R(0,1) = 0` with `0 ≠ 1` (definiteness **refuted in proved form**),
    `R(0,2) = 0`, `R(2,1) = −2`, and `¬(0 ≤ 0 + (−2))` (the triangle
    **refuted**); confinement's hypothesis-free conclusion is **refuted**
    at the interior vertex for every solution. With symmetry and
    connectivity verified on the fixture, exactly the nonnegativity
    hypothesis is isolated — the hypotheses are load-bearing, not
    decoration.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks interfaces where the arithmetic is
  fully evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Electrical
import Scaffold.QA.SpectralGraph.EffectiveResistance_QA
import Scaffold.QA.SpectralGraph.Foster_QA
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## The triangle inequality: equality on the path, strictness on K₃
-/

/-- The `e 0 − e 1` demand on the path is solved by `![1, 0, 0]`
(the voltage drops along the first edge only). -/
theorem path_demand01_QA :
    (laplacian connPathAdj).mulVec ![1, 0, 0]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, connPathAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three]

/-- **Edge resistance on the path:** `R 0 1 = 1`, pinned through the
agreement theorem at the witness above. -/
theorem path_R01_QA : effectiveResistance connPathAdj 0 1 = 1 :=
  effectiveResistance_eq connPathAdj connPathAdj_isSymm connPathAdj_nonneg
    connPath_supportGraph_connected
    ⟨![1, 0, 0], path_demand01_QA, by norm_num [Matrix.cons_val']⟩

/-- The `e 1 − e 2` demand on the path is solved by `![0, 0, −1]`. -/
theorem path_demand12_QA :
    (laplacian connPathAdj).mulVec ![0, 0, -1]
      = Pi.single 1 (1 : ℝ) - Pi.single 2 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, connPathAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three]

/-- **Second edge resistance on the path:** `R 1 2 = 1`. -/
theorem path_R12_QA : effectiveResistance connPathAdj 1 2 = 1 :=
  effectiveResistance_eq connPathAdj connPathAdj_isSymm connPathAdj_nonneg
    connPath_supportGraph_connected
    ⟨![0, 0, -1], path_demand12_QA, by norm_num [Matrix.cons_val']⟩

/-- **The equality case:** on the path, the triangle inequality is an
*identity* at the middle vertex — series resistances add exactly
(`2 = 1 + 1`). Any proof route with a slack constant fails here. -/
theorem path_triangle_eq_QA :
    effectiveResistance connPathAdj 0 2
      = effectiveResistance connPathAdj 0 1 + effectiveResistance connPathAdj 1 2 := by
  rw [path_effectiveResistance_eq_two_QA, path_R01_QA, path_R12_QA]; norm_num

/-- The triangle inequality *attained* on the path, through the
delivered theorem at the middle vertex. -/
theorem path_triangle_attained_QA :
    effectiveResistance connPathAdj 0 2
      ≤ effectiveResistance connPathAdj 0 1 + effectiveResistance connPathAdj 1 2 :=
  le_of_eq path_triangle_eq_QA

/-- The degenerate instantiation `v = u` (the theorem's `u = v` branch):
the bound reads `R 0 2 ≤ 0 + R 0 2` through the self-distance law. -/
theorem path_triangle_degenerate_QA :
    effectiveResistance connPathAdj 0 2
      ≤ effectiveResistance connPathAdj 0 0 + effectiveResistance connPathAdj 0 2 :=
  effectiveResistance_le_add connPathAdj connPathAdj_isSymm connPathAdj_nonneg
    connPath_supportGraph_connected 0 0 2

/-- **The strict case on `K₃`** (all three values `2/3` from
`Foster_QA`): the parallel detour strictly overpays, `2/3 < 4/3` — the
honest gap against the path's equality. -/
theorem tri_triangle_strict_QA :
    effectiveResistance fosterTriAdj 0 2
      < effectiveResistance fosterTriAdj 0 1 + effectiveResistance fosterTriAdj 1 2 := by
  rw [fosterTri_R02, fosterTri_R01, fosterTri_R12]; norm_num

/-!
## Definiteness and confinement: positive witnesses on the path
-/

/-- The `e 0 − e 2` demand on the path is solved by the middle
potential `![2, 1, 0]` — the actual unit-current potential (voltage
difference `2`, the pinned endpoint resistance; energy `2` by the
imported `path_energy_value_QA` up to sign). -/
theorem path_demand02_mid_QA :
    (laplacian connPathAdj).mulVec ![2, 1, 0]
      = Pi.single 0 (1 : ℝ) - Pi.single 2 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, connPathAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three] <;>
    try norm_num

/-- **Confinement instantiated at every vertex** of the path at the
middle potential `![2, 1, 0]`: both halves of the maximum principle
hold, exactly as the theorems claim. -/
theorem path_confine_all_QA (x : Fin 3) :
    min ((![2, 1, 0] : Fin 3 → ℝ) 0) ((![2, 1, 0] : Fin 3 → ℝ) 2)
      ≤ (![2, 1, 0] : Fin 3 → ℝ) x
      ∧ (![2, 1, 0] : Fin 3 → ℝ) x
        ≤ max ((![2, 1, 0] : Fin 3 → ℝ) 0) ((![2, 1, 0] : Fin 3 → ℝ) 2) :=
  ⟨laplacian_mulVec_eq_single_sub_single_min_le connPathAdj
      connPathAdj_isSymm connPathAdj_nonneg connPath_supportGraph_connected
      path_demand02_mid_QA x,
    laplacian_mulVec_eq_single_sub_single_le_max connPathAdj
      connPathAdj_isSymm connPathAdj_nonneg connPath_supportGraph_connected
      path_demand02_mid_QA x⟩

/-- **The interior value is strictly interior:** the middle vertex's
potential `1` lies strictly between the boundary values `0` and `2` —
confinement is not vacuous on this witness, and the boundary values are
genuinely apart (they differ by the pinned resistance `2`). -/
theorem path_confine_strict_QA :
    ![2, 1, 0] 2 < ![2, 1, 0] 1 ∧ ![2, 1, 0] 1 < ![2, 1, 0] 0 := by
  norm_num [Matrix.cons_val', Matrix.head_cons, Matrix.tail_cons]

/-- **Definiteness, off-diagonal:** the forward direction of the `iff`
converts `R 0 2 = 0` into the false `0 = 2` — on the path the pinned
value `2` makes the conversion land on a contradiction, exactly as the
theorem intends. -/
theorem path_definiteness_offdiag_QA : effectiveResistance connPathAdj 0 2 ≠ 0 := by
  intro h
  have h02 := (effectiveResistance_eq_zero_iff connPathAdj connPathAdj_isSymm
    connPathAdj_nonneg connPath_supportGraph_connected).1 h
  exact absurd h02 (by decide)

/-- **Definiteness, diagonal:** both sides of the `iff` hold at `u = v`,
through the self-distance law and `rfl`. -/
theorem path_definiteness_diag_QA :
    effectiveResistance connPathAdj 0 0 = 0 ∧ (0 : Fin 3) = 0 :=
  ⟨effectiveResistance_self connPathAdj 0, rfl⟩

/-!
## The signed fence: nonnegativity is load-bearing
-/

/-- The signed fixture: symmetric weights, support graph the connected
path `1 — 0 — 2`, but the `1–2` weight is **negative**. Symmetric and
connected, yet *not* a nonnegative network — exactly the hypothesis the
fence isolates. (Entrywise-if fixture pattern, per `Foster_QA`'s note
that matrix notation's zero-function normalization leaves `vecTail`
leftovers.) -/
def signedAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    if i = j then 0 else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then -1 else 1

theorem signedAdj_isSymm : signedAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [signedAdj]

theorem signedAdj_not_nonneg : ¬ (∀ i j : Fin 3, 0 ≤ signedAdj i j) := by
  intro h
  have h12 : (0 : ℝ) ≤ signedAdj 1 2 := h 1 2
  have e : signedAdj 1 2 = -1 := by simp [signedAdj]
  rw [e] at h12
  norm_num at h12

/-- The support graph of the signed fixture is connected: both other
vertices are adjacent to `0` through the two positive weights (the
negative edge `1–2` contributes nothing, leaving the path `1—0—2`). -/
theorem signed_supportGraph_connected :
    (supportGraph signedAdj signedAdj_isSymm).Connected := by
  have hfrom0 : ∀ v : Fin 3,
      (supportGraph signedAdj signedAdj_isSymm).Reachable 0 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
        ⟨by decide, by simp [signedAdj]⟩ SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 2) (w := 2)
        ⟨by decide, by simp [signedAdj]⟩ SimpleGraph.Walk.nil⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, hfrom0⟩

/-- **Hypothesis isolation, stated:** the fixture satisfies exactly the
two structural hypotheses of the new theorems and fails exactly the
third (nonnegativity). -/
theorem signed_fence_isolation_QA :
    signedAdj.IsSymm ∧ (supportGraph signedAdj signedAdj_isSymm).Connected
      ∧ ¬ (∀ i j : Fin 3, 0 ≤ signedAdj i j) :=
  ⟨signedAdj_isSymm, signed_supportGraph_connected, signedAdj_not_nonneg⟩

/-- Row `1` of the signed Laplacian in action, through the diffusion
form: `(L *ᵥ f) 1 = f 2 − f 0` (the zero degree at `1` collapses the
diagonal; the negative edge enters with its sign). -/
theorem signed_row1_QA (f : Fin 3 → ℝ) :
    (laplacian signedAdj).mulVec f 1 = f 2 - f 0 := by
  rw [laplacian_mulVec_apply signedAdj f 1]
  simp [signedAdj, Fin.sum_univ_three]

/-- Row `2` of the signed Laplacian in action: `(L *ᵥ f) 2 = f 1 − f 0`. -/
theorem signed_row2_QA (f : Fin 3 → ℝ) :
    (laplacian signedAdj).mulVec f 2 = f 1 - f 0 := by
  rw [laplacian_mulVec_apply signedAdj f 2]
  simp [signedAdj, Fin.sum_univ_three]

/-- **Solution shape of the `e 0 − e 1` demand:** every solution has
`f 1 = f 0` and `f 2 = f 0 − 1` — the interior vertex sits a full unit
*below* both boundary values, the configuration that breaks
confinement. -/
theorem signed_demand01_shape_QA (f : Fin 3 → ℝ)
    (hf : (laplacian signedAdj).mulVec f
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ)) :
    f 1 = f 0 ∧ f 2 = f 0 - 1 := by
  have r1 := congrFun hf 1
  have r2 := congrFun hf 2
  rw [signed_row1_QA f] at r1
  rw [signed_row2_QA f] at r2
  simp [Pi.sub_apply, Pi.single_apply] at r1 r2
  constructor <;> linarith

/-- Every `e 0 − e 1` resistance value on the signed fixture is `0` —
the voltage difference collapses along the equal boundary values. -/
theorem signed_value01_QA (r : ℝ) (h : IsEffectiveResistance signedAdj 0 1 r) :
    r = 0 := by
  obtain ⟨f, hf, hfr⟩ := h
  obtain ⟨h1, h2⟩ := signed_demand01_shape_QA f hf
  linarith

/-- **Value pin:** `R(0,1) = 0` on the signed fixture — through the
junk-free branch (`dif_pos`) with the value pinned by the shape lemma
(the shelf's uniqueness theorem is unavailable: it needs the
nonnegativity that fails here). -/
theorem signed_R01_QA : effectiveResistance signedAdj 0 1 = 0 := by
  have hex : ∃ r : ℝ, IsEffectiveResistance signedAdj 0 1 r :=
    ⟨0, ⟨![0, 0, -1],
      by
        funext i
        fin_cases i <;>
          simp [laplacian, degreeMatrix, deg, signedAdj, Matrix.mulVec,
            Matrix.dotProduct, Fin.sum_univ_three],
      by norm_num [Matrix.cons_val']⟩⟩
  simp only [effectiveResistance, dif_pos hex]
  exact signed_value01_QA _ (Classical.choose_spec hex)

/-- **Solution shape of the `e 0 − e 2` demand:** every solution has
`f 2 = f 0` and `f 1 = f 0 − 1`. -/
theorem signed_demand02_shape_QA (f : Fin 3 → ℝ)
    (hf : (laplacian signedAdj).mulVec f
      = Pi.single 0 (1 : ℝ) - Pi.single 2 (1 : ℝ)) :
    f 2 = f 0 ∧ f 1 = f 0 - 1 := by
  have r1 := congrFun hf 1
  have r2 := congrFun hf 2
  rw [signed_row1_QA f] at r1
  rw [signed_row2_QA f] at r2
  simp [Pi.sub_apply, Pi.single_apply] at r1 r2
  constructor <;> linarith

/-- **Value pin:** `R(0,2) = 0` on the signed fixture. -/
theorem signed_R02_QA : effectiveResistance signedAdj 0 2 = 0 := by
  have hex : ∃ r : ℝ, IsEffectiveResistance signedAdj 0 2 r :=
    ⟨0, ⟨![0, -1, 0],
      by
        funext i
        fin_cases i <;>
          simp [laplacian, degreeMatrix, deg, signedAdj, Matrix.mulVec,
            Matrix.dotProduct, Fin.sum_univ_three],
      by norm_num [Matrix.cons_val']⟩⟩
  simp only [effectiveResistance, dif_pos hex]
  obtain ⟨f, hf, hfr⟩ := Classical.choose_spec hex
  obtain ⟨h1, h2⟩ := signed_demand02_shape_QA f hf
  linarith

/-- **Solution shape of the `e 2 − e 1` demand:** every solution has
`f 2 = f 0 − 1` and `f 1 = f 0 + 1`, so the value is forced to `−2`. -/
theorem signed_R21_QA : effectiveResistance signedAdj 2 1 = -2 := by
  have hex : ∃ r : ℝ, IsEffectiveResistance signedAdj 2 1 r :=
    ⟨-2, ⟨![0, 1, -1],
      by
        funext i
        fin_cases i <;>
          simp [laplacian, degreeMatrix, deg, signedAdj, Matrix.mulVec,
            Matrix.dotProduct, Fin.sum_univ_three],
      by norm_num [Matrix.cons_val']⟩⟩
  simp only [effectiveResistance, dif_pos hex]
  obtain ⟨f, hf, hfr⟩ := Classical.choose_spec hex
  have r1 := congrFun hf 1
  have r2 := congrFun hf 2
  rw [signed_row1_QA f] at r1
  rw [signed_row2_QA f] at r2
  simp [Pi.sub_apply, Pi.single_apply] at r1 r2
  linarith

/-- **The definiteness fence:** on the symmetric, connectedly-supported
signed fixture, `R(0,1) = 0` at *distinct* vertices — the
hypothesis-free form of `effectiveResistance_pos_of_ne` is refuted in
proved form, with exactly the nonnegativity hypothesis failing. -/
theorem signed_pos_refuted_QA :
    ¬ ((0 : Fin 3) ≠ 1 → 0 < effectiveResistance signedAdj 0 1) := by
  intro h
  have h0 := h (by decide)
  rw [signed_R01_QA] at h0
  exact absurd h0 (by norm_num)

/-- **The triangle fence:** on the same fixture,
`R(0,1) = 0 ≤ R(0,2) + R(2,1) = 0 + (−2)` is refuted in proved form —
the signed triangle inequality *fails*, with exactly the nonnegativity
hypothesis failing. -/
theorem signed_triangle_refuted_QA :
    ¬ (effectiveResistance signedAdj 0 1
      ≤ effectiveResistance signedAdj 0 2 + effectiveResistance signedAdj 2 1) := by
  rw [signed_R01_QA, signed_R02_QA, signed_R21_QA]
  norm_num

/-- **The confinement fence:** for *every* solution of the `e 0 − e 1`
demand on the signed fixture, the min-side conclusion fails at the
interior vertex (`min (f 0) (f 1) = f 0 > f 0 − 1 = f 2`) — the
maximum principle's hypothesis-free form is refuted in proved form,
again with exactly the nonnegativity hypothesis failing. -/
theorem signed_confine_refuted_QA (f : Fin 3 → ℝ)
    (hf : (laplacian signedAdj).mulVec f
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ)) :
    ¬ (min (f 0) (f 1) ≤ f 2) := by
  obtain ⟨h1, h2⟩ := signed_demand01_shape_QA f hf
  intro hle
  rw [h1, min_self] at hle
  linarith

end SpectralGraphTheory.QA
