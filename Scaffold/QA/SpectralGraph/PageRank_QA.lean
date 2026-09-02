import Scaffold.Mathlib.GraphTheory.PageRank
import Scaffold.QA.SpectralGraph.IrreducibleStationary_QA
import Mathlib.Data.Matrix.Notation

/-!
# PageRank QA

Load-bearing QA for `Scaffold.Mathlib.GraphTheory.PageRank` — the
second Perron–Frobenius consumer, whose entire content is that the
teleportation floor restores on **reducible** input what the raw walk
loses: a unique stationary distribution with full support. Four
sections, each reusing `IrreducibleStationary_QA`'s fixtures (the
QA-to-QA import precedent of `KernelBridge_QA`/`Tikhonov_QA`):

- **Section A** (structural, on the reducible two-edge fixture `A4` at
  `α = 1/2`): entry pins, the teleportation floor at a zero-support
  pair by theorem *and* raw route, row sums by both routes, the
  row-stochasticity bridge instantiated, and irreducibility — on input
  whose *own* irreducibility provably fails (the imported reducibility
  fence).
- **Section B** (the reducible-input positive witness): the PageRank
  distribution of `A4` at `α = 1/2` is the uniform vector (forced by
  the fixture's vertex transitivity), verified **completely raw**
  against pinned entries; the `∃!` join identifies *every* stationary
  distribution with the hand value — on the very fixture where the
  raw walk has two (the imported `pi4a`/`pi4b`).
- **Section C** (the asymmetric fixture): PageRank of the directed
  star `A3` at `α = 1/2` is `(4/9, 5/18, 5/18)`, verified raw —
  provably *distinct* from the raw stationary `(1/2, 1/4, 1/4)`,
  teleportation shifting mass to the leaves being the construction's
  observable content.
- **Section D** (the endpoint fences, complementary, each isolating
  exactly one hypothesis): `α = 1` on the reducible fixture —
  teleportation removed, `googleMatrix A4 1 = walkTransitionMatrix A4`
  pinned, the `∃!` refuted through the imported witnesses with degrees
  and row sums intact (exactly `hα2`); `α = -1` on `K₂` — the mixture
  degenerates to the identity, `googleMatrix K2 (-1) = 1` pinned, the
  `∃!` refuted by two distinct stationary distributions with row
  stochasticity *still holding* (it is `α`-free — exactly `hα`).

Nothing here proves or validates the `perron_frobenius` axiom; since
2026-09-02 (`proposals/cesaro-stationary-existence.md`) the theorems
below are themselves hard crust (the stationary layer was re-proved
without axiom contact by the Cesàro/power-positivity route), so the
theorem routes check that the interfaces compose while the raw routes
check the mathematics independently of the theorems.
-/

open scoped Matrix

namespace Scaffold.QA.SpectralGraph

open SpectralGraphTheory Matrix

/-! ## Section A: the structural layer on the reducible two-edge fixture

`A4` (two disjoint `Fin 4` edges) is reducible — its support digraph
has two strongly connected components, and the imported
`A4_existsUnique_refuted_QA` exhibits two stationary distributions of
its raw walk. The Google matrix at `α = 1/2` has `(1 - α) * 4⁻¹ = 1/8`
in every entry: the floor at a zero-support pair is `1/8`, an edge
entry `1/2 + 1/8 = 5/8`. -/

/-- The Google matrix of the reducible two-edge fixture at `α = 1/2`. -/
noncomputable def A4G : Matrix (Fin 4) (Fin 4) ℝ := googleMatrix A4 (1 / 2)

theorem A4G_00 : A4G 0 0 = 1 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_00, Fintype.card_fin]; norm_num

theorem A4G_01 : A4G 0 1 = 5 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_01, Fintype.card_fin]; norm_num

theorem A4G_02 : A4G 0 2 = 1 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_02, Fintype.card_fin]; norm_num

theorem A4G_03 : A4G 0 3 = 1 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_03, Fintype.card_fin]; norm_num

theorem A4G_10 : A4G 1 0 = 5 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_10, Fintype.card_fin]; norm_num

theorem A4G_11 : A4G 1 1 = 1 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_11, Fintype.card_fin]; norm_num

theorem A4G_12 : A4G 1 2 = 1 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_12, Fintype.card_fin]; norm_num

theorem A4G_13 : A4G 1 3 = 1 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_13, Fintype.card_fin]; norm_num

theorem A4G_20 : A4G 2 0 = 1 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_20, Fintype.card_fin]; norm_num

theorem A4G_21 : A4G 2 1 = 1 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_21, Fintype.card_fin]; norm_num

theorem A4G_22 : A4G 2 2 = 1 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_22, Fintype.card_fin]; norm_num

theorem A4G_23 : A4G 2 3 = 5 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_23, Fintype.card_fin]; norm_num

theorem A4G_30 : A4G 3 0 = 1 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_30, Fintype.card_fin]; norm_num

theorem A4G_31 : A4G 3 1 = 1 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_31, Fintype.card_fin]; norm_num

theorem A4G_32 : A4G 3 2 = 5 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_32, Fintype.card_fin]; norm_num

theorem A4G_33 : A4G 3 3 = 1 / 8 := by
  simp only [A4G, googleMatrix_apply, A4P_eq, A4_33, Fintype.card_fin]; norm_num

/-- **The teleportation floor, raw route:** at the zero-support pair
`(0, 3)` — no arc, not even in the same component — the entry is
exactly the additive teleportation weight `1/8 > 0`. -/
theorem A4G_floor_raw_QA : 0 < A4G 0 3 := by rw [A4G_03]; norm_num

/-- **The teleportation floor, theorem route:** the same fact through
`googleMatrix_pos` (unconditional hard crust), the two routes agreeing
on the value. -/
theorem A4G_floor_theorem_QA : 0 < A4G 0 3 :=
  googleMatrix_pos A4 A4_nonneg_QA A4_deg_QA
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 < 1 by norm_num) 0 3

/-- **Row stochasticity, theorem route:** every row of the Google
matrix sums to one. -/
theorem A4G_row_sum_QA (i : Fin 4) : ∑ j, A4G i j = 1 :=
  googleMatrix_row_sum A4 A4_deg_QA (1 / 2) i

/-- **Row stochasticity, raw route:** the first row's sum from the
pinned entries alone (`1/8 + 5/8 + 1/8 + 1/8`). -/
theorem A4G_row_sum_raw_QA : ∑ j, A4G 0 j = 1 := by
  simp only [Fin.sum_univ_four, A4G_00, A4G_01, A4G_02, A4G_03]; norm_num

/-- **The bridge instantiated:** the Google matrix is its own walk
transition matrix (all degrees one). The composition point between the
delivered consumer layer and the regularized walk, on the fixture. -/
theorem A4G_walk_eq_QA : walkTransitionMatrix A4G = A4G :=
  walkTransitionMatrix_eq_of_row_sum_one _ A4G_row_sum_QA

/-- **Irreducibility on reducible input:** the Google matrix of the
two-component fixture is irreducible — every pair one positive arc
apart through the floor — although the fixture's own support digraph
provably is not (the imported reducibility fence). This is the
construction's content instantiated. -/
theorem A4G_irr_QA : A4G.IsIrreducible :=
  googleMatrix_isIrreducible A4 A4_nonneg_QA A4_deg_QA
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 < 1 by norm_num)

/-! ## Section B: the reducible-input positive witness

By the fixture's vertex transitivity (each edge flippable, the two
edges swappable — all automorphisms of the weighted matrix `A4G`), the
PageRank distribution is uniform. The hand value is verified raw; the
`∃!` (conditional on `perron_frobenius`) then identifies every
stationary distribution with it — on the fixture where the raw walk
has two. -/

/-- The uniform distribution on `Fin 4`. -/
noncomputable def u4 : Fin 4 → ℝ := ![1 / 4, 1 / 4, 1 / 4, 1 / 4]

theorem u4_0 : u4 0 = 1 / 4 := rfl
theorem u4_1 : u4 1 = 1 / 4 := rfl
theorem u4_2 : u4 2 = 1 / 4 := rfl
theorem u4_3 : u4 3 = 1 / 4 := rfl

theorem u4_nonneg_QA : ∀ i, 0 ≤ u4 i := by
  intro i; fin_cases i <;> simp [u4_0, u4_1, u4_2, u4_3]

theorem u4_sum_QA : ∑ i, u4 i = 1 := by
  simp only [Fin.sum_univ_four, u4_0, u4_1, u4_2, u4_3]; norm_num

theorem u4_stat_0 : (u4 ᵥ* A4G) 0 = u4 0 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_four, u4_0, u4_1,
    u4_2, u4_3, A4G_00, A4G_10, A4G_20, A4G_30]; norm_num

theorem u4_stat_1 : (u4 ᵥ* A4G) 1 = u4 1 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_four, u4_0, u4_1,
    u4_2, u4_3, A4G_01, A4G_11, A4G_21, A4G_31]; norm_num

theorem u4_stat_2 : (u4 ᵥ* A4G) 2 = u4 2 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_four, u4_0, u4_1,
    u4_2, u4_3, A4G_02, A4G_12, A4G_22, A4G_32]; norm_num

theorem u4_stat_3 : (u4 ᵥ* A4G) 3 = u4 3 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_four, u4_0, u4_1,
    u4_2, u4_3, A4G_03, A4G_13, A4G_23, A4G_33]; norm_num

/-- **The uniform vector is stationary for the Google walk, raw:**
every coordinate computed from the pinned entries alone — the column
sums of `A4G` are one by the same arithmetic that pins the row sums. -/
theorem u4_stationary_raw_QA : u4 ᵥ* A4G = u4 := by
  funext j
  fin_cases j
  · exact u4_stat_0
  · exact u4_stat_1
  · exact u4_stat_2
  · exact u4_stat_3

theorem u4_ne_zero_QA : u4 ≠ 0 := by
  intro h
  have h0 : u4 0 = 0 := congrFun h 0
  rw [u4_0] at h0; norm_num at h0

/-- The full three-part predicate, assembled for the `∃!` join. -/
theorem u4_pred_QA : (∀ i, 0 ≤ u4 i) ∧ (∑ i, u4 i = 1) ∧ u4 ᵥ* A4G = u4 :=
  ⟨u4_nonneg_QA, u4_sum_QA, u4_stationary_raw_QA⟩

/-- **The `∃!` instantiated on reducible input** (hard crust since
2026-09-02, formerly conditional on `perron_frobenius`): the
teleportation-regularized walk of the two-block fixture has exactly
one nonnegative stationary distribution — the statement the raw walk's
`A4_existsUnique_refuted_QA` refutes on the same fixture. -/
theorem A4G_existsUnique_QA :
    ∃! π : Fin 4 → ℝ, (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧ π ᵥ* A4G = π :=
  existsUnique_pageRankVec A4 A4_nonneg_QA A4_deg_QA
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 < 1 by norm_num)

/-- **The load-bearing join:** every stationary distribution of the
fixture's Google walk equals the uniform hand value — the theorem's
uniqueness clause pinning the raw-computed witness. A wrong uniqueness
clause or a misstated floor breaks this identification. -/
theorem A4G_stationary_eq_uniform_QA (π : Fin 4 → ℝ)
    (hπ : (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧ π ᵥ* A4G = π) : π = u4 := by
  obtain ⟨τ, -, huniq⟩ := A4G_existsUnique_QA
  exact (huniq π hπ).trans (huniq u4 u4_pred_QA).symm

/-- **Full support instantiated:** the PageRank distribution is
strictly positive (theorem route; the values are also pinned raw in
`u4_nonneg_QA`'s strict companions). -/
theorem A4G_full_support_QA : ∀ i, 0 < u4 i :=
  pageRankVec_pos A4 A4_nonneg_QA A4_deg_QA
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 < 1 by norm_num)
    u4_nonneg_QA u4_ne_zero_QA u4_stationary_raw_QA

/-! ## Section C: the asymmetric fixture — teleportation shifts mass

On the directed star `A3` the raw stationary distribution is
`(1/2, 1/4, 1/4)` (the imported `pi3`, pinned raw there). With
teleportation at `α = 1/2` the unique stationary vector moves to
`(4/9, 5/18, 5/18)`: the leaves gain teleportation mass, the hub
keeps its walk mass. Distinctness from the raw value is the
construction's observable content — the quantity PageRank is *for*. -/

/-- The Google matrix of the directed star at `α = 1/2`. -/
noncomputable def A3G : Matrix (Fin 3) (Fin 3) ℝ := googleMatrix A3 (1 / 2)

theorem A3G_00 : A3G 0 0 = 1 / 6 := by
  simp only [A3G, googleMatrix_apply, A3P_00, Fintype.card_fin]; norm_num

theorem A3G_01 : A3G 0 1 = 5 / 12 := by
  simp only [A3G, googleMatrix_apply, A3P_01, Fintype.card_fin]; norm_num

theorem A3G_02 : A3G 0 2 = 5 / 12 := by
  simp only [A3G, googleMatrix_apply, A3P_02, Fintype.card_fin]; norm_num

theorem A3G_10 : A3G 1 0 = 2 / 3 := by
  simp only [A3G, googleMatrix_apply, A3P_10, Fintype.card_fin]; norm_num

theorem A3G_11 : A3G 1 1 = 1 / 6 := by
  simp only [A3G, googleMatrix_apply, A3P_11, Fintype.card_fin]; norm_num

theorem A3G_12 : A3G 1 2 = 1 / 6 := by
  simp only [A3G, googleMatrix_apply, A3P_12, Fintype.card_fin]; norm_num

theorem A3G_20 : A3G 2 0 = 2 / 3 := by
  simp only [A3G, googleMatrix_apply, A3P_20, Fintype.card_fin]; norm_num

theorem A3G_21 : A3G 2 1 = 1 / 6 := by
  simp only [A3G, googleMatrix_apply, A3P_21, Fintype.card_fin]; norm_num

theorem A3G_22 : A3G 2 2 = 1 / 6 := by
  simp only [A3G, googleMatrix_apply, A3P_22, Fintype.card_fin]; norm_num

/-- The hand-computed PageRank vector of the star at `α = 1/2`:
`(4/9, 5/18, 5/18)` — the solution of `π ᵥ* G = π` with mass one. -/
noncomputable def pr3 : Fin 3 → ℝ := ![4 / 9, 5 / 18, 5 / 18]

theorem pr3_0 : pr3 0 = 4 / 9 := rfl
theorem pr3_1 : pr3 1 = 5 / 18 := rfl
theorem pr3_2 : pr3 2 = 5 / 18 := rfl

theorem pr3_nonneg_QA : ∀ i, 0 ≤ pr3 i := by
  intro i; fin_cases i <;> simp [pr3_0, pr3_1, pr3_2] <;> norm_num

theorem pr3_sum_QA : ∑ i, pr3 i = 1 := by
  simp only [Fin.sum_univ_three, pr3_0, pr3_1, pr3_2]; norm_num

theorem pr3_stat_0 : (pr3 ᵥ* A3G) 0 = pr3 0 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three, pr3_0, pr3_1,
    pr3_2, A3G_00, A3G_10, A3G_20]; norm_num

theorem pr3_stat_1 : (pr3 ᵥ* A3G) 1 = pr3 1 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three, pr3_0, pr3_1,
    pr3_2, A3G_01, A3G_11, A3G_21]; norm_num

theorem pr3_stat_2 : (pr3 ᵥ* A3G) 2 = pr3 2 := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_three, pr3_0, pr3_1,
    pr3_2, A3G_02, A3G_12, A3G_22]; norm_num

/-- **The hand value is stationary, raw:** every coordinate against the
pinned entries — `4/9·1/6 + 5/18·2/3 + 5/18·2/3 = 4/9` etc.,
independent of any theorem. -/
theorem pr3_stationary_raw_QA : pr3 ᵥ* A3G = pr3 := by
  funext j
  fin_cases j
  · exact pr3_stat_0
  · exact pr3_stat_1
  · exact pr3_stat_2

theorem pr3_ne_zero_QA : pr3 ≠ 0 := by
  intro h
  have h0 : pr3 0 = 0 := congrFun h 0
  rw [pr3_0] at h0; norm_num at h0

theorem pr3_pred_QA : (∀ i, 0 ≤ pr3 i) ∧ (∑ i, pr3 i = 1) ∧ pr3 ᵥ* A3G = pr3 :=
  ⟨pr3_nonneg_QA, pr3_sum_QA, pr3_stationary_raw_QA⟩

/-- **The `∃!` instantiated on the asymmetric fixture** (hard crust
since 2026-09-02, formerly conditional on `perron_frobenius`). -/
theorem A3G_existsUnique_QA :
    ∃! π : Fin 3 → ℝ, (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧ π ᵥ* A3G = π :=
  existsUnique_pageRankVec A3 A3_nonneg_QA A3_deg_QA
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 < 1 by norm_num)

/-- **The join:** every stationary distribution of the star's Google
walk equals the hand value `(4/9, 5/18, 5/18)`. -/
theorem A3G_eq_hand_QA (π : Fin 3 → ℝ)
    (hπ : (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧ π ᵥ* A3G = π) : π = pr3 := by
  obtain ⟨τ, -, huniq⟩ := A3G_existsUnique_QA
  exact (huniq π hπ).trans (huniq pr3 pr3_pred_QA).symm

/-- **Teleportation shifts mass:** the PageRank vector is provably
*not* the raw stationary distribution `(1/2, 1/4, 1/4)` (imported
`pi3`, pinned raw there) — at the hub coordinate `4/9 ≠ 1/2`. The two
notions of centrality the construction distinguishes, separated in
proved form. -/
theorem pr3_ne_pi3_QA : pr3 ≠ pi3 := by
  intro h
  have h0 : pr3 0 = pi3 0 := congrFun h 0
  rw [pr3_0, pi3_0] at h0; norm_num at h0

/-- **Full support instantiated on the asymmetric fixture.** -/
theorem A3G_full_support_QA : ∀ i, 0 < pr3 i :=
  pageRankVec_pos A3 A3_nonneg_QA A3_deg_QA
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 < 1 by norm_num)
    pr3_nonneg_QA pr3_ne_zero_QA pr3_stationary_raw_QA

/-! ## Section D: the endpoint fences

The damping window `[0, 1)` is load-bearing at both ends, and the two
fences are complementary: `α = 1` keeps `0 ≤ α` and violates
`α < 1`; `α = -1` keeps `α < 1` and violates `0 ≤ α`. Row
stochasticity is `α`-free (`googleMatrix_row_sum` takes no `α`
restriction) and is verified intact at both — so each refutation is
attributable to the dropped hypothesis alone. -/

/-- **At `α = 1` the teleportation is gone:** `googleMatrix A4 1`
*is* the raw walk transition matrix, pinned entrywise (`1 · P i j +
0 · n⁻¹ = P i j`). -/
theorem A4G1_eq_walk_QA : googleMatrix A4 1 = walkTransitionMatrix A4 := by
  apply Matrix.ext
  intro i j
  rw [googleMatrix_apply, one_mul, sub_self, zero_mul, add_zero]

/-- Row stochasticity survives the `α = 1` endpoint (it is affine in
`α`) — part of the fence: the failure at `α = 1` is not a
row-sum failure. -/
theorem A4G1_row_sum_QA (i : Fin 4) : ∑ j, googleMatrix A4 1 i j = 1 :=
  googleMatrix_row_sum A4 A4_deg_QA 1 i

/-- **Fence at `α = 1` (exactly `hα2` isolated):** the `∃!` conclusion
with `α < 1` dropped is false — the imported witnesses `pi4a`/`pi4b`
are two distinct stationary distributions of `googleMatrix A4 1` by
the entrywise identification above, with nonnegativity, degrees, and
row sums all verified intact. -/
theorem A4G1_not_unique_QA :
    ¬ ∃! π : Fin 4 → ℝ, (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧
      π ᵥ* googleMatrix A4 1 = π := by
  intro h
  obtain ⟨τ, -, huniq⟩ := h
  have hpa : (∀ i, 0 ≤ pi4a i) ∧ ∑ i, pi4a i = 1 ∧
      pi4a ᵥ* googleMatrix A4 1 = pi4a := by
    refine ⟨pi4a_pred_QA.1, pi4a_pred_QA.2.1, ?_⟩
    rw [A4G1_eq_walk_QA]
    exact pi4a_pred_QA.2.2
  have hpb : (∀ i, 0 ≤ pi4b i) ∧ ∑ i, pi4b i = 1 ∧
      pi4b ᵥ* googleMatrix A4 1 = pi4b := by
    refine ⟨pi4b_pred_QA.1, pi4b_pred_QA.2.1, ?_⟩
    rw [A4G1_eq_walk_QA]
    exact pi4b_pred_QA.2.2
  exact pi4a_ne_pi4b_QA ((huniq pi4a hpa).trans (huniq pi4b hpb).symm)

/-- The `K₂` edge fixture. -/
def K2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem K2_00 : K2 0 0 = 0 := rfl
theorem K2_01 : K2 0 1 = 1 := rfl
theorem K2_10 : K2 1 0 = 1 := rfl
theorem K2_11 : K2 1 1 = 0 := rfl

theorem K2_nonneg_QA : ∀ i j, 0 ≤ K2 i j := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [K2_00, K2_01, K2_10, K2_11]

theorem K2_deg_0 : deg K2 0 = 1 := by
  simp only [deg, Fin.sum_univ_two, K2_00, K2_01]; norm_num

theorem K2_deg_1 : deg K2 1 = 1 := by
  simp only [deg, Fin.sum_univ_two, K2_10, K2_11]; norm_num

theorem K2_deg (i : Fin 2) : deg K2 i = 1 := by
  fin_cases i <;> simp [K2_deg_0, K2_deg_1]

theorem K2_deg_pos_QA : ∀ i, 0 < deg K2 i := by
  intro i; rw [K2_deg i]; norm_num

theorem K2P_eq (i j : Fin 2) : walkTransitionMatrix K2 i j = K2 i j := by
  rw [walkTransitionMatrix_apply, K2_deg i, inv_one, one_mul]

/-- **At `α = -1` the mixture degenerates:** negative teleportation
weight cancels the walk — `googleMatrix K2 (-1) = 1` pinned entrywise
(`-1 · P i j + 2 · (1/2) = 1 - P i j`). Every vector is then fixed;
the walk structure is destroyed rather than regularized. -/
theorem K2Gm1_eq_one_QA : googleMatrix K2 (-1) = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [googleMatrix_apply, K2P_eq, K2_00, K2_01, K2_10, K2_11,
      Fintype.card_fin, Matrix.one_apply] <;> norm_num

/-- Row stochasticity survives the `α = -1` endpoint too — the affine
identity is indifferent to the sign of `α`. -/
theorem K2Gm1_row_sum_QA (i : Fin 2) : ∑ j, googleMatrix K2 (-1) i j = 1 :=
  googleMatrix_row_sum K2 (fun i => K2_deg_pos_QA i) (-1) i

/-- The two point masses on `Fin 2`. -/
noncomputable def e2a : Fin 2 → ℝ := ![1, 0]
noncomputable def e2b : Fin 2 → ℝ := ![0, 1]

theorem e2a_0 : e2a 0 = 1 := rfl
theorem e2a_1 : e2a 1 = 0 := rfl
theorem e2b_0 : e2b 0 = 0 := rfl
theorem e2b_1 : e2b 1 = 1 := rfl

theorem e2a_nonneg_QA : ∀ i, 0 ≤ e2a i := by
  intro i; fin_cases i <;> simp [e2a_0, e2a_1]

theorem e2b_nonneg_QA : ∀ i, 0 ≤ e2b i := by
  intro i; fin_cases i <;> simp [e2b_0, e2b_1]

theorem e2a_sum_QA : ∑ i, e2a i = 1 := by
  simp only [Fin.sum_univ_two, e2a_0, e2a_1]; norm_num

theorem e2b_sum_QA : ∑ i, e2b i = 1 := by
  simp only [Fin.sum_univ_two, e2b_0, e2b_1]; norm_num

theorem e2a_stationary_QA : e2a ᵥ* googleMatrix K2 (-1) = e2a := by
  rw [K2Gm1_eq_one_QA, Matrix.vecMul_one]

theorem e2b_stationary_QA : e2b ᵥ* googleMatrix K2 (-1) = e2b := by
  rw [K2Gm1_eq_one_QA, Matrix.vecMul_one]

theorem e2a_ne_e2b_QA : e2a ≠ e2b := by
  intro h
  have h0 : e2a 0 = e2b 0 := congrFun h 0
  rw [e2a_0, e2b_0] at h0; norm_num at h0

/-- **Fence at `α = -1` (exactly `hα` isolated):** the `∃!` conclusion
with `0 ≤ α` dropped is false — on the degenerate identity mixture both
point masses are stationary distributions, distinct, with nonnegativity,
degrees, mass, and row stochasticity all verified intact (`α < 1` holds
at `-1`). -/
theorem K2Gm1_not_unique_QA :
    ¬ ∃! π : Fin 2 → ℝ, (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧
      π ᵥ* googleMatrix K2 (-1) = π := by
  intro h
  obtain ⟨τ, -, huniq⟩ := h
  exact e2a_ne_e2b_QA
    ((huniq e2a ⟨e2a_nonneg_QA, e2a_sum_QA, e2a_stationary_QA⟩).trans
      (huniq e2b ⟨e2b_nonneg_QA, e2b_sum_QA, e2b_stationary_QA⟩).symm)

end Scaffold.QA.SpectralGraph
