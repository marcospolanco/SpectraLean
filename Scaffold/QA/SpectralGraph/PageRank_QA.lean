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


section SpectralCeilingQA

/-!
### Section Spectral: the ceiling's eigen-equation pins

The spectral ceiling's QA obligation (2026-09-06, the sharp layer's
Slice 1): the raw eigen-equation pinned at a fresh two-cycle fixture —
the `−α`-eigenpair, the ceiling ATTAINED — and the end-mix shadow at
eigenvalue `0`.
-/

/-- The two-cycle fixture: two vertices, one arc each way (every
vertex out-degree one, the walk is the swap). -/
def prCyc : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem prCyc_nonneg : ∀ i j, 0 ≤ prCyc i j := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [prCyc]

theorem prCyc_deg_pos : ∀ i, 0 < deg prCyc i := by
  intro i
  fin_cases i <;> norm_num [deg, prCyc, Fin.sum_univ_two]

/-- The alternating vector: mass zero, and a walk left-eigenpair at
eigenvalue `-1` (the swap flips it). -/
def prAlt : Fin 2 → ℝ := ![1, -1]

theorem prAlt_mass : ∑ i, prAlt i = 0 := by
  norm_num [prAlt, Fin.sum_univ_two]

theorem prAlt_shadow : prAlt ᵥ* walkTransitionMatrix prCyc = (-1 : ℝ) • prAlt := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, prCyc, prAlt,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      walkTransitionMatrix, deg, degreeMatrix, Matrix.diagonal_mul,
      Matrix.diagonal_apply, inv_mul_cancel₀]

/-- **The attainment pin**: the shadow twin maps the `-1` walk pair to
the Google left-eigenpair at `α · (-1)` — the ceiling `|c| ≤ α` is
ATTAINED at `-α` (Haveliwala–Kamvar's equality case, the periodic
chain). -/
theorem prAlt_google_eigen (α : ℝ) :
    prAlt ᵥ* googleMatrix prCyc α = (α * (-1 : ℝ)) • prAlt :=
  googleMatrix_vecMul_of_shadow prCyc α prAlt prAlt_mass prAlt_shadow

/-- The instantiated eigen-equation at `α = 4/5`, raw. -/
theorem prAlt_google_eigen_raw :
    prAlt ᵥ* googleMatrix prCyc (4 / 5 : ℝ) = (-4 / 5 : ℝ) • prAlt := by
  rw [prAlt_google_eigen]
  norm_num

/-- **The ceiling instance**: the attained eigenvalue `-4/5` obeys
`|-4/5| ≤ 4/5` — the ceiling theorem instantiated at the fixture
(load-bearing: a mis-signed teleport weight in `googleMatrix` would
break the mass collapse and this instance). -/
theorem prAlt_ceiling_QA :
    |(-4 / 5 : ℝ)| ≤ 4 / 5 :=
  googleMatrix_abs_eigen_le prCyc prCyc_nonneg prCyc_deg_pos
    (by norm_num : (0 : ℝ) < 4 / 5) prAlt (by
      intro h
      have := congrFun h 0
      norm_num [prAlt] at this)
    prAlt_google_eigen_raw (by norm_num)

/-- **The end-mix shadow**: at the complete graph `K₂` the walk
matrix's action on the alternating vector is zero — the shadow
eigenvalue is `0`, the strict side of the ceiling (`|λ₂| < α` off the
periodic chains; the twin maps this pair to a Google eigenpair at
`α · 0 = 0`). -/
theorem prK2_shadow_zero :
    prAlt ᵥ* walkTransitionMatrix (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)
      = (0 : ℝ) • prAlt := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, prAlt,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      walkTransitionMatrix, deg, degreeMatrix, Matrix.diagonal_mul,
      Matrix.diagonal_apply, inv_mul_cancel₀]


/-- **The `-α` eigenpair as a genuine eigenvalue** — the ceiling's
attainment through the eigen-API bridge: the delivered raw
eigen-equation lifts to `HasEigenvector`, hence `HasEigenvalue`, and
the eigen-level ceiling instantiates to `|-4/5| ≤ 4/5`. -/
theorem prAlt_hasEigenvector_QA :
    Module.End.HasEigenvector (googleMatrix prCyc (4 / 5 : ℝ)).vecMulLinear
      (-4 / 5 : ℝ) prAlt := by
  have hEq : prAlt ᵥ* googleMatrix prCyc (4 / 5 : ℝ) = (-4 / 5 : ℝ) • prAlt :=
    prAlt_google_eigen_raw
  have hne : prAlt ≠ 0 := by
    intro h
    have := congrFun h 0
    norm_num [prAlt] at this
  exact Module.End.hasEigenvector_iff.2 ⟨by
    show prAlt ∈ Module.End.eigenspace (googleMatrix prCyc (4 / 5 : ℝ)).vecMulLinear (-4 / 5 : ℝ)
    rw [Module.End.mem_eigenspace_iff, Matrix.vecMulLinear_apply]
    exact hEq, hne⟩

theorem prAlt_hasEigenvalue_QA :
    Module.End.HasEigenvalue (googleMatrix prCyc (4 / 5 : ℝ)).vecMulLinear
      (-4 / 5 : ℝ) :=
  Module.End.hasEigenvalue_of_hasEigenvector prAlt_hasEigenvector_QA

theorem prAlt_eigen_ceiling_QA :
    |(-4 / 5 : ℝ)| ≤ 4 / 5 :=
  googleMatrix_hasEigenvector_abs_le prCyc prCyc_nonneg prCyc_deg_pos
    (by norm_num : (0 : ℝ) < 4 / 5) prAlt_hasEigenvector_QA (by norm_num)

/-- **The eigen-level shadow at the fixture**: the `-α`-eigenvector of
the Google matrix is the `-1`-eigenvector of the walk matrix. -/
theorem prAlt_eigen_shadow_QA :
    Module.End.HasEigenvector (walkTransitionMatrix prCyc).vecMulLinear
      (-1 : ℝ) prAlt := by
  have h := googleMatrix_hasEigenvector_shadow prCyc prCyc_deg_pos
    (by norm_num : (4 / 5 : ℝ) ≠ 0) prAlt_hasEigenvector_QA (by norm_num)
  convert h using 1
  show (-1 : ℝ) = -4 / 5 / (4 / 5)
  have hrw : (-4 : ℝ) / 5 / (4 / 5) = (-4 : ℝ) / 5 * (5 / 4) := by
    rw [div_div_eq_mul_div]
    ring
  rw [hrw]
  norm_num

end SpectralCeilingQA

section StrictnessQA

/-!
### Section Strictness: the strict half's pins and the necessity fence

The strictness layer's QA obligation (2026-09-06, the sharp layer's
Slice 5): the eigen-equation pinned at a fresh PRIMITIVE two-vertex
fixture — a self-loop plus an arc, `P²` strictly positive — where the
off-one eigenvalue `-α/2` is STRICTLY inside the α-disk; and the
primitivity-necessity fence at the periodic two-cycle, where Slice 1
pinned the ceiling ATTAINED and where primitivity provably fails.
-/

/-- The primitive two-vertex fixture: a self-loop at vertex 0 plus one
arc each way — the walk is aperiodic and its square is strictly
positive (`P = [[1/2,1/2],[1,0]]`, `P² = [[3/4,1/4],[1/2,1/2]]`). -/
def prPrim : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 0]

theorem prPrim_nonneg : ∀ i j, 0 ≤ prPrim i j := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [prPrim]

theorem prPrim_deg_pos : ∀ i, 0 < deg prPrim i := by
  intro i
  fin_cases i <;> norm_num [deg, prPrim, Fin.sum_univ_two]

theorem prPrim_P_00 : walkTransitionMatrix prPrim 0 0 = 1 / 2 := by
  norm_num [walkTransitionMatrix, deg, prPrim, Fin.sum_univ_two,
    degreeMatrix, Matrix.diagonal_apply, Matrix.diagonal_mul, mul_inv_cancel₀]

theorem prPrim_P_01 : walkTransitionMatrix prPrim 0 1 = 1 / 2 := by
  norm_num [walkTransitionMatrix, deg, prPrim, Fin.sum_univ_two,
    degreeMatrix, Matrix.diagonal_apply, Matrix.diagonal_mul, mul_inv_cancel₀]

theorem prPrim_P_10 : walkTransitionMatrix prPrim 1 0 = 1 := by
  norm_num [walkTransitionMatrix, deg, prPrim, Fin.sum_univ_two,
    degreeMatrix, Matrix.diagonal_apply, Matrix.diagonal_mul, mul_inv_cancel₀]

theorem prPrim_P_11 : walkTransitionMatrix prPrim 1 1 = 0 := by
  norm_num [walkTransitionMatrix, deg, prPrim, Fin.sum_univ_two,
    degreeMatrix, Matrix.diagonal_apply, Matrix.diagonal_mul, mul_inv_cancel₀]

/-- The primitivity witness: `P²` is strictly positive, entrywise —
`(3/4, 1/4, 1/2, 1/2)`. -/
theorem prPrim_primitive : (walkTransitionMatrix prPrim).IsPrimitive := by
  refine ⟨2, by norm_num, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two, prPrim_P_00,
      prPrim_P_01, prPrim_P_10, prPrim_P_11]

theorem prAlt_ne_zero : prAlt ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [prAlt, Matrix.cons_val_zero] at this

/-- The alternating vector is the walk's `-1/2` left-eigenvector at the
primitive fixture (mass zero — the shadow of the eigen-equation). -/
theorem prPrim_alt_shadow :
    prAlt ᵥ* walkTransitionMatrix prPrim = (-1 / 2 : ℝ) • prAlt := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, prAlt,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      prPrim_P_00, prPrim_P_01, prPrim_P_10, prPrim_P_11]

/-- **The strictness instance**: the eigenvalue `-α/2` is STRICTLY
inside the α-disk at the primitive fixture (`α/2 < α` at every
`0 < α`) — the ceiling's equality case excluded by aperiodicity. -/
theorem prPrim_strict_QA :
    |(4 / 5 : ℝ) * (-1 / 2 : ℝ)| < 4 / 5 := by
  have heigen : prAlt ᵥ* googleMatrix prPrim (4 / 5 : ℝ)
      = ((4 / 5 : ℝ) * (-1 / 2 : ℝ)) • prAlt :=
    googleMatrix_vecMul_of_shadow prPrim (4 / 5) prAlt prAlt_mass prPrim_alt_shadow
  have := googleMatrix_abs_eigen_lt_of_primitive prPrim prPrim_nonneg
    prPrim_deg_pos (by norm_num : (0:ℝ) < 4 / 5) prPrim_primitive prAlt
    prAlt_ne_zero heigen (by norm_num)
  norm_num at this ⊢
  linarith

/-- **The eigen-level strictness pin**: the `-α/2` pair lifted to a
genuine `HasEigenvalue` through the Slice-4 bridge, with the
eigen-level strictness theorem instantiated. -/
theorem prPrim_eigen_strict_QA :
    |(4 / 5 : ℝ) * (-1 / 2 : ℝ)| < 4 / 5 := by
  have hwalk : Module.End.HasEigenvector (walkTransitionMatrix prPrim).vecMulLinear
      (-1 / 2 : ℝ) prAlt :=
    Module.End.hasEigenvector_iff.2
      ⟨by simpa [Matrix.vecMulLinear_apply] using prPrim_alt_shadow, prAlt_ne_zero⟩
  have hv : Module.End.HasEigenvector (googleMatrix prPrim (4 / 5 : ℝ)).vecMulLinear
      ((4 / 5 : ℝ) * (-1 / 2 : ℝ)) prAlt :=
    googleMatrix_hasEigenvector_of_shadow prPrim (4 / 5) prAlt_mass
      prAlt_ne_zero hwalk
  have := googleMatrix_hasEigenvalue_abs_lt_of_primitive prPrim prPrim_nonneg
    prPrim_deg_pos (by norm_num : (0:ℝ) < 4 / 5) prPrim_primitive
    (Module.End.hasEigenvalue_of_hasEigenvector hv) (by norm_num)
  norm_num at this ⊢
  linarith

/-- **The necessity fence**: the two-cycle — where the ceiling is
ATTAINED at `|−α| = α` — is NOT primitive; the walk's powers alternate
between the identity and the swap, so primitivity (aperiodicity) is
exactly what the strictness theorem needs. -/
theorem prCycP_eq : walkTransitionMatrix prCyc = prCyc := by
  have hrow : ∀ i : Fin 2, ∑ j, prCyc i j = 1 := by
    intro i
    fin_cases i <;> norm_num [prCyc, Fin.sum_univ_two]
  exact walkTransitionMatrix_eq_of_row_sum_one prCyc hrow

theorem prCyc_pow_two_eq_one :
    (walkTransitionMatrix prCyc) ^ 2 = 1 := by
  have hpp : prCyc * prCyc = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, prCyc,
        Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
  rw [pow_two, prCycP_eq]
  exact hpp

theorem prCyc_pow_add_two (k : ℕ) :
    (walkTransitionMatrix prCyc) ^ (k + 2) = (walkTransitionMatrix prCyc) ^ k := by
  rw [pow_add, prCyc_pow_two_eq_one, mul_one]

theorem prCyc_not_primitive : ¬ (walkTransitionMatrix prCyc).IsPrimitive := by
  rintro ⟨k, -, hk⟩
  have h2 : (walkTransitionMatrix prCyc) ^ 2 = 1 := prCyc_pow_two_eq_one
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have h2m : (walkTransitionMatrix prCyc) ^ (m + m) = 1 := by
      rw [show m + m = 2 * m by ring, pow_mul, h2, one_pow]
    have h011 := hk 0 1
    rw [h2m] at h011
    have hone : ((1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 = 0 := by
      simp [Matrix.one_apply]
    rw [hone] at h011
    exact absurd h011 (lt_irrefl 0)
  · subst hm
    have h2m : (walkTransitionMatrix prCyc) ^ (2 * m) = 1 := by
      rw [pow_mul, h2, one_pow]
    have hkm : (walkTransitionMatrix prCyc) ^ (2 * m + 1)
        = walkTransitionMatrix prCyc := by
      rw [pow_add, h2m, one_mul, pow_one]
    have h000 := hk 0 0
    rw [hkm, prCycP_eq] at h000
    have hz : prCyc 0 0 = 0 := rfl
    rw [hz] at h000
    exact absurd h000 (lt_irrefl 0)

end StrictnessQA

section RightEigenQA

/-!
### Section RightEigen: the right-eigenvector forms' pins and boundary witnesses

The right-eigenvector delivery's QA obligation (2026-09-06,
`proposals/right-eigenvector-sharp-layer.md`): the right `-α` pair
ATTAINED at the periodic two-cycle, the right `-α/2` pair with
strictness instantiated at the primitive fixture, the general
left/right bridge pinned at the walk matrix — and the two boundary
witnesses recording WHY this delivery needed a new route: the right
eigenvector's NONZERO mass (the left mass lemma cannot transfer) and
the no-right-shadow witness (the left shadow lemma is genuinely false
at the right convention).
-/

/-- The primitive fixture's Google matrix pinned in closed form:
`G(4/5) = [[1/2,1/2],[9/10,1/10]]`. -/
theorem prPrimG_eq :
    googleMatrix prPrim (4 / 5 : ℝ) = !![1/2, 1/2; 9/10, 1/10] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [googleMatrix_apply, Fintype.card_fin, prPrim_P_00,
      prPrim_P_01, prPrim_P_10, prPrim_P_11]

/-- The primitive fixture's right `-α/2` eigenvector: `(5,−9)` pairs
at `-2/5`. -/
def prPrimRV : Fin 2 → ℝ := ![5, -9]

theorem prPrimRV_ne_zero : prPrimRV ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [prPrimRV, Matrix.cons_val_zero] at this

/-- The raw right eigen-equation at the primitive fixture. -/
theorem prPrimRV_right_eigen :
    googleMatrix prPrim (4 / 5 : ℝ) *ᵥ prPrimRV = (-2 / 5 : ℝ) • prPrimRV := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, prPrimRV,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      prPrimG_eq]

/-- **The right-convention strictness pin**: `|−2/5| < 4/5` at the
right eigenvector of the primitive fixture, through the raw right
strictness theorem (the bridge + Slice 5 underneath). -/
theorem prPrim_right_strict_QA :
    |(-2 / 5 : ℝ)| < 4 / 5 :=
  googleMatrix_abs_mulVec_eigen_lt_of_primitive prPrim prPrim_nonneg
    prPrim_deg_pos (by norm_num : (0 : ℝ) < 4 / 5) prPrim_primitive prPrimRV
    prPrimRV_ne_zero prPrimRV_right_eigen (by norm_num)

/-- **The nonzero-mass boundary witness**: the right eigenvector has
mass `-4 ≠ 0` — the left route's mass lemma cannot transfer to the
right convention (this is why the delivery needed the determinant
bridge). -/
theorem prPrimRV_mass_ne : ∑ i, prPrimRV i = -4 := by
  norm_num [prPrimRV, Fin.sum_univ_two]

/-- **The no-right-shadow witness**: `(5,−9)` is NOT a right
eigenvector of the walk at `-1/2` — teleportation shifts
right-eigenvectors off the shadow, unlike the left case where the
shadow lemma is exact. -/
theorem prPrim_no_right_shadow_QA :
    ¬ (walkTransitionMatrix prPrim *ᵥ prPrimRV = (-1 / 2 : ℝ) • prPrimRV) := by
  intro h
  have h0 := congrFun h 0
  simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, Pi.smul_apply,
    smul_eq_mul, prPrimRV, Matrix.cons_val_zero, Matrix.head_cons,
    prPrim_P_00, prPrim_P_01] at h0
  norm_num at h0

/-- The two-cycle's Google matrix pinned in closed form:
`G(4/5) = [[1/10,9/10],[9/10,1/10]]`. -/
theorem prCycG_eq :
    googleMatrix prCyc (4 / 5 : ℝ) = !![1/10, 9/10; 9/10, 1/10] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [googleMatrix, walkTransitionMatrix, deg, prCyc, Fin.sum_univ_two,
      degreeMatrix, Matrix.diagonal_apply, Matrix.diagonal_mul, inv_mul_cancel₀,
      Fintype.card_fin]

/-- **The right `-α` pair attained** at the periodic two-cycle: the
alternating vector pairs at `-4/5` from the right — the ceiling
ATTAINED at the right convention, exactly where the left QA pinned
it. -/
theorem prAlt_right_eigen :
    googleMatrix prCyc (4 / 5 : ℝ) *ᵥ prAlt = (-4 / 5 : ℝ) • prAlt := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, prAlt,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      prCycG_eq]

theorem prAlt_right_ceiling_QA :
    |(-4 / 5 : ℝ)| ≤ 4 / 5 :=
  googleMatrix_abs_mulVec_eigen_le prCyc prCyc_nonneg prCyc_deg_pos
    (by norm_num : (0 : ℝ) < 4 / 5) prAlt prAlt_ne_zero prAlt_right_eigen
    (by norm_num)

/-- The walk's raw right `-1/2` pair at the primitive fixture:
`(1,−2)`. -/
theorem prPrim_walk_right :
    walkTransitionMatrix prPrim *ᵥ ![1, -2] = (-1 / 2 : ℝ) • ![1, -2] := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      prPrim_P_00, prPrim_P_01, prPrim_P_10, prPrim_P_11]

/-- **The bridge pin**: from the raw RIGHT pair at the walk matrix,
the general left/right bridge delivers the LEFT `HasEigenvalue` —
load-bearing on `hasEigenvalue_mulVecLin_iff_vecMulLinear` at a
non-Google matrix. -/
theorem prPrim_bridge_QA :
    Module.End.HasEigenvalue (walkTransitionMatrix prPrim).vecMulLinear
      (-1 / 2 : ℝ) :=
  (hasEigenvalue_mulVecLin_iff_vecMulLinear _ _).1
    (Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.2 ⟨by
        show (![1, -2] : Fin 2 → ℝ) ∈ Module.End.eigenspace
          (walkTransitionMatrix prPrim).mulVecLin (-1 / 2 : ℝ)
        rw [Module.End.mem_eigenspace_iff]
        exact prPrim_walk_right, by
        intro h
        have := congrFun h 0
        norm_num at this⟩))

end RightEigenQA

section DoublyStochasticQA

/-!
### Section DoublyStochastic: the doubly-stochastic right forms' pins

The follow-on's QA obligation (2026-09-06, the right-eigenvector
proposal's priced item): the right shadow and twin round-tripped at
the two-cycle (doubly stochastic — the swap), the end-mix `0`-pair,
and the NON-SYMMETRIC doubly-stochastic `Fin 3` fixture proving the
hypothesis class is genuinely larger than the symmetric cone (on
`Fin 2`, doubly stochastic forces symmetry — the `Fin 3` cyclic
chain is the smallest witness otherwise).
-/

/-- The two-cycle's walk is column-stochastic (the swap is doubly
stochastic). -/
theorem prCyc_col_stoch : ∀ j, ∑ i, walkTransitionMatrix prCyc i j = 1 := by
  intro j
  rw [prCycP_eq]
  fin_cases j <;> norm_num [prCyc, Fin.sum_univ_two]

/-- **The right shadow instantiated at the two-cycle**: from the
pinned right `-α` pair, the shadow theorem DELIVERS the walk's `-1`
right pair. -/
theorem prAlt_right_shadow_QA :
    walkTransitionMatrix prCyc *ᵥ prAlt = (-1 : ℝ) • prAlt := by
  have h := googleMatrix_mulVec_shadow prCyc prCyc_col_stoch
    (by norm_num : (4 / 5 : ℝ) ≠ 0) prAlt prAlt_right_eigen
    (by norm_num : (-4 / 5 : ℝ) ≠ 1)
  rw [show (-4 / 5 : ℝ) / (4 / 5) = -1 by norm_num] at h
  exact h

/-- **The right twin round-trips**: the shadow-delivered walk pair
maps back through the twin to the pinned Google pair. -/
theorem prAlt_right_twin_QA :
    googleMatrix prCyc (4 / 5 : ℝ) *ᵥ prAlt = (-4 / 5 : ℝ) • prAlt := by
  have h := googleMatrix_mulVec_of_shadow prCyc prCyc_col_stoch (4 / 5) prAlt
    prAlt_mass prAlt_right_shadow_QA
  rw [show (4 / 5 : ℝ) * (-1 : ℝ) = -4 / 5 by norm_num] at h
  exact h

/-- The end-mix fixture: the complete graph's walk. -/
def prEnd2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]

theorem prEnd2_col_stoch :
    ∀ j, ∑ i, walkTransitionMatrix prEnd2 i j = 1 := by
  intro j
  fin_cases j <;>
    norm_num [walkTransitionMatrix, deg, prEnd2, Fin.sum_univ_two,
      degreeMatrix, Matrix.diagonal_apply, Matrix.diagonal_mul,
      inv_mul_cancel₀]

/-- The end-mix right `0`-pair, raw. -/
theorem prEnd2_right_eigen :
    googleMatrix prEnd2 (4 / 5 : ℝ) *ᵥ prAlt = (0 : ℝ) • prAlt := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, prAlt,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      googleMatrix, walkTransitionMatrix, deg, prEnd2,
      degreeMatrix, Matrix.diagonal_apply, Matrix.diagonal_mul,
      inv_mul_cancel₀, Fintype.card_fin]

/-- **The end-mix right shadow at eigenvalue `0`**: the theorem
delivers the walk's `0` pair (the strict side of the ceiling, now at
the right convention too). -/
theorem prEnd2_right_shadow_QA :
    walkTransitionMatrix prEnd2 *ᵥ prAlt = (0 : ℝ) • prAlt := by
  have h := googleMatrix_mulVec_shadow prEnd2 prEnd2_col_stoch
    (by norm_num : (4 / 5 : ℝ) ≠ 0) prAlt prEnd2_right_eigen
    (by norm_num : (0 : ℝ) ≠ 1)
  simpa using h

/-- A NON-SYMMETRIC doubly-stochastic chain on `Fin 3` (the cyclic
chain `(1/2,1/2,0)` shifted): doubly stochasticity does NOT imply
symmetry — on `Fin 2` it does, so this is the smallest witness that
the follow-on's hypothesis class is genuinely larger than the
symmetric cone. -/
noncomputable def prDbl3 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/2, 1/2, 0; 0, 1/2, 1/2; 1/2, 0, 1/2]

theorem prDbl3_not_symm : ¬ prDbl3.IsSymm := by
  intro h
  have h2 : prDbl3 0 1 = prDbl3ᵀ 0 1 := by rw [h]
  rw [Matrix.transpose_apply] at h2
  norm_num [prDbl3, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.vecHead,
    Matrix.vecTail] at h2

theorem prDbl3_row_stoch : ∀ i, ∑ j, prDbl3 i j = 1 := by
  intro i
  fin_cases i <;>
    norm_num [prDbl3, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one, Matrix.cons_val_succ,
      Matrix.vecHead, Matrix.vecTail]

theorem prDbl3P_eq : walkTransitionMatrix prDbl3 = prDbl3 :=
  walkTransitionMatrix_eq_of_row_sum_one prDbl3 prDbl3_row_stoch

/-- The non-symmetric fixture is genuinely doubly stochastic at the
walk level — the follow-on's hypotheses hold off the symmetric cone. -/
theorem prDbl3_col_stoch :
    ∀ j, ∑ i, walkTransitionMatrix prDbl3 i j = 1 := by
  intro j
  rw [prDbl3P_eq]
  fin_cases j <;>
    norm_num [prDbl3, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one, Matrix.cons_val_succ,
      Matrix.vecHead, Matrix.vecTail]

end DoublyStochasticQA

section CharacterizationQA

/-!
### Section Characterization: the `|λ₂| = α` iff pinned at both
fixtures

The characterization's QA obligation (2026-09-06, the sharp layer's
item 3 composed): both directions instantiated at the two-cycle (the
periodic chain, where equality lives), the right-convention twin
instantiated, and the negative witness at the primitive fixture —
strictness's contrapositive content at the eigenpair level (no
mass-zero peripheral walk pair exists there).
-/

/-- **The ⇐ direction pinned at the two-cycle**: the pinned
peripheral mass-zero walk pair (the `-1` shadow pair) delivers a
Google pair at `α · (-1)` with the ceiling ATTAINED. -/
theorem prCyc_iff_attain_QA :
    ∃ μ : Fin 2 → ℝ, μ ≠ 0 ∧ μ ᵥ* googleMatrix prCyc (4 / 5 : ℝ)
      = (-4 / 5 : ℝ) • μ ∧ |(-4 / 5 : ℝ)| = 4 / 5 :=
  (googleMatrix_abs_eigen_eq_alpha_iff prCyc prCyc_deg_pos
    (by norm_num : (0 : ℝ) < 4 / 5) (by norm_num : (-4 / 5 : ℝ) ≠ 1)).mpr
    ⟨prAlt, prAlt_ne_zero, prAlt_mass, by
      rw [prAlt_shadow]
      congr 1
      norm_num, by norm_num⟩

/-- **The ⇒ direction pinned at the two-cycle**: the pinned attained
Google pair (raw) delivers a mass-zero peripheral walk pair at the
shadow eigenvalue `-4/5 / (4/5) = -1`. -/
theorem prCyc_iff_extract_QA :
    ∃ ν : Fin 2 → ℝ, ν ≠ 0 ∧ ∑ i, ν i = 0 ∧
      ν ᵥ* walkTransitionMatrix prCyc = ((-4 / 5 : ℝ) / (4 / 5)) • ν ∧
      |((-4 / 5 : ℝ) / (4 / 5))| = 1 :=
  (googleMatrix_abs_eigen_eq_alpha_iff prCyc prCyc_deg_pos
    (by norm_num : (0 : ℝ) < 4 / 5) (by norm_num : (-4 / 5 : ℝ) ≠ 1)).mp
    ⟨prAlt, prAlt_ne_zero, prAlt_google_eigen_raw, by norm_num⟩

/-- **The negative witness at the primitive fixture**: no mass-zero
peripheral walk pair exists there (the mass-zero line is spanned by
the alternating vector, on which the walk acts at `-1/2`) — the iff's
contrapositive content, matching Slice 5's strictness. -/
theorem prPrim_no_peripheral_QA :
    ¬ (∃ ν : Fin 2 → ℝ, ν ≠ 0 ∧ ∑ i, ν i = 0 ∧
      ∃ c' : ℝ, ν ᵥ* walkTransitionMatrix prPrim = c' • ν ∧ |c'| = 1) := by
  rintro ⟨ν, hν0, hmass, c', hν, hc'⟩
  have hline : ν 1 = -ν 0 := by
    have h := hmass
    simp only [Fin.sum_univ_two] at h
    linarith
  have h0 : ν 0 ≠ 0 := by
    intro h0
    apply hν0
    funext i
    fin_cases i <;> simp [h0, hline]
  have heq0 := congrFun hν 0
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two,
    Pi.smul_apply, smul_eq_mul, prPrim_P_00, prPrim_P_10] at heq0
  rw [hline] at heq0
  have hz : ν 0 * (c' + 1 / 2) = 0 := by
    nlinarith [heq0]
  rcases mul_eq_zero.1 hz with h | h
  · exact h0 h
  · have hc'eq : c' = -1 / 2 := by linarith
    rw [hc'eq, abs_of_neg (by norm_num : (-1 / 2 : ℝ) < 0)] at hc'
    norm_num at hc'

/-- **The right-convention iff pinned at the two-cycle** (doubly
stochastic): the pinned right Google pair delivers a mass-zero
peripheral RIGHT walk pair. -/
theorem prCyc_iff_right_QA :
    ∃ w : Fin 2 → ℝ, w ≠ 0 ∧ ∑ i, w i = 0 ∧
      walkTransitionMatrix prCyc *ᵥ w = ((-4 / 5 : ℝ) / (4 / 5)) • w ∧
      |((-4 / 5 : ℝ) / (4 / 5))| = 1 :=
  (googleMatrix_mulVec_abs_eigen_eq_alpha_iff prCyc prCyc_col_stoch
    (by norm_num : (0 : ℝ) < 4 / 5) (by norm_num : (-4 / 5 : ℝ) ≠ 1)).mp
    ⟨prAlt, prAlt_ne_zero, prAlt_right_eigen, by norm_num⟩

end CharacterizationQA

section SharpFences

/-!
### Section SharpFences: the sharp-layer family's adversarial fence audit

The audit's QA obligation (2026-09-06,
`proposals/adversarial-fences-sharp-layer-family.md`, found by this
run's theorem-level QA-mention survey): hypothesis-form fences for
the family's unfenced load-bearing clauses — the mass lemma's and
shadow's `hc` (the stationary `1`-pair has mass `2`), the shadow's
`hα` (the junk `0/0` shadow at the genuine `0`-pair), the ceiling's
`hα` (negative `α` at the primitive fixture, eigenvalue `1/2`),
`hnn` (the signed adjacency, eigenvalue `-12/5`), and `hμ0` (the
zero-vector junk corner); the twin's `hmass`; the iff's `hc1` (at
`c = α = 1` the left side holds while the right side's mass-zero
`1`-pair of the swap does not exist); the sign-rigidity engine's
`hrow` (a non-stochastic `M` with `M² = 1 > 0` and a mixed-sign
peripheral pair) and `hk` (the swap: mixed-sign peripheral pair, no
positive power — `prCyc_not_primitive`); and the doubly-stochastic
trio's `hcol` (the delivered `prPrim` boundary witness in fence
form). Census finding caught by the spike: at the two-cycle
`G(-1) = I` — its off-one spectrum is EMPTY, so the negative-`α`
fence lives at the primitive fixture, where the shadow eigenvalue is
genuinely off-one.
-/

/-- The constant vector: a genuine left-`1`-eigenpair of the two-cycle
Google matrix (doubly stochastic there) with mass `2 ≠ 0`. -/
def sfaOnes : Fin 2 → ℝ := ![1, 1]

theorem sfaOnes_ne_zero : sfaOnes ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [sfaOnes, Matrix.cons_val_zero] at this

theorem sfaOnes_pair :
    sfaOnes ᵥ* googleMatrix prCyc (4 / 5 : ℝ) = (1 : ℝ) • sfaOnes := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, sfaOnes,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one, prCycG_eq]

/-- **The mass lemma's `hc` fence**: the `1`-pair is genuine while the
mass is `2 ≠ 0`. -/
theorem sfa_mass_hc_fence : ¬ (∑ i, sfaOnes i = 0) := by
  norm_num [sfaOnes, Fin.sum_univ_two]

/-- **The shadow's `hc` fence**: at `c = 1` the shadow conclusion reads
`(1,1) ᵥ* P = (5/4) • (1,1)`, but the swap fixes `(1,1)`. -/
theorem sfa_shadow_hc_fence :
    ¬ (sfaOnes ᵥ* walkTransitionMatrix prCyc = (5 / 4 : ℝ) • sfaOnes) := by
  intro h
  have h0 := congrFun h 0
  rw [prCycP_eq] at h0
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two,
    Pi.smul_apply, smul_eq_mul, sfaOnes, Matrix.cons_val_zero,
    Matrix.head_cons, Matrix.cons_val_one, prCyc] at h0
  norm_num at h0

/-- **The shadow's `hα` fence**: at `α = 0` the shadow eigenvalue is
junk (`0/0 = 0`), and the genuine `0`-pair's walk action is `-1`, not
`0`. -/
theorem sfa_shadow_hα_fence :
    ¬ (prAlt ᵥ* walkTransitionMatrix prCyc = (0 / 0 : ℝ) • prAlt) := by
  intro h
  rw [prAlt_shadow] at h
  have h0 := congrFun h 0
  simp only [Pi.smul_apply, smul_eq_mul, prAlt, Matrix.cons_val_zero] at h0
  norm_num at h0

/-- The `α = 0` Google matrix at the two-cycle is `J/2`; the
alternating vector pairs at `0`. -/
theorem sfa_alt_zero_pair :
    prAlt ᵥ* googleMatrix prCyc (0 : ℝ) = (0 : ℝ) • prAlt := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, prAlt,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      Pi.smul_apply, smul_eq_mul,
      googleMatrix, walkTransitionMatrix, deg, prCyc,
      degreeMatrix, Matrix.diagonal_apply, Matrix.diagonal_mul,
      inv_mul_cancel₀, Fintype.card_fin]

/-- **The ceiling's `hα` fence (negative α)**: at the primitive fixture
and `α = -1` the Google matrix is `[[1/2,1/2],[0,1]]`, the
alternating vector pairs at `1/2 ≠ 1`, and `|1/2| ≤ -1` fails.
(Census finding, caught by the spike: at the two-cycle `G(-1)` is the
IDENTITY — its off-one spectrum is empty, so `α < 0` is fenceable only
where the walk has a genuinely off-one shadow eigenvalue.) -/
theorem sfa_ceiling_neg_alpha_pair :
    prAlt ᵥ* googleMatrix prPrim (-1 : ℝ) = (1 / 2 : ℝ) • prAlt := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, prAlt,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      Pi.smul_apply, smul_eq_mul,
      googleMatrix, walkTransitionMatrix, deg, prPrim,
      degreeMatrix, Matrix.diagonal_apply, Matrix.diagonal_mul,
      inv_mul_cancel₀, Fintype.card_fin]

theorem sfa_ceiling_neg_alpha_fence : ¬ (|(1 / 2 : ℝ)| ≤ (-1 : ℝ)) := by
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  norm_num

/-- The signed adjacency fixture: every degree `1` (positive), entries
signed — the ceiling's `hnn` breaker. -/
def sfaSigned : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 2; 2, -1]

theorem sfaSigned_deg_pos : ∀ i, 0 < deg sfaSigned i := by
  intro i
  fin_cases i <;> norm_num [deg, sfaSigned, Fin.sum_univ_two]

theorem sfa_alt_signed_pair :
    prAlt ᵥ* googleMatrix sfaSigned (4 / 5 : ℝ) = (-12 / 5 : ℝ) • prAlt := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, prAlt,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      Pi.smul_apply, smul_eq_mul,
      googleMatrix, walkTransitionMatrix, deg, sfaSigned,
      degreeMatrix, Matrix.diagonal_apply, Matrix.diagonal_mul,
      inv_mul_cancel₀, Fintype.card_fin]

/-- **The ceiling's `hnn` fence**: at the signed adjacency (degrees
genuinely positive), the off-one eigenvalue is `-12/5` and
`|-12/5| ≤ 4/5` fails. -/
theorem sfa_ceiling_hnn_fence : ¬ (|(-12 / 5 : ℝ)| ≤ 4 / 5) := by
  rw [abs_of_neg (by norm_num : (-12 / 5 : ℝ) < 0)]
  norm_num

/-- **The ceiling's `hμ0` fence (junk corner)**: the zero vector
satisfies every eigen-equation form; at `c = 5` the conclusion
`|5| ≤ 4/5` fails. -/
theorem sfa_ceiling_zero_mu_pair :
    (0 : Fin 2 → ℝ) ᵥ* googleMatrix prCyc (4 / 5 : ℝ) = (5 : ℝ) • 0 := by
  funext j
  simp [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two]

theorem sfa_ceiling_hμ0_fence : ¬ (|(5 : ℝ)| ≤ 4 / 5) := by
  norm_num

/-- The constant vector's walk pair at the swap (genuine for the
twin's dropped-mass fence). -/
theorem sfaOnes_walk_pair :
    sfaOnes ᵥ* walkTransitionMatrix prCyc = (1 : ℝ) • sfaOnes := by
  rw [prCycP_eq]
  funext j
  fin_cases j <;>
    norm_num [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, sfaOnes,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one, prCyc]

/-- **The twin's `hmass` fence**: the walk `1`-pair of mass `2` does
NOT map through the twin (`(1,1) ᵥ* G = (1,1) ≠ (4/5) • (1,1)`). -/
theorem sfa_twin_hmass_fence :
    ¬ (sfaOnes ᵥ* googleMatrix prCyc (4 / 5 : ℝ) = (4 / 5 : ℝ) • sfaOnes) := by
  intro h
  rw [sfaOnes_pair] at h
  have h0 := congrFun h 0
  simp only [Pi.smul_apply, smul_eq_mul, sfaOnes, Matrix.cons_val_zero] at h0
  norm_num at h0

/-- **The iff's `hc1` fence**: at `c = α = 1` the LEFT side holds (the
stationary pair, `|1| = 1 = α`) while NO mass-zero `1`-pair of the
swap exists — the iff without `c ≠ 1` is false. -/
theorem sfa_iff_hc1_fence :
    ¬ (∃ ν : Fin 2 → ℝ, ν ≠ 0 ∧ ∑ i, ν i = 0 ∧
      ν ᵥ* walkTransitionMatrix prCyc = (1 : ℝ) • ν) := by
  rintro ⟨ν, hν0, hmass, hν⟩
  have hline : ν 1 = -ν 0 := by
    have h := hmass
    simp only [Fin.sum_univ_two] at h
    linarith
  have heq := congrFun hν 0
  rw [prCycP_eq] at heq
  simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two,
    Pi.smul_apply, smul_eq_mul, prCyc] at heq
  rw [hline] at heq
  norm_num at heq
  have h0 : ν 0 = 0 := by linarith
  apply hν0
  funext i
  fin_cases i <;> simp [h0, hline]

/-- **The iff's left side at `c = α = 1`** (the genuine half of the
fence above). -/
theorem sfaOnes_pair_alpha1 :
    sfaOnes ᵥ* googleMatrix prCyc (1 : ℝ) = (1 : ℝ) • sfaOnes := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, sfaOnes,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      Pi.smul_apply, smul_eq_mul,
      googleMatrix, walkTransitionMatrix, deg, prCyc,
      degreeMatrix, Matrix.diagonal_apply, Matrix.diagonal_mul,
      inv_mul_cancel₀, Fintype.card_fin]

/-- The non-stochastic engine fixture: `M² = 1` (strictly positive)
with a mixed-sign peripheral left-pair at `-1`. -/
noncomputable def sfaNS : Matrix (Fin 2) (Fin 2) ℝ := !![0, 2; 1/2, 0]

theorem sfaNS_sq : sfaNS ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two, sfaNS,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      Matrix.vecHead, Matrix.vecTail]

theorem sfaNS_vecMul_pair :
    ![1, -2] ᵥ* sfaNS = (-1 : ℝ) • ![1, -2] := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one, sfaNS]

/-- **The engine's `hrow` fence**: `M² = 1 > 0` and the `-1`-pair is
genuinely peripheral, but `M` is not row-stochastic (rows `2` and
`1/2`) — and the conclusion fails: the pair is mixed-sign. -/
theorem sfa_engine_hrow_fence :
    ¬ ((∀ i : Fin 2, 0 ≤ (![1, -2] : Fin 2 → ℝ) i) ∨
       (∀ i : Fin 2, (![1, -2] : Fin 2 → ℝ) i ≤ 0)) := by
  intro h
  rcases h with h | h
  · have := h 1
    norm_num at this
  · have := h 0
    norm_num at this

/-- **The engine's `hk` fence**: the swap IS row-stochastic and the
alternating vector is a genuine peripheral `-1`-pair, but no power is
strictly positive (`prCyc_not_primitive`) — and the conclusion fails:
the pair is mixed-sign. -/
theorem sfa_engine_hk_fence :
    ¬ ((∀ i : Fin 2, 0 ≤ prAlt i) ∨ (∀ i : Fin 2, prAlt i ≤ 0)) := by
  intro h
  rcases h with h | h
  · have := h 1
    norm_num [prAlt, Matrix.head_cons] at this
  · have := h 0
    norm_num [prAlt, Matrix.cons_val_zero] at this

/-- **The doubly-stochastic trio's `hcol` fence (mass half)**: the
right eigenvector at the non-column-stochastic `prPrim` has mass
`-4 ≠ 0` — the delivered boundary witness in fence form. -/
theorem sfa_hcol_mass_fence : ¬ (∑ i, prPrimRV i = 0) := by
  rw [prPrimRV_mass_ne]
  norm_num

end SharpFences

section SortedSpectrumQA

/-!
### Section Sorted: the sorted-spectrum pins at the two-cycle

The sorted-spectrum delivery's QA obligation (2026-09-06): the
two-cycle (2-regular symmetric) — the Google matrix's symmetry
pinned, the top `evals ⟨1⟩ = 1` pinned, the bottom `evals ⟨0⟩ = -4/5`
ATTAINED (through the trace engine and the pinned top), the
second-from-top instance, and the trace pin. The follow-on
(the separating 4-cycle fixture, where the second-from-top index is
DISTINCT from the bottom) is pinned further below.
-/

theorem prCyc_deg_one : ∀ i, deg prCyc i = 1 := by
  intro i
  fin_cases i <;> norm_num [deg, prCyc, Fin.sum_univ_two]

theorem prCyc_isSymm : prCyc.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

theorem prCycG_symm : (googleMatrix prCyc (4 / 5 : ℝ)).IsSymm :=
  googleMatrix_isSymm_of_regular prCyc prCyc_isSymm 1 prCyc_deg_one (4 / 5)

/-- **The top pinned**: `evals G(4/5) ⟨1⟩ = 1` at the two-cycle. -/
theorem prCycG_top_QA :
    evals prCycG_symm ⟨1, by norm_num [Fintype.card_fin]⟩ = 1 := by
  have h := googleMatrix_evals_top_eq_one prCyc prCyc_nonneg prCyc_deg_pos
    (by norm_num : (0 : ℝ) < 4 / 5) (by norm_num : (4 / 5 : ℝ) < 1) prCycG_symm
  simpa [Fintype.card_fin] using h

/-- The trace pin (the bottom pin's other input). -/
theorem prCycG_trace : (googleMatrix prCyc (4 / 5 : ℝ)).trace = 1 / 5 := by
  norm_num [Matrix.trace, prCycG_eq, Fin.sum_univ_two]

/-- **The bottom pinned and ATTAINED**: `evals G(4/5) ⟨0⟩ = -4/5 = -α`
— through the trace engine and the pinned top (load-bearing on
both). -/
theorem prCycG_bot_QA :
    evals prCycG_symm ⟨0, by norm_num [Fintype.card_fin]⟩ = -4 / 5 := by
  have htop : evals prCycG_symm ⟨1, by norm_num [Fintype.card_fin]⟩ = 1 := prCycG_top_QA
  have hsum : evals prCycG_symm ⟨0, by norm_num [Fintype.card_fin]⟩
      + evals prCycG_symm ⟨1, by norm_num [Fintype.card_fin]⟩ = 1 / 5 := by
    have h := evals_sum_eq_trace prCycG_symm
    rw [prCycG_trace] at h
    have h' : ∑ i : Fin 2, evals prCycG_symm i = 1 / 5 := h
    rw [Fin.sum_univ_two] at h'
    exact h'
  rw [htop] at hsum
  linarith

/-- **The second-from-top instance**: at `n = 2` the index
`⟨n−2⟩ = ⟨0⟩`, and the ceiling `−4/5 ≤ 4/5` holds — instantiated
through the second-from-top theorem. -/
theorem prCycG_second_QA :
    evals prCycG_symm ⟨0, by norm_num [Fintype.card_fin]⟩ ≤ 4 / 5 := by
  have h := googleMatrix_evals_second_le prCyc prCyc_nonneg prCyc_deg_pos
    (by norm_num : (0 : ℝ) < 4 / 5) (by norm_num : (4 / 5 : ℝ) < 1) prCycG_symm
    (by norm_num : 2 ≤ Fintype.card (Fin 2))
  simpa [Fintype.card_fin] using h

/-! ### The separating regular fixture: the 4-cycle pins

The sorted-spectrum delivery's priced follow-up
(`proposals/sharp-second-eigenvalue-layer.md`, 2026-09-06): at `n = 2`
the second-from-top index COINCIDES with the bottom, so the two
delivered bounds were never pinned at distinct sorted indices. The
4-cycle (`C₄`, 2-regular symmetric) separates them: `G(4/5) =
(2/5)·A + (1/20)·J` has entries `9/20` (edges) and `1/20` (floor),
trace `1/5`, and spectrum ascending `{-4/5, 0, 0, 1}` — the
second-from-top sits STRICTLY inside the `α`-disk at `0` while the
bottom ATTAINS `-α`. The exact middle pins are the subspace
Rayleigh–Ritz engine's (`evals_le_of_linearIndependent`) first
exercise on the PageRank family, at `k = 2` and `k = 3`. -/

/-- The 4-cycle adjacency — 2-regular, symmetric. -/
def prC4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0]

theorem prC4_nonneg : ∀ i j, 0 ≤ prC4 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [prC4]

theorem prC4_deg_two : ∀ i, deg prC4 i = 2 := by
  intro i
  fin_cases i <;> simp [deg, prC4, Fin.sum_univ_four] <;> norm_num

theorem prC4_deg_pos : ∀ i, 0 < deg prC4 i := by
  intro i
  rw [prC4_deg_two i]
  norm_num

theorem prC4_isSymm : prC4.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

theorem prC4G_symm : (googleMatrix prC4 (4 / 5 : ℝ)).IsSymm :=
  googleMatrix_isSymm_of_regular prC4 prC4_isSymm 2 prC4_deg_two (4 / 5)

/-- The concrete matrix pin: every entry is the edge value `9/20` or
the teleportation floor `1/20`. -/
theorem prC4G_eq :
    googleMatrix prC4 (4 / 5 : ℝ) =
      !![1/20, 9/20, 1/20, 9/20; 9/20, 1/20, 9/20, 1/20;
         1/20, 9/20, 1/20, 9/20; 9/20, 1/20, 9/20, 1/20] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [googleMatrix, walkTransitionMatrix, deg, prC4, Fin.sum_univ_four,
      degreeMatrix, Matrix.diagonal_apply, Matrix.diagonal_mul, inv_mul_cancel₀,
      Fintype.card_fin]

/-- The trace pin: `4 · 1/20 = 1/5`. -/
theorem prC4G_trace : (googleMatrix prC4 (4 / 5 : ℝ)).trace = 1 / 5 := by
  norm_num [Matrix.trace, prC4G_eq, Fin.sum_univ_four]

/-- The alternating mode, a `G`-eigenvector at `-α = -4/5`. -/
def prC4Alt : Fin 4 → ℝ := ![1, -1, 1, -1]

theorem prC4Alt_ne : prC4Alt ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [prC4Alt] at h0

theorem prC4G_alt_pair :
    googleMatrix prC4 (4 / 5 : ℝ) *ᵥ prC4Alt = (-4 / 5 : ℝ) • prC4Alt := by
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_four, prC4G_eq,
      prC4Alt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
      Matrix.head_cons]

/-- The even-odd mode `e₀ − e₂`, a `G`-eigenvector at `0`. -/
def prC4E02 : Fin 4 → ℝ := ![1, 0, -1, 0]

theorem prC4E02_ne : prC4E02 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [prC4E02] at h0

theorem prC4G_e02_pair :
    googleMatrix prC4 (4 / 5 : ℝ) *ᵥ prC4E02 = (0 : ℝ) • prC4E02 := by
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_four, prC4G_eq,
      prC4E02, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
      Matrix.head_cons]

/-- The even-odd mode `e₁ − e₃`, a `G`-eigenvector at `0`. -/
def prC4E13 : Fin 4 → ℝ := ![0, 1, 0, -1]

theorem prC4E13_ne : prC4E13 ≠ 0 := by
  intro h
  have h0 := congrFun h 1
  simp [prC4E13] at h0

theorem prC4G_e13_pair :
    googleMatrix prC4 (4 / 5 : ℝ) *ᵥ prC4E13 = (0 : ℝ) • prC4E13 := by
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_four, prC4G_eq,
      prC4E13, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
      Matrix.head_cons]

/-- The numeric pairwise dot pins — the mode family's Gram matrix
(`2`, `2`, `4` on the diagonal, `0` off). -/
theorem prC4E02_dotE02 : Matrix.dotProduct prC4E02 prC4E02 = 2 := by
  norm_num [Matrix.dotProduct, prC4E02, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.head_cons]

theorem prC4E13_dotE13 : Matrix.dotProduct prC4E13 prC4E13 = 2 := by
  norm_num [Matrix.dotProduct, prC4E13, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.head_cons]

theorem prC4E02_dotE13 : Matrix.dotProduct prC4E02 prC4E13 = 0 := by
  norm_num [Matrix.dotProduct, prC4E02, prC4E13, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.head_cons]

theorem prC4E13_dotE02 : Matrix.dotProduct prC4E13 prC4E02 = 0 := by
  norm_num [Matrix.dotProduct, prC4E13, prC4E02, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.head_cons]

theorem prC4E02_dotAlt : Matrix.dotProduct prC4E02 prC4Alt = 0 := by
  norm_num [Matrix.dotProduct, prC4E02, prC4Alt, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.head_cons]

theorem prC4E13_dotAlt : Matrix.dotProduct prC4E13 prC4Alt = 0 := by
  norm_num [Matrix.dotProduct, prC4E13, prC4Alt, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.head_cons]

theorem prC4Alt_dotE02 : Matrix.dotProduct prC4Alt prC4E02 = 0 := by
  norm_num [Matrix.dotProduct, prC4Alt, prC4E02, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.head_cons]

theorem prC4Alt_dotE13 : Matrix.dotProduct prC4Alt prC4E13 = 0 := by
  norm_num [Matrix.dotProduct, prC4Alt, prC4E13, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.head_cons]

theorem prC4Alt_dotAlt : Matrix.dotProduct prC4Alt prC4Alt = 4 := by
  norm_num [Matrix.dotProduct, prC4Alt, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.head_cons]

/-- The two-dimensional test family. -/
def prC4Fam2 : Fin 2 → (Fin 4 → ℝ) := ![prC4E02, prC4E13]

theorem prC4Fam2_zero : prC4Fam2 0 = prC4E02 := rfl
theorem prC4Fam2_one : prC4Fam2 1 = prC4E13 := rfl

/-- The three-dimensional test family. -/
def prC4Fam3 : Fin 3 → (Fin 4 → ℝ) := ![prC4E02, prC4E13, prC4Alt]

theorem prC4Fam3_zero : prC4Fam3 0 = prC4E02 := rfl
theorem prC4Fam3_one : prC4Fam3 1 = prC4E13 := rfl
theorem prC4Fam3_two : prC4Fam3 2 = prC4Alt := rfl

/-- `G` acts as the zero map on the span of the two `0`-modes. -/
theorem prC4G_two_family_mulVec (c : Fin 2 → ℝ) :
    googleMatrix prC4 (4 / 5 : ℝ) *ᵥ (∑ l : Fin 2, c l • prC4Fam2 l)
      = 0 := by
  simp only [Fin.sum_univ_two, Matrix.mulVec_add, Matrix.mulVec_smul,
    prC4Fam2_zero, prC4Fam2_one, prC4G_e02_pair, prC4G_e13_pair, smul_smul,
    mul_zero, zero_smul, smul_zero, add_zero]

/-- **`evals ⟨1⟩ ≤ 0`** by the subspace Rayleigh–Ritz engine at the
2-dimensional test family `{e₀−e₂, e₁−e₃}`: on its span `G` acts as
`0`, so the quadratic form vanishes identically. -/
theorem prC4G_one_le_zero :
    evals prC4G_symm ⟨1, by norm_num [Fintype.card_fin]⟩ ≤ 0 := by
  have hgi : LinearIndependent ℝ prC4Fam2 := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hdot0 : Matrix.dotProduct prC4E02
        (∑ l : Fin 2, c l • prC4Fam2 l) = 0 := by
      rw [hc, Matrix.dotProduct_zero]
    have hdot1 : Matrix.dotProduct prC4E13
        (∑ l : Fin 2, c l • prC4Fam2 l) = 0 := by
      rw [hc, Matrix.dotProduct_zero]
    rw [Fin.sum_univ_two, Matrix.dotProduct_add, Matrix.dotProduct_smul,
      Matrix.dotProduct_smul, prC4Fam2_zero, prC4Fam2_one, prC4E02_dotE02,
      prC4E02_dotE13, smul_eq_mul] at hdot0
    rw [Fin.sum_univ_two, Matrix.dotProduct_add, Matrix.dotProduct_smul,
      Matrix.dotProduct_smul, prC4Fam2_zero, prC4Fam2_one, prC4E13_dotE02,
      prC4E13_dotE13, smul_eq_mul] at hdot1
    norm_num at hdot0 hdot1
    have hc0 : c 0 = 0 := by linarith
    have hc1 : c 1 = 0 := by linarith
    fin_cases i
    · exact hc0
    · exact hc1
  refine evals_le_of_linearIndependent prC4G_symm (k := 2)
    (by norm_num) (by norm_num) hgi ?_
  intro c
  rw [quadForm, prC4G_two_family_mulVec c, Matrix.dotProduct_zero, zero_mul]

/-- `G` acts as `-(4/5) · c₂ •` the alternating mode on the span of
the three-family. -/
theorem prC4G_three_family_mulVec (c : Fin 3 → ℝ) :
    googleMatrix prC4 (4 / 5 : ℝ) *ᵥ (∑ l : Fin 3, c l • prC4Fam3 l)
      = (-(4 / 5 : ℝ) * c 2) • prC4Alt := by
  simp only [Fin.sum_univ_three, Matrix.mulVec_add, Matrix.mulVec_smul,
    prC4Fam3_zero, prC4Fam3_one, prC4Fam3_two, prC4G_e02_pair, prC4G_e13_pair,
    prC4G_alt_pair, smul_smul, mul_zero, zero_smul, smul_zero, add_zero]
  rw [zero_add]
  congr 1
  ring

/-- **`evals ⟨2⟩ ≤ 0`** by the subspace Rayleigh–Ritz engine at the
3-dimensional test family `{e₀−e₂, e₁−e₃, alternating}`: on its span
`quadForm G x = -(16/5) · c₂² ≤ 0`. -/
theorem prC4G_two_le_zero :
    evals prC4G_symm ⟨2, by norm_num [Fintype.card_fin]⟩ ≤ 0 := by
  have hgi : LinearIndependent ℝ prC4Fam3 := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hdot0 : Matrix.dotProduct prC4E02
        (∑ l : Fin 3, c l • prC4Fam3 l) = 0 := by
      rw [hc, Matrix.dotProduct_zero]
    have hdot1 : Matrix.dotProduct prC4E13
        (∑ l : Fin 3, c l • prC4Fam3 l) = 0 := by
      rw [hc, Matrix.dotProduct_zero]
    have hdot2 : Matrix.dotProduct prC4Alt
        (∑ l : Fin 3, c l • prC4Fam3 l) = 0 := by
      rw [hc, Matrix.dotProduct_zero]
    rw [Fin.sum_univ_three, Matrix.dotProduct_add, Matrix.dotProduct_add,
      Matrix.dotProduct_smul, Matrix.dotProduct_smul, Matrix.dotProduct_smul,
      prC4Fam3_zero, prC4Fam3_one, prC4Fam3_two, prC4E02_dotE02,
      prC4E02_dotE13, prC4E02_dotAlt, smul_eq_mul] at hdot0
    rw [Fin.sum_univ_three, Matrix.dotProduct_add, Matrix.dotProduct_add,
      Matrix.dotProduct_smul, Matrix.dotProduct_smul, Matrix.dotProduct_smul,
      prC4Fam3_zero, prC4Fam3_one, prC4Fam3_two, prC4E13_dotE02,
      prC4E13_dotE13, prC4E13_dotAlt, smul_eq_mul] at hdot1
    rw [Fin.sum_univ_three, Matrix.dotProduct_add, Matrix.dotProduct_add,
      Matrix.dotProduct_smul, Matrix.dotProduct_smul, Matrix.dotProduct_smul,
      prC4Fam3_zero, prC4Fam3_one, prC4Fam3_two, prC4Alt_dotE02,
      prC4Alt_dotE13, prC4Alt_dotAlt, smul_eq_mul] at hdot2
    norm_num at hdot0 hdot1 hdot2
    have hc0 : c 0 = 0 := by linarith
    have hc1 : c 1 = 0 := by linarith
    have hc2 : c 2 = 0 := by linarith
    fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2
  refine evals_le_of_linearIndependent prC4G_symm (k := 3)
    (by norm_num) (by norm_num) hgi ?_
  intro c
  have hdotu : Matrix.dotProduct (∑ l : Fin 3, c l • prC4Fam3 l) prC4Alt
      = 4 * c 2 := by
    rw [Fin.sum_univ_three, Matrix.add_dotProduct, Matrix.add_dotProduct,
      Matrix.smul_dotProduct, Matrix.smul_dotProduct, Matrix.smul_dotProduct,
      prC4Fam3_zero, prC4Fam3_one, prC4Fam3_two, prC4E02_dotAlt,
      prC4E13_dotAlt, prC4Alt_dotAlt]
    simp only [smul_eq_mul, mul_zero, zero_add]
    ring
  rw [quadForm, prC4G_three_family_mulVec c, Matrix.dotProduct_smul, smul_eq_mul,
    hdotu, zero_mul]
  nlinarith [sq_nonneg (c 2)]

/-- **The top pinned**: `evals ⟨3⟩ = 1` at the 4-cycle. -/
theorem prC4G_top_QA :
    evals prC4G_symm ⟨3, by norm_num [Fintype.card_fin]⟩ = 1 := by
  have h := googleMatrix_evals_top_eq_one prC4 prC4_nonneg prC4_deg_pos
    (by norm_num : (0 : ℝ) < 4 / 5) (by norm_num : (4 / 5 : ℝ) < 1) prC4G_symm
  simpa [Fintype.card_fin] using h

/-- **The bottom pinned and ATTAINED**: `evals ⟨0⟩ = -4/5 = -α` —
`googleMatrix_evals_bot_ge` from below, the exhibited `-α` eigenpair
plus `evals_first_le_eigvalOf` from above (load-bearing on both the
delivered theorem and the concrete fixture). -/
theorem prC4G_bot_QA :
    evals prC4G_symm ⟨0, by norm_num [Fintype.card_fin]⟩ = -4 / 5 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul prC4G_symm
      prC4Alt_ne prC4G_alt_pair
    have hfirst := evals_first_le_eigvalOf prC4G_symm
      (by norm_num : 1 ≤ Fintype.card (Fin 4)) i
    rw [hi] at hfirst
    exact hfirst
  · have h := googleMatrix_evals_bot_ge prC4 prC4_nonneg prC4_deg_pos
      (by norm_num : (0 : ℝ) < 4 / 5) prC4G_symm
    have h' : -(4 / 5 : ℝ)
        ≤ evals prC4G_symm ⟨0, by norm_num [Fintype.card_fin]⟩ := by
      simpa [Fintype.card_fin] using h
    linarith

/-- The full-spectrum sum at the fixture. -/
theorem prC4G_sum :
    ∑ i : Fin 4, evals prC4G_symm i = 1 / 5 := by
  have h := evals_sum_eq_trace prC4G_symm
  rw [prC4G_trace] at h
  exact h

/-- **The separating second-from-top pin**: `evals ⟨2⟩ = 0` — the
literal `λ₂` of the family name, STRICTLY inside the `α`-disk, at an
index DISTINCT from the bottom (the `n = 2` fixture could not see
this). The trace engine plus both family bounds. -/
theorem prC4G_second_QA :
    evals prC4G_symm ⟨2, by norm_num [Fintype.card_fin]⟩ = 0 := by
  have hsum' : evals prC4G_symm ⟨0, by norm_num [Fintype.card_fin]⟩
      + evals prC4G_symm ⟨1, by norm_num [Fintype.card_fin]⟩
      + evals prC4G_symm ⟨2, by norm_num [Fintype.card_fin]⟩
      + evals prC4G_symm ⟨3, by norm_num [Fintype.card_fin]⟩ = 1 / 5 := by
    have h := prC4G_sum
    rw [Fin.sum_univ_four] at h
    exact h
  rw [prC4G_bot_QA, prC4G_top_QA] at hsum'
  linarith [prC4G_one_le_zero, prC4G_two_le_zero]

/-- **The separating first pin**: `evals ⟨1⟩ = 0` (the second `0`). -/
theorem prC4G_first_QA :
    evals prC4G_symm ⟨1, by norm_num [Fintype.card_fin]⟩ = 0 := by
  have hsum' : evals prC4G_symm ⟨0, by norm_num [Fintype.card_fin]⟩
      + evals prC4G_symm ⟨1, by norm_num [Fintype.card_fin]⟩
      + evals prC4G_symm ⟨2, by norm_num [Fintype.card_fin]⟩
      + evals prC4G_symm ⟨3, by norm_num [Fintype.card_fin]⟩ = 1 / 5 := by
    have h := prC4G_sum
    rw [Fin.sum_univ_four] at h
    exact h
  rw [prC4G_bot_QA, prC4G_top_QA] at hsum'
  linarith [prC4G_one_le_zero, prC4G_two_le_zero]

/-- **The separation itself**: the second-from-top and the bottom are
DISTINCT sorted indices with distinct values — the `n = 2` coincident
fixture's separating witness. -/
theorem prC4G_second_ne_bot_QA :
    evals prC4G_symm ⟨2, by norm_num [Fintype.card_fin]⟩
      ≠ evals prC4G_symm ⟨0, by norm_num [Fintype.card_fin]⟩ := by
  rw [prC4G_second_QA, prC4G_bot_QA]
  norm_num

/-- **The strict ceiling instance at the separated index**:
`|λ₂| = |0| = 0 < α = 4/5` — the ceiling STRICTLY satisfied at the
second-from-top while the bottom attains `-α` exactly: both bounds of
the family name `|λ₂| ≤ α` instantiated at distinct sorted indices. -/
theorem prC4G_second_strict_QA :
    |evals prC4G_symm ⟨2, by norm_num [Fintype.card_fin]⟩| < 4 / 5 := by
  rw [prC4G_second_QA]
  norm_num

theorem prC4G_abs_bot_attained_QA :
    |evals prC4G_symm ⟨0, by norm_num [Fintype.card_fin]⟩| = 4 / 5 := by
  rw [prC4G_bot_QA]
  norm_num

end SortedSpectrumQA

end Scaffold.QA.SpectralGraph
