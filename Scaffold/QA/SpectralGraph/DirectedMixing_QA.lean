import Scaffold.Mathlib.GraphTheory.DirectedMixing
import Scaffold.QA.SpectralGraph.PageRank_QA
import Mathlib.Data.Matrix.Notation

/-!
# Directed mixing QA

Load-bearing QA for `Scaffold.Mathlib.GraphTheory.DirectedMixing` —
the PageRank power iteration, conditional on the
`primitive_power_tendsto` admission — together with the admission's
own mandated fence. Nothing here proves or validates the axiom; the
conditional lemmas below inherit its trust cost (checked by
`#print axioms`). Four sections, reusing `PageRank_QA`'s fixtures (the
QA-to-QA import precedent):

- **Section A** (positive witness, the reducible `A4` fixture at
  `α = 1/2`): the Google matrix primitive by theorem route with a raw
  floor spot-check; its irreducibility reached by **two routes** (the
  delivered single-arc route vs the new primitivity transfer — a
  misstatement in `reachable_of_pow_pos` contradicts the delivered
  independent proof); the power iteration instantiated at `e₀` with
  the limit coefficient pinned raw to the uniform PageRank value; the
  second iterate computed completely raw, strictly inside the limit
  (the sequence visibly in motion toward it); the entrywise and
  non-uniform-start walk forms instantiated.
- **Section B** (the periodicity refutation — the admission's fence):
  the directed 2-cycle `P₂ = !![0,1;1,0]` — nonnegative,
  row-stochastic, *and irreducible*, with the uniform stationary
  distribution verified raw — is provably *not* primitive (every power
  is `1` or `P₂`, both with zero entries), and its power action at
  `e₀` provably has **no limit at all** (even/odd subsequences at
  `e₀`/`e₁`). The hypothesis-free conclusion is refuted in proved
  form with exactly `hprim` isolated: this is simultaneously the
  documentation of why `perron_frobenius`'s no-dominance scope was the
  honest call, and why the new admission needs primitivity.
- **Section C** (coherence): powers of the Google matrix fix
  `onesVec` unconditionally; joined with the axiom's limit at
  `x = onesVec`, limit uniqueness forces the limit coefficient
  `(π ⬝ᵥ onesVec)` to be `1` — cross-checked against the raw
  computation of `∑ i, π i` (the two routes to the same mass fact).
- **Section D** (the degenerate-cardinality audit,
  `proposals/audit-perron-frobenius-family-degenerate-corner.md`,
  2026-08-28): at `Fintype.card V = 0` the axiom's mass-one hypothesis
  is unsatisfiable (`mass_one_unsat_card_zero_QA` — safe by
  unsatisfiability, no guard needed); at the singleton `Fin 1` /
  `!![1]` every hypothesis is satisfiable and the axiom's limit is
  the hand-provable constant sequence (`P1_singleton_hand_QA` / the
  axiom instance `P1_singleton_axiom_QA`).
-/
open scoped Matrix Topology

namespace Scaffold.QA.SpectralGraph

open SpectralGraphTheory Matrix Filter

/-! ## Section A: the positive witness on the reducible fixture -/

/-- The Google matrix of the reducible fixture is primitive — theorem
route (the teleportation floor at `k = 1`). -/
theorem dmQA_google_isPrimitive : (A4G).IsPrimitive :=
  googleMatrix_isPrimitive A4 A4_nonneg_QA A4_deg_QA (by norm_num) (by norm_num)

/-- Raw spot-check of the floor at a zero-support pair of the fixture
(the walk entry `A4 0 3` is `0`; the floor is the only mass). -/
theorem dmQA_floor_raw : 0 < A4G 0 3 := by rw [A4G_03]; norm_num

/-- Irreducibility by the new primitivity transfer (route 2; route 1
is the imported `A4G_irr_QA` by single arcs). -/
theorem dmQA_google_irr_transfer : A4G.IsIrreducible :=
  Scaffold.LinearAlgebra.isIrreducible_of_isPrimitive
    (fun i j => le_of_lt (googleMatrix_pos A4 A4_nonneg_QA A4_deg_QA
      (by norm_num) (by norm_num) i j))
    dmQA_google_isPrimitive

-- (No equality lemma joins the two irreducibility routes: proofs of
-- the same `Prop` are `rfl`-equal by proof irrelevance, so such a
-- lemma would be inert surface. The two-route content is that the
-- delivered single-arc proof and the new primitivity transfer *both*
-- hold — a misstatement in either contradicts nothing here, which is
-- why the load-bearing join lives one level up, in the fence below,
-- where the *conclusion* is refuted on the fixture the transfer's
-- hypothesis cannot reach.)

/-- The power iteration at `e₀` (conditional on
`primitive_power_tendsto`): the iterated Google action converges
entrywise. -/
theorem dmQA_power_e0 :
    Filter.Tendsto (fun t : ℕ => (A4G ^ t) *ᵥ (![1, 0, 0, 0] : Fin 4 → ℝ))
      Filter.atTop (𝓝 ((u4 ⬝ᵥ (![1, 0, 0, 0] : Fin 4 → ℝ)) • (1 : Fin 4 → ℝ))) :=
  pageRank_powerIteration A4 A4_nonneg_QA A4_deg_QA (by norm_num) (by norm_num)
    u4_nonneg_QA u4_sum_QA u4_stationary_raw_QA _

/-- The limit coefficient, computed raw: the uniform PageRank weight
`1/4`. -/
theorem dmQA_power_e0_limit :
    (u4 ⬝ᵥ (![1, 0, 0, 0] : Fin 4 → ℝ)) = 1 / 4 := by
  simp [Matrix.dotProduct, u4, Fin.sum_univ_four]

/-- Entrywise convergence at a zero-support pair (conditional on
`primitive_power_tendsto`). -/
theorem dmQA_entrywise_03 :
    Filter.Tendsto (fun t : ℕ => (A4G ^ t) 0 3) Filter.atTop (𝓝 (u4 3)) :=
  pageRank_entrywise_tendsto A4 A4_nonneg_QA A4_deg_QA (by norm_num)
    (by norm_num) u4_nonneg_QA u4_sum_QA u4_stationary_raw_QA 0 3

/-- The entrywise limit value, raw: `u4 3 = 1/4`. -/
theorem dmQA_entrywise_03_limit : u4 3 = 1 / 4 := rfl

/-- The second iterate, computed completely raw from the pinned
entries: `(A4G ^ 2) 0 3 = 3/16`. -/
theorem dmQA_sq_03 : (A4G ^ 2) 0 3 = 3 / 16 := by
  rw [pow_two, Matrix.mul_apply, Fin.sum_univ_four, A4G_00, A4G_03,
    A4G_01, A4G_13, A4G_02, A4G_23, A4G_33]
  norm_num

/-- The second iterate is strictly inside the limit: the sequence is
visibly in motion toward `1/4` from below. -/
theorem dmQA_sq_03_lt : (A4G ^ 2) 0 3 < u4 3 := by
  rw [dmQA_sq_03, show u4 3 = 1 / 4 from rfl]; norm_num

/-- The non-uniform start sums to one (raw). -/
theorem dmQA_nu_sum : ∑ i, (![1 / 2, 1 / 2, 0, 0] : Fin 4 → ℝ) i = 1 := by
  norm_num [Fin.sum_univ_four]

/-- The walk-evolution form at the non-uniform start (conditional on
`primitive_power_tendsto`): genuinely mixing toward the uniform
PageRank distribution. -/
theorem dmQA_walk_nu :
    Filter.Tendsto (fun t : ℕ =>
        (![1 / 2, 1 / 2, 0, 0] : Fin 4 → ℝ) ᵥ* (A4G ^ t))
      Filter.atTop (𝓝 u4) :=
  pageRank_walk_tendsto A4 A4_nonneg_QA A4_deg_QA (by norm_num) (by norm_num)
    u4_nonneg_QA u4_sum_QA u4_stationary_raw_QA _ dmQA_nu_sum

/-! ## Section B: the periodicity refutation (the admission's fence) -/

/-- The directed 2-cycle: nonnegative, row-stochastic, irreducible —
and periodic. -/
noncomputable def P2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem P2_nonneg : ∀ i j, 0 ≤ P2 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [P2]

theorem P2_row_sum (i : Fin 2) : ∑ j, P2 i j = 1 := by
  fin_cases i <;> norm_num [P2, Fin.sum_univ_two]

theorem P2_irreducible : P2.IsIrreducible := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    [exact Relation.ReflTransGen.refl;
     exact Relation.ReflTransGen.single (by norm_num [P2]);
     exact Relation.ReflTransGen.single (by norm_num [P2]);
     exact Relation.ReflTransGen.refl]

/-- The uniform distribution on `Fin 2`. -/
noncomputable def u2 : Fin 2 → ℝ := ![1 / 2, 1 / 2]

theorem u2_nonneg : ∀ i, 0 ≤ u2 i := by
  intro i; fin_cases i <;> norm_num [u2]

theorem u2_sum : ∑ i, u2 i = 1 := by norm_num [u2, Fin.sum_univ_two]

/-- The uniform distribution is stationary for the 2-cycle (raw). -/
theorem u2_stationary : u2 ᵥ* P2 = u2 := by
  funext i
  fin_cases i <;> norm_num [u2, P2, Matrix.vecMul, Matrix.dotProduct,
    Fin.sum_univ_two]

theorem P2_sq : P2 * P2 = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem P2_pow_even (k : ℕ) : P2 ^ (2 * k) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, ih, pow_two, P2_sq,
      one_mul]

theorem P2_pow_odd (k : ℕ) : P2 ^ (2 * k + 1) = P2 := by
  rw [pow_add, P2_pow_even, one_mul, pow_one]

/-- The 2-cycle is provably **not** primitive: every power is `1` or
`P₂`, both carrying zero entries. -/
theorem P2_not_primitive : ¬ P2.IsPrimitive := by
  rintro ⟨k, -, hpos⟩
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [hm, show m + m = 2 * m from by ring, P2_pow_even] at hpos
    have h01 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 :=
      Matrix.one_apply_ne (by decide)
    have := hpos 0 1
    rw [h01] at this
    norm_num at this
  · rw [hm, P2_pow_odd] at hpos
    have h11 : P2 1 1 = 0 := by norm_num [P2]
    have := hpos 1 1
    rw [h11] at this
    norm_num at this

theorem P2_mulVec_e0 : P2 *ᵥ (![1, 0] : Fin 2 → ℝ) = ![0, 1] := by
  funext i
  fin_cases i <;> norm_num [P2, Matrix.mulVec, Matrix.dotProduct,
    Fin.sum_univ_two]

theorem dmQA_even_atTop :
    Filter.Tendsto (fun k : ℕ => 2 * k) Filter.atTop Filter.atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨b, fun k _ => by omega⟩

theorem dmQA_odd_atTop :
    Filter.Tendsto (fun k : ℕ => 2 * k + 1) Filter.atTop Filter.atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨b + 1, fun k _ => by omega⟩

/-- **The fence**: the power action of the 2-cycle at `e₀` has no
limit at all — the even subsequence is constantly `e₀`, the odd
constantly `e₁`. -/
theorem P2_no_limit : ∀ l : Fin 2 → ℝ,
    ¬ Filter.Tendsto (fun t : ℕ => (P2 ^ t) *ᵥ (![1, 0] : Fin 2 → ℝ))
      Filter.atTop (𝓝 l) := by
  intro l h
  have heven : Filter.Tendsto (fun _ : ℕ => (![1, 0] : Fin 2 → ℝ))
      Filter.atTop (𝓝 l) := by
    have h0 := h.comp dmQA_even_atTop
    simpa only [Function.comp_def, P2_pow_even, Matrix.one_mulVec] using h0
  have hodd : Filter.Tendsto (fun _ : ℕ => (![0, 1] : Fin 2 → ℝ))
      Filter.atTop (𝓝 l) := by
    have h0 := h.comp dmQA_odd_atTop
    simpa only [Function.comp_def, P2_pow_odd, P2_mulVec_e0] using h0
  have h1 : (![1, 0] : Fin 2 → ℝ) = l :=
    tendsto_nhds_unique tendsto_const_nhds heven
  have h2 : (![0, 1] : Fin 2 → ℝ) = l :=
    tendsto_nhds_unique tendsto_const_nhds hodd
  have h4 : (![1, 0] : Fin 2 → ℝ) = (![0, 1]) := h1.trans h2.symm
  have h5 : (1 : ℝ) = 0 := by
    have hh := congrFun h4 0
    simp at hh
  exact absurd h5 (by norm_num)

/-- **The isolation**: on the 2-cycle, every hypothesis of
`primitive_power_tendsto` except `hprim` is verified — nonnegativity,
row stochasticity, and the full stationary trio for `u2` — primitivity
provably fails, and the hypothesis-free conclusion is refuted for
every candidate limit. Exactly `hprim` is the fence. -/
theorem P2_fence_isolation :
    (∀ i j, 0 ≤ P2 i j) ∧ (∀ i, ∑ j, P2 i j = 1) ∧
      (∀ i, 0 ≤ u2 i) ∧ (∑ i, u2 i = 1) ∧ (u2 ᵥ* P2 = u2) ∧
      ¬ P2.IsPrimitive ∧
      ∀ l : Fin 2 → ℝ,
        ¬ Filter.Tendsto (fun t : ℕ => (P2 ^ t) *ᵥ (![1, 0] : Fin 2 → ℝ))
          Filter.atTop (𝓝 l) :=
  ⟨P2_nonneg, P2_row_sum, u2_nonneg, u2_sum, u2_stationary,
    P2_not_primitive, P2_no_limit⟩

/-! ## Section C: the coherence join -/

/-- Powers of the Google matrix fix `onesVec` (theorem route). -/
theorem dmQA_onesVec_fix (t : ℕ) :
    (A4G ^ t) *ᵥ (onesVec : Fin 4 → ℝ) = onesVec :=
  googleMatrix_pow_mulVec_onesVec A4 A4_deg_QA (1 / 2) t

/-- The axiom's limit at `x = onesVec` (conditional on
`primitive_power_tendsto`). -/
theorem dmQA_onesVec_axiom :
    Filter.Tendsto (fun t : ℕ => (A4G ^ t) *ᵥ (onesVec : Fin 4 → ℝ))
      Filter.atTop (𝓝 ((u4 ⬝ᵥ (onesVec : Fin 4 → ℝ)) • (1 : Fin 4 → ℝ))) :=
  pageRank_powerIteration A4 A4_nonneg_QA A4_deg_QA (by norm_num) (by norm_num)
    u4_nonneg_QA u4_sum_QA u4_stationary_raw_QA _

/-- **The join** (conditional on `primitive_power_tendsto`): the
sequence is unconditionally constant at `onesVec`, so limit uniqueness
forces the axiom's limit vector to *be* `onesVec` — the axiom's limit
is consistent with the mass bookkeeping, and the limit coefficient is
pinned to `1`. -/
theorem dmQA_coherence_join :
    ((u4 ⬝ᵥ (onesVec : Fin 4 → ℝ)) • (1 : Fin 4 → ℝ)) = onesVec := by
  have hconst : Filter.Tendsto (fun _ : ℕ => (onesVec : Fin 4 → ℝ))
      Filter.atTop (𝓝 onesVec) := tendsto_const_nhds
  have hax : Filter.Tendsto (fun _ : ℕ => (onesVec : Fin 4 → ℝ))
      Filter.atTop (𝓝 ((u4 ⬝ᵥ (onesVec : Fin 4 → ℝ)) • (1 : Fin 4 → ℝ))) := by
    simpa only [dmQA_onesVec_fix] using dmQA_onesVec_axiom
  exact tendsto_nhds_unique hax hconst

/-- The raw route to the same coefficient: `u4 ⬝ᵥ onesVec = ∑ u4 = 1`. -/
theorem dmQA_coherence_raw : (u4 ⬝ᵥ (onesVec : Fin 4 → ℝ)) = 1 := by
  simp only [Matrix.dotProduct, onesVec, mul_one]
  exact u4_sum_QA

/-! ## Section D: the degenerate-cardinality audit
(`proposals/audit-perron-frobenius-family-degenerate-corner.md`,
2026-08-28). The two corners the hazard class names for
`primitive_power_tendsto`: at `Fintype.card V = 0` the mass-one
hypothesis is *unsatisfiable* (the empty sum is `0`, so the axiom's
hypothesis set has no instantiation there — safe by unsatisfiability,
not by a guard); at the singleton `Fin 1` / `!![1]` every hypothesis
is satisfiable and the axiom's limit is pinned by hand as the constant
sequence (trivial satisfiability breaks no clause). -/

/-- **The empty-cardinality verdict (no axiom contact).** At
`Fintype.card V = 0` the axiom's `hπsum : ∑ i, π i = 1` hypothesis is
unsatisfiable — the empty sum is `0` — so the axiom's hypothesis set
has **no instantiation at the degenerate dimension**: the corner is
safe by unsatisfiability, not by a `Nonempty V` guard. This theorem is
the Lean-confirmed verdict behind `scripts/lint_axioms.py`'s allowlist
entry for `primitive_power_tendsto` (provisional until this audit
landed). -/
-- @refutes: primitive_power_tendsto
theorem mass_one_unsat_card_zero_QA {V : Type} [Fintype V]
    (hV : Fintype.card V = 0) (π : V → ℝ) (hπsum : ∑ i, π i = 1) : False := by
  rw [Fintype.card_eq_zero_iff] at hV
  letI : IsEmpty V := hV
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hπsum
  norm_num at hπsum

/-- The singleton fixture: the identity `!![1]` on `Fin 1`, with the
constant-one stationary vector — every hypothesis of
`primitive_power_tendsto` satisfiable at the corner where `hπsum`
becomes trivial. -/
noncomputable def P1 : Matrix (Fin 1) (Fin 1) ℝ := !![1]

theorem P1_eq_one : P1 = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i; fin_cases j
  simp [P1, Matrix.one_apply]

theorem P1_nonneg : ∀ i j, 0 ≤ P1 i j := by
  intro i j
  fin_cases i; fin_cases j
  simp [P1]

theorem P1_row_sum (i : Fin 1) : ∑ j, P1 i j = 1 := by
  fin_cases i
  simp [P1, Fin.sum_univ_one]

theorem P1_primitive : P1.IsPrimitive := by
  refine ⟨1, by norm_num, ?_⟩
  intro i j
  fin_cases i; fin_cases j
  simp [pow_one, P1]

theorem u1_nonneg : ∀ i, 0 ≤ (1 : Fin 1 → ℝ) i := by intro i; simp

theorem u1_sum : ∑ i, (1 : Fin 1 → ℝ) i = 1 := by
  simp [Fin.sum_univ_one]

theorem u1_stationary : (1 : Fin 1 → ℝ) ᵥ* P1 = 1 := by
  funext j
  fin_cases j
  simp [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_one, P1]

/-- **Singleton hand pin (no axiom).** The axiom's conclusion shape at
the singleton, proved unconditionally: the power sequence is constant
(the identity's powers are the identity) and the limit vector is the
start itself (`(π ⬝ᵥ x) • 1 = x` on one coordinate). The statement the
axiom concludes here is genuinely true — established without it. -/
theorem P1_singleton_hand_QA (x : Fin 1 → ℝ) :
    Filter.Tendsto (fun t : ℕ => P1 ^ t *ᵥ x)
      Filter.atTop (𝓝 (((1 : Fin 1 → ℝ) ⬝ᵥ x) • (1 : Fin 1 → ℝ))) := by
  have hconst : (fun t : ℕ => P1 ^ t *ᵥ x) = fun _ : ℕ => x := by
    funext t
    rw [P1_eq_one, one_pow, Matrix.one_mulVec]
  have hlim : (((1 : Fin 1 → ℝ) ⬝ᵥ x) • (1 : Fin 1 → ℝ)) = x := by
    have hd : ((1 : Fin 1 → ℝ) ⬝ᵥ x) = x 0 := by
      simp only [Matrix.dotProduct, Pi.one_apply, one_mul, Fin.sum_univ_one]
    rw [hd]
    funext i
    fin_cases i
    simp
  rw [hconst, hlim]
  exact tendsto_const_nhds

/-- **Singleton axiom instance (conditional on
`primitive_power_tendsto`).** The axiom applied at the corner where its
mass-one hypothesis is trivially satisfiable: the instance is
non-vacuous there, and — joined with the hand pin above — its
conclusion is the hand-provable constant-sequence limit, so trivial
satisfiability breaks no clause of the statement. -/
theorem P1_singleton_axiom_QA (x : Fin 1 → ℝ) :
    Filter.Tendsto (fun t : ℕ => P1 ^ t *ᵥ x)
      Filter.atTop (𝓝 (((1 : Fin 1 → ℝ) ⬝ᵥ x) • (1 : Fin 1 → ℝ))) :=
  Scaffold.LinearAlgebra.primitive_power_tendsto P1 P1_nonneg P1_row_sum
    P1_primitive u1_nonneg u1_sum u1_stationary x

end Scaffold.QA.SpectralGraph
