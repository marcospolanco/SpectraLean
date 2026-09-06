import Scaffold.Mathlib.GraphTheory.DirectedMixing
import Scaffold.QA.SpectralGraph.PageRank_QA
import Mathlib.Data.Matrix.Notation

/-!
# Directed mixing QA

Load-bearing QA for `Scaffold.Mathlib.GraphTheory.DirectedMixing` —
the PageRank power iteration, hard crust since the 2026-09-02
retirement of the `primitive_power_tendsto` admission
(`proposals/retire-primitive-power-convergence.md`: the
Doeblin/Dobrushin contraction route, `#print axioms` on the retired
theorem exactly the standard three) — together with the admission's
own mandated fence, kept live against the now-proved statement's
hypothesis set. Nine sections, reusing `PageRank_QA`'s fixtures (the
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
  non-uniform-start walk forms instantiated. (These lemmas were
  conditional on the retired admission and are hard crust since the
  2026-09-02 retirement.)
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
- **Section E** (the retirement's mechanism section, 2026-09-02): the
  Doeblin range engine pinned on the strictly positive fixture `Qd` —
  the contraction attained exactly, the iterated contraction attained
  at every time through the exact closed form, the theorem instance
  joined to the raw closed form at the zero limit, and the wrong-`δ`
  refutation fence.
- **Section F** (the Doeblin TV contraction and the PageRank `α^t`
  rate, `proposals/doeblintv-tv-contraction-pagerank-rate.md`,
  2026-09-02): the TV contraction attained exactly on `Qd` at the
  basis pair, the iterated form attained exactly at every time
  through the mode closed form, the floor-free refutation fence on
  the permutation `P₂` (the entries-floor hypothesis exactly what
  fails), and the Google rate `TV ≤ α^t · TV₀` attained exactly at
  every time on the periodic 2-cycle — with the plain walk's
  never-decay pin `TV ≡ 1/2` beside it: the periodic chain that
  provably never mixes becomes exactly-`α`-convergent after
  teleportation.
- **Section G** (the directed mixing time and its empirical PageRank
  consumer, `proposals/directed-mixing-time-object.md`, 2026-09-02):
  the per-start law joined to Section F's closed forms
  (`PR_law_eq_QA`, `PR_tv_eq_QA`), the object `t_mix(1/8) = 2` pinned
  in both directions with the α-ceiling attained exactly
  (`⌈log 4/log 2⌉ = 2`), the depth form attained with equality at the
  threshold time, the new equal-mass entrywise TV extraction pinned
  with both sides `1/4` (equality — the constant sharp), the junk
  corner fenced at `ε = 0`, and — in
  `Scaffold.QA.Derived.EmpiricalStationary_QA` — the bias-term and
  depth-form capstone instances at `2 exp (−1/8)` and `2 exp (−1/32)`.
- **Section H** (the directed uniform mixing time,
  `proposals/directed-uniform-mixing-time.md`, 2026-09-02): the
  two-start distance's exact closed form `d(t) = (1/2)^t` from raw law
  literals with **submultiplicativity attained with equality at every
  time** (`PRU_pair_submul_attained_QA`), the Dobrushin contraction
  attained exactly at the basis pair (`PRU_contraction_attained_QA` —
  the matrix-level engine's sharp constant load-bearing on the directed
  axis), the worst-start closed form `d̄(t) = (1/2)^(t+1)` with
  `d̄ = d/2` and the domination theorem instance beside it, the mixed
  submultiplicativity attained with equality at every time, the
  uniform object `t_mix^unif(1/8) = 2` pinned in both directions
  through the sup interchange (both starts pinned `2` independently),
  the refined α-ceiling attained exactly (`⌈log (d̄(0)/ε)/log(1/α)⌉ =
  2` = the object) with the display form's slack witnessed (`2 < 3`),
  the escalation corollary attained exactly (`t_mix(1/32) = 4 =
  (1+1)·2` at the fixture's own pinned certificate constants), and the
  `ε = 0` junk corner fenced; the worst-start capstone instance lives
  in `Scaffold.QA.Derived.EmpiricalStationary_QA`.
- **Section I** (the adversarial fence completion,
  `proposals/adversarial-fences-tv-dobrushin-engines.md`, 2026-09-02):
  negative witnesses for the seven load-bearing hypotheses of the
  TV/Dobrushin engine family the 2026-09-02 deliveries left unfenced —
  the equal-mass clauses of both TV contractions (refuted at the
  all-half matrix, whose Dobrushin coefficient is exactly `0`:
  `1/2 ≤ 0`), the row-sum and nonnegativity clauses of non-expansiveness
  (the doubled identity doubles the basis pair's TV; the signed
  stochastic fixture triples it), the row-sum clause of Dobrushin
  submultiplicativity (`δ(Qx²) = 2 > δ(Qx)² = 1`), and the zero-mass
  clauses of both pairing cores (`1 ≤ 1/2`) — each with an isolation
  companion proving the refuted clause is exactly what fails at the
  fixture. Pure hard crust: these refute *theorem* instantiations, so
  no `-- @refutes` tags (nothing admitted is consumed).
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
`Fintype.card V = 0` the statement's `hπsum : ∑ i, π i = 1` hypothesis
is unsatisfiable — the empty sum is `0` — so the (formerly admitted,
now proved — retired 2026-09-02, which removed the `-- @refutes` tag
with the axiom) hypothesis set has **no instantiation at the
degenerate dimension**: the corner is safe by unsatisfiability, not by
a `Nonempty V` guard. This theorem is the Lean-confirmed verdict that
stood behind `scripts/lint_axioms.py`'s since-removed allowlist entry
for `primitive_power_tendsto`. -/
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

/-- **Singleton theorem instance.** The retired-axiom-turned-theorem
applied at the corner where its mass-one hypothesis is trivially
satisfiable: the instance is non-vacuous there, and — joined with the
hand pin above — its conclusion is the hand-provable constant-sequence
limit, so trivial satisfiability breaks no clause of the statement. -/
theorem P1_singleton_axiom_QA (x : Fin 1 → ℝ) :
    Filter.Tendsto (fun t : ℕ => P1 ^ t *ᵥ x)
      Filter.atTop (𝓝 (((1 : Fin 1 → ℝ) ⬝ᵥ x) • (1 : Fin 1 → ℝ))) :=
  Scaffold.LinearAlgebra.primitive_power_tendsto P1 P1_nonneg P1_row_sum
    P1_primitive u1_nonneg u1_sum u1_stationary x

/-! ## Section E: the retirement's mechanism QA (the Doeblin
contraction, `proposals/retire-primitive-power-convergence.md`,
2026-09-02) -/

open Scaffold.LinearAlgebra SpectralGraphTheory

/-- The contraction fixture: a strictly positive row-stochastic `2×2`
with min entry `1/4` (Doeblin coefficient `ρ = 1 - 2·(1/4) = 1/2`). -/
noncomputable def Qd : Matrix (Fin 2) (Fin 2) ℝ := !![3/4, 1/4; 1/4, 3/4]

/-- The antisymmetric test vector (entrywise range `2`). -/
noncomputable def yd : Fin 2 → ℝ := ![1, -1]

/-- The stationary distribution of the fixture (uniform). -/
noncomputable def ud : Fin 2 → ℝ := ![1/2, 1/2]

theorem Qd_nonneg : ∀ i j, 0 ≤ Qd i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Qd]

theorem Qd_row_sum : ∀ i, ∑ j, Qd i j = 1 := by
  intro i
  fin_cases i <;> norm_num [Qd, Fin.sum_univ_two]

theorem Qd_min_entry : ∀ i j, (1/4 : ℝ) ≤ Qd i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Qd]

theorem Qd_01 : Qd 0 1 = 1/4 := by norm_num [Qd]

theorem Qd_primitive : Qd.IsPrimitive := by
  refine ⟨1, by norm_num, fun i j => ?_⟩
  rw [pow_one]
  fin_cases i <;> fin_cases j <;> norm_num [Qd]

theorem ud_nonneg : ∀ i, 0 ≤ ud i := by intro i; fin_cases i <;> norm_num [ud]

theorem ud_sum : ∑ i, ud i = 1 := by norm_num [ud, Fin.sum_univ_two]

theorem ud_stationary : ud ᵥ* Qd = ud := by
  funext j
  fin_cases j <;>
    norm_num [ud, Qd, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two]

/-- The test vector's entrywise range, pinned by hand. -/
theorem yd_entryRange : entryRange yd = 2 := by
  have hsup : entrySup yd = 1 := by
    refine le_antisymm ?_ ?_
    · refine (Finset.sup'_le_iff Finset.univ_nonempty (fun i => yd i)).mpr
        fun i _ => ?_
      fin_cases i <;> norm_num [yd]
    · have h := Finset.le_sup' (fun i => yd i) (Finset.mem_univ (0 : Fin 2))
      rwa [show yd 0 = 1 from by norm_num [yd]] at h
  have hinf : entryInf yd = -1 := by
    refine le_antisymm ?_ ?_
    · have h := Finset.inf'_le (fun i => yd i) (Finset.mem_univ (1 : Fin 2))
      rwa [show yd 1 = -1 from by norm_num [yd]] at h
    · refine Finset.le_inf' Finset.univ_nonempty (fun i => yd i) fun i _ => ?_
      fin_cases i <;> norm_num [yd]
  unfold entryRange
  rw [hsup, hinf]
  norm_num

/-- The one-step action on the test vector, pinned raw: the antisymmetric
mode halves. -/
theorem Qd_mulVec_yd : Qd *ᵥ yd = (1/2 : ℝ) • yd := by
  funext i
  fin_cases i <;>
    norm_num [Qd, yd, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-- The iterated action's exact closed form: each application halves the
antisymmetric mode. -/
theorem Qd_pow_mulVec_yd (t : ℕ) :
    Qd ^ t *ᵥ yd = (1/2 : ℝ) ^ t • yd := by
  induction t with
  | zero => simp [pow_zero, Matrix.one_mulVec]
  | succ t ih =>
    calc Qd ^ (t + 1) *ᵥ yd = Qd *ᵥ (Qd ^ t *ᵥ yd) := by
          rw [pow_succ', ← Matrix.mulVec_mulVec]
      _ = Qd *ᵥ ((1/2 : ℝ) ^ t • yd) := by rw [ih]
      _ = (1/2 : ℝ) ^ t • (Qd *ᵥ yd) := Matrix.mulVec_smul _ _ _
      _ = (1/2 : ℝ) ^ t • ((1/2 : ℝ) • yd) := by rw [Qd_mulVec_yd]
      _ = (1/2 : ℝ) ^ (t + 1) • yd := by
          rw [pow_succ', smul_smul]
          congr 1
          ring

/-- The scaled test vector's entrywise range at a nonnegative scale. -/
theorem entryRange_smul_yd {c : ℝ} (hc : 0 ≤ c) : entryRange (c • yd) = c * 2 := by
  have hsup : entrySup (c • yd) = c * 1 := by
    refine le_antisymm ?_ ?_
    · refine (Finset.sup'_le_iff Finset.univ_nonempty
        (fun i => (c • yd) i)).mpr fun i _ => ?_
      fin_cases i <;> (norm_num [yd]; try linarith)
    · have h := Finset.le_sup' (fun i => (c • yd) i)
        (Finset.mem_univ (0 : Fin 2))
      simpa [yd, entrySup] using h
  have hinf : entryInf (c • yd) = c * (-1) := by
    refine le_antisymm ?_ ?_
    · have h := Finset.inf'_le (fun i => (c • yd) i)
        (Finset.mem_univ (1 : Fin 2))
      simpa [yd, entryInf] using h
    · refine Finset.le_inf' Finset.univ_nonempty (fun i => (c • yd) i)
        fun i _ => ?_
      fin_cases i <;> (norm_num [yd]; try linarith)
  unfold entryRange
  rw [hsup, hinf]
  linarith

/-- **The contraction attained exactly** (the engine's strongest QA
shape): the Doeblin bound `range (Q *ᵥ y) ≤ (1 - |V|δ) · range y` at
`δ = 1/4`, `|V| = 2` is an equality at the fixture — `1 = (1/2) · 2`.
Load-bearing on the exact coefficient: a wrong constant (`1 - δ` alone,
or `1 - |V|δ` at a wrong cardinality count) breaks the pin. -/
theorem Qd_contraction_attained_QA :
    entryRange (Qd *ᵥ yd) =
      (1 - (Fintype.card (Fin 2) : ℝ) * (1/4)) * entryRange yd := by
  have h1 : entryRange ((1/2 : ℝ) • yd) = 1 := by
    rw [entryRange_smul_yd (by norm_num)]
    norm_num
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  rw [Qd_mulVec_yd, h1, yd_entryRange, hcard]
  norm_num

/-- The engine instance at the fixture (the theorem, not the value). -/
theorem Qd_contraction_instance_QA :
    entryRange (Qd *ᵥ yd) ≤ (1 - (Fintype.card (Fin 2) : ℝ) * (1/4)) *
      entryRange yd :=
  entryRange_mulVec_le_of_pos_entries Qd_row_sum Qd_min_entry yd

/-- **The iterated contraction attained at every time.** The block
iterated bound is an equality at every `t`, through the exact closed
form. -/
theorem Qd_iterated_range_QA (t : ℕ) :
    entryRange (Qd ^ t *ᵥ yd) =
      (1 - (Fintype.card (Fin 2) : ℝ) * (1/4)) ^ t * entryRange yd := by
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  rw [Qd_pow_mulVec_yd, entryRange_smul_yd (pow_nonneg (by norm_num) t),
    yd_entryRange, hcard]
  norm_num

/-- **The retired theorem's instance at the fixture, at the zero
limit** (the mechanism's end-to-end witness): the power sequence is
the geometrically scaled mode `(1/2)^t • yd`, and the theorem's limit
at the uniform stationary vector is the zero vector (`ud ⬝ᵥ yd = 0`). -/
theorem Qd_tendsto_instance_QA :
    Filter.Tendsto (fun t : ℕ => Qd ^ t *ᵥ yd) Filter.atTop
      (𝓝 ((ud ⬝ᵥ yd) • (1 : Fin 2 → ℝ))) := by
  have hπ : ud ⬝ᵥ yd = 0 := by
    norm_num [ud, yd, Matrix.dotProduct, Fin.sum_univ_two]
  have hmain := primitive_power_tendsto Qd Qd_nonneg Qd_row_sum Qd_primitive
    ud_nonneg ud_sum ud_stationary yd
  rw [hπ] at hmain ⊢
  exact hmain

/-- The raw closed form tends to zero, independently of the theorem. -/
theorem Qd_closedForm_tendsto_QA :
    Filter.Tendsto (fun t : ℕ => (1/2 : ℝ) ^ t • yd) Filter.atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (1/2 : ℝ) < 1 by norm_num)).smul_const
    yd
  simpa using h

/-- **The wrong-δ refutation fence.** Pretending `δ = 1/2` (larger than
the true min entry `1/4`) would contract the range to zero in one step
(`1 - 2·(1/2) = 0`), forcing `Qd *ᵥ yd` constant — refuted at the
pinned values. The entries-bound hypothesis is exactly what fails:
`Qd 0 1 = 1/4 < 1/2`. -/
theorem Qd_wrong_delta_refuted_QA :
    ¬ (entryRange (Qd *ᵥ yd) ≤ (1 - (Fintype.card (Fin 2) : ℝ) * (1/2)) *
      entryRange yd) := by
  have h1 : entryRange (Qd *ᵥ yd) = 1 := by
    rw [Qd_mulVec_yd, entryRange_smul_yd (by norm_num)]
    norm_num
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  intro hcon
  rw [h1, yd_entryRange, hcard] at hcon
  norm_num at hcon

/-- **The entries-bound hypothesis provably fails at the pretend `δ`. -/
theorem Qd_half_le_refuted_QA : ¬ ∀ i j, (1/2 : ℝ) ≤ Qd i j := by
  intro hcon
  have h01 : (1/2 : ℝ) ≤ Qd 0 1 := hcon 0 1
  rw [Qd_01] at h01
  norm_num at h01

/-! ## Section F: the Doeblin TV contraction and the PageRank α^t rate

`proposals/doeblin-tv-contraction-pagerank-rate.md` (2026-09-02): the
Doeblin engine's second consumer, at the law level —
`tvDistance_vecMul_le_of_pos_entries` and its iterated/assembly forms
(`Mixing.lean`) and `pageRank_tvDistance_le` (`DirectedMixing.lean`)
pinned on the Section E fixture `Qd`, the Section B periodic fixture
`P₂`, and the Google matrix of the imported edge `A2` at `α = 1/2`
(which is `!![1/4, 3/4; 3/4, 1/4]` — the transposed `Qd` blend). The
centerpiece: the periodic chain that provably never mixes
(`P2_no_limit`) becomes exactly-`α`-convergent after teleportation,
with the bound attained at *every* time. -/

/-- The first basis vector fixture. -/
noncomputable def e0 : Fin 2 → ℝ := ![1, 0]

/-- The second basis vector fixture. -/
noncomputable def e1 : Fin 2 → ℝ := ![0, 1]

theorem e0_sum : ∑ i, e0 i = 1 := by norm_num [e0, Fin.sum_univ_two]

theorem e0_e1_mass : ∑ i, e0 i = ∑ i, e1 i := by
  norm_num [e0, e1, Fin.sum_univ_two]

theorem Qd_vecMul_e0_zero : (e0 ᵥ* Qd) 0 = 3/4 := by
  norm_num [e0, Qd, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two]

theorem Qd_vecMul_e0_one : (e0 ᵥ* Qd) 1 = 1/4 := by
  norm_num [e0, Qd, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two]

theorem Qd_vecMul_e1_zero : (e1 ᵥ* Qd) 0 = 1/4 := by
  norm_num [e1, Qd, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two]

theorem Qd_vecMul_e1_one : (e1 ᵥ* Qd) 1 = 3/4 := by
  norm_num [e1, Qd, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two]

/-- The one-step evolved laws, pinned raw. -/
theorem Qd_vecMul_e0 : e0 ᵥ* Qd = ![3/4, 1/4] := by
  funext j
  fin_cases j <;>
    simp [Qd_vecMul_e0_zero, Qd_vecMul_e0_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]

theorem Qd_vecMul_e1 : e1 ᵥ* Qd = ![1/4, 3/4] := by
  funext j
  fin_cases j <;>
    simp [Qd_vecMul_e1_zero, Qd_vecMul_e1_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]

theorem tv_e0_e1 : tvDistance e0 e1 = 1 := by
  rw [tvDistance, Fin.sum_univ_two]
  have h0 : |e0 0 - e1 0| = 1 := by
    rw [show e0 0 - e1 0 = 1 by norm_num [e0, e1], abs_one]
  have h1 : |e0 1 - e1 1| = 1 := by
    rw [show e0 1 - e1 1 = -1 by norm_num [e0, e1], abs_neg, abs_one]
  rw [h0, h1]
  norm_num

/-- **The contraction attained exactly** (the engine's strongest QA
shape, now at the law level): `TV(e₀ ᵥ* Qd, e₁ ᵥ* Qd) = 1/2` and the
coefficient times `TV(e₀, e₁) = 1` is exactly `1/2` — the bound is an
equality at the fixture. Load-bearing on the exact coefficient
`1 - |V|δ`: a wrong constant breaks the pin. -/
theorem Qd_tv_attained_QA :
    tvDistance (e0 ᵥ* Qd) (e1 ᵥ* Qd)
      = (1 - (Fintype.card (Fin 2) : ℝ) * (1/4)) * tvDistance e0 e1 := by
  have hL : tvDistance (e0 ᵥ* Qd) (e1 ᵥ* Qd) = 1/2 := by
    rw [tvDistance, Fin.sum_univ_two]
    have h0 : |(e0 ᵥ* Qd) 0 - (e1 ᵥ* Qd) 0| = 1/2 := by
      rw [Qd_vecMul_e0_zero, Qd_vecMul_e1_zero,
        show ((3:ℝ)/4 - 1/4) = 1/2 from by norm_num,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    have h1 : |(e0 ᵥ* Qd) 1 - (e1 ᵥ* Qd) 1| = 1/2 := by
      rw [Qd_vecMul_e0_one, Qd_vecMul_e1_one,
        show ((1:ℝ)/4 - 3/4) = -(1/2) from by norm_num, abs_neg,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    rw [h0, h1]
    norm_num
  have hR : (1 - (Fintype.card (Fin 2) : ℝ) * (1/4)) * tvDistance e0 e1
      = 1/2 := by
    have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
    rw [hcard, tv_e0_e1]
    norm_num
  rw [hL, hR]

/-- The contraction instance at the fixture (the theorem, not the
value). -/
theorem Qd_tv_instance_QA :
    tvDistance (e0 ᵥ* Qd) (e1 ᵥ* Qd)
      ≤ (1 - (Fintype.card (Fin 2) : ℝ) * (1/4)) * tvDistance e0 e1 :=
  tvDistance_vecMul_le_of_pos_entries Qd_row_sum Qd_min_entry e0 e1
    e0_e1_mass

/-- The fixture is symmetric, so the row action is the column action. -/
theorem Qd_symm : Qdᵀ = Qd := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The antisymmetric mode under the row action, via the symmetric
closed form. -/
theorem yd_vecMul_pow_Qd (t : ℕ) : yd ᵥ* Qd ^ t = (1/2 : ℝ)^t • yd := by
  rw [← Matrix.mulVec_transpose, Matrix.transpose_pow, Qd_symm]
  exact Qd_pow_mulVec_yd t

/-- The start vector's mode decomposition. -/
theorem e0_eq_ud_add : e0 = ud + (1/2 : ℝ) • yd := by
  funext i
  fin_cases i <;> norm_num [e0, ud, yd]

/-- **The evolved law's exact closed form**: `e₀ ᵥ* Qd^t` is the
stationary part plus the geometrically decaying antisymmetric mode. -/
theorem Qd_e0_pow (t : ℕ) :
    e0 ᵥ* Qd ^ t = ud + (1/2 : ℝ)^(t+1) • yd := by
  calc e0 ᵥ* Qd ^ t = (ud + (1/2 : ℝ) • yd) ᵥ* Qd ^ t := by rw [e0_eq_ud_add]
    _ = ud ᵥ* Qd ^ t + ((1/2 : ℝ) • yd) ᵥ* Qd ^ t := Matrix.add_vecMul _ _ _
    _ = ud + (1/2 : ℝ) • (yd ᵥ* Qd ^ t) := by
        rw [vecMul_pow_eq_of_vecMul_eq ud_stationary, Matrix.vecMul_smul]
    _ = ud + (1/2 : ℝ) • ((1/2 : ℝ)^t • yd) := by rw [yd_vecMul_pow_Qd]
    _ = ud + (1/2 : ℝ)^(t+1) • yd := by
        rw [pow_succ', smul_smul]

theorem tv_e0_ud : tvDistance e0 ud = 1/2 := by
  rw [tvDistance, Fin.sum_univ_two]
  have h0 : |e0 0 - ud 0| = 1/2 := by
    rw [show e0 0 - ud 0 = 1/2 by norm_num [e0, ud],
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  have h1 : |e0 1 - ud 1| = 1/2 := by
    rw [show e0 1 - ud 1 = -(1/2) by norm_num [e0, ud], abs_neg,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [h0, h1]
  norm_num

/-- **The iterated bound attained exactly at every time**: the truth
`TV(e₀ ᵥ* Qd^t, ud) = (1/2)^{t+1}` equals the bound
`(1/2)^t · TV(e₀, ud) = (1/2)^t · 1/2` — equality at every `t`,
through the exact closed form. -/
theorem Qd_tv_every_attained_QA (t : ℕ) :
    tvDistance (e0 ᵥ* Qd ^ t) ud
      = (1 - (Fintype.card (Fin 2) : ℝ) * (1/4)) ^ t * tvDistance e0 ud := by
  have hyd0 : yd 0 = 1 := by norm_num [yd]
  have hyd1 : yd 1 = -1 := by norm_num [yd]
  have hL : tvDistance (e0 ᵥ* Qd ^ t) ud = (1/2 : ℝ)^(t+1) := by
    rw [Qd_e0_pow, tvDistance, Fin.sum_univ_two]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
    have h0 : |(1/2 : ℝ)^(t+1) * yd 0| = (1/2 : ℝ)^(t+1) := by
      rw [hyd0, mul_one, abs_of_nonneg (pow_nonneg (by norm_num) _)]
    have h1 : |(1/2 : ℝ)^(t+1) * yd 1| = (1/2 : ℝ)^(t+1) := by
      rw [hyd1, mul_neg_one, abs_neg,
        abs_of_nonneg (pow_nonneg (by norm_num) _)]
    rw [h0, h1]
    ring
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  have hR : (1 - (Fintype.card (Fin 2) : ℝ) * (1/4)) ^ t * tvDistance e0 ud
      = (1/2 : ℝ)^t * (1/2) := by
    rw [hcard, tv_e0_ud, show ((1:ℝ) - 2 * (1/4)) = 1/2 from by norm_num]
  rw [hL, hR, pow_succ]

/-- **The floor-free refutation fence.** The permutation `P₂` is
row-stochastic and the masses match — only the entries-floor
hypothesis fails (`P₂ 0 0 = 0 < 1/4`) — and the contraction conclusion
is refuted at pinned values: `TV(e₀ ᵥ* P₂, e₁ ᵥ* P₂) = 1 > 1/2`. The
`hle` hypothesis is exactly what fails. -/
theorem P2_tv_no_floor_refuted_QA :
    ¬ (tvDistance (e0 ᵥ* P2) (e1 ᵥ* P2)
      ≤ (1 - (Fintype.card (Fin 2) : ℝ) * (1/4)) * tvDistance e0 e1) := by
  have hL : tvDistance (e0 ᵥ* P2) (e1 ᵥ* P2) = 1 := by
    rw [tvDistance, Fin.sum_univ_two]
    have h0 : |(e0 ᵥ* P2) 0 - (e1 ᵥ* P2) 0| = 1 := by
      have hp : (e0 ᵥ* P2) 0 = 0 := by
        norm_num [e0, P2, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two]
      have hq : (e1 ᵥ* P2) 0 = 1 := by
        norm_num [e1, P2, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two]
      rw [hp, hq, show ((0:ℝ) - 1) = -(1:ℝ) from by norm_num, abs_neg, abs_one]
    have h1 : |(e0 ᵥ* P2) 1 - (e1 ᵥ* P2) 1| = 1 := by
      have hp : (e0 ᵥ* P2) 1 = 1 := by
        norm_num [e0, P2, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two]
      have hq : (e1 ᵥ* P2) 1 = 0 := by
        norm_num [e1, P2, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two]
      rw [hp, hq, show ((1:ℝ) - 0) = 1 from by norm_num, abs_one]
    rw [h0, h1]
    norm_num
  have hR : (1 - (Fintype.card (Fin 2) : ℝ) * (1/4)) * tvDistance e0 e1
      = 1/2 := by
    have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
    rw [hcard, tv_e0_e1]
    norm_num
  intro hcon
  rw [hL, hR] at hcon
  norm_num at hcon

/-- **The entries-floor hypothesis provably fails at the permutation
fixture** (the isolation half of the fence). -/
theorem P2_quarter_le_refuted_QA : ¬ ∀ i j, (1/4 : ℝ) ≤ P2 i j := by
  intro hcon
  have h : (1/4 : ℝ) ≤ P2 0 0 := hcon 0 0
  rw [show P2 0 0 = 0 from by norm_num [P2]] at h
  norm_num at h

/-! ### The PageRank rate on the periodic 2-cycle -/

/-- The Google matrix of the edge (the imported `A2` fixture) at
`α = 1/2`, pinned raw: the strictly positive teleportation blend. -/
noncomputable def Gd : Matrix (Fin 2) (Fin 2) ℝ := googleMatrix A2 (1/2)

theorem Gd_apply (i j : Fin 2) : Gd i j = (1/2) * A2 i j + 1/4 := by
  have hd : deg A2 i = 1 := by
    fin_cases i <;> simp [deg, A2, Fin.sum_univ_two]
  rw [Gd, googleMatrix_apply, walkTransitionMatrix_apply, hd, inv_one, one_mul]
  norm_num

theorem Gd_eq : Gd = !![1/4, 3/4; 3/4, 1/4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Gd_apply, A2]

theorem Gd_symm : Gdᵀ = Gd := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gd_eq]

/-- The uniform law is stationary for `Gd` (the column sums are one). -/
theorem u2_stationary_Gd : u2 ᵥ* Gd = u2 := by
  funext j
  fin_cases j <;>
    norm_num [u2, Gd_eq, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two]

/-- The antisymmetric mode under the Google row action: the mode factor
is exactly `-α = -1/2`. -/
theorem Gd_mulVec_yd : Gd *ᵥ yd = (-(1/2 : ℝ)) • yd := by
  funext i
  fin_cases i <;>
    norm_num [Gd_eq, yd, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

theorem yd_vecMul_pow_Gd (t : ℕ) : yd ᵥ* Gd ^ t = (-(1/2 : ℝ))^t • yd := by
  induction t with
  | zero => simp [pow_zero, Matrix.one_mulVec]
  | succ t ih =>
    calc yd ᵥ* Gd ^ (t + 1) = (yd ᵥ* Gd ^ t) ᵥ* Gd := by
          rw [pow_succ, Matrix.vecMul_vecMul]
      _ = ((-(1/2 : ℝ))^t • yd) ᵥ* Gd := by rw [ih]
      _ = (-(1/2 : ℝ))^t • (yd ᵥ* Gd) := Matrix.vecMul_smul _ _ _
      _ = (-(1/2 : ℝ))^t • ((-(1/2 : ℝ)) • yd) := by
          have hyd : yd ᵥ* Gd = Gd *ᵥ yd := by
            rw [← Matrix.mulVec_transpose, Gd_symm]
          rw [hyd, Gd_mulVec_yd]
      _ = (-(1/2 : ℝ))^(t+1) • yd := by
          rw [pow_succ, smul_smul]

theorem e0_eq_u2_add : e0 = u2 + (1/2 : ℝ) • yd := by
  funext i
  fin_cases i <;> norm_num [e0, u2, yd]

/-- **The evolved PageRank law's exact closed form**: the stationary
part plus the alternating, geometrically decaying antisymmetric mode. -/
theorem Gd_e0_pow (t : ℕ) :
    e0 ᵥ* Gd ^ t = u2 + (1/2 : ℝ) • ((-(1/2 : ℝ))^t • yd) := by
  calc e0 ᵥ* Gd ^ t = (u2 + (1/2 : ℝ) • yd) ᵥ* Gd ^ t := by rw [e0_eq_u2_add]
    _ = u2 ᵥ* Gd ^ t + ((1/2 : ℝ) • yd) ᵥ* Gd ^ t := Matrix.add_vecMul _ _ _
    _ = u2 + (1/2 : ℝ) • (yd ᵥ* Gd ^ t) := by
        rw [vecMul_pow_eq_of_vecMul_eq u2_stationary_Gd, Matrix.vecMul_smul]
    _ = u2 + (1/2 : ℝ) • ((-(1/2 : ℝ))^t • yd) := by rw [yd_vecMul_pow_Gd]

theorem tv_e0_u2 : tvDistance e0 u2 = 1/2 := by
  rw [tvDistance, Fin.sum_univ_two]
  have h0 : |e0 0 - u2 0| = 1/2 := by
    rw [show e0 0 - u2 0 = 1/2 by norm_num [e0, u2],
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  have h1 : |e0 1 - u2 1| = 1/2 := by
    rw [show e0 1 - u2 1 = -(1/2) by norm_num [e0, u2], abs_neg,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [h0, h1]
  norm_num

/-- **The PageRank rate attained exactly at every time on the periodic
fixture**: the truth `TV(e₀ ᵥ* Gd^t, u2) = (1/2)^{t+1}` equals the
bound `α^t · TV(e₀, u2) = (1/2)^t · 1/2` at every `t` — the periodic
chain that provably never mixes becomes exactly-`α`-convergent after
teleportation. -/
theorem Gd_tv_every_attained_QA (t : ℕ) :
    tvDistance (e0 ᵥ* Gd ^ t) u2 = (1/2 : ℝ)^t * tvDistance e0 u2 := by
  have hyd0 : yd 0 = 1 := by norm_num [yd]
  have hyd1 : yd 1 = -1 := by norm_num [yd]
  have habshalf : |(1/2 : ℝ)| = 1/2 :=
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  have hL : tvDistance (e0 ᵥ* Gd ^ t) u2 = (1/2 : ℝ) * |(-(1/2 : ℝ))^t| := by
    rw [Gd_e0_pow, tvDistance, Fin.sum_univ_two]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h0 : |(u2 0 + (1/2 : ℝ) * ((-(1/2 : ℝ))^t * yd 0)) - u2 0|
        = (1/2 : ℝ) * |(-(1/2 : ℝ))^t| := by
      have hu2 : u2 0 = 1/2 := by norm_num [u2]
      rw [hu2, hyd0]
      rw [show ((1/2 : ℝ) + (1/2 : ℝ) * ((-(1/2 : ℝ))^t * 1)) - (1/2 : ℝ)
          = (1/2 : ℝ) * (-(1/2 : ℝ))^t from by ring, abs_mul, habshalf]
    have h1 : |(u2 1 + (1/2 : ℝ) * ((-(1/2 : ℝ))^t * yd 1)) - u2 1|
        = (1/2 : ℝ) * |(-(1/2 : ℝ))^t| := by
      have hu2 : u2 1 = 1/2 := by norm_num [u2]
      rw [hu2, hyd1]
      rw [show ((1/2 : ℝ) + (1/2 : ℝ) * ((-(1/2 : ℝ))^t * -1)) - (1/2 : ℝ)
          = -((1/2 : ℝ) * (-(1/2 : ℝ))^t) from by ring, abs_neg, abs_mul,
        habshalf]
    rw [h0, h1]
    ring
  rw [hL, tv_e0_u2, abs_pow, abs_neg, habshalf]
  ring

/-- The theorem instance at the fixture (the rate theorem, not the
value). -/
theorem Gd_rate_instance_QA (t : ℕ) :
    tvDistance (e0 ᵥ* Gd ^ t) u2 ≤ (1/2 : ℝ)^t * tvDistance e0 u2 :=
  pageRank_tvDistance_le A2 A2_nonneg_QA A2_deg_QA (by norm_num) (by norm_num)
    u2_sum u2_stationary_Gd e0_sum t

/-- **The plain-walk contrast**: on the same periodic fixture the raw
walk's TV distance to uniform is `1/2` at *every* time — the
never-decay pin beside the exactly-decaying Google rate, the
periodicity fix in one picture. -/
theorem P2_tv_never_decays_QA (t : ℕ) :
    tvDistance (e0 ᵥ* P2 ^ t) u2 = 1/2 := by
  rcases Nat.even_or_odd t with h | h
  · obtain ⟨k, hk⟩ := h
    rw [hk, show k + k = 2 * k from by omega, P2_pow_even k, Matrix.vecMul_one,
      tv_e0_u2]
  · obtain ⟨k, hk⟩ := h
    rw [hk, P2_pow_odd k, tvDistance, Fin.sum_univ_two]
    have h0 : |(e0 ᵥ* P2) 0 - u2 0| = 1/2 := by
      have hp : (e0 ᵥ* P2) 0 = 0 := by
        norm_num [e0, P2, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two]
      have hu : u2 0 = 1/2 := by norm_num [u2]
      rw [hp, hu, show ((0:ℝ) - 1/2) = -(1/2) from by norm_num, abs_neg,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    have h1 : |(e0 ᵥ* P2) 1 - u2 1| = 1/2 := by
      have hp : (e0 ᵥ* P2) 1 = 1 := by
        norm_num [e0, P2, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two]
      have hu : u2 1 = 1/2 := by norm_num [u2]
      rw [hp, hu, show ((1:ℝ) - 1/2) = 1/2 from by norm_num,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    rw [h0, h1]
    norm_num


/-! ## Section G: the directed mixing time and the PageRank sampling
capstone (`proposals/directed-mixing-time-object.md`)

The `t_mix` object family's directed sibling, pinned against Section
F's exact closed forms on the periodic 2-cycle: the per-start law
join, the object pinned in both directions, the α-ceiling attained
exactly, the depth form attained at the threshold, the entrywise TV
extraction attained, and the junk corner fenced. The empirical
capstone instances live in `Scaffold.QA.Derived.EmpiricalStationary_QA`
(their consumer's own QA module), joining this section's fixture pins.
-/

theorem piSingle_zero_eq_e0 : (Pi.single (0 : Fin 2) (1 : ℝ) : Fin 2 → ℝ) = e0 := by
  funext i
  fin_cases i <;> norm_num [e0, Pi.single_apply]

theorem PR_law_eq_QA (t : ℕ) :
    pageRankDistribution A2 (1/2) t 0 = e0 ᵥ* Gd ^ t := by
  show (Pi.single (0 : Fin 2) (1 : ℝ) : Fin 2 → ℝ) ᵥ* (googleMatrix A2 (1/2) ^ t)
    = e0 ᵥ* Gd ^ t
  rw [piSingle_zero_eq_e0]
  simp [Gd]

theorem PR_tv_eq_QA (t : ℕ) :
    tvDistance (pageRankDistribution A2 (1/2) t 0) u2
      = (1/2 : ℝ) ^ (t + 1) := by
  rw [PR_law_eq_QA, Gd_tv_every_attained_QA, tv_e0_u2, ← pow_succ]

theorem PR_pow_half_le_QA {s T : ℕ} (hT : T ≤ s + 1) :
    (1/2 : ℝ) ^ (s + 1) ≤ (1/2 : ℝ) ^ T := by
  obtain ⟨k, hk⟩ : ∃ k, s + 1 = T + k := ⟨s + 1 - T, by omega⟩
  rw [hk, pow_add]
  calc (1/2 : ℝ) ^ T * (1/2 : ℝ) ^ k ≤ (1/2 : ℝ) ^ T * 1 :=
        mul_le_mul_of_nonneg_left
          (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)
    _ = (1/2 : ℝ) ^ T := mul_one _

theorem PR_tmix_witness_QA :
    ∀ s : ℕ, 2 ≤ s →
      tvDistance (pageRankDistribution A2 (1/2) s 0) u2 ≤ 1/8 := by
  intro s hs
  have h3 : (3 : ℕ) ≤ s + 1 := by omega
  have hp := PR_pow_half_le_QA h3
  rw [PR_tv_eq_QA]
  calc (1/2 : ℝ) ^ (s + 1) ≤ (1/2 : ℝ) ^ 3 := hp
    _ = 1/8 := by norm_num

/-- **The object pinned in both directions** on the periodic fixture:
`t_mix(1/8) = 2` — the witness direction from the exact closed form,
the lower bound from attainment (no time `≤ 1` is a witness, since
`TV_1 = 1/4 > 1/8`). -/
theorem PR_tmix_eighth_QA : pageRankMixingTimeFrom A2 (1/2) u2 0 (1/8) = 2 := by
  refine le_antisymm ?_ ?_
  · exact pageRankMixingTimeFrom_le_of_cert A2 (1/2) u2 0 2 PR_tmix_witness_QA
  · by_contra h
    push_neg at h
    have hwit : ∃ T : ℕ, ∀ s : ℕ, T ≤ s →
        tvDistance (pageRankDistribution A2 (1/2) s 0) u2 ≤ 1/8 :=
      ⟨2, PR_tmix_witness_QA⟩
    have hspec := pageRankMixingTimeFrom_spec A2 (1/2) u2 0 hwit
    have h1 : pageRankMixingTimeFrom A2 (1/2) u2 0 (1/8) ≤ 1 := by omega
    have hcon := hspec 1 h1
    rw [PR_tv_eq_QA] at hcon
    have hev : (1/2 : ℝ) ^ (1 + 1) = 1/4 := by norm_num
    rw [hev] at hcon
    norm_num at hcon

theorem PR_ceiling_arith_QA :
    Nat.ceil (Real.log ((1/2 : ℝ) / (1/8)) / Real.log (1 / (1/2 : ℝ))) = 2 := by
  have hr1 : ((1/2 : ℝ) / (1/8)) = 4 := by norm_num
  have hr2 : (1 : ℝ) / (1/2) = 2 := by norm_num
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow (2 : ℝ) 2]
    push_cast
    ring
  have hlog2ne : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  rw [hr1, hr2, hlog4]
  have hdiv : (2 : ℝ) * Real.log 2 / Real.log 2 = 2 := by field_simp
  rw [hdiv]
  norm_num

/-- **The α-ceiling attained exactly**: the ceiling's right side at the
fixture is `⌈log 4 / log 2⌉ = ⌈2⌉ = 2`, and the object is exactly `2`
— the Doeblin threshold is tight on the fixture where the rate itself
is attained at every time. -/
theorem PR_tmix_ceiling_attained_QA :
    pageRankMixingTimeFrom A2 (1/2) u2 0 (1/8)
      = Nat.ceil (Real.log (tvDistance (Pi.single (0 : Fin 2) (1 : ℝ) : Fin 2 → ℝ) u2
          / (1/8)) / Real.log (1 / (1/2 : ℝ))) := by
  have htv : tvDistance (Pi.single (0 : Fin 2) (1 : ℝ) : Fin 2 → ℝ) u2 = 1/2 := by
    rw [piSingle_zero_eq_e0]; exact tv_e0_u2
  rw [htv, PR_tmix_eighth_QA, PR_ceiling_arith_QA]

/-- **The depth-form instance attained at the boundary**: at the
threshold time `t = 2` the depth form reads `TV_2 ≤ 1/8` — and the
truth is exactly `1/8`. -/
theorem PR_depth_boundary_attained_QA :
    tvDistance (pageRankDistribution A2 (1/2) 2 0) u2 = 1/8 := by
  have h := PR_tv_eq_QA 2
  norm_num at h
  exact h

theorem PR_depth_instance_QA :
    tvDistance (pageRankDistribution A2 (1/2) 2 0) u2 ≤ 1/8 := by
  have hthr : Real.log (tvDistance (Pi.single (0 : Fin 2) (1 : ℝ) : Fin 2 → ℝ) u2
      / (1/8)) / Real.log (1 / (1/2 : ℝ)) ≤ 2 := by
    have htv : tvDistance (Pi.single (0 : Fin 2) (1 : ℝ) : Fin 2 → ℝ) u2 = 1/2 := by
      rw [piSingle_zero_eq_e0]; exact tv_e0_u2
    rw [htv]
    have hr1 : ((1/2 : ℝ) / (1/8)) = 4 := by norm_num
    have hr2 : (1 : ℝ) / (1/2) = 2 := by norm_num
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow (2 : ℝ) 2]
      push_cast
      ring
    have hlog2ne : Real.log 2 ≠ 0 :=
      ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    rw [hr1, hr2, hlog4]
    have hdiv : (2 : ℝ) * Real.log 2 / Real.log 2 = 2 := by field_simp
    rw [hdiv]
  exact pageRank_tvDistance_le_of_depth A2 A2_nonneg_QA A2_deg_QA
    (by norm_num) (by norm_num) u2_sum u2_stationary_Gd (sum_piSingle 0)
    (by norm_num) 2 hthr

/-- **The entrywise extraction attained** at `t = 1`, coordinate `0`:
both the deviation `|(e0 ᵥ* G) 0 − u2 0| = |3/4 − 1/2| = 1/4` and the
TV distance `(1/2)^2 = 1/4` pin to the same value — the sharp constant
load-bearing (a factor-`2` statement would read `1/4 ≤ 1/2`, slack). -/
theorem PR_entrywise_both_QA :
    |pageRankDistribution A2 (1/2) 1 0 0 - u2 0| = 1/4
      ∧ tvDistance (pageRankDistribution A2 (1/2) 1 0) u2 = 1/4 := by
  have hlaw : pageRankDistribution A2 (1/2) 1 0 = e0 ᵥ* Gd :=
    (PR_law_eq_QA 1).trans (by rw [pow_one])
  have hentry : (e0 ᵥ* Gd) 0 = 1/4 := by
    have h := congrFun (Gd_e0_pow 1) 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_one] at h
    rw [h]
    norm_num [u2, yd]
  constructor
  · rw [hlaw, hentry]
    have hu2 : u2 0 = 1/2 := by norm_num [u2]
    rw [hu2]
    norm_num
  · have h := PR_tv_eq_QA 1
    norm_num at h
    exact h

theorem PR_entrywise_instance_QA :
    |pageRankDistribution A2 (1/2) 1 0 0 - u2 0|
      ≤ tvDistance (pageRankDistribution A2 (1/2) 1 0) u2 := by
  obtain ⟨h1, h2⟩ := PR_entrywise_both_QA
  rw [h1, h2]

/-- **The junk corner fenced**: at `ε = 0` the witness set is empty
(every TV is strictly positive), so `sInf ∅ = 0` — the object's
documented degeneracy, pinned. -/
theorem PR_tmix_zero_junk_QA : pageRankMixingTimeFrom A2 (1/2) u2 0 0 = 0 := by
  have hempty : {t : ℕ | ∀ s : ℕ, t ≤ s →
      tvDistance (pageRankDistribution A2 (1/2) s 0) u2 ≤ 0} = ∅ := by
    refine Set.eq_empty_iff_forall_not_mem.mpr ?_
    intro t ht
    have hpos : 0 < tvDistance (pageRankDistribution A2 (1/2) t 0) u2 := by
      rw [PR_tv_eq_QA]
      positivity
    exact absurd (ht t (le_refl t)) (not_le.mpr hpos)
  rw [pageRankMixingTimeFrom, hempty, Nat.sInf_empty]


theorem piSingle_one_eq_e1 : (Pi.single (1 : Fin 2) (1 : ℝ) : Fin 2 → ℝ) = e1 := by
  funext i
  fin_cases i <;> norm_num [e1, Pi.single_apply]

theorem PR_law_eq_e1_QA (t : ℕ) :
    pageRankDistribution A2 (1/2) t 1 = e1 ᵥ* Gd ^ t := by
  show (Pi.single (1 : Fin 2) (1 : ℝ) : Fin 2 → ℝ) ᵥ* (googleMatrix A2 (1/2) ^ t)
    = e1 ᵥ* Gd ^ t
  rw [piSingle_one_eq_e1]
  simp [Gd]

theorem e1_eq_u2_sub : e1 = u2 - (1/2 : ℝ) • yd := by
  funext i
  fin_cases i <;> norm_num [e1, u2, yd]

theorem smul_vecMul_eq {c : ℝ} (v : Fin 2 → ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (c • v) ᵥ* M = c • (v ᵥ* M) := by
  funext j
  simp only [Matrix.vecMul, Matrix.dotProduct, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem Gd_e1_pow (t : ℕ) :
    e1 ᵥ* Gd ^ t = u2 - (1/2 : ℝ) • ((-(1/2 : ℝ))^t • yd) := by
  have hu2 : u2 ᵥ* Gd ^ t = u2 :=
    Scaffold.LinearAlgebra.vecMul_pow_eq_of_vecMul_eq u2_stationary_Gd t
  rw [e1_eq_u2_sub, Matrix.sub_vecMul, smul_vecMul_eq, yd_vecMul_pow_Gd, hu2,
    smul_smul]

theorem PR_tv_eq_one_QA (t : ℕ) :
    tvDistance (pageRankDistribution A2 (1/2) t 1) u2 = (1/2 : ℝ) ^ (t + 1) := by
  have hyd0 : yd 0 = 1 := by norm_num [yd]
  have hyd1 : yd 1 = -1 := by norm_num [yd]
  have habshalf : |(1/2 : ℝ)| = 1/2 :=
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  rw [PR_law_eq_e1_QA, Gd_e1_pow, tvDistance, Fin.sum_univ_two]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have h0 : |(u2 0 - (1/2 : ℝ) * ((-(1/2 : ℝ))^t * yd 0)) - u2 0|
      = (1/2 : ℝ) * |(-(1/2 : ℝ))^t| := by
    have hu2 : u2 0 = 1/2 := by norm_num [u2]
    rw [hu2, hyd0]
    rw [show ((1/2 : ℝ) - (1/2 : ℝ) * ((-(1/2 : ℝ))^t * 1)) - (1/2 : ℝ)
        = -((1/2 : ℝ) * (-(1/2 : ℝ))^t) from by ring, abs_neg, abs_mul,
      habshalf]
  have h1 : |(u2 1 - (1/2 : ℝ) * ((-(1/2 : ℝ))^t * yd 1)) - u2 1|
      = (1/2 : ℝ) * |(-(1/2 : ℝ))^t| := by
    have hu2 : u2 1 = 1/2 := by norm_num [u2]
    rw [hu2, hyd1]
    rw [show ((1/2 : ℝ) - (1/2 : ℝ) * ((-(1/2 : ℝ))^t * -1)) - (1/2 : ℝ)
        = (1/2 : ℝ) * (-(1/2 : ℝ))^t from by ring, abs_mul, habshalf]
  rw [h0, h1, abs_pow, abs_neg, habshalf]
  ring

theorem tv_self_eq_zero (μ : Fin 2 → ℝ) : tvDistance μ μ = 0 := by
  simp [tvDistance]

/-- **The off-diagonal exact value**: the two starts' surfer laws at
time `t` are `u2 ± (1/2)(−1/2)^t • yd`, so their TV distance is
exactly `(1/2)^t`. -/
theorem PRU_pair_zero_one_QA (t : ℕ) :
    tvDistance (pageRankDistribution A2 (1/2) t 0)
        (pageRankDistribution A2 (1/2) t 1) = (1/2 : ℝ) ^ t := by
  have hyd0 : yd 0 = 1 := by norm_num [yd]
  have hyd1 : yd 1 = -1 := by norm_num [yd]
  have habshalf : |(1/2 : ℝ)| = 1/2 :=
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  rw [PR_law_eq_QA, PR_law_eq_e1_QA, Gd_e0_pow, Gd_e1_pow, tvDistance,
    Fin.sum_univ_two]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have h0 : (u2 0 + (1/2 : ℝ) * ((-(1/2 : ℝ))^t * yd 0))
        - (u2 0 - (1/2 : ℝ) * ((-(1/2 : ℝ))^t * yd 0))
      = (-(1/2 : ℝ))^t := by
    rw [hyd0]
    ring
  have h1 : (u2 1 + (1/2 : ℝ) * ((-(1/2 : ℝ))^t * yd 1))
        - (u2 1 - (1/2 : ℝ) * ((-(1/2 : ℝ))^t * yd 1))
      = -((-(1/2 : ℝ))^t) := by
    rw [hyd1]
    ring
  rw [h0, h1, abs_neg, abs_pow, abs_neg, habshalf]
  ring

theorem PRU_pair_tv_le_QA (t : ℕ) : ∀ a b : Fin 2,
    tvDistance (pageRankDistribution A2 (1/2) t a)
        (pageRankDistribution A2 (1/2) t b) ≤ (1/2 : ℝ) ^ t := by
  intro a b
  rcases (show a = 0 ∨ a = 1 by omega) with ha | ha <;> rw [ha]
  all_goals rcases (show b = 0 ∨ b = 1 by omega) with hb | hb <;> rw [hb]
  · exact le_trans (le_of_eq (tv_self_eq_zero _))
        (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) t)
  · exact le_of_eq (PRU_pair_zero_one_QA t)
  · rw [tvDistance_symm]
    exact le_of_eq (PRU_pair_zero_one_QA t)
  · exact le_trans (le_of_eq (tv_self_eq_zero _))
        (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) t)

/-- **The exact closed form `d(t) = (1/2)^t`** — LPW's two-start
distance on the periodic fixture, pinned from the raw law literals:
submultiplicativity will be attained with *equality at every time*. -/
theorem PRU_pair_closed_QA (t : ℕ) :
    pageRankTVPair A2 (1/2) t = (1/2 : ℝ) ^ t := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le
      (⟨(0, 1), Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin 2 × Fin 2)).Nonempty)
      (f := fun p : Fin 2 × Fin 2 =>
        tvDistance (pageRankDistribution A2 (1/2) t p.1)
          (pageRankDistribution A2 (1/2) t p.2))
      fun p _ => PRU_pair_tv_le_QA t p.1 p.2
  · have h0 : (1/2 : ℝ) ^ t = tvDistance (pageRankDistribution A2 (1/2) t 0)
          (pageRankDistribution A2 (1/2) t 1) := (PRU_pair_zero_one_QA t).symm
    rw [h0]
    exact Finset.le_sup'
      (f := fun p : Fin 2 × Fin 2 =>
        tvDistance (pageRankDistribution A2 (1/2) t p.1)
          (pageRankDistribution A2 (1/2) t p.2))
      (Finset.mem_univ (0, 1))

/-- **Submultiplicativity attained with equality at every time** —
`d(s+t) = d(s) · d(t)` on the fixture (`(1/2)^(s+t) = (1/2)^s (1/2)^t`):
the strongest QA shape a submultiplicative bound can have, load-bearing
on the exact statement of the mixed class. -/
theorem PRU_pair_submul_attained_QA (s t : ℕ) :
    pageRankTVPair A2 (1/2) (s + t)
      = pageRankTVPair A2 (1/2) s * pageRankTVPair A2 (1/2) t := by
  rw [PRU_pair_closed_QA, PRU_pair_closed_QA, PRU_pair_closed_QA, pow_add]

theorem Gd_vecMul_e0 : e0 ᵥ* Gd = ![1/4, 3/4] := by
  rw [Gd_eq]
  funext i
  fin_cases i <;> norm_num [e0, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two]

theorem Gd_vecMul_e1 : e1 ᵥ* Gd = ![3/4, 1/4] := by
  rw [Gd_eq]
  funext i
  fin_cases i <;> norm_num [e1, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two]

/-- **The Dobrushin contraction attained exactly** at the basis pair on
one Google step: `TV(e0 ᵥ* G, e1 ᵥ* G) = 1/2 = TV(e0, e1) · d(1)` —
both sides independently pinned, the matrix-level engine's sharp
constant load-bearing on the directed axis. -/
theorem PRU_contraction_attained_QA :
    tvDistance (e0 ᵥ* Gd) (e1 ᵥ* Gd)
      = tvDistance e0 e1 * tvDobrushinCoeff Gd := by
  have hjoin : tvDobrushinCoeff Gd = pageRankTVPair A2 (1/2) 1 := by
    rw [show Gd = googleMatrix A2 (1/2) ^ 1 from by rw [Gd, pow_one],
      ← pageRankTVPair_eq_tvDobrushinCoeff A2 (1/2) 1]
  have hpair : pageRankTVPair A2 (1/2) 1 = 1/2 := by
    rw [PRU_pair_closed_QA, pow_one]
  rw [hjoin, hpair, tv_e0_e1, Gd_vecMul_e0, Gd_vecMul_e1, tvDistance,
    Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    neg_sub, abs_of_neg, abs_of_nonneg]

theorem PRU_uniform_tv_le_QA (t : ℕ) : ∀ a : Fin 2,
    tvDistance (pageRankDistribution A2 (1/2) t a) u2 ≤ (1/2 : ℝ) ^ (t + 1) := by
  intro a
  rcases (show a = 0 ∨ a = 1 by omega) with ha | ha <;> rw [ha]
  · exact le_of_eq (PR_tv_eq_QA t)
  · exact le_of_eq (PR_tv_eq_one_QA t)

/-- **The exact closed form `d̄(t) = (1/2)^(t+1)`** — the worst-start
distance on the fixture (both starts pin to the same value). -/
theorem PRU_uniform_closed_QA (t : ℕ) :
    pageRankTVUniform A2 (1/2) u2 t = (1/2 : ℝ) ^ (t + 1) := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le
      (⟨0, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin 2)).Nonempty)
      (f := fun x => tvDistance (pageRankDistribution A2 (1/2) t x) u2)
      fun x _ => PRU_uniform_tv_le_QA t x
  · have h0 : (1/2 : ℝ) ^ (t + 1)
        = tvDistance (pageRankDistribution A2 (1/2) t 0) u2 :=
      (PR_tv_eq_QA t).symm
    rw [h0]
    exact Finset.le_sup'
      (f := fun x => tvDistance (pageRankDistribution A2 (1/2) t x) u2)
      (Finset.mem_univ 0)

/-- **`d̄ = d/2` on the fixture, with the domination theorem instance
beside it** — the classical `d̄(t) ≤ d(t)` pinned as an exact factor-`2`
gap (the stationary target halves the two-start distance), and the
delivered domination theorem instantiated beside it (strict, since the
exact factor is `1/2`). -/
theorem PRU_uniform_le_pair_QA (t : ℕ) :
    pageRankTVUniform A2 (1/2) u2 t ≤ pageRankTVPair A2 (1/2) t
      ∧ pageRankTVUniform A2 (1/2) u2 t = (1/2) * pageRankTVPair A2 (1/2) t := by
  exact ⟨pageRankTVUniform_le_pageRankTVPair A2 (1/2) u2_nonneg u2_sum
    u2_stationary_Gd t,
    by rw [PRU_uniform_closed_QA, PRU_pair_closed_QA, ← pow_succ']⟩

/-- **The mixed submultiplicativity attained with equality at every
time** — `d̄(s+t) = d̄(s) · d(t)` on the fixture. -/
theorem PRU_uniform_submul_attained_QA (s t : ℕ) :
    pageRankTVUniform A2 (1/2) u2 (s + t)
      = pageRankTVUniform A2 (1/2) u2 s * pageRankTVPair A2 (1/2) t := by
  rw [PRU_uniform_closed_QA, PRU_uniform_closed_QA, PRU_pair_closed_QA,
    pow_add, pow_add]
  ring

theorem PR_tmix_one_witness_QA :
    ∀ s : ℕ, 2 ≤ s →
      tvDistance (pageRankDistribution A2 (1/2) s 1) u2 ≤ 1/8 := by
  intro s hs
  have h3 : (3 : ℕ) ≤ s + 1 := by omega
  have hp := PR_pow_half_le_QA h3
  rw [PR_tv_eq_one_QA]
  calc (1/2 : ℝ) ^ (s + 1) ≤ (1/2 : ℝ) ^ 3 := hp
    _ = 1/8 := by norm_num

/-- The start-`1` twin of the pinned object: `t_mix(1/8) = 2` from
either start on the symmetric fixture. -/
theorem PR_tmix_one_eighth_QA : pageRankMixingTimeFrom A2 (1/2) u2 1 (1/8) = 2 := by
  refine le_antisymm ?_ ?_
  · exact pageRankMixingTimeFrom_le_of_cert A2 (1/2) u2 1 2 PR_tmix_one_witness_QA
  · by_contra h
    push_neg at h
    have hwit : ∃ T : ℕ, ∀ s : ℕ, T ≤ s →
        tvDistance (pageRankDistribution A2 (1/2) s 1) u2 ≤ 1/8 :=
      ⟨2, PR_tmix_one_witness_QA⟩
    have hspec := pageRankMixingTimeFrom_spec A2 (1/2) u2 1 hwit
    have h1 : pageRankMixingTimeFrom A2 (1/2) u2 1 (1/8) ≤ 1 := by omega
    have hcon := hspec 1 h1
    rw [PR_tv_eq_one_QA] at hcon
    have hev : (1/2 : ℝ) ^ (1 + 1) = 1/4 := by norm_num
    rw [hev] at hcon
    norm_num at hcon

/-- **The uniform object pinned in both directions** on the periodic
fixture: `t_mix^unif(1/8) = 2` — the worst start's per-start object
(the sup interchange), both starts pinned `2` independently. -/
theorem PRU_tmix_eighth_QA : pageRankMixingTime A2 (1/2) u2 (1/8) = 2 := by
  rw [pageRankMixingTime_eq_sup_pageRankMixingTimeFrom A2 (1/2) u2
    ⟨2, fun s hs x => by
      rcases (show x = 0 ∨ x = 1 by omega) with hx | hx <;> rw [hx]
      · exact PR_tmix_witness_QA s hs
      · exact PR_tmix_one_witness_QA s hs⟩]
  have hle : (Finset.univ : Finset (Fin 2)).sup'
      (⟨0, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin 2)).Nonempty)
      (fun x => pageRankMixingTimeFrom A2 (1/2) u2 x (1/8)) ≤ 2 := by
    refine Finset.sup'_le
      (⟨0, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin 2)).Nonempty)
      (f := fun x => pageRankMixingTimeFrom A2 (1/2) u2 x (1/8))
      fun x _ => ?_
    rcases (show x = 0 ∨ x = 1 by omega) with hx | hx
    · subst hx
      show pageRankMixingTimeFrom A2 (1/2) u2 0 (1/8) ≤ 2
      rw [PR_tmix_eighth_QA]
    · subst hx
      show pageRankMixingTimeFrom A2 (1/2) u2 1 (1/8) ≤ 2
      rw [PR_tmix_one_eighth_QA]
  have hge : (2 : ℕ) ≤ (Finset.univ : Finset (Fin 2)).sup'
      (⟨0, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin 2)).Nonempty)
      (fun x => pageRankMixingTimeFrom A2 (1/2) u2 x (1/8)) := by
    have h0 : (2 : ℕ) ≤ pageRankMixingTimeFrom A2 (1/2) u2 0 (1/8) := by
      rw [PR_tmix_eighth_QA]
    exact le_trans h0
      (Finset.le_sup'
        (f := fun x => pageRankMixingTimeFrom A2 (1/2) u2 x (1/8))
        (Finset.mem_univ 0))
  exact le_antisymm hle hge

/-- **The refined α-ceiling attained exactly**: the ceiling's right side
at the fixture is `⌈log (d̄(0)/ε) / log (1/α)⌉ = ⌈log 4 / log 2⌉ = 2`,
and the uniform object is exactly `2` — the worst-start constant
`d̄(0) = 1/2` keeps the per-start ceiling's tightness. -/
theorem PRU_tmix_ceiling_attained_QA :
    pageRankMixingTime A2 (1/2) u2 (1/8)
      = Nat.ceil (Real.log (pageRankTVUniform A2 (1/2) u2 0 / (1/8))
          / Real.log (1 / (1/2 : ℝ))) := by
  have hd0 : pageRankTVUniform A2 (1/2) u2 0 = 1/2 := by
    have h := PRU_uniform_closed_QA 0
    norm_num at h
    exact h
  rw [hd0, PRU_tmix_eighth_QA, PR_ceiling_arith_QA]

theorem PRU_display_ceiling_arith_QA :
    Nat.ceil (Real.log (1 / (1/8 : ℝ)) / Real.log (1 / (1/2 : ℝ))) = 3 := by
  have hr1 : (1 : ℝ) / (1/8 : ℝ) = 8 := by norm_num
  have hr2 : (1 : ℝ) / (1/2 : ℝ) = 2 := by norm_num
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, Real.log_pow (2 : ℝ) 3]
    push_cast
    ring
  have hlog2ne : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  rw [hr1, hr2, hlog8]
  have hdiv : (3 : ℝ) * Real.log 2 / Real.log 2 = 3 := by field_simp
  rw [hdiv]
  norm_num

/-- **The display-form ceiling with slack witnessed**: the start-free
bound `⌈log 8 / log 2⌉ = 3` against the object's `2` — the simplex
diameter `d̄(0) ≤ 1` costs exactly the factor the refined form saves on
this fixture. -/
theorem PRU_tmix_display_ceiling_QA :
    pageRankMixingTime A2 (1/2) u2 (1/8)
      < Nat.ceil (Real.log (1 / (1/8 : ℝ)) / Real.log (1 / (1/2 : ℝ))) := by
  have h := pageRankMixingTime_le_of_rate' A2 A2_nonneg_QA A2_deg_QA
    (by norm_num) (by norm_num) u2_nonneg u2_sum u2_stationary_Gd
    (by norm_num : (0 : ℝ) < 1/8)
  rw [PRU_tmix_eighth_QA, PRU_display_ceiling_arith_QA] at h ⊢
  omega

theorem PR_tmix_thirtysecond_witness_QA :
    ∀ s : ℕ, 4 ≤ s → ∀ x : Fin 2,
      tvDistance (pageRankDistribution A2 (1/2) s x) u2 ≤ 1/32 := by
  intro s hs x
  have h5 : (5 : ℕ) ≤ s + 1 := by omega
  have hp := PR_pow_half_le_QA h5
  rcases (show x = 0 ∨ x = 1 by omega) with hx | hx <;> rw [hx]
  · rw [PR_tv_eq_QA]
    calc (1/2 : ℝ) ^ (s + 1) ≤ (1/2 : ℝ) ^ 5 := hp
      _ = 1/32 := by norm_num
  · rw [PR_tv_eq_one_QA]
    calc (1/2 : ℝ) ^ (s + 1) ≤ (1/2 : ℝ) ^ 5 := hp
      _ = 1/32 := by norm_num

/-- **The uniform object at a second threshold, pinned in both
directions**: `t_mix^unif(1/32) = 4` — the escalation corollary's
truth value. -/
theorem PRU_tmix_thirtysecond_QA : pageRankMixingTime A2 (1/2) u2 (1/32) = 4 := by
  refine le_antisymm ?_ ?_
  · exact pageRankMixingTime_le_of_cert A2 (1/2) u2 4
      PR_tmix_thirtysecond_witness_QA
  · by_contra h
    push_neg at h
    have hwit : ∃ T : ℕ, ∀ s : ℕ, T ≤ s → ∀ x : Fin 2,
        tvDistance (pageRankDistribution A2 (1/2) s x) u2 ≤ 1/32 :=
      ⟨4, PR_tmix_thirtysecond_witness_QA⟩
    have hspec := pageRankMixingTime_spec A2 (1/2) u2 hwit
    have h3 : pageRankMixingTime A2 (1/2) u2 (1/32) ≤ 3 := by omega
    have hcon := hspec 3 h3 0
    rw [PR_tv_eq_QA] at hcon
    have hev : (1/2 : ℝ) ^ (3 + 1) = 1/16 := by norm_num
    rw [hev] at hcon
    norm_num at hcon

/-- **The escalation corollary attained exactly**: with one certified
evaluation `t₀ = 2` (`d̄(2) = 1/8`, `d(2) = 1/4 = ρ`), the corollary
reads `t_mix(1/32) ≤ (1 + 1) · 2 = 4` — and the truth is exactly `4`.
The certificate constants are the fixture's own pinned distances, not
hand-supplied numbers. -/
theorem PRU_escalation_attained_QA :
    pageRankMixingTime A2 (1/2) u2 (1/32) = 4
      ∧ pageRankMixingTime A2 (1/2) u2 (1/32) ≤ (1 + 1) * 2 := by
  refine ⟨PRU_tmix_thirtysecond_QA, ?_⟩
  have hunif : pageRankTVUniform A2 (1/2) u2 2 ≤ 1/8 := by
    have h := PRU_uniform_closed_QA 2
    norm_num at h
    exact le_of_eq h
  have hpair : pageRankTVPair A2 (1/2) 2 ≤ 1/4 := by
    have h := PRU_pair_closed_QA 2
    norm_num at h
    exact le_of_eq h
  exact pageRankMixingTime_le_mul_of_escalation A2 A2_nonneg_QA
    A2_deg_QA (by norm_num) (by norm_num) u2_sum u2_stationary_Gd 2 1
    hunif hpair (by norm_num)

/-- **The `ε = 0` junk corner fenced**: at an unreachable threshold
the witness set is empty and the uniform object reads the `sInf ∅ = 0`
junk value (TV is strictly positive at every time here), mirroring the
per-start fence. -/
theorem PRU_tmix_zero_junk_QA : pageRankMixingTime A2 (1/2) u2 0 = 0 := by
  have hempty : {t : ℕ | ∀ s : ℕ, t ≤ s → ∀ x : Fin 2,
      tvDistance (pageRankDistribution A2 (1/2) s x) u2 ≤ 0} = ∅ := by
    by_contra hne
    obtain ⟨t, ht⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hcon := ht t (Nat.le_refl t) 0
    rw [PR_tv_eq_QA] at hcon
    have hpos : (0 : ℝ) < (1/2 : ℝ) ^ (t + 1) := by positivity
    linarith
  unfold pageRankMixingTime
  rw [hempty]
  exact Nat.sInf_empty

/-! ## Section I: the adversarial fence completion for the TV/Dobrushin
engines (`proposals/adversarial-fences-tv-dobrushin-engines.md`,
2026-09-02)

The 2026-09-02 directed-rate deliveries added `Mixing.lean`'s Doeblin
TV-contraction and Dobrushin-coefficient sections but fenced only the
entries-floor clause (Section F) and the junk corners (Section G/H).
This section is the adversarial re-read's completion of the fence
discipline: a negative witness for every remaining load-bearing
hypothesis of the family, each with an isolation companion proving the
refuted clause is exactly what fails at the fixture (the other
hypotheses verified genuine). The refuting fixtures are new because the
existing ones cannot kill these clauses: `Qd`/`Gd` are strictly positive
with distinct rows (their contractions are the *attainment* pins), and
`P2` kills the floor clause but is a genuine permutation (row sums one,
mass-compatible — the mass-dropped conclusions still hold there). -/

/-- The mass-`2` start: the equal-mass clauses' refuting vector. -/
noncomputable def twoE0 : Fin 2 → ℝ := ![2, 0]

/-- The all-half matrix: row-stochastic, strictly positive, identical
rows — so its Dobrushin coefficient is exactly `0`. -/
noncomputable def Qh : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 1/2; 1/2, 1/2]

/-- The doubled identity: nonnegative, row sums `2` (row stochasticity
fails). -/
noncomputable def Mx : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 2]

/-- The signed stochastic fixture: row sums `1`, negative off-diagonal
(nonnegativity fails). -/
noncomputable def Mn : Matrix (Fin 2) (Fin 2) ℝ := !![2, -1; -1, 2]

/-- The submultiplicativity refuter: row sums `2` and `0`, square
`2·I`. -/
noncomputable def Qx : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]

theorem Qh_apply (i j : Fin 2) : Qh i j = 1/2 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem Qh_row_sum (i : Fin 2) : ∑ j, Qh i j = 1 := by
  fin_cases i <;> norm_num [Qh, Fin.sum_univ_two]

theorem Qh_half_le : ∀ i j, (1/2 : ℝ) ≤ Qh i j := fun i j => by rw [Qh_apply]

theorem Mx_row_zero : Mx 0 = ![2, 0] := by funext j; fin_cases j <;> rfl

theorem Mx_row_one : Mx 1 = ![0, 2] := by funext j; fin_cases j <;> rfl

theorem Mx_nonneg : ∀ i j, 0 ≤ Mx i j := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [Mx]

theorem Mn_row_sum (i : Fin 2) : ∑ j, Mn i j = 1 := by
  fin_cases i <;> norm_num [Mn, Fin.sum_univ_two]

theorem Mn_zero_one : Mn 0 1 = -1 := by rfl

theorem Qx_row_zero : Qx 0 = ![1, 1] := by funext j; fin_cases j <;> rfl

theorem Qx_row_one : Qx 1 = ![1, -1] := by funext j; fin_cases j <;> rfl

theorem Qx_sq : Qx ^ 2 = Mx := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Qx, Mx, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- TV of two explicit two-point vectors, the section's computation
interface. -/
theorem tv_lit (a b c d : ℝ) :
    tvDistance (![a, b] : Fin 2 → ℝ) (![c, d] : Fin 2 → ℝ)
      = (|a - c| + |b - d|) / 2 := by
  rw [tvDistance, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-! ### The evolved vectors, pinned raw -/

theorem twoE0_vecMul_Qh : twoE0 ᵥ* Qh = ![1, 1] := by
  funext j
  fin_cases j <;>
    norm_num [twoE0, Qh, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem e0_vecMul_Qh : e0 ᵥ* Qh = ![1/2, 1/2] := by
  funext j
  fin_cases j <;>
    norm_num [e0, Qh, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem e0_vecMul_Mx : e0 ᵥ* Mx = ![2, 0] := by
  funext j
  fin_cases j <;>
    norm_num [e0, Mx, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem e1_vecMul_Mx : e1 ᵥ* Mx = ![0, 2] := by
  funext j
  fin_cases j <;>
    norm_num [e1, Mx, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem e0_vecMul_Mn : e0 ᵥ* Mn = ![2, -1] := by
  funext j
  fin_cases j <;>
    norm_num [e0, Mn, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem e1_vecMul_Mn : e1 ᵥ* Mn = ![-1, 2] := by
  funext j
  fin_cases j <;>
    norm_num [e1, Mn, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-! ### The scalar values, pinned raw -/

theorem tv_twoE0_e0 : tvDistance twoE0 e0 = 1/2 := by
  rw [show twoE0 = ![2, 0] from rfl, show e0 = ![1, 0] from rfl, tv_lit]; norm_num

theorem tv_twoE0Qh_e0Qh :
    tvDistance (twoE0 ᵥ* Qh) (e0 ᵥ* Qh) = 1/2 := by
  rw [twoE0_vecMul_Qh, e0_vecMul_Qh, tv_lit]; norm_num

theorem tv_e0Mx_e1Mx : tvDistance (e0 ᵥ* Mx) (e1 ᵥ* Mx) = 2 := by
  rw [e0_vecMul_Mx, e1_vecMul_Mx, tv_lit]; norm_num

theorem tv_e0Mn_e1Mn : tvDistance (e0 ᵥ* Mn) (e1 ᵥ* Mn) = 3 := by
  rw [e0_vecMul_Mn, e1_vecMul_Mn, tv_lit]; norm_num

/-! ### The Dobrushin coefficients of the fixtures -/

theorem Qh_pair_zero : ∀ p : Fin 2 × Fin 2,
    tvDistance (Qh p.1) (Qh p.2) = 0 := by
  rintro ⟨a, b⟩
  have h : Qh a = Qh b := by funext j; rw [Qh_apply, Qh_apply]
  rw [h, tv_self_eq_zero]

theorem Qh_dobrushin : tvDobrushinCoeff Qh = 0 := by
  refine le_antisymm ?_ (tvDobrushinCoeff_nonneg Qh)
  refine Finset.sup'_le
    (⟨(0, 0), Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin 2 × Fin 2)).Nonempty)
    (f := fun p : Fin 2 × Fin 2 => tvDistance (Qh p.1) (Qh p.2))
    fun p _ => (Qh_pair_zero p).le

theorem tv_Mx_01 : tvDistance (Mx 0) (Mx 1) = 2 := by
  rw [Mx_row_zero, Mx_row_one, tv_lit]; norm_num

theorem Mx_pair_le : ∀ p : Fin 2 × Fin 2,
    tvDistance (Mx p.1) (Mx p.2) ≤ 2 := by
  rintro ⟨a, b⟩
  simp only []
  rcases (show a = 0 ∨ a = 1 by omega) with ha | ha <;> rw [ha]
  all_goals rcases (show b = 0 ∨ b = 1 by omega) with hb | hb <;> rw [hb]
  · rw [tv_self_eq_zero]; norm_num
  · rw [Mx_row_zero, Mx_row_one, tv_lit]; norm_num
  · rw [tvDistance_symm, Mx_row_zero, Mx_row_one, tv_lit]; norm_num
  · rw [tv_self_eq_zero]; norm_num

theorem Mx_dobrushin : tvDobrushinCoeff Mx = 2 := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le
      (⟨(0, 0), Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin 2 × Fin 2)).Nonempty)
      (f := fun p : Fin 2 × Fin 2 => tvDistance (Mx p.1) (Mx p.2))
      fun p _ => Mx_pair_le p
  · have hle : tvDistance (Mx 0) (Mx 1) ≤ tvDobrushinCoeff Mx :=
      Finset.le_sup'
        (f := fun p : Fin 2 × Fin 2 => tvDistance (Mx p.1) (Mx p.2))
        (Finset.mem_univ (0, 1))
    exact tv_Mx_01.symm.le.trans hle

theorem tv_Qx_01 : tvDistance (Qx 0) (Qx 1) = 1 := by
  rw [Qx_row_zero, Qx_row_one, tv_lit]; norm_num

theorem Qx_pair_le : ∀ p : Fin 2 × Fin 2,
    tvDistance (Qx p.1) (Qx p.2) ≤ 1 := by
  rintro ⟨a, b⟩
  simp only []
  rcases (show a = 0 ∨ a = 1 by omega) with ha | ha <;> rw [ha]
  all_goals rcases (show b = 0 ∨ b = 1 by omega) with hb | hb <;> rw [hb]
  · rw [tv_self_eq_zero]; norm_num
  · rw [Qx_row_zero, Qx_row_one, tv_lit]; norm_num
  · rw [tvDistance_symm, Qx_row_zero, Qx_row_one, tv_lit]; norm_num
  · rw [tv_self_eq_zero]; norm_num

theorem Qx_dobrushin : tvDobrushinCoeff Qx = 1 := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le
      (⟨(0, 0), Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin 2 × Fin 2)).Nonempty)
      (f := fun p : Fin 2 × Fin 2 => tvDistance (Qx p.1) (Qx p.2))
      fun p _ => Qx_pair_le p
  · have hle : tvDistance (Qx 0) (Qx 1) ≤ tvDobrushinCoeff Qx :=
      Finset.le_sup'
        (f := fun p : Fin 2 × Fin 2 => tvDistance (Qx p.1) (Qx p.2))
        (Finset.mem_univ (0, 1))
    exact tv_Qx_01.symm.le.trans hle

/-! ### The scalar values of the pairing-core fixtures -/

theorem dot_e0_e0 : e0 ⬝ᵥ e0 = 1 := by
  norm_num [e0, Matrix.dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem sum_abs_e0 : ∑ i, |e0 i| = 1 := by
  norm_num [e0, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

theorem sum_mul_e0_e0 : ∑ z : Fin 2, e0 z * e0 z = 1 := by
  norm_num [e0, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

theorem sum_e0 : ∑ i, e0 i = 1 := by
  norm_num [e0, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

theorem sum_twoE0 : ∑ i, twoE0 i = 2 := by
  norm_num [twoE0, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

theorem entryRange_e0 : entryRange e0 = 1 := by
  have hs : entrySup e0 = 1 := by
    refine le_antisymm ?_ (le_entrySup e0 0)
    refine Finset.sup'_le (Finset.univ_nonempty)
      (f := fun i => e0 i) fun i _ => ?_
    fin_cases i <;> simp [e0]
  have hi : entryInf e0 = 0 := by
    refine le_antisymm (entryInf_le e0 1) ?_
    refine Finset.le_inf' (Finset.univ_nonempty)
      (f := fun i => e0 i) fun i _ => ?_
    fin_cases i <;> simp [e0]
  rw [entryRange, hs, hi]; norm_num

theorem hD_e0 : ∀ z z' : Fin 2, |e0 z - e0 z'| ≤ 1 := by
  intro z z'
  fin_cases z <;> fin_cases z' <;> simp [e0]

/-! ### The seven fences -/

/-- **Fence 1: the equal-mass clause of the Doeblin TV contraction is
load-bearing.** At the all-half matrix `Qh` (row-stochastic, every entry
`≥ 1/2`) with the mass-`2` start `twoE0 = 2•e₀` against the mass-`1`
start `e₀`, the un-guarded conclusion reads `1/2 ≤ 0` — the coefficient
`1 - |V|·(1/2) = 0` collapses the bound while the evolved TV stays
`1/2`. -/
theorem fence_doeblin_tv_mass_refuted_QA :
    ¬ (tvDistance (twoE0 ᵥ* Qh) (e0 ᵥ* Qh)
      ≤ (1 - (Fintype.card (Fin 2) : ℝ) * (1/2)) * tvDistance twoE0 e0) := by
  intro hcon
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  have hR : (1 - (Fintype.card (Fin 2) : ℝ) * (1/2)) * tvDistance twoE0 e0
      = 0 := by
    rw [hcard, tv_twoE0_e0]; norm_num
  rw [tv_twoE0Qh_e0Qh, hR] at hcon
  norm_num at hcon

/-- **Fence 2: the equal-mass clause of the sharp Dobrushin contraction
is load-bearing.** At the same fixture, `δ(Qh) = 0` exactly (identical
rows), so the un-guarded conclusion reads `1/2 ≤ 0`. -/
theorem fence_dobrushin_tv_mass_refuted_QA :
    ¬ (tvDistance (twoE0 ᵥ* Qh) (e0 ᵥ* Qh)
      ≤ tvDistance twoE0 e0 * tvDobrushinCoeff Qh) := by
  intro hcon
  rw [tv_twoE0Qh_e0Qh, tv_twoE0_e0, Qh_dobrushin] at hcon
  norm_num at hcon

/-- **Fence 3: the row-stochasticity clause of TV non-expansiveness is
load-bearing.** At the doubled identity (nonnegative, row sums `2`), the
basis pair's TV doubles: `2 ≤ 1` is false. -/
theorem fence_nonexp_row_refuted_QA :
    ¬ (tvDistance (e0 ᵥ* Mx) (e1 ᵥ* Mx) ≤ tvDistance e0 e1) := by
  intro hcon
  rw [tv_e0Mx_e1Mx, tv_e0_e1] at hcon
  norm_num at hcon

/-- **Fence 4: the nonnegativity clause of TV non-expansiveness is
load-bearing.** At the signed stochastic fixture (row sums `1`, negative
off-diagonal), the basis pair's TV triples: `3 ≤ 1` is false. -/
theorem fence_nonexp_nonneg_refuted_QA :
    ¬ (tvDistance (e0 ᵥ* Mn) (e1 ᵥ* Mn) ≤ tvDistance e0 e1) := by
  intro hcon
  rw [tv_e0Mn_e1Mn, tv_e0_e1] at hcon
  norm_num at hcon

/-- **Fence 5: the row-stochasticity clause of Dobrushin
submultiplicativity is load-bearing.** At `Qx = !![1, 1; 1, -1]` (row
sums `2, 0`) with `s = t = 1`: `δ(Qx²) = δ(2·I) = 2 > δ(Qx)² =
TV((1,1),(1,-1))² = 1`. -/
theorem fence_dobrushin_submul_row_refuted_QA :
    ¬ (tvDobrushinCoeff (Qx ^ (1 + 1))
      ≤ tvDobrushinCoeff (Qx ^ 1) * tvDobrushinCoeff (Qx ^ 1)) := by
  intro hcon
  rw [show Qx ^ (1 + 1) = Qx ^ 2 from by norm_num, Qx_sq,
    show (Qx : Matrix (Fin 2) (Fin 2) ℝ) ^ 1 = Qx from pow_one Qx,
    Mx_dobrushin, Qx_dobrushin] at hcon
  norm_num at hcon

/-- **Fence 6: the zero-mass clause of zero-sum interval pinning is
load-bearing.** At `w = e₀` (mass `1`) against `h = e₀` (entrywise range
`1`), the un-guarded conclusion reads `1 ≤ 1/2`. -/
theorem fence_interval_pin_mass_refuted_QA :
    ¬ (|e0 ⬝ᵥ e0| ≤ (1/2) * entryRange e0 * ∑ i, |e0 i|) := by
  intro hcon
  rw [dot_e0_e0, entryRange_e0, sum_abs_e0] at hcon
  norm_num at hcon

/-- **Fence 7: the zero-mass clause of the pairing core is
load-bearing.** At `c = e₀` (mass `1`) against `g = e₀` (oscillation
bound `D = 1`, every `hD` clause verified by `hD_e0`), the un-guarded
conclusion reads `1 ≤ 1/2`. -/
theorem fence_pairing_mass_refuted_QA :
    ¬ (|∑ z : Fin 2, e0 z * e0 z| ≤ ((∑ z : Fin 2, |e0 z|) / 2) * (1 : ℝ)) := by
  intro hcon
  rw [sum_mul_e0_e0, sum_abs_e0] at hcon
  norm_num at hcon

/-! ### The isolation companions -/

/-- **Isolation for fences 1 and 2**: every other hypothesis of both
contraction lemmas holds genuinely at the fixture — row sums one,
entries `≥ 1/2` (so the Doeblin coefficient `1 - |V|δ` is exactly `0`,
and `δ(Qh) = 0` by identical rows) — the masses are `2` and `1`, and
the equal-mass clause is exactly what fails. -/
theorem fence_mass_isolation_QA :
    (∀ i, ∑ j, Qh i j = 1) ∧ (∀ i j, (1/2 : ℝ) ≤ Qh i j)
      ∧ ∑ i, twoE0 i = 2 ∧ ∑ i, e0 i = 1
      ∧ ¬ (∑ i, twoE0 i = ∑ i, e0 i) := by
  refine ⟨Qh_row_sum, Qh_half_le, sum_twoE0, sum_e0, ?_⟩
  intro h
  rw [sum_twoE0, sum_e0] at h
  norm_num at h

/-- **Isolation for fence 3**: the doubled identity is genuinely
nonnegative and genuinely not row-stochastic (row sums `2`). -/
theorem fence_nonexp_row_isolation_QA :
    (∀ i j, 0 ≤ Mx i j) ∧ (2 : ℝ) = ∑ j, Mx 0 j := by
  refine ⟨Mx_nonneg, ?_⟩
  rw [Mx_row_zero]; norm_num [Fin.sum_univ_two]

/-- **Isolation for fence 4**: the signed fixture has genuine row sums
`1` and a genuinely negative entry. -/
theorem fence_nonexp_nonneg_isolation_QA :
    (∀ i, ∑ j, Mn i j = 1) ∧ Mn 0 1 = -1 ∧ ¬ (0 ≤ Mn 0 1) := by
  refine ⟨Mn_row_sum, Mn_zero_one, ?_⟩
  rw [Mn_zero_one]
  norm_num

/-- **Isolation for fence 5**: the submultiplicativity refuter has
genuinely failing row sums (row `0` sums to `2`, row `1` to `0`). -/
theorem fence_dobrushin_submul_isolation_QA :
    (2 : ℝ) = ∑ j, Qx 0 j ∧ (0 : ℝ) = ∑ j, Qx 1 j
      ∧ ¬ (∀ i, ∑ j, Qx i j = 1) := by
  refine ⟨by rw [Qx_row_zero]; norm_num [Fin.sum_univ_two],
    by rw [Qx_row_one]; norm_num [Fin.sum_univ_two], ?_⟩
  intro h
  have h0 := h 0
  rw [Qx_row_zero] at h0
  norm_num [Fin.sum_univ_two] at h0

/-- **Isolation for fences 6 and 7**: the pairing-core fixture has every
oscillation clause verified at `D = 1`, and its mass is genuinely `1`,
not `0`. -/
theorem fence_pairing_mass_isolation_QA :
    (∀ z z', |e0 z - e0 z'| ≤ 1) ∧ ¬ (∑ z : Fin 2, e0 z = 0) := by
  refine ⟨hD_e0, ?_⟩
  rw [sum_e0]
  norm_num


section DobrushinShadowQA

/-!
### The Dobrushin shadow's pins (2026-09-06,
`proposals/sharp-second-eigenvalue-layer.md`, Slice 2 (a))

The shadow ceiling's QA obligation, at the two-cycle fixture: the
`t = 1` rate bound pinned with its constant attained (the walk's
Dobrushin coefficient is `1` there, so the bound IS `α`), and the
`α^t` corollary instantiated.
-/

/-- The two-cycle fixture (same graph as `PageRank_QA`'s spectral
pins). -/
def dmxCyc : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem dmxCyc_nonneg : ∀ i j, 0 ≤ dmxCyc i j := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [dmxCyc]

theorem dmxCyc_deg_pos : ∀ i, 0 < deg dmxCyc i := by
  intro i
  fin_cases i <;> norm_num [deg, dmxCyc, Fin.sum_univ_two]

/-- **The walk's Dobrushin coefficient is `1` on the two-cycle**: the
swapped rows are point masses at distinct vertices. -/
theorem dmxCyc_dobrushin_one :
    tvDobrushinCoeff (walkTransitionMatrix dmxCyc) = 1 := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le
      (⟨(0, 1), Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin 2 × Fin 2)).Nonempty)
      (f := fun p => tvDistance (walkTransitionMatrix dmxCyc p.1)
        (walkTransitionMatrix dmxCyc p.2))
      fun p _ => ?_
    exact tvDistance_le_one_of_nonneg_of_sum_eq_one
      (walkTransitionMatrix_nonneg dmxCyc dmxCyc_nonneg dmxCyc_deg_pos p.1)
      (walkTransitionMatrix_row_sum dmxCyc dmxCyc_deg_pos p.1)
      (walkTransitionMatrix_nonneg dmxCyc dmxCyc_nonneg dmxCyc_deg_pos p.2)
      (walkTransitionMatrix_row_sum dmxCyc dmxCyc_deg_pos p.2)
  · have hrow0 : walkTransitionMatrix dmxCyc 0 = ![0, 1] := by
      funext j
      fin_cases j <;>
        norm_num [walkTransitionMatrix, deg, degreeMatrix, dmxCyc,
          Fin.sum_univ_two, Matrix.diagonal_mul, Matrix.diagonal_apply,
          inv_mul_cancel₀]
    have hrow1 : walkTransitionMatrix dmxCyc 1 = ![1, 0] := by
      funext j
      fin_cases j <;>
        norm_num [walkTransitionMatrix, deg, degreeMatrix, dmxCyc,
          Fin.sum_univ_two, Matrix.diagonal_mul, Matrix.diagonal_apply,
          inv_mul_cancel₀]
    have h0 : (1 : ℝ) = tvDistance (walkTransitionMatrix dmxCyc 0)
        (walkTransitionMatrix dmxCyc 1) := by
      rw [hrow0, hrow1, tvDistance]
      have hsum : ∑ i, |(![0, 1] : Fin 2 → ℝ) i - (![1, 0] : Fin 2 → ℝ) i| = 2 := by
        rw [Fin.sum_univ_two]
        norm_num [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
      rw [hsum]
      norm_num
    rw [h0]
    refine Finset.le_sup'
      (f := fun p : Fin 2 × Fin 2 =>
        tvDistance (walkTransitionMatrix dmxCyc p.1)
          (walkTransitionMatrix dmxCyc p.2))
      (Finset.mem_univ (0, 1))

/-- **The rate bound attained at the ceiling**: with `δ(P) = 1` the
`t = 1` bound IS `α` — instantiated at `α = 4/5` through the pinned
coefficient. -/
theorem dmxCyc_rate_attained_QA :
    pageRankTVPair dmxCyc (4 / 5 : ℝ) 1 ≤ 4 / 5 := by
  have h := pageRankTVPair_one_le dmxCyc (by norm_num : (0 : ℝ) ≤ 4 / 5)
  rw [dmxCyc_dobrushin_one, mul_one] at h
  exact h

/-- The `α^t` corollary instantiated at `t = 2`. -/
theorem dmxCyc_alpha_pow_QA :
    pageRankTVPair dmxCyc (4 / 5 : ℝ) 2 ≤ (4 / 5 : ℝ) ^ 2 :=
  pageRankTVPair_le_pow_alpha dmxCyc dmxCyc_nonneg dmxCyc_deg_pos
    (by norm_num) 2

/-- **The exact `t = 1` identity at the fixture**: with the pinned
`δ(P) = 1`, the two-start distance IS `α` — the exact shadow
attained. -/
theorem dmxCyc_one_eq_QA :
    pageRankTVPair dmxCyc (4 / 5 : ℝ) 1 = 4 / 5 := by
  rw [pageRankTVPair_one_eq dmxCyc (by norm_num : (0 : ℝ) ≤ 4 / 5),
    dmxCyc_dobrushin_one, mul_one]

end DobrushinShadowQA

end Scaffold.QA.SpectralGraph
