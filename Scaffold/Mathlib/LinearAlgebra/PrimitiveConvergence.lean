import Mathlib.Topology.Constructions
import Scaffold.Mathlib.LinearAlgebra.PerronFrobenius

/-!
# Primitive power convergence — the directed mixing gate

The primitivity-shaped admission the standing handoff names as the gate
for directed-axis mixing/rate work (`perron_frobenius` deliberately
claims no strict eigenvalue dominance: on the irreducible-but-periodic
directed 2-cycle the powers provably do not converge — the
`strict_dominance_refuted_QA` imprimitivity fence of the
Perron–Frobenius module, and the QA fence of this module's consumer
layer re-proves it in the convergence form). Everything the
PF-consumer shelf built — `IrreducibleStationary`, `PageRank` —
establishes *stationary* structure (existence, uniqueness, support);
no convergence statement is reachable from the existing axiom, because
convergence is genuinely false on the periodic input the axiom
honestly covers. This module admits the missing statement: powers of a
**primitive** row-stochastic matrix converge to the rank-one stationary
projector. It is the classical power-method / Markov-chain convergence
theorem, and its first consumer (`GraphTheory.DirectedMixing`) is the
PageRank power iteration — the loop-closer with the delivered
existence/`∃!` layer: the distribution is not only unique, it is
computable.

## The statement and its calibration

`Matrix.IsPrimitive` is Horn & Johnson's definition of primitivity
verbatim: some strictly positive power is strictly positive,
entrywise. This is strictly stronger than irreducibility (every
irreducible *aperiodic* matrix is primitive; the directed 2-cycle is
irreducible but has no positive power), and the hypothesis is exactly
what separates convergence from oscillation:

- on `P₂ = !![0,1;1,0]` — nonnegative, row-stochastic, *and*
  irreducible — `P₂ ^ t *ᵥ e₀` alternates between `e₀` and `e₁`
  forever, so `¬ Tendsto` in proved form (`P2_no_limit_QA` in
  `DirectedMixing_QA`): the hypothesis-free conclusion is refuted and
  `hprim` is load-bearing, with every other axiom hypothesis
  (nonnegativity, row stochasticity, existence of a nonnegative
  mass-one stationary vector — the uniform one) *verified* on the same
  fixture. Exactly `hprim` is isolated.

The admitted statement is the row-stochastic specialization of the
source's primitive Perron–Frobenius limit: the source states
`lim (A/ρ(A))^m = x yᵀ` at the Perron data; at a row-stochastic
matrix the Perron root is `1`, the right Perron vector is the constant-one vector,
and the left is the stationary distribution `π`, so the limit reads
`Pᵗ *ᵥ x → (π ⬝ᵥ x) • 1` — the specialization is one line of
Perron-vector identification, stated directly to keep the blast radius
small.

## Trust boundary and honest scope

`primitive_power_tendsto` is an **admitted axiom** — a Lean-usable
interface, not a foundationally proved theorem. Every consumer below
or downstream that applies it is conditional on exactly this axiom
(the PageRank power iteration composes it with hypotheses that are
unconditional hard crust, so its trust cost is *this* axiom alone —
`perron_frobenius` is needed to *produce* `π`, not to conclude the
convergence, and the two axioms' trust costs are independent).

No rate: the geometric rate (`|λ₂|`-shaped bounds) needs the complex
spectral theory of non-symmetric matrices, which the shelf does not
have; convergence alone is admitted. Rates are a separate future
admission gated on a consumer. Coordinate (Π) topology only; no
operator-norm convergence statement. `hrow` is a convenience
hypothesis kept for source fidelity and structural checkability — on a
primitive nonnegative matrix with a positive mass-one stationary
vector, Perron–Frobenius itself pins the spectral radius to `1`, so no
refutation QA for it exists or is claimed (recorded in
`proposals/primitive-power-convergence.md`).

## Unconditional hard crust (no axiom contact)

`isPrimitive_of_pos` (a positive matrix is primitive at `k = 1` — the
entire content of the Google-matrix consumer's discharge),
`reachable_of_pow_pos` and `isIrreducible_of_isPrimitive` (an entry of
a positive power is a sum over positive-weight walks, so primitivity
implies strong connectivity — the connective tissue to the delivered
PF-consumer layer, load-bearing on `Matrix.IsIrreducible`'s exact
combinatorial shape), `pow_mulVec_one` (powers of a row-stochastic
matrix fix the constant-one vector — the coherence engine), and the two generic
corollaries of the axiom at matrix level: `primitive_entrywise_tendsto`
(each column of `Pᵗ` converges to `π`) and `primitive_vecMul_tendsto`
(the row-action form `ν ᵥ* Pᵗ → π`, for any start summing to one).

## Statement differences from the source

- The source's primitive limit is stated at the Perron data; this is
  the row-stochastic specialization (see above), given-π form.
- Primitivity is the positive-power definition, not an aperiodicity
  index; no characterization theorems are bundled.
- Arbitrary `Fintype V` with no guard: on the empty type the mass-one
  hypothesis `∑ i, π i = 1` is unsatisfiable (the statement is
  vacuous), and on a singleton it is trivially true.

Source:
- Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., Cambridge
  University Press, 2013, §8.5 (primitive matrices; the
  Perron–Frobenius limit theorem for primitive matrices). Section-level
  locator recorded; the page-level locator is pending the same
  physical-copy review as the other Horn–Johnson rows — not invented.
- The row-stochastic specialization is the finite Markov-chain
  convergence theorem, cf. Levin, Y., Peres, Y. & Wilmer, E.,
  "Markov Chains and Mixing Times", AMS 2009, Theorem 4.9 (chapter
  4, "Markov Chain Mixing"); theorem-level locator likewise pending
  physical-copy verification. The mathematical content admitted here
  is Horn–Johnson's; the Markov-chain reference is the stochastic-form
  cross-reference only.

QA: exercised by `Scaffold.QA.SpectralGraph.DirectedMixing_QA.*` (the
reducible-fixture positive witness with the limit pinned to the
raw-verified uniform PageRank value and the second iterate computed
raw inside it; the periodicity refutation with `hprim` exactly
isolated; the `onesVec` coherence join; the irreducibility transfer
cross-checked against the delivered single-arc route).

Admitted 2026-08-24 (`proposals/primitive-power-convergence.md`,
count 9 → 10).
-/

open scoped Matrix Topology

namespace Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

/-- H&J's definition of primitivity: some strictly positive power is
strictly positive, entrywise. Strictly stronger than
`Matrix.IsIrreducible` (see `isIrreducible_of_isPrimitive`): the
directed 2-cycle is irreducible but every odd power is a permutation
matrix with zero entries, so it is not primitive — which is exactly
why power convergence needs this hypothesis and not mere
irreducibility. -/
def IsPrimitive (P : Matrix V V ℝ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∀ i j, 0 < (P ^ k) i j

end Matrix

namespace Scaffold.LinearAlgebra

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Primitive power convergence** (admitted axiom). Powers of a
primitive row-stochastic matrix converge, in every coordinate, to the
rank-one stationary projector applied to the starting vector:
`(P ^ t) *ᵥ x → (π ⬝ᵥ x) • onesVec`, where `π` is any nonnegative
mass-one stationary vector (`π ᵥ* P = π`, Mathlib's left-action form).
Equivalently, every row of `Pᵗ` converges to `π`.

The hypothesis `Matrix.IsPrimitive` is load-bearing and fenced: on
the irreducible periodic directed 2-cycle the conclusion is refuted in
proved form with every other hypothesis verified
(`Scaffold.QA.SpectralGraph.P2_no_limit_QA`). Given-π form: consumers
hold their stationary distribution (e.g. the delivered unique
PageRank vector); the axiom produces no witness.

Source:
- Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., Cambridge
  University Press, 2013, §8.5 (primitive matrices; the
  Perron–Frobenius limit for primitive matrices), specialized to the
  row-stochastic case at Perron root `1`.
- Cross-reference for the stochastic form: Levin–Peres–Wilmer,
  "Markov Chains and Mixing Times", Theorem 4.9.

Statement differences and honest scope (no rate, Π topology,
`hrow`'s status): see the module documentation. Section-level
locators, page-level pending physical-copy review per repository
policy.

QA: exercised by
`Scaffold.QA.SpectralGraph.DirectedMixing_QA.*`. -/
axiom primitive_power_tendsto (P : Matrix V V ℝ)
    (hnn : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    (hprim : P.IsPrimitive)
    {π : V → ℝ} (hπnn : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* P = π) (x : V → ℝ) :
    Filter.Tendsto (fun t : ℕ => (P ^ t) *ᵥ x) Filter.atTop
      (𝓝 ((π ⬝ᵥ x) • (1 : V → ℝ)))

/-- A strictly positive matrix is primitive, at `k = 1`. The entire
content of the Google-matrix consumer's primitivity discharge: the
teleportation floor is positivity, and positivity is primitivity.
Unconditional hard crust. -/
theorem isPrimitive_of_pos (P : Matrix V V ℝ) (h : ∀ i j, 0 < P i j) :
    P.IsPrimitive :=
  ⟨1, by norm_num, by rwa [pow_one]⟩

/-- An entry of a positive power is a sum over length-`k` walks, so a
positive entry yields a positive-weight directed walk: the
walk decomposition behind `isIrreducible_of_isPrimitive`. Unconditional
hard crust. -/
theorem reachable_of_pow_pos {P : Matrix V V ℝ} (hnn : ∀ i j, 0 ≤ P i j) :
    ∀ (k : ℕ) (i j : V), 0 < (P ^ k) i j →
      Relation.ReflTransGen (fun a b => 0 < P a b) i j := by
  intro k
  induction k with
  | zero =>
    intro i j hij
    rw [pow_zero, Matrix.one_apply] at hij
    by_cases h : i = j
    · subst h; exact Relation.ReflTransGen.refl
    · rw [if_neg h] at hij
      exact absurd hij (by norm_num)
  | succ k ih =>
    intro i j hij
    rw [pow_succ, Matrix.mul_apply] at hij
    have hsome : ∃ m : V, 0 < (P ^ k) i m * P m j := by
      by_contra hcon
      push_neg at hcon
      have h1 : 0 ≤ ∑ m : V, -((P ^ k) i m * P m j) :=
        Finset.sum_nonneg (fun m _ => neg_nonneg.mpr (hcon m))
      rw [Finset.sum_neg_distrib] at h1
      linarith
    obtain ⟨m, hm⟩ := hsome
    have hkm : 0 < (P ^ k) i m := by
      by_contra hc
      push_neg at hc
      have hle : (P ^ k) i m * P m j ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc (hnn m j)
      linarith
    have hmj : 0 < P m j := by
      by_contra hc
      push_neg at hc
      have hnnkm : 0 ≤ (P ^ k) i m := by
        by_contra h2
        push_neg at h2
        have hle : (P ^ k) i m * P m j ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (le_of_lt h2) (hnn m j)
        linarith
      have hle : (P ^ k) i m * P m j ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hnnkm hc
      linarith
    exact (ih i m hkm).tail hmj

/-- **Primitivity implies irreducibility**: a positive power makes
every pair reachable through positive-weight arcs. The connective
tissue between this module's hypothesis and the delivered
Perron–Frobenius consumer layer's `Matrix.IsIrreducible`; strictly
stronger (the 2-cycle witnesses the gap). Unconditional hard crust.

QA: exercised — cross-checked against the delivered single-arc
irreducibility route on the Google fixture — by
`Scaffold.QA.SpectralGraph.DirectedMixing_QA.*`. -/
theorem isIrreducible_of_isPrimitive {P : Matrix V V ℝ}
    (hnn : ∀ i j, 0 ≤ P i j) (hprim : P.IsPrimitive) :
    P.IsIrreducible := by
  obtain ⟨k, -, hpos⟩ := hprim
  exact fun i j => reachable_of_pow_pos hnn k i j (hpos i j)

/-- Powers of a row-stochastic matrix fix the constant-one vector
`(1 : V → ℝ)`: the iterates' mass bookkeeping, and the coherence
engine for the axiom's limit at `x = 1`. Unconditional hard crust;
the graph-side `onesVec` translation is `DirectedMixing`'s. -/
theorem pow_mulVec_one {P : Matrix V V ℝ} (hrow : ∀ i, ∑ j, P i j = 1)
    (t : ℕ) :
    (P ^ t) *ᵥ (1 : V → ℝ) = 1 := by
  have hP1 : P *ᵥ (1 : V → ℝ) = 1 := by
    funext i
    simp only [Matrix.mulVec, Matrix.dotProduct, Pi.one_apply, mul_one]
    exact hrow i
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hP1]
    exact ih

/-- **Entrywise convergence** (conditional on `primitive_power_tendsto`
alone): every column of `Pᵗ` converges to `π` — the transition
probability `P(X_t = j | X_0 = i)` tends to the stationary weight of
`j`, independent of the start `i`. The axiom applied at the basis
vector `e j` through `Matrix.mulVec_single`. -/
theorem primitive_entrywise_tendsto (P : Matrix V V ℝ)
    (hnn : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    (hprim : P.IsPrimitive)
    {π : V → ℝ} (hπnn : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* P = π) (i j : V) :
    Filter.Tendsto (fun t : ℕ => (P ^ t) i j) Filter.atTop (𝓝 (π j)) := by
  have h := primitive_power_tendsto P hnn hrow hprim hπnn hπsum hπstat
    (Pi.single j 1)
  have h0 := (tendsto_pi_nhds.mp h) i
  simp only [Matrix.mulVec_single, Pi.single_apply, one_mul, smul_eq_mul,
    Pi.smul_apply, Pi.one_apply, mul_one,
    Matrix.dotProduct_single] at h0
  exact h0

/-- Finite sums of convergent sequences converge (private support for
`primitive_vecMul_tendsto`; the pin has no tendsto-sum lemma). -/
private theorem tendsto_finset_sum (F : V → ℕ → ℝ) (G : V → ℝ)
    (h : ∀ m, Filter.Tendsto (F m) Filter.atTop (𝓝 (G m))) :
    Filter.Tendsto (fun t => ∑ m, F m t) Filter.atTop (𝓝 (∑ m, G m)) := by
  have key : ∀ (s : Finset V), Filter.Tendsto (fun t => ∑ m in s, F m t)
      Filter.atTop (𝓝 (∑ m in s, G m)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert m s hm ih =>
      have h1 : (fun t : ℕ => ∑ x ∈ insert m s, F x t)
          = fun t => F m t + ∑ x ∈ s, F x t := by
        funext t
        rw [Finset.sum_insert hm]
      have h2 : (∑ x ∈ insert m s, G x) = G m + ∑ x ∈ s, G x :=
        Finset.sum_insert hm
      rw [h1, h2]
      exact (h m).add ih
  exact key Finset.univ

/-- **Walk-evolution convergence** (conditional on
`primitive_power_tendsto` alone): the row action of the powers takes
any start vector summing to one (a distribution, though only the sum
is used — no nonnegativity hypothesis) to the stationary distribution,
`ν ᵥ* Pᵗ → π`. The Markov-chain mixing first slice, entrywise/Π
topology; the rate forms are explicitly out of the admitted statement
(see the module documentation). -/
theorem primitive_vecMul_tendsto (P : Matrix V V ℝ)
    (hnn : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    (hprim : P.IsPrimitive)
    {π : V → ℝ} (hπnn : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* P = π) (ν : V → ℝ) (hνsum : ∑ i, ν i = 1) :
    Filter.Tendsto (fun t : ℕ => ν ᵥ* (P ^ t)) Filter.atTop (𝓝 π) := by
  rw [tendsto_pi_nhds]
  intro j
  have hsum := tendsto_finset_sum (fun m => fun t => ν m * (P ^ t) m j)
    (fun m => ν m * π j) (fun m => (primitive_entrywise_tendsto P hnn
      hrow hprim hπnn hπsum hπstat m j).const_mul (ν m))
  have hfac : ∑ x, ν x * π j = π j := by
    rw [← Finset.sum_mul, hνsum, one_mul]
  rw [hfac] at hsum
  simpa only [Matrix.vecMul, Matrix.dotProduct] using hsum

end Scaffold.LinearAlgebra
