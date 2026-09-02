import Mathlib.Topology.Constructions
import Mathlib.Algebra.Order.Archimedean.Basic
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
honestly covers. This module carried the missing statement as an
admission (2026-08-24) and **proves it since 2026-09-02**: powers of a
**primitive** row-stochastic matrix converge to the rank-one stationary
projector — by the Doeblin/Dobrushin contraction route (see the
retirement section below; `#print axioms` exactly the standard three).
It is the classical power-method / Markov-chain convergence
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

## Retired 2026-09-02: the Doeblin/Dobrushin contraction route

`primitive_power_tendsto` was admitted 2026-08-24 with the recorded
replacement path "no dedicated local proof route is currently priced".
That pricing missed an elementary route that needs no Perron–Frobenius
machinery at all (proposal
`proposals/retire-primitive-power-convergence.md`): a primitive matrix
has a strictly positive power `Q = P^m`, every entry of `Q` is `≥ δ`
for some `δ > 0` (finiteness), and splitting each row as `δ` (uniform
part) plus a remainder of mass `1 - |V|·δ` shows every entry of
`Q *ᵥ y` lands in one common interval — the entrywise range contracts
geometrically, `range (Q *ᵥ y) ≤ (1 - |V|δ) · range y`, the classical
Doeblin/Dobrushin coefficient bound (`entryRange_mulVec_le_of_pos_entries`
below). Iterating over `m`-blocks with plain stochastic
non-expansiveness on the `t mod m` remainder gives
`range (P^t *ᵥ x) ≤ ρ^(t/m) · range x` for `ρ = 1 - |V|δ ∈ [0, 1)`;
the π-pairing is invariant by stationarity and is a convex combination
of the entries, so both the entry and the limit coefficient lie in the
(vanishing) range interval — a direct ε–N convergence proof. The whole
directed mixing layer (`DirectedMixing`'s three theorems, both generic
corollaries below) is now hard crust at unchanged statements.

Honest scope after the retirement: the statement still carries **no
rate clause**, and the proof's byproduct rate `ρ^(t/m)` is the Doeblin
bound — explicit but typically far from sharp. The *sharp* `|λ₂|`-type
rate still needs the complex spectral theory of non-symmetric
matrices, which the shelf does not have; that remains a separate
future admission gated on a consumer. Coordinate (Π) topology only; no
operator-norm convergence statement. `hrow` is a convenience
hypothesis kept for source fidelity and structural checkability.

## Hard crust (no axiom contact)

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

/-- Powers of a row-stochastic matrix fix the constant-one vector
`(1 : V → ℝ)`: the iterates' mass bookkeeping, and the coherence
engine for the convergence theorem's limit at `x = 1`. Unconditional
hard crust; the graph-side `onesVec` translation is `DirectedMixing`'s.
(Moved ahead of the Doeblin engine: `pow_row_sum` below is its sum
form.) -/
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

section Doeblin

/-! ### The entrywise-range engine (Doeblin's coefficient)
-/

/-- The entrywise supremum of a vector on a nonempty finite type. -/
def entrySup [Nonempty V] (y : V → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => y i)

/-- The entrywise infimum of a vector on a nonempty finite type. -/
def entryInf [Nonempty V] (y : V → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => y i)

/-- The entrywise range (diameter) of a vector on a nonempty finite
type: the quantity Doeblin's coefficient controls. -/
def entryRange [Nonempty V] (y : V → ℝ) : ℝ := entrySup y - entryInf y

omit [DecidableEq V] in
theorem le_entrySup [Nonempty V] (y : V → ℝ) (i : V) : y i ≤ entrySup y :=
  Finset.le_sup' (fun i => y i) (Finset.mem_univ i)

omit [DecidableEq V] in
theorem entryInf_le [Nonempty V] (y : V → ℝ) (i : V) : entryInf y ≤ y i :=
  Finset.inf'_le (fun i => y i) (Finset.mem_univ i)

omit [DecidableEq V] in
theorem entryRange_nonneg [Nonempty V] (y : V → ℝ) : 0 ≤ entryRange y := by
  obtain ⟨i⟩ := ‹Nonempty V›
  exact sub_nonneg.mpr ((entryInf_le y i).trans (le_entrySup y i))

omit [DecidableEq V] in
/-- A row-stochastic action keeps every entry inside the vector's
entrywise interval (convex combination of the entries). -/
theorem mulVec_le_entrySup [Nonempty V] {M : Matrix V V ℝ}
    (hnn : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j = 1) (y : V → ℝ)
    (i : V) : (M *ᵥ y) i ≤ entrySup y := by
  have h1 : ∀ j ∈ (Finset.univ : Finset V), M i j * y j ≤ M i j * entrySup y :=
    fun j _ => mul_le_mul_of_nonneg_left (le_entrySup y j) (hnn i j)
  calc (M *ᵥ y) i = ∑ j, M i j * y j := rfl
    _ ≤ ∑ j, M i j * entrySup y := Finset.sum_le_sum h1
    _ = entrySup y := by rw [← Finset.sum_mul, hrow i, one_mul]

omit [DecidableEq V] in
/-- The mirror of `mulVec_le_entrySup` at the infimum. -/
theorem entryInf_le_mulVec [Nonempty V] {M : Matrix V V ℝ}
    (hnn : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j = 1) (y : V → ℝ)
    (i : V) : entryInf y ≤ (M *ᵥ y) i := by
  have h1 : ∀ j ∈ (Finset.univ : Finset V), M i j * entryInf y ≤ M i j * y j :=
    fun j _ => mul_le_mul_of_nonneg_left (entryInf_le y j) (hnn i j)
  calc entryInf y = (∑ j, M i j) * entryInf y := by rw [hrow i, one_mul]
    _ = ∑ j, M i j * entryInf y := by rw [Finset.sum_mul]
    _ ≤ ∑ j, M i j * y j := Finset.sum_le_sum h1
    _ = (M *ᵥ y) i := rfl

omit [DecidableEq V] in
/-- A convex combination of the entries (nonnegative mass-one weights)
lies inside the entrywise interval. -/
theorem entryInf_le_dotProduct [Nonempty V] {w : V → ℝ}
    (hwnn : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1) (y : V → ℝ) :
    entryInf y ≤ w ⬝ᵥ y := by
  have h1 : ∀ j ∈ (Finset.univ : Finset V), w j * entryInf y ≤ w j * y j :=
    fun j _ => mul_le_mul_of_nonneg_left (entryInf_le y j) (hwnn j)
  calc entryInf y = (∑ j, w j) * entryInf y := by rw [hwsum, one_mul]
    _ = ∑ j, w j * entryInf y := by rw [Finset.sum_mul]
    _ ≤ ∑ j, w j * y j := Finset.sum_le_sum h1
    _ = w ⬝ᵥ y := rfl

omit [DecidableEq V] in
/-- The mirror of `entryInf_le_dotProduct` at the supremum. -/
theorem dotProduct_le_entrySup [Nonempty V] {w : V → ℝ}
    (hwnn : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1) (y : V → ℝ) :
    w ⬝ᵥ y ≤ entrySup y := by
  have h1 : ∀ j ∈ (Finset.univ : Finset V), w j * y j ≤ w j * entrySup y :=
    fun j _ => mul_le_mul_of_nonneg_left (le_entrySup y j) (hwnn j)
  calc w ⬝ᵥ y = ∑ j, w j * y j := rfl
    _ ≤ ∑ j, w j * entrySup y := Finset.sum_le_sum h1
    _ = entrySup y := by rw [← Finset.sum_mul, hwsum, one_mul]

omit [DecidableEq V] in
/-- **Stochastic non-expansiveness of the entrywise range.** Every
row-stochastic nonneg matrix action contracts nothing and expands
nothing: `range (M *ᵥ y) ≤ range y`. -/
theorem entryRange_mulVec_le [Nonempty V] {M : Matrix V V ℝ}
    (hnn : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j = 1) (y : V → ℝ) :
    entryRange (M *ᵥ y) ≤ entryRange y := by
  have hsup : entrySup (M *ᵥ y) ≤ entrySup y :=
    (Finset.sup'_le_iff Finset.univ_nonempty (fun i => (M *ᵥ y) i)).mpr
      (fun i _ => mulVec_le_entrySup hnn hrow y i)
  have hinf : entryInf y ≤ entryInf (M *ᵥ y) :=
    Finset.le_inf' Finset.univ_nonempty (fun i => (M *ᵥ y) i)
      (fun i _ => entryInf_le_mulVec hnn hrow y i)
  exact sub_le_sub hsup hinf

omit [DecidableEq V] in
/-- **The Doeblin/Dobrushin contraction.** If every entry of the
row-stochastic `Q` is at least `δ`, then `Q`'s action contracts the
entrywise range by the coefficient `1 - |V|·δ`: each row splits as
`δ` (uniform part) plus a remainder of mass `1 - |V|δ`, and the uniform
part shifts all entries by the same constant, leaving only the
remainder's convex-combination spread. The classical first-moment
(Markov-chain Doeblin) coefficient bound.

QA: the mechanism section of `DirectedMixing_QA` pins this attained
exactly on the strictly positive `2×2` fixture and refutes the
wrong-`δ` form. -/
theorem entryRange_mulVec_le_of_pos_entries [Nonempty V] {Q : Matrix V V ℝ}
    (hrow : ∀ i, ∑ j, Q i j = 1) {δ : ℝ} (hle : ∀ i j, δ ≤ Q i j)
    (y : V → ℝ) :
    entryRange (Q *ᵥ y) ≤ (1 - (Fintype.card V : ℝ) * δ) * entryRange y := by
  have hsplit : ∀ i, (Q *ᵥ y) i = δ * (∑ j, y j) + ∑ j, (Q i j - δ) * y j := by
    intro i
    have heq : ∀ j, Q i j * y j = δ * y j + (Q i j - δ) * y j := fun _ => by ring
    calc (Q *ᵥ y) i = ∑ j, Q i j * y j := rfl
      _ = ∑ j, (δ * y j + (Q i j - δ) * y j) :=
        Finset.sum_congr rfl (fun j _ => heq j)
      _ = δ * (∑ j, y j) + ∑ j, (Q i j - δ) * y j := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcoef : ∀ i, ∑ j, (Q i j - δ) = 1 - (Fintype.card V : ℝ) * δ := by
    intro i
    rw [Finset.sum_sub_distrib, hrow i]
    simp
  have hsub : ∀ i, (Q *ᵥ y) i ≤ δ * (∑ j, y j) +
      (1 - (Fintype.card V : ℝ) * δ) * entrySup y := by
    intro i
    have h1 : ∀ j ∈ (Finset.univ : Finset V),
        (Q i j - δ) * y j ≤ (Q i j - δ) * entrySup y :=
      fun j _ => mul_le_mul_of_nonneg_left (le_entrySup y j)
        (sub_nonneg.mpr (hle i j))
    have h2 : ∑ j, (Q i j - δ) * y j ≤
        (1 - (Fintype.card V : ℝ) * δ) * entrySup y :=
      calc ∑ j, (Q i j - δ) * y j ≤ ∑ j, (Q i j - δ) * entrySup y :=
          Finset.sum_le_sum h1
        _ = (∑ j, (Q i j - δ)) * entrySup y := by rw [Finset.sum_mul]
        _ = (1 - (Fintype.card V : ℝ) * δ) * entrySup y := by rw [hcoef i]
    rw [hsplit i]
    linarith
  have hsub' : ∀ i, δ * (∑ j, y j) +
      (1 - (Fintype.card V : ℝ) * δ) * entryInf y ≤ (Q *ᵥ y) i := by
    intro i
    have h1 : ∀ j ∈ (Finset.univ : Finset V),
        (Q i j - δ) * entryInf y ≤ (Q i j - δ) * y j :=
      fun j _ => mul_le_mul_of_nonneg_left (entryInf_le y j)
        (sub_nonneg.mpr (hle i j))
    have h2 : (1 - (Fintype.card V : ℝ) * δ) * entryInf y ≤
        ∑ j, (Q i j - δ) * y j :=
      calc (1 - (Fintype.card V : ℝ) * δ) * entryInf y
          = (∑ j, (Q i j - δ)) * entryInf y := by rw [hcoef i]
        _ = ∑ j, (Q i j - δ) * entryInf y := by rw [Finset.sum_mul]
        _ ≤ ∑ j, (Q i j - δ) * y j := Finset.sum_le_sum h1
    rw [hsplit i]
    linarith
  have hsup : entrySup (Q *ᵥ y) ≤ δ * (∑ j, y j) +
      (1 - (Fintype.card V : ℝ) * δ) * entrySup y :=
    (Finset.sup'_le_iff Finset.univ_nonempty (fun i => (Q *ᵥ y) i)).mpr
      (fun i _ => hsub i)
  have hinf : δ * (∑ j, y j) +
      (1 - (Fintype.card V : ℝ) * δ) * entryInf y ≤ entryInf (Q *ᵥ y) :=
    Finset.le_inf' Finset.univ_nonempty (fun i => (Q *ᵥ y) i)
      (fun i _ => hsub' i)
  calc entryRange (Q *ᵥ y) = entrySup (Q *ᵥ y) - entryInf (Q *ᵥ y) := rfl
    _ ≤ (δ * (∑ j, y j) + (1 - (Fintype.card V : ℝ) * δ) * entrySup y) -
        (δ * (∑ j, y j) + (1 - (Fintype.card V : ℝ) * δ) * entryInf y) :=
        sub_le_sub hsup hinf
    _ = (1 - (Fintype.card V : ℝ) * δ) * (entrySup y - entryInf y) := by ring

/-! ### Matrix-power plumbing
-/

/-- Entries of powers of a nonnegative matrix are nonnegative. -/
theorem pow_nonneg_entries {P : Matrix V V ℝ} (hnn : ∀ i j, 0 ≤ P i j) :
    ∀ (t : ℕ) (i j : V), 0 ≤ (P ^ t) i j := by
  intro t
  induction t with
  | zero =>
    intro i j
    simp only [pow_zero, Matrix.one_apply]
    split <;> norm_num
  | succ t ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (ih i k) (hnn k j))

/-- Row sums of powers of a row-stochastic matrix stay one (the sum
form of `pow_mulVec_one`). -/
theorem pow_row_sum {P : Matrix V V ℝ} (hrow : ∀ i, ∑ j, P i j = 1)
    (t : ℕ) (i : V) : ∑ j, (P ^ t) i j = 1 := by
  have h := pow_mulVec_one hrow t
  have hi := congrFun h i
  simpa only [Matrix.mulVec, Matrix.dotProduct, Pi.one_apply, mul_one] using hi

/-- Stationarity iterates: a left stationary vector of `P` is stationary
for every power. -/
theorem vecMul_pow_eq_of_vecMul_eq {P : Matrix V V ℝ} {π : V → ℝ}
    (h : π ᵥ* P = π) (t : ℕ) : π ᵥ* P ^ t = π := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih]; exact h

/-- On a finite index set, a pointwise-positive function has a positive
lower bound. -/
theorem exists_pos_le_of_finite {ι : Type} (s : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ s, 0 < f i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, by norm_num, fun i hi => absurd hi (Finset.not_mem_empty i)⟩
  | @insert a s ha ih =>
    obtain ⟨δ, hδpos, hδle⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨min δ (f a), lt_min hδpos (h a (Finset.mem_insert_self a s)),
      fun i hi => ?_⟩
    by_cases hia : i = a
    · subst hia; exact min_le_right _ _
    · exact (min_le_left _ _).trans
        (hδle i ((Finset.mem_insert.mp hi).resolve_left hia))

/-- **The iterated Doeblin contraction over `q` blocks.** With `Q = P^m`
entrywise `≥ δ`, the `m·q`-step action contracts the entrywise range by
`(1 - |V|δ)^q`. -/
theorem entryRange_pow_mul_le [Nonempty V] {P : Matrix V V ℝ}
    (hrow : ∀ i, ∑ j, P i j = 1) {m : ℕ} {δ : ℝ}
    (hle : ∀ i j, δ ≤ (P ^ m) i j) (q : ℕ) :
    ∀ y : V → ℝ, entryRange ((P ^ (m * q)) *ᵥ y) ≤
      (1 - (Fintype.card V : ℝ) * δ) ^ q * entryRange y := by
  have hQrow : ∀ i, ∑ j, (P ^ m) i j = 1 := pow_row_sum hrow m
  have hnδ : (Fintype.card V : ℝ) * δ ≤ 1 := by
    obtain ⟨i₀⟩ := ‹Nonempty V›
    have h1 : (Fintype.card V : ℝ) * δ = ∑ j : V, δ := by simp
    calc (Fintype.card V : ℝ) * δ = ∑ j : V, δ := h1
      _ ≤ ∑ j, (P ^ m) i₀ j := Finset.sum_le_sum (fun j _ => hle i₀ j)
      _ = 1 := hQrow i₀
  have hρ : 0 ≤ 1 - (Fintype.card V : ℝ) * δ := by linarith
  induction q with
  | zero => intro y; simp
  | succ q ih =>
    intro y
    have hmeq : m * (q + 1) = m * q + m := by ring
    have hpow : P ^ (m * (q + 1)) = P ^ (m * q) * P ^ m := by
      rw [hmeq, pow_add]
    have hstep := entryRange_mulVec_le_of_pos_entries hQrow hle y
    calc entryRange ((P ^ (m * (q + 1))) *ᵥ y)
        = entryRange ((P ^ (m * q) * P ^ m) *ᵥ y) := by rw [hpow]
      _ = entryRange ((P ^ (m * q)) *ᵥ ((P ^ m) *ᵥ y)) := by
          rw [← Matrix.mulVec_mulVec]
      _ ≤ (1 - (Fintype.card V : ℝ) * δ) ^ q * entryRange ((P ^ m) *ᵥ y) :=
          ih ((P ^ m) *ᵥ y)
      _ ≤ (1 - (Fintype.card V : ℝ) * δ) ^ q *
          ((1 - (Fintype.card V : ℝ) * δ) * entryRange y) :=
          mul_le_mul_of_nonneg_left hstep (pow_nonneg hρ q)
      _ = (1 - (Fintype.card V : ℝ) * δ) ^ (q + 1) * entryRange y := by
          rw [pow_succ]; ring

end Doeblin

/-- **Primitive power convergence — proved** (retired from axiom
2026-09-02, `proposals/retire-primitive-power-convergence.md`). Powers
of a primitive row-stochastic matrix converge, in every coordinate, to
the rank-one stationary projector applied to the starting vector:
`(P ^ t) *ᵥ x → (π ⬝ᵥ x) • onesVec`, where `π` is any nonnegative
mass-one stationary vector (`π ᵥ* P = π`, Mathlib's left-action form).
Equivalently, every row of `Pᵗ` converges to `π`.

The hypothesis `Matrix.IsPrimitive` is load-bearing and fenced: on
the irreducible periodic directed 2-cycle the conclusion is refuted in
proved form with every other hypothesis verified
(`Scaffold.QA.SpectralGraph.P2_no_limit_QA`). Given-π form: consumers
hold their stationary distribution (e.g. the delivered unique
PageRank vector); the proof produces no witness.

The proof is the Doeblin/Dobrushin contraction route (see the module
documentation): no Perron–Frobenius machinery, `#print axioms` exactly
the standard three.

Source:
- Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., Cambridge
  University Press, 2013, §8.5 (primitive matrices; the
  Perron–Frobenius limit for primitive matrices), specialized to the
  row-stochastic case at Perron root `1`.
- Cross-reference for the stochastic form: Levin–Peres–Wilmer,
  "Markov Chains and Mixing Times", Theorem 4.9.

Statement differences and honest scope (no rate clause — the proof's
Doeblin-rate byproduct is explicit but typically loose; Π topology;
`hrow`'s status): see the module documentation. Section-level
locators, page-level pending physical-copy review per repository
policy.

QA: exercised by
`Scaffold.QA.SpectralGraph.DirectedMixing_QA.*` (the fixture instances
plus the mechanism section pinning the contraction attained exactly
and the wrong-`δ` fence). -/
theorem primitive_power_tendsto (P : Matrix V V ℝ)
    (hnn : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    (hprim : P.IsPrimitive)
    {π : V → ℝ} (hπnn : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* P = π) (x : V → ℝ) :
    Filter.Tendsto (fun t : ℕ => (P ^ t) *ᵥ x) Filter.atTop
      (𝓝 ((π ⬝ᵥ x) • (1 : V → ℝ))) := by
  haveI hVne : Nonempty V := by
    rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset V) with h | h
    · rw [h, Finset.sum_empty] at hπsum; norm_num at hπsum
    · exact ⟨h.choose⟩
  obtain ⟨m, hm0, hpos⟩ := hprim
  obtain ⟨δ, hδpos, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i j : V, δ ≤ (P ^ m) i j := by
    obtain ⟨δ', hδ', hle'⟩ := exists_pos_le_of_finite
      (Finset.univ : Finset (V × V)) (fun p => (P ^ m) p.1 p.2)
      (fun p _ => hpos p.1 p.2)
    exact ⟨δ', hδ', fun i j => hle' (i, j) (Finset.mem_univ _)⟩
  have hQrow : ∀ i, ∑ j, (P ^ m) i j = 1 := pow_row_sum hrow m
  have hnδ : (Fintype.card V : ℝ) * δ ≤ 1 := by
    obtain ⟨i₀⟩ := ‹Nonempty V›
    have h1 : (Fintype.card V : ℝ) * δ = ∑ j : V, δ := by simp
    calc (Fintype.card V : ℝ) * δ = ∑ j : V, δ := h1
      _ ≤ ∑ j, (P ^ m) i₀ j := Finset.sum_le_sum (fun j _ => hδle i₀ j)
      _ = 1 := hQrow i₀
  have hcardpos : 0 < (Fintype.card V : ℝ) := by
    have hc : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ‹Nonempty V›
    exact_mod_cast hc
  have hprod : 0 < (Fintype.card V : ℝ) * δ :=
    mul_pos hcardpos hδpos
  have hρ : 0 ≤ 1 - (Fintype.card V : ℝ) * δ := by linarith
  have hρ' : 1 - (Fintype.card V : ℝ) * δ < 1 := by linarith
  -- the invariant pairing
  have hpair : ∀ t : ℕ, π ⬝ᵥ ((P ^ t) *ᵥ x) = π ⬝ᵥ x := by
    intro t
    rw [Matrix.dotProduct_mulVec, vecMul_pow_eq_of_vecMul_eq hπstat t]
  -- the per-entry decay bound
  have hbound : ∀ (t : ℕ) (i : V),
      |(P ^ t *ᵥ x) i - π ⬝ᵥ x| ≤
        (1 - (Fintype.card V : ℝ) * δ) ^ (t / m) * entryRange x := by
    intro t i
    have hteq : m * (t / m) + t % m = t := Nat.div_add_mod t m
    have hmemA : entryInf (P ^ t *ᵥ x) ≤ (P ^ t *ᵥ x) i := entryInf_le _ i
    have hmemB : (P ^ t *ᵥ x) i ≤ entrySup (P ^ t *ᵥ x) := le_entrySup _ i
    have hmemC : entryInf (P ^ t *ᵥ x) ≤ π ⬝ᵥ x := by
      have h := entryInf_le_dotProduct hπnn hπsum (P ^ t *ᵥ x)
      rwa [hpair t] at h
    have hmemD : π ⬝ᵥ x ≤ entrySup (P ^ t *ᵥ x) := by
      have h := dotProduct_le_entrySup hπnn hπsum (P ^ t *ᵥ x)
      rwa [hpair t] at h
    have hin : |(P ^ t *ᵥ x) i - π ⬝ᵥ x| ≤
        entrySup (P ^ t *ᵥ x) - entryInf (P ^ t *ᵥ x) := by
      rw [abs_le]
      constructor <;> linarith
    have hblock := entryRange_pow_mul_le hrow hδle (t / m)
      ((P ^ (t % m)) *ᵥ x)
    have hrem := entryRange_mulVec_le (pow_nonneg_entries hnn (t % m))
      (pow_row_sum hrow (t % m)) x
    calc |(P ^ t *ᵥ x) i - π ⬝ᵥ x| ≤ entryRange (P ^ t *ᵥ x) := hin
      _ = entryRange (P ^ (m * (t / m) + t % m) *ᵥ x) := by rw [hteq]
      _ = entryRange ((P ^ (m * (t / m)) * P ^ (t % m)) *ᵥ x) := by rw [pow_add]
      _ = entryRange ((P ^ (m * (t / m))) *ᵥ ((P ^ (t % m)) *ᵥ x)) := by
          rw [← Matrix.mulVec_mulVec]
      _ ≤ (1 - (Fintype.card V : ℝ) * δ) ^ (t / m) *
          entryRange ((P ^ (t % m)) *ᵥ x) := hblock
      _ ≤ (1 - (Fintype.card V : ℝ) * δ) ^ (t / m) * entryRange x :=
          mul_le_mul_of_nonneg_left hrem (pow_nonneg hρ _)
  -- the assembly
  refine tendsto_pi_nhds.mpr fun i => ?_
  have hcoord : ((π ⬝ᵥ x) • (1 : V → ℝ)) i = π ⬝ᵥ x := by simp
  rw [hcoord, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ℕ,
      (1 - (Fintype.card V : ℝ) * δ) ^ q₀ * entryRange x < ε := by
    rcases lt_or_eq_of_le (entryRange_nonneg x) with hDpos | hD0
    · obtain ⟨q, hq⟩ := exists_pow_lt_of_lt_one
        (show 0 < ε / entryRange x by positivity)
        (show 1 - (Fintype.card V : ℝ) * δ < 1 by linarith)
      exact ⟨q, (lt_div_iff₀ hDpos).mp hq⟩
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul, ← hD0]
      exact hε
  rw [Filter.eventually_atTop]
  refine ⟨m * q₀, fun t ht => ?_⟩
  have hdiv : q₀ ≤ t / m :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact ht)
  have hpow : (1 - (Fintype.card V : ℝ) * δ) ^ (t / m) ≤
      (1 - (Fintype.card V : ℝ) * δ) ^ q₀ :=
    pow_le_pow_of_le_one hρ (by linarith) hdiv
  have hle := hbound t i
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (le_trans hle
    (mul_le_mul_of_nonneg_right hpow (entryRange_nonneg x))) hq₀

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

/-- **Entrywise convergence** (the convergence theorem applied at the
basis vector): every column of `Pᵗ` converges to `π`
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
