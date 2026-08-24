import Scaffold.Mathlib.GraphTheory.IrreducibleStationary
import Scaffold.Mathlib.GraphTheory.Normalized

/-!
# PageRank: the teleportation-regularized walk — the second
Perron–Frobenius consumer

The second named consumer of the `perron_frobenius` admission
(2026-08-22). The first — `GraphTheory.IrreducibleStationary` (2026-08-24)
— proves the stationary theory of an *irreducible* walk and is honest
about it: its `hirr` hypothesis is load-bearing, and its own QA fence
exhibits a reducible network (two disjoint edges) whose raw walk has two
stationary distributions. PageRank is the classical repair of exactly
that failure: mix the walk `P = D⁻¹ A` with the uniform matrix —
the *Google matrix* `G i j = α * P i j + (1 - α) * (card V)⁻¹` — and
the teleportation term puts a positive floor in **every** entry, so `G`
is strictly positive and hence irreducible *unconditionally*. The
reducibility of the input, the obstruction that motivates the
construction, is thereby dissolved rather than assumed away: no
irreducibility hypothesis appears in any statement below.

**Trust boundary.** The three PageRank theorems
(`exists_pageRankVec`, `existsUnique_pageRankVec`, `pageRankVec_pos`)
are *conditional on the `perron_frobenius` axiom* — Lean-checked
deductions through the delivered consumer layer, never foundationally
proved. They make no new axiom contact: the two axiom applications
happen inside `IrreducibleStationary`'s engine; this module composes
that layer at the Google matrix through the row-stochasticity bridge
`walkTransitionMatrix_eq_of_row_sum_one` (a row-stochastic matrix is
its own walk transition matrix). Everything else here — the
teleportation floor, irreducibility, row sums, the bridge — is
unconditional hard crust.

## Statement shapes (recorded in `proposals/pagerank-distributions.md`)

- The damping range is `0 ≤ α < 1`, not `0 < α < 1`: at `α = 0` the
  matrix is the uniform one, itself strictly positive on a nonempty
  vertex type, so excluding it would understate the statement. Both
  endpoints are load-bearing and fenced in QA: at `α = 1` (no
  teleportation) uniqueness dies on reducible input, and at
  `α = -1` the mixture degenerates (on `K₂` to the identity) and
  uniqueness dies with it — while row stochasticity, being affine in
  `α`, survives both.
- `Nonempty V` is an instance hypothesis: on the empty type the
  teleportation weight `(card V)⁻¹` is `0⁻¹ = 0` and no distribution
  exists at all.
- Nothing about power iteration, rates, or mixing: geometric
  convergence of `π_{t+1} = π_t ᵥ* G` needs strict spectral dominance,
  which the axiom deliberately does not claim (the
  `strict_dominance_refuted_QA` imprimitivity fence). The rank-one
  update structure also makes `G`'s Perron root `1` with multiplicity
  structure the axiom does not pin down; those are separate future
  obligations, not smuggled in here.

## Source and conventions

The construction is Page–Brin–Motwani–Winograd's (Section 2 of the
1999 Stanford Digital Library tech report "The PageRank Citation
Ranking: Bringing Order to the Web"; section-level locator, pending
physical-copy verification like the other external locators). Their
convention is the *column*-stochastic web matrix with teleportation
`E = v vᵀ` for a personalization vector `v`; this module states the
transposed convention — the shelf's row-stochastic
`walkTransitionMatrix` with uniform teleportation — so the stationary
vector proved here is the left eigenvector at eigenvalue `1`, i.e. the
PageRank vector of the column form at uniform personalization. The
mathematical content (the Perron–Frobenius application) is Horn &
 Johnson, "Matrix Analysis", 2nd ed., Theorem 8.4.4, cited through the
axiom's own record.

QA: exercised by `Scaffold.QA.SpectralGraph.PageRank_QA.*` (the
reducible-fixture instantiation with the uniform hand value, the
asymmetric-fixture PageRank with its raw verification, and both
endpoint fences).

Delivered 2026-08-24 (`proposals/pagerank-distributions.md`).
-/

open scoped Matrix

namespace SpectralGraphTheory

open Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The Google (teleportation-regularized) walk matrix: the walk
transition matrix `P = D⁻¹ A` of `A` mixed with the uniform matrix,
entry form `G i j = α * P i j + (1 - α) * (card V)⁻¹`. The
teleportation weight `(1 - α)` spread uniformly over the vertex type is
the Page–Brin damping construction; the entry form (not the
outer-product form) is deliberate — QA pins entries at literal indices
and the floor inequality `0 < G i j` is read off entrywise.
Noncomputable because `walkTransitionMatrix` is. -/
noncomputable def googleMatrix (A : WAdj (V := V)) (α : ℝ) : Matrix V V ℝ :=
  Matrix.of fun i j => α * walkTransitionMatrix A i j + (1 - α) * (Fintype.card V : ℝ)⁻¹

/-- Entry form of the Google matrix:
`G i j = α * P i j + (1 - α) * (card V)⁻¹`. The pin-level interface
every entry computation consumes. -/
theorem googleMatrix_apply (A : WAdj (V := V)) (α : ℝ) (i j : V) :
    googleMatrix A α i j =
      α * walkTransitionMatrix A i j + (1 - α) * (Fintype.card V : ℝ)⁻¹ := rfl

/-- The walk transition matrix of a nonnegative network with positive
out-degrees is nonnegative: positive row scaling preserves the sign
pattern. Unconditional hard crust (the entry-form reading of what
`IrreducibleStationary`'s engine proves inline); the floor hypothesis
of every `googleMatrix_*` sign statement consumes it. -/
theorem walkTransitionMatrix_nonneg (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (hdeg : ∀ i, 0 < deg A i) (i j : V) :
    0 ≤ walkTransitionMatrix A i j := by
  rw [walkTransitionMatrix_apply]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt (hdeg i))) (hnn i j)

/-- The Google matrix is nonnegative on the damping window `[0, 1]`:
both summands of the entry form are nonnegative there. Unconditional
hard crust; the hypothesis form under which the consumer layer's
`hnn` is discharged. -/
theorem googleMatrix_nonneg (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (hdeg : ∀ i, 0 < deg A i) {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 1) (i j : V) :
    0 ≤ googleMatrix A α i j := by
  rw [googleMatrix_apply]
  exact add_nonneg
    (mul_nonneg hα (walkTransitionMatrix_nonneg A hnn hdeg i j))
    (mul_nonneg (by linarith) (inv_nonneg.mpr (Nat.cast_nonneg _)))

/-- **The teleportation floor** (the construction's entire content):
on the damping window `[0, 1)` with nonempty vertex type, *every*
entry of the Google matrix is strictly positive — regardless of the
input walk's support, reducibility, or asymmetry. The floor is the
additive weight `(1 - α) * (card V)⁻¹ > 0`; no hypothesis on `A`
beyond nonnegativity and positive out-degrees appears. Unconditional
hard crust, and the engine of `googleMatrix_isIrreducible`.

QA: exercised by `Scaffold.QA.SpectralGraph.PageRank_QA.*` (the raw
floor pins at zero-support pairs). -/
theorem googleMatrix_pos (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (hdeg : ∀ i, 0 < deg A i) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1)
    [Nonempty V] (i j : V) :
    0 < googleMatrix A α i j := by
  rw [googleMatrix_apply]
  have h1 : 0 ≤ α * walkTransitionMatrix A i j :=
    mul_nonneg hα (walkTransitionMatrix_nonneg A hnn hdeg i j)
  have h2 : 0 < (1 - α) * (Fintype.card V : ℝ)⁻¹ := by
    have hc : 0 < Fintype.card V := Fintype.card_pos
    exact mul_pos (by linarith) (inv_pos.mpr (Nat.cast_pos.mpr hc))
  linarith

/-- Row stochasticity of the Google matrix — for **every** real `α`:
the row sum is `α * 1 + (1 - α) * 1 = 1`, affine in `α` and so valid
at both fence endpoints (`α = 1` and `α = -1`), where positivity and
uniqueness die but this does not. Unconditional hard crust on nonempty
`V`; supplies `deg (googleMatrix A α) i = 1` and, through the bridge,
the row-sum hypothesis of `walkTransitionMatrix_eq_of_row_sum_one`.

QA: exercised by `Scaffold.QA.SpectralGraph.PageRank_QA.*` (raw row
sums and the fence instantiations). -/
theorem googleMatrix_row_sum (A : WAdj (V := V)) (hdeg : ∀ i, 0 < deg A i)
    (α : ℝ) [Nonempty V] (i : V) :
    ∑ j, googleMatrix A α i j = 1 := by
  have hc : 0 < Fintype.card V := Fintype.card_pos
  have hnne : (Fintype.card V : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hc)
  have hsum : ∑ j : V, ((Fintype.card V : ℝ)⁻¹) = 1 := by
    have hone : ∑ j : V, (1 : ℝ) = (Fintype.card V : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Nat.smul_one_eq_cast]
    have h1 : ∑ j : V, ((Fintype.card V : ℝ)⁻¹)
        = ((Fintype.card V : ℝ)⁻¹) * (Fintype.card V : ℝ) := by
      rw [← hone, Finset.mul_sum]
      simp
    rw [h1, inv_mul_cancel₀ hnne]
  simp only [googleMatrix_apply, Finset.sum_add_distrib, ← Finset.mul_sum,
    walkTransitionMatrix_row_sum A hdeg i, hsum]
  ring

/-- The Google matrix has all degrees one (its row sums are one), so
the consumer layer's positive-degree hypothesis is discharged at it
unconditionally. -/
theorem googleMatrix_deg_eq_one (A : WAdj (V := V)) (hdeg : ∀ i, 0 < deg A i)
    (α : ℝ) [Nonempty V] (i : V) :
    deg (googleMatrix A α) i = 1 := by
  simp only [deg]
  exact googleMatrix_row_sum A hdeg α i

/-- **Irreducibility of the Google matrix is derived, not assumed** —
the entire point of the construction. The teleportation floor makes
every entry positive, so every pair of vertices is one directed arc
apart in the support digraph: strong connectivity by
`ReflTransGen.single` at each pair. No hypothesis on `A` beyond
nonnegativity and positive out-degrees — the input may be reducible,
disconnected, asymmetric. Unconditional hard crust.

QA: exercised by `Scaffold.QA.SpectralGraph.PageRank_QA.*` (the
reducible-fixture instantiation, where the input walk's own
irreducibility provably fails). -/
theorem googleMatrix_isIrreducible (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (hdeg : ∀ i, 0 < deg A i) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1)
    [Nonempty V] :
    (googleMatrix A α).IsIrreducible := by
  intro i j
  exact Relation.ReflTransGen.single (googleMatrix_pos A hnn hdeg hα hα' i j)

/-- **The row-stochasticity bridge**: any matrix whose rows all sum to
one is its own walk transition matrix (`D⁻¹ M = M` when every degree is
`1`). This is the composition point between the delivered
irreducible-stationary layer — stated at `walkTransitionMatrix A` —
and any row-stochastic matrix; the Google matrix is the first
consumer, not the only possible one. Unconditional hard crust.

QA: exercised by `Scaffold.QA.SpectralGraph.PageRank_QA.*`. -/
theorem walkTransitionMatrix_eq_of_row_sum_one (M : Matrix V V ℝ)
    (hrow : ∀ i, ∑ j, M i j = 1) :
    walkTransitionMatrix M = M := by
  apply Matrix.ext
  intro i j
  rw [walkTransitionMatrix_apply, show deg M i = 1 from hrow i, inv_one, one_mul]

/-- **Existence of the PageRank distribution** (conditional on
`perron_frobenius`): every nonnegative network with positive
out-degrees — reducible or not, asymmetric or not — has a stationary
distribution for its teleportation-regularized walk `π ᵥ* G = π` that
is strictly positive and normalized to total mass one. Composition:
the consumer layer's existence theorem at the Google matrix, whose
irreducibility is the teleportation floor's, translated through the
row-stochasticity bridge.

QA: exercised by `Scaffold.QA.SpectralGraph.PageRank_QA.*` (the
reducible fixture and the asymmetric star, hand values verified
raw). -/
theorem exists_pageRankVec (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (hdeg : ∀ i, 0 < deg A i) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1)
    [Nonempty V] :
    ∃ π : V → ℝ, (∀ i, 0 < π i) ∧ (∑ i, π i = 1) ∧
      π ᵥ* googleMatrix A α = π := by
  have hex' : ∃ i j, 0 < googleMatrix A α i j :=
    ⟨Classical.arbitrary V, Classical.arbitrary V,
      googleMatrix_pos A hnn hdeg hα hα' _ _⟩
  have hdeg' : ∀ i, 0 < deg (googleMatrix A α) i := by
    intro i
    rw [googleMatrix_deg_eq_one A hdeg α i]
    norm_num
  obtain ⟨π, hπpos, hπsum, hπs⟩ :=
    exists_stationaryVec_of_irreducible (googleMatrix A α)
      (fun i j => googleMatrix_nonneg A hnn hdeg hα (le_of_lt hα') i j)
      (googleMatrix_isIrreducible A hnn hdeg hα hα') hex' hdeg'
  have hb : walkTransitionMatrix (googleMatrix A α) = googleMatrix A α :=
    walkTransitionMatrix_eq_of_row_sum_one _ (fun i => googleMatrix_row_sum A hdeg α i)
  refine ⟨π, hπpos, hπsum, ?_⟩
  rw [hb] at hπs
  exact hπs

/-- **The PageRank distribution exists and is unique** (conditional on
`perron_frobenius`): there is exactly one nonnegative mass-one vector
fixed by the Google walk `π ᵥ* G = π` — **with no irreducibility
hypothesis on the input network**. This is the statement the raw walk
cannot support: on reducible input the raw stationary distributions
are non-unique (the `IrreducibleStationary_QA` reducibility fence
exhibits two), and the teleportation floor is precisely what restores
uniqueness. Uniqueness is among nonnegative distributions, with strict
positivity derived (`pageRankVec_pos`).

QA: exercised — and its endpoint hypothesis-free forms *refuted* in
proved form at `α = 1` (reducible fixture, teleportation removed) and
`α = -1` (`K₂`, identity degeneration) — by
`Scaffold.QA.SpectralGraph.PageRank_QA.*`. -/
theorem existsUnique_pageRankVec (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (hdeg : ∀ i, 0 < deg A i) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1)
    [Nonempty V] :
    ∃! π : V → ℝ, (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧
      π ᵥ* googleMatrix A α = π := by
  have hex' : ∃ i j, 0 < googleMatrix A α i j :=
    ⟨Classical.arbitrary V, Classical.arbitrary V,
      googleMatrix_pos A hnn hdeg hα hα' _ _⟩
  have hdeg' : ∀ i, 0 < deg (googleMatrix A α) i := by
    intro i
    rw [googleMatrix_deg_eq_one A hdeg α i]
    norm_num
  obtain ⟨π, ⟨hπ1, hπ2, hπ3⟩, huniq⟩ :=
    existsUnique_stationaryVec_of_irreducible (googleMatrix A α)
      (fun i j => googleMatrix_nonneg A hnn hdeg hα (le_of_lt hα') i j)
      (googleMatrix_isIrreducible A hnn hdeg hα hα') hex' hdeg'
  have hb : walkTransitionMatrix (googleMatrix A α) = googleMatrix A α :=
    walkTransitionMatrix_eq_of_row_sum_one _ (fun i => googleMatrix_row_sum A hdeg α i)
  rw [hb] at hπ3
  refine ⟨π, ⟨hπ1, hπ2, hπ3⟩, ?_⟩
  intro τ hτ
  refine huniq τ ⟨hτ.1, hτ.2.1, ?_⟩
  rw [hb]
  exact hτ.2.2

/-- **Full support: no stationary vector of the Google walk can vanish
anywhere** (conditional on `perron_frobenius`). Every nonzero
nonnegative vector fixed by `π ᵥ* G = π` is strictly positive — the
teleportation floor's trace on the stationary distribution: even a
vertex with no inbound walk arcs receives teleportation mass.

QA: exercised by `Scaffold.QA.SpectralGraph.PageRank_QA.*`. -/
theorem pageRankVec_pos (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (hdeg : ∀ i, 0 < deg A i) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1)
    [Nonempty V] {σ : V → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hσ0 : σ ≠ 0)
    (hσs : σ ᵥ* googleMatrix A α = σ) : ∀ i, 0 < σ i := by
  have hex' : ∃ i j, 0 < googleMatrix A α i j :=
    ⟨Classical.arbitrary V, Classical.arbitrary V,
      googleMatrix_pos A hnn hdeg hα hα' _ _⟩
  have hdeg' : ∀ i, 0 < deg (googleMatrix A α) i := by
    intro i
    rw [googleMatrix_deg_eq_one A hdeg α i]
    norm_num
  have hb : walkTransitionMatrix (googleMatrix A α) = googleMatrix A α :=
    walkTransitionMatrix_eq_of_row_sum_one _ (fun i => googleMatrix_row_sum A hdeg α i)
  exact stationaryVec_pos_of_irreducible (googleMatrix A α)
    (fun i j => googleMatrix_nonneg A hnn hdeg hα (le_of_lt hα') i j)
    (googleMatrix_isIrreducible A hnn hdeg hα hα') hex' hdeg' hσ hσ0 (by
      rw [hb]
      exact hσs)

end SpectralGraphTheory
