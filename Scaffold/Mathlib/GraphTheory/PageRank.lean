import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Scaffold.Mathlib.GraphTheory.IrreducibleStationary
import Scaffold.Mathlib.GraphTheory.Normalized
import Scaffold.Mathlib.LinearAlgebra.PrimitiveConvergence

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

**Hard crust since 2026-09-02**
(`proposals/cesaro-stationary-existence.md`): the three PageRank
theorems (`exists_pageRankVec`, `existsUnique_pageRankVec`,
`pageRankVec_pos`) are *proved* with no axiom contact — the
`IrreducibleStationary` engine they compose through was re-proved that
day by the Cesàro/power-positivity/min-ratio route, and this module
composes that layer at the Google matrix through the row-stochasticity
bridge `walkTransitionMatrix_eq_of_row_sum_one` (a row-stochastic
matrix is its own walk transition matrix). Everything here — the
teleportation floor, irreducibility, row sums, the bridge, and now the
stationary conclusions — is unconditional hard crust.

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
  a genuinely spectral statement outside the elementary
  Cesàro/power-positivity route (the
  `strict_dominance_refuted_QA` imprimitivity fence in the
  Perron–Frobenius QA records why no such clause is free). The rank-one
  update structure also makes `G`'s Perron root `1` with multiplicity
  structure no delivered theorem pins down; those are separate future
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

/-- **Existence of the PageRank distribution** (hard crust since
2026-09-02, formerly conditional on `perron_frobenius`): every
nonnegative network with positive
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

/-- **The PageRank distribution exists and is unique** (hard crust
since 2026-09-02, formerly conditional on `perron_frobenius`): there
is exactly one nonnegative mass-one vector
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
anywhere** (hard crust since 2026-09-02, formerly conditional on
`perron_frobenius`). Every nonzero
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


section SpectralCeiling

/-!
### The spectral ceiling — the sharp `|λ₂| = α` layer, Slice 1

The Google matrix's off-one left spectrum is controlled by the damping
coefficient: every left eigenvalue `c ≠ 1` obeys `|c| ≤ α`
(Haveliwala–Kamvar's inequality half, `proposals/
sharp-second-eigenvalue-layer.md`, 2026-09-06). All statements at the
vecMul level — the shelf's stationarity convention — so no eigen-API
is needed. The mechanism: the mass lemma (row-stochastic mass
bookkeeping forces zero mass at `c ≠ 1`), the shadow lemma (the
teleportation term cannot see mass-zero vectors, so G's off-one
left-eigenvectors ARE the walk matrix's mass-zero left-eigenvectors
with eigenvalues scaled by `1/α`), the ℓ¹ peripheral bound (the left
action of a nonnegative row-stochastic matrix contracts the absolute
sum), and the attainment twin (conversely, a mass-zero walk
left-eigenpair maps to a Google left-eigenpair at `α · c'` — the
equality half at the eigenvector level, what the periodic-fixture QA
pins attain).

Sources:
- T. H. Haveliwala and S. Kamvar, "The Second Eigenvalue of the
  Google Matrix", Stanford Digital Library tech report 2003-20
  (2003) — the α-control statement; our ceiling is the inequality
  half at the eigenvector level, with the teleportation-mass
  mechanism in place of their rank-one spectral analysis.

QA: the eigen-equation pins at the two-cycle fixture in
`Scaffold.QA.SpectralGraph.PageRank_QA.lean` (Section Spectral).
-/

section CeilingSpike

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The mass lemma**: a left eigenvector of the Google matrix at an
eigenvalue `c ≠ 1` has zero total mass. -/
theorem googleMatrix_vecMul_mass_zero (A : WAdj (V := V))
    (hdeg : ∀ i, 0 < deg A i) (α : ℝ) [Nonempty V]
    (μ : V → ℝ) {c : ℝ} (hμ : μ ᵥ* googleMatrix A α = c • μ)
    (hc : c ≠ 1) :
    ∑ i, μ i = 0 := by
  have hmass : ∑ j, (μ ᵥ* googleMatrix A α) j = ∑ j, μ j := by
    simp only [Matrix.vecMul, Matrix.dotProduct]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, googleMatrix_row_sum A hdeg α i, mul_one]
  have hL : ∑ j, (c • μ) j = ∑ j, (μ ᵥ* googleMatrix A α) j := by
    rw [hμ]
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hL
  rw [hmass] at hL
  have hz : (c - 1) * ∑ j, μ j = 0 := by nlinarith [hL]
  rcases mul_eq_zero.1 hz with h | h
  · exact absurd h (sub_ne_zero.2 hc)
  · exact h

/-- **The shadow lemma**: with zero mass, the teleportation term
vanishes from the left action, and the eigen-equation collapses to
the walk matrix's — G's off-one left-eigenvectors ARE P's mass-zero
left-eigenvectors, eigenvalues scaled by `1/α`. -/
theorem googleMatrix_vecMul_shadow (A : WAdj (V := V))
    (hdeg : ∀ i, 0 < deg A i) {α : ℝ} (hα : α ≠ 0) [Nonempty V]
    (μ : V → ℝ) {c : ℝ} (hμ : μ ᵥ* googleMatrix A α = c • μ)
    (hc : c ≠ 1) :
    μ ᵥ* walkTransitionMatrix A = (c / α) • μ := by
  have hmass := googleMatrix_vecMul_mass_zero A hdeg α μ hμ hc
  funext j
  have hentry : (μ ᵥ* googleMatrix A α) j
      = α * (μ ᵥ* walkTransitionMatrix A) j
        + (1 - α) * (Fintype.card V : ℝ)⁻¹ * ∑ i, μ i := by
    simp only [Matrix.vecMul, Matrix.dotProduct, googleMatrix_apply]
    rw [Finset.sum_congr rfl (fun i _ => show μ i * (α * walkTransitionMatrix A i j
        + (1 - α) * (Fintype.card V : ℝ)⁻¹)
        = α * (μ i * walkTransitionMatrix A i j)
          + (1 - α) * (Fintype.card V : ℝ)⁻¹ * μ i from by ring),
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : α * (μ ᵥ* walkTransitionMatrix A) j = c * μ j := by
    have hJ := congrFun hμ j
    rw [hentry, hmass, mul_zero, add_zero, Pi.smul_apply, smul_eq_mul] at hJ
    linarith
  have h2 : (c / α) * μ j = (μ ᵥ* walkTransitionMatrix A) j := by
    field_simp
    linarith [h1]
  simpa [Pi.smul_apply, smul_eq_mul] using h2.symm

omit [DecidableEq V] in
/-- **The ℓ¹ peripheral bound**: a nonzero left eigenvector of a
nonnegative row-stochastic matrix has `|c| ≤ 1` — the left action
contracts the absolute sum. -/
theorem abs_vecMulEigen_le_one {M : Matrix V V ℝ}
    (hnn : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j = 1)
    (μ : V → ℝ) (hμ0 : μ ≠ 0) {c : ℝ}
    (hμ : μ ᵥ* M = c • μ) :
    |c| ≤ 1 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, μ i₀ ≠ 0 := by
    by_contra hcon
    exact hμ0 (funext fun i => by
      by_contra hne
      exact hcon ⟨i, hne⟩)
  have hpos : (0 : ℝ) < ∑ i, |μ i| :=
    Finset.sum_pos' (fun i _ => abs_nonneg _)
      ⟨i₀, Finset.mem_univ i₀, abs_pos.2 hi₀⟩
  have hL : |c| * ∑ i, |μ i| = ∑ j, |(μ ᵥ* M) j| := by
    rw [Finset.mul_sum, hμ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  have hle : ∑ j, |(μ ᵥ* M) j| ≤ ∑ i, |μ i| := by
    calc ∑ j, |(μ ᵥ* M) j| ≤ ∑ j, ∑ i, |μ i| * M i j := by
          refine Finset.sum_le_sum fun j _ => ?_
          simp only [Matrix.vecMul, Matrix.dotProduct]
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, abs_of_nonneg (hnn i j)]
      _ = ∑ i, ∑ j, |μ i| * M i j := Finset.sum_comm
      _ = ∑ i, |μ i| * ∑ j, M i j :=
          Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ i, |μ i| := by simp [hrow]
  have hfin := hL.trans_le hle
  rcases le_total 0 c with hc0 | hc0
  · rw [abs_of_nonneg hc0] at hfin ⊢
    nlinarith [hpos]
  · rw [abs_of_nonpos hc0] at hfin ⊢
    nlinarith [hpos]

/-- **The spectral ceiling** — Haveliwala–Kamvar's inequality half:
every left eigenvalue `c ≠ 1` of the Google matrix obeys
`|c| ≤ α`. -/
theorem googleMatrix_abs_eigen_le (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) [Nonempty V]
    (μ : V → ℝ) (hμ0 : μ ≠ 0) {c : ℝ}
    (hμ : μ ᵥ* googleMatrix A α = c • μ) (hc : c ≠ 1) :
    |c| ≤ α := by
  have hshadow := googleMatrix_vecMul_shadow A hdeg (ne_of_gt hα) μ hμ hc
  have hP := abs_vecMulEigen_le_one
    (walkTransitionMatrix_nonneg A hnn hdeg) (walkTransitionMatrix_row_sum A hdeg)
    μ hμ0 hshadow
  calc |c| = α * |c / α| := by
        rw [abs_div, abs_of_pos hα]
        field_simp
    _ ≤ α * 1 := mul_le_mul_of_nonneg_left hP (le_of_lt hα)
    _ = α := mul_one _

/-- **The attainment twin**: conversely, a mass-zero left-eigenpair of
the walk matrix is a left-eigenpair of the Google matrix at the
damped eigenvalue `α · c'` — the teleportation term cannot see
mass-zero vectors. -/
theorem googleMatrix_vecMul_of_shadow (A : WAdj (V := V))
    (α : ℝ) [Nonempty V]
    (μ : V → ℝ) {c' : ℝ} (hmass : ∑ i, μ i = 0)
    (hμ : μ ᵥ* walkTransitionMatrix A = c' • μ) :
    μ ᵥ* googleMatrix A α = (α * c') • μ := by
  funext j
  have hentry : (μ ᵥ* googleMatrix A α) j
      = α * (μ ᵥ* walkTransitionMatrix A) j
        + (1 - α) * (Fintype.card V : ℝ)⁻¹ * ∑ i, μ i := by
    simp only [Matrix.vecMul, Matrix.dotProduct, googleMatrix_apply]
    rw [Finset.sum_congr rfl (fun i _ => show μ i * (α * walkTransitionMatrix A i j
        + (1 - α) * (Fintype.card V : ℝ)⁻¹)
        = α * (μ i * walkTransitionMatrix A i j)
          + (1 - α) * (Fintype.card V : ℝ)⁻¹ * μ i from by ring),
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hentry, hmass, mul_zero, add_zero, hμ, Pi.smul_apply, smul_eq_mul,
    Pi.smul_apply, smul_eq_mul]
  ring

end CeilingSpike

/-- **The eigenvector-level ceiling** — Slice 1's statement lifted to
the eigen-API through the definitional `vecMulLinear` bridge. -/
theorem googleMatrix_hasEigenvector_abs_le (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) [Nonempty V] {c : ℝ} {μ : V → ℝ}
    (hμ : Module.End.HasEigenvector (googleMatrix A α).vecMulLinear c μ)
    (hc : c ≠ 1) :
    |c| ≤ α := by
  have hne : μ ≠ 0 := (Module.End.hasEigenvector_iff.1 hμ).2
  have hEq : μ ᵥ* googleMatrix A α = c • μ := by
    have := Module.End.HasEigenvector.apply_eq_smul hμ
    simpa [Matrix.vecMulLinear_apply] using this
  exact googleMatrix_abs_eigen_le A hnn hdeg hα μ hne hEq hc

/-- **The eigenvalue-level ceiling** — Haveliwala–Kamvar's inequality
half in Mathlib's eigen-API. -/
theorem googleMatrix_hasEigenvalue_abs_le (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) [Nonempty V] {c : ℝ}
    (hc : Module.End.HasEigenvalue (googleMatrix A α).vecMulLinear c)
    (h1 : c ≠ 1) :
    |c| ≤ α := by
  obtain ⟨μ, hμ⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hc
  exact googleMatrix_hasEigenvector_abs_le A hnn hdeg hα hμ h1

/-- **The eigen-level shadow**: an eigenvector of the Google matrix at
`c ≠ 1` is an eigenvector of the walk matrix at `c/α`. -/
theorem googleMatrix_hasEigenvector_shadow (A : WAdj (V := V))
    (hdeg : ∀ i, 0 < deg A i) {α : ℝ} (hα : α ≠ 0) [Nonempty V]
    {c : ℝ} {μ : V → ℝ}
    (hμ : Module.End.HasEigenvector (googleMatrix A α).vecMulLinear c μ)
    (hc : c ≠ 1) :
    Module.End.HasEigenvector (walkTransitionMatrix A).vecMulLinear (c / α) μ := by
  have hne : μ ≠ 0 := (Module.End.hasEigenvector_iff.1 hμ).2
  have hEq : μ ᵥ* googleMatrix A α = c • μ := by
    have := Module.End.HasEigenvector.apply_eq_smul hμ
    simpa [Matrix.vecMulLinear_apply] using this
  refine Module.End.hasEigenvector_iff.2 ⟨?_, hne⟩
  have hshadow := googleMatrix_vecMul_shadow A hdeg hα μ hEq hc
  simpa [Matrix.vecMulLinear_apply] using hshadow

/-- **The eigen-level attainment twin**: a mass-zero eigenvector of
the walk matrix at `c'` is an eigenvector of the Google matrix at
`α · c'`. -/
theorem googleMatrix_hasEigenvector_of_shadow (A : WAdj (V := V))
    (α : ℝ) [Nonempty V] {c' : ℝ} {μ : V → ℝ}
    (hmass : ∑ i, μ i = 0) (hne : μ ≠ 0)
    (hμ : Module.End.HasEigenvector (walkTransitionMatrix A).vecMulLinear c' μ) :
    Module.End.HasEigenvector (googleMatrix A α).vecMulLinear (α * c') μ := by
  have hEq : μ ᵥ* walkTransitionMatrix A = c' • μ := by
    have := Module.End.HasEigenvector.apply_eq_smul hμ
    simpa [Matrix.vecMulLinear_apply] using this
  refine Module.End.hasEigenvector_iff.2 ⟨?_, hne⟩
  have htwin := googleMatrix_vecMul_of_shadow A α μ hmass hEq
  simpa [Matrix.vecMulLinear_apply] using htwin

end SpectralCeiling

section Strictness

/-!
### The strictness layer — the sharp `|λ₂| = α` layer, Slice 5

The ceiling's strict half: on a primitive walk (aperiodic chain) every
off-one Google left-eigenvalue is STRICTLY inside the α-disk
(`proposals/sharp-second-eigenvalue-layer.md`, 2026-09-06). The route
is the peripheral argument, elementary over ℝ — no Perron–Frobenius,
no complex spectral theory: a peripheral (`|c| = 1`) mass-zero
left-eigenvector of a matrix with a strictly positive power has all
entries weakly of one sign (equality in the ℓ¹ contraction forces
equality in the triangle inequality at every column, and a strictly
positive column of weights forces a common sign), so zero mass forces
the zero vector. The equality `|c| = α` is therefore attainable only
through periodic chains — exactly where Slice 1's QA pinned it
(the two-cycle's `-α` pair), and primitivity is what excludes them.

Sources:
- T. H. Haveliwala and S. Kamvar, "The Second Eigenvalue of the
  Google Matrix", Stanford Digital Library tech report 2003-20
  (2003) — the strictness statement for aperiodic chains; our route
  is the peripheral-eigenvector argument at the vecMul level, not
  their rank-one spectral decomposition.

QA: the strictness pins at the fresh primitive two-vertex fixture and
the primitivity-necessity fence at the periodic two-cycle in
`Scaffold.QA.SpectralGraph.PageRank_QA.lean` (Section Strictness).
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Engine 1**: a left-eigenvector of `M` is a left-eigenvector of
every power, at the powered eigenvalue. -/
theorem vecMul_pow_smul_eq {M : Matrix V V ℝ} {μ : V → ℝ} {c : ℝ}
    (hμ : μ ᵥ* M = c • μ) (n : ℕ) : μ ᵥ* M ^ n = c ^ n • μ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.vecMul_vecMul, ih, Matrix.vecMul_smul, hμ,
        smul_smul, ← pow_succ]

/-- **The peripheral sign-rigidity engine**: on a nonnegative
row-stochastic matrix with a strictly positive power, a peripheral
(`|c| = 1`) left-eigenvector has all entries weakly of one sign — the
equality case of the ℓ¹ contraction forces equality in the triangle
inequality at every column, and a strictly positive column of weights
then forces a common sign (Horn–Johnson primitivity's companion
mechanism, proved elementarily over ℝ). -/
theorem vecMul_sign_coherent_of_abs_eq_pow_pos {M : Matrix V V ℝ}
    (hrow : ∀ i, ∑ j, M i j = 1) {k : ℕ}
    (hk : ∀ i j, 0 < (M ^ k) i j) {μ : V → ℝ} {c : ℝ}
    (hμ : μ ᵥ* M = c • μ) (hc : |c| = 1) [Nonempty V] :
    (∀ i, 0 ≤ μ i) ∨ (∀ i, μ i ≤ 0) := by
  have hnnk : ∀ i j, 0 ≤ (M ^ k) i j := fun i j => le_of_lt (hk i j)
  have hrowk : ∀ i, ∑ j, (M ^ k) i j = 1 := Scaffold.LinearAlgebra.pow_row_sum hrow k
  have hμk : μ ᵥ* M ^ k = c ^ k • μ := vecMul_pow_smul_eq hμ k
  have hck : |c ^ k| = 1 := by rw [abs_pow, hc, one_pow]
  -- The ℓ¹ chain: both ends compute to the same absolute sum.
  have hL1 : ∑ j, |(μ ᵥ* M ^ k) j| = ∑ j, |μ j| := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hμk, Pi.smul_apply, smul_eq_mul, abs_mul, hck, one_mul]
  have hR1 : ∑ j, ∑ i, |μ i| * (M ^ k) i j = ∑ i, |μ i| := by
    calc ∑ j, ∑ i, |μ i| * (M ^ k) i j = ∑ i, ∑ j, |μ i| * (M ^ k) i j :=
          Finset.sum_comm
      _ = ∑ i, |μ i| * ∑ j, (M ^ k) i j :=
          Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ i, |μ i| := by simp [hrowk]
  -- Pointwise equality in the triangle bound.
  have hle : ∀ j, |(μ ᵥ* M ^ k) j| ≤ ∑ i, |μ i| * (M ^ k) i j := by
    intro j
    simp only [Matrix.vecMul, Matrix.dotProduct]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum fun i _ => by rw [abs_mul, abs_of_nonneg (hnnk i j)]
  have hzsum : ∑ j, ((∑ i, |μ i| * (M ^ k) i j) - |(μ ᵥ* M ^ k) j|) = 0 := by
    have hsplit : ∑ j, ((∑ i, |μ i| * (M ^ k) i j) - |(μ ᵥ* M ^ k) j|)
        = (∑ j, ∑ i, |μ i| * (M ^ k) i j) - ∑ j, |(μ ᵥ* M ^ k) j| :=
      Finset.sum_sub_distrib
    have hsum : ∑ j, ∑ i, |μ i| * (M ^ k) i j = ∑ j, |(μ ᵥ* M ^ k) j| :=
      hR1.trans hL1.symm
    rw [hsplit, hsum, sub_self]
  have hptw : ∀ j, |(μ ᵥ* M ^ k) j| = ∑ i, |μ i| * (M ^ k) i j := by
    intro j
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sub_nonneg.2 (hle j))).1 hzsum j (Finset.mem_univ j)
    exact (sub_eq_zero.1 hterm).symm
  -- Two-case sign extraction at one column.
  obtain ⟨j₀⟩ : Nonempty V := ‹_›
  have hcol := hptw j₀
  simp only [Matrix.vecMul, Matrix.dotProduct] at hcol
  rcases le_total 0 (∑ i, μ i * (M ^ k) i j₀) with hS | hS
  · refine Or.inl fun i => ?_
    rw [abs_of_nonneg hS] at hcol
    have hz : ∑ j, (|μ j| - μ j) * (M ^ k) j j₀ = 0 := by
      have hsplit : ∑ j, (|μ j| - μ j) * (M ^ k) j j₀
          = (∑ i, |μ i| * (M ^ k) i j₀) - ∑ i, μ i * (M ^ k) i j₀ := by
        simp only [sub_mul]
        rw [Finset.sum_sub_distrib]
      rw [hsplit, hcol, sub_self]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (sub_nonneg.2 (le_abs_self (μ j))) (hnnk j j₀))).1 hz i
      (Finset.mem_univ i)
    rcases mul_eq_zero.1 hterm with h | h
    · exact abs_eq_self.1 (sub_eq_zero.1 h)
    · exact absurd h (ne_of_gt (hk i j₀))
  · refine Or.inr fun i => ?_
    rw [abs_of_nonpos hS] at hcol
    have hz : ∑ j, (|μ j| + μ j) * (M ^ k) j j₀ = 0 := by
      have hsplit : ∑ j, (|μ j| + μ j) * (M ^ k) j j₀
          = (∑ i, |μ i| * (M ^ k) i j₀) + ∑ i, μ i * (M ^ k) i j₀ := by
        simp only [add_mul]
        rw [Finset.sum_add_distrib]
      rw [hsplit, ← hcol, neg_add_cancel]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (by linarith [neg_le_abs (μ j)]) (hnnk j j₀))).1 hz i
      (Finset.mem_univ i)
    rcases mul_eq_zero.1 hterm with h | h
    · have hnegeq : |μ i| = -μ i := eq_neg_of_add_eq_zero_left h
      have hmu : μ i = -|μ i| := by linarith
      linarith [abs_nonneg (μ i)]
    · exact absurd h (ne_of_gt (hk i j₀))

/-- **The strictness theorem** — Haveliwala–Kamvar's strict half: on a
walk whose transition matrix has a strictly positive power (a primitive
/ aperiodic chain), every off-one Google left-eigenvalue is STRICTLY
inside the α-disk — the ceiling's equality case is attainable only
through periodic chains. -/
theorem googleMatrix_abs_eigen_lt_of_pow_pos (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) [Nonempty V] {k : ℕ}
    (hk : ∀ i j, 0 < ((walkTransitionMatrix A) ^ k) i j)
    (μ : V → ℝ) (hμ0 : μ ≠ 0) {c : ℝ}
    (hμ : μ ᵥ* googleMatrix A α = c • μ) (hc : c ≠ 1) :
    |c| < α := by
  have hmass := googleMatrix_vecMul_mass_zero A hdeg α μ hμ hc
  have hshadow := googleMatrix_vecMul_shadow A hdeg (ne_of_gt hα) μ hμ hc
  have hceil := googleMatrix_abs_eigen_le A hnn hdeg hα μ hμ0 hμ hc
  by_contra hlt
  have heq : |c| = α := le_antisymm hceil (not_lt.1 hlt)
  have hperiph : |c / α| = 1 := by
    rw [abs_div, abs_of_pos hα, div_eq_iff (ne_of_gt hα), heq, one_mul]
  rcases vecMul_sign_coherent_of_abs_eq_pow_pos
    (walkTransitionMatrix_row_sum A hdeg) hk hshadow hperiph with
    hpos | hpos
  · have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hpos i)).1 hmass
    exact hμ0 (funext fun i => hz i (Finset.mem_univ i))
  · have hzero : ∑ i, -μ i = 0 := by
      have hnz : ∑ i, -μ i = -∑ i, μ i := Finset.sum_neg_distrib
      rw [hnz, hmass, neg_zero]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => neg_nonneg.2 (hpos i))).1 hzero
    exact hμ0 (funext fun i => neg_eq_zero.1 (hz i (Finset.mem_univ i)))

/-- The `IsPrimitive` form of the strictness theorem: on a primitive
walk (aperiodic chain), every off-one Google left-eigenvalue is
strictly inside the α-disk. -/
theorem googleMatrix_abs_eigen_lt_of_primitive (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) [Nonempty V]
    (hprim : (walkTransitionMatrix A).IsPrimitive)
    (μ : V → ℝ) (hμ0 : μ ≠ 0) {c : ℝ}
    (hμ : μ ᵥ* googleMatrix A α = c • μ) (hc : c ≠ 1) :
    |c| < α := by
  obtain ⟨k, -, hk⟩ := hprim
  exact googleMatrix_abs_eigen_lt_of_pow_pos A hnn hdeg hα hk μ hμ0 hμ hc

/-- **The eigen-level strictness**: on a primitive walk, every
off-one eigenvalue of the Google matrix (left-eigenvector convention)
is strictly inside the α-disk — Haveliwala–Kamvar's strict statement
in Mathlib's eigen-API. -/
theorem googleMatrix_hasEigenvalue_abs_lt_of_primitive (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) [Nonempty V]
    (hprim : (walkTransitionMatrix A).IsPrimitive) {c : ℝ}
    (hc : Module.End.HasEigenvalue (googleMatrix A α).vecMulLinear c)
    (h1 : c ≠ 1) :
    |c| < α := by
  obtain ⟨μ, hμ⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hc
  have hne : μ ≠ 0 := (Module.End.hasEigenvector_iff.1 hμ).2
  have hEq : μ ᵥ* googleMatrix A α = c • μ := by
    have := Module.End.HasEigenvector.apply_eq_smul hμ
    simpa [Matrix.vecMulLinear_apply] using this
  exact googleMatrix_abs_eigen_lt_of_primitive A hnn hdeg hα hprim μ hne hEq h1

/-- **The `|λ₂| = α` characterization** — the sharp layer's item 3,
composed from its two delivered halves: the Google matrix has an
off-one left-eigenvalue AT modulus `α` iff the walk has a mass-zero
peripheral (`|c'| = 1`) left-eigenpair at the shadow eigenvalue
`c/α`. Equality is exactly the periodic-chain phenomenon: on a
primitive walk Slice 5's strictness forbids the left side, and the
peripheral side is empty (the QA's negative witness at the primitive
fixture). -/
theorem googleMatrix_abs_eigen_eq_alpha_iff (A : WAdj (V := V))
    (hdeg : ∀ i, 0 < deg A i) {α : ℝ} (hα : 0 < α) [Nonempty V]
    {c : ℝ} (hc1 : c ≠ 1) :
    (∃ μ : V → ℝ, μ ≠ 0 ∧ μ ᵥ* googleMatrix A α = c • μ ∧ |c| = α) ↔
    (∃ ν : V → ℝ, ν ≠ 0 ∧ ∑ i, ν i = 0 ∧
      ν ᵥ* walkTransitionMatrix A = (c / α) • ν ∧ |c / α| = 1) := by
  constructor
  · rintro ⟨μ, hμ0, hμ, habs⟩
    refine ⟨μ, hμ0, googleMatrix_vecMul_mass_zero A hdeg α μ hμ hc1,
      googleMatrix_vecMul_shadow A hdeg (ne_of_gt hα) μ hμ hc1, ?_⟩
    rw [abs_div, abs_of_pos hα, habs, div_self (ne_of_gt hα)]
  · rintro ⟨ν, hν0, hmass, hν, hperiph⟩
    refine ⟨ν, hν0, ?_, ?_⟩
    · rw [googleMatrix_vecMul_of_shadow A α ν hmass hν]
      congr 1
      field_simp
    · rw [abs_div, abs_of_pos hα] at hperiph
      rwa [div_eq_iff (ne_of_gt hα), one_mul] at hperiph

end Strictness

section RightEigenvalue

/-!
### The right-eigenvector forms — the sharp layer at `mulVecLin`

The sharp layer's statements at the RIGHT-eigenvector convention
(`G *ᵥ v = c • v` — the power-iteration convention, where every
`M^t *ᵥ x`-shaped consumer lives), delivered through a general
left/right spectrum bridge
(`proposals/right-eigenvector-sharp-layer.md`, 2026-09-06): a square
matrix's left and right eigenvalue sets coincide. The bridge is
elementary — `det Mᵀ = det M` at the kernel level, through
`Matrix.exists_mulVec_eq_zero_iff` — no charpoly, no field
extension; the priced "charpoly-invariance" route was heavier than
needed.

Why a new route at all: the left machinery's two engines both fail
at the right convention IN GENERAL. The mass lemma cannot transfer
(right-eigenvectors at off-one eigenvalues generally have NONZERO
mass — QA pins the witness), and the shadow lemma is genuinely FALSE
on the right (the teleportation term is rank-one on the right and
moves eigenvectors off the walk's shadow — QA pins the witness); see
`proposals/right-eigenvector-sharp-layer.md`. **On column-stochastic
walks (every doubly-stochastic / Eulerian / regular chain), however,
both engines DO hold on the right**: the transposed walk is
row-stochastic and `googleMatrix Pᵀ α = Gᵀ`, so every left theorem
transports — the doubly-stochastic right forms below (the same
proposal's follow-on, 2026-09-06).

Sources:
- T. H. Haveliwala and S. Kamvar, "The Second Eigenvalue of the
  Google Matrix", Stanford Digital Library tech report 2003-20
  (2003) — the bound is convention-free in the source; these forms
  bring the shelf's statement to the convention the power method
  uses.

QA: the two boundary witnesses plus the right-pair pins in
`Scaffold.QA.SpectralGraph.PageRank_QA.lean` (Section RightEigen).
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The raw right-eigenpair ↔ determinant bridge: `M` has a nonzero
right-eigenpair at `c` iff `c • 1 − M` is singular. Reusable beyond
the Google family. -/
theorem exists_mulVec_eq_smul_iff_det {n : Type} [Fintype n] [DecidableEq n]
    {K : Type} [Field K] (M : Matrix n n K) (c : K) :
    (∃ v ≠ 0, M *ᵥ v = c • v) ↔ (c • 1 - M).det = 0 := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    refine (Matrix.exists_mulVec_eq_zero_iff (M := c • 1 - M)).mp ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
      hv, sub_self]
  · intro hdet
    obtain ⟨v, hv0, hv⟩ :=
      (Matrix.exists_mulVec_eq_zero_iff (M := c • 1 - M)).mpr hdet
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
      sub_eq_zero] at hv
    exact hv.symm

/-- The raw left-eigenpair ↔ determinant bridge, through the
transpose. -/
theorem exists_vecMul_eq_smul_iff_det {n : Type} [Fintype n] [DecidableEq n]
    {K : Type} [Field K] (M : Matrix n n K) (c : K) :
    (∃ μ ≠ 0, μ ᵥ* M = c • μ) ↔ (c • 1 - M).det = 0 := by
  have hEq : (c • 1 - Mᵀ) = (c • 1 - M)ᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  constructor
  · rintro ⟨μ, hμ0, hμ⟩
    have hk : (c • 1 - Mᵀ) *ᵥ μ = 0 := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
        Matrix.mulVec_transpose, hμ, sub_self]
    have hd : (c • 1 - Mᵀ).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨μ, hμ0, hk⟩
    rw [← Matrix.det_transpose, ← hEq]
    exact hd
  · intro hdet
    obtain ⟨μ, hμ0, hμ⟩ :=
      (Matrix.exists_mulVec_eq_zero_iff (M := c • 1 - Mᵀ)).mpr
        (by rw [hEq, Matrix.det_transpose]; exact hdet)
    refine ⟨μ, hμ0, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
      sub_eq_zero] at hμ
    rw [← Matrix.mulVec_transpose]
    exact hμ.symm

/-- **The left/right spectrum bridge**: a square matrix's left and
right eigenvalue sets coincide — the eigen-API form of
`det Mᵀ = det M` at the kernel level, no charpoly needed. Stated for
any field and any square matrix; the eigen-value upgrade of the
vecMul↔mulVec transpose duality the mixing layer's engine join
exploits at the law level. -/
theorem hasEigenvalue_mulVecLin_iff_vecMulLinear {n : Type} [Fintype n]
    [DecidableEq n] {K : Type} [Field K] (M : Matrix n n K) (c : K) :
    Module.End.HasEigenvalue M.mulVecLin c ↔
    Module.End.HasEigenvalue M.vecMulLinear c := by
  constructor
  · intro hR
    obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hR
    obtain ⟨-, hv0⟩ := Module.End.hasEigenvector_iff.1 hv
    have happly : M *ᵥ v = c • v :=
      Module.End.HasEigenvector.apply_eq_smul hv
    obtain ⟨μ, hμ0, hμ⟩ := (exists_vecMul_eq_smul_iff_det M c).mpr
      ((exists_mulVec_eq_smul_iff_det M c).mp ⟨v, hv0, happly⟩)
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.2 ⟨by
        simpa [Matrix.vecMulLinear_apply] using hμ, hμ0⟩)
  · intro hL
    obtain ⟨μ, hμ⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hL
    obtain ⟨-, hμ0⟩ := Module.End.hasEigenvector_iff.1 hμ
    have happly : μ ᵥ* M = c • μ := by
      have := Module.End.HasEigenvector.apply_eq_smul hμ
      simpa [Matrix.vecMulLinear_apply] using this
    obtain ⟨v, hv0, hv⟩ := (exists_mulVec_eq_smul_iff_det M c).mpr
      ((exists_vecMul_eq_smul_iff_det M c).mp ⟨μ, hμ0, happly⟩)
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.2 ⟨by simpa using hv, hv0⟩)

/-- **The right-eigenvalue ceiling** — Haveliwala–Kamvar's inequality
half at the right convention: every right eigenvalue `c ≠ 1` of the
Google matrix obeys `|c| ≤ α`. -/
theorem googleMatrix_hasEigenvalue_mulVecLin_abs_le (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) [Nonempty V] {c : ℝ}
    (hc : Module.End.HasEigenvalue (googleMatrix A α).mulVecLin c)
    (h1 : c ≠ 1) :
    |c| ≤ α :=
  googleMatrix_hasEigenvalue_abs_le A hnn hdeg hα
    ((hasEigenvalue_mulVecLin_iff_vecMulLinear _ c).1 hc) h1

/-- The raw right-eigenpair form of the ceiling: `G *ᵥ v = c • v` at
`v ≠ 0` and `c ≠ 1` forces `|c| ≤ α`. -/
theorem googleMatrix_abs_mulVec_eigen_le (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) [Nonempty V] (v : V → ℝ) (hv0 : v ≠ 0)
    {c : ℝ} (hv : googleMatrix A α *ᵥ v = c • v) (hc : c ≠ 1) :
    |c| ≤ α :=
  googleMatrix_hasEigenvalue_mulVecLin_abs_le A hnn hdeg hα
    (Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.2 ⟨by
        show v ∈ Module.End.eigenspace (googleMatrix A α).mulVecLin c
        rw [Module.End.mem_eigenspace_iff]
        exact hv, hv0⟩)) hc

/-- **The right-eigenvalue strictness**: on a primitive walk, every
off-one RIGHT eigenvalue of the Google matrix is strictly inside the
α-disk — the strictness layer at the power-method convention. -/
theorem googleMatrix_hasEigenvalue_mulVecLin_abs_lt_of_primitive
    (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) [Nonempty V]
    (hprim : (walkTransitionMatrix A).IsPrimitive) {c : ℝ}
    (hc : Module.End.HasEigenvalue (googleMatrix A α).mulVecLin c)
    (h1 : c ≠ 1) :
    |c| < α :=
  googleMatrix_hasEigenvalue_abs_lt_of_primitive A hnn hdeg hα hprim
    ((hasEigenvalue_mulVecLin_iff_vecMulLinear _ c).1 hc) h1

/-- The raw right-eigenpair form of the strictness theorem. -/
theorem googleMatrix_abs_mulVec_eigen_lt_of_primitive (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) [Nonempty V]
    (hprim : (walkTransitionMatrix A).IsPrimitive)
    (v : V → ℝ) (hv0 : v ≠ 0) {c : ℝ}
    (hv : googleMatrix A α *ᵥ v = c • v) (hc : c ≠ 1) :
    |c| < α :=
  googleMatrix_hasEigenvalue_mulVecLin_abs_lt_of_primitive A hnn hdeg hα hprim
    (Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.2 ⟨by
        show v ∈ Module.End.eigenspace (googleMatrix A α).mulVecLin c
        rw [Module.End.mem_eigenspace_iff]
        exact hv, hv0⟩)) hc

/-- Setup: on a column-stochastic walk, the transposed walk matrix
is its own walk transition matrix (its row sums are the walk's column
sums, each one). -/
theorem walkTransitionMatrix_transpose_eq_of_col_sum_one (A : WAdj (V := V))
    (hcol : ∀ j, ∑ i, walkTransitionMatrix A i j = 1) :
    walkTransitionMatrix (walkTransitionMatrix A)ᵀ = (walkTransitionMatrix A)ᵀ := by
  have hrow : ∀ i, ∑ j, (walkTransitionMatrix A)ᵀ i j = 1 := by
    intro i
    simpa only [Matrix.transpose_apply] using hcol i
  exact walkTransitionMatrix_eq_of_row_sum_one _ hrow

/-- Setup: on a column-stochastic walk, the transposed walk's Google
matrix IS the transposed Google matrix — the transport that makes
every left statement a right statement at the transposed walk. -/
theorem googleMatrix_transpose_eq_of_col_sum_one (A : WAdj (V := V))
    (hcol : ∀ j, ∑ i, walkTransitionMatrix A i j = 1) (α : ℝ) :
    googleMatrix (walkTransitionMatrix A)ᵀ α = (googleMatrix A α)ᵀ := by
  have h1 := walkTransitionMatrix_transpose_eq_of_col_sum_one A hcol
  funext i j
  simp only [googleMatrix_apply, h1, Matrix.transpose_apply]

/-- **The right mass lemma on a column-stochastic walk**: a right
eigenvector of the Google matrix at `c ≠ 1` has zero total mass —
the left mass lemma transported through the transpose. -/
theorem googleMatrix_mulVec_mass_zero (A : WAdj (V := V))
    (hcol : ∀ j, ∑ i, walkTransitionMatrix A i j = 1) [Nonempty V]
    (α : ℝ) (v : V → ℝ) {c : ℝ} (hv : googleMatrix A α *ᵥ v = c • v)
    (hc : c ≠ 1) :
    ∑ i, v i = 0 := by
  have hdegT : ∀ i, 0 < deg ((walkTransitionMatrix A)ᵀ) i := by
    intro i
    have h1 : deg ((walkTransitionMatrix A)ᵀ) i = 1 := by
      rw [deg]
      simpa only [Matrix.transpose_apply] using hcol i
    rw [h1]
    norm_num
  have hleft : v ᵥ* googleMatrix ((walkTransitionMatrix A)ᵀ) α = c • v := by
    rw [googleMatrix_transpose_eq_of_col_sum_one A hcol,
      ← Matrix.mulVec_transpose, Matrix.transpose_transpose]
    exact hv
  exact googleMatrix_vecMul_mass_zero _ hdegT α v hleft hc

/-- **The right shadow on a column-stochastic walk**: a right
eigenvector of the Google matrix at `c ≠ 1` is a right eigenvector of
the walk at `c/α` — the left shadow lemma transported through the
transpose (`googleMatrix Pᵀ α = Gᵀ` under column stochasticity).
The two engines that fail at the right convention in general DO hold
on doubly-stochastic chains (every Eulerian/regular chain); see the
section docstring for the general-case boundary witnesses. -/
theorem googleMatrix_mulVec_shadow (A : WAdj (V := V))
    (hcol : ∀ j, ∑ i, walkTransitionMatrix A i j = 1) [Nonempty V]
    {α : ℝ} (hα : α ≠ 0) (v : V → ℝ) {c : ℝ}
    (hv : googleMatrix A α *ᵥ v = c • v) (hc : c ≠ 1) :
    walkTransitionMatrix A *ᵥ v = (c / α) • v := by
  have hdegT : ∀ i, 0 < deg ((walkTransitionMatrix A)ᵀ) i := by
    intro i
    have h1 : deg ((walkTransitionMatrix A)ᵀ) i = 1 := by
      rw [deg]
      simpa only [Matrix.transpose_apply] using hcol i
    rw [h1]
    norm_num
  have hleft : v ᵥ* googleMatrix ((walkTransitionMatrix A)ᵀ) α = c • v := by
    rw [googleMatrix_transpose_eq_of_col_sum_one A hcol,
      ← Matrix.mulVec_transpose, Matrix.transpose_transpose]
    exact hv
  have hshadow := googleMatrix_vecMul_shadow _ hdegT hα v hleft hc
  rw [walkTransitionMatrix_transpose_eq_of_col_sum_one A hcol,
    ← Matrix.mulVec_transpose, Matrix.transpose_transpose] at hshadow
  exact hshadow

/-- **The right attainment twin on a column-stochastic walk**: a
mass-zero right-eigenpair of the walk maps to a right-eigenpair of
the Google matrix at `α · c'` — the left twin transported through
the transpose. -/
theorem googleMatrix_mulVec_of_shadow (A : WAdj (V := V))
    (hcol : ∀ j, ∑ i, walkTransitionMatrix A i j = 1) [Nonempty V]
    (α : ℝ) (v : V → ℝ) {c' : ℝ} (hmass : ∑ i, v i = 0)
    (hv : walkTransitionMatrix A *ᵥ v = c' • v) :
    googleMatrix A α *ᵥ v = (α * c') • v := by
  have hleftP : v ᵥ* walkTransitionMatrix ((walkTransitionMatrix A)ᵀ)
      = c' • v := by
    rw [walkTransitionMatrix_transpose_eq_of_col_sum_one A hcol,
      ← Matrix.mulVec_transpose, Matrix.transpose_transpose]
    exact hv
  have hleft := googleMatrix_vecMul_of_shadow ((walkTransitionMatrix A)ᵀ) α v
    hmass hleftP
  rw [googleMatrix_transpose_eq_of_col_sum_one A hcol,
    ← Matrix.mulVec_transpose, Matrix.transpose_transpose] at hleft
  exact hleft

/-- **The `|λ₂| = α` characterization, doubly-stochastic right
twin**: on a column-stochastic walk, the Google matrix has an
off-one RIGHT-eigenvalue at modulus `α` iff the walk has a mass-zero
peripheral right-eigenpair at `c/α`. -/
theorem googleMatrix_mulVec_abs_eigen_eq_alpha_iff (A : WAdj (V := V))
    (hcol : ∀ j, ∑ i, walkTransitionMatrix A i j = 1) [Nonempty V]
    {α : ℝ} (hα : 0 < α) {c : ℝ} (hc1 : c ≠ 1) :
    (∃ v : V → ℝ, v ≠ 0 ∧ googleMatrix A α *ᵥ v = c • v ∧ |c| = α) ↔
    (∃ w : V → ℝ, w ≠ 0 ∧ ∑ i, w i = 0 ∧
      walkTransitionMatrix A *ᵥ w = (c / α) • w ∧ |c / α| = 1) := by
  constructor
  · rintro ⟨v, hv0, hv, habs⟩
    refine ⟨v, hv0, googleMatrix_mulVec_mass_zero A hcol α v hv hc1,
      googleMatrix_mulVec_shadow A hcol (ne_of_gt hα) v hv hc1, ?_⟩
    rw [abs_div, abs_of_pos hα, habs, div_self (ne_of_gt hα)]
  · rintro ⟨w, hw0, hmass, hw, hperiph⟩
    refine ⟨w, hw0, ?_, ?_⟩
    · rw [googleMatrix_mulVec_of_shadow A hcol α w hmass hw]
      congr 1
      field_simp
    · rw [abs_div, abs_of_pos hα] at hperiph
      rwa [div_eq_iff (ne_of_gt hα), one_mul] at hperiph

end RightEigenvalue

section SortedSpectrum

/-!
### The sorted-spectrum forms — the literal `λ₂` on regular graphs

The sharp layer is NAMED "`|λ₂| ≤ α`" but its statements are
eigenpair-level; on regular input (symmetric `A`, equal degrees) the
Google matrix is symmetric, so the shelf's whole `evals`/`eigvalOf`
machinery applies and the ceiling becomes statements about spectrum
objects (`proposals/sharp-second-eigenvalue-layer.md`, follow-on,
2026-09-06). The new mathematics is the **`1`-eigenspace simplicity**
(`one_eigenspace_eq_smul_of_pos_isSymm`): strict entrywise positivity
(the teleportation floor, `α < 1`) plus the sign-rigidity engine
(the `Strictness` section's) plus the min-ratio argument. On it:
the top of the spectrum is exactly `1`; the second-from-top obeys
`evals ⟨n−2⟩ ≤ α` (at most one eigenbasis index exceeds `α`, by
simplicity plus the eigenbasis orthogonality); and the bottom obeys
`-α ≤ evals ⟨0⟩`.

QA: the pins at the two-cycle (2-regular symmetric) and the
separating 4-cycle fixture (spectrum `{-4/5, 0, 0, 1}`, both bounds
pinned at DISTINCT indices) in
`Scaffold.QA.SpectralGraph.PageRank_QA.lean` (Section Sorted).
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- On regular input (symmetric adjacency, equal degrees), the Google
matrix is symmetric — the whole sorted-spectrum machinery applies. -/
theorem googleMatrix_isSymm_of_regular (A : WAdj (V := V))
    (hsymm : A.IsSymm) (d : ℝ) (hdegd : ∀ i, deg A i = d)
    (α : ℝ) : (googleMatrix A α).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [googleMatrix_apply, walkTransitionMatrix_apply, hdegd,
    hsymm.apply]

/-- Strict entrywise positivity on `0 < α < 1`: the teleportation
floor. -/
theorem googleMatrix_entry_pos (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) [Nonempty V] (i j : V) :
    0 < googleMatrix A α i j := by
  rw [googleMatrix_apply]
  have h1 : 0 ≤ α * walkTransitionMatrix A i j :=
    mul_nonneg (le_of_lt hα) (walkTransitionMatrix_nonneg A hnn hdeg i j)
  have h2 : 0 < (1 - α) * (Fintype.card V : ℝ)⁻¹ := by
    refine mul_pos (by linarith) (inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos))
  linarith

/-- The constant vector is a right `1`-eigenvector (row
stochasticity). -/
theorem googleMatrix_mulVec_ones (A : WAdj (V := V))
    (hdeg : ∀ i, 0 < deg A i) (α : ℝ) [Nonempty V] :
    googleMatrix A α *ᵥ (1 : V → ℝ) = 1 := by
  funext i
  have hi := googleMatrix_row_sum A hdeg α i
  simp only [Matrix.mulVec, Matrix.dotProduct, Pi.one_apply, mul_one] at *
  exact hi

omit [DecidableEq V] in
/-- Every nonnegative `1`-eigenvector of a strictly positive
row-stochastic matrix is strictly positive. -/
theorem pos_of_mulVec_eq_smul_of_nonneg {M : Matrix V V ℝ}
    (hpos : ∀ i j, 0 < M i j)
    {x : V → ℝ} (hx : M *ᵥ x = x) (hx0 : x ≠ 0) (hxnn : ∀ i, 0 ≤ x i) :
    ∀ i, 0 < x i := by
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, 0 < x j₀ := by
    by_contra hcon
    push_neg at hcon
    exact hx0 (funext fun i => le_antisymm (hcon i) (hxnn i))
  intro i
  have hi : x i = ∑ j, M i j * x j := by
    have := congrFun hx i
    simpa [Matrix.mulVec, Matrix.dotProduct] using this.symm
  have hterm : ∀ j ∈ (Finset.univ : Finset V), 0 ≤ M i j * x j := by
    intro j _
    exact mul_nonneg (le_of_lt (hpos i j)) (hxnn j)
  have hone : 0 < M i j₀ * x j₀ := mul_pos (hpos i j₀) hj₀
  rw [hi]
  exact Finset.sum_pos' hterm ⟨j₀, Finset.mem_univ j₀, hone⟩

/-- **The `1`-eigenspace simplicity**: on a strictly positive
symmetric row-stochastic matrix, any two `1`-eigenvectors are
proportional — the sign-rigidity engine (weak sign) plus strict
positivity (which the nonnegative weak-sign eigenvector earns
entrywise) plus the min-ratio argument. -/
theorem one_eigenspace_eq_smul_of_pos_isSymm {M : Matrix V V ℝ}
    (hrow : ∀ i, ∑ j, M i j = 1) (hpos : ∀ i j, 0 < M i j)
    (hM : M.IsSymm) [Nonempty V] {v w : V → ℝ}
    (hv : M *ᵥ v = v) (hv0 : v ≠ 0) (hw : M *ᵥ w = w) (hw0 : w ≠ 0) :
    ∃ c : ℝ, v = c • w := by
  have hleft : ∀ x : V → ℝ, M *ᵥ x = x → x ᵥ* M = x := by
    intro x hx
    rw [← Matrix.mulVec_transpose, hM.eq]
    exact hx
  have hcoer : ∀ x : V → ℝ, M *ᵥ x = x → (∀ i, 0 ≤ x i) ∨ (∀ i, x i ≤ 0) := by
    intro x hx
    exact vecMul_sign_coherent_of_abs_eq_pow_pos hrow
      (fun i j => by rw [pow_one]; exact hpos i j)
      (show x ᵥ* M = (1 : ℝ) • x by simpa using hleft x hx) (by norm_num)
  have hnegpair : ∀ x : V → ℝ, M *ᵥ x = x → M *ᵥ (-x) = -x := by
    intro x hx
    have hsm : M *ᵥ ((-1 : ℝ) • x) = (-1 : ℝ) • x := by
      rw [Matrix.mulVec_smul, hx]
    simpa using hsm
  have hnegne : ∀ x : V → ℝ, x ≠ 0 → (-x : V → ℝ) ≠ 0 := by
    intro x hx hcon
    exact hx (by
      have := congrArg (fun u : V → ℝ => (-1 : ℝ) • u) hcon
      simpa using this)
  have key : ∀ x : V → ℝ, M *ᵥ x = x → x ≠ 0 →
      (∀ i, 0 < x i) ∨ (∀ i, x i < 0) := by
    intro x hx hx0
    rcases hcoer x hx with h | h
    · exact Or.inl (pos_of_mulVec_eq_smul_of_nonneg hpos hx hx0 h)
    · refine Or.inr fun i => ?_
      have h := pos_of_mulVec_eq_smul_of_nonneg hpos (hnegpair x hx)
        (hnegne x hx0) (fun j => neg_nonneg.2 (h j)) i
      simp only [Pi.neg_apply] at h
      linarith
  -- the min-ratio core: two strictly positive 1-eigenvectors are proportional
  have minratio : ∀ p q : V → ℝ, M *ᵥ p = p → M *ᵥ q = q →
      (∀ i, 0 < p i) → (∀ i, 0 < q i) → ∃ c : ℝ, p = c • q := by
    intro p q hp hq hppos hqpos
    set R : V → ℝ := fun i => p i / q i with hRdef
    set S : Finset ℝ := (Finset.univ : Finset V).image R with hSdef
    have hSne : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
    set c : ℝ := S.min' hSne with hcdef
    have hcmin : ∀ i, c ≤ R i := fun i =>
      S.min'_le (R i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    obtain ⟨i₀, hi₀mem, hi₀⟩ := Finset.mem_image.1 (S.min'_mem hSne)
    have hRi₀ : R i₀ = c := hi₀
    have hpair : M *ᵥ (p - c • q) = p - c • q := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hp, hq]
    have hge : ∀ i, 0 ≤ (p - c • q) i := by
      intro i
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_nonneg,
        ← le_div_iff₀ (hqpos i)]
      exact hcmin i
    have hzero : (p - c • q) i₀ = 0 := by
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero]
      exact (div_eq_iff (ne_of_gt (hqpos i₀))).mp hRi₀
    by_contra hcon
    have hne : p - c • q ≠ 0 := by
      intro hz
      exact hcon ⟨c, (eq_of_sub_eq_zero hz : p = c • q)⟩
    have hstrict := pos_of_mulVec_eq_smul_of_nonneg hpos hpair hne hge i₀
    rw [hzero] at hstrict
    exact lt_irrefl 0 hstrict
  -- the four sign cases
  rcases key v hv hv0 with hvpos | hvneg
  · rcases key w hw hw0 with hwpos | hwneg
    · exact minratio v w hv hw hvpos hwpos
    · obtain ⟨c, hc⟩ := minratio v (-w) hv (hnegpair w hw) hvpos
        (fun i => by
          simp only [Pi.neg_apply, Left.neg_pos_iff]
          exact hwneg i)
      exact ⟨-c, by rw [hc, smul_neg, neg_smul]⟩
  · rcases key w hw hw0 with hwpos | hwneg
    · obtain ⟨c, hc⟩ := minratio (-v) w (hnegpair v hv) hw
        (fun i => by simp only [Pi.neg_apply]; linarith [hvneg i]) hwpos
      refine ⟨-c, ?_⟩
      have h2 := congrArg (fun u : V → ℝ => (-1 : ℝ) • u) hc
      simpa using h2
    · obtain ⟨c, hc⟩ := minratio (-v) (-w) (hnegpair v hv) (hnegpair w hw)
        (fun i => by
          simp only [Pi.neg_apply, Left.neg_pos_iff]
          exact hvneg i)
        (fun i => by
          simp only [Pi.neg_apply, Left.neg_pos_iff]
          exact hwneg i)
      exact ⟨c, by
        have := congrArg (fun u : V → ℝ => (-1 : ℝ) • u) hc
        simpa using this⟩

/-- Every eigenbasis eigenvalue is either exactly `1` or obeys the
ceiling `|λ| ≤ α` (the right-ceiling composed with the eigenbasis
eigenpair). -/
theorem googleMatrix_eigvalOf_cases (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) [Nonempty V]
    (hG : (googleMatrix A α).IsSymm) (i : V) :
    eigvalOf (googleMatrix A α) hG i = 1 ∨
      |eigvalOf (googleMatrix A α) hG i| ≤ α := by
  by_cases h1 : eigvalOf (googleMatrix A α) hG i = 1
  · exact Or.inl h1
  · have hvne : eigvecOf (googleMatrix A α) hG i ≠ 0 := by
      intro hz
      have hin : ∑ k, eigvecOf (googleMatrix A α) hG i k
          * eigvecOf (googleMatrix A α) hG i k = 1 := by
        simpa using eigvecOf_inner (googleMatrix A α) hG i i
      rw [hz] at hin
      simp at hin
    have hev : googleMatrix A α *ᵥ eigvecOf (googleMatrix A α) hG i
        = eigvalOf (googleMatrix A α) hG i • eigvecOf (googleMatrix A α) hG i :=
      (isHermitian_of_isSymm hG).mulVec_eigenvectorBasis i
    exact Or.inr (googleMatrix_abs_mulVec_eigen_le A hnn hdeg hα
      (eigvecOf (googleMatrix A α) hG i) hvne hev h1)

/-- **The top of the spectrum is exactly `1`**: on regular input, the
Google matrix's largest eigenvalue is the stationary `1` — the
right-ceiling bounds everything above `α`, and the constant vector
witnesses `1`. -/
theorem googleMatrix_evals_top_eq_one (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) [Nonempty V]
    (hG : (googleMatrix A α).IsSymm) :
    evals hG ⟨Fintype.card V - 1, Nat.sub_lt Fintype.card_pos (by norm_num)⟩
      = 1 := by
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos
  have hall : ∀ i, eigvalOf (googleMatrix A α) hG i ≤ 1 := by
    intro i
    rcases googleMatrix_eigvalOf_cases A hnn hdeg hα hG i with h | h
    · exact le_of_eq h
    · exact (abs_le.1 h).2.trans (le_of_lt hα1)
  have hcount : (Fintype.card V - 1) + 1 ≤
      ((Finset.univ : Finset V).filter
        (fun i => eigvalOf (googleMatrix A α) hG i ≤ 1)).card := by
    have hsub : ((Finset.univ : Finset V).filter
        (fun i => eigvalOf (googleMatrix A α) hG i ≤ 1)) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      exact Finset.mem_filter.2 ⟨Finset.mem_univ i, hall i⟩
    rw [hsub, Finset.card_univ]
    omega
  apply le_antisymm
  · exact evals_le_of_card_eigvalOf_le hG (by omega) hcount
  · obtain ⟨i, hi⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul hG
      (by
        intro h
        exact one_ne_zero (congrFun h (Nonempty.some ‹Nonempty V›)))
      (show googleMatrix A α *ᵥ (1 : V → ℝ) = (1 : ℝ) • 1 by
        simpa using googleMatrix_mulVec_ones A hdeg α)
    have := eigvalOf_le_evals_last hG hcard i
    rw [hi] at this
    exact this

/-- **The second-from-top obeys the ceiling**: `evals ⟨n−2⟩ ≤ α` —
at most one eigenbasis index exceeds `α`, namely the simple top `1`
(simplicity through `one_eigenspace_eq_smul_of_pos_isSymm` plus the
eigenbasis orthogonality). -/
theorem googleMatrix_evals_second_le (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) [Nonempty V]
    (hG : (googleMatrix A α).IsSymm)
    (hcard : 2 ≤ Fintype.card V) :
    evals hG ⟨Fintype.card V - 2, by omega⟩ ≤ α := by
  have hvecne : ∀ k, eigvecOf (googleMatrix A α) hG k ≠ 0 := by
    intro k hz
    have hin : ∑ m, eigvecOf (googleMatrix A α) hG k m
        * eigvecOf (googleMatrix A α) hG k m = 1 := by
      simpa using eigvecOf_inner (googleMatrix A α) hG k k
    rw [hz] at hin
    simp at hin
  -- the `1`-eigvalOf class is a subsingleton
  have hone : ∀ i j, eigvalOf (googleMatrix A α) hG i = 1 →
      eigvalOf (googleMatrix A α) hG j = 1 → i = j := by
    intro i j hi hj
    by_contra hne
    obtain ⟨c, hc⟩ := one_eigenspace_eq_smul_of_pos_isSymm
      (googleMatrix_row_sum A hdeg α) (googleMatrix_entry_pos A hnn hdeg hα hα1)
      hG
      (by
        have hev : googleMatrix A α *ᵥ eigvecOf (googleMatrix A α) hG i
            = eigvalOf (googleMatrix A α) hG i • eigvecOf (googleMatrix A α) hG i :=
          (isHermitian_of_isSymm hG).mulVec_eigenvectorBasis i
        rw [hi, one_smul] at hev
        exact hev)
      (hvecne i)
      (by
        have hev : googleMatrix A α *ᵥ eigvecOf (googleMatrix A α) hG j
            = eigvalOf (googleMatrix A α) hG j • eigvecOf (googleMatrix A α) hG j :=
          (isHermitian_of_isSymm hG).mulVec_eigenvectorBasis j
        rw [hj, one_smul] at hev
        exact hev)
      (hvecne j)
    have horth : ∑ k, eigvecOf (googleMatrix A α) hG i k
        * eigvecOf (googleMatrix A α) hG j k = 0 := by
      rw [eigvecOf_inner (googleMatrix A α) hG i j, if_neg hne]
    have hself : ∑ k, eigvecOf (googleMatrix A α) hG j k
        * eigvecOf (googleMatrix A α) hG j k = 1 := by
      rw [eigvecOf_inner (googleMatrix A α) hG j j, if_pos rfl]
    rw [hc] at horth
    simp only [Pi.smul_apply, smul_eq_mul] at horth
    have horth' : c * ∑ k, eigvecOf (googleMatrix A α) hG j k
        * eigvecOf (googleMatrix A α) hG j k = 0 := by
      rw [Finset.mul_sum]
      simp only [mul_assoc] at horth
      exact horth
    rw [hself, mul_one] at horth'
    have hc0 : c = 0 := by linarith
    exact hvecne i (by rw [hc, hc0, zero_smul])
  -- at most one index exceeds α
  have hgt : ((Finset.univ : Finset V).filter
      (fun i => α < eigvalOf (googleMatrix A α) hG i)).card ≤ 1 := by
    refine le_trans (b := ((Finset.univ : Finset V).filter
        (fun i => eigvalOf (googleMatrix A α) hG i = 1)).card)
      (Finset.card_le_card ?_) (Finset.card_le_one.mpr ?_)
    · intro i hi
      have h1 : α < eigvalOf (googleMatrix A α) hG i := (Finset.mem_filter.1 hi).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ i, ?_⟩
      rcases googleMatrix_eigvalOf_cases A hnn hdeg hα hG i with h | h
      · exact h
      · exact absurd h1 (not_lt.2 (abs_le.1 h).2)
    · intro a ha b hb
      exact hone a b (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
  -- so at least n - 1 indices obey the ceiling
  have hcount : Fintype.card V - 1 ≤ ((Finset.univ : Finset V).filter
      (fun i => eigvalOf (googleMatrix A α) hG i ≤ α)).card := by
    classical
    have hsub : ((Finset.univ : Finset V).filter
        (fun i => eigvalOf (googleMatrix A α) hG i ≤ α)) ⊆ Finset.univ :=
      Finset.filter_subset _ _
    have hpart := Finset.card_sdiff_add_card_eq_card hsub
    have hsd : ((Finset.univ : Finset V) \ ((Finset.univ : Finset V).filter
        (fun i => eigvalOf (googleMatrix A α) hG i ≤ α))) =
        (Finset.univ : Finset V).filter
          (fun i => α < eigvalOf (googleMatrix A α) hG i) := by
      ext i
      simp [Finset.mem_sdiff, Finset.mem_filter]
    rw [hsd, Finset.card_univ] at hpart
    omega
  have hcount' : Fintype.card V - 2 + 1 ≤ ((Finset.univ : Finset V).filter
      (fun i => eigvalOf (googleMatrix A α) hG i ≤ α)).card := by omega
  exact evals_le_of_card_eigvalOf_le hG (by omega) hcount'

/-- **The bottom obeys the ceiling from below**: `-α ≤ evals ⟨0⟩`. -/
theorem googleMatrix_evals_bot_ge (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) [Nonempty V]
    (hG : (googleMatrix A α).IsSymm) :
    -α ≤ evals hG ⟨0, Fintype.card_pos⟩ := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf hG ⟨0, Fintype.card_pos⟩
  rw [hi]
  rcases googleMatrix_eigvalOf_cases A hnn hdeg hα hG i with h | h
  · linarith
  · exact (abs_le.1 h).1

end SortedSpectrum

end SpectralGraphTheory
