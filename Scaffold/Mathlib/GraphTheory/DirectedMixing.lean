import Scaffold.Mathlib.LinearAlgebra.PrimitiveConvergence
import Scaffold.Mathlib.GraphTheory.PageRank

/-!
# Directed mixing — the PageRank power iteration

The first consumer of the `primitive_power_tendsto` admission
(2026-08-24) and the directed axis' first convergence theorem. The
delivered PageRank layer (`GraphTheory.PageRank`) proved the
*stationary* theory: the teleportation floor makes the Google matrix
`G` irreducible on every nonnegative input, so the PageRank
distribution exists, is unique among nonnegative distributions, and
has full support — all conditional on `perron_frobenius`. Its own
statement-shapes section records what it deliberately did not claim:
"nothing about power iteration, rates, or mixing: geometric
convergence … needs strict spectral dominance". This module is that
recorded obligation, discharged at the convergence level: the floor
makes `G` strictly *positive*, hence primitive with `k = 1`
(`googleMatrix_isPrimitive` — the hypothesis of the new axiom,
derived never assumed), so **the power iteration converges** — the
PageRank distribution is computable, closing the loop with the
existence/`∃!` layer.

**Trust boundary.** `pageRank_powerIteration`,
`pageRank_entrywise_tendsto`, and `pageRank_walk_tendsto` are
*conditional on `primitive_power_tendsto` alone* — Lean-checked
deductions, never foundationally proved. They make **no**
`perron_frobenius` contact: the stationary vector enters as a
hypothesis (`π ᵥ* G = π`, nonnegative, mass one), which on reducible
input is *supplied* by the delivered layer, but the two axioms' trust
costs are independent and separately consumable. `googleMatrix_isPrimitive`
and the entrywise/walk translations are unconditional hard crust.

## The statements

- **`googleMatrix_isPrimitive`** (unconditional): `G` is primitive at
  `0 ≤ α < 1` on nonempty `V` — `isPrimitive_of_pos` at
  `googleMatrix_pos`. On the same reducible input where the raw walk's
  stationary structure degenerates, the regularized walk is not merely
  irreducible (the delivered fact) but primitive: aperiodicity is
  also derived, not assumed.
- **`pageRank_powerIteration`** (conditional, the headline): for every
  starting vector `x`, `(G ^ t) *ᵥ x → (π ⬝ᵥ x) • 1` entrywise — the
  classical PageRank power method, at any nonnegative mass-one
  stationary `π` (by the delivered `∃!`, there is exactly one).
- **`pageRank_entrywise_tendsto`** (conditional): `(G ^ t) i j → π j` —
  the `t`-step transition probability from `i` to `j` tends to the
  PageRank weight of `j`, independent of the start.
- **`pageRank_walk_tendsto`** (conditional): `ν ᵥ* (G ^ t) → π` for
  every start vector summing to one — the Markov-chain mixing first
  slice, entrywise topology.

## Scope honesty

No rate: the geometric convergence constant (`|λ₂|`, total variation,
χ²) needs the complex spectral theory of non-symmetric matrices — a
separate future admission gated on a named consumer, per
`proposals/primitive-power-convergence.md`. The periodicity fence is
the module's QA centerpiece: on the directed 2-cycle — nonnegative,
row-stochastic, *irreducible*, with the uniform stationary
distribution verified — the powers provably oscillate
(`P2_no_limit_QA`), so the hypothesis-free convergence conclusion is
refuted in proved form and `hprim` is exactly the missing hypothesis;
this is simultaneously the documentation of why `perron_frobenius`'s
no-dominance scope was the honest call.

QA: exercised by `Scaffold.QA.SpectralGraph.DirectedMixing_QA.*` (the
reducible-fixture positive witness with the limit pinned to the
raw-verified uniform value and the second iterate computed raw inside
it; the periodicity refutation with every other hypothesis verified;
the `onesVec` coherence join; the irreducibility transfer cross-checked
against the delivered single-arc route).

Delivered 2026-08-24 (`proposals/primitive-power-convergence.md`).
-/

open scoped Matrix Topology

namespace SpectralGraphTheory

open Matrix Filter

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The Google matrix is primitive** — unconditionally on the
input's reducibility or asymmetry: the teleportation floor
`(1 - α) * (card V)⁻¹ > 0` makes every entry positive at
`0 ≤ α < 1`, and a positive matrix is primitive at `k = 1`. Strictly
stronger than the delivered `googleMatrix_isIrreducible` (the 2-cycle
witnesses the gap): *aperiodicity* is derived here, never assumed.
Unconditional hard crust.

QA: exercised by `Scaffold.QA.SpectralGraph.DirectedMixing_QA.*`. -/
theorem googleMatrix_isPrimitive (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (hdeg : ∀ i, 0 < deg A i) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1)
    [Nonempty V] :
    (googleMatrix A α).IsPrimitive :=
  Scaffold.LinearAlgebra.isPrimitive_of_pos _
    (fun i j => googleMatrix_pos A hnn hdeg hα hα' i j)

/-- **The PageRank power iteration converges** (conditional on
`primitive_power_tendsto` alone): for every starting vector `x`, the
iterated action of the Google matrix converges entrywise to
`(π ⬝ᵥ x) • 1`, at any nonnegative mass-one stationary vector `π` —
of which the delivered `existsUnique_pageRankVec` (conditional on
`perron_frobenius`) says there is exactly one. This is the classical
PageRank algorithm as a theorem: start anywhere, push through the
regularized walk, read off the PageRank weights as the limit. No
`perron_frobenius` contact: producing `π` needs that axiom, concluding
the convergence needs only `primitive_power_tendsto`.

QA: exercised — the reducible-fixture instantiation with the limit
pinned to the raw-verified uniform value — by
`Scaffold.QA.SpectralGraph.DirectedMixing_QA.*`. -/
theorem pageRank_powerIteration (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (hdeg : ∀ i, 0 < deg A i) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1)
    [Nonempty V] {π : V → ℝ} (hπnn : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π) (x : V → ℝ) :
    Filter.Tendsto (fun t : ℕ => (googleMatrix A α ^ t) *ᵥ x)
      Filter.atTop (𝓝 ((π ⬝ᵥ x) • (1 : V → ℝ))) :=
  Scaffold.LinearAlgebra.primitive_power_tendsto _
    (fun i j => le_of_lt (googleMatrix_pos A hnn hdeg hα hα' i j))
    (fun i => googleMatrix_row_sum A hdeg α i)
    (googleMatrix_isPrimitive A hnn hdeg hα hα') hπnn hπsum hπstat x

/-- **Entrywise PageRank convergence** (conditional on
`primitive_power_tendsto` alone): the `t`-step transition probability
`(G ^ t) i j` tends to the PageRank weight `π j`, independent of the
start `i`. The column form of the power iteration.

QA: exercised by `Scaffold.QA.SpectralGraph.DirectedMixing_QA.*`. -/
theorem pageRank_entrywise_tendsto (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i) {α : ℝ}
    (hα : 0 ≤ α) (hα' : α < 1) [Nonempty V] {π : V → ℝ}
    (hπnn : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π) (i j : V) :
    Filter.Tendsto (fun t : ℕ => (googleMatrix A α ^ t) i j)
      Filter.atTop (𝓝 (π j)) :=
  Scaffold.LinearAlgebra.primitive_entrywise_tendsto _
    (fun i j => le_of_lt (googleMatrix_pos A hnn hdeg hα hα' i j))
    (fun i => googleMatrix_row_sum A hdeg α i)
    (googleMatrix_isPrimitive A hnn hdeg hα hα') hπnn hπsum hπstat i j

/-- **Walk-evolution PageRank convergence** (conditional on
`primitive_power_tendsto` alone): starting from any vector `ν`
summing to one (a distribution; only the sum is used), the row action
of the Google powers converges to the PageRank distribution,
`ν ᵥ* (G ^ t) → π`. The Markov-chain mixing first slice for the
directed axis, entrywise topology; rates are out of the admitted
statement's scope.

QA: exercised — the non-uniform-start fixture instantiation — by
`Scaffold.QA.SpectralGraph.DirectedMixing_QA.*`. -/
theorem pageRank_walk_tendsto (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (hdeg : ∀ i, 0 < deg A i) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1)
    [Nonempty V] {π : V → ℝ} (hπnn : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π) (ν : V → ℝ)
    (hνsum : ∑ i, ν i = 1) :
    Filter.Tendsto (fun t : ℕ => ν ᵥ* (googleMatrix A α ^ t))
      Filter.atTop (𝓝 π) :=
  Scaffold.LinearAlgebra.primitive_vecMul_tendsto _
    (fun i j => le_of_lt (googleMatrix_pos A hnn hdeg hα hα' i j))
    (fun i => googleMatrix_row_sum A hdeg α i)
    (googleMatrix_isPrimitive A hnn hdeg hα hα') hπnn hπsum hπstat ν hνsum

/-- The graph-side translation of the mass bookkeeping: powers of the
Google matrix fix `onesVec`. Unconditional hard crust (the
`pow_mulVec_one` translation at `G`); the QA coherence join consumes
it against the axiom's limit. -/
theorem googleMatrix_pow_mulVec_onesVec (A : WAdj (V := V))
    (hdeg : ∀ i, 0 < deg A i) (α : ℝ) [Nonempty V] (t : ℕ) :
    (googleMatrix A α ^ t) *ᵥ (onesVec : V → ℝ) = onesVec :=
  Scaffold.LinearAlgebra.pow_mulVec_one
    (fun i => googleMatrix_row_sum A hdeg α i) t

end SpectralGraphTheory
