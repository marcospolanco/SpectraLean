import Scaffold.Mathlib.LinearAlgebra.PrimitiveConvergence
import Scaffold.Mathlib.GraphTheory.PageRank
import Scaffold.Mathlib.GraphTheory.Mixing

/-!
# Directed mixing — the PageRank power iteration

The first consumer of the `primitive_power_tendsto` admission
(2026-08-24) and the directed axis' first convergence theorem — **hard
crust since the 2026-09-02 retirement**
(`proposals/retire-primitive-power-convergence.md`: the axiom became a
proved theorem at its unchanged statement by the Doeblin/Dobrushin
contraction route, `#print axioms` exactly the standard three). The
delivered PageRank layer (`GraphTheory.PageRank`) proved the
*stationary* theory: the teleportation floor makes the Google matrix
`G` irreducible on every nonnegative input, so the PageRank
distribution exists, is unique among nonnegative distributions, and
has full support — all hard crust since 2026-09-02
(`proposals/cesaro-stationary-existence.md`: the stationary layer was
re-proved without `perron_frobenius` by the Cesàro/power-positivity
route). Its own
statement-shapes section records what it deliberately did not claim:
"nothing about power iteration, rates, or mixing: geometric
convergence … needs strict spectral dominance". This module is that
recorded obligation, discharged at the convergence level: the floor
makes `G` strictly *positive*, hence primitive with `k = 1`
(`googleMatrix_isPrimitive` — the hypothesis of the new axiom,
derived never assumed), so **the power iteration converges** — the
PageRank distribution is computable, closing the loop with the
existence/`∃!` layer.

**Trust boundary after the retirement.** `pageRank_powerIteration`,
`pageRank_entrywise_tendsto`, and `pageRank_walk_tendsto` are hard
crust: `primitive_power_tendsto` is now a proved theorem (the
Doeblin/Dobrushin contraction route), and they make **no**
`perron_frobenius` contact: the stationary vector enters as a
hypothesis (`π ᵥ* G = π`, nonnegative, mass one), which on reducible
input is *supplied* by the delivered layer, so the directed mixing
layer's trust cost is zero admitted axioms, and the hypothesis itself
is now dischargeable in hard crust too (the stationary layer's
existence/`∃!`/full-support theorems are proved since 2026-09-02).
`googleMatrix_isPrimitive`
and the entrywise/walk translations are unconditional hard crust.

## The statements

- **`googleMatrix_isPrimitive`** (unconditional): `G` is primitive at
  `0 ≤ α < 1` on nonempty `V` — `isPrimitive_of_pos` at
  `googleMatrix_pos`. On the same reducible input where the raw walk's
  stationary structure degenerates, the regularized walk is not merely
  irreducible (the delivered fact) but primitive: aperiodicity is
  also derived, not assumed.
- **`pageRank_powerIteration`** (the headline): for every
  starting vector `x`, `(G ^ t) *ᵥ x → (π ⬝ᵥ x) • 1` entrywise — the
  classical PageRank power method, at any nonnegative mass-one
  stationary `π` (by the delivered `∃!`, there is exactly one).
- **`pageRank_entrywise_tendsto`**: `(G ^ t) i j → π j` —
  the `t`-step transition probability from `i` to `j` tends to the
  PageRank weight of `j`, independent of the start.
- **`pageRank_walk_tendsto`**: `ν ᵥ* (G ^ t) → π` for
  every start vector summing to one — the Markov-chain mixing first
  slice, entrywise topology.
- **`pageRank_tvDistance_le`** (2026-09-02,
  `proposals/doeblin-tv-contraction-pagerank-rate.md`): the *rate*
  form — `TV(ν ᵥ* (G ^ t), π) ≤ α^t · TV(ν, π)`, the field-standard
  PageRank power-method rate, with the teleportation floor
  `(1 - α)·|V|⁻¹` read as a Doeblin floor of contraction coefficient
  exactly `α` through the mixing layer's new directed TV contraction.
  Sign-free on `ν`; `π` enters through stationarity and mass alone.

Fourth (2026-09-02, `proposals/directed-mixing-time-object.md`), the
**directed mixing time** — the `t_mix` object family's missing sibling
(`walkMixingTimeFrom`/`lazyWalkMixingTimeFrom`/`contMixingTimeFrom`/
`walkMixingTime` all exist undirected): the per-start Google-walk law
`pageRankDistribution` (the random surfer's position distribution,
probability-certified), the ⌈log⌉-threshold depth form of the rate
(`pageRank_tvDistance_le_of_depth`), and the object
`pageRankMixingTimeFrom` with its package — certificate interface,
well-ordered attainment (`_spec`), the α-ceiling
(`_le_of_rate`), ε-antitonicity — the named consumer being
`Derived/EmpiricalStationary.lean`'s PageRank sampling capstone
(`empiricalPageRank_stationary_tail_of_depth`), which discharges its
gate through the object's own attainment specification.

Fifth (2026-09-02, `proposals/directed-uniform-mixing-time.md`), the
**directed uniform (worst-start) `t_mix` object** — the family's last
missing member, with LPW's `d`/`d̄` distances at the Google law
(`pageRankTVPair`/`pageRankTVUniform`), the submultiplicativity class
(`d(s+t) ≤ d(s)d(t)` and `d̄(s+t) ≤ d̄(s)d(t)`, pure Markovity through
the mixing layer's new matrix-level Dobrushin-coefficient engine
`tvDistance_vecMul_le_tvDobrushinCoeff`), the ε-escalation corollaries,
the object `pageRankMixingTime` with its package (attainment `_spec`,
the witness-load-bearing per-start domination, the sup interchange, the
refined α-ceiling at `d̄(0)` and its display form), and the
well-posedness supplier `exists_pageRankMixingTime_witness`. The named
consumer is the worst-start sampling capstone
(`empiricalPageRank_uniform_tail_of_depth`): one start-independent
threshold certifies `n` simulated trajectories for *every* start — the
agent that cannot control the surfer's start gets a single certificate.

## Scope honesty

The convergence theorems carry no rate clause, and the sharp geometric
constant (`|λ₂|`, which for the Google matrix is exactly `α` in the
spectral picture) needs the complex spectral theory of non-symmetric
matrices — a separate future admission gated on a named consumer, per
`proposals/primitive-power-convergence.md`. What *is* delivered
(2026-09-02) is the coarse explicit rate at the TV level: the Doeblin
coefficient `α` itself, attained exactly at every time on the
periodic-fixture QA — explicit, and on the Google matrix not merely
loose (the QA pins the `α^t` shape sharp there), but with no sharpness
*theorem* for general primitive chains. The periodicity fence is
still the module's QA centerpiece: on the directed 2-cycle —
nonnegative, row-stochastic, *irreducible*, with the uniform
stationary distribution verified — the powers provably oscillate
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

/-- **The PageRank power iteration converges** (hard crust since the
2026-09-02 retirement of `primitive_power_tendsto`, now a proved
theorem): for every starting vector `x`, the
iterated action of the Google matrix converges entrywise to
`(π ⬝ᵥ x) • 1`, at any nonnegative mass-one stationary vector `π` —
of which the delivered `existsUnique_pageRankVec` (hard crust since
the same day's Cesàro stationary re-proof) says there is exactly one.
This is the classical PageRank algorithm as a theorem: start anywhere,
push through the regularized walk, read off the PageRank weights as
the limit. The whole chain — producing `π` and concluding the
convergence — is now proved (the retired `primitive_power_tendsto` and
the stationary layer both are).

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

/-- **Entrywise PageRank convergence** (hard crust since the
retirement): the `t`-step transition probability
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

/-- **Walk-evolution PageRank convergence** (hard crust since the
retirement): starting from any vector `ν`
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

/-- **The PageRank power method converges at rate `α` in total
variation** — the field-standard PageRank rate: the teleportation floor
`(1 - α)·|V|⁻¹` is a Doeblin floor with contraction coefficient
exactly `α`, so `TV(ν ᵥ* (G ^ t), π) ≤ α^t · TV(ν, π)` for any
mass-one start and any mass-one stationary `π` (the delivered `∃!`
layer, PF-conditional, supplies exactly one such `π`; this bound
consumes whatever stationary vector the caller holds — sign hypotheses
on `ν` and `π`'s nonnegativity included nowhere, stationarity and mass
alone). Hard crust: no `perron_frobenius` contact, the mixing layer's
Doeblin TV contraction applied at `m = 1`. The *sharp* `|λ₂| = α`
statement needs the complex spectral theory of non-symmetric matrices
and stays a separate gated admission; this is the coarse explicit
rate — which the QA pins attained exactly at every time on the
periodic 2-cycle fixture where the plain walk provably never mixes.

QA: exercised — attained exactly at every time, with the plain-walk
never-decay contrast beside it — by
`Scaffold.QA.SpectralGraph.DirectedMixing_QA.*`. -/
theorem pageRank_tvDistance_le (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (hdeg : ∀ i, 0 < deg A i) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1)
    [Nonempty V] {π : V → ℝ} (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π)
    {ν : V → ℝ} (hνsum : ∑ i, ν i = 1) (t : ℕ) :
    tvDistance (ν ᵥ* (googleMatrix A α ^ t)) π
      ≤ α ^ t * tvDistance ν π := by
  have hfloor : ∀ i j : V,
      (1 - α) * (Fintype.card V : ℝ)⁻¹ ≤ googleMatrix A α i j := by
    intro i j
    rw [googleMatrix_apply]
    exact le_add_of_nonneg_left
      (mul_nonneg hα (walkTransitionMatrix_nonneg A hnn hdeg i j))
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by
    have hc : 0 < Fintype.card V := Fintype.card_pos
    exact ne_of_gt (Nat.cast_pos.mpr hc)
  have hcoef : 1 - (Fintype.card V : ℝ) * ((1 - α) * (Fintype.card V : ℝ)⁻¹)
      = α := by
    have h1 : (Fintype.card V : ℝ) * ((1 - α) * (Fintype.card V : ℝ)⁻¹)
        = 1 - α := by
      rw [mul_left_comm, mul_inv_cancel₀ hcard, mul_one]
    rw [h1, sub_sub_cancel]
  have hfloor' : ∀ i j : V, (1 - α) * (Fintype.card V : ℝ)⁻¹
      ≤ (googleMatrix A α ^ 1) i j := by
    intro i j
    rw [pow_one]
    exact hfloor i j
  have hmain := tvDistance_vecMul_pow_le_of_pos_power
    (fun i j => googleMatrix_nonneg A hnn hdeg hα (le_of_lt hα') i j)
    (fun i => googleMatrix_row_sum A hdeg α i) hfloor'
    hπsum hπstat hνsum t
  rwa [Nat.div_one, hcoef] at hmain

/-! ## The directed mixing time (`t_mix` at the Google law)

The `t_mix` object family's directed sibling, with the per-start
Google-walk law and the ⌈log⌉-threshold depth form of the rate above.
Everything here is hard crust: the rate engine
(`pageRank_tvDistance_le`) is proved, and no `perron_frobenius` contact
exists anywhere in the section — the stationary vector is a *parameter*,
matching the rate theorem's given-`π` design (the `∃!` supplier is
PF-conditional; this object consumes whatever stationary vector the
caller holds). The named consumer is the empirical PageRank capstone in
`Derived/EmpiricalStationary.lean`. -/

/-- The single-start row action of a matrix: the `x`-th row. The
per-start Google-walk law's entry bridge. -/
theorem piSingle_vecMul_apply (M : Matrix V V ℝ) (x j : V) :
    ((Pi.single x (1 : ℝ) : V → ℝ) ᵥ* M) j = M x j := by
  simp only [Matrix.vecMul, Matrix.dotProduct, Pi.single_apply]
  rw [Finset.sum_eq_single x]
  · simp
  · intro b _ hb
    rw [if_neg hb, zero_mul]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- The per-start Google-walk law: the distribution of the random
surfer's position after `t` steps from `x` — the directed twin of
`walkDistribution`. Its probability certification (`_nonneg`,
`sum_pageRankDistribution`) needs only nonnegative weights and positive
degrees on the teleportation window `0 ≤ α < 1`: both
row-stochasticity and nonnegativity are preserved under powers. -/
noncomputable def pageRankDistribution (A : WAdj (V := V)) (α : ℝ) (t : ℕ) (x : V) :
    V → ℝ :=
  (Pi.single x (1 : ℝ) : V → ℝ) ᵥ* (googleMatrix A α ^ t)

theorem pageRankDistribution_apply (A : WAdj (V := V)) (α : ℝ) (t : ℕ) (x j : V) :
    pageRankDistribution A α t x j = (googleMatrix A α ^ t) x j :=
  piSingle_vecMul_apply _ x j

/-- The Google-walk law is entrywise nonnegative at every time. -/
theorem pageRankDistribution_nonneg (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (hdeg : ∀ i, 0 < deg A i) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) [Nonempty V]
    (t : ℕ) (x j : V) :
    0 ≤ pageRankDistribution A α t x j := by
  rw [pageRankDistribution_apply]
  exact Scaffold.LinearAlgebra.pow_nonneg_entries
    (fun i j => le_of_lt (googleMatrix_pos A hnn hdeg hα hα' i j)) t x j

/-- The Google-walk law is a probability vector: row-stochasticity is
preserved under powers. -/
theorem sum_pageRankDistribution (A : WAdj (V := V)) (hdeg : ∀ i, 0 < deg A i)
    (α : ℝ) [Nonempty V] (t : ℕ) (x : V) :
    ∑ j, pageRankDistribution A α t x j = 1 := by
  simp only [pageRankDistribution_apply]
  exact Scaffold.LinearAlgebra.pow_row_sum
    (fun i => googleMatrix_row_sum A hdeg α i) t x

theorem sum_piSingle (x : V) : ∑ i, (Pi.single x (1 : ℝ) : V → ℝ) i = 1 := by
  simp only [Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The `t = 0` join: the surfer has not moved. -/
theorem pageRankDistribution_zero (A : WAdj (V := V)) (α : ℝ) (x : V) :
    pageRankDistribution A α 0 x = (Pi.single x (1 : ℝ) : V → ℝ) := by
  funext j
  rw [pageRankDistribution_apply, pow_zero, Matrix.one_apply,
    Pi.single_apply]
  by_cases hxj : x = j
  · simp [hxj]
  · simp [hxj, Ne.symm hxj]

/-- The log-threshold calculus bridge at the Doeblin rate — a private
twin of `Oversmoothing.lean`'s public
`pow_mul_le_of_log_threshold`, kept private so this module's import
closure stays free of the undirected mixing stack (which the
directed layer does not otherwise need); promote to a shared home if a
third consumer appears. -/
private theorem pow_mul_le_of_log_threshold' {r C ε : ℝ} (hr : 0 < r)
    (hr1 : r < 1) (hC : 0 ≤ C) (hε : 0 < ε) (t : ℕ)
    (hthr : Real.log (C / ε) / Real.log (1 / r) ≤ (t : ℝ)) :
    r ^ t * C ≤ ε := by
  rcases eq_or_lt_of_le hC with h0 | hC0
  · rw [← h0, mul_zero]
    exact le_of_lt hε
  · have hrinv : 0 < 1 / r := div_pos (by norm_num) hr
    have hrinv1 : 1 < 1 / r := (one_lt_div hr).mpr hr1
    have hlogpos : 0 < Real.log (1 / r) := Real.log_pos hrinv1
    have hCE : 0 < C / ε := div_pos hC0 hε
    have hstep : Real.log (C / ε) ≤ (t : ℝ) * Real.log (1 / r) :=
      (div_le_iff₀ hlogpos).mp hthr
    have hexp : Real.exp (Real.log (C / ε))
        ≤ Real.exp ((t : ℝ) * Real.log (1 / r)) :=
      Real.exp_le_exp.mpr hstep
    rw [Real.exp_log hCE, ← Real.log_pow (1 / r) t] at hexp
    rw [Real.exp_log (pow_pos hrinv t), one_div, inv_pow, inv_eq_one_div] at hexp
    have hfin : C * r ^ t ≤ 1 * ε :=
      (div_le_div_iff₀ hε (pow_pos hr t)).mp hexp
    rw [mul_comm]
    linarith

/-- **The ⌈log⌉-threshold depth form of the PageRank rate**: past the
depth `log (TV(ν, π) / ε) / log (1 / α)`, the `t`-step evolved law is
within `ε` of stationarity — the depth packaging of
`pageRank_tvDistance_le`, exactly the shape of the undirected
`walkDistribution_tvDistance_le_of_depth` at the Doeblin rate. The
strict window `0 < α < 1` is honest: at `α = 0` the chain mixes in one
step (the threshold's logarithm degenerates); the sharp `|λ₂| = α`
layer stays gated. QA: `PR_depth_instance_QA` (attained with equality
at the threshold time on the periodic fixture). -/
theorem pageRank_tvDistance_le_of_depth (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) (hα' : α < 1) [Nonempty V]
    {π : V → ℝ} (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π)
    {ν : V → ℝ} (hνsum : ∑ i, ν i = 1) {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (hthr : Real.log (tvDistance ν π / ε) / Real.log (1 / α) ≤ (t : ℝ)) :
    tvDistance (ν ᵥ* (googleMatrix A α ^ t)) π ≤ ε := by
  refine le_trans
    (pageRank_tvDistance_le A hnn hdeg (le_of_lt hα) hα' hπsum hπstat hνsum t) ?_
  exact pow_mul_le_of_log_threshold' hα hα' (tvDistance_nonneg ν π) hε t hthr

/-- The **directed mixing time** from `x` at threshold `ε` against the
caller-held stationary vector `π`: LPW ch. 20's per-start `t_mix`
reading at the Google law — the least number of steps from which the
random surfer's law stays within `ε` of `π` in total variation. The
`t_mix` object family's directed sibling
(`walkMixingTimeFrom`/`lazyWalkMixingTimeFrom`/`contMixingTimeFrom`/
`walkMixingTime` all exist; this was the missing member). Junk corner:
at an unreachable `ε` the witness set is empty and `sInf ∅ = 0` on `ℕ`
— pinned and fenced in QA (`PR_tmix_zero_junk_QA`). The sup-over-starts
uniform twin is delivered below (`pageRankMixingTime`), on the
submultiplicativity class its gate named. QA: the exact closed forms `PR_tmix_eighth_QA` (pinned in
both directions), `PR_tmix_ceiling_attained_QA` (the α-ceiling
attained exactly). -/
noncomputable def pageRankMixingTimeFrom (A : WAdj (V := V)) (α : ℝ) (π : V → ℝ)
    (x : V) (ε : ℝ) : ℕ :=
  sInf {t : ℕ | ∀ s : ℕ, t ≤ s →
    tvDistance (pageRankDistribution A α s x) π ≤ ε}

/-- The witness-time set is bounded below by `0` by construction. -/
theorem pageRankMixingTimeFrom_bddBelow (A : WAdj (V := V)) (α : ℝ) (π : V → ℝ)
    (x : V) (ε : ℝ) :
    BddBelow {t : ℕ | ∀ s : ℕ, t ≤ s →
      tvDistance (pageRankDistribution A α s x) π ≤ ε} :=
  ⟨0, fun _ _ => Nat.zero_le _⟩

/-- Any witness time certifies the mixing time — the certificate
interface. -/
theorem pageRankMixingTimeFrom_le_of_cert (A : WAdj (V := V)) (α : ℝ) (π : V → ℝ)
    (x : V) {ε : ℝ} (T : ℕ)
    (hT : ∀ s : ℕ, T ≤ s →
      tvDistance (pageRankDistribution A α s x) π ≤ ε) :
    pageRankMixingTimeFrom A α π x ε ≤ T :=
  csInf_le (pageRankMixingTimeFrom_bddBelow A α π x ε) hT

/-- **The mixing time is attained**: `ℕ` is well-ordered, so the
infimum of a nonempty witness set is a *member* of it, and membership
is the uniform bound — the specification the empirical PageRank
capstone consumes (the same loop the Poisson bridge closed for the
discrete object). -/
theorem pageRankMixingTimeFrom_spec (A : WAdj (V := V)) (α : ℝ) (π : V → ℝ)
    (x : V) {ε : ℝ}
    (hne : ∃ t : ℕ, ∀ s : ℕ, t ≤ s →
      tvDistance (pageRankDistribution A α s x) π ≤ ε) :
    ∀ s : ℕ, pageRankMixingTimeFrom A α π x ε ≤ s →
      tvDistance (pageRankDistribution A α s x) π ≤ ε :=
  csInf_mem hne

/-- **The α-ceiling** — the field-standard directed mixing bound in
ceiling form: on the teleportation window `0 < α < 1`, with any mass-one
stationary `π`, `t_mix(ε) ≤ ⌈log (TV(δ_x, π) / ε) / log (1 / α)⌉` —
the Doeblin rate's own threshold, `Nat.ceil`-packaged exactly like the
undirected spectral ceiling. Attained exactly on the periodic 2-cycle
fixture (`PR_tmix_ceiling_attained_QA`: `⌈log 4 / log 2⌉ = ⌈2⌉ = 2` =
the object). -/
theorem pageRankMixingTimeFrom_le_of_rate (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) (hα' : α < 1) [Nonempty V]
    {π : V → ℝ} (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π) {ε : ℝ} (hε : 0 < ε) (x : V) :
    pageRankMixingTimeFrom A α π x ε
      ≤ Nat.ceil (Real.log (tvDistance (Pi.single x (1 : ℝ) : V → ℝ) π / ε)
        / Real.log (1 / α)) := by
  set thr : ℝ := Real.log (tvDistance (Pi.single x (1 : ℝ) : V → ℝ) π / ε)
    / Real.log (1 / α) with hthrdef
  refine pageRankMixingTimeFrom_le_of_cert A α π x (Nat.ceil thr) ?_
  intro s hs
  exact pageRank_tvDistance_le_of_depth A hnn hdeg hα hα' hπsum hπstat
    (sum_piSingle x) hε s
    (le_trans (Nat.le_ceil thr) (by exact_mod_cast hs))

/-- **ε-antitonicity**: a stricter threshold takes at least as long,
given the stricter threshold is reachable. -/
theorem pageRankMixingTimeFrom_anti (A : WAdj (V := V)) (α : ℝ) (π : V → ℝ)
    (x : V) {ε δ : ℝ} (hεδ : ε ≤ δ)
    (hne : ∃ t : ℕ, ∀ s : ℕ, t ≤ s →
      tvDistance (pageRankDistribution A α s x) π ≤ ε) :
    pageRankMixingTimeFrom A α π x δ ≤ pageRankMixingTimeFrom A α π x ε :=
  csInf_le_csInf (pageRankMixingTimeFrom_bddBelow A α π x δ) hne
    (fun _ ht => fun s hs => (ht s hs).trans hεδ)

theorem pageRankDistribution_eq_row (A : WAdj (V := V)) (α : ℝ) (t : ℕ) (x : V) :
    pageRankDistribution A α t x = (googleMatrix A α ^ t) x := by
  funext j
  rw [pageRankDistribution_apply]

/-- The law-evolution identity: `t + s` steps of the random surfer is
`s` more steps from the `t`-step law. -/
theorem pageRankDistribution_add (A : WAdj (V := V)) (α : ℝ) (t s : ℕ) (x : V) :
    pageRankDistribution A α (t + s) x
      = (pageRankDistribution A α t x) ᵥ* (googleMatrix A α ^ s) := by
  simp only [pageRankDistribution, Matrix.vecMul_vecMul, pow_add]

/-- **The two-start directed distance** — LPW's `d(t)` at the Google
law: the worst-case TV distance between the `t`-step surfer laws from
two starts. On a finite type a genuine maximum (`Finset.sup'`). -/
noncomputable def pageRankTVPair (A : WAdj (V := V)) (α : ℝ) [Nonempty V]
    (t : ℕ) : ℝ :=
  (Finset.univ : Finset (V × V)).sup'
    ⟨(‹Nonempty V›.some, ‹Nonempty V›.some), Finset.mem_univ _⟩ fun p =>
      tvDistance (pageRankDistribution A α t p.1) (pageRankDistribution A α t p.2)

theorem pageRankTVPair_nonneg (A : WAdj (V := V)) (α : ℝ) [Nonempty V] (t : ℕ) :
    0 ≤ pageRankTVPair A α t :=
  le_trans (tvDistance_nonneg _ _)
    (Finset.le_sup'
      (f := fun p : V × V =>
        tvDistance (pageRankDistribution A α t p.1) (pageRankDistribution A α t p.2))
      (Finset.mem_univ (‹Nonempty V›.some, ‹Nonempty V›.some)))

/-- **The engine join**: LPW's `d(t)` at the Google law *is* the
Dobrushin coefficient of the `t`-th Google power — the identification
that routes the matrix-level contraction to the directed law level. -/
theorem pageRankTVPair_eq_tvDobrushinCoeff (A : WAdj (V := V)) (α : ℝ)
    [Nonempty V] (t : ℕ) :
    pageRankTVPair A α t = tvDobrushinCoeff (googleMatrix A α ^ t) := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le
      (⟨(‹Nonempty V›.some, ‹Nonempty V›.some), Finset.mem_univ _⟩ :
        (Finset.univ : Finset (V × V)).Nonempty)
      (f := fun p : V × V =>
        tvDistance (pageRankDistribution A α t p.1) (pageRankDistribution A α t p.2))
      fun p _ => ?_
    show tvDistance (pageRankDistribution A α t p.1)
        (pageRankDistribution A α t p.2) ≤ tvDobrushinCoeff (googleMatrix A α ^ t)
    rw [pageRankDistribution_eq_row A α t p.1, pageRankDistribution_eq_row A α t p.2]
    exact Finset.le_sup'
      (f := fun q : V × V =>
        tvDistance ((googleMatrix A α ^ t) q.1) ((googleMatrix A α ^ t) q.2))
      (Finset.mem_univ p)
  · refine Finset.sup'_le
      (⟨(‹Nonempty V›.some, ‹Nonempty V›.some), Finset.mem_univ _⟩ :
        (Finset.univ : Finset (V × V)).Nonempty)
      (f := fun p : V × V =>
        tvDistance ((googleMatrix A α ^ t) p.1) ((googleMatrix A α ^ t) p.2))
      fun p _ => ?_
    show tvDistance ((googleMatrix A α ^ t) p.1) ((googleMatrix A α ^ t) p.2)
      ≤ pageRankTVPair A α t
    rw [← pageRankDistribution_eq_row A α t p.1, ← pageRankDistribution_eq_row A α t p.2]
    exact Finset.le_sup'
      (f := fun q : V × V =>
        tvDistance (pageRankDistribution A α t q.1) (pageRankDistribution A α t q.2))
      (Finset.mem_univ p)

/-- **The Google-walk Dobrushin contraction**: applying `t` Google
steps to both sides of an equal-mass pair contracts TV by the
two-start distance `d(t)` — the directed twin of the undirected
engine, by the matrix-level contraction through the engine join. -/
theorem tvDistance_vecMul_pow_googleMatrix_le (A : WAdj (V := V)) (α : ℝ)
    [Nonempty V] (t : ℕ) (μ ν : V → ℝ) (hmass : ∑ i, μ i = ∑ i, ν i) :
    tvDistance (μ ᵥ* (googleMatrix A α ^ t)) (ν ᵥ* (googleMatrix A α ^ t))
      ≤ tvDistance μ ν * pageRankTVPair A α t := by
  rw [pageRankTVPair_eq_tvDobrushinCoeff]
  exact tvDistance_vecMul_le_tvDobrushinCoeff μ ν hmass

/-- **Submultiplicativity of the two-start distance** — LPW's classical
`d(s + t) ≤ d(s) · d(t)` at the Google law: pure Markovity (row
stochasticity of the Google matrix is the only graph input). -/
theorem pageRankTVPair_submul (A : WAdj (V := V)) (hdeg : ∀ i, 0 < deg A i)
    (α : ℝ) [Nonempty V] (s t : ℕ) :
    pageRankTVPair A α (s + t) ≤ pageRankTVPair A α s * pageRankTVPair A α t := by
  rw [pageRankTVPair_eq_tvDobrushinCoeff, pageRankTVPair_eq_tvDobrushinCoeff,
    pageRankTVPair_eq_tvDobrushinCoeff]
  exact tvDobrushinCoeff_pow_add_le _ (fun i => googleMatrix_row_sum A hdeg α i) s t

/-- **The worst-start directed distance** — the `d̄(t)` of the mixing
literature at the Google law, against the caller-held stationary
vector `π` (the rate theorem's given-`π` design). -/
noncomputable def pageRankTVUniform (A : WAdj (V := V)) (α : ℝ) (π : V → ℝ)
    [Nonempty V] (t : ℕ) : ℝ :=
  (Finset.univ : Finset V).sup'
    ⟨‹Nonempty V›.some, Finset.mem_univ _⟩ fun x =>
      tvDistance (pageRankDistribution A α t x) π

theorem pageRankTVUniform_nonneg (A : WAdj (V := V)) (α : ℝ) (π : V → ℝ)
    [Nonempty V] (t : ℕ) :
    0 ≤ pageRankTVUniform A α π t :=
  le_trans (tvDistance_nonneg _ _)
    (Finset.le_sup'
      (f := fun x => tvDistance (pageRankDistribution A α t x) π)
      (Finset.mem_univ ‹Nonempty V›.some))

omit [Fintype V] in
theorem piSingle_nonneg (x : V) (i : V) :
    0 ≤ (Pi.single x (1 : ℝ) : V → ℝ) i := by
  simp only [Pi.single_apply]
  split <;> norm_num

/-- **The worst-start distance is dominated by the two-start
distance** — the classical `d̄(t) ≤ d(t)` at the Google law: the
contraction at the pair `(δ_x, π)` (both mass one), with
`TV(δ_x, π) ≤ 1` from the simplex diameter. No mixture identity, no
reversibility — stationarity of `π` under the Google power does all
the work. -/
theorem pageRankTVUniform_le_pageRankTVPair (A : WAdj (V := V)) (α : ℝ)
    [Nonempty V] {π : V → ℝ}
    (hπnn : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π) (t : ℕ) :
    pageRankTVUniform A α π t ≤ pageRankTVPair A α t := by
  have hstat : π ᵥ* (googleMatrix A α ^ t) = π :=
    Scaffold.LinearAlgebra.vecMul_pow_eq_of_vecMul_eq hπstat t
  have hlaw : ∀ x : V, pageRankDistribution A α t x
      = (Pi.single x (1 : ℝ) : V → ℝ) ᵥ* (googleMatrix A α ^ t) := fun _ => rfl
  refine Finset.sup'_le
    (⟨‹Nonempty V›.some, Finset.mem_univ _⟩ :
      (Finset.univ : Finset V).Nonempty)
    (f := fun x => tvDistance (pageRankDistribution A α t x) π)
    fun x _ => ?_
  calc tvDistance (pageRankDistribution A α t x) π
      = tvDistance ((Pi.single x (1 : ℝ) : V → ℝ) ᵥ* (googleMatrix A α ^ t))
          (π ᵥ* (googleMatrix A α ^ t)) := by
            rw [hstat, hlaw x]
    _ ≤ tvDistance (Pi.single x (1 : ℝ) : V → ℝ) π * pageRankTVPair A α t :=
          tvDistance_vecMul_pow_googleMatrix_le A α t
            (Pi.single x (1 : ℝ) : V → ℝ) π (by rw [sum_piSingle x, hπsum])
    _ ≤ 1 * pageRankTVPair A α t := by
          refine mul_le_mul_of_nonneg_right ?_ (pageRankTVPair_nonneg A α t)
          exact tvDistance_le_one_of_nonneg_of_sum_eq_one
            (piSingle_nonneg x) (sum_piSingle x) hπnn hπsum
    _ = pageRankTVPair A α t := by ring

/-- **Discrete TV monotonicity in time** at the Google law: the surfer
law's TV distance to stationarity never increases — the Doeblin rate at
the residual exponent (`α^j ≤ 1`), through the law-evolution identity. -/
theorem pageRankDistribution_tvDistance_anti (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i) {α : ℝ}
    (hα : 0 ≤ α) (hα' : α < 1) [Nonempty V] {π : V → ℝ}
    (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π) (t j : ℕ) (x : V) :
    tvDistance (pageRankDistribution A α (t + j) x) π
      ≤ tvDistance (pageRankDistribution A α t x) π := by
  rw [pageRankDistribution_add]
  calc tvDistance ((pageRankDistribution A α t x) ᵥ* (googleMatrix A α ^ j)) π
      ≤ α ^ j * tvDistance (pageRankDistribution A α t x) π :=
          pageRank_tvDistance_le A hnn hdeg hα hα' hπsum hπstat
            (sum_pageRankDistribution A hdeg α t x) j
    _ ≤ 1 * tvDistance (pageRankDistribution A α t x) π := by
          refine mul_le_mul_of_nonneg_right ?_ (tvDistance_nonneg _ _)
          exact pow_le_one₀ hα (le_of_lt hα')
    _ = tvDistance (pageRankDistribution A α t x) π := by ring

/-- **The mixed submultiplicativity** — the classical companion
`d̄(s + t) ≤ d̄(s) · d(t)` at the Google law: the contraction at the
pair `(ν_s^x, π)` (both mass one — the law's by conservation,
stationarity's by hypothesis), no sign hypothesis anywhere. -/
theorem pageRankTVUniform_mul_pageRankTVPair_le (A : WAdj (V := V))
    (hdeg : ∀ i, 0 < deg A i) (α : ℝ) [Nonempty V] {π : V → ℝ}
    (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π) (s t : ℕ) :
    pageRankTVUniform A α π (s + t)
      ≤ pageRankTVUniform A α π s * pageRankTVPair A α t := by
  have hstat : π ᵥ* (googleMatrix A α ^ t) = π :=
    Scaffold.LinearAlgebra.vecMul_pow_eq_of_vecMul_eq hπstat t
  refine Finset.sup'_le
    (⟨‹Nonempty V›.some, Finset.mem_univ _⟩ :
      (Finset.univ : Finset V).Nonempty)
    (f := fun x => tvDistance (pageRankDistribution A α (s + t) x) π)
    fun x _ => ?_
  show tvDistance (pageRankDistribution A α (s + t) x) π
    ≤ pageRankTVUniform A α π s * pageRankTVPair A α t
  rw [show pageRankDistribution A α (s + t) x
      = (pageRankDistribution A α s x) ᵥ* (googleMatrix A α ^ t) from
      pageRankDistribution_add A α s t x]
  calc tvDistance ((pageRankDistribution A α s x) ᵥ* (googleMatrix A α ^ t)) π
      = tvDistance ((pageRankDistribution A α s x) ᵥ* (googleMatrix A α ^ t))
          (π ᵥ* (googleMatrix A α ^ t)) := by rw [hstat]
    _ ≤ tvDistance (pageRankDistribution A α s x) π * pageRankTVPair A α t :=
          tvDistance_vecMul_pow_googleMatrix_le A α t
            (pageRankDistribution A α s x) π
            (by rw [sum_pageRankDistribution A hdeg α s x, hπsum])
    _ ≤ pageRankTVUniform A α π s * pageRankTVPair A α t := by
          refine mul_le_mul_of_nonneg_right ?_ (pageRankTVPair_nonneg A α t)
          exact Finset.le_sup'
            (f := fun y => tvDistance (pageRankDistribution A α s y) π)
            (Finset.mem_univ x)

/-- **The escalation engine** — `d̄((k + 1)·t₀) ≤ d̄(t₀) · d(t₀)^k`: the
mixed submultiplicativity iterated, the certificate-free geometric
decay powering the ε-escalation corollary. -/
theorem pageRankTVUniform_succ_mul_le (A : WAdj (V := V))
    (hdeg : ∀ i, 0 < deg A i) (α : ℝ) [Nonempty V] {π : V → ℝ}
    (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π) (k t₀ : ℕ) :
    pageRankTVUniform A α π ((k + 1) * t₀)
      ≤ pageRankTVUniform A α π t₀ * (pageRankTVPair A α t₀) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : (k + 1 + 1) * t₀ = (k + 1) * t₀ + t₀ := by ring
    rw [hsplit]
    calc pageRankTVUniform A α π ((k + 1) * t₀ + t₀)
        ≤ pageRankTVUniform A α π ((k + 1) * t₀) * pageRankTVPair A α t₀ :=
          pageRankTVUniform_mul_pageRankTVPair_le A hdeg α hπsum hπstat _ _
      _ ≤ (pageRankTVUniform A α π t₀ * (pageRankTVPair A α t₀) ^ k)
            * pageRankTVPair A α t₀ :=
          mul_le_mul_of_nonneg_right ih (pageRankTVPair_nonneg A α t₀)
      _ = pageRankTVUniform A α π t₀ * (pageRankTVPair A α t₀) ^ (k + 1) := by
          rw [pow_succ, mul_assoc]

/-! ### The uniform mixing-time object -/

/-- **The uniform (worst-start) directed mixing time** — LPW's
`t_mix(ε)` at the Google law: the least number of steps from which
*every* start's surfer law stays within `ε` of `π` in total variation —
the worst-case-start twin of the delivered per-start
`pageRankMixingTimeFrom`, completing the `t_mix` object family's
directed half. Junk corner: at an unreachable `ε` the time set is
empty and `sInf ∅ = 0` on `ℕ` (pinned and fenced in QA). On a finite
type the object is the worst start's per-start mixing time
(`pageRankMixingTime_eq_sup_pageRankMixingTimeFrom`). -/
noncomputable def pageRankMixingTime (A : WAdj (V := V)) (α : ℝ) (π : V → ℝ)
    (ε : ℝ) : ℕ :=
  sInf {t : ℕ | ∀ s : ℕ, t ≤ s → ∀ x : V,
    tvDistance (pageRankDistribution A α s x) π ≤ ε}

/-- The witness-time set is bounded below by `0` by construction. -/
theorem pageRankMixingTime_bddBelow (A : WAdj (V := V)) (α : ℝ) (π : V → ℝ)
    (ε : ℝ) :
    BddBelow {t : ℕ | ∀ s : ℕ, t ≤ s → ∀ x : V,
      tvDistance (pageRankDistribution A α s x) π ≤ ε} :=
  ⟨0, fun _ _ => Nat.zero_le _⟩

/-- Any uniform witness time certifies the uniform mixing time. -/
theorem pageRankMixingTime_le_of_cert (A : WAdj (V := V)) (α : ℝ) (π : V → ℝ)
    {ε : ℝ} (T : ℕ)
    (hT : ∀ s : ℕ, T ≤ s → ∀ x : V,
      tvDistance (pageRankDistribution A α s x) π ≤ ε) :
    pageRankMixingTime A α π ε ≤ T :=
  csInf_le (pageRankMixingTime_bddBelow A α π ε) hT

/-- **The uniform mixing time is attained** — `ℕ` is well-ordered, so
given any witness the infimum is a member, and membership is the
uniform bound (the statement the escalation corollary and the
worst-start empirical capstone compose). -/
theorem pageRankMixingTime_spec (A : WAdj (V := V)) (α : ℝ) (π : V → ℝ)
    {ε : ℝ}
    (hne : ∃ t : ℕ, ∀ s : ℕ, t ≤ s → ∀ x : V,
      tvDistance (pageRankDistribution A α s x) π ≤ ε) :
    ∀ s : ℕ, pageRankMixingTime A α π ε ≤ s → ∀ x : V,
      tvDistance (pageRankDistribution A α s x) π ≤ ε :=
  csInf_mem hne

/-- Per-start times are dominated by the uniform time, *given a
uniform witness* (set inclusion — the uniform predicate implies the
per-start one). The witness hypothesis is load-bearing, exactly as in
the undirected twin: at the junk corner (`sInf ∅ = 0`) the
un-witnessed statement has no reason to hold, and no theorem below
instantiates without a witness (the α-ceiling and the escalation both
supply one). -/
theorem pageRankMixingTimeFrom_le_pageRankMixingTime (A : WAdj (V := V))
    (α : ℝ) (π : V → ℝ) (x : V) {ε : ℝ}
    (hne : ∃ t : ℕ, ∀ s : ℕ, t ≤ s → ∀ y : V,
      tvDistance (pageRankDistribution A α s y) π ≤ ε) :
    pageRankMixingTimeFrom A α π x ε ≤ pageRankMixingTime A α π ε := by
  obtain ⟨t, ht⟩ := hne
  exact csInf_le_csInf (pageRankMixingTimeFrom_bddBelow A α π x ε)
    ⟨t, ht⟩ (fun t' ht' s hs => ht' s hs x)

/-- **The uniform object is the worst start's per-start object** — on a
finite type the sup over starts commutes with the infimum over times,
through each per-start attainment (given any uniform witness).
Hypothesis-light: no graph structure at all. -/
theorem pageRankMixingTime_eq_sup_pageRankMixingTimeFrom (A : WAdj (V := V))
    (α : ℝ) (π : V → ℝ) [Nonempty V] {ε : ℝ}
    (hne : ∃ t : ℕ, ∀ s : ℕ, t ≤ s → ∀ x : V,
      tvDistance (pageRankDistribution A α s x) π ≤ ε) :
    pageRankMixingTime A α π ε = (Finset.univ : Finset V).sup'
      ⟨‹Nonempty V›.some, Finset.mem_univ _⟩
      (fun x => pageRankMixingTimeFrom A α π x ε) := by
  obtain ⟨t₀, ht₀⟩ := hne
  refine le_antisymm ?_ ?_
  · refine pageRankMixingTime_le_of_cert A α π _ fun s hs x => ?_
    have hxle : pageRankMixingTimeFrom A α π x ε ≤ s := by
      have h1 : pageRankMixingTimeFrom A α π x ε
          ≤ (Finset.univ : Finset V).sup'
            ⟨‹Nonempty V›.some, Finset.mem_univ _⟩
            (fun y => pageRankMixingTimeFrom A α π y ε) :=
        Finset.le_sup' (f := fun y => pageRankMixingTimeFrom A α π y ε)
          (Finset.mem_univ x)
      exact le_trans h1 hs
    exact pageRankMixingTimeFrom_spec A α π x
      ⟨t₀, fun s' hs' => ht₀ s' hs' x⟩ s hxle
  · refine Finset.sup'_le
      (⟨‹Nonempty V›.some, Finset.mem_univ _⟩ :
        (Finset.univ : Finset V).Nonempty)
      (f := fun x => pageRankMixingTimeFrom A α π x ε) fun x _ => ?_
    exact pageRankMixingTimeFrom_le_pageRankMixingTime A α π x ⟨t₀, ht₀⟩

/-- The uniform ceiling's certificate body: past the display threshold
`log (1/ε) / log (1/α)`, *every* start's surfer law is within `ε` —
the Doeblin rate at the worst start constant `TV(δ_x, π) ≤ 1`. Kept
private until a second consumer appears; both α-ceilings and the
witness supplier run through it. -/
private theorem pageRank_ceiling_cert (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i) {α : ℝ}
    (hα : 0 < α) (hα' : α < 1) [Nonempty V] {π : V → ℝ}
    (hπnn : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π) {ε : ℝ} (hε : 0 < ε) (s : ℕ)
    (hs : (Nat.ceil (Real.log (1 / ε) / Real.log (1 / α)) : ℕ) ≤ s) (x : V) :
    tvDistance (pageRankDistribution A α s x) π ≤ ε := by
  have hthr : Real.log (1 / ε) / Real.log (1 / α) ≤ (s : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hs)
  calc tvDistance (pageRankDistribution A α s x) π
      ≤ α ^ s * tvDistance (Pi.single x (1 : ℝ) : V → ℝ) π :=
          pageRank_tvDistance_le A hnn hdeg (le_of_lt hα) hα' hπsum hπstat
            (sum_piSingle x) s
    _ ≤ α ^ s * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_of_lt hα) s)
          exact tvDistance_le_one_of_nonneg_of_sum_eq_one
            (piSingle_nonneg x) (sum_piSingle x) hπnn hπsum
    _ ≤ ε := pow_mul_le_of_log_threshold' hα hα' (by norm_num) hε s hthr

/-- **The uniform witness supplier** — well-posedness of the uniform
object on the teleportation window: every `ε > 0` is reachable from
every start simultaneously (the Doeblin rate pays for all of them at
the single display threshold). The existence half of the object's
specification, and the empirical worst-start capstone's witness. -/
theorem exists_pageRankMixingTime_witness (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i) {α : ℝ}
    (hα : 0 < α) (hα' : α < 1) [Nonempty V] {π : V → ℝ}
    (hπnn : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, ∀ s : ℕ, T ≤ s → ∀ x : V,
      tvDistance (pageRankDistribution A α s x) π ≤ ε :=
  ⟨Nat.ceil (Real.log (1 / ε) / Real.log (1 / α)),
    fun s hs x => pageRank_ceiling_cert A hnn hdeg hα hα' hπnn hπsum hπstat
      hε s hs x⟩

/-- **The uniform α-ceiling, refined** — the field-standard directed
uniform bound at the worst-start constant `d̄(0) = max_x TV(δ_x, π)`:
`t_mix(ε) ≤ ⌈log (d̄(0) / ε) / log (1 / α)⌉`. Sharp on the fixture
where the per-start ceiling is (both pinned in QA). -/
theorem pageRankMixingTime_le_of_rate (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i) {α : ℝ}
    (hα : 0 < α) (hα' : α < 1) [Nonempty V] {π : V → ℝ}
    (hπsum : ∑ i, π i = 1) (hπstat : π ᵥ* googleMatrix A α = π)
    {ε : ℝ} (hε : 0 < ε) :
    pageRankMixingTime A α π ε
      ≤ Nat.ceil (Real.log (pageRankTVUniform A α π 0 / ε)
        / Real.log (1 / α)) := by
  refine pageRankMixingTime_le_of_cert A α π
    (Nat.ceil (Real.log (pageRankTVUniform A α π 0 / ε)
      / Real.log (1 / α))) ?_
  intro s hs x
  have hthr : Real.log (pageRankTVUniform A α π 0 / ε)
      / Real.log (1 / α) ≤ (s : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hs)
  have hTV0 : tvDistance (Pi.single x (1 : ℝ) : V → ℝ) π
      ≤ pageRankTVUniform A α π 0 := by
    rw [← pageRankDistribution_zero A α x]
    exact Finset.le_sup'
      (f := fun y => tvDistance (pageRankDistribution A α 0 y) π)
      (Finset.mem_univ x)
  calc tvDistance (pageRankDistribution A α s x) π
      ≤ α ^ s * tvDistance (Pi.single x (1 : ℝ) : V → ℝ) π :=
          pageRank_tvDistance_le A hnn hdeg (le_of_lt hα) hα' hπsum hπstat
            (sum_piSingle x) s
    _ ≤ α ^ s * pageRankTVUniform A α π 0 :=
          mul_le_mul_of_nonneg_left hTV0 (pow_nonneg (le_of_lt hα) s)
    _ ≤ ε := pow_mul_le_of_log_threshold' hα hα'
          (pageRankTVUniform_nonneg A α π 0) hε s hthr

/-- **The uniform α-ceiling, display form** — the start-free bound
`t_mix(ε) ≤ ⌈log (1 / ε) / log (1 / α)⌉` at a nonnegative mass-one
stationary vector (the simplex diameter `d̄(0) ≤ 1` folded in). Coarser
than the refined form by exactly that worst-case start constant; QA
pins the gap on the fixture. -/
theorem pageRankMixingTime_le_of_rate' (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i) {α : ℝ}
    (hα : 0 < α) (hα' : α < 1) [Nonempty V] {π : V → ℝ}
    (hπnn : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π) {ε : ℝ} (hε : 0 < ε) :
    pageRankMixingTime A α π ε
      ≤ Nat.ceil (Real.log (1 / ε) / Real.log (1 / α)) := by
  refine pageRankMixingTime_le_of_cert A α π
    (Nat.ceil (Real.log (1 / ε) / Real.log (1 / α))) ?_
  exact fun s hs x =>
    pageRank_ceiling_cert A hnn hdeg hα hα' hπnn hπsum hπstat hε s hs x

/-- **The ε-escalation corollary** — the submultiplicativity class's
consumer capstone at the Google law: one evaluation time `t₀` with both
distances certified (`d̄(t₀) ≤ ε₀`, `d(t₀) ≤ ρ < 1`) yields *every*
ε-level mixing time — `t_mix(ε) ≤ (k + 1) · t₀` whenever
`ε₀ · ρᵏ ≤ ε`. LPW's canonical bridge from a single certified
evaluation (the `t_mix := t_mix(1/4)` convention) to arbitrary
accuracy, on the directed axis; the statement that needs the *uniform*
object (the worst start's certificate is what iterates). -/
theorem pageRankMixingTime_le_mul_of_escalation (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i) {α : ℝ}
    (hα : 0 ≤ α) (hα' : α < 1) [Nonempty V] {π : V → ℝ}
    (hπsum : ∑ i, π i = 1) (hπstat : π ᵥ* googleMatrix A α = π)
    {ε ε₀ ρ : ℝ} (t₀ k : ℕ)
    (hunif : pageRankTVUniform A α π t₀ ≤ ε₀)
    (hpair : pageRankTVPair A α t₀ ≤ ρ) (hk : ε₀ * ρ ^ k ≤ ε) :
    pageRankMixingTime A α π ε ≤ (k + 1) * t₀ := by
  refine pageRankMixingTime_le_of_cert A α π ((k + 1) * t₀) fun s hs x => ?_
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hs
  have hpow : (pageRankTVPair A α t₀) ^ k ≤ ρ ^ k :=
    pow_le_pow_left₀ (pageRankTVPair_nonneg A α t₀) hpair k
  have hesc := pageRankTVUniform_succ_mul_le A hdeg α hπsum hπstat k t₀
  have hsup : tvDistance (pageRankDistribution A α ((k + 1) * t₀) x) π
      ≤ pageRankTVUniform A α π ((k + 1) * t₀) :=
    Finset.le_sup'
      (f := fun y =>
        tvDistance (pageRankDistribution A α ((k + 1) * t₀) y) π)
      (Finset.mem_univ x)
  rw [hj]
  calc tvDistance (pageRankDistribution A α ((k + 1) * t₀ + j) x) π
      ≤ tvDistance (pageRankDistribution A α ((k + 1) * t₀) x) π :=
          pageRankDistribution_tvDistance_anti A hnn hdeg hα hα' hπsum hπstat
            ((k + 1) * t₀) j x
    _ ≤ pageRankTVUniform A α π ((k + 1) * t₀) := hsup
    _ ≤ pageRankTVUniform A α π t₀ * (pageRankTVPair A α t₀) ^ k := hesc
    _ ≤ ε₀ * ρ ^ k :=
          mul_le_mul hunif hpow (pow_nonneg (pageRankTVPair_nonneg A α t₀) k)
            (le_trans (pageRankTVUniform_nonneg A α π t₀) hunif)
    _ ≤ ε := hk

/-- **The ⌈log⌉ display form** — the escalation corollary at its
field-standard display: `t_mix(ε) ≤ (⌈log(ε₀/ε)/log(1/ρ)⌉ + 1) · t₀`
under `0 < ε₀`, `0 < ε`, `0 < ρ < 1`. -/
theorem pageRankMixingTime_le_of_escalation (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hdeg : ∀ i, 0 < deg A i) {α : ℝ}
    (hα : 0 ≤ α) (hα' : α < 1) [Nonempty V] {π : V → ℝ}
    (hπsum : ∑ i, π i = 1) (hπstat : π ᵥ* googleMatrix A α = π)
    {ε ε₀ ρ : ℝ} (hε₀ : 0 < ε₀) (hε : 0 < ε) (t₀ : ℕ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hunif : pageRankTVUniform A α π t₀ ≤ ε₀)
    (hpair : pageRankTVPair A α t₀ ≤ ρ) :
    pageRankMixingTime A α π ε
      ≤ (Nat.ceil (Real.log (ε₀ / ε) / Real.log (1 / ρ)) + 1) * t₀ := by
  have hkey := pow_mul_le_of_log_threshold' hρ hρ1 (le_of_lt hε₀) hε
    (Nat.ceil (Real.log (ε₀ / ε) / Real.log (1 / ρ))) (Nat.le_ceil _)
  exact pageRankMixingTime_le_mul_of_escalation A hnn hdeg hα hα' hπsum hπstat
    t₀ (Nat.ceil (Real.log (ε₀ / ε) / Real.log (1 / ρ))) hunif hpair
    (by rw [mul_comm]; exact hkey)

end SpectralGraphTheory
