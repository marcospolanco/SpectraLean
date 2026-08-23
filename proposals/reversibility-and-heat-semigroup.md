# Proposal: Reversibility and the Heat Semigroup on the Graph Laplacian

**Status:** **PROPOSAL COMPLETE 2026-08-23 — Phases A, B, and C all
delivered, zero new axioms at every step (count stays 9 from first
delivery to last).** Phase A (reversibility/detailed balance, both of
its steps) DELIVERED 2026-08-22 as pure hard crust in
`GraphTheory.Stationary` (no new definitions). **Phase B DELIVERED in
full 2026-08-23 across four runs**: Step 0 (survey) + Step 1
(definition, symmetry, identity at zero), Step 2 (the semigroup law),
Step 3 (mass conservation), and Step 4 (eigenmode decay + the
connected-graph DC limit — the payoff statement; see the delivery
record below) — all in `GraphTheory.Heat`. The external consumer's
four-item interface (identity, semigroup law, mass conservation,
eigenmode decay with the DC limit) is complete hard crust. **Phase C
(the heat-flow derivative + remainder bound, the second `sgt-gaps.md`
request) DELIVERED 2026-08-23, priority High — Steps 0 + 1** (the
survey + `heatKernel_mulVec_hasDerivAt_zero`)**, Step 2** (the
first-order remainder bound
`heatKernel_firstOrder_remainder_apply_le` +
`heatKernel_firstOrder_remainder_interval`, completing the
dissolution-theorem analytic input; see "Phase C delivery record" near
the end).
**Phase B's operator-decision gate was
RESOLVED 2026-08-23, priority raised to High.** `sgt-gaps.md` — a
document from the independent `spectral-proof` clean-sheet rewrite
project, handed to this repository directly by the operator — names this
proposal's Phase B by file path as the one remaining Scaffold dependency
it needs, and lists the exact interface: heat evolution
specialized to `laplacian A`; identity at time zero and the semigroup
law; mass conservation (`onesVec` preservation); and eigenmode decay,
including the connected-graph consequence that free diffusion leaves
only the DC component in the limit. That is Steps 1–4 below verbatim —
no proposal-scope change is needed, only authorization to proceed. This
is a real external named consumer, not the proposal naming itself (the
distinction "Why this axis" below was careful to preserve). Originally
proposed 2026-08-18.

Two independent phases, split because they sit on opposite sides of an
existing backlog gate — see "Why this axis." Assessed from
`Scaffold/Mathlib/GraphTheory/{Stationary,RandomWalk,Normalized,
Spectral}.lean`, `docs/6_SGT_BACKLOG.md` items 5–6, `docs/7_SGT_RADAR.md`
axis 5, and a fresh survey of
`.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/
{Exponential,MatrixExponential}.lean` for matrix-exponential machinery.

## Recommendation

- **Phase A — Reversibility.** Prove the simple random walk on a weighted
  undirected graph is reversible with respect to its stationary measure
  (detailed balance): `π i * P i j = π j * P j i`. This is standard —
  every introductory Markov-chains text states it as the defining
  property that makes spectral (rather than merely stochastic) methods
  apply to the walk at all.
- **Phase B — The heat semigroup.** Define `heatKernel A t := exp (-t •
  laplacian A)` and prove the semigroup property, symmetry, mass
  conservation, and the eigenmode-decay monotonicity theorem — the
  continuous-time counterpart of `mixing-time-bound.md`'s discrete decay
  bound, and the standard "diffusion on a graph" object (Chung,
  *Spectral Graph Theory*, ch. 1 and 6; Grigor'yan, *Introduction to
  Analysis on Graphs*, ch. 3).

Both are textbook results with no free parameters and no invented
terminology — they are exactly the two items `docs/7_SGT_RADAR.md:48`
lists as absent that `mixing-time-bound.md` does not already claim.

## Why this axis

`docs/7_SGT_RADAR.md:48` (axis 5, "Random walks and diffusion," score
2.5/5): "Absent: mixing-time statements, heat kernels, reversibility;
walk-spectrum transfer is the named Mathlib gap." `mixing-time-bound.md`
targets the first item. This proposal targets the other two, which have
no proposal file today.

Both phases also have a named place in the backlog, at different gate
states:

- **Phase A's gate is already open.** `docs/6_SGT_BACKLOG.md:100-104`
  (item 6, "Thermodynamics / statistical mechanics"): "Gated on item 1-2
  stability: entropy and reversibility interfaces... No admission before
  the Markov prerequisites are stable." Items 1 and 2 are both recorded
  **delivered** in the same document (`docs/6_SGT_BACKLOG.md:22-54`), so
  the stated precondition is met. Nothing about Phase A requires an
  operator decision.
- **Phase B's gate was conditional; it is now resolved.**
  `docs/6_SGT_BACKLOG.md:93-98` (item 5, "Graph-dynamical systems"):
  "*Only when a named SGT consumer needs them*: diffusion / heat flow
  `e^{-tL}`... The retained persistence package is a compatibility
  example, not a roadmap driver." This proposal originally named itself
  as the consumer, which this repository's own center-out policy
  correctly does not treat as sufficient (naming one in a proposal is
  not the same as an operator adopting it). **2026-08-23: `sgt-gaps.md`,
  from the independent `spectral-proof` rewrite project, supplies the
  real external consumer this gate requires** — see the Status line
  above. The distinction the original text drew is exactly why this
  update matters: this is a different project asking for this proposal's
  Phase B by name, not this proposal asking for itself.

Phase B is also independently attractive on cost grounds: unlike the
discrete walk matrix `L_walk` (not symmetric for irregular graphs, so
`evals` does not yet apply to it — the residual gap `mixing-time-
bound.md` step 1 is scoped to close), the heat semigroup acts directly
on `laplacian A` / `normalizedLaplacian A`, which are *already*
symmetric with an *already*-proved sorted spectrum and eigenbasis
(`Spectral.lean`: `evals`, `evals_sorted`, `spectralProjector`,
`eigvecOf_complete`). Phase B does not depend on the open walk-
eigenvalue-transfer gap at all.

## Phase A: Reversibility (detailed balance)

### Step 1: Irregular case

For `A.IsSymm` and `hd : ∀ i, 0 < deg A i`, with `π i := deg A i / vol A
univ` (the stationary measure already proved in `Stationary.lean`'s
`walkTransitionMatrix_transpose_mulVec_deg`) and `P := walkTransitionMatrix
A` (`Normalized.lean:201`, `P i j = A i j / deg A i`), prove detailed
balance:

```
π i * P i j = π j * P j i
```

The proof is short given what is already on the shelf: both sides reduce
to `A i j / vol A univ` — the `deg A i` in `π i`'s numerator cancels
against `walkTransitionMatrix`'s `deg A i` denominator on the left, the
same happens on the right, and the two remaining numerators agree by
`hA : A.IsSymm`. No new definitions of `deg`, `vol`, or `P` are needed;
this composes existing lemmas rather than growing the interface.

### Step 2: Regular case (optional, cheaper)

The same statement for `RandomWalk.transitionMatrix` (`d`-regular case)
is a direct specialization — with `π` uniform (`1/|V|`) it is close to
definitionally true from `A.IsSymm` alone. Worth stating separately only
if a consumer needs the regular-case interface without going through the
general one; otherwise Step 1 subsumes it via
`randomWalkLaplacian_eq_smul_laplacian`.

### QA

- Positive witness: detailed balance checked numerically on an
  irregular fixture (e.g. the 3-vertex path with degrees `1, 2, 1`
  already used in `Normalized.lean`'s own QA) — compute both sides
  independently and confirm equality.
- Negative witness: an asymmetric weight matrix (`A i j ≠ A j i`) where
  detailed balance fails, to show the symmetry hypothesis is
  load-bearing rather than vacuous.

## Phase B: The heat semigroup

### Step 0: Survey (record before proving)

Confirm the exact Mathlib lemma names and hypotheses before writing
Scaffold statements:

- `Mathlib.Analysis.Normed.Algebra.MatrixExponential`: `IsSymm.exp`
  (symmetric matrices exponentiate to symmetric matrices), `exp_zero`,
  `exp_neg`, `Commute.exp` (commuting matrices exponentiate to commuting
  matrices).
- `Mathlib.Analysis.Normed.Algebra.Exponential`: `exp_add_of_commute` /
  `exp_add_of_commute_of_mem_ball` (semigroup property for commuting
  elements) and `expSeries_radius_eq_top` — for a finite-dimensional
  matrix algebra the exponential series has infinite radius of
  convergence, so any `_of_mem_ball` hypothesis in the general Banach-
  algebra statement is automatically satisfied here and should not block
  the semigroup step.

### Step 1: Definition and basic properties

Define `heatKernel A t := NormedSpace.exp ℝ (-(t • laplacian A))`.
Prove:

- **Symmetry:** `(heatKernel A t).IsSymm`, from `IsSymm.exp` applied to
  `-(t • laplacian A)` (symmetric because `laplacian A` is, via
  `laplacian_symmetric`, and negation/scalar multiplication preserve
  symmetry).
- **Identity at `t = 0`:** `heatKernel A 0 = 1`, from `exp_zero`.

### Step 2: Semigroup property

`heatKernel A s * heatKernel A t = heatKernel A (s + t)`. Proof:
`-(s • laplacian A)` and `-(t • laplacian A)` commute (both are scalar
multiples of the same matrix), so the commuting-elements addition lemma
surveyed in Step 0 applies directly; `smul_add` reduces the exponent to
`-((s + t) • laplacian A)`.

### Step 3: Mass conservation

`heatKernel A t *ᵥ onesVec = onesVec`. This is the standard "heat
diffusing on a graph doesn't create or destroy total heat" fact,
following from `laplacian A *ᵥ onesVec = 0` (already proved,
`laplacian_ones_in_kernel`, per `Stationary.lean`'s own docstring
reference) lifted through the exponential's power series — `onesVec` is
a fixed point of every power of `-(t • laplacian A)` beyond the zeroth,
so the series collapses to `onesVec` itself.

### Step 4: Eigenmode decay (the payoff statement)

Express `heatKernel A t` through the already-proved orthonormal
eigenbasis of `laplacian A` (`Spectral.lean`'s `spectralProjector`,
`eigvecOf_complete` — the same machinery `Dynamics.lean` and
`Derived.ProjectorDrift` already reuse), i.e. the standard spectral-
calculus identity

```
heatKernel A t = ∑ k, Real.exp (-t * evals hA k) • spectralProjector ...
```

Then prove the monotonicity theorem that makes this worth having: for
sorted eigenvalues `evals hA i ≤ evals hA j` and `t ≥ 0`, the mode-`j`
decay factor is at most the mode-`i` decay factor —
`Real.exp (-t * evals hA j) ≤ Real.exp (-t * evals hA i)` — immediate
from `evals_sorted` (already proved) and the antitonicity of `Real.exp`
in a negated, scaled argument. This is the precise, unembellished
statement of "higher graph frequencies dissipate at least as fast as
lower ones under diffusion," with no free parameters and no interpretive
claim beyond the inequality itself.

### Deferred and removed

- **Heat-kernel trace / Weyl-law asymptotics** — a real classical topic,
  but a separate proposal-scale project, not a default continuation.
- **Continuous-time total variation / stochastic completeness** — needs
  the same probability-measure wrapper `mixing-time-bound.md` defers in
  its own step 4; out of scope here for the same reason.
- **Infinite-graph analytic questions** (essential self-adjointness,
  Markov uniqueness) — Scaffold is `Fintype V` throughout; these
  questions are vacuous in the finite setting and should not be
  admitted as if they were open problems here.

### QA

- Positive witness: on a small fixture (e.g. `K₂` or the 3-vertex path
  already used elsewhere in this neighborhood), compute `heatKernel A t`
  at a concrete `t` two independent ways — directly from the
  `NormedSpace.exp` definition and via the Step 4 eigenbasis sum — and
  confirm agreement.
- Negative/structural witness: on a disconnected fixture, confirm heat
  does *not* cross components (mass is conserved per-component, not
  merely globally) — a direct corollary of the already-proved
  component-count kernel theorem in `electrical-structure-crust.md`'s
  delivered work, and a good sanity check that Step 3's conservation
  statement isn't accidentally vacuous.

## Operating instructions for an autonomous run

- One step per run; Phase A is small enough that both its steps may fit
  in a single run.
- **No new axioms.** Every step composes either already-proved Scaffold
  theorems or directly-imported Mathlib exponential lemmas. If Step 4's
  spectral-calculus identity turns out to need machinery genuinely absent
  from both, stop and record the precise obstruction in
  `docs/6_SGT_BACKLOG.md` rather than admitting anything.
- Survey Mathlib before each step per this repository's standing rule;
  update `docs/8_MATHLIB_COVERAGE_MAP.md` if the survey finds something
  that map missed.
- Phase B's operator-decision gate is resolved (see "Open next step");
  an autonomous run may begin Step 0 without further authorization.

## Open next step

**Phase A — DELIVERED 2026-08-22** (see the delivery record below). No
Phase A work remains; the regular-case Step 2 was delivered as the
uniform-measure corollary composed from `transitionMatrix_symmetric`
(the already-on-shelf theorem the pre-edit survey found), exactly the
proposal's own "otherwise Step 1 subsumes it" branch.

**Phase B is authorized. RESOLVED 2026-08-23** — see the Status line and
"Why this axis" above: `sgt-gaps.md` (the `spectral-proof` rewrite
project) names this exact Phase B by file path as its one remaining
Scaffold dependency, satisfying `docs/6_SGT_BACKLOG.md` item 5's "named
SGT consumer" gate with a real external requester rather than the
proposal naming itself. **Step 0 and Step 1 are DELIVERED 2026-08-23**
(see the delivery record below). **Step 2 is DELIVERED 2026-08-23** (see
the delivery record below). **Step 3 is DELIVERED 2026-08-23** (see the
delivery record below). **Step 4 is DELIVERED 2026-08-23 — the proposal
is COMPLETE** (see the delivery record below). No further work is
authorized by this proposal; the deferred items below (heat-kernel trace
asymptotics, stochastic completeness, infinite-graph questions) remain
deliberately out of scope.

## Delivery record

### Phase B, Step 4 — eigenmode decay + the connected-graph DC limit
(DELIVERED 2026-08-23, run `20260823T112921Z-run-1`; the proposal
COMPLETE)

Delivered in `Scaffold/Mathlib/GraphTheory/Heat.lean` (QA extended at
`Scaffold/QA/SpectralGraph/Heat_QA.lean`, 25 → 46 theorem
declarations), all proved, zero new axioms per this proposal's own
mandate (count stays 9). `#print axioms` on all ten new/rewritten
public and all twenty-one new QA declarations reads only `propext,
Classical.choice, Quot.sound`:

- **The payoff `heatKernel_mulVec_tendsto_atTop`:** on every connected
  graph with symmetric nonnegative weights, the heat flow of *any*
  initial vector converges, as `t → ∞`, to its mean —
  `((∑ j, x j) / |V|) • onesVec`. Free diffusion leaves only the DC
  component. The assembly is load-bearing on the shelf's spectral
  center end-to-end: PSD bounds every eigenvalue below
  (`quadForm_eigvecOf_self` + `laplacian_psd`); kernel-mode existence
  from `det L = 0` (`Matrix.exists_mulVec_eq_zero_iff` at `onesVec` —
  the Step-0-selected route, shorter than the expansion argument) +
  `det_eq_prod_eigenvalues` + `Finset.prod_eq_zero_iff`; the kernel
  characterization `laplacian_kernel_eq_span_onesVec` makes the kernel
  eigenvector a unit multiple of `onesVec`; a *second* kernel mode
  would put two orthogonal unit vectors in one line (the Fiedler
  template) — impossible — so every other eigenvalue is strictly
  positive and its factor vanishes by the new
  `tendsto_exp_neg_mul_atTop`; the eigenbasis expansion turns the flow
  into the finite damped sum; `tendsto_finset_sum` passes the limit
  through; the surviving kernel contribution is identified with the
  mean through the unit normalization `c² |V| = 1`.
- **`heatKernel_mulVec_eigvecOf`** — eigenmode decay in mode form:
  every eigenbasis vector of `laplacian A` is an eigenvector of
  `heatKernel A t` at *every* time, with eigenvalue the mode's decay
  factor `Real.exp (-(t * λᵢ))` — the precise sense in which diffusion
  damps each graph frequency separately.
- **`heatKernel_decayFactor_antitone` / `heatKernel_decayFactor_le_one`**
  — the proposal's named monotonicity statement (sorted `λᵢ ≤ λⱼ`,
  `t ≥ 0` ⇒ the mode-`j` factor ≤ the mode-`i` factor; `evals_sorted` +
  `Real.exp_le_exp`), plus the dissipation bound (PSD ⇒ every factor
  ≤ `1` at `t ≥ 0` — damping, never amplification).
- **`heatKernel_mulVec_eq_sum`** — the spectral-calculus identity in
  action form: `heatKernel A t *ᵥ x = ∑ᵢ e^{−t·λᵢ} (vᵢ ⬝ᵥ x) • vᵢ`
  over the proved orthonormal eigenbasis (`eigvecOf_expansion_apply` +
  `Matrix.mulVecLin` linearity + the mode theorem). The proposal's
  sketch wrote this through `spectralProjector`; the delivered form is
  the honest eigenbasis expansion (the survey's recorded finding: the
  basis API and the sorted API connect only through existential
  `evals_mem_eigvalOf`, so the expansion is stated where the machinery
  lives — on `eigvecOf`/`eigvalOf`).
- **The eigenmode engine `exp_mulVec_eq_smul_of_mulVec_eq_smul`**
  (`M *ᵥ v = μ • v → exp ℝ M *ᵥ v = Real.exp μ • v`) — the
  load-bearing bridge the plan required: the proof is Step 3's
  `expSeries_hasSum_exp` pushed through the continuous action at an
  eigenvector (`HasSum.map`, the Step-3 pattern), each series term
  collapsed by the new power lemma `pow_mulVec_smul`, the remaining
  scalar series summed by the pin's
  `NormedSpace.exp_series_hasSum_exp'` *at ℝ* (identified with
  `Real.exp` through `Real.exp_eq_exp_ℝ` — the pin's normed-section
  lemma applies at the scalar level, where no matrix-type transfer is
  needed). Step 3's kernel engine
  `exp_mulVec_eq_of_mulVec_eq_zero` is re-derived as the `μ = 0` case
  **at unchanged statement** (its standalone proof replaced by a
  one-line corollary).
- **The rank-one-idempotent collapse `exp_eq_one_add_of_mul_self_eq_smul`**
  (`M * M = c • M → exp ℝ M = 1 + ((exp c − 1)/c) • M`, `c ≠ 0`) —
  the square-zero collapse's sibling and a second consumer of Step 3's
  convergence: every power from the first is a scalar multiple of `M`,
  the scalar tail shifted by the pin's topological-group
  `hasSum_nat_add_iff'` (the pin carries **no** plain tail-shift
  `HasSum` lemma — a survey finding), divided through `c` by a
  continuous additive map, reassembled by `tsum_eq_zero_add` +
  `tsum_smul_const`. This is what makes the symmetric K₂ fixture
  (Laplacian squaring to `2 • L`) exactly evaluable at symbolic times.
- **QA (21 new declarations):** eigenmode decay on K₂ by **two
  independent routes to one statement** (engine at every time vs. the
  closed form `heatKernel K₂ t = 1 + ((e^{−2t} − 1)/2) • L` plus hand
  arithmetic — a wrong sign, factor, or eigenvalue anywhere in either
  chain contradicts the other); the **engine⇄collapse cross-validation**
  at a nonzero eigenvalue (on the all-ones matrix `m2`:
  `exp m2 *ᵥ ![1,1] = e² • ![1,1]` derived through the engine and,
  independently, from the collapse's value by hand); the **K₂ Laplacian
  spectrum pinned `evals L = [0, 2]`** from trace/determinant/sortedness
  (the Cheeger-QA pinning pattern, at the combinatorial Laplacian) with
  the monotonicity theorem instantiated to `e^{−2} ≤ 1` reading both
  constants from the pin; and **the DC limit by two routes**
  (the theorem with the mean computed by hand vs. the raw route —
  the closed form's action `![2 − e^{−2t}, 2 + e^{−2t}]` tending to
  `![2,2]` through the scalar decay-factor lemma — independent of the
  theorem, the kernel characterization, PSD, and the eigenbasis).

Pin-specific technique notes for future runs: the pin has no
`HasSum.congr` — a two-line funext wrapper (`hasSum_of_eq`, private in
the module) is the honest family transport; `hasSum_nat_add_iff'`
(topological groups) is the only tail-shift at this pin, and it yields
`HasSum (fun n => f (n + 1)) (g − ∑ i ∈ range 1, f i)` with the
`range 1` sum needing `Finset.sum_range_succ`/`sum_range_zero` to
reduce (no `Finset.sum_range_1` here); `NormedSpace.exp_eq_tsum` at
matrix type rewrites into a **beta-redex** — follow it with an explicit
`show` of the β-reduced sum; `Tendsto.congr` at this pin takes a
*pointwise ∀* equality, not an `EventuallyEq`; `rw` cannot rewrite
under binders (use `simp only [theorem]` for applying a theorem inside
a `fun t => …`); scalar `2 • v` statements default `2` to ℕ unless the
vector is ascribed `(… : Fin 2 → ℝ)` and the scalar `(2 : ℝ)`;
`div_mul_cancel₀` takes its value argument first
(`div_mul_cancel₀ _ two_ne_zero`); and `neg_pos` is unusable at this
pin (its `0 < -a` shape mis-elaborates — derive `0 < -μ` by `linarith`).

Verification: `lake env lean` on the module and the QA file — zero
errors, zero warnings each; explicit `lake build` targets for both ✔;
`#print axioms` via `wip/heat_step4_axcheck.lean` on all thirty-one
new/rewritten declarations — `propext, Classical.choice, Quot.sound`
only; full `lake build` ✔ (2252 targets, "Build completed successfully",
detached per the recorded procedure; no warnings in the changed
modules); `lint_axioms` (9, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (1482 → 1503 QA
declarations, `Heat_QA` 25 → 46). Records updated: this proposal
(status header COMPLETE, this delivery record, open-next-step closed),
`proposals/README.md` (the High row retired to the Delivered table),
README (1503; the heat-semigroup sentence and module-table row gaining
eigenmode decay and the DC limit), the radar (axis 5 **re-scored
3.5 → 4.0** — the named trigger fired; QA axis count synced
1482/40 → 1503/40, held at 4.0), the scoreboard (both Direct rows, the
`lake build` row, lint row, a new interpretation bullet), the SGT
index map (Heat section +10 declaration rows, status line → Steps
0–4), the execution plan, and the activity log.

### Phase B, Step 3 — mass conservation (DELIVERED 2026-08-23, run
`20260823T092311Z-run-1`)

Delivered in `Scaffold/Mathlib/GraphTheory/Heat.lean` (QA extended at
`Scaffold/QA/SpectralGraph/Heat_QA.lean`, 17 → 25 theorem
declarations), all proved, zero new axioms per this proposal's own
mandate (count stays 9). `#print axioms` on all six new public and all
eight new QA declarations reads only `propext, Classical.choice,
Quot.sound`:

- **The headline `heatKernel_mulVec_onesVec`:** `heatKernel A t *ᵥ
  onesVec = onesVec` at every time, hypothesis-free — heat diffusing
  on the graph neither creates nor destroys total heat, through the
  shelf's `laplacian_ones_in_kernel` (`L *ᵥ 1 = 0` needs no symmetry:
  the Laplacian's row sums vanish identically). With Steps 1–2 this
  completes the external consumer's three-item interface (identity,
  semigroup law, mass conservation).
- **The general engine `exp_mulVec_eq_of_mulVec_eq_zero`:**
  `M *ᵥ v = 0 → NormedSpace.exp ℝ M *ᵥ v = v` — conservation for
  *any* kernel vector, not just `onesVec`. The route is the proposal's
  own sketch (positive powers annihilate `v`), but the interchange it
  needs had to be built, because of the run's central survey finding
  (below): the additive action `N ↦ N *ᵥ v` is continuous
  entrywise, pushes the series `HasSum` through `HasSum.map` (the same
  pattern the pin's own `Matrix.transpose_tsum` uses), and the pushed
  series collapses onto its `n = 0` term by `tsum_eq_sum` over `{0}`
  at `pow_add`-factorized power annihilation
  (`M^(n+1) = M^n * M`, `Matrix.mulVec_mulVec`).
- **The summability layer, built entrywise from scratch — the run's
  sharpest survey finding:** `NormedSpace.exp` at this pin is defined
  in the *topological-algebra* section (no norm), which is why
  `Heat.lean`'s statements elaborate with the Pi topology on matrices;
  the pin's normed `expSeries_summable'` therefore cannot be applied
  at matrix type without `letI`-ing the `linftyOp` norm (whose
  induced topology has no transfer lemma to the Pi one at this pin);
  and the pin has **no Pi-type `HasSum`/`Summable` lemmas at all**.
  Delivered instead: `abs_pow_apply_le` (`|(M ^ n) i j| ≤ B ^ n` at
  `B = ∑ p q, |M p q|`, by `Matrix.mul_apply`-induction — the entire
  matrix-analysis input, norm-free), `summable_exp_term` (comparison
  against `Real.summable_pow_div_factorial` through
  `Summable.of_norm_bounded`), the pin-gap assembler `hasSum_pi`
  (`Filter.tendsto_pi_nhds` + `Finset.sum_apply`), and the assembled
  `expSeries_hasSum_exp` (the exponential series converges to
  `NormedSpace.exp ℝ M` in the entrywise topology — the content the
  pin's normed section does not provide at matrix type, and the
  foundation Step 4's eigenbasis expansion can build on).
- **QA (8 new declarations):** conservation by **two independent
  routes to one statement** (the theorem on the asymmetric fixture vs
  the hand-computed route: the closed form `!![1-t, t; -t, 1+t]`
  multiplied onto `onesVec` entrywise); the raw kernel-instance check
  (`asymLaplacian_mulVec_ones_raw_QA` — the exact instance of
  `laplacian_ones_in_kernel` the theorem consumes, verified
  independently); the symmetric-fixture instantiation (conservation
  not locked to the square-zero accident); the proposal's named
  **per-component no-leakage witness** on the new disconnected `Fin 3`
  fixture `disAdj` (edge `{0,1}` + isolated vertex `2`): the
  `{0,1}`-component indicator checked `L`-harmonic raw from the
  definitions, then fixed by the engine at every time, with the
  isolated-vertex indicator fixed too — heat provably does not cross
  components, so the conservation statement is not accidentally
  vacuous on disconnected input; and the **kernel-hypothesis guard**
  (a non-kernel vector is provably *not* fixed: the exact kernel
  `!![0,1;-1,2]` sends `![1,0]` to `![0,-1]`, refuting the
  hypothesis-free strengthening with every other structural fact
  intact).

Pin-specific technique notes for future runs: application binds
tighter than `^`, so matrix-power entries need explicit parens
(`(M ^ n) i j`); `pow_succ'` at this pin factors the *wrong* way
(`a^(n+1) = a * a^n`) — use `pow_add` + `pow_one` for `M^n * M`;
`Filter.tendsto_congr` lives under `namespace Filter`
(`Filter.tendsto_congr`); `Finset.sum_apply` takes the index first
(`Finset.sum_apply x s f`); `Finset.sum_le_sum` needs the `f`/`g`
named arguments or the `OrderedAddCommMonoid` synthesis gets stuck
behind a metavariable; and `Finset.sum_le_sum_of_subset` is
canonically-ordered-only at this pin (unusable over ℝ) — singleton
bounds go through `Finset.sum_insert`/`Finset.insert_erase` splitting
plus `le_add_of_nonneg_right`. On the QA side: `Fin 3` cons-literals
resist `simp`'s index-2 reduction and `fin_cases`' `⟨n, ⋯⟩`-form
indices resist `rfl`, while kernel `decide` is blocked by
`Real.decidableEq`'s classical path — the robust fixture encoding is
an entrywise function (`Matrix.of fun i j => if … then 1 else 0`) with
function-form indicators, which `simp`/`norm_num` reduce at
`fin_cases` literals.

Verification: `lake env lean` on the module and the QA file — zero
errors, zero warnings each; explicit `lake build` targets for both ✔;
`#print axioms` via `wip/heat_step3_axcheck.lean` on all fourteen new
declarations — `propext, Classical.choice, Quot.sound` only; full
`lake build` ✔ (2252 targets, "Build completed successfully",
detached); `lint_axioms` (9, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (1474 → 1482 QA
declarations, `Heat_QA` 17 → 25).

### Phase B, Step 2 — the semigroup property (DELIVERED 2026-08-23, run
`20260823T074418Z-run-1`)

Delivered in `Scaffold/Mathlib/GraphTheory/Heat.lean` (QA extended at
`Scaffold/QA/SpectralGraph/Heat_QA.lean`, 10 → 17 theorem
declarations), all proved, zero new axioms per this proposal's own
mandate. `#print axioms` on both new public and all seven new QA
declarations reads only `propext, Classical.choice, Quot.sound`:

- **The semigroup law `heatKernel_mul_heatKernel`:**
  `heatKernel A s * heatKernel A t = heatKernel A (s + t)`, hypothesis-
  free (no symmetry; negative times included — the backward/growing
  semigroup per the Step-1 scope note). Route exactly as the sketch and
  the Step-0 survey recorded: the exponents `-(s • laplacian A)` and
  `-(t • laplacian A)` are scalar multiples of one matrix, hence
  commute (`(s • L) * (t • L) = (s * t) • (L * L)` both ways through
  `Algebra.smul_mul_assoc`/`Algebra.mul_smul_comm`/`smul_smul`), so the
  pin's `Matrix.exp_add_of_commute` applies — **with no ball/radius
  hypothesis**, the survey's norm-free finding holding exactly as
  recorded (re-verified against the pinned source this run: the wrapper
  `letI`s the `linftyOp` norm inside its own proof). The joined exponent
  reduces by `neg_add` + `add_smul`.
- **The every-time square-zero collapse
  `exp_neg_smul_eq_one_add_of_mul_self_eq_zero`:**
  `exp ℝ (-(t • M)) = 1 + -(t • M)` for every `t` when `M * M = 0` —
  the Step-1 `t = 1` handle generalized: the exponent squares to
  `(t * t) • (M * M) = 0`. This is what makes the QA fixture exactly
  evaluable at *symbolic* times, not just `t = 1`.
- **QA (7 new declarations):** the semigroup law witnessed by **two
  independent routes to one closed-form statement** — the raw route
  (`heatKernel_asym_semigroup_raw_QA`: both sides' closed forms
  `!![1-s, s; -s, 1+s]` and `!![1-t, t; -t, 1+t]` multiplied by hand
  through `Matrix.mul` on literals, every entry closed by `ring`,
  independent of the theorem) and the theorem route
  (`heatKernel_asym_semigroup_theorem_QA`: the law composed with one
  closed form) — a wrong time-combination constant anywhere in the
  delivered chain contradicts the hand computation; the **every-time
  closed form** `heatKernel asymAdj t = !![1-t, t; -t, 1+t]` for
  symbolic `t`; the **numeric instance** at `s = 2, t = 3`
  (`!![-4, 5; -5, 6]`); the **group property** `heatKernel asymAdj 1 *
  heatKernel asymAdj (-1) = 1` (forward-then-backward flow is the
  identity — the semigroup law and the time-zero identity, the
  consumer's two core interface items, working together); and the
  **degenerate `t = 0` identities** on the symmetric K₂ fixture where
  no closed form exists (both orders).

Verification: `lake env lean` on the module and the QA file — zero
errors, zero warnings each; explicit `lake build` targets for both ✔;
`#print axioms` via `wip/heat_step2_axcheck.lean` on all nine new
declarations — `propext, Classical.choice, Quot.sound` only; full
`lake build` ✔ (2252 targets, "Build completed successfully",
detached); `lint_axioms` (9, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (1467 → 1474 QA
declarations, `Heat_QA` 10 → 17).

### Phase B, Steps 0–1 — survey + the definition with symmetry and
identity (DELIVERED 2026-08-23, run `20260823T061507Z-run-1`)

Delivered in the new `Scaffold/Mathlib/GraphTheory/Heat.lean` (namespace
`SpectralGraphTheory`; QA at `Scaffold/QA/SpectralGraph/Heat_QA.lean`,
10 theorem declarations), all proved, zero new axioms per this proposal's
own mandate. `#print axioms` on every new public and QA declaration reads
only `propext, Classical.choice, Quot.sound`:

- **Step 0 (survey, recorded before any statement was written):** the
  pin's `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` is
  exactly the surface this proposal's sketch anticipated, and it is
  *purpose-built to be norm-free*: `Matrix.exp_add_of_commute`,
  `Matrix.isUnit_exp`, `Matrix.exp_neg`, `Matrix.exp_zsmul`,
  `Matrix.exp_conj`/`exp_conj'` each `letI` the `linftyOp` matrix norm
  *inside* their proofs, so none of the `_of_mem_ball`/radius hypotheses
  of the general Banach-algebra statements reach the caller — the sketch's
  `expSeries_radius_eq_top` concern does not arise at this pin, and
  Step 2 will not need it. Two naming corrections to the sketch: (1)
  there is no `Matrix.exp` declaration — the function is
  `NormedSpace.exp` applied at matrix type, with the `Matrix.*` names
  being wrapper lemmas (`Matrix.IsSymm.exp` at line 108 of the pinned
  file needs only `[Field 𝕂] [CommRing 𝔸] [TopologicalRing 𝔸]
  [Algebra 𝕂 𝔸] [T2Space 𝔸]`, all global instances for
  `Matrix V V ℝ` via `Mathlib/Topology/Instances/Matrix.lean`: the Pi
  topology, `Matrix.topologicalRing` at `[Fintype V]`, T2); (2) the
  matrix-level `exp_add_of_commute` takes its norm hypotheses on the
  *entry* ring (`NormedRing ℝ`, `NormedAlgebra ℝ ℝ`, `CompleteSpace ℝ`
  — all global), so no norm choice leaks into Step 2's statement either.
  Also recorded: the repo's `Perturbation.Duhamel` already carries a
  vector-level damped eigenbasis semigroup (`heatApply`, built "no
  `Matrix.exp`" on purpose) — a different representation of the same
  dynamics; a matrix↔vector bridge is Step-4 business, not Step-1's.
- **Step 1 (delivery):** `heatKernel A t := NormedSpace.exp ℝ
  (-(t • laplacian A))` — the external consumer's first interface item
  ("heat evolution specialized to `laplacian A`"); **`heatKernel_isSymm`**
  (`(heatKernel A t).IsSymm` under `A.IsSymm`, every `t`: the shelf's
  `laplacian_symmetric` through `Matrix.IsSymm.smul`, `.neg`, and the
  pin's `Matrix.IsSymm.exp`); **`heatKernel_zero`** (`heatKernel A 0 = 1`,
  hypothesis-free, via `zero_smul`/`neg_zero`/`NormedSpace.exp_zero`);
  and the general **square-zero exponential collapse**
  `exp_eq_one_add_of_mul_self_eq_zero` (`M * M = 0 → exp ℝ M = 1 + M`,
  by `NormedSpace.exp_eq_tsum` + `tsum_eq_sum` over `Finset.range 2`
  with `pow_add`/`pow_two` killing every power from the second on) —
  the closed-form handle that makes exact QA evaluation possible
  whenever the exponent is square-zero.
- **Statement-shape notes (recorded in the module docstring before
  stating):** `t` ranges over all of ℝ — for negative `t` this is the
  growing backward semigroup, the same caveat `Perturbation.Duhamel`
  documents; Steps 2–4 carry `0 ≤ t` only where their mathematics needs
  it. `heatKernel` is total in `A` (no symmetry hypothesis to define);
  symmetry is a theorem under `hA`, and QA proves the hypothesis
  load-bearing.
- **QA (`Heat_QA.lean`):** fixtures — the symmetric edge `K₂`, and the
  asymmetric `asymAdj = !![0,1;-1,0]` whose Laplacian
  `!![1,-1;1,-1]` is square-zero (degrees `(1,-1)`). Witnesses: the
  time-zero identity on both fixtures (all entries computed; and
  hypothesis-free, holding where the symmetry theorem cannot be
  applied); symmetry through the theorem on `K₂` at every `t` with the
  hypothesis derived from the literal; the **exact closed form**
  `heatKernel asymAdj 1 = !![0,1;-1,2]` (every entry computed through
  the collapse — the spike itself caught the first draft's wrong `(1,1)`
  entry `0` where the truth is `1 + -(-1) = 2`, the exact failure mode
  numeric QA exists for); the **symmetry hypothesis
  refuted-on-omission** (the same computed kernel is provably
  asymmetric, entries `1 ≠ -1`, with the fixture's `IsSymm` provably
  violated at the same pair — `hA` load-bearing, not decorative); and
  the **sign witness** `heatKernel asymAdj 1 ≠ NormedSpace.exp ℝ
  (1 • laplacian asymAdj)` (with `+L` the value is `1 + L =
  !![2,-1;1,0]`; entrywise at `(0,0)`: `0 ≠ 2`) — pinning the
  definition's negation and scalar action against a concretely
  evaluated alternative.

Verification: `lake env lean` on the module and the QA file — zero
errors, zero warnings each; explicit `lake build` targets for both ✔;
`#print axioms` (via `wip/heat_axcheck.lean`) on all four public and ten
QA declarations — `propext, Classical.choice, Quot.sound` only; **full
`lake build` ✔ (2252 targets, "Build completed successfully",
detached)**; `lint_axioms` (**9**, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1467 QA
declarations / 9 explicit axioms / 0 sorries**; `Heat_QA` a new file row
at 10). Spike discipline followed (`wip/heat_spike.lean` green before
transfer). Records updated: this proposal, `proposals/README.md`, README,
the radar (axis 5 held at 3.5 with the QA count synced and the hold
logged per protocol — Step 1 is the definition layer, not the
heat-kernel *statements* Steps 2–4 deliver), the scoreboard, the SGT
index map, the coverage map (the matrix-exponential survey correction),
backlog item 5, the execution plan, and the activity log. Nothing
committed.

### Phase A — reversibility (detailed balance) (DELIVERED 2026-08-22,
run `20260822T061043Z-run-1`)

Delivered in `GraphTheory.Stationary` (the module that already holds the
adjoint-stationarity theorem the stationary measure rests on), all
proved, zero new axioms, **no new definitions** (the proposal's own
mandate — composes `deg`/`vol`/`walkTransitionMatrix`/
`transitionMatrix_symmetric` rather than growing the interface).
`#print axioms` on every new public theorem reads only `propext,
Classical.choice, Quot.sound`:

- **Step 1 (irregular case)**, exactly the proposal's one-line route:
  `walk_detailed_balance` — `deg A i * P i j = deg A j * P j i`, both
  sides exactly `A i j` (the degree weight cancels `walkTransitionMatrix`'s
  `D⁻¹` row factor through the new entry lemma
  `Normalized.walkTransitionMatrix_apply`; `A.IsSymm` identifies the two
  adjacency entries); `walk_detailed_balance_measure` — the π-form
  `deg A i / vol A Finset.univ * P i j = deg A j / vol A Finset.univ *
  P j i`, obtained by side-condition-free division of the degree
  identity (`div_mul_eq_mul_div`), so **no volume-positivity hypothesis
  is carried** (for positive degrees on a nonempty vertex type the
  volume is positive and `π` is the stationary measure certified by
  `walkTransitionMatrix_transpose_mulVec_deg`);
  `diagonal_deg_mul_walkTransitionMatrix_isSymm` — the matrix
  packaging `(D * P).IsSymm` (reversibility *is* symmetrizability; the
  balance identity is exactly its entrywise `IsSymm` condition), the
  self-adjointness interface the mixing-time program's ℓ²(π) proxy
  consumes.
- **Step 2 (regular case)**: delivered as
  `transitionMatrix_detailed_balance_uniform` — the uniform-measure
  balance for `RandomWalk.transitionMatrix`, *composed* from the
  already-proved `RandomWalk.transitionMatrix_symmetric` (found on the
  shelf by the pre-edit survey) rather than re-proved; the proposal's
  own "worth stating separately only if a consumer needs it" clause was
  resolved in favor of stating it, since the uniform form is the
  regular-cone mirror of `walk_detailed_balance_measure` and costs one
  rewrite.
- **Mathlib survey (recorded before proving):** no detailed-balance,
  reversibility, or Markov-chain-structure machinery anywhere in the
  pin (the coverage map already records the random-walk/Markov absence
  upstream; no correction needed).
- **QA** (`Stationary_QA.lean`, 12 → 26 declarations), the proposal's
  two prescribed witnesses: **positive** — the P₃ path fixture
  (degrees 1, 2, 1), balance instantiated through the theorems at every
  index pair and cross-checked by raw literal arithmetic (degree form
  `1 = 1` at `(0,1)`; π-form `1/4 = 1/4` with `vol = 4` pinned
  independently from the degrees; the symmetrized matrix's
  off-diagonal entries both `1` — the two directed flows carry equal
  degree-weighted mass; the uniform form instantiated at the edge);
  **negative** — the asymmetric matrix `!![0,2;1,0]` with positive
  degrees `(2, 1)`, where the hypothesis-free balance statement is
  refuted (`deg 0 * P 0 1 = 2 ≠ 1 = deg 1 * P 1 0`) and the symmetry
  hypothesis is provably violated at the same entry pair — `hA` is
  load-bearing, not decorative.
- **Statement-shape note (recorded before stating):** the π-form was
  initially drafted with a `vol ≠ 0` side condition; the delivered
  statement carries none — the identity holds for any `vol` value by
  the division route, making the theorem strictly more general. Also
  fixed during delivery: bare `univ` in a statement elaborates as an
  auto-bound *local* finset (not `Finset.univ`) — the house form
  `(Finset.univ : Finset V)` is used explicitly.

Verification: `lake env lean` on `Normalized.lean`, `Stationary.lean`,
and `Stationary_QA.lean` — zero errors (the two Stationary warnings are
the documented pre-existing ones, verified identical in HEAD);
`#print axioms` on all public and headline QA theorems — three standard
axioms only; oleans built; **full `lake build` ✔ (2227 targets,
"Build completed successfully")**; `lint_axioms` (10, unchanged),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(**1095 QA declarations / 10 explicit axioms / 0 sorries**). Radar axis
5 **held at 3.0** per protocol (a composed identity within the
walk-operator interface family counted at the same day's mixing-time
re-score, not a new capability family; the hold and the natural
re-score triggers logged in the radar). One records repair delivered
alongside: the radar axis-5 *table row* and "Weakest axes" paragraph,
which the 2026-08-22 mixing-time run had left stale at score 2.5 with
the closed gap still named, were synced to the recorded 3.0 state.

## Phase C: The heat-flow derivative and a first-order remainder bound (opened 2026-08-23/24, priority High)

**Status:** Proposed — `sgt-gaps.md` item 3 (from `spectral-proof`),
delivered after Phase B, so this is a second, more specific request on
the interface Phase B just finished: "the standard analytic input for
the rewrite's dissolution theorem." Promoted straight to High, same
resolution class as Phase B and Tikhonov Phase 2.

**The ask, precisely:** for `heatKernel A t := NormedSpace.exp ℝ
(-(t • laplacian A))` (`Heat.lean:208`), the standard matrix-exponential
calculus at time zero,

```lean
HasDerivAt (fun t : ℝ => heatKernel A t *ᵥ x) (-(laplacian A *ᵥ x)) 0
```

plus an explicit first-order remainder bound on a bounded interval
(Euclidean norm or entrywise) — a semigroup-only equivalent is
acceptable if it supports a Taylor/mean-value bound for an observable
formed from boundary coordinates. **State symmetry/nonnegative-weight
hypotheses only where mathematically needed** — the requester is
explicit that lifecycle-leakage interpretation stays in `spectral-proof`,
not here.

**Cost, surveyed:** this repository already has the exact proof pattern
for a vector-level `HasDerivAt` through a finite spectral sum —
`Duhamel.lean:191`'s `heatApply_hasDerivAt`, proved by differentiating
`∑ i, Real.exp (-s * eigvalOf M hM i) * (…)` termwise via
`HasDerivAt.sum` and `HasDerivAt.exp`, exactly the shape
`Heat.lean:605`'s `heatKernel_mulVec_eq_sum` already expands
`heatKernel A t *ᵥ x` into. At `t = 0` every exponential factor is `1`
and the sum collapses to `∑ i, −λᵢ (vᵢ ⬝ᵥ x) • vᵢ = −(laplacian A *ᵥ x)`
by the shelf's own eigenbasis-expansion identity
(`eigvecOf_expansion_apply`) applied to `laplacian A *ᵥ x` directly —
the derivative-at-zero statement should not need `A.IsSymm` beyond what
`heatKernel_mulVec_eq_sum` already assumes to exist. The remainder
bound is the one genuinely new piece: a finite-sum Taylor/Lagrange
estimate bounding `‖heatKernel A t *ᵥ x − x + t • (laplacian A *ᵥ x)‖`
by a second-derivative bound on a compact interval — likely via
`Real.exp`'s own quadratic remainder bound (`Real.abs_exp_sub_one_sub_id_le`
or the pin's Taylor-series remainder API for `Real.exp`) applied
termwise through the same finite eigenbasis sum, then summed with
Cauchy–Schwarz for the Euclidean-norm form.

**Build order:**

- **Step 0:** survey the pin's exact `Real.exp` remainder/Taylor lemmas
  (`Mathlib.Analysis.SpecialFunctions.Exp` and
  `Mathlib.Analysis.Calculus.Taylor`) before committing to a statement
  shape for the remainder bound.
- **Step 1:** `heatKernel_mulVec_hasDerivAt_zero` — the derivative-at-zero
  identity above, adapting `Duhamel.lean`'s termwise-sum technique to
  `heatKernel_mulVec_eq_sum`.
- **Step 2:** the first-order remainder bound on a bounded interval
  `[0, T]`, in whichever norm Step 0's survey finds cleanest — entrywise
  is likely cheaper than Euclidean and may be what the consumer actually
  needs (state both if the entrywise form is nearly free once the
  Euclidean one is proved).

**QA:** a positive witness computing both the derivative and a concrete
remainder bound on a small fixture at a specific `t`, cross-checked
against `heatKernel`'s direct exponential-series value (the same
cross-check pattern `Heat.lean`'s own QA already uses); a boundary
witness showing the bound degrades as expected as `T` grows, so the
"first-order" claim isn't accidentally global.

**No new axioms; no proposal-scope change beyond this phase.** One step
per run.

## Phase C delivery record

### Phase C, Steps 0 + 1 — survey + the derivative at zero (DELIVERED
2026-08-23, run `20260823T153334Z-run-1`)

Delivered in `Scaffold/Mathlib/GraphTheory/Heat.lean` (QA extended at
`Scaffold/QA/SpectralGraph/Heat_QA.lean`, 46 → 50 theorem
declarations), all proved, zero new axioms per this proposal's own
mandate (count stays 9). `#print axioms` on both new public and all
four new QA declarations reads only `propext, Classical.choice,
Quot.sound`:

- **Step 0 (survey, recorded before any statement was frozen, and in
  the module's own docstring):** the pin carries
  `Real.abs_exp_sub_one_sub_id_le`
  (`Mathlib/Data/Complex/Exponential.lean:1211`) — `|x| ≤ 1 →
  |Real.exp x - 1 - x| ≤ x ^ 2` — exactly the termwise quadratic
  remainder engine the proposal's cost sketch guessed, so Step 2's
  statement shape is committed to the termwise route through
  `heatKernel_mulVec_eq_sum` at `|t * λᵢ| ≤ 1`, summed entrywise (the
  pin's `Analysis/Calculus/Taylor.lean` exists but adds Taylor-coordinate
  plumbing the plain exponential bound does not need). The run's
  sharpest elaboration finding, recorded in the module: **stating the
  derivative theorem's proof directly in vector form times out at
  `whnf`** on a variable vertex type `V` (the `HasDerivAt.smul_const` /
  `HasDerivAt.sum` instance synthesis over the `Pi` norm instances) —
  the `Fin 2` QA statements elaborate fine, which is what isolated the
  trap to the variable-type instance search. The delivered route is
  two-layer by design: the entrywise engine plus a one-line assembly.
- **Step 1 (delivery), the headline
  `heatKernel_mulVec_hasDerivAt_zero`:**
  `HasDerivAt (fun t : ℝ => heatKernel A t *ᵥ x) (-(laplacian A *ᵥ x))
  0` — the infinitesimal generator statement `d/dt e^{-tL} x |₀ = -L x`
  in `HasDerivAt` form, exactly the requester's asked shape. The
  entrywise engine `heatKernel_mulVec_apply_hasDerivAt_zero` is
  Duhamel's `heatApply_hasDerivAt` technique verbatim, adapted to the
  Step-4 eigenbasis expansion `heatKernel_mulVec_eq_sum`: each mode's
  factor differentiated by `HasDerivAt.exp`/`.mul_const`, the finite
  sum by `HasDerivAt.sum`; at `t = 0` every factor is `1` and the
  derivative sum is re-expanded to `-(L *ᵥ x)` by
  `eigvecOf_expansion_apply` with the shelf's self-adjoint pairing
  transfer `dotProduct_eigvecOf_mulVec` (`v i ⬝ᵥ (L *ᵥ x) = λ i (v i
  ⬝ᵥ x)` — the pre-edit survey's finding that this lemma already
  exists on the shelf saved the run its one planned sub-proof). The
  vector form assembles by the pin's `hasDerivAt_pi`
  (`Analysis/Calculus/Deriv/Prod.lean`). `hA : A.IsSymm` is carried
  exactly as `heatKernel_mulVec_eq_sum` already requires — nothing
  more (the proposal's own minimal-hypothesis instruction).
- **QA (4 new declarations):** the derivative value on K₂ at
  `x = ![1, 3]` pinned to `![2, -2]` by **two independent routes to one
  statement** — the theorem route (`heatKernel_edge_deriv_theorem_QA`,
  the Laplacian action supplied by the raw entrywise computation
  `edgeLaplacian_mulVec_dc`) vs. the raw route
  (`heatKernel_edge_deriv_raw_QA`: the Step-4 closed form
  `1 + ((e^{-2t}-1)/2) • L` plus scalar calculus only — `d/dt
  (e^{-2t}-1)/2 |₀ = -1` — no eigenbasis, no expansion, no
  `hasDerivAt_pi`); plus the **infinitesimal-conservation cross-check
  in both directions** (`heatKernel_edge_deriv_conservation_QA`:
  derivative `0` at `onesVec` through the Phase C theorem +
  `laplacian_ones_in_kernel`, vs.
  `heatKernel_edge_deriv_conservation_route2_QA`: the same from Step
  3's conservation alone, the flow being *constant* — Phase C and
  Phase B Step 3 checking each other).

Pin-specific technique notes for the Step-2 run: Duhamel's
`(hasDerivAt_id t).neg.mul_const c` chain produces the unparenthesized
`-t * c` function shape, while `heatKernel_mulVec_eq_sum`'s factors
are `Real.exp (-(t * λᵢ))` — build the inner `HasDerivAt` at the
parenthesized shape (`((hasDerivAt_id 0).mul_const λ).neg`) and let
the stated derivative stay unnormalized (`-(1 * λᵢ)`, reduced only in
the final value identification); `HasDerivAt.const_mul` at this pin
elaborates the constant on the *left* (`fun y => d * id y` — use
`.mul_const` for right-multiplication and `2 * t`-shaped inner
functions via `.const_mul`); `Finset.sum_neg_distrib` exists only as
the `to_additive` child of `prod_inv_distrib` (not greppable as a
declaration — it is usable); a per-term `rw` chain through
`Pi.smul_apply, smul_eq_mul` leaves a `mul_assoc` residue (close with
`ring`, not a second `rw`); and the QA t=0 closed-form extension needs
the `by_cases` split (the collapse lemma requires `t ≠ 0`; at `t = 0`
both sides compute directly).

Verification: spike first (`wip/heatC_spike.lean` green, all
`#print axioms` the standard three; eight rounds to green — the fixes
became the trap list above, the decisive one being the entrywise-plus-
`hasDerivAt_pi` restructure after the vector-form `whnf` timeout) then
transfer; `lake env lean` on the module and the QA file — zero errors,
zero warnings each; explicit `lake build` targets for both ✔;
`#print axioms` via `wip/heatC_axcheck.lean` on all six new
declarations — `propext, Classical.choice, Quot.sound` only; **full
`lake build` ✔ (2252 targets, "Build completed successfully"; no
warnings in the changed modules)**; `lint_axioms` (**9**, unchanged),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(**1507 QA declarations / 9 explicit axioms / 0 sorries**, idempotent;
`Heat_QA` 46 → 50). Records updated: this proposal (the Phase C
delivery record, open-next-step → Step 2), `proposals/README.md` (the
High row), README (1507; the heat-semigroup sentence and module-table
row gaining the derivative), the scoreboard (both Direct rows, the
`lake build` row, lint row, a new interpretation bullet), the SGT
index map (Heat section +2 declaration rows, Phase C status line), the
execution plan, and the activity log. Nothing committed; the prior
runs' uncommitted deliveries preserved untouched.

### Phase C, Step 2 — the first-order remainder bound (DELIVERED
2026-08-23, run `20260823T170118Z-run-1`; the proposal COMPLETE)

Delivered in `Scaffold/Mathlib/GraphTheory/Heat.lean` (QA extended at
`Scaffold/QA/SpectralGraph/Heat_QA.lean`, 50 → 66 theorem
declarations), all proved, zero new axioms per this proposal's own
mandate (count stays 9; `#print axioms` on both new public and all
fifteen new public QA declarations reads only `propext,
Classical.choice, Quot.sound`):

- **The core bound `heatKernel_firstOrder_remainder_apply_le`**: on
  the window `ht : ∀ i, |t * λᵢ| ≤ 1`,
  `|(heatKernel A t *ᵥ x) a - x a + t * ((laplacian A *ᵥ x) a)| ≤
  t ^ 2 * ∑ i, λᵢ ^ 2 * |vᵢ ⬝ᵥ x| * |vᵢ a|` — the entrywise
  (boundary-observable) form the requester's dissolution theorem reads
  (a coordinate functional *is* the "observable formed from boundary
  coordinates" of the original ask; the Euclidean-norm variant would
  add Cauchy–Schwarz plumbing with a √n loss and no new content, and is
  deliberately not stated — a consumer naming one can adjoin it). The
  committed Step-0 route verbatim: the flow coordinate expanded by
  `heatKernel_mulVec_eq_sum`, `x a` by `eigvecOf_expansion_apply`, and
  the generator coordinate by the same expansion with
  `dotProduct_eigvecOf_mulVec` transferring `vᵢ ⬝ᵥ (L *ᵥ x)` to
  `λᵢ (vᵢ ⬝ᵥ x)`; the three sums combined termwise (the pin's
  to_additive children `Finset.sum_sub_distrib`/`Finset.sum_add_distrib`,
  used right-to-left); the triangle by `Finset.abs_sum_le_sum_abs`; and
  per mode the surveyed `Real.abs_exp_sub_one_sub_id_le` at
  `x := -(t * λᵢ)` (its `|exp x - 1 - x| ≤ x ^ 2` matching the
  `-(-tλ) = +tλ` sign by one `ring`). **Hypotheses minimal**: `hA`
  exactly as the expansion requires — *no* nonnegativity, the bound
  being per-mode and valid for any symmetric network, PSD or not; and
  the window hypothesis is stated per eigenvalue, the weakest usable
  form.
- **The interval packaging `heatKernel_firstOrder_remainder_interval`**:
  if `T` itself meets the window, every `t ∈ [0, T]` obeys the same
  bound — the uniform-in-time form on a bounded interval, the
  hypothesis transfer `|t · λ| = t|λ| ≤ T|λ| = |T · λ| ≤ 1` by
  monotonicity at `0 ≤ t ≤ T`. The proposal's `[0, T]` phrasing made
  literal.

QA (`Heat_QA.lean`, 15 new public + 1 private declaration), the
proposal's named pair and their support:

- **Support layer** — the K₂ eigenvalue inventory, stated per vertex
  index (not through the sort machinery): `edge_eigvalOf_nonneg`
  (PSD at the unit eigenvector), `edge_eigvalOf_sum` (trace `2`),
  `edge_eigvalOf_prod` (determinant `0`), `edge_eigvalOf_cases`
  (every `eigvalOf` is `0` or `2`, both orderings covered by
  `fin_cases` at the vanishing product factor), and
  `edge_eigvalOf_exists_two` (exactly one mode at `2` — the trace
  forces it).
- **The eigen-sum constant `edge_remainder_sum_eq`**: the theorem's
  spectral constant at `x = ![1, 3]`, `a = 0` on K₂ is *exactly* `4` —
  through the eigenmode structure `edge_eigvecOf_mode_two` (every
  λ = 2 eigenvector is `c • ![1, -1]` with `2c² = 1`, from the
  coordinate eigen-equation via the new
  `edgeLaplacian_mulVec_coords` plus the unit normalization
  `eigvecOf_inner`), making the mode's contribution
  `4 · 2|c| · |c| = 8c² = 4` **independent of the spectral-theorem
  choice's orientation sign** — the QA constant is robust to however
  Mathlib happened to pick the eigenvector.
- **The concrete-bound witness** (positive witness, cross-checked):
  `heatKernel_edge_remainder_bound_half_QA` instantiates the theorem
  at the window endpoint `t = 1/2` (hypothesis by `edge_window`) with
  the RHS evaluated to the concrete `1`;
  `heatKernel_edge_remainder_value_raw` pins the *raw* remainder
  `1 - 2t - e^{-2t}` at every nonzero time through the independently
  QA'd closed form `heatKernel_edge_closed_QA` — no eigenbasis, no
  exponential bound lemma; `heatKernel_edge_remainder_cross_QA`
  composes them into `Real.exp (-1) ≤ 1`.
- **The boundary-degradation witness**:
  `heatKernel_edge_remainder_degrades_QA` exhibits *both* times'
  concrete constants — `|1/2 - e^{-1/2}| ≤ 1/4` (at `t = 1/4`, through
  the interval-route instance `heatKernel_edge_remainder_interval_QA`)
  and `e⁻¹ ≤ 1` (at `t = 1/2`) — so a wrong power of `t` in the
  theorem (t¹ would give `2` and `1/2`; t³ would give `1/2` and
  `1/16`) contradicts at least one component; the "first-order" claim
  is pinned as exactly quadratic.
- **The fence** `heatKernel_edge_remainder_window_fenced_QA`: the
  window hypothesis provably *fails* at `t = 1` on K₂ (some mode has
  `|1 · 2| = 2 ≰ 1`), so the bound is local to `[0, 1/2]` on this
  fixture by construction — the first-order claim is not accidentally
  global.

Pin-technique notes recorded for future runs: `set`-abstracting
`eigvalOf`/`eigvecOf` mid-proof breaks subsequent `rw`s (new terms
reintroduce the un-abstracted spelling — prove `have`s at the original
spelling or avoid `set`); `Finset.sum_sub_distrib` rewrites
sum-of-differences to difference-of-sums, so assembling the three-sum
combination needs it *right-to-left*; the final `t²`-factoring must
split `(t * λᵢ)²` per-term *before* `← Finset.mul_sum` (the
i-dependent square is not a constant factor); the numeral `2 • v`
elaborates as ℕ-smul (`nsmul`) at `V → ℝ` — always annotate
`(2 : ℝ) •`; `rw [edgeLaplacian_eq]` under an `eigvecOf` term dies
with motive-not-type-correct (the rewrite would touch the proof
`laplacian_symmetric …` inside `eigvecOf`'s arguments) — derive
coordinate facts on fresh goals (`edgeLaplacian_mulVec_coords`) and
combine by `linarith`; `mul_self_abs` does not exist at this pin
(`← abs_mul` + `abs_of_nonneg (mul_self_nonneg _)` instead);
`eigvecOf_inner`'s diagonal instance reduces with
`simp only [if_pos rfl, if_true]` (`if_pos rfl` alone leaves
`if True then _ else _`); and in `degrades`-style composites, rewrite
numeric arguments *before* combining (`2 * (1/4)` collapses inside
`Real.exp`'s argument under one `rw [harg]` pass, so follow-ups must
match the collapsed form).

Verification: spike first (`wip/heatC2_spike.lean` core, then
`wip/heatC2_qa_spike.lean` QA, both green before transfer; the
recorded trap list above is the fixes en route); `lake env lean` on the
module and the QA file — zero errors, zero warnings each; explicit
`lake build` targets for both ✔; `#print axioms` via
`wip/heatC2_axcheck.lean` on all seventeen new declarations —
`propext, Classical.choice, Quot.sound` only; **full `lake build` ✔
(2252 targets, "Build completed successfully"; zero warnings in the
changed modules — the log's warning mass is the documented Mathlib-pin
doc-string set)**; `lint_axioms` (**9**, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1522/9/0**,
idempotent; `Heat_QA` 50 → 66). Records updated: this proposal (status
header, the Phase C Step-2 delivery record, open-next-step retired),
`proposals/README.md` (the High row moved to Delivered), README (1522;
heat-semigroup paragraph + module-table row), the radar (axis 5 + QA
axis **held** at 4.0/4.0 with the delivery recorded and counts synced
1507/40 → 1522/40), the scoreboard (both Direct rows, the `lake build`
row, lint row, a new interpretation bullet), the SGT index map (Heat
section +2 declaration rows, Phase C status line), the execution plan,
and the activity log. Nothing committed; the prior runs' uncommitted
deliveries preserved untouched.
