# Proposal: Reversibility and the Heat Semigroup on the Graph Laplacian

**Status:** Active — Phase A (reversibility/detailed balance, both of its
steps) DELIVERED 2026-08-22 as pure hard crust in `GraphTheory.Stationary`
(zero new axioms, no new definitions); Phase B (the heat semigroup)
remains open behind its recorded operator-decision gate. Originally
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
- **Phase B's gate is explicitly conditional and not yet open.**
  `docs/6_SGT_BACKLOG.md:93-98` (item 5, "Graph-dynamical systems"):
  "*Only when a named SGT consumer needs them*: diffusion / heat flow
  `e^{-tL}`... The retained persistence package is a compatibility
  example, not a roadmap driver." This proposal names a consumer — see
  "Open next step" — but per this repository's own center-out policy,
  naming one in a proposal is not the same as an operator adopting it.

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
- Do not begin Phase B without the operator decision named below on
  record — Phase A carries no such precondition and may start
  immediately.

## Open next step

**Phase A — DELIVERED 2026-08-22** (see the delivery record below). No
Phase A work remains; the regular-case Step 2 was delivered as the
uniform-measure corollary composed from `transitionMatrix_symmetric`
(the already-on-shelf theorem the pre-edit survey found), exactly the
proposal's own "otherwise Step 1 subsumes it" branch.

**Phase B needs one operator decision first, per `docs/6_SGT_BACKLOG.md`
item 5's own gate:** whether this proposal — which names itself as a
consumer, and needs none of `mixing-time-bound.md`'s still-open
walk-eigenvalue-transfer step — counts as the "named SGT consumer" that
gate requires, or whether that decision should wait for
`mixing-time-bound.md` to reach a point where it explicitly asks for a
continuous-time comparison. This is a scope call in the same spirit as
`admit-perron-frobenius.md`'s axis-opening decision, not a routine
backlog item; an autonomous run should not start Phase B Lean work
without it recorded here.

## Delivery record

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
