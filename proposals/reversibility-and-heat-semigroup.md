# Proposal: Reversibility and the Heat Semigroup on the Graph Laplacian

**Status:** Proposed. Assistant's assessment of project direction, requested
2026-08-18 (closes the two named-but-unclaimed gaps on the random-walk/
diffusion axis). Authorizes no Lean changes, axiom admissions, document
rewrites, or external publication.

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

**Phase A** is unblocked now: begin with Step 1 (irregular-case detailed
balance).

**Phase B** needs one operator decision first, per `docs/6_SGT_BACKLOG.md`
item 5's own gate: whether this proposal — which names itself as a
consumer, and notes it needs none of `mixing-time-bound.md`'s still-open
walk-eigenvalue-transfer step — counts as the "named SGT consumer" that
gate requires, or whether that decision should wait for
`mixing-time-bound.md` to reach a point where it explicitly asks for a
continuous-time comparison. This is a scope call in the same spirit as
`admit-perron-frobenius.md`'s axis-opening decision, not a routine
backlog item; an autonomous run should not start Phase B Lean work
without it recorded here.
