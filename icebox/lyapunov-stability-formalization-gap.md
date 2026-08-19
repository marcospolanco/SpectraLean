# Icebox: Lyapunov Stability Formalization Gap

**Status:** Technical finding, not a proposal. No priority; not something an
autonomous run should act on. Written 2026-08-18 while scoping
`proposals/reversibility-and-heat-semigroup.md`, whose Phase B (the heat
semigroup `e^{-tL}`) delivers the discrete/spectral shadow of a Lyapunov
argument as a free corollary. Kept here because the question "why not just
also formalize Lyapunov stability properly" is worth a real technical
answer, and the finding is general — it applies to any future proposal
that wants a continuous-time trajectory-stability result, not just this
one.

## The question this answers

"Lyapunov stability is completely standard math — why isn't there a
proposal for it?" A fair question, since nothing about Lyapunov's direct
method itself is exotic (Lyapunov, 1892; every ODE and control-theory
text covers it). The answer is not that the *theorem* is suspect — it's
that Scaffold and the pinned Mathlib have almost none of the
*infrastructure* the theorem is stated in terms of.

## What "Lyapunov stability" actually requires, precisely

The classical statement: given `dx/dt = f(x)` and a scalar function
`V`, if `V(x) > 0` away from an equilibrium `x*` and `dV/dt =
∇V(x)·f(x) ≤ 0` along every trajectory, then `x*` is stable (and
asymptotically stable if the inequality is strict). Two ingredients are
load-bearing and neither is a small ask:

1. **An actual trajectory** — a function `x : ℝ → E` (or `ℝ≥0 → E`)
   that *solves* the ODE, with existence/uniqueness already settled, not
   just a discrete-time sequence or a closed-form matrix-exponential
   object.
2. **A derivative-along-that-trajectory statement** — `dV/dt` at a point
   means `HasDerivAt (V ∘ x) _ t`, chained through `f` via the chain
   rule, not just "the matrix has this algebraic property."

Neither of these currently exists anywhere in this repository.

## Verified against Scaffold (2026-08-18)

Checked directly, not presumed. Every dynamical object Scaffold defines
today is one of:

- A **discrete-time sequence** of matrices, `ℕ → Matrix V V ℝ`
  (`Scaffold/Mathlib/GraphTheory/Dynamics.lean`'s `TimeVaryingGraph`,
  consumed by `Derived.{EventStream,ProjectorDrift}`) — no continuum,
  no derivative.
- A **closed-form algebraic object** at a single time `t` — the heat
  semigroup proposal's `heatKernel A t := exp(-t • laplacian A)` is a
  *value*, not a trajectory; its "`t`-dependence" is handled entirely
  through algebraic identities (`exp_add_of_commute`, monotonicity of
  `evals`), never through `HasDerivAt` or any calculus on `t`.

There is no file anywhere in `Scaffold/` that defines a solution curve to
an ODE, takes a derivative of a scalar functional along one, or states a
monotonicity-along-a-trajectory theorem. This is not a gap in one
module; it is an entire missing category of formalization that nothing
in the existing SGT center touches.

## Verified against the pinned Mathlib (2026-08-18)

- **`grep -rli "lyapunov"` across all of `.lake/packages/mathlib`:
  zero hits.** No Lyapunov-function definition, no stability theorem,
  under any naming.
- **`Mathlib/Dynamics/`** exists but covers a different meaning of
  "dynamics" entirely: `TopologicalEntropy`, `BirkhoffSum`,
  `FixedPoints`, `Circle/RotationNumber`, `Ergodic`. None of it is
  ODE trajectory stability.
- **`Mathlib/Analysis/ODE/{Gronwall,PicardLindelof}.lean`** is the
  closest real asset: `PicardLindelof` gives existence/uniqueness of
  solutions under a Lipschitz hypothesis, and `Gronwall` gives bounds on
  the *distance between two trajectories* (`dist_le_of_trajectories_ODE`,
  `ODE_solution_unique`) via `HasDerivAt`-based comparison arguments.
  This is genuine, usable machinery — but it proves trajectories stay
  close together or coincide, not that a chosen scalar functional
  decreases along one. Building a Lyapunov-stability theorem from it
  would mean writing that connective layer from scratch: Scaffold would
  be the one contributing the "take `V`, take a solution curve from
  Picard–Lindelöf, chain-rule `dV/dt` through `f`, conclude
  monotonicity" argument, not importing it.

## Why this is a different tier than the heat-semigroup work

The heat-semigroup proposal (`reversibility-and-heat-semigroup.md`,
Phase B) is, despite invoking `exp`, still finite-dimensional algebra in
disguise: `heatKernel A t` is one matrix per `t`, related to
`heatKernel A s` by an algebraic identity (`exp_add_of_commute`), and
its eigenmode-decay theorem is a statement about `Real.exp` composed
with the already-proved sorted spectrum `evals` — no calculus on `t` is
ever performed, because none is needed. Genuine Lyapunov stability is a
qualitatively different kind of claim: it is a statement about a
*curve* through state space and the *derivative* of a functional along
that curve. Everything Scaffold has built so far — Courant–Fischer,
Cheeger, electrical flows, Thomson's principle, the heat semigroup — is
eigenbasis expansion, quadratic forms, and dimension counting. None of
it is calculus-on-a-parameter, and neither is most of what the pinned
Mathlib offers in this neighborhood.

## Three real paths forward, honestly ordered by cost

1. **Take the free corollary and stop there.** The discrete/spectral
   monotonicity fact — the non-constant-subspace energy strictly
   decreases in `t` under `heatKernel A t` — is already in reach as a
   one-line addition to the heat-semigroup proposal's Step 4, with zero
   new machinery. This captures the actual mathematical content anyone
   citing "Lyapunov" here almost certainly wants, without the word
   "Lyapunov" or any trajectory-calculus claim attached to it.
2. **Build the minimal connective layer on top of `PicardLindelof` +
   `Gronwall`.** Real and honest work — state a solution curve for
   `dx/dt = -M x` (M symmetric PSD) via Picard–Lindelöf, define `V(x) =
   xᵀMx`, and prove `HasDerivAt (V ∘ x) (-2 * (x t)ᵀM²(x t)) t` by the
   chain rule, hence monotonicity. This is a genuine, scoped,
   well-known-math proposal — but it is new infrastructure (Scaffold's
   first ODE-trajectory work), not a build-order step tacked onto an
   existing one, and should be written up and prioritized as such if
   ever pursued, not folded silently into another proposal's scope.
3. **Wait for a named consumer.** Per this repository's center-out
   policy, infrastructure this size (a first calculus-on-trajectories
   layer) shouldn't be admitted speculatively. Nothing in the current
   SGT backlog (`docs/6_SGT_BACKLOG.md`) names a consumer that needs
   continuous-time trajectory stability rather than the discrete/
   spectral version route 1 already covers.

## Re-survey trigger

If the pinned Mathlib version advances and adds Lyapunov-stability or
general ODE-stability machinery to `Mathlib/Analysis/ODE/` or
`Mathlib/Dynamics/`, re-run the searches above before relying on this
finding — per the same discipline `docs/8_MATHLIB_COVERAGE_MAP.md`
applies to its own rows.
