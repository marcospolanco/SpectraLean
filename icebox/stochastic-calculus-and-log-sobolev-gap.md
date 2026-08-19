# Icebox: Stochastic Calculus and Log-Sobolev Formalization Gap

**Status:** Technical finding, not a proposal. No priority; not something an
autonomous run should act on. Written 2026-08-18 alongside
`proposals/finite-relative-entropy.md`, which delivers the cheap half of
`docs/6_SGT_BACKLOG.md` item 6 ("entropy and reversibility interfaces,
Dirichlet/functional inequalities, dissipation"). This entry covers the
two pieces of that same backlog item that are not cheap: continuous-time
stochastic dynamics, and the sharp functional inequalities
(`docs/7_SGT_RADAR.md` axis 3's named-absent log-Sobolev) that would
describe how fast such dynamics forget their initial condition.

## The question this answers

Two related questions, both worth real technical answers rather than a
wave at "it's hard":

1. "Why not formalize noisy/randomly-perturbed dynamics on a graph
   directly, instead of only the deterministic heat semigroup
   (`reversibility-and-heat-semigroup.md` Phase B)?"
2. "`docs/7_SGT_RADAR.md` axis 3 names log-Sobolev as absent right next
   to Poincaré — Poincaré is basically already available for free
   (`lambda2_variational` *is* the graph Poincaré inequality under a
   different name), so why isn't log-Sobolev the next easy step?"

## Where the two gaps meet

They are one gap, not two, because log-Sobolev inequalities are stated
*about* continuous-time stochastic dynamics: the classical form bounds
relative entropy's dissipation rate along a diffusion process (`d/dt
Ent(p_t) ≤ -c · I(p_t)`, entropy against Fisher information), which
presupposes exactly the trajectory-of-distributions object item 1 asks
about. You cannot state the sharp inequality without first having
something for it to be an inequality *about*.

## Part 1: continuous-time stochastic dynamics

### What it would take

A time-indexed family of probability distributions `p_t` evolving under
noise plus drift — the Fokker–Planck / Kolmogorov-forward picture, or
equivalently a stochastic process `X_t` whose law is `p_t`, built from an
Itô integral against Brownian motion. Either route needs:

- A construction of Brownian motion (or at minimum, a filtered
  probability space supporting a continuous martingale with the right
  quadratic variation).
- An Itô integral and Itô's formula (the stochastic chain rule), to make
  sense of "solves a stochastic differential equation" at all.
- Existence/uniqueness theory for SDE solutions analogous to (and
  strictly harder than) the deterministic Picard–Lindelöf theorem
  already surveyed in `icebox/lyapunov-stability-formalization-gap.md`.

### Verified against the pinned Mathlib (2026-08-18)

- `Probability/Martingale/` exists but is **discrete-time only** —
  exactly the machinery Scaffold already consumes via
  `matrix_azuma_hoeffding` (`Scaffold/Mathlib/Probability/Concentration/
  Matrix/Azuma.lean`). A discrete-time martingale is not a substitute for
  a continuous-time process; there is no bridge between them in the
  pinned tree.
- A search for `brownian`, `ito`, and `stochasticprocess` (any casing,
  anywhere in `.lake/packages/mathlib/Mathlib`) returns **zero hits**.
- `Analysis/ODE/{Gronwall,PicardLindelof}.lean` (surveyed already in the
  Lyapunov entry) covers *deterministic* trajectories only; nothing
  there generalizes to a stochastic driving term.

Continuous-time stochastic calculus is, in short, not partially there —
it is entirely absent, at every layer, from the pinned Mathlib.

## Part 2: log-Sobolev inequalities

### What it would take

Given `docs/7_SGT_RADAR.md`'s own framing (axis 3, "Absent: Poincaré,
log-Sobolev"), it is worth being precise about why one half of that pair
is nearly free and the other is not:

- **Poincaré (spectral gap) is already substantively available.** The
  graph Poincaré inequality — `Var(f) ≤ (1/λ₂) · (Dirichlet energy of
  f)` — is a restatement of the already-proved `lambda2_variational`
  (`docs/7_SGT_RADAR.md:46`). What is missing is only the *name* and the
  variance-form packaging, not the mathematical content; this is a
  candidate for a small follow-on note to an existing module, not a new
  proposal, and is **not** part of what this icebox entry is about.
- **Log-Sobolev is a strictly stronger, qualitatively different
  inequality**, bounding *entropy* by a Dirichlet-energy-like quantity
  (`Ent(f²) ≤ C · ∫ |∇f|²`) rather than *variance*. It gives exponential
  decay of relative entropy, not merely of variance — the standard tool
  (Bakry–Émery, Diaconis–Saloff-Coste for Markov chains specifically)
  for sharp mixing-rate statements stronger than what the ℓ² mixing
  route in `proposals/mixing-time-bound.md` targets. It requires the
  entropy functional `proposals/finite-relative-entropy.md` would
  deliver *and* a genuinely new comparison argument between that
  functional and the Dirichlet form — not a corollary of anything
  currently proved or proposed.

### Verified against the pinned Mathlib (2026-08-18)

A search for `sobolev` combined with `entropy` or `log`, and a direct
search for `logsobolev`/`log-sobolev` under any naming, across
`.lake/packages/mathlib/Mathlib`: **zero hits**. (Mathlib's `Sobolev`
results, where they exist, are about Sobolev *spaces* for PDE theory —
an unrelated meaning of the word from a different subfield — not the
functional inequality named here.)

## Why this is a different tier than the finite-entropy proposal

`proposals/finite-relative-entropy.md` is, despite the word "entropy," a
two-line `Finset.sum` definition and one classical Jensen-inequality
corollary — genuinely cheap because Mathlib's convexity API already does
the load-bearing work. Both items in this entry are the opposite case:
Part 1 needs an entire subfield of analysis (stochastic calculus) that
does not exist at any layer in the pinned Mathlib, and Part 2 needs a
comparison theorem that has never been proved for any graph in this
repository's setting and is not a corollary of anything on the shelf,
Mathlib-side or Scaffold-side. Matched against this repository's own
"Grow the crust" standard — reuse what's proved, admit only what's
genuinely load-bearing and well-cited, never invent free-floating
machinery — neither item clears the bar for admission today.

## Three real paths forward, honestly ordered by cost

1. **Take `proposals/finite-relative-entropy.md` and stop there.** It
   delivers the entropy functional and its basic properties, which is
   most of what a downstream consumer citing "entropy" on a finite graph
   would actually need, without touching either gap in this entry.
2. **Formalize the discrete-time log-Sobolev inequality for a finite
   Markov chain directly**, bypassing continuous-time stochastic calculus
   entirely. The Diaconis–Saloff-Coste discrete log-Sobolev constant is
   defined purely in terms of the transition matrix and the stationary
   measure — both already on the shelf (`Normalized.lean`,
   `Stationary.lean`) — with no Brownian motion or Itô calculus required.
   This is real, scoped, well-known math and the honest "cheaper door
   in" if this axis is ever prioritized; it still needs
   `finite-relative-entropy.md`'s functional and is still a materially
   harder proof than anything delivered on this axis so far, so it
   should be scoped and evaluated as its own proposal, not assumed free.
3. **Build continuous-time stochastic calculus from scratch.** Real and
   valuable in principle, but a multi-month, research-grade
   formalization program on its own — comparable in scale to, and
   arguably larger than, the Golden–Thompson/Lieb gap already iceboxed in
   `icebox/matrix-chernoff-formalization-gap.md`. Not a means to an end
   for any currently-named consumer.

## Re-survey trigger

If the pinned Mathlib version advances and adds stochastic-calculus
(`Probability/Ito`, `Probability/BrownianMotion`, or similar) or
log-Sobolev/hypercontractivity machinery, re-run the searches above
before relying on this finding — per the same discipline
`docs/8_MATHLIB_COVERAGE_MAP.md` applies to its own rows.
