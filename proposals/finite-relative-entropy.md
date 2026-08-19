# Proposal: Relative Entropy and Shannon Entropy for Finite Distributions

**Status:** Proposed. Assistant's assessment of project direction, requested
2026-08-18 (closes the entropy half of a backlog item this project has
already opened the other half of). Authorizes no Lean changes, axiom
admissions, document rewrites, or external publication.

Assessed from `docs/6_SGT_BACKLOG.md` item 6, `docs/3_SPECTRAL_THEORY.md`
§4, and a fresh survey of `.lake/packages/mathlib/Mathlib/Analysis/Convex/
{Jensen,SpecificFunctions/Basic}.lean` and a repository-wide search for
existing Kullback–Leibler or entropy machinery (none found beyond scalar
binary entropy — see "Why this axis").

## Recommendation

Define Kullback–Leibler divergence (relative entropy) and Shannon entropy
for finite probability distributions on `Fintype V` — the two-line
classical definitions, proved from Mathlib's existing convexity API rather
than from scratch:

```
klDiv (p q : V → ℝ) : ℝ := ∑ i, p i * Real.log (p i / q i)
shannonEntropy (p : V → ℝ) : ℝ := -∑ i, p i * Real.log (p i)
```

with the two textbook facts that make either quantity usable: Gibbs'
inequality (`0 ≤ klDiv p q`, equality iff `p = q`) and the entropy upper
bound it implies (`shannonEntropy p ≤ Real.log (Fintype.card V)`,
maximized exactly at the uniform distribution).

## Why this axis

`docs/6_SGT_BACKLOG.md:100-104` (item 6, "Thermodynamics / statistical
mechanics"): "*Gated on item 1–2 stability:* entropy and reversibility
interfaces, Dirichlet/functional inequalities, dissipation. No admission
before the Markov prerequisites are stable." `proposals/reversibility-
and-heat-semigroup.md` opened this gate and delivered the reversibility
half. This proposal delivers the entropy half — the same item, the
remaining named piece, under the same now-satisfied precondition (items
1–2 are recorded delivered).

There is also a concrete, already-named consumer on record, not a
hypothetical one: `docs/3_SPECTRAL_THEORY.md:52-69` describes a
"retained research material, not an active implementation agenda"
pipeline (the x90 detector) whose flow explicitly ends at "spectral
entropy H(t), rate dH/dt, truncation error" computed from a graph's
selected eigenvalues. That document names the quantity and leaves it
undefined. This proposal does not resurrect that pipeline (it is
explicitly not an active agenda, and reviving it is a separate
decision), but it does mean `shannonEntropy` is not a definition
invented on spec — a real document in this repository already assumes
its existence.

**Verified absent from Mathlib**, not merely uncited: a search for
`kullback`, `KLDiv`, `RelativeEntropy`, and `entropy` across the pinned
tree turns up only `Analysis/SpecialFunctions/BinaryEntropy.lean`
(entropy of a *single* probability `p ∈ [0,1]`, not a distribution over a
finite type, and not relative entropy between two distributions) and a
docstring in `MeasureTheory/Measure/Tilted.lean` that *mentions*
Kullback–Leibler divergence as a possible application of exponential
tilting without defining it. Neither gives a usable interface for a
graph-indexed finite distribution.

## Why this is cheap despite being genuinely absent

Unlike the icebox'd stochastic-calculus/log-Sobolev gap (see
`icebox/stochastic-calculus-and-log-sobolev-gap.md`), this is not new
infrastructure — it is two `Finset.sum` definitions plus one classical
convexity argument, and Mathlib already has the load-bearing piece:
`Real.log` is proved strictly concave on `(0, ∞)`
(`strictConcaveOn_log_Ioi`, `Analysis/Convex/SpecificFunctions/
Basic.lean:63`), and the finite weighted Jensen inequality is proved in
general form (`StrictConcaveOn.lt_map_sum`,
`Analysis/Convex/Jensen.lean:145`). Gibbs' inequality is the textbook
one-step corollary of applying that Jensen inequality to `log` with
weights `p i` at points `q i / p i` — exactly the standard information-
theory proof (Cover & Thomas, *Elements of Information Theory*, Theorem
2.6.3, "information inequality"), not a from-scratch analytic argument.
No measure-theoretic probability machinery is needed: everything stays
in Scaffold's existing finite-`Fintype`, `Finset.sum` style, the same way
`degreeSqrt`/`degreeInvSqrt` stayed diagonal-only rather than reaching
for a general matrix square root.

## Build order

### Step 1: Kullback–Leibler divergence and Gibbs' inequality

Define `klDiv p q` as above, with the standard convention that a term
where `p i = 0` contributes `0` regardless of `q i` (state this as an
explicit `if p i = 0 then 0 else ...` in the definition, not left
implicit — this repository's own convention, per the electrical-
resistance proposal's honestly-witnessed junk-fallback precedent, is to
make junk cases visible rather than silent).

Prove `klDiv_nonneg`: for `p, q : V → ℝ` with `∀ i, 0 ≤ p i`, `∑ i, p i =
1`, `∀ i, 0 < q i`, `∑ i, q i = 1`, `0 ≤ klDiv p q`. Route: apply
`StrictConcaveOn.lt_map_sum` (or the non-strict `ConcaveOn.le_map_sum`
for the equality case) to `Real.log`, weights `p i`, points `q i / p i`
restricted to `{i | p i ≠ 0}`; the sum of weighted points telescopes to
`∑ q i ≤ 1` — Jensen gives `∑ p i * log(q i/p i) ≤ log(∑ q i) ≤ log 1 =
0`, i.e. `klDiv p q = -∑ p i * log(q i/p i) ≥ 0`.

Prove `klDiv_eq_zero_iff`: `klDiv p q = 0 ↔ p = q` (on the support where
`p i ≠ 0`), from the strict-concavity equality case
(`StrictConcaveOn.eq_of_map_sum_eq`) — the load-bearing use of "strict"
rather than plain concavity.

### Step 2: Shannon entropy and its maximum

Define `shannonEntropy p` as above (same `p i = 0 ↦ 0` convention).
Prove `shannonEntropy_le_log_card`: `shannonEntropy p ≤ Real.log
(Fintype.card V)`, by instantiating Step 1's `klDiv_nonneg` at `q i :=
(Fintype.card V : ℝ)⁻¹` (the uniform distribution) and unfolding —
`klDiv p uniform = Real.log (Fintype.card V) - shannonEntropy p`, so
nonnegativity of the left side is exactly the bound. Prove the equality
case (`shannonEntropy p = Real.log (Fintype.card V) ↔ p = uniform`)
directly from Step 1's equality case at the same instantiation, at no
extra proof cost.

### Deferred and removed

- **Spectral entropy specifically** (`H` of the normalized eigenvalue
  distribution `evals / trace`, the quantity `docs/3_SPECTRAL_THEORY.md`
  names) — a two-line application of Step 2 once `evals`
  nonnegativity/PSD is in scope, but reviving the retained x90 pipeline
  it belongs to is explicitly out of scope for this proposal and is its
  own separate decision.
- **Continuous / measure-theoretic relative entropy** — out of scope by
  design; Scaffold is `Fintype V` throughout, and the finite definition
  above is the correct-weight version for everything this repository
  currently represents.
- **Log-Sobolev inequalities** — the natural next consumer of
  `shannonEntropy`, but a materially harder, still-absent result; see
  `icebox/stochastic-calculus-and-log-sobolev-gap.md`, which names this
  proposal as its prerequisite rather than folding the two together.

## QA plan

- Positive witness: `klDiv` computed by hand between two concrete
  distributions on `Fin 2` (e.g. a biased pair `(3/4, 1/4)` against
  `(1/2, 1/2)`) and checked strictly positive — not just `≥ 0` from the
  theorem, but a genuine nonzero numeric instance, guarding against the
  bound being vacuously tight everywhere.
- Equality witness: `klDiv p p = 0` computed directly from the
  definition, independent of the theorem, and cross-checked against
  `klDiv_eq_zero_iff`.
- Entropy witness: `shannonEntropy` of the uniform distribution on `Fin
  4` computed to `Real.log 4` two ways — directly from the definition and
  through `shannonEntropy_le_log_card`'s equality case.
- Negative witness: a non-uniform distribution on `Fin 4` with strictly
  smaller entropy than `Real.log 4`, confirming the bound is strict away
  from uniform (load-bearing use of the strict-concavity route from Step
  1, not just the non-strict inequality).

## Operating instructions for an autonomous run

- One step per run; both steps are small enough that a single run may
  cover both if the first lands cleanly.
- **No new axioms.** Both steps are direct corollaries of
  `strictConcaveOn_log_Ioi` and Mathlib's general Jensen inequality
  lemmas. If the strict-equality case turns out to need a Jensen variant
  not present in the pinned Mathlib, stop and record the precise
  obstruction rather than admitting anything — this proposal's entire
  cost case rests on that machinery already existing.
- Survey Mathlib's `Analysis/Convex/Jensen.lean` API precisely (the exact
  lemma signatures, not just their names) before writing Scaffold
  statements, per this repository's standing rule.

## Open next step

Unblocked now — no operator decision required (unlike
`reversibility-and-heat-semigroup.md`'s Phase B, this axis's backlog gate
is already open and this proposal names its own consumer directly rather
than needing one adopted). Begin with Step 1.
