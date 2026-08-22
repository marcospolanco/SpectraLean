# Proposal: Relative Entropy and Shannon Entropy for Finite Distributions

**Status:** DELIVERED 2026-08-22 — both steps in one run (the operating
instruction's own clause), pure hard crust, **zero new axioms** (count
stays 10; `#print axioms` on all nine public theorems reads only
`propext, Classical.choice, Quot.sound`). Module
`Scaffold/Mathlib/InformationTheory/Entropy.lean`, QA
`Scaffold/QA/InformationTheory/Entropy_QA.lean` (31 declarations). See
the delivery record at the bottom. Closes the entropy half of backlog
item 6 (the reversibility half landed earlier the same day).

**Original status line (superseded):** Assistant's assessment of
project direction, requested 2026-08-18 (closes the entropy half of a
backlog item this project has already opened the other half of).
Authorizes no Lean changes, axiom admissions, document rewrites, or
external publication.

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

None — both steps delivered. The named optional follow-ons stay exactly
as scoped under "Deferred and removed" (spectral entropy `H(t)` of the
eigenvalue distribution is a two-line application of Step 2 once its
consumer decision is made; continuous/measure-theoretic entropy and
log-Sobolev remain out of scope). No operator decision is pending on
this proposal.

## Delivery record (2026-08-22)

**Both steps, one run, zero new axioms.** The module
`Scaffold/Mathlib/InformationTheory.Entropy` (namespace
`Scaffold.InformationTheory`) is built from one scalar definition —
`klTerm a b := if a = 0 then 0 else a * Real.log (a / b)`, the visible
junk convention this proposal mandates — with `klDiv p q := ∑ i,
klTerm (p i) (q i)` and `shannonEntropy p := -∑ i, klTerm (p i) 1`
(the proposal's exact sign; the negated sum makes each summand's
nonpositivity and the quantity's nonnegativity visible). Statement
shapes are exactly the proposal's: `klDiv_nonneg` and
`klDiv_eq_zero_iff` under `0 ≤ p`, `∑ p = 1`, `0 < q`, `∑ q = 1`;
`shannonEntropy_le_log_card` and `shannonEntropy_eq_log_card_iff` under
the `p`-hypotheses only (the `Nonempty V` side condition *derived*
from `∑ p = 1`, not assumed — an empty type admits no probability
vector). A small bonus theorem `shannonEntropy_nonneg` fell out of the
sign-visible definition (`Finset.single_le_sum` + `log_le_log`).

**Route decision (recorded before stating):** the mandated Jensen-API
survey ran first and found the whole shelf present —
`ConcaveOn.le_map_sum` (Jensen.lean:71), `StrictConcaveOn.lt_map_sum`
(:145), `StrictConcaveOn.eq_of_map_sum_eq` (:169),
`StrictConcaveOn.map_sum_eq_iff'` (:233), `strictConcaveOn_log_Ioi`
(SpecificFunctions/Basic.lean:63) — so this proposal's stop-and-record
clause (a missing strict-equality Jensen variant) was **not**
triggered. The delivered route is nonetheless the *term-wise*
information inequality: `sub_le_klTerm` from
`Real.one_sub_inv_le_log_of_pos` (`1 − x⁻¹ ≤ log x`, Log/Basic.lean:281)
and `eq_of_klTerm_eq_sub` from `Real.log_lt_sub_one_of_pos`
(Log/Basic.lean:230) applied at the reciprocal. This is the same
textbook proof (Cover–Thomas 2.6.3's own route via `log t ≤ t − 1`
term-wise) with strictly less plumbing: no Finset-`smul` Jensen side
conditions, no `Ioi`-membership, no support-finset filtering — and the
`a = 0` junk case is discharged *inside* the per-term bound
(`0 ≥ −b`), where its strictness is even stronger (gap `= b > 0`), so
the equality case `p = q` needs no `∑_{support} q` argument at all.
Gibbs' inequality is then one `Finset.sum_le_sum`, and the equality
case one gap-decomposition
(`Finset.sum_eq_zero_iff_of_nonneg` + per-index
`eq_of_klTerm_eq_sub`). The uniform bridge `klDiv_apply_uniform`
(`klDiv p (fun _ => n⁻¹) = log n − shannonEntropy p`) is the only
place the two quantities meet; both entropy theorems compose it with
the corresponding Gibbs statement, with `sum_inv_card_eq_one`
supplying the uniform normalization.

**QA (31 declarations, `QA/InformationTheory/Entropy_QA.lean`, all
`#print axioms`-clean):** the four prescribed witnesses plus two
additions. (1) The biased pair `(3/4, 1/4)` vs `(1/2, 1/2)` on `Fin 2`
with the divergence hand-computed to `(1/4)·log(27/16)` by raw
`log_pow`/`log_mul` algebra and pinned **strictly positive** — the
bound is not vacuously tight. (2) The diagonal `klDiv pBias pBias = 0`
computed from the definition alone, then fed *through* the equality
iff to recover `pBias = pBias`, and the forward direction used to
derive `klDiv pBias qFair ≠ 0` from `pBias ≠ qFair`. (3) The uniform
distribution on `Fin 4` computed to `log 4` two ways (definition; the
equality case of the maximum). (4) The non-uniform
`(1/2, 1/6, 1/6, 1/6)` pinned **strictly** below `log 4` — strictness
available *only* through the equality-case iff (the plain bound gives
`≤`), the load-bearing use of the strict route this proposal's QA plan
requires — plus its divergence-side companion `0 < klDiv pSkew u` via
the bridge. (5) The delta distribution `(1, 0, 0, 0)` with entropy
exactly `0`, the `p i = 0 ↦ 0` junk convention exhibited, and strictly
below the maximum. (6) The uniform bridge itself numerically
cross-checked at the fair coin: `klDiv_bridge_bias` proves
`¼·log(27/16) = log 2 − ¼·log(256/27)` from the two independently
hand-computed pins — a wrong sign or constant in the bridge would
fail to match this arithmetic.

**Pin-specific API notes for future QA on this snapshot:**
`Real.log_pow` takes `(x : ℝ) (n : ℕ)` explicitly with *no*
hypotheses; `Real.log_inv` takes its argument explicitly
(`Real.log_inv 4`); `Finset.sum_one` does not exist at that name (the
constant-sum route is `Finset.sum_const` + `Finset.card_univ` +
`Nat.smul_one_eq_cast`); coefficient identities like
`4 * ((1/4) * atom) = atom` need `ring_nf`, not `norm_num` (norm_num
does not fold numeric coefficients across an atom product); and
`Finset.sum_sub_distrib` is oriented `∑ (f − g) = ∑ f − ∑ g`.

**Verification:** `lake env lean` on the module and QA — zero errors,
zero warnings each; explicit target builds
(`lake build Scaffold.Mathlib.InformationTheory.Entropy` /
`...Scaffold.QA.InformationTheory.Entropy_QA`) ✔; `#print axioms` on
the nine public and thirteen headline QA theorems ✔ (three standard
axioms only); umbrella import added and **full `lake build` ✔ (2229
targets, "Build completed successfully", zero errors)**; `lint_axioms`
(10, unchanged), `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (**1243 QA declarations / 10 axioms / 0
sorries**; `Entropy_QA` a new file row at 31). Records updated:
module/QA docstrings, umbrella, this proposal, `proposals/README.md`
(Medium row → Delivered; progress paragraph), the new
`index/map/information_theory.md` + map README row, scoreboard (counts,
both Direct rows, the `lake build` row — with a recorded scope
correction that the default target certifies the public umbrella
closure, not the QA tree — and a new interpretation bullet), radar
(QA axis held at 4.0, count synced 1243/37, sync logged), README
(counts, module table, proved list, and the stale
conditional-on-Davis–Kahan persistence note corrected), backlog item
6 (entropy half delivered), the execution plan, and the activity log.
