# The Entropy Leg of the Mixing Program: Pinsker, the D ≤ χ² Bridge, and Entropy Decay

**Status:** COMPLETE — delivered 2026-09-01 by run
`20260901T174415Z-run-1`, session `ses_fa1ee00b0ffehfb6e5wqiiijBT`
(zero new axioms; count stays 5; QA 3544 → 3566)

**Home of the delivery:** `Scaffold/Mathlib/InformationTheory/Entropy.lean`
(generic layer), `Scaffold/Mathlib/GraphTheory/Mixing.lean` (Pinsker +
the decay theorems), `Scaffold/Mathlib/GraphTheory/Oversmoothing.lean`
(the entropy floor), QA in `Scaffold/QA/SpectralGraph/Mixing_QA.lean`.

## Why this, why now

The standing handoff (2026-09-01, after the uniform-`t_mix` delivery)
left three candidates: the reverse TV → χ² calculus (no consumer
named), log-Sobolev (axis 3's remaining named gap, "consumer-gated on
a named consumer for an entropy inequality composing
`InformationTheory.Entropy`'s Gibbs bound"), and the operator-gated
items. The gate names a *missing consumer*, and
`InformationTheory.Entropy`'s own module docstring recorded that
consumer's intent from birth ("downstream consumers this serves: the
mixing-time program's `chiSquareDistance` is the quadratic member of
the same family of distribution-distances, and relative entropy
against the stationary measure is the classical refinement of the same
ℓ²(π) geometry") — intent never materialized: the entropy module has
zero graph-level consumers. This milestone builds the consumer first.
After it, log-Sobolev's adoption is an operator choice pointing at a
concrete on-shelf statement (entropy decay at an LSI rate replacing
the χ²-piggyback bound), not a missing-machinery gap.

The mixing program's distance ledger motivates the shape: TV and χ²
each have a decay family (χ² `chiSquareDistance_le_of_connected`, its
continuous twin, and the TV conversions) and a floor family (the
spectral TV/χ² floors, 2026-09-01). Entropy has neither. This
delivers both sides for the third classical distance:

- **Decay:** `D(ν_t ‖ π) ≤ χ²(t, x) ≤ r^{2t}((πx)⁻¹−1)` (discrete,
  the χ² theorem's exact hypothesis set) and the continuous-time twin
  at `contChiSquareDistance_le`'s hypothesis set — entropy decays at
  the χ² rate because `D ≤ χ²` termwise (`log u ≤ u − 1`).
- **Floor:** Pinsker (`2·TV² ≤ D`) composed with the delivered
  spectral TV floor
  (`walkDistribution_tvDistance_ge_of_eigenpair`) — the floor
  family's first non-TV member: on the periodic chain `K₂`, entropy
  never decays (`D = log 2` at every time, exactly pinned in QA).

## The statements

Generic layer (`Entropy.lean`; all proved, zero axioms):

1. `klTerm_le_sq_div : klTerm a b ≤ (a − b)² / b` for `0 ≤ a`,
   `0 < b` — the termwise `D ≤ χ²` engine (`log_le_sub_one_of_pos`
   at `a/b`, scaled).
2. `klDiv_le_sum_sq_div : klDiv p q ≤ ∑ i, (p i − q i)² / q i` —
   the entropy–χ² bridge, in exactly the sum shape
   `chiSquareDistance` carries (load-bearing: the walk-level decay
   theorem is a one-line composition *because* the shapes match).
3. `sum_klTerm_ge_klTerm` — the two-block **log-sum** bound
   `klTerm (∑_S p) (∑_S q) ≤ ∑_{i∈S} klTerm (p i) (q i)` — proved by
   rescaling to block-conditional probability vectors and applying
   Gibbs' inequality (`sub_le_klTerm`) on the block: the first
   consumer of the entropy module's machinery *inside another proof*,
   precisely the "entropy inequality composing the Gibbs bound" the
   log-Sobolev gate asked for.
4. `klTerm_add_klTerm_one_sub_ge_two_sq` — the **binary two-point
   Pinsker bound**: `2(a − b)² ≤ klTerm a b + klTerm (1−a) (1−b)` for
   `a ∈ [0, 1]`, `0 < b < 1`. Route (decided after the first-order
   scalar-bounds route was found insufficient — see the technique
   record): the explicit FTC identity, for `a ≥ b`,
   `d(a‖b) = ∫_b^a (a−t)/(t(1−t)) dt` (antiderivative
   `t ↦ a·log t + (1−a)·log(1−t)`), the integrand compared pointwise
   against `4(a−t)` by AM-GM (`t(1−t) ≤ 1/4` on `(0,1)`), and
   `∫_b^a 4(a−t) dt = 2(a−b)²`. The statement is symmetric under
   `(a,b) ↦ (1−a,1−b)`, so the `a ≥ b` instance closes both.

Graph layer (`Mixing.lean`, TV section extension; `Oversmoothing.lean`
floor section extension):

5. `tvDistance_le_sqrt_half_klDiv` — **Pinsker's inequality** in the
   shelf's vector form: `tvDistance p q ≤ √(klDiv p q / 2)` for
   probability vectors `p` and strictly positive `q`. Assembly: the
   TV-as-positive-part identity (`TV = ∑_{p>q}(p−q) = a − b` at
   `a = p(S)`, `b = q(S)`, `S = {q < p}`), the two-block
   decomposition of `klDiv` through (3), and (4).
6. `klDiv_walkDistribution_le` — **entropy decay**, discrete:
   `D(ν_t ‖ π) ≤ r^{2t}·((πx)⁻¹−1)` at exactly
   `chiSquareDistance_le_of_connected`'s hypothesis set (the bridge
   (2) composed with the delivered χ² theorem).
7. `klDiv_contWalkDistribution_le` — the **continuous-time twin** at
   `contChiSquareDistance_le`'s hypothesis set:
   `D ≤ e^{−2tλ₂(L_sym)}·((πx)⁻¹−1)`.
8. `klDiv_walkDistribution_ge_of_eigenpair` (in `Oversmoothing.lean`,
   beside its TV floor) — the **entropy floor**: `2·((1/2)·|1−μ|^t·
   |(√D⁻¹ v) x|/c)² ≤ D(ν_t ‖ π)` at the TV floor's exact hypothesis
   set, Pinsker composed with
   `walkDistribution_tvDistance_ge_of_eigenpair`.

## Step-0: degenerate corners (checked before stating)

- **The q-zero Pinsker corner (real, fenced in QA).** At
  `q = (1, 0)`, `p = (1/2, 1/2)` on `Fin 2`: `klTerm (1/2) 0`
  evaluates to `(1/2)·log((1/2)/0) = (1/2)·log 0 = 0` through
  `div_zero` and `Real.log_zero` — the junk convention silently drops
  the mass where `q` is zero and `p` is not. Then `klDiv p q = 0`
  while `tvDistance p q = 1/2`, so the un-guarded statement reads
  `1/2 ≤ 0`: materially false. The strict `0 < q i` hypothesis is
  load-bearing (the same class as `tvDistance_le_half_sqrt`'s mass
  guard); QA refutes the un-guarded form.
- **The b ∈ {0,1} binary corners.** The binary bound (4) at `b = 0`
  with `a > 0` has a junk left side (`klTerm a 0 = a·log 0 = 0` and
  then `2a² ≤ 0` is false); at `b = 1`, `a < 1` likewise. Stated with
  `0 < b < 1`; the mixing application supplies `b = π(S) ∈ (0,1)`
  strictly because `π` is entrywise positive (and the `S = ∅`/`S = univ`
  cases have `a = b`, where both sides are `0` and the statement is
  closed before the binary bound is invoked).
- **The a ∈ {0,1} edges of the binary bound** are genuine (not junk):
  at `a = 1` the statement is `log(1/b) ≥ 2(1−b)²`, attained in the
  limit `b → 1`; the FTC route handles them uniformly because the
  antiderivative `a·log t + (1−a)·log(1−t)` never evaluates a log at
  `0` (the coefficient vanishes first).
- **The `klTerm` junk convention at `p i = 0`** (zero terms
  contribute exactly `0`): inherited from the entropy module's own
  discipline; every graph-level hypothesis set supplies `0 ≤ ν_t`
  (`walkDistribution_nonneg` / its continuous twin) and `0 < π`
  (`stationaryVec_pos`), exactly the standing-hypothesis pattern of
  the χ² layer.

## Design decisions

- **Route for the binary bound.** The first-order scalar-bounds route
  (Lemma-A `log t ≥ 2(t−1)/(t+1)` on the first term + the proved
  `log t ≥ 1 − 1/t` on the second) was worked through and *fails*:
  it yields only `(a−b)²/(a+b)`, insufficient when `a + b > 1/2` —
  the second term genuinely needs second-order information. The FTC
  identity route is one-line-per-step and honest; it needs
  `intervalIntegral` imports in `Entropy.lean` (Mathlib calculus, not
  measure theory of the kind the mixing scoping records excluded —
  the *definitions* remain junk-safe finite sums; the integral is a
  proof device only, inside one private lemma).
- **Placement.** Pinsker's vector form needs both `tvDistance`
  (GraphTheory) and `klDiv` (InformationTheory); it goes in
  `Mixing.lean`'s TV section (the import is acyclic — InformationTheory
  imports no graph module). The floor consumer goes beside the TV
  floor in `Oversmoothing.lean` (same import addition). `Entropy.lean`
  keeps every generic (graph-free) fact.
- **No new distance object.** `klDiv` against `stationaryVec` is
  already a real definition composing the two modules; no new
  `entropyMixingTime` object is introduced. A `t_mix`-style entropy
  packaging would be a follow-on gated on a consumer, exactly as the
  TV proposal gated its own `t_mix` object.

## QA plan (in `Mixing_QA.lean`, new section)

On the triangle (π uniform `1/3`, `r = 1/2`, the standing fixture):
exact `D(ν₁ ‖ π) = log(3/2)` from the raw law literal; the bridge
instance `log(3/2) ≤ χ²(1) = 1/2` with both sides independently
pinned; the decay instance at `t = 1, 2` (at `t = 2`, the exact
`D = (1/4)log(3/4) + (3/4)log(9/8)` pinned and bounded by `1/8`
through `log ≤ x − 1`); the vector-Pinsker instance
`2·(1/3)² ≤ log(3/2)`; the entropy-floor instance `2·(1/4)² = 1/8 ≤
log(3/2)`; the binary bound pin at `(a,b) = (1/2, 3/4)`:
`(1/2)log(4/3) ≥ 1/8`. On `K₂` (periodic): the **exact never-decay
pin** `D(ν_t ‖ π) = log 2` at every `t` (both alternating laws), the
Pinsker instance `1/2 ≤ log 2`, and the **non-reversibility fence**
`¬(χ² ≤ D)` (`χ² = 1 > log 2` at every time — the bridge is one-way).
The **q-zero refutation fence** for the un-guarded Pinsker statement.
Continuous-time: the `t = 0` join pin `D_cont(0) = log 2` on `K₂`
(the discrete twin's exact value, matching `contChiSquareDistance`'s
own `t = 0` join idiom) and the decay instance through the earlier
fixture's pinned χ² values.

## Verification plan

Spike `wip/entropymix_spike.lean` first (all shelf declarations + the
full QA section + a `#print axioms` audit block, iterated to zero
errors/warnings before any shelf edit). Then: `lake env lean` on all
touched modules, explicit `lake build` targets, `#print axioms` on
every new declaration (expect exactly `propext, Classical.choice,
Quot.sound` — pure hard crust), full `lake build` followed
immediately by `check_build_completeness.py`, `lint_axioms`,
`check_refutation_independence` (no tags added — nothing here touches
an axiom), `check_public_reachability`, `check_citations`,
`check_markdown_links`, scoreboard regeneration, and
`check_scaffold_map_freshness` after the records sync.

## Deferred / follow-ons

- The reverse TV → χ² calculus: still no consumer named (unchanged).
- A log-Sobolev inequality (`Ent_π(f²) ≤ C·E(f)`) or modified LSI:
  now has a named on-shelf consumer (the decay theorem it would
  improve); adoption is an operator decision per the center-out
  policy's axiom-admission bar.
- An entropy mixing-time object: gated on a consumer, per the TV
  proposal's own precedent.

## Delivery record

**Delivered as stated, with two statement corrections the spike's
elaborator forced** (both caught in `wip/entropymix_spike.lean` before
any shelf edit — the falsifiability discipline working):

1. **The termwise `D ≤ χ²` shape is genuinely sum-level.** The
   originally-drafted termwise lemma `klTerm a b ≤ (a−b)²/b` is false
   as stated (the `log u ≤ u − 1` route yields `a²/b − a`, which
   differs from `(a−b)²/b` by `(a − b)`, the wrong sign at `a > b`);
   the termwise lemma landed as `klTerm_le_sub_one_mul`
   (`klTerm a b ≤ a·(a/b − 1)`) and the bridge
   `klDiv_le_sum_sq_div` carries the two mass hypotheses that
   identify `∑ p²/q − 1` with `∑ (p−q)²/q`. The mass hypotheses are
   load-bearing, not hygiene.
2. **The block multiplier of the rescaling identity is `a`, not
   `a/b`.** The two-block log-sum's per-term split is
   `klTerm (a·u) (b·v) = a·u·log(a/b) + a·klTerm u v`; an `(a/b)`
   multiplier (a transcription slip in the first draft) is refuted by
   `ring` at the elaborator — the identity checks only at `a`.

**Verification** (the run's own, before recording): spike iterated to
zero errors/zero warnings before any shelf edit; `lake env lean` zero
errors on all five touched modules (`Entropy.lean`, `Mixing.lean`,
`Oversmoothing.lean`, `Entropy_QA.lean`, `Mixing_QA.lean`, the QA
module carrying only its 3 recorded pre-existing benign `ring_nf`
notes); explicit `lake build` targets ✔; `#print axioms` via
`wip/entropymix_axcheck.lean` on all 34 nameable new declarations
(12 shelf + 22 QA): every one exactly `propext, Classical.choice,
Quot.sound` — zero contact with any admitted axiom; full `lake build`
✔ immediately followed by `check_build_completeness.py` — 133 source
files, 133 fresh artifacts, 0 stale, 0 missing, exit 0;
`lint_axioms` exit 0 (5, both PF findings allowlisted-confirmed);
`check_refutation_independence` (10-tag clean — no tags added,
nothing here touches an axiom); `check_public_reachability` clean (63
repo modules); `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (3566/5/0) with the verification row added.

**Technique findings** (for the next run's spike): the pinned
Mathlib's `∑ i in s, f i - g i` parses as `(∑ i in s, f i) - g i`
(the subtraction breaks the sum body — parenthesize; this produced a
cascade of baffling `unknown identifier 'i'` errors far from the
cause); `hasDerivAt_const` takes the point first
(`hasDerivAt_const t c`); `sq_le_sq'` takes the negated-side bound
first (`sq_le_sq' (-b ≤ a) (a ≤ b)`); `Finset.sum_sub_distrib` is
forward (`∑(f−g) = ∑f − ∑g`); `Finset.sum_le_sum_of_subset` requires
`CanonicallyOrderedAdd` in the pinned Mathlib (use the
split-complement identity plus `sum_nonneg` on ℝ instead);
`Real.log_inv` takes its argument; `field_simp` cannot close
identities that need `x⁻¹ · x = 1` without the nonzero fact in
context (provide it, or use `eq_div_iff` cross-multiplication with
`ring`); `rw` inside calc steps must respect the calc's stated
direction (the `show` states the chain's own equation, LHS first);
`open N in` attaches to the next *command* only — a section comment
consumes it (use a bare `open` before a final section, or per-file);
and the stale-olen import-boundary recurrence bit twice (rebuild the
imported module before re-elaborating its consumers).

**Log-Sobolev gate discharge:** the consumer the gate asked for is on
the shelf — the entropy-decay family above is an entropy inequality
composing `InformationTheory.Entropy`'s Gibbs bound (via
`sum_klTerm_ge_klTerm`), and a log-Sobolev inequality would now
improve it at its own rate. Adopting LSI remains an operator decision
per the admission bar; the radar's axis-3 note records the gate as
discharged.
