# Proposal: Audit the Four Zero-Consumer Scalar Concentration Axioms for the Subgaussian Junk-Integral Hazard

**Status:** DELIVERED 2026-08-28 (run `20260828T070330Z-run-1`) — Step 0
complete for all four axioms, with one materially false axiom found and
repaired. Per-axiom verdicts: `hoeffding_lemma` **materially false in
two ways beyond the two recorded junk mechanisms, repaired in place**
(probability-measure guard + `√6·a` constant; two refutation witnesses
proved in QA with genuinely-satisfied hypotheses);
`hoeffding_inequality`, `bernstein_inequality`,
`bernstein_bounded_variance` **audited and confirmed sound** against the
junk-integral hazard — their guard set (`IsProbabilityMeasure` + bounded
+ measurable) discharges integrability through two new proved safety
lemmas left on the shelf. Zero new axioms; the explicit axiom count
stays 10. Delivery record below.

Assessed from `Scaffold/Mathlib/Probability/Concentration/Scalar/Bernstein.lean`
(`bernstein_inequality`, `bernstein_bounded_variance`),
`Scaffold/Mathlib/Probability/Concentration/Scalar/Hoeffding.lean`
(`hoeffding_inequality`), `Scaffold/Mathlib/Probability/Concentration/
Scalar/Subgaussian.lean` (`hoeffding_lemma`), and the delivered
`proposals/prove-subgaussian-tail-bound.md`'s "Adjacent hazard recorded"
section, which named this exact hazard on 2026-08-22 and explicitly left
it unaddressed.

## Why these four, now

`docs/5_QA_SCOREBOARD.md` counts 10 explicit axioms. Six of the ten now
have at least one real theorem consumer somewhere in `Scaffold/Mathlib`
or `Scaffold/Derived`: `perron_frobenius`, `primitive_power_tendsto`,
`matrix_bernstein`, `matrix_azuma_hoeffding`, `hoeffding_empirical`, and
(via `davis_kahan_sin_theta`, a proved theorem rather than an axiom)
the Fiedler-line delivery. `matrix_hoeffding` is the one remaining
zero-consumer axiom with an active proposal
(`matrix-hoeffding-spectral-gap-estimation.md`, indexed Medium).

That leaves four zero-consumer axioms with **no proposal at all**:
`bernstein_inequality`, `bernstein_bounded_variance`, `hoeffding_lemma`,
`hoeffding_inequality`. These are not merely unused — the delivered
subgaussian retirement found that a sibling axiom in this exact file
family (`subgaussian_tail_bound`, in the same module as `hoeffding_lemma`)
was **materially false** via two independent junk-value mechanisms
(`Real.sInf_empty` vacuity on unconstrained-mass measures;
`MeasureTheory.integral_undef` making non-integrable variables satisfy
mean/moment hypotheses vacuously), and closed with an explicit, never-
followed-up warning:

> "The junk-integral mechanism is not specific to this axiom.
> `hoeffding_inequality` and `bernstein_inequality` state their
> centering/mean hypotheses as Bochner integrals over an *unconstrained*
> `μ`; on an infinite measure, a non-integrable `X i` satisfies
> `∫ X i ∂μ = 0` by the same `integral_undef` junk... Any future
> retirement attempt of either must run its own Step 0 against this
> hazard."

Building any future consumer proposal on top of these four without
first checking whether they carry the same defect would repeat exactly
the mistake the 2026-08-22 retirement caught — a theorem consumer
inheriting a false axiom silently, discovered only when someone tries
to instantiate it at a degenerate fixture (as QA there did).

## The finding (structural comparison, not yet Lean-checked)

A close read of the four axioms' exact hypothesis lists shows they are
**not uniform** with respect to the two known junk mechanisms — this is
the actual content of this proposal, and it changes the audit's shape
per axiom.

**Three axioms carry both guards the old `subgaussian_tail_bound` was
missing:**

- `bernstein_inequality`, `bernstein_bounded_variance`
  (`Bernstein.lean`), and `hoeffding_inequality` / `hoeffding_empirical`
  (`Hoeffding.lean`) are all stated under the section variable
  `{μ : Measure Ω} [IsProbabilityMeasure μ]` — finite total mass,
  which rules out the mass-scaling variant of mechanism 1 (the old
  axiom's `μ` carried no such constraint, which is exactly how
  `(3:ℝ≥0∞) • δ₀` broke it).
- All four also carry `h_meas : ∀ i, Measurable (X i)` and
  `h_bound : ∀ i ω, |X i ω| ≤ a` (or the `[0,1]`-bounded form for
  `hoeffding_empirical`). Bounded + measurable + finite measure is a
  standard sufficient condition for `Integrable` in Mathlib, which (if
  it discharges cleanly here) rules out mechanism 2 — the mean/variance
  integrals in `h_mean`/`h_var` cannot be silently non-integrable junk
  zeros the way `subgaussianNorm`'s MGF integral was for a heavy-tailed
  variable.

  If this integrability argument goes through as expected, these three
  axioms are **not** exposed to either mechanism the old axiom fell to,
  and the correct outcome of their audit is a recorded proof of safety
  — not a restatement, and not a proof-from-Mathlib attempt (see
  Non-goals).

**One axiom carries neither guard:** `hoeffding_lemma`
(`Subgaussian.lean`) is declared under the module's bare section
variable `{μ : Measure Ω}` — **no** `IsProbabilityMeasure` constraint,
exactly mechanism 1's setup — and its hypothesis list
(`ha`, `h_bound : ∀ ω, |X ω| ≤ a`, `h_mean : ∫ ω, X ω ∂μ = 0`) has
**no measurability hypothesis on `X` at all**. This is the same file,
the same `subgaussianNorm`-mediated machinery, and the same missing
constraints as the axiom already found false there. It is precisely
the axiom the retirement proposal's own Non-goals section named as
"a different axiom in the same file with a similar `subgaussianNorm`-
mediated shape" and explicitly declined to touch.

**Important honesty note, not yet resolved:** hand-tracing suggests
`hoeffding_lemma` may *not* actually be falsifiable by either known
mechanism, for a reason specific to its shape: the junk mechanisms make
`subgaussianNorm X μ` collapse to `0` (the `sInf` junk value) exactly
when they'd also make `h_mean` vacuous, and `0 ≤ a` holds trivially
given `ha : 0 ≤ a` — unlike `subgaussian_tail_bound`, where the
hypothesis-side norm and the conclusion-side probability bound were
different objects that could decouple, here the conclusion **is** the
`subgaussianNorm` bound, so the same junk collapse that guts the
hypothesis also guts the conclusion in the same direction, consistently.
This is exactly the kind of reasoning that must not be trusted without
a Lean spike — it is offered here as the audit's starting hypothesis,
not its answer.

## Scope

1. **Step 0 (mandatory, not done by this document), one spike per
   axiom, in this order:**
   - `hoeffding_lemma` first (highest suspicion, same-file precedent).
     Attempt to construct a genuine counterexample using an
     unconstrained-mass measure and/or a non-ae-strongly-measurable
     bounded `X`, following the exact refutation-family template the
     2026-08-22 retirement used (`3 • δ₀`-style fixture,
     `Real.sInf_empty`/`integral_undef` mechanism named explicitly). If
     no counterexample is found after a genuine attempt, record why the
     "honesty note" above holds (or doesn't) as a proved fact about the
     junk mechanism's interaction with `subgaussianNorm`'s own
     definition — not an assertion.
   - `bernstein_inequality`, `bernstein_bounded_variance`,
     `hoeffding_inequality` next: confirm (as a real Lean lemma, not a
     hand-argument) that `h_bound` + `h_meas` + `IsProbabilityMeasure μ`
     together discharge `Integrable (X i) μ` and
     `Integrable (fun ω => (X i ω - ∫ X i ∂μ)^2) μ` at the exact shelf
     lemma this pin provides (likely
     `MeasureTheory.Integrable.of_bound` or the `Memℒp`/boundedness
     route — confirm signature before writing anything public). If this
     closes as expected, the audit is complete for that axiom: safe,
     no restatement.
   - Zero new axioms in this scope regardless of outcome. This is a
     verification pass, not a formalization campaign.
2. **If a genuine falsifying instance is found for any axiom:**
   repair-and-retire at the same name and conclusion with honest
   hypotheses, per the Woodbury/subgaussian precedent
   (`docs/2_ARCHITECTURE.md` §9, `prove-subgaussian-tail-bound.md`'s
   delivery record as the template). This is the highest-value possible
   outcome and should not be short-circuited if it arises — but it is
   not the expected outcome for three of the four axioms per the
   structural finding above.
3. **If no falsifying instance is found:** record the closed audit in
   this proposal (the exact integrability lemma used, or the exact
   argument for why `hoeffding_lemma`'s missing guards turn out not to
   matter) and update `prove-subgaussian-tail-bound.md`'s "Adjacent
   hazard recorded" section to point here as resolved, rather than
   leaving it a dangling, unaddressed warning.
4. Update `docs/5_QA_SCOREBOARD.md` and the explicit axiom count only if
   an axiom actually changes; otherwise this proposal's only footprint
   is the audit record itself plus whatever small safety lemmas Step 0
   produces (these may be worth keeping on the shelf even though they
   prove no axiom, if a future consumer needs the same integrability
   fact — record but do not force a consumer).

## Acceptance criteria

- No `axiom`, `sorry`, or `admit` introduced by the audit itself.
- For each of the four axioms, the delivery record states one of:
  (a) a proved safety argument with the exact Mathlib lemma used, (b) a
  repair-and-retire delivery, or (c) an honest "not tractable at
  reasonable cost, here is exactly where it got stuck" verdict — never
  silence, and never a restatement without a demonstrated defect.
- If nothing is retired, the explicit axiom count is unchanged and
  `lint_axioms`/`check_citations`/`check_markdown_links`/a full
  `lake build` still pass (any new safety lemmas must build cleanly).
- `prove-subgaussian-tail-bound.md`'s "Adjacent hazard recorded" section
  is updated to cite this proposal's resolution rather than left as an
  open warning with no pointer.

## Non-goals

- This is **not** a retirement campaign by default. The structural
  finding above predicts three of the four axioms are already safe;
  the expected majority outcome is "audited, confirmed sound, left as
  an axiom" — do not manufacture a proof-from-Mathlib attempt at
  `bernstein_inequality`/`bernstein_bounded_variance`/
  `hoeffding_inequality` just because the integrability check passes.
  (The pairwise-vs-mutual-independence gap the subgaussian proposal
  also flagged for these two — `IndepFun.mgf_add` being two-at-a-time
  while the classical proof needs a multi-way MGF factorization — is a
  separate, harder blocker on any actual retirement attempt and is
  explicitly out of scope here; this proposal only audits integrability
  vacuity, not the independence-hypothesis gap.)
- The matrix trio (`matrix_hoeffding`, `matrix_bernstein`,
  `matrix_azuma_hoeffding`) is out of scope. `matrix_bernstein` already
  has a real consumer (`Derived/SparsificationTail.lean`);
  `matrix_hoeffding` has its own proposal; all three route their
  hypotheses through Scaffold's `MatrixMDS` structure, a different
  integral surface from the plain-Bochner one this proposal examines,
  and would need their own Step 0 against the same hazard class.
- Do not restate any axiom's name, hypotheses, or conclusion unless
  Step 0 produces an actual counterexample — a "looks safer this way"
  restatement without a demonstrated defect is exactly the kind of
  change this repository's Step 1 contract forbids
  (`discharge-perturbation-axioms.md`'s precedent).

## Delivery record (2026-08-28, run `20260828T070330Z-run-1`)

Step 0 ran as specified — one spike per axiom, in the prescribed order —
and produced the highest-value outcome scope item 2 anticipated, though
not through the mechanism the proposal predicted.

**`hoeffding_lemma`: materially false — two defects, both Lean-verified.**
The proposal's "honesty note" hand-trace (junk collapses the norm
downward; the conclusion is an upper bound) turned out to be *correct
for the junk mechanisms* — but it missed that the axiom is false for
classical reasons on perfectly well-behaved spaces:

1. **Constant defect** (`old_hoeffding_lemma_refuted_constant_QA`): at
   the fair-coin Rademacher fixture `rademacherX` on `rademacherMeasure`
   (`½·(δ_true + δ_false)`, a genuine probability measure), every
   hypothesis of the old axiom holds genuinely — `|±1| ≤ 1`, and
   `∫ X ∂μ = 0` as an *honest* integral of an integrable bounded
   variable — yet the defining set only contains `K` with
   `K² ≥ 1/log 2`, so `subgaussianNorm ≥ 6/5 > 1 = a`. The refutation
   needs no junk values at all: `Real.log_two_lt_d9` gives
   `log 2 < 0.6932 < 25/36 ≤ 1/K²` for `K ≤ 6/5`, hence
   `exp (1/K²) > 2`, so `K` is excluded.
2. **Guard defect** (`old_hoeffding_lemma_refuted_guard_QA`): at the
   mass-`19/10` rescaling `scaledRademacherMeasure` (finite, *not*
   probability; mean still genuinely zero by cancellation), the
   threshold `1/√(log (2/M))` exceeds `4` — every `K ≤ 21/5` is
   excluded via `log (20/19) ≤ 1/19 < 25/441 ≤ 1/K²` (rational
   arithmetic plus `Real.log_le_sub_one_of_pos`, no decimal bounds
   needed). Since the norm is `≥ 21/5` there, **no** constant `≤ 4`
   repairs the old statement: the missing probability-measure guard is
   load-bearing, not decorative.

**The repair** (same name, per the subgaussian-retirement template;
architecture §9 emergency-repair precedent): `hoeffding_lemma` now
carries `[IsProbabilityMeasure μ]` and concludes
`subgaussianNorm X μ ≤ √6 * a`. The `√6` is derived, not asserted from
a source: the cited λ-form (Vershynin Lemma 2.6.2,
`E exp(λX) ≤ exp(λ²a²/2)`) gives the two-sided tail
`P {|X| ≥ x} ≤ 2 exp(−x²/(2a²))`, and layer-cake integration of
`Y = exp(X²/K²)` yields `E Y ≤ 1 + 2/(K²/(2a²) − 1) = 2` exactly at
`K² = 6a²`. Junk safety of the repaired statement: both junk
mechanisms collapse the norm *downward* (empty set → `sInf = 0`; full
set via junk-zero integrals → `sInf = 0`) and the conclusion is an
upper bound, so non-integrable/non-measurable inputs cannot falsify it;
the full derivation is in the axiom's docstring. The repaired statement
is re-instantiated at the refuting fixture
(`hoeffding_lemma_rademacher_QA`: `≤ √6·1`, consistent with the proved
`6/5` lower bound since `6/5 < √6`), and the existing
`subgaussian_norm_zero_QA` consumer carries over unchanged at `a = 0`
(`√6·0 = 0`).

**The three guarded axioms: confirmed sound, with the safety lemmas left
on the shelf.** `integrable_of_bounded_measurable` (in `Hoeffding.lean`)
proves `Integrable X μ` from exactly `h_meas` + `h_bound` +
`IsProbabilityMeasure μ` — so `hoeffding_inequality`'s `h_mean` clause
is an honest constraint, never a junk-integral vacuity.
`integrable_sq_sub_mean` (in `Bernstein.lean`) proves the centered-square
integrability behind both Bernstein axioms' variance statistics the same
way (bound `(|a| + |∫X|)²`, `Integrable.mono'` at `integrable_const`,
which the probability hypothesis makes available). Both lemmas are
consumed by QA at the Rademacher fixture
(`integrable_rademacher_QA`, `integrable_sq_sub_mean_rademacher_QA`),
and `rademacherMeasure_mean_QA` itself routes integrability through the
first lemma — the audit's finding made durable and reusable. Per the
Non-goals, no retirement attempt was manufactured for these three.

**Technique findings** (for future Step-0s on this shelf): the pin's
`Measurable.pow` is the exponent-*function* version — for natural
powers use `Measurable.mul` + `pow_two` or `measurable_pow.comp`;
`le_csInf` in this pin requires `Set.Nonempty` *and* the ∀∈ bound (the
documented Fiedler-run note holds; each defining set needed an explicit
member — `K = 2` at the probability fixture via `exp (1/4) ≤ 2`, and
`K = 100` at the scaled fixture via `exp (1/10000) < 10000/9999`, the
latter from `add_one_lt_exp` at the negative point composed with
`exp (x)·exp(−x) = 1`); strictness discipline — `le_csInf` yields a
non-strict lower bound, so a refutation at threshold `c` must refute
`≤ c'` for some `c' < c` (the scaled refutation proves `≥ 21/5` and
refutes `≤ 4`, not `≤ 21/5`); the numeral-normalization trap — after
instantiating at `K = 2`/`K = 100`, integrals display `1 / 2 ^ 2` and
`1 / 100 ^ 2`, so numeric bridges (`show (2:ℝ)^2 = 4 from by norm_num`)
are needed before matching decimal-statement lemmas; the stale-olen
recurrence at the module/QA import boundary (rebuild module targets
before elaborating the consumer), twice this run after the two
stash-pop baseline comparisons.

**Verification:** spike first (`wip/asc_spike.lean`, zero errors/warnings
before any shelf edit); `lake env lean` zero errors on all three changed
modules with warnings exactly at the pre-existing baselines (1/2/2,
line-shifted) and zero errors on the QA file whose warning count
*improved* 9 → 8 (the repair gives `subgaussian_norm_zero_QA` a use for
the probability-measure instance); explicit `lake build` targets ✔ (the
three modules 1970/1970, the QA file); `#print axioms` via
`wip/asc_axcheck.lean` on all 21 audited declarations — the 17
refutation-family and both safety lemmas exactly
`propext, Classical.choice, Quot.sound`, the two axiom consumers
(`subgaussian_norm_zero_QA`, `hoeffding_lemma_rademacher_QA`) carrying
`hoeffding_lemma` and nothing else beyond the standard three — the
delivery's entire trust boundary. Axiom count stays 10 (one repaired in
place, none added or removed); `lint_axioms`, `check_citations`,
`check_markdown_links`, scoreboard regeneration, map-freshness check,
full `lake build` + `check_build_completeness` — see the terminal
activity entry for the recorded outcomes.
