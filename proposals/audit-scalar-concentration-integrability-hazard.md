# Proposal: Audit the Four Zero-Consumer Scalar Concentration Axioms for the Subgaussian Junk-Integral Hazard

**Status:** Proposed 2026-08-28.

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
