# Proposal: Discharge Davis–Kahan / Weyl / Cheeger Hard Direction

**Status:** Proposed; priority **Medium**, contingent on Step 0's survey
landing before Step 1 begins — the same contingency pattern
`decidable-spectral-certificates.md` used. Assistant's assessment of
project direction, requested 2026-08-19, promoted from `sgt-gaps.md` item
3. Authorizes no Lean changes, axiom admissions, or external publication.

Companion to `docs/2_ARCHITECTURE.md` §9 (upstream-replacement lifecycle)
and this session's precedent of axiom retirements (Courant–Fischer,
Cauchy interlacing, Cheeger easy direction, Sherman–Morrison, Woodbury) —
this is the same category of work, shrinking the mushy center rather than
growing the hard crust into new territory.

## Clean-room boundary

Internal prioritization and analysis. If counsel approves a public
repository export, restate from the standard operator-perturbation-theory
literature (Davis & Kahan; Bhatia). Do not copy this proposal verbatim.

Assessed from `Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/
{Weyl,DavisKahan}.lean` and `Scaffold/Mathlib/GraphTheory/Cheeger.lean`
(all three axioms confirmed present, exact statements read directly,
2026-08-19), `Spectral.lean`'s `evals_min_max` (the general Courant–Fischer
engine, proved 2026-08-18), and a 2026-08-19 spot-check into
`.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/{Spectrum,
ContinuousFunctionalCalculus/Order}.lean`.

## External consumer

The single most load-bearing classical result among this repository's
admitted axioms: Davis–Kahan sin-Θ is the standard eigenvector
perturbation bound behind spectral clustering stability arguments and PCA
robustness theory generally; Weyl's inequality is used anywhere
eigenvalues need to be bounded under perturbation, in numerical linear
algebra broadly.

## The ask, precisely

Not "add an axiom" — **discharge one already admitted.** Three separate
targets, not one bundled effort:

1. `weyl_inequality` (`Weyl.lean:60`): for symmetric `A, E` and every
   sorted index `i`, `|evals (hA.add hE) i − evals hA i| ≤ ‖E‖` (ℓ²
   operator norm).
2. `davis_kahan_sin_theta` (`DavisKahan.lean:64`): the sin-Θ eigenvector
   perturbation bound.
3. `cheeger_lower_bound` (`Cheeger.lean:88`): the hard direction of
   Cheeger's inequality (regular graphs).

If any turns out to be out of reach, **the axiom stays, and stays
visible** — per the original assessment's own honesty, this is an
improvement attempt, not a correction owed. Do not weaken this into
admitting a restated or narrower version to claim partial credit.

## Why the three are not equally tractable — do not treat them as one problem

**Weyl's inequality is the one worth spiking first, on a real (if
unverified) lead.** The admitted statement is not the plain additive
Courant–Fischer corollary — it is stated in the ℓ² **operator norm**, and
its own docstring says it is built from the additive bound *plus*
`λ₁(E) ≤ ‖E‖` / `λₙ(E) ≥ −‖E‖`, i.e. it needs an operator-norm-to-
eigenvalue bridge that does not exist anywhere in Scaffold today (the
same bridge `resolvent-calculus-psd.md`'s Step 0 also needs — the two
proposals should share whatever that spike produces, not duplicate it).
A 2026-08-19 keyword search found
`IsSelfAdjoint.spectralRadius_eq_nnnorm` in
`Mathlib.Analysis.CStarAlgebra.Spectrum` — a general C*-algebra fact
that a self-adjoint element's norm equals its spectral radius, exactly
the needed shape. **This was found by grep, not verified by
elaboration** — real uncertainty remains about whether the instance
chain resolves for `Matrix V V ℝ` under `Matrix.L2OpNorm` (the file
Scaffold already imports for this axiom) and whether `spectrum ℝ A`
connects cleanly to Scaffold's own `evals`/`eigvalOf`. If it does, the
*additive* Weyl bound itself is a short, standard argument from
`evals_min_max` (a subspace-intersection argument nearly identical in
shape to the Cauchy-interlacing proof already delivered).

**Davis–Kahan is genuinely unclear.** Nothing surveyed so far suggests a
comparable shortcut; treat it as "large" as originally rated, with its
own from-scratch tractability question, not assumed to ride along with
Weyl's finding.

**The Cheeger hard direction is known-hard, not merely unexplored.** This
is textbook-established: unlike the easy direction (already proved this
session via a variational argument), the hard direction requires a
genuinely different constructive/combinatorial argument (a sweep-cut or
similar), not a Courant–Fischer corollary. Do not expect this proposal's
Weyl-side optimism to transfer here.

## Build order

### Step 0: Tractability survey (mandatory; the whole gate)

Per axiom, in this order:

1. **Weyl.** Spike the operator-norm bridge directly: write
   `(hA : A.IsSymm) → ‖A‖ = max (|evals hA ⟨0,_⟩|) (|evals hA ⟨n-1,_⟩|)`
   (or the equivalent spectral-radius shape) and attempt to close it via
   the C*-algebra thread above. Record whether it elaborates and what it
   actually needed. If it lands, spike the *additive* Weyl bound
   separately from `evals_min_max` (do not assume the norm bridge implies
   the additive bound is easy too — check both). Record a real cost
   estimate for the full statement only after both spikes are done.
2. **Davis–Kahan.** Survey what the sin-Θ bound's standard proof actually
   needs (typically: the norm bridge above, plus a resolvent-based or
   variational argument relating the perturbed and unperturbed
   eigenspaces) against what's on the shelf. Record findings even if
   negative.
3. **Cheeger hard direction.** Survey the standard sweep-cut argument's
   Lean cost specifically — this is the one where "known-hard" should be
   treated as the working assumption unless the survey finds otherwise,
   not spiked with the same optimism as Weyl.

Record all three findings in this document before any Step 1 begins on
any of the three axioms — they may be pursued independently once
surveyed (this is not a single bundled effort).

### Step 1 (per axiom, only after that axiom's Step 0 survey is positive)

Prove the axiom's exact existing statement — same name, same hypotheses,
same conclusion — via whichever route Step 0 found. Do not restate the
theorem more narrowly to make it easier; a narrower proved theorem is not
a valid discharge of the existing axiom (the `sherman_morrison`/
`woodbury_identity` retirements are the precedent for "same shape,
now proved").

## QA plan

Per discharged axiom: reuse the existing QA file's fixtures (`Weyl_QA.lean`
etc. — survey what already exists before adding new ones), plus at least
one negative witness confirming the bound is not vacuously true (e.g., a
nonzero perturbation where the bound is strict, not just satisfied at
equality trivially).

## Operating instructions for an autonomous run

- Step 0 is mandatory and per-axiom; do not begin Step 1 on any axiom
  before that axiom's own survey is recorded.
- **No new axioms, and no restated/narrower replacement axioms.** If a
  survey finds an axiom out of reach, record the precise obstruction in
  `docs/6_SGT_BACKLOG.md` and leave the existing axiom exactly as is —
  visible, cited, unchanged.
- Pursue the three axioms independently; a positive finding on Weyl does
  not authorize assuming Davis–Kahan or the Cheeger hard direction are
  similarly reachable.
- Survey Mathlib precisely (exact instance and lemma signatures, not just
  names) before writing any Scaffold statement — the C*-algebra thread
  above is a lead, not a confirmed asset.

## Open next step

Step 0's Weyl spike — unblocked now, the cheapest of the three surveys to
run given the concrete lead already found.
