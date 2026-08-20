# Proposal: Discharge Davis–Kahan / Weyl / Cheeger Hard Direction

**Status:** In progress — the Weyl target is **delivered** (Step 0
surveyed positive and Step 1 executed 2026-08-20; see the delivery
record below). Davis–Kahan and the Cheeger hard direction remain
unsurveyed — their Step 0s are the open next steps, and Step 1 on
either is unauthorized until its own survey lands. Priority **Medium**,
contingent on each target's Step 0 survey landing before its Step 1
begins — the same contingency pattern
`decidable-spectral-certificates.md` used. Assistant's assessment of
project direction, requested 2026-08-19, promoted from `sgt-gaps.md`
item 3. Authorizes no axiom admissions or external publication.

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

**Update (2026-08-19): the norm bridge Weyl needs is now proved — this
section originally flagged a lead, `resolvent-calculus-psd.md`'s own
Step 0 has since resolved it, both ways.** That proposal's Step 0 spiked
the exact C*-algebra thread named below and found it **structurally
inapplicable** to real matrices, elaboration-verified: `CStarAlgebra`
requires `NormedAlgebra ℂ A`, and real matrices are not a complex
algebra — not an instance-search gap a different search could close.
The two proposals were right to expect they'd need the same bridge; they
were wrong to expect the C*-algebra route would supply it.

**But that proposal's own contingency fired, and the fallback is exactly
what this proposal needs.** `resolvent-calculus-psd.md` delivered a
from-scratch finite-dimensional bridge instead, in the new module
`Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent`:
`l2OpNorm_eq_max_abs_evals` — `‖M‖ = max |evals hM 0| |evals hM last|`
for symmetric `M` — proved from the already-shelf eigenbasis machinery
(`toEuclideanCLM`, Parseval, `ContinuousLinearMap.opNorm_le_bound`), no
axioms. This is precisely `λ₁(E) ≤ ‖E‖` / `λₙ(E) ≥ −‖E‖` in one packaged
identity — the operator-norm-to-eigenvalue bridge Weyl's admitted axiom's
own docstring says it's built from. **Weyl's Step 0 is now mostly done as
a side effect of a sibling proposal, not something to re-spike from
scratch.** What remains is composing `l2OpNorm_eq_max_abs_evals` with
the *additive* Weyl bound from `evals_min_max` (a subspace-intersection
argument, likely nearly identical in shape to the already-delivered
Cauchy-interlacing proof) — genuinely closer to Step 1 than Step 0 now.

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

**Weyl — surveyed 2026-08-20, decisive positive.** The additive bound
was spiked exactly as this section directs, before any Step 1 edit, and
the proposal's caution was vindicated in both directions:

- The additive bound is **not** a free corollary of the norm bridge. It
  consumes *both* Courant–Fischer witness directions
  (`exists_submodule_forall_rayleigh_le` for the upper bound — the
  witness subspace for `A` is exhibited as a member of the competitor
  set defining `λᵢ(A+E)` through `evals_min_max`;
  `exists_ne_mem_rayleigh_ge_of_finrank_eq` for the lower — the
  competitor direction for `A` run inside the witness subspace for
  `A+E`), plus *both* Rayleigh domination bounds: the top half from the
  EML step's `quadForm_le_evals_last` and the bottom half from the new
  mirror `evals_first_mul_dotProduct_le_quadForm` (added to
  `GraphTheory.Spectral` with this delivery — it did not exist).
- Composition with `l2OpNorm_eq_max_abs_evals` is then exactly as
  predicted: `‖E‖ = max |λ₁(E)| |λₙ(E)|` turns the additive window into
  the spectral-norm statement in two `linarith` steps, with the bridge's
  `1 ≤ card V` hypothesis covered by vacuity (`Fin 0` has no index).
- **Cost estimate for the full statement (the recording this section
  requires):** ~120 lines of Lean — three private translation lemmas
  (Rayleigh↔multiplication form both directions; a local
  `quadForm_add'` copy, since the generic one lives in the outer
  `GraphTheory.Expander` module this perturbation module must not
  import), two public additive-bound theorems, and the composed
  retirement theorem. Verified end-to-end in a scratch spike before any
  module was edited; the spike then transferred to
  `Perturbation/Weyl.lean` essentially verbatim.

**Davis–Kahan — unsurveyed.** The plan below stands unchanged.

**Cheeger hard direction — unsurveyed.** The plan below stands
unchanged.

Per-axiom order as originally written:

1. **Weyl.** ~~The norm bridge is delivered — reuse
    `l2OpNorm_eq_max_abs_evals` from `Analysis.OperatorTheory.Resolvent`
    directly; do not re-spike the C*-algebra route (confirmed dead above).
    What remains: spike the *additive* Weyl bound from `evals_min_max`
    (do not assume the norm bridge makes the additive bound free too —
    check it on its own), then compose the two. Record a real cost
    estimate for the full statement once the additive spike is done.~~
    **Done — see above and the delivery record below.**
2. **Davis–Kahan.** Survey what the sin-Θ bound's standard proof actually
    needs (typically: the norm bridge above, plus a resolvent-based or
    variational argument relating the perturbed and unperturbed
    eigenspaces) against what's on the shelf. Record findings even if
    negative. Note added 2026-08-20: the shelf gained since the original
    writing — the resolvent identity, the norm/Lipschitz resolvent
    bounds, and the resolvent-map injectivity are all proved in
    `Analysis.OperatorTheory.Resolvent`, and Weyl itself is now proved —
    but no survey of what a sin-Θ proof needs has been run, so "large"
    stands.
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

**Weyl Step 1 — DELIVERED 2026-08-20.** `weyl_inequality` retired from
admitted axiom to proved theorem in `Perturbation/Weyl.lean` at the
unchanged name, hypotheses, and conclusion (explicit axioms 13 → 12),
exactly along the surveyed route:

- the two public additive bounds `weyl_additive_upper` /
  `weyl_additive_lower` (`λᵢ(A) + λ₁(E) ≤ λᵢ(A+E) ≤ λᵢ(A) + λₙ(E)`,
  symmetry-only, every sorted index) — reusable hard-crust interfaces in
  their own right;
- the composed retirement `theorem weyl_inequality` (additive window →
  norm bridge), `#print axioms` reading only `propext,
  Classical.choice, Quot.sound`;
- `spectral_gap_stability` is unchanged code and now fully hard crust;
- the derived consumers shed the axiom dependency without recompilation
  changes: `davisKahanTwoPoint` is conditional on
  `davis_kahan_sin_theta` alone, `eventStreamProjectorDrift` on two
  axioms instead of three (both verified by `#print axioms`);
- QA per this proposal's plan: the existing `Weyl_QA` fixtures kept
  (zero-perturbation instances), plus the required non-vacuity witness
  and more — the nonzero fixture `A = E = !![2,1;1,2]` with both spectra
  pinned independently (trace/determinant/sortedness) and `‖E‖ = 3`
  through the proved bridge: the bound **attained exactly** at the top
  index (`|6−3| = 3 = ‖E‖`), **strict** at the bottom (`1 < 3`), both
  additive bounds instantiated at both indices, and the
  **window-endpoint guard** — the upper additive bound with `λ₁(E)` in
  place of `λₙ(E)` refuted (`6 ≤ 4` is false), so the window's
  endpoints are load-bearing and not interchangeable.

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

The Davis–Kahan Step 0 survey (what a sin-Θ proof needs vs. the now
richer shelf — the proved resolvent identity/norm/Lipschitz/injectivity
family and the proved Weyl); the Cheeger hard-direction survey after
that, still under its known-hard working assumption. Weyl is delivered
and closed (2026-08-20).
