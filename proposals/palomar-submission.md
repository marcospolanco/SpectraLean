# Proposal: Submit to the Palomar Registry

**Status:** Proposed; priority **Low — human decision required**. Assistant's
assessment of project direction, requested 2026-08-19. Authorizes no GitHub
authentication, external submission, or publication of any kind — every
action past Step 2 below needs the operator's own explicit go-ahead, and the
final submission step needs the operator's own GitHub credentials, which
this assistant does not have and should not be given.

Companion to [Traction Plan](../docs/traction-plan.md) (the audience and
distribution strategy this feeds — see "Relationship to the traction plan"
below, which is not a routine fit), [Get Outside Signal](get-outside-signal.md)
and [Clean-Room SGT Export](clean-room-sgt-export.md) (the sibling outreach
proposals, and why this one is not gated the same way — see "Clean-room
boundary"), and `governance/CONTRIBUTING.md`'s citation discipline, directly
reusable for `formalization.yaml`.

## What Palomar is, briefly

A registry of Lean-verified mathematics (announced 2026-08-18, incubated by
the Lean FRO and ICARM, Terence Tao on the scientific board with eight other
mathematicians). Functions as a preprint-server analogue for individual
machine-checked results, not a code repository or a journal. Registration is
one `Challenge.lean` (a short, human-readable statement, restricted to
Mathlib-level imports, may contain `sorry`) plus one `Solution.lean` (an
arbitrarily long proof, may import other pinned Git repositories, forbidden
from containing `sorry`/`sorryAx`/custom axioms unless those axioms are
individually declared in `comparator.json` and approved) plus a
`formalization.yaml` disclosing authorship, sources, and AI/human review
roles. Review is two independent kernels checking the Solution proves
exactly the Challenge's statement, plus an LLM checking the informal
description matches and clears a minimal research-interest bar — explicitly
not human peer review.

## Relationship to the traction plan — read this before treating it as routine

`docs/traction-plan.md` states plainly: **"This plan applies only to the new
clean-room repository. Do not reference this repository [Scaffold], its
history, persistence work, or prior application rationale in the new
project's public materials."** Palomar submission does not obviously live
inside that scope, for a structural reason: a Palomar Solution can pin *any*
public Git repository as a dependency, and Scaffold already is one
(`origin` is `https://github.com/marcospolanco/scaffold.git`, confirmed
2026-08-19). Submitting a theorem straight from Scaffold's current commit
history is possible today, entirely independent of whether or when the
clean-room export ever happens — this is not a distribution mechanism *for*
the traction plan's existing scope so much as a **second, faster, lower-friction
track that the traction plan should probably be extended to cover**, not
folded into silently. Two live options, not resolved by this document:

1. **Submit from Scaffold directly, now.** Fastest path to real outside
   signal; does not wait on the clean-room export or its patent-counsel gate.
2. **Wait and submit from the clean-room repository once it exists**, keeping
   Palomar submission inside `docs/traction-plan.md`'s existing "Launch
   sequence" (a natural step 2a, alongside or instead of the Zulip post) and
   its existing communication rules.

This document is written to support option 1 primarily, since it is
actionable today, but does not foreclose option 2 — an operator choosing
option 2 should treat this proposal as dormant until the export lands, not
delete it.

## Clean-room boundary — narrower gate than the export proposals, not zero gate

`clean-room-sgt-export.md` is gated on full patent counsel sign-off because
it exports a whole methodology and rationale into a new repository's public
materials. This is a different, smaller act: submitting one already-proved
theorem from a repository that is already public. The relevant risk is not
"does the new repo's marketing leak IP" — it already doesn't, Scaffold's
README and history are already visible — the relevant risk is narrower:
**does the specific submitted theorem's proof trace back to the deleted,
proprietary `spectral-proof/` material.**

**This is checkable, and for the recommended candidate it is checkable more
strongly than a name-diff.** `spectral-proof/` was permanently deleted at
commit `8e3a29f` (2026-08-18 15:55:05 -0700), after the provenance audit
recorded in `cdx-clean-assess.md` found near-zero overlap (4 of 215 exact
name matches, all generic textbook terms). `foster_theorem` was authored at
commit `91b7cb6` (2026-08-19 06:20:51 -0700) — **over fourteen hours after
`spectral-proof/` no longer existed anywhere in the working tree.** It is not
merely unlikely to be contaminated; the source material was not present to
contaminate it from. The same argument covers everything in
`GraphTheory.ElectricalFlow` and `GraphTheory.Expander` (all authored
2026-08-18 17:20:51 or later). It does **not** cover `evals_min_max`
(Courant–Fischer, committed `3f7ca8e`, 2026-08-18 15:12:10 — before the
deletion) — that theorem needs the name-diff argument instead, not the
temporal one, if it's ever the submission target.

**Still recommend a lightweight sign-off, not zero gate.** "I checked the
timestamps" is this assistant's own reasoning, not a legal determination.
Given this project's established caution on exactly this question, get an
explicit yes from whoever would otherwise be consulted on the export,
scoped narrowly ("does submitting `foster_theorem` to Palomar from
Scaffold's current public repo raise any concern") — a much smaller ask
than the export's full review, and one that shouldn't block on it.

## Recommendation: start with `foster_theorem`, one submission

Not `evals_min_max`, not a bundle, not "several at once." Reasons:

- **Doubly clean provenance** (temporal argument above), stronger than
  anything else currently in the repo except the electrical-flow and
  Expander material, and more recognizable as a *named* classical result
  than either of those to a reviewer (LLM or human) unfamiliar with this
  project.
- **Small, self-contained dependency chain**: the potential-equation
  definition of `effectiveResistance`, the eigenbasis machinery, and the
  kernel characterization — all in `GraphTheory.{Spectral,Electrical,Foster}`,
  nothing reaching into the concentration/perturbation bridge or any
  admitted axiom.
- **Zero axioms**, confirmed by `#print axioms` this session
  (`propext, Classical.choice, Quot.sound` only).
- **A real "first submission" test case**, per Tao's own announcement
  (he submitted his own Sendov's-conjecture formalization first, as a
  single-result test, not a bundle) — this mirrors the intended usage
  pattern exactly.

## The real design work: restating `effectiveResistance` in Mathlib-only terms

This is not a routine transcription and should not be treated as one. The
Challenge file can only import Lean core, Mathlib, or Tau Ceti — it cannot
reference Scaffold's own `WAdj`, `laplacian`, or `effectiveResistance`
directly. Two honest routes, decide before writing `Challenge.lean`:

1. **Inline the potential-equation definition** directly in the Challenge
   statement — state Foster's theorem as a claim about `∃ f, laplacian A *ᵥ f
   = ... ∧ ...`-shaped potential equations using bare `Matrix V V ℝ` and
   `Matrix.IsSymm`, reproducing Scaffold's own defining relation without
   naming it, so the Challenge is self-contained and Mathlib-only.
2. **State it via the energy/Dirichlet form instead of resistance
   explicitly** — Foster's theorem can be phrased as a claim purely about
   `quadForm`-style quadratic energy sums, sidestepping the need to name
   "resistance" as an object at all in the Challenge, at the cost of a less
   recognizable statement to a reader expecting the classical
   circuit-theory phrasing.

Route 1 is likely truer to the classical statement and worth the extra
Challenge-side work; record the decision before Step 2 below, per this
project's own "decide and record before writing the statement" convention.

## Build order

### Step 0: The narrow clean-room check (above) — mandatory, not skippable

Get the scoped sign-off described above before any Lean file is written for
submission, even in draft form.

### Step 1: Confirm the repository state Palomar needs

- A public commit SHA on `origin` (any commit; Palomar does not require a
  tagged release — `governance/RELEASES.md` currently has no real tag past
  a placeholder `0.1.0` entry, so this does not block).
- Confirm `lakefile.lean`/`lake-manifest.json`/`lean-toolchain` at that
  commit satisfy Palomar's build-file requirements (they should already,
  since this repository already builds cleanly — verify, don't assume).

### Step 2: Draft `Challenge.lean`

Restate `foster_theorem`'s public signature per the design decision above.
May contain `sorry` at this stage — that is explicitly permitted and is the
right way to iterate on getting the statement shape right before Step 3.

### Step 3: Draft `Solution.lean`

Import Scaffold pinned at the Step 1 commit; prove the Step 2 Challenge
statement via `foster_theorem`, with whatever thin bridging lemma the
restatement in Step 2 needs. Zero `sorry`, zero custom axioms — verify with
`#print axioms` before considering this step done, the same discipline
already standard in this repository's own delivery records.

### Step 4: Draft `comparator.json` and `formalization.yaml`

The metadata file is where this project's existing transparency actually
pays off — most of what Palomar wants disclosed
(authorship, AI/human review roles, sources, review status) is already
tracked in `docs/AGENT_ACTIVITY.md`'s delivery records; this step is mostly
transcription into Palomar's schema, not new documentation work. Source
citation for Foster's theorem itself needs verification before it appears
here — the classical circuit-theory citation (Foster, 1949, or the graph-
theoretic restatement more commonly cited) has not been checked this
session and should not be asserted from memory.

### Step 5: Local verification before any external action

Run the Comparator tool locally if available, or at minimum confirm
`Solution.lean` builds clean and `#print axioms` on the compared declaration
matches Step 3's requirement, before Step 6.

### Step 6: Submission — operator action only, not autonomous

Everything past this point requires the human operator directly: signing in
with GitHub (Palomar verifies push access, then discards the token — this
assistant has no GitHub credentials and should not be given any), submitting
via `submit.palomar-registry.org`, and — after automated review passes —
the explicit choose-to-register-or-withdraw decision Palomar's own process
reserves as a separate, deliberate step. An autonomous run should not reach
Step 6 under any circumstance; this is the same category as every other
"send/submit/publish" action this project already treats as requiring
explicit per-instance authorization, not standing permission.

## Deferred and removed

- **Bulk/whole-repository submission** — structurally impossible under
  Palomar's design (one Challenge/Solution pair per submission, size-capped
  well below any of Scaffold's real modules) and undesirable even if it
  were possible (it would bundle proved and axiom-backed work together,
  diluting the clean signal a single zero-axiom theorem gives). See the
  session discussion this proposal is drawn from for the full reasoning;
  not reproduced here.
- **`evals_min_max` (Courant–Fischer) as a submission target** — real and
  arguably more foundational than Foster's theorem, but committed before
  the `spectral-proof/` deletion, so it needs the weaker name-diff
  provenance argument rather than the clean temporal one. A fine second
  submission, not the first.
- **Any submission from the clean-room repository** — belongs to
  `docs/traction-plan.md`'s scope once that repository exists, not this
  document's.

## Acceptance criteria

- The clean-room sign-off (Step 0) is on record before any Lean file is
  drafted for submission.
- `Challenge.lean` is Mathlib-only, states Foster's theorem per the chosen
  design route, and is auditable against the classical statement by someone
  unfamiliar with Scaffold's internal names.
- `Solution.lean` proves exactly that statement with zero `sorry` and zero
  axioms beyond the three Palomar permits, verified by `#print axioms`.
- The Foster citation in `formalization.yaml` is verified against a real
  source before submission, not carried over from memory.
- Submission (Step 6) happens only on the operator's own explicit
  instruction and using the operator's own GitHub credentials.

## Open next step

Step 0 — the narrow clean-room sign-off. Nothing else should proceed before
it, including drafting `Challenge.lean` in earnest (a rough sketch to test
the Route 1 vs. Route 2 design question is fine; a submission-ready draft
is not).
