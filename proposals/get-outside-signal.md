# Proposal: Get Outside Signal

**Status:** Proposed. Assistant's assessment of project direction, requested
2026-08-17 (conversation) / drafted 2026-08-18. Authorizes no Lean changes,
repository creation, PR submission, Zulip/GitHub posts, or any other external
publication. Every action item below that touches the outside world is
gated on the approval steps in [Clean-Room SGT
Export](clean-room-sgt-export.md), not on this document.

Companion to [Grow the Crust Through Electrical
Structure](electrical-structure-crust.md) and [Prove One Named
Inequality](prove-cheeger-easy-direction.md). Both of those are bets on more
internal proof, scored on this repository's own radar. This one is a bet on
external signal: whether anyone outside this repository would accept what
has been proved here. That question is not answerable by another radar
pass, and `docs/traction-plan.md` — a real plan — has zero execution against
it.

**Clean-room note.** This document is not exportable as-is (radar scores,
run history). More importantly, its *subject* is the export itself: this
proposal cannot be carried out by acting on this repository's code directly.
See [Correction](#correction-this-repository-is-quarantined) below.

Assessed from `docs/traction-plan.md`, `proposals/clean-room-sgt-export.md`,
`proposals/prove-cheeger-easy-direction.md` ("Supporting moves"),
`proposals/prove-lambda2-variational.md`, `docs/7_SGT_RADAR.md`,
`index/sources/chung_spectral_graph.md` and `index/sources/README.md`, the
candidate declarations in
`Scaffold/Mathlib/GraphTheory/{RandomWalk,Normalized}.lean`, and
[Mathlib's contribution guide](https://leanprover-community.github.io/contribute/index.html)
(checked 2026-08-18) for its AI-contribution policy.

## Correction: this repository is quarantined

The verbal version of this recommendation ("just open a Mathlib PR for
`walkTransitionMatrix` row-stochasticity") undersold a real constraint.
`clean-room-sgt-export.md` treats this repository as quarantined — possible
patent-sensitive research context — and forbids external publication without
counsel approval. `traction-plan.md` is explicit that it "applies only to
the new clean-room repository. Do not reference this repository, its
history, persistence work, or prior application rationale in the new
project's public materials." A Mathlib PR is exactly the kind of external
publication both documents gate.

So the actual highest-leverage move is not "write a PR." It is: **the
clean-room export proposal already exists, was never executed, and is the
literal prerequisite for every measure of traction this project claims to
want.** This proposal is therefore a sequencing argument, not a new export
plan — it does not re-litigate `clean-room-sgt-export.md`, it argues for
running it.

## Correction: Mathlib has a specific, enforced AI-contribution bar

Found 2026-08-18, after the phases below were first drafted: this proposal
was written by an AI assistant, at the direction of a human operator, from
a repository whose most recent Lean work was itself agent-driven
(`docs/AGENT_ACTIVITY.md`). Phase 3 sends a PR into a community that has an
explicit, current policy on exactly that provenance, quoted here rather than
summarized because the exact wording is the constraint:

- **Disclosure is mandatory, not optional.** "If you use artificial
  intelligence (such as GitHub's copilot mode, ChatGPT, or agents like
  Claude, Gemini, or Lean-dedicated agents like Aristotle), you must explain
  this in the PR description and explain which tool(s) you used and how you
  used it."
- **The bar is human command of the material, not tool origin.** "Code
  written by an AI without the supervision of a Lean subject expert fails to
  meet [Mathlib's] standards by a large margin." Mathlib's standards on
  generality, integration with the library, and maintainability are
  explicitly the bar; "getting code to mathlib's standards requires
  understanding and writing Lean code by hand."
- **Low-effort AI PRs are closed on sight**, especially ones opened without
  prior Zulip discussion of their merits: "Members of the review team will
  summarily close without comment any low quality PR produced using LLMs,
  especially if the author has made little effort to directly engage in the
  community in a discussion about its merits before opening the PR."
- **LLM-written prose is separately banned in review conversation**: "using
  an LLM when writing comments on GitHub or Zulip is not allowed; use your
  own words."
- **Repeated low-effort submissions escalate to a ban**: authors who open
  several such PRs "without putting in this learning effort" risk
  suspension or a permanent ban from both PRs and Zulip.

This does not block Phase 3 — it changes what Phase 3 requires. It reframes
"open the PR" from a submission task into a competence requirement: the
human running Phase 3 must be able to defend
`walkTransitionMatrix_row_sum` or the `√D` congruence proof, line by line,
in their own words, to a Mathlib reviewer, and must say plainly in the PR
description that Claude assisted in drafting it. An AI-drafted PR dropped
into the queue without that — however correct the Lean is — is the specific
failure mode this policy exists to close on sight.

**This is not new risk so much as confirmation of existing sequencing.**
`traction-plan.md`'s own launch sequence already puts "ask focused
questions" and community engagement (step 3) before "propose ... APIs
upstream" (step 4) — it was already asking for exactly the Zulip-first
engagement this policy requires. The finding sharpens Phase 3 below rather
than adding a new phase.

## Why this, why now

`docs/traction-plan.md`'s own "Measures of traction" — outside imports,
external issues and pull requests, downstream packages, upstream adoption —
are each at zero, and cannot become nonzero while the only existing code
lives in a quarantined repository. Meanwhile two proof-shaped proposals
compete for the next run, and both would, if landed, produce another
internal number (17 axioms instead of 18; axis 6 at 3.0 instead of 1.0) that
no outside party has ever been positioned to see or use. The project has
255 QA'd declarations and 18 cited axioms and has never had a single outside
reviewer.

This is not an argument against the other two proposals — it is an argument
that none of the three compete for the same run, because this one's first
phase is not a Lean proof at all.

## Recommendation

Treat `clean-room-sgt-export.md`'s approval gate as the next concrete
milestone, sized to the minimum scope `traction-plan.md` needs, then run
its own launch sequence (steps 1–4) with two named candidate upstream PRs
already scoped and ready.

### Phase 0 — outside this document's authority

Patent counsel sign-off on the export's initial file list and terminology
scan, per `clean-room-sgt-export.md`'s approval gate. No later phase can
start without this. This document does not request it; it names it as the
blocking dependency so it is not silently skipped by momentum toward the
more tractable-looking Lean proposals.

### Phase 1 — the minimal export

Not the full SGT center — `clean-room-sgt-export.md` already recommends
"favor a small foundation over breadth." The smallest export that makes
`traction-plan.md`'s release-readiness checklist satisfiable:

- Graph and Laplacian definitions (`WAdj`, `laplacian`, `laplacian_quadForm`,
  `laplacian_psd`) — the proved core, no axioms, already the repository's
  strongest asset per `electrical-structure-crust.md`.
- Whichever of the two Phase 2 candidate declarations below is chosen first,
  since `traction-plan.md` wants "one short, useful proof example" and a
  proof already scoped as independently useful is a better example than one
  picked for narrative reasons.
- Deliberately exclude Cheeger, Weyl, Davis–Kahan, concentration, and
  anything admitted — an outside reader's first impression should be
  proved-not-assumed material, per `traction-plan.md`'s communication rule
  against marketing axiom-backed results as formalized.
- The `papers/` index below (see "The paper as the hook") — not Lean code,
  but the artifact that makes the rest of this export legible to the
  audience `traction-plan.md` names.

**Phase 1's acceptance bar, concretely.** Added 2026-08-18, from
conversation: "what would it take to be listed alongside PhysLean, SciLean,
CvxLean, CSLib" turns out to be answerable against machinery already named
above, not a new plan. Those four are indexed on
[Reservoir](https://reservoir.lean-lang.org), Lean's package registry,
whose [inclusion criteria](https://reservoir.lean-lang.org/inclusion-criteria)
are four mechanical checks:

| Criterion | Status |
|---|---|
| Public GitHub repository (no forks/private/template repos) | Blocked on Phase 0 — the export must be the public artifact, never this repository, per `clean-room-sgt-export.md` |
| `lake-manifest.json` at repository root | Already present at this repository's root; carries forward automatically once the export is a real Lake package |
| GitHub-recognized OSI-approved license | Already satisfied — Apache 2.0 (`LICENSE`) |
| ≥2 GitHub stars | Trivial once public; not a real blocker |

Two of four are already true and travel with the export for free. The
other two are both downstream of Phase 0/1 — there is no separate
Reservoir-specific work item.

**Registry inclusion is the floor, not the peer bar.** PhysLean, SciLean,
CvxLean, and CSLib are documented, actively maintained libraries with
generated API documentation, not just Reservoir listings. `traction-plan.md`'s
release-readiness checklist — written before this comparison was made —
already specifies exactly that bar: one-sentence purpose, a Lake install
snippet pinned to a release tag, three narrow imports, one short useful
proof example, generated API documentation, and an explicit proved-vs-
assumed table. Add to Phase 1's scope explicitly: **generated API docs**
(`doc-gen4`, the standard tool all four peer libraries use) is not yet
named anywhere in this proposal and should be, since a library without a
docs site is not evaluated as a peer of one that has one.

**What is genuinely different about Scaffold.** None of the four peer
libraries carry a patent-sensitivity quarantine gate — their path from
"exists" to "public and listed" is pure engineering effort. Scaffold's
path runs through Phase 0's counsel sign-off first. That gate is
Scaffold-specific overhead, not a generic requirement of the Lean
ecosystem, and should not be normalized away by comparison to peers who
don't carry it.

### Phase 2 — the named upstream candidates

Both already surveyed against the pinned Mathlib and found absent, so
neither risks a wasted PR on duplicated work:

1. **`walkTransitionMatrix_row_sum`**
   (`Scaffold/Mathlib/GraphTheory/Normalized.lean:208-212`) — row-
   stochasticity of the irregular walk transition matrix `D⁻¹A`. A search of
   the pinned Mathlib found no `SimpleGraph`-native random-walk or Markov-
   chain material at all (`Mathlib/Probability` has none), so this is not a
   restatement of an existing lemma under a different name.
2. **`degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt`**
   (`Scaffold/Mathlib/GraphTheory/Normalized.lean:155-167`) — the diagonal
   `√D` congruence bridging the normalized and combinatorial Laplacians.
   Smaller and more self-contained than (1); a plausible first choice if a
   minimal first PR is preferred over the most useful one.

Both currently depend on Scaffold's `WAdj` wrapper type. Neither is
PR-ready as written — a Mathlib PR would need to restate the hypothesis in
terms of a plain symmetric nonnegative `Matrix V V ℝ` (or fold into
Mathlib's own `SimpleGraph.adjMatrix` idiom, using the `toWAdj` agreement
proved in `SimpleGraphAdapter.lean` to translate), not import `WAdj`
itself. This restatement cost is real and is exactly the kind of thing
Mathlib review would surface faster than another internal pass — which is
the point of doing this.

## The paper as the hook: a `papers/` index

Added 2026-08-18, from conversation. Phase 1's export as scoped above is
two isolated lemmas plus a proved core — correct, but not a hook. A
domain expert does not evaluate a Lean library by radar axis; they
evaluate it by the paper they already trust. "Did you get Chung's Cheeger
chapter right" is answerable and inviting in a way "here is our
proved-depth score" is not. That is the actual currency Scaffold has been
missing an artifact for.

**Not starting from zero.** `index/sources/*.md` already does something
adjacent for eight sources (Chung 1997, Davis–Kahan 1970, Horn & Johnson,
Weyl 1912/Bhatia, Tropp, Vershynin, Wainwright, Higham) — a bibliographic
entry plus a theorem-number-to-Lean-declaration table. But its own README
scopes it narrowly: "mappings from primary sources to Lean **axioms**,"
updated only "when adding a new axiom." It never lists a proved theorem,
so a paper whose results have since been proved rather than admitted
would not visibly read as more done. It was built for the assurance
radar's citation-fidelity axis, not for an outside reader.

**The extension, not a parallel structure.** Promote the existing
`index/sources/` files rather than fork a second system: add a proved-
declarations column beside the axiom column, and a one-line coverage
summary per paper ("N of M named results proved, P admitted, rest not
attempted"). A `papers/` directory (or `index/papers/`, to keep the
existing `index/` root) becomes the export-facing view of exactly that
same table — the same underlying fact, presented for someone who read the
paper, not someone who reads this repository's radar.

**First concrete target: Chung 1997.** `index/sources/chung_spectral_graph.md`
already tracks exactly three results — `cheeger_lower_bound`,
`cheeger_upper_bound`, `lambda2_variational` — all currently admitted. It
is also the paper `proposals/prove-lambda2-variational.md` targets
directly: if that proposal lands, this page's own table would show one of
three moving from admitted to proved, in public, against a paper a
spectral graph theorist already owns a copy of. That is a stronger Phase 1
"short, useful proof example" than either Phase 2 candidate alone, because
it comes with a trusted reference frame attached.

**Discipline flag — do not let the index become a work-generator.** As an
index, this is free: it restates facts already true, so it doesn't compete
with [load-bearing growth](../docs/1_STRATEGY.md#load-bearing-growth-the-path-to-falsifiability)
for run priority. But "let's fully cover Chung 1997" as a *goal driving
new proof or axiom admission* is a different decision — a landmark paper
is not automatically a named SGT consumer any more than a Mathlib gap was.
If that's wanted later, it needs its own leverage case under
`docs/1_STRATEGY.md`'s center-out policy, not a free pass for being in a
`papers/` folder.

### Phase 3 — traction-plan launch sequence, steps 1–4

Once Phase 1 and 2 exist in the public repository: tag a release, post to
Lean Zulip per `traction-plan.md`'s launch sequence, and open the PR for
whichever of the two candidates was exported. Steps 3 and 5 (ask the
community which adapter is most needed; publish a note after adoption) are
explicitly *not* scheduled here — they depend on a response this proposal
cannot predict.

**Gate on the AI-contribution bar above, not just on Phase 0–2 completing:**

- The Zulip post (`traction-plan.md` step 2) must precede the PR and must
  be written by the human operator in their own words — not posted as
  drafted by an assistant, per the "own words" rule on GitHub/Zulip
  comments.
- The PR description must disclose Claude's role in drafting the proof,
  naming the tool, per the disclosure rule.
- Whoever opens the PR must be able to walk a reviewer through
  `walkTransitionMatrix_row_sum` or the `√D` congruence proof unaided —
  the "supervision of a Lean subject expert" bar — before it is opened, not
  worked out reactively in review.
- If no one on the team can currently do that unaided, that is itself
  information Phase 0–2 should surface, not something to discover after a
  PR is summarily closed.

## What this is not

- Not a request to publish anything now. Every phase past Phase 0 is
  future-conditional on counsel sign-off that has not been sought.
- Not a claim that the Mathlib PR will be accepted. The honest bet is on
  the *information* review produces, not a guaranteed merge.
- Not a claim that AI assistance disqualifies this work from Mathlib. It
  does not — disclosed, human-supervised AI-assisted contributions are
  explicitly permitted. It is a claim that undisclosed or unsupervised
  submission is the specific failure mode Mathlib's review team closes on
  sight, so Phase 3 cannot be run the way earlier runs in this repository
  were: agent-driven with a human approving after the fact.
- Not a replacement for the other two proposals. If counsel sign-off stalls,
  `electrical-structure-crust.md` steps 3–6 or
  `prove-cheeger-easy-direction.md` remain the live internal options and
  neither depends on this one.

## Open next step

Raise Phase 0 as a decision with whoever owns the counsel relationship for
this repository. Nothing else in this document should be acted on before
that answer exists.
