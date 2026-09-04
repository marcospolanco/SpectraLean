# Governance

This document exists for one reader: someone assessing whether Scaffold's
process can be trusted, who does not want to reconstruct that assessment
from a dozen scattered files. It is a map, not a new policy — every rule
below already lives somewhere in this repository, and every claim here
cites exactly where. Roughly half of what actually governs this project
lives outside this directory (`docs/`, `proposals/`, `scripts/`); this
document brings it together in one place rather than pretending
`governance/` is self-contained.

**If you read nothing else, read "The trust argument" and "Known gaps"
below** — the first is the claim this project is making about itself, the
second is where that claim is not yet fully backed by mechanism.

## The trust argument

Scaffold's position, stated plainly: **nothing here is claimed to be
error-free. What is claimed is that every assumption is explicit, cited,
and narrow; everything downstream of an assumption is machine-checked
against it by Lean's kernel; and when an assumption turns out to be
wrong, that gets found by the project's own deliberate practice, fixed in
the open, and recorded — not silently patched or left for an outside
reader to discover.**

Three concrete facts back this, each checkable in minutes, not asserted:

- **Zero `sorry`, `admit`, or hidden `native_decide` anywhere in the
  public API.** Every unproved assumption is a named `axiom` declaration
  with a citation — `scripts/lint_axioms.py` fails the build otherwise.
- **A small, currently-shrinking axiom surface.** As of this writing, 4
  admitted axioms (`matrix_azuma_hoeffding`, `matrix_bernstein`,
  `matrix_hoeffding`, `perron_frobenius`), each with a `Replacement
  path:` note stating what would retire it. The count was 5 as recently
  as 2026-09-02 (`primitive_power_tendsto` retired via
  `proposals/retire-primitive-power-convergence.md`) and 8 before that
  (`docs/9_ERRATA.md`'s repair history) — the trend is down, not up.
- **A public record of every time an admitted axiom or a shipped theorem
  was found mathematically wrong.** `docs/9_ERRATA.md` — nine entries as
  of this writing, every one found by this project's own adversarial
  practice (see below), not by an external user hitting a bug. Absence
  from that list means "not yet tested this way," not "verified correct
  forever" — the document says this about itself, explicitly, rather
  than letting a short errata list imply more than it can support.

Everything else in this document is the mechanism that makes those three
bullets true rather than aspirational.

## Map of mechanisms

Grouped by what question each one answers. File paths are exact; none of
this is paraphrased into a new vocabulary.

### 1. What is allowed to become a permanent trust boundary (an axiom)?

**`docs/2_ARCHITECTURE.md` §5 — Axiom admission policy.** An axiom is
admissible only if it unlocks a concrete downstream use case, its
conclusion is meaningful and composable, its documentation cites an
authoritative source precisely, and — the part with the most teeth — its
**degenerate corners have actually been checked, not assumed benign**.
Every real defect this project has found in an admitted axiom came from
an implicit boundary the source paper's prose never states, not from the
main inequality being wrong. The policy names five specific hazard
classes to check before admission (empty/degenerate cardinality,
unconstrained measure mass, junk-valued integrals defaulting to `0`, a
wrong classical constant, `≤`/`<` boundary mismatches), explicitly kept
as "a floor, not a ceiling" — updated every time a new mechanism is
found. Two scripts flank an axiom's lifecycle mechanically:
`scripts/lint_axioms.py`'s degenerate-corner guard check (flags axioms
missing a visible `Fintype`/`Measure` guard, with a reasoned allowlist
for accepted exceptions) and `scripts/check_refutation_independence.py`
(a refutation fixture cannot itself depend on the axiom it refutes).

### 2. What is an axiom worth in this codebase — and how does it stop being one?

**`docs/2_ARCHITECTURE.md` §9 — Upstream replacement lifecycle.** A
six-step process for retiring an axiom once a proved replacement exists
(compare assumptions/conclusions precisely, adapt, re-run downstream QA,
deprecate with a migration note, hold a compatibility window, remove).
**Emergency removal** — skipping the deprecation window — is the
explicit escape hatch for "a materially false statement, an inconsistent
assumption set, or a declaration that creates unacceptable trust
exposure," and every use of that escape hatch is required to produce an
entry in the Errata (below); an emergency removal with no Errata entry
"defeats the purpose of keeping the list."

### 3. What does a piece of QA actually have to prove to count?

**`docs/2_ARCHITECTURE.md` §6 — QA contract.** No `sorry`/`admit`;
exercises a real definition or public axiom; checks a mathematically
meaningful property; stays small enough to diagnose an interface
failure; does not claim a trivial consequence validates the theorem it
guards. A high QA count is not treated as self-evidently meaningful —
see Phase 3 below, which exists specifically to stress-test whether QA
passes for the right reason.

### 4. Is the QA actually load-bearing, or does it just look like it?

**`governance/ADVERSARIAL_REVIEW.md` — the standing audit methodology.**
Distinct from both the automated hygiene scripts and routine PR review;
this asks a different question outright: *are the proofs and QA actually
load-bearing, or do they only look like it?* Five documented failure
classes motivate it (mathematically false axioms, vacuous/tautological
theorems exploiting Lean's totalization defaults, "paper-tiger" QA that
only tests small symmetric coincidences, citation drift from the source
literature, and ghost dependencies in roadmap documents) — none
hypothetical: the pre-repair `woodbury_identity` and `cheeger_lower_bound`
axioms both compiled while being mathematically false, and a proposal
once cited a theorem (`matrix_chernoff_upper_lower`) that did not exist
anywhere in the repository, caught only by grepping for it directly
rather than trusting the citation.

Six phases, each with a runnable procedure:

| Phase | Question | Can run autonomously? |
| --- | --- | --- |
| 1. Axiom falsification | Does an extremal fixture refute this axiom at its stated hypotheses? | Yes |
| 2. Junk-value exploitation | Does the proof secretly rely on a totalization default (`x/0=0`) or a vacuous hypothesis? | Yes |
| 3. QA suite deconstruction | Does the QA test real failure modes, or only small-fixture coincidences? | Yes |
| 4. Literature fidelity | Does the Lean statement match the cited source's actual convention and constant? | **No — needs a human with the source text** |
| 5. Roadmap reality check | Does every "delivered" claim in a proposal correspond to code that actually exists? | Yes |
| 6. Public-exposure readiness | Does a public claim overstate what's proved; does a rewritten history invalidate an external pin? | **No — a judgment call about how outside readers parse language, not mechanically checkable** |

A five-tier severity ladder (P0 critical soundness bug through P4
"hypothesis stronger than necessary" and P5 "public-exposure risk," the
latter two added after a real pilot run surfaced findings the original
four tiers didn't fit) routes each finding to the right response —
P0 gets emergency removal per the upstream-replacement lifecycle above;
P4 is explicitly *not* urgent, tracked as ordinary API-cleanup debt.

### 5. Who actually verifies a change before it lands — and how do they avoid trusting the thing they're checking?

**`docs/arch/commit-steward-protocol.md`.** Scaffold's autonomous agent
(`scripts/opencode-pursue`) has **no git authority** — it cannot commit,
push, or declare its own work verified. Something outside it stages,
independently re-verifies, and commits. This document formalizes that
role's two responsibilities:

- **The mechanical verification gate** (runs on every batch of
  uncommitted work): read every delivery record in full, cross-check the
  record against the actual diff, run the full nine-check verification
  ladder independently (`lake build`, `check_build_completeness.py`,
  `lint_axioms.py`, `check_refutation_independence.py`,
  `check_public_reachability.py`, `check_scaffold_map_freshness.py`,
  `check_backlog_freshness.py`, `check_citations.py`,
  `check_markdown_links.py`), escalate to an independent `#print axioms`
  re-derivation for any change touching an axiom or a widely-consumed
  module, sweep for `sorry`/`admit`, run a stability check immediately
  before staging (nothing changed between "verified" and "committed"),
  then commit with a message that cites what was actually re-checked.
  **The rule underneath every step: never assert something is verified
  without having independently run the check that verifies it** — a
  record's own self-report is evidence, never the verification itself.
- **Strategic process review** (occasional, judgment-triggered): noticing
  a policy, a piece of tooling, or a documentation surface has itself
  drifted — not a Lean correctness issue, a process one — and deciding
  whether to fix it directly, write a proposal, or escalate to a human.

This protocol exists because of specific, named production failures, not
hypothetical ones: a full `lake build` once printed "Build completed
successfully" over a three-error QA file; a run once delivered two
complete, verified theorems but exited before writing its own
`docs/AGENT_ACTIVITY.md` entry (the "records-gap pattern"); a
hand-maintained status table went stale for days despite its own
regeneration hook running on every commit; an axiom repair once changed
the actual mathematical content of four admitted axioms in a way no
line-count diff could distinguish from a cosmetic edit.

### 6. What decides what gets built next, and what stops new machinery from being admitted just because it's reachable?

**`docs/1_STRATEGY.md` — Center-out prioritization.** Spectral graph
theory is the organizing center; work expands outward only along
dependencies that unlock a concrete SGT theorem, experiment, or
downstream application, ranked by a leverage test (how many proof
obligations does this unlock; does it repair a load-bearing definition;
will the interface be reused; is the expected gain worth its
maintenance cost). "Adjacency to SGT is not sufficient by itself" — this
is the same rule `proposals/weighted-matrix-tree-theorem.md`'s own gate
("admit or define nothing here until a named consumer states which
identity it needs") and `proposals/mutual-information-and-data-processing.md`'s
gate both instantiate.

**The sharper, more distinctive principle in the same document: "Load-bearing
growth."** Height is not evidence — a declaration that compiles and sits
beside existing work, without depending on any earlier definition being
*exactly* right, adds surface area but tests nothing. The concrete proof
this isn't academic: the pre-repair `cheeger_lower_bound` axiom
typechecked, was admitted, and sat undisturbed — and was false
(evaluated to `1/2 ≤ 0` on `K₂`). What caught it was not the tower
staying balanced; it was a QA witness engineered specifically to try to
knock that block over. The policy this produces: prefer work whose
success is *contingent* on an earlier definition being exactly right —
where getting the substrate wrong would make the new proof fail to
typecheck, loudly and immediately, rather than sit beside it unaffected.

### 7. How does a piece of new work actually get authorized?

**`proposals/README.md`.** Every substantial piece of work is a written
proposal before it's Lean code — an **Active priority** table (High /
Low, "Low" meaning gated on a human or technical decision, not merely
less urgent) is what an autonomous run checks before choosing what to
pursue next; a **Delivered** section keeps completed proposals in place
as evidence live documents still cite, never archived out from under
their own citations; a **Retired** section for abandoned ones. New
machinery proposed without a named internal consumer (the matrix-tree
theorem, the mutual-information module) is explicitly marked as needing
an operator decision before Step 1 begins — writing the proposal is not
authorization to build it.

**`docs/7_SGT_RADAR.md`'s re-scoring protocol** governs the QA/assurance
scoreboard specifically: a score may rise only for usable, verified
coverage (proved statements, or admitted statements with QA-exercised
interfaces and named consumers), every change must cite the milestone
that caused it in `AGENT_ACTIVITY.md`, and scores must cite declarations
that exist in the current tree — no silent re-scoring.

### 8. When something is found wrong, where does that go on the record?

**`docs/9_ERRATA.md`.** Not a bug tracker — a specific, narrow ledger:
an admitted axiom or shipped theorem statement that was demonstrated
false or inconsistent *after* already being part of the public API, by a
concrete counterexample or a derivation of `False`. A first proof of a
previously-honest axiom does not belong here (nothing was ever wrong);
a documentation or tooling bug has its own record elsewhere. The
document is explicit about how to read its own count: nine entries is
not a small number, and it is not evidence the project is unusually
error-prone — every one was found by the project's own deliberate
adversarial-fixture practice, not by an external user hitting the bug
in production. The maintenance rule: any commit-steward pass that finds
a materially false axiom or theorem statement must add an entry here in
the same pass that repairs it.

### 9. What does this project hold itself to relative to the library it wants to join?

**`governance/mathlib-standards.md`.** Scaffold intends its load-bearing
work to be adoptable into Mathlib with minimal friction, so it holds
itself to Mathlib's actual quality culture rather than a bespoke
standard — surveyed directly from Mathlib's own contributor/style/review
documentation, not assumed. The trust model this imports: **the kernel
checks proofs; humans check statements** — Lean confirms you defined
*something*, not that you defined what you meant, so new definitions
receive the heaviest review and are expected to ship with characterizing
lemmas. Scaffold's own axioms play the role Mathlib's `sorry`s play in
this framing — explicit, cited, named targets for future discharge, not
hidden debt. The document also surveys Mathlib's separated
review/merge authority, its easiest-to-hardest review checklist, its CI
gates (`lake --iofail` turning every warning into a failure; zero new
axioms; a daily independent re-verification job), and closes with a
concrete adoption table of what Scaffold can take directly under
Apache 2.0 versus what it should imitate.

### 10. What happens before anything here becomes public, licensable, or citable outside this repository?

**Patent-counsel gate, `proposals/clean-room-sgt-export.md`.** The
current repository is treated as quarantined — it may contain
patent-sensitive research context — and nothing crosses into a public
export repository without patent counsel approving the selection and
publication boundary first. This is stated explicitly as an
exposure-reduction plan, not legal advice or a determination of
patentability. A four-question inclusion test gates every file
individually (does it expose a general, application-independent SGT
interface; can its API be explained in neutral mathematical terms only;
does it have clean provenance; can it be independently recreated or
reviewed). Every proposal downstream of this gate
(`sell-the-methodology.md`, `get-outside-signal.md`,
`discovery-mcp-server.md`, `palomar-submission.md`) records the same
line: Phase 0 is explicitly outside that document's own authority.

**Release-readiness bar, `docs/traction-plan.md`.** Applies only to the
eventual clean-room repository, never to this one. Before any public
announcement: a one-sentence purpose, a pinned install snippet, real
proof examples at zero admitted axioms, and — the load-bearing line —
an explicit table separating proved declarations from assumptions,
**generated from `scripts/lint_axioms.py`'s actual count, not asserted
narratively**. A module is "proved" only if that generated count is
zero.

**Phase 6 of the adversarial review** (above) is the mechanical half of
this same concern applied continuously, not just at export time: does a
public-facing claim overstate what's proved; does a rewritten or rebased
history invalidate a citation someone outside the project already made.

### 11. The community-process layer

The four documents that look like standard open-source project
governance, because that is what they are:

- **`governance/CODE_OF_CONDUCT.md`** — a Contributor Covenant–style
  conduct policy.
- **`governance/CONTRIBUTING.md`** — contribution types, the same
  center-out scope policy as `docs/1_STRATEGY.md` restated for a
  contributor audience, submission process, PR checklists split by
  change type (axiom addition vs. QA lemmas vs. other), and a review
  process note that explicitly points reviewers at
  `ADVERSARIAL_REVIEW.md`'s hypothesis-necessity check rather than
  restating it.
- **`governance/MAINTAINERS.md`** — maintainer list and how that role is
  granted.
- **`governance/RELEASES.md`** — the changelog.

These are the only four mechanisms that live entirely inside
`governance/` and nowhere else. Everything in sections 1–10 above lives
partly or entirely in `docs/`, `proposals/`, or `scripts/`.

## Known gaps

Stated as plainly as everything above, because a governance document
that only lists what works is not one a reviewer should trust:

- **The commit-steward protocol's own "Sequence 0" is not implemented.**
  The protocol names the guarantee it wants — *the exact Git tree that
  passed the complete trusted verification ladder is the exact tree
  committed* — and states four specific ways the current live process
  fails it: the ladder runs on the live worktree and then stages
  whatever exists at commit time (no immutable snapshot); the verifier
  scripts live inside the same worktree a change could edit; the live
  `--commit` wrapper's automated path omits
  `check_refutation_independence.py` and `check_public_reachability.py`
  from its ladder (the full nine-check ladder above is the *steward's*
  procedure, not yet what runs unattended); and there is no enforced
  wall-clock or CPU budget on an autonomous run, only prompt guidance.
  None of this assumes a malicious agent — it protects against races,
  accidental edits, and stale checks in an otherwise-honest pipeline
  that is not yet fully closed.
- **Phase 4 (literature fidelity) and Phase 6 (public-exposure
  readiness) of the adversarial review cannot run autonomously by
  design**, not merely as a current limitation — both need a human with
  either the cited source text in hand or actual judgment about how an
  outside reader parses language. Treat any claim that these phases
  were "completed" by an autonomous run with the same skepticism the
  adversarial-review document itself asks for.
- **Absence from `docs/9_ERRATA.md` is not a soundness proof.** The
  document says this about itself: an axiom not yet listed there is one
  nobody has yet built the adversarial fixture to break, not one
  verified error-free.
- **This document is new** (written 2026-09-04) and has not itself been
  through the adversarial-review or commit-steward process it describes.
  Treat it as an accurate map of what exists as of that date, subject to
  the same drift risk every other status document in this repository is
  explicitly checked for (`scripts/check_scaffold_map_freshness.py`,
  `scripts/check_backlog_freshness.py`) — there is not yet an equivalent
  freshness check for this file itself.

## Verifying this yourself

Every quantitative claim above is reproducible in minutes, without
trusting this document:

```sh
lake build                                   # full library compiles
python3 scripts/lint_axioms.py               # current axiom count + citations
python3 scripts/check_citations.py           # every axiom properly cited
python3 scripts/check_refutation_independence.py  # fence proofs don't consume what they refute
python3 scripts/check_public_reachability.py # no non-public module leaks into the public API
python3 scripts/generate_qa_scoreboard.py    # current QA declaration count
```

Then read, in this order: `docs/2_ARCHITECTURE.md` (the constitution
sections 1 and 3, and §§5–10 this document draws from directly),
`docs/9_ERRATA.md` (every mistake found and how), and
`docs/AGENT_ACTIVITY.md` (the append-only record of every delivery,
including this document's own).
