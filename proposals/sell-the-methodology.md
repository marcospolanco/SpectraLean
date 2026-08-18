# Proposal: Sell the Methodology, Not the Subfield

**Status:** Proposed. Assistant's assessment of project direction, requested
2026-08-18. Authorizes no Lean changes, publication, or drafting of the
artifact described below.

Companion to [Get Outside Signal](get-outside-signal.md), which this
proposal does not replace — it reframes what gets emphasized once that
proposal's Phase 1 export exists, and adds a parallel artifact rather than
a new phase. Also companion to `docs/1_STRATEGY.md`'s [Load-bearing
growth](../docs/1_STRATEGY.md#load-bearing-growth-the-path-to-falsifiability)
section, which this proposal argues should be externally legible, not just
an internal practice note.

Assessed from live Reservoir star data pulled this session, the
AI-for-formalization arXiv literature surfaced this session, `docs/1_STRATEGY.md`,
`docs/2_ARCHITECTURE.md`, `docs/AGENT_ACTIVITY.md` (the Cheeger-refutation
incident), `docs/traction-plan.md`'s stated audience and step-5 shape, and
`proposals/{get-outside-signal,clean-room-sgt-export}.md` for the
publication gate.

## The finding

Reservoir's actual star ranking (checked this session) has no graph-theory
library anywhere near its top tier. What correlates with popularity there
is celebrity (`teorth/Analysis`, `teorth/equational_theories`,
`google-deepmind/formal_conjectures`), broad non-specialist audience
(physics, general undergraduate analysis, CS fundamentals — all larger
publics than graph theory), a viral hook (FLT's 350-year-old open problem,
`equational_theories`' crowdsourced puzzle), or being a *tool* every Lean
user needs regardless of subfield (`LeanCopilot` at 1,310★, `paperproof`,
`ryu`, `batteries`) rather than a content library people opt into by
mathematical taste. SGT loses on all four axes and always will — it is a
specialist's specialist topic, and no amount of execution quality changes
that ceiling.

But subfield choice was never actually what makes this repository unusual.
Re-read what `docs/1_STRATEGY.md` and `docs/2_ARCHITECTURE.md` actually
describe: 18 cited axioms with precise provenance, zero `sorry`/`admit`,
a documented incident where the project's own QA caught its own false
admitted statement (`old_cheeger_lower_bound_refuted_QA`,
`docs/AGENT_ACTIVITY.md`), and — as of this conversation — an explicit
named principle for growing formalized material such that growth is itself
a falsification test
([Load-bearing growth](../docs/1_STRATEGY.md#load-bearing-growth-the-path-to-falsifiability)).
None of that is a spectral-graph-theory result. It is a rigor practice for
agent-driven formalization that happens to have been demonstrated on SGT.

**The mechanism, stated precisely.** Mathlib and Scaffold put trust-review
at opposite ends of the same process, and that inversion — not the axiom
count, not the QA count — is the actual pitch. Mathlib is careful at the
edge: a human expert has to vouch for a change, Zulip discussion has to
happen, style and generality have to conform, before anything enters the
trunk — the cost is paid once, upfront, by a gatekeeper, and everything
inside is trusted by default afterward. That discipline is why Mathlib
grows slowly and why it is trusted. Scaffold runs the same trade in
reverse: the center is allowed to be mushy — an axiom enters cheap, cited
but not community-vetted — and the actual test of whether it holds is
deferred downstream, to whether later load-bearing work can be built on
top of it without breaking. The Cheeger-refutation incident is this
mechanism caught in the act: the axiom sat admitted and wrong until later
work happened to stress it, and a QA witness engineered to knock it over
caught the break — nobody reviewed it into correctness at the door. Each
individual step stays conservative (one step per run, no new axioms, a
QA witness required), but because trust-review is deferred rather than
paid upfront by a gatekeeper, the aggregate pace is not bounded by expert
review bandwidth the way Mathlib's is.

This is structurally close to blockchain confirmation, and worth naming as
such to an audience that will recognize the shape immediately: a block
isn't trusted because a committee vetted it before inclusion, it is
trusted because of what gets built on top of it afterward — depth of
subsequent confirmation is the actual signal, and a bad block gets found
out because the chain built on it eventually breaks or gets abandoned. The
mechanisms differ in kind, not just detail, and the difference matters:
blockchain finality is a probabilistic, economic argument (reversing a
deep chain is expensive), while Scaffold's version is deductive (a proof
that is load-bearing on a false axiom's exact statement either fails to
typecheck or fails a QA witness, mechanically, not probabilistically). But
the structural claim is the same shape — trust accrues from the depth and
density of what has been built on top without failure, not from a single
upfront gate — and it is the fastest way to make the pitch legible to a
reader who has never opened a Lean file but has thought about confirmation
depth.

**Two honest limits on this pitch, both real.** First, "adversarial"
overstates current maturity: there is no systematic, continuously-running
harness trying to break every axiom; the Cheeger catch was one instance
where later work happened to cross-check a shape, not a running
adversarial pipeline. The mechanism is real and demonstrated; the coverage
is not yet comprehensive, and the writeup should claim the former without
implying the latter. Second, the inversion only pays for itself if
load-bearing consumption keeps pace with admission — an axiom that gets
admitted and then never gets built on top of gets none of this benefit, it
just sits as unverified risk with no compensating check, exactly as
exposed as it would be under any other model. The speed this approach buys
is real only as long as growth stays load-bearing rather than merely
adjacent, which is the entire reason that distinction earned its own named
principle in `docs/1_STRATEGY.md` rather than staying implicit.

## Why this, why now

There is a live, small, growing research genre built around exactly this
question — how to do AI-assisted or agent-driven Lean formalization
credibly — distinct from "Lean/Mathlib contributors who want graph
Laplacians" (`docs/traction-plan.md`'s current, and only, stated audience).
Surfaced this session: "Sorries Are Not the Hard Part: An Expert-Review
Case Study of a Semi-Autonomous Formalization" (arXiv:2606.13925), "QED: An
Open-Source Multi-Agent System for Generating Mathematical Proofs on Open
Problems" (arXiv:2604.24021), "LeanArchitect: Automating Blueprint
Generation for Humans and AI" (arXiv:2601.22554), and "MathlibPR: Pull
Request Merge-Readiness Benchmark for Formal Mathematical Libraries"
(arXiv:2605.07147) — the last one particularly relevant given the Mathlib
AI-contribution-bar finding already folded into `get-outside-signal.md`.
This audience does not need to find SGT interesting. It needs the practice
to be legible and evidenced, and this repository already has the evidence
— it just isn't packaged for that reader anywhere.

## Recommendation

Package a technical case-study writeup — not a Lean-package pitch — as a
companion artifact to `get-outside-signal.md`'s export, aimed at the
AI-for-formalization research audience *in parallel with*, not instead of,
the graph-theory audience `traction-plan.md` already names.

## Calibration — do not oversell the analogy

This will not behave like `LeanCopilot` (1,310★) just because it trades a
subfield pitch for a tooling-adjacent one. `LeanCopilot` is installable
software with immediate utility to any Lean user; stars are the right
success metric for it. A methodology writeup is closer in kind to the
arXiv case-study papers named above than to a tool — its success metric is
readership and citation, not GitHub stars, and its ceiling is smaller and
slower to reach. That does not invalidate the pitch — the audience is
real, current, and actively publishing — but this is a niche-credibility
play, not a virality play, and should be scoped with that ceiling in mind
from the start.

## What this does not replace

- **Not a replacement for `get-outside-signal.md`'s phases.** The Mathlib
  PR and the `papers/` index still matter on their own terms; this is an
  additional artifact drawn from the same export, not a substitute for it.
- **Not an argument to abandon SGT.** The methodology has no evidence
  without a demonstrated body of work behind it, and that body of work is
  exactly what already exists. SGT remains the worked example — it stops
  being pitched as the reason to care.
- **Not a lighter version of the Phase 0 gate.** If anything, this needs a
  *harder* clean-room pass than the code export, not an easier one — prose
  describing internal process and reasoning is more likely to leak
  application-specific or patent-sensitive framing than isolated Lean
  declarations are. This document does not authorize drafting the writeup
  ahead of that review.

## Concrete artifact

A short technical note, matching the shape `docs/traction-plan.md`'s own
step 5 already specifies ("the problem, API design, trust boundary,
examples, and roadmap") but moved earlier rather than gated on prior
adoption:

1. The trust-boundary discipline itself — mushy center / hard crust, from
   `docs/2_ARCHITECTURE.md` and `docs/1_STRATEGY.md`.
2. The load-bearing-growth/falsifiability principle, evidenced concretely
   by the Cheeger-refutation incident: an admitted statement that
   typechecked, sat in the tower, and was false, until a QA witness
   engineered to knock it over caught it. A real, checkable, honestly
   slightly-embarrassing anecdote is far more convincing to this audience
   than an abstract rigor claim.
3. Framed toward the specific research genre named above as the actual
   peer set to be *read alongside* — not competed against on stars.

## Open next step

Scope whether this note is written as a standalone writeup or folded into
the `papers/` index's presentation layer once that exists. Separately, and
outside this document's authority: raise with whoever owns the clean-room
review whether a prose methodology writeup needs a stricter sanitization
pass than the code export, before committing any time to drafting it.
