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
