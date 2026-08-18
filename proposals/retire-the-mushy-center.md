# Proposal: Retire the Mushy Center Systematically

**Status:** Proposed. This document authorizes no Lean changes, axiom
removals, worktree creation, commits, or external publication on its own.

## Goal

Replace Scaffold's explicit cited axioms with proved theorems wherever a
credible proof route exists, while preserving the project's trust boundary:
no hidden `sorry`, no weakened public theorem shape, and no claim that an
unproved source result has become formalized.

The aim is not an arbitrary numerical target. Some literature-backed
assumptions may remain necessary until Mathlib or a local proof route catches
up. The near-term deliverable is a disciplined elimination program in which
every current axiom has an owner, evidence-backed disposition, and next
action.

## Why a campaign, not a sequence of opportunistic proofs

The hard crust has already shown that individual axiom retirements are
possible: a bad statement shape can be exposed by QA, repaired explicitly,
and then replaced by a theorem. Repeating that process one declaration at a
time without an inventory, however, risks optimizing for whichever lemma is
most visible rather than the one that unlocks the most downstream SGT work.

An axiom-elimination campaign makes the mushy center a managed dependency
surface. It prioritizes results with real consumers and plausible proof paths,
and it records genuine blockers instead of replacing a visible axiom with an
equally opaque derived dependency.

## Operating model

### 1. Establish an elimination board

Before formalization work starts, generate a versioned board from the current
explicit-axiom surface. Each row must name:

- the declaration, defining module, precise public type, citation, and current
  axiom count recorded by `scripts/lint_axioms.py`;
- direct and transitive Scaffold consumers, with the load-bearing consumer
  called out separately;
- the candidate route: an exact Mathlib theorem, a local proof from existing
  hard crust, or a prerequisite proof that must be retired first;
- the statement-fidelity result: exact replacement, intentional public API
  migration, or a detected false/underspecified shape requiring repair before
  proof work;
- expected edit surface and hotspot classification; and
- status: `survey`, `ready`, `in progress`, `blocked`, `retired`, or
  `not currently credible`, with dated evidence for the last two statuses.

The board is a planning and review artifact, not a claim that every source
result is true. Its count must be generated from repository evidence at every
milestone rather than copied from an old proposal.

### 2. Survey in parallel, prove only non-overlapping slices in parallel

Survey work is safe to parallelize. A survey agent may inspect the Mathlib
pin, search exact theorem names and type mismatches, map consumers, and write
a small proof plan. It must not modify public Lean files or change the axiom
surface.

Formalization work gets one project-local worktree per owned slice. An agent
owns its target declaration, directly necessary helper module, closest QA
consumer, and corresponding board entry. It may not absorb unrelated changes
from another worktree.

`GraphTheory.Spectral` is a shared hotspot. Only one proof agent writes it at
a time. Other candidates should first be expressed through stable helper
modules or through read-only surveys; parallel agents must not race to edit a
large central file merely because their axioms have different names.

### 3. Use a two-stage proof workflow

For each candidate:

1. **Survey:** establish the exact proof route and reproduce the proposed
   theorem type in a scratch check. If the type does not faithfully match the
   intended mathematics, stop and record a statement-shape repair proposal.
2. **Formalize:** replace the axiom with a theorem of the same public shape,
   or make the smallest explicitly reviewed migration. Add only proved helper
   declarations; do not admit new facts to make the retirement appear to
   succeed.
3. **Falsify:** add or strengthen a QA witness that would fail if the newly
   proved route or its load-bearing dependency were wrong. A proof that merely
   compiles beside the former axiom is insufficient.
4. **Integrate:** an independent integration pass builds the changed module,
   its closest QA consumer, and the umbrella; updates citations, indexes,
   scoreboard, radar, and the elimination board; then records the axiom-count
   movement from the generated tooling.

The implementation agent remains unable to commit. The integration wrapper
may create a commit only after its independent verification and review gates
pass.

## Selection rule

Rank `ready` candidates by the following order:

1. A proof retirement that unblocks a concrete SGT theorem or several
   downstream consumers.
2. A statement-shape repair that prevents a false or misleading axiom from
   contaminating the crust.
3. A candidate with an exact Mathlib route or a short dependency path through
   already-proved Scaffold definitions.
4. A candidate that can be isolated outside a shared hotspot.
5. A low-risk proof that validates the worktree and integration process.

Do not prioritize an axiom simply because it is old, easy to rename, or easy
to hide behind a new wrapper. A blocked candidate remains visible on the
board; it is not silently displaced by an axiom-backed corollary.

## Pilot

Start with two or three `ready` candidates that do not share a writable
module. The current high-priority normalized Cheeger transfer is a natural
survey candidate because it has a named consumer and the combinatorial
variational route is already proved; its survey must still establish the
exact normalized transfer before implementation starts. Pair it with one
candidate outside `GraphTheory.Spectral` when the board identifies a credible
route.

The pilot succeeds only if it demonstrates all of the following:

- an independently verified theorem replaces at least one explicit axiom;
- the closest QA consumer exercises the replacement rather than the former
  assumption;
- concurrent worktrees remain isolated and integrate without absorbing
  unrelated changes; and
- the board correctly records a blocked candidate when the survey finds no
  credible route.

Scale beyond the pilot only after those outcomes are reviewed. This prevents a
large swarm from producing conflicting, weakly tested proof attempts in the
same central modules.

## Acceptance criteria for each retirement

- No new axiom, `sorry`, or `admit` is introduced.
- The public statement is identical, or the migration and its consumers are
  explicitly documented and reviewed.
- The changed module and nearest QA consumer elaborate directly.
- A QA proof is load-bearing on the replacement or exposes a relevant
  negative witness.
- `scripts/generate_qa_scoreboard.py`, `scripts/lint_axioms.py`,
  `scripts/check_citations.py`, `scripts/check_markdown_links.py`, and
  `lake build` pass in the integration worktree.
- The board, source/index mapping, scoreboard, radar, execution plan, and
  activity record distinguish the proved result from any axioms that remain.

## Deferred decisions

This proposal does not decide whether every axiom should ultimately be proved
locally, upstreamed to Mathlib, retained as a transparent research assumption,
or removed after a public API migration. Those are case-by-case decisions the
elimination board is meant to make reviewable.

It also does not authorize broad parallel editing of shared SGT-center files.
Worktree parallelism is a containment mechanism, not a reason to abandon
dependency order or review.
