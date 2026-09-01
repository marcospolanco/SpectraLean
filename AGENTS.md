# Scaffold Agent Instructions

## Mission

Advance Scaffold as a disciplined, axiom-transparent Lean research substrate centered on spectral graph theory. Work radiates outward from load-bearing SGT definitions and theorem interfaces toward perturbation and concentration bridges, and reusable downstream applications. `docs/3_SPECTRAL_THEORY.md` retains an example event-driven/dynamic-persistence package built along the way; it is not a roadmap goal — see that document's own scope boundary.

## Read first

- `README.md` for purpose, maturity, and the center-out policy.
- `docs/1_STRATEGY.md` for prioritization.
- `docs/2_ARCHITECTURE.md` for the trust model and contribution contract.
- `docs/5_QA_SCOREBOARD.md` for the last recorded verification state.
- `docs/8_MATHLIB_COVERAGE_MAP.md` before claiming Mathlib lacks (or has)
  something — check it first, correct it if a targeted search finds it
  stale, rather than re-surveying from scratch in a proposal.
- `proposals/README.md` for the active priority list — check before
  selecting a milestone, per Priority order item 0 below.
- `docs/EXECUTION_PLAN.md` for the active autonomous-work queue and handoff.
- `docs/AGENT_ACTIVITY.md` for recent operator-facing progress reports.
- `governance/CONTRIBUTING.md` before changing public APIs.

## Priority order

0. Check `proposals/README.md`'s Active priority table. If anything is
   marked High, pursue the highest-leverage High item first — skip any
   marked "Low — human decision required" regardless of how they'd
   otherwise rank, since those need a decision this run cannot make.
   Otherwise fall through to the ranking below.
1. Restore honest, comprehensive build reachability.
2. Repair invalid imports and source-layout defects.
3. Replace `True`, constant, and admitted placeholders with meaningful SGT definitions or theorem shapes.
4. Reduce the explicit trust surface and improve citation/index coverage.
5. Strengthen reusable SGT QA and bridge interfaces.
6. Advance application-facing work only when its inner dependencies are credible.

Choose the smallest coherent milestone that unlocks the most downstream SGT progress per unit of complexity. When outer work exposes an inner defect, move inward and fix the load-bearing dependency first.

## Working rules

- Inspect `git status` before editing and preserve unrelated changes.
- Do not edit `research/archive/` except archive metadata.
- Use Mathlib types and conventions where practical.
- Public assumptions must be explicit axioms with precise citations; do not hide them behind `sorry`.
- QA may contain no `sorry` or `admit`, and must not be presented as validation of an axiom's truth.
- Do not add breadth without naming the SGT obligation or consumer it unlocks.
- Prefer load-bearing work — a proof or QA witness that would fail if an
  existing definition were wrong, not one that merely compiles beside it —
  over reachable-but-inert breadth. See `docs/1_STRATEGY.md` § Load-bearing
  growth: the path to falsifiability.
- Do not commit, push, publish, rewrite history, or perform broad deletion.
- Never access or modify files outside this worktree.

## Autonomous reporting

When running under `scripts/opencode-pursue`, maintain the two versioned
operator-facing records:

- Before editing, update `docs/EXECUTION_PLAN.md` with the active milestone,
  its SGT-leverage rationale, and next action; append an `in-progress` entry
  to `docs/AGENT_ACTIVITY.md` with the same information. Every new activity
  entry must begin with an exact UTC timestamp, wrapper run identifier, and
  OpenCode session ID, using the required format at the top of that file.
- After every coherent milestone, update the execution plan and append a
  compact activity entry: UTC date/time, status, changes or investigated
  area, decisive commands and outcomes, verification, remaining risk, and
  next handoff.
- Before a normal exit, append a terminal `completed`, `blocked`, or
  `superseded` entry. Do not expose chain-of-thought, credentials, or raw
  unbounded command output; the wrapper retains raw local transcripts.

Use `date -u +%Y-%m-%dT%H:%M:%SZ` for the timestamp. Before the terminal
entry, inspect `opencode session list --max-count 1 --format json` to obtain
the session ID. If the command is inconclusive, report `unavailable`; never
invent an identifier.

If the same failure repeats or no meaningful source/documentation progress is
possible after 12 tool steps, record exact evidence as a blocker, pivot to a
ready safe milestone, or end the run. Do not wait indefinitely for a provider
response.

## Verification

Run checks proportionate to the change. The default build currently succeeds;
distinguish a regression from excluded or uncertified modules.

```sh
python3 scripts/generate_qa_scoreboard.py
python3 scripts/lint_axioms.py
python3 scripts/check_refutation_independence.py
python3 scripts/check_public_reachability.py
python3 scripts/check_citations.py
python3 scripts/check_markdown_links.py
lake build
python3 scripts/check_build_completeness.py
python3 scripts/check_scaffold_map_freshness.py
python3 scripts/check_backlog_freshness.py
```

`check_build_completeness.py` runs after every full `lake build`: a
"Build completed successfully" exit does not by itself certify every
on-disk source (an interrupted run once left a broken QA file that the
full build passed over silently). The script fails nonzero if any
`Scaffold/**/*.lean` source has a missing or mtime-stale `.olean`
artifact; its docstring records the calibrated remediation.

`check_refutation_independence.py` (2026-08-30,
`proposals/axiom-audit-tooling.md`) verifies mechanically that every
QA declaration tagged `-- @refutes: <axiom>` does not, in its proof
term, depend on the axiom it refutes — the "a refutation cannot
consume what it refutes" discipline previously checked by hand in
every repair record. It runs `#print axioms` through a generated
`lake env lean` file, so it requires the built oleans (run it after
`lake build`, or accept the elaboration cost of loading imports). A
tag naming anything but a currently admitted axiom fails, so tags are
removed with their axiom's retirement.

`check_public_reachability.py` (2026-08-30, same proposal) walks the
import graph from the public umbrella `Scaffold.lean` and fails if any
module under `wip/` (the only non-public Lean directory, per its
Step-0 survey) is reachable, directly or transitively, or if any
`wip.*` import appears in a public module at all.

`check_scaffold_map_freshness.py` reconciles the transit map's two
hand-maintained data tables (the SVG generator's and the HTML's)
against each other, against the scoreboard's generated numbers, and
against each station's cited proposal's own status line — a delivery
that changes a proposal's status header is not verified until it
passes. The pre-commit hook runs it report-only; this ladder step is
the blocking enforcement.

`check_backlog_freshness.py` (2026-09-01, found stale by the commit
steward after a two-week, dozens-of-deliveries gap) fails if
`docs/6_SGT_BACKLOG.md`'s "Last reviewed" date has fallen more than
seven days behind the latest `docs/AGENT_ACTIVITY.md` entry. It is a
clock check, not a content check — it cannot verify the backlog's
prose is accurate, only that someone has looked recently. A delivery
that closes or opens a gate the backlog names should update that
item's text in the same delivery (the records-ladder obligation
`proposals/README.md` already carries) and then bump the reviewed
date; this check only catches the case where that discipline lapses
entirely.

`lint_axioms.py` includes the degenerate-corner guard check
(`proposals/lint-axiom-degenerate-corner-guards.md`) and the
replacement-path documentation check (`proposals/axiom-audit-tooling.md`,
2026-08-30: every `Scaffold/Mathlib` axiom's docstring must carry a
labeled `Replacement path:` note — the theorem, engine, or Mathlib gap
that would retire it, or an explicit no-known-route statement).
The degenerate-corner guard: every
`Scaffold/Mathlib` axiom whose signature carries a `Fintype`-carried
matrix/vector index type with no visible `Nonempty` guard, or a
`Measure` argument with no visible probability/finite-measure/total-
mass guard, is flagged unless the script's per-axiom allowlist records
why the corner is accepted. A new axiom admission should settle its
allowlist entry deliberately at admission time, not at the next lint
pass.

For Lean changes, directly build or elaborate every changed module and its closest QA consumer; do not rely only on the umbrella target.
