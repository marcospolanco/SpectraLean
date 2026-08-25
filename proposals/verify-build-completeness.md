# Proposal: Verify Build Completeness by File Reconciliation, Not Exit Status Alone

**Status:** COMPLETE (delivered 2026-08-25 by run `20260825T032035Z-run-1`,
one run, Steps 0+1 — see the delivery record at the end of this file);
**priority was:** High (tooling/process, not mathematics — authorized a new
verification script and a change to the documented verification ladder every
delivery run already follows; no Lean content, no axiom admissions).

## The incident this responds to

During the 2026-08-24/25 session, `Scaffold/QA/SpectralGraph/Magnetic_QA.lean`
was left with three real compile errors (two redundant `match` alternatives,
one unsolved `⊢ False`) by a run that was interrupted mid-delivery by its
own step budget before finishing the file. A subsequent operator-run
`lake build` — the standard, full, no-target-specified invocation used
throughout this project's verification ladder — printed **"Build
completed successfully"** with zero reported errors. The bug was only
caught by *explicitly* targeting the file
(`lake build Scaffold.QA.SpectralGraph.Magnetic_QA`), which failed
loudly and immediately with the exact three errors.

This means the project's most-repeated verification step — "run `lake
build`, confirm it says Build completed successfully" — silently passed
over a genuinely broken file. Reading `lakefile.lean`'s own comment
(*"the default target is the library root `Scaffold.lean`, so `lake
build` certifies every public module reachable from the umbrella"*)
names the exact assumption that failed: a file only just created,
mid-session, was not yet part of whatever Lake's default build actually
scanned in that invocation, so it was silently absent from the checked
set rather than reported as an error. **The false-positive risk is not
theoretical — it happened, in this repository, in this session, and was
caught only because a human asked "are we sure?" before committing.**

## The ask

A reconciliation script, `scripts/check_build_completeness.py`, run as a
**mandatory step after every `lake build`** and before any commit,
alongside the existing `lint_axioms.py` / `check_citations.py` /
`check_markdown_links.py` triad:

1. Recursively enumerate every `Scaffold/**/*.lean` source file (excluding
   the git-ignored `wip/` scratch directory).
2. For each, compute the expected build artifact path under
   `.lake/build/lib/<module-path>.olean`.
3. Fail (nonzero exit, listing every offending file) if:
   - the `.olean` does not exist at all, **or**
   - the `.olean`'s mtime is older than the `.lean` source's mtime (a
     stale artifact — the exact signature of a file whose latest edit
     was never actually rebuilt).
4. On success, print the total file count checked, so a human or agent
   reading the log sees "N source files, N fresh artifacts, 0 stale, 0
   missing" rather than inferring completeness from silence.

This is deliberately **not** a re-implementation of Lean's type checker
and **not** a change to `lakefile.lean`'s target configuration — it is a
cheap, independent, file-system-level cross-check that a build claiming
success actually touched everything on disk. Confirmed empirically
against the current tree: `.lake/build/lib/Scaffold/QA/SpectralGraph/Magnetic_QA.olean`
now postdates its source by design; before the fix, the same comparison
would have flagged it (either missing or stale, depending on exactly
when the interrupted run's edit landed relative to the last successful
build of that specific file).

## Where this plugs in

- **The documented verification ladder.** Every delivery entry in
  `docs/AGENT_ACTIVITY.md` already cites a fixed sequence: `lake env
  lean` on changed modules, explicit `lake build <target>` for each new
  module, a full `lake build`, `lint_axioms`, `check_citations`,
  `check_markdown_links`, scoreboard regeneration. Add
  `check_build_completeness.py` to this list, run after the full `lake
  build` and before any of the record-file updates — a delivery is not
  "verified" until this passes.
- **The operator's own commit-time check.** The standing instruction
  ("commit whenever the repo is idle and passes verification") should
  read this script's exit code as part of "passes verification," not
  substitute a bare `lake build` for it.
- **Not the pre-commit hook.** The existing `.git/hooks/pre-commit`
  regenerates `docs/scaffold_map.svg` on every commit and should stay
  fast; a full reconciliation pass belongs in the pre-commit *verification*
  step a human or agent runs deliberately before staging, not in an
  automatic hook that fires on every commit regardless of whether a
  fresh `lake build` just ran.

## Acceptance bar

- The script runs in well under a minute on the current tree (a
  filesystem walk plus stat calls — no Lean invocation).
- It correctly flags the historical incident: run it against a tree
  state reconstructed with `Magnetic_QA.lean`'s three-error version and
  confirm it reports that file as stale/missing (a regression test,
  committed as a fixture or documented manually since the broken
  version is not worth preserving in-tree).
- `docs/AGENT_ACTIVITY.md`'s format block and any strategy/process
  documentation describing the verification ladder are updated to name
  this script as a required step.
- No Lean, no axioms, no QA declarations — this proposal's entire
  deliverable is the script plus the documentation update.

## Delivery record (2026-08-25)

Delivered in one run by `20260825T032035Z-run-1`: the script
(`scripts/check_build_completeness.py`), the ladder wiring (five
locations), and — unplanned but decisive — the remediation of eight
live findings the script surfaced **on its first invocation against the
real tree**.

**The script.** Exactly the ask: enumerates `Scaffold.lean` (the
default target itself, so it must always have an artifact) plus every
`Scaffold/**/*.lean` (git-ignored scratch excluded), maps each to
`.lake/build/lib/<module-path>.olean`, and fails nonzero listing every
MISSING (no artifact — never elaborated by any invocation) and STALE
(artifact mtime strictly older than source mtime, nanosecond
resolution) file, printing `N source files, N fresh artifacts, S stale,
M missing`. Exit codes: 0 complete, 1 incomplete, 2 operational error.
No Lean invocation, no lakefile parsing, no Lake-internals
re-implementation (the trace files hold only a Lake-internal UInt64
`depHash` — reproducing it would be exactly the fragile
internals-copy this proposal forbids). `--root` supports running
against arbitrary trees (used by the regression suite).

**Semantics calibrated by two decisive experiments on the pinned
toolchain (v4.14.0).** (1) A source whose *content* changed since its
last build (mtime newer, bytes different) *is* rebuilt and its olean
rewritten by an explicit target build — real staleness is fixable. (2)
A pure `touch` of an up-to-date source does **not** trigger a rebuild
(verified: olean mtime unchanged) — Lake's up-to-date check is
content-hash based, so a byte-identical roundtrip (git
stash/checkout, editor save) leaves a *permanently* mtime-stale
artifact that a plain rebuild cannot refresh. STALE therefore
necessarily fails closed (it is the incident's own variant — see the
live findings below), with the docstring recording the
always-terminating remediation: `lake build <module>` rewrites real
staleness; if Lake reports the module up to date yet the check still
flags it, remove the gitignored derived artifact and rebuild once —
forcing re-elaboration, which both refreshes the timestamp and
re-proves the current content compiles.

**The live findings (the fence's first catch).** Run 1 against the
real tree reported 3 MISSING + 5 STALE — this was not a dry-run tool;
the defect class it targets was present *right then*:

- MISSING: `Scaffold/QA/Perturbation/ProjectionGap_QA.lean` (586
  lines) and `Scaffold/QA/SpectralGraph/Expander_QA.lean` (1,181
  lines) — two real QA modules with no artifact at all — plus
  `Scaffold/Mathlib/Core.lean` (a 2-line legacy re-export shim from
  the initial commit that nothing imports, hence never built). All
  three elaborate clean and now have artifacts.
- STALE: `Dynamics_QA.lean` — a **genuine never-rebuilt content
  edit** (source edited 2026-08-20, artifact still 2026-08-18; no
  invocation had elaborated the current bytes until this run's
  rebuild) — the incident class caught live, not reconstructed;
  `Mixing_QA.lean` and `SpectralCertificates_QA.lean` likewise
  rebuilt; `Subgaussian.lean` and `Entropy_QA.lean` were the
  benign byte-identical-roundtrip case (Lake skip; remediated by the
  documented artifact-removal route, which re-elaborated both —
  green, one pre-existing unused-variable linter note in
  `Subgaussian.lean` only).

Every remediation was a real elaboration, so the tree is not merely
green-by-mtime: all 103 sources have been elaborated as-is.

**Regression suite (the acceptance bar's incident reconstruction).**
A synthetic mini-tree (`--root` at the temp scratch) containing: a
three-error `Scaffold/QA/SpectralGraph/Magnetic_QA.lean` with no
artifact — **flagged MISSING, exit 1**, the historical incident
reproduced; an explicit-mtime STALE pair (flagged with both mtimes);
a fresh module and umbrella (counted); a `wip/Scratch.lean`
(excluded — 5 files counted, not 6); usage and bad-root errors (exit
2). Healing the tree flips the run to `5 source files, 5 fresh
artifacts, 0 stale, 0 missing`, exit 0. Documented here rather than
committed as a fixture, per this proposal's own either/or.

**Ladder wiring (all five documented locations).** `AGENTS.md` §
Verification (the command list plus the rationale paragraph);
`scripts/opencode-pursue`'s `verify_for_commit` (immediately after
`lake build`, so `--commit` fails closed on an unreconciled tree);
`scripts/README.md` (the script table); `docs/2_ARCHITECTURE.md` §10
(named in the measured-properties sentence plus a paragraph on why an
exit status is not coverage); `docs/AGENT_ACTIVITY.md` (the format
block now requires any entry claiming a verified full build to record
this script passing immediately after the `lake build` it cites).

**Verification.** Full ladder on the real tree, in the mandated
order: `lake build` ✔ ("Build completed successfully"; the log's only
Scaffold diagnostic the documented pre-existing `Subgaussian.lean`
unused-variable note); `check_build_completeness.py` immediately
after: **103 source files, 103 fresh artifacts, 0 stale, 0 missing**,
exit 0; `lint_axioms` (10 axioms, no issues), `check_citations`,
`check_markdown_links` pass; scoreboard regeneration idempotent
(md5-stable across two runs). No Lean, no axioms, no QA declarations
changed — the seven elaborated modules were remediation of existing
sources, not edits.

**Remaining risk / notes.** The STALE tier is deliberately
conservative: byte-identical roundtrips fail until the documented
force-re-elaboration runs (rare; git operations are the usual
trigger — this run itself induced one live via its own `touch`
experiment and closed it the same way). The check is mtime-based, so
clock skew between source and artifact writes could in principle
mask a fast edit-build-edit-build sequence within the same
filesystem timestamp tick; nanosecond comparison makes this
unlikely, and content-hash currency remains Lake's own ground truth.
No pre-commit hook was added, per the proposal's explicit choice.
