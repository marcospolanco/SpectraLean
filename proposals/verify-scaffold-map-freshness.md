# Proposal: Verify Transit-Map Freshness by Reconciliation, Not the Pre-Commit Hook Alone

**Status:** Proposed 2026-08-28.

## The incident this responds to

The operator noticed `README.md`'s embedded transit map
(`docs/scaffold_map.svg`) showed the Alon–Boppana bound as "Gated" —
weeks after it was adopted (2026-08-26) and delivered COMPLETE
(2026-08-27), with its own downstream consumer already delivered the
same day. The assumption going in was that `.git/hooks/pre-commit`,
which runs `scripts/generate_scaffold_map_svg.py` on every commit,
would have caught this. It did not, because it cannot: the hook
regenerates the SVG's *rendering* from a hardcoded Python data table
(`STATUS`/`SPOKES`/`CORE` in that script) — it has no connection to any
proposal's actual status. A human has to remember to edit that literal
"when a proposal's status changes" (the script's own docstring says
this in as many words), and nobody had, since **2026-08-24** — visible
in plain sight the whole time in the header's own hardcoded stamp,
`"as of commit 73ccbff, 2026-08-24"`, itself never updated.

Auditing the rest of the table found **eight** stale nodes, not one
(fixed in `9c32a77`): Alon–Boppana Bound, Approx. Spectral Projection,
Discrete Affine Convergence, Heat — Phase C, Tikhonov — Phase 2, and
Leverage Scores were all shown gated/open/in-progress despite being
delivered complete days earlier; worst, "Matrix Chernoff Bridge"'s note
still asserted `matrix_bernstein` "does not exist anywhere in the
repository" — a finding `proposals/README.md` itself had already found
stale and corrected on 2026-08-26, two days before this fix. The
repo-wide stats line (`9 explicit axioms · 1503 QA declarations`) was
also two axioms and over a thousand QA declarations behind.

Separately: `docs/scaffold_map.html` (the interactive version) carries
a **second, independent copy** of the same station data, which the
pre-commit hook never touches at all — it can drift from the SVG's own
data without any mechanism, automated or otherwise, ever comparing the
two.

This is the same failure shape as the proposals-priority-table
indexing gap found and fixed earlier (a hand-maintained side-document,
not derived from source, silently drifting from ground truth) and the
same shape as the build-completeness incident
`verify-build-completeness.md` responded to (automation that runs on
every commit creating a false sense of currency while the thing it's
supposedly checking goes stale underneath it). The fix pattern here
should be the same: **a mandatory reconciliation script**, not a
process reminder that will be forgotten the same way the docstring's
own "update both by hand" instruction already was.

## The ask

A script, `scripts/check_scaffold_map_freshness.py`, run as a mandatory
step in the same verification ladder `check_build_completeness.py`
occupies, with two tiers of check — one exact and mechanical, one a
best-effort staleness signal that fails loud rather than silently
guessing:

**Tier 1 (hard fail, zero heuristics — do this regardless of scope
questions below):**

1. The repo-wide stats line (`N explicit axioms · M QA declarations`)
   embedded in both `scripts/generate_scaffold_map_svg.py`'s header
   text and `docs/scaffold_map.html`'s stamp must match
   `docs/5_QA_SCOREBOARD.md`'s live generated numbers exactly. Parse
   the scoreboard's generated table (same file
   `scripts/generate_qa_scoreboard.py` already writes), not a second
   hardcoded copy.
2. The SVG script's `SPOKES`/`CORE` data and the HTML's `stations`
   array must agree on every station's status, pairwise, by name. The
   script's own docstring already claims they "carry the same data
   independently" — enforce that claim mechanically instead of trusting
   it. A station present in one file and missing from the other is a
   failure, not a silent skip.

**Tier 2 (a staleness signal, not an oracle — warn, and fail the check
so a human or agent must look, but never auto-edit a status):**

3. Extend each station's data (in both files) with an explicit
   `source` field naming the `proposals/*.md` file it tracks, where one
   exists (some core/classical entries — Courant–Fischer, Cauchy
   Interlacing — may have none; that's fine, skip those). This is new
   schema, not present today, and is most of Step 1's actual work.
4. For every station with a `source`, read that proposal's own
   `**Status:**` line (or nearest equivalent — this repo's convention
   is not fully uniform, see Non-goals) and classify it into one of a
   small number of buckets by keyword (`COMPLETE`/`DELIVERED` →
   expect `proved` or `axiom`-with-a-consumer; `Proposed` with no
   delivery record → expect `open`; explicit `gated`/`blocked`/
   "requires an operator decision" language → expect `gated`). If the
   station's declared status tier doesn't match the expected bucket,
   report it as a finding — file, station, declared status, proposal's
   own status line, one line each — and exit nonzero. Do not attempt to
   fix it automatically; picking `proved` vs `axiom` vs `progress`
   for a genuinely ambiguous delivery (partial completion, a proposal
   COMPLETE at Step 1 with Step 2 deferred) is exactly the judgment
   call this repository's own discipline reserves for the person or
   run doing the actual status update, not a script guessing from
   prose.

On success, print a summary in the same style as
`check_build_completeness.py`: station count checked, count with a
`source` link, count without (an explicit list, so gaps in coverage are
visible rather than silently treated as "nothing to check").

## Where this plugs in

- **The same verification ladder as `check_build_completeness.py`**:
  `AGENTS.md` § Verification, `scripts/opencode-pursue`'s
  `verify_for_commit`, `scripts/README.md`, `docs/2_ARCHITECTURE.md`
  §10, `docs/AGENT_ACTIVITY.md`'s format block. A delivery that changes
  a proposal's status header is not "verified" until this passes,
  exactly as build completeness already isn't.
- **The pre-commit hook, in report-only mode.** Unlike
  `check_build_completeness.py` (which deliberately stayed out of the
  hook to keep it fast), this check is cheap — text parsing and regex,
  no Lean invocation, no filesystem walk of build artifacts — so Step 1
  should evaluate running it inside `.git/hooks/pre-commit` right after
  the existing SVG regeneration, printing findings to stderr without
  blocking the commit (the hook has no precedent for blocking, and
  changing that is a bigger decision than this proposal's scope).
  Blocking enforcement stays in the ladder step above.

## Acceptance bar

- Tier 1 correctly flags the historical incident: reconstruct the
  pre-fix state (9 axioms/1503 QA in the header against the current
  scoreboard's real numbers) and confirm nonzero exit; confirm it also
  flags a synthetic station present in one file's data but not the
  other's.
- Tier 2 correctly flags at least the two clearest historical cases as
  a regression fixture: a station whose `source` proposal's status line
  reads `COMPLETE`/`DELIVERED` while the station itself is still
  `"gated"` or `"open"` (the Alon–Boppana case), and a station whose
  note text is directly contradicted by current evidence (the Matrix
  Chernoff Bridge case) — the latter may need to stay a documented
  manual example rather than an automated check if no cheap general
  rule captures it; record which.
- Running it on the post-fix tree (`9c32a77` and later) exits 0.
- `docs/AGENT_ACTIVITY.md`'s format block and the verification-ladder
  documentation name this script as a required step, mirroring
  `check_build_completeness.py`'s own ladder wiring exactly.
- No Lean, no axioms, no QA declarations — this proposal's entire
  deliverable is the script, the `source`-field schema addition to both
  map files, and the documentation update.

## Non-goals

- **Not a general natural-language status classifier.** This
  repository's `**Status:**` lines are hand-written prose, not a fixed
  enum (compare `prove-subgaussian-tail-bound.md`'s
  `"DELIVERED ... but not at the unchanged statement..."` against
  `alon-boppana-bound.md`'s `"ADOPTED"` against a plain `"Proposed"`).
  Tier 2's keyword classification will have real false positives and
  false negatives; it is a forcing function to look, not a certifier.
  If Step 0 finds the false-positive rate makes it more noise than
  signal, narrowing Tier 2 to only the small set of unambiguous
  keywords (`COMPLETE`, `DELIVERED`, `Proposed` with nothing else) and
  treating everything else as "no claim, skip" is an acceptable and
  expected scope reduction — record it as such rather than forcing a
  fragile parser to handle every status line's idiosyncratic phrasing.
- **Not a rewrite of the map's visual design or taxonomy.** Several
  recent deliveries (Ramanujan Expansion Ceiling, Fiedler-subspace
  Davis–Kahan, the empirical-stationary-distribution consumer, Multiway
  and Signed graphs) have no station on the map at all — that is a
  completeness gap, not a freshness gap, and is a separate judgment
  call (which spoke does a new result belong on?) that this proposal
  does not resolve. Flag missing stations as a matter for a human/
  operator to decide, not something Tier 1 or Tier 2 invents nodes for.
- **Not a change to what the pre-commit hook blocks.** Per the
  `verify-build-completeness.md` precedent, changing the hook to reject
  commits is a bigger decision than a documentation-freshness checker
  should make unilaterally; Step 1 should default to report-only in the
  hook and hard-fail only in the explicit ladder step.
