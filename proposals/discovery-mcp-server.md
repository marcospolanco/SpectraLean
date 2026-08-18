# Proposal: A Discovery-Layer MCP Server

**Status:** Proposed. Assistant's assessment of project direction,
requested 2026-08-18. Authorizes no server deployment, hosting, or
external publication. Gated on the same clean-room review as every other
document that stages outreach content — see [Clean-Room SGT
Export](clean-room-sgt-export.md) — and, per the calibration below,
plausibly a *stricter* pass than the code export itself.

Companion to [Get Outside Signal](get-outside-signal.md) — this is a
candidate distribution mode for its Phase 3, not a replacement for the
Lake dependency relationship itself — and to [Sell the
Methodology](sell-the-methodology.md), since the actual audience for this
tool is closer to AI-agent-tooling developers than to the formal-methods
engineers who consume Scaffold as a pinned dependency.

Assessed from `scripts/{lint_axioms,check_citations,generate_qa_scoreboard}.py`,
`docs/{5_QA_SCOREBOARD,7_SGT_RADAR,8_MATHLIB_COVERAGE_MAP}.md`,
`index/{sources,map}/*.md`, and `clean-room-sgt-export.md`'s quarantine
policy.

## The finding

There are two separate problems that look like one. **Integration** —
building a certified proof on top of Scaffold's theorems — has exactly one
real mode: a pinned Lake dependency, `require`d and `import`ed, because
Lean's trust model requires the consumer's toolchain to actually
re-elaborate what it depends on. No interface abstraction, including an
MCP server, can substitute for that; you cannot mock or stub a Lean
dependency the way you'd stub an HTTP API. **Discovery** — knowing whether
a given declaration is proved or admitted, what a coverage axis's ceiling
is, what's absent — is a different problem, currently solved only by
grepping markdown by hand. That second problem is real, distinct, and is
where an MCP server actually fits: not as a substitute for the dependency,
but as a queryable front end for data this repository already generates.

## Recommendation

Ship the underlying data as static, generated files first (Phase 1).
Build a live MCP server wrapping that data only if Phase 1 turns out to be
insufficient (Phase 2) — do not default to "build a server" just because
it is technically possible when the underlying data is already static and
regenerated per release, not truly dynamic.

## Calibration

Do not treat this as automatically worth building. The data behind every
proposed tool below — axiom status, radar scores, coverage-map entries —
is already fully expressed in generated markdown files
(`docs/5_QA_SCOREBOARD.md`, `docs/7_SGT_RADAR.md`,
`docs/8_MATHLIB_COVERAGE_MAP.md`) that any AI coding assistant with file
access can already read directly, without a server. MCP earns its cost
specifically when the consumer *doesn't* have file access to the export
(a remote agent, a hosted tool, a query interface separate from cloning
the repo) or when the query shape benefits from structured lookup over
free-text grep (e.g., "give me every declaration whose axiom count is
nonzero" as a typed call rather than a regex). If neither of those is
true for the actual expected consumer, Phase 1's static files are the
entire deliverable and Phase 2 should not be built.

## What it would expose (Phase 2 scope, if reached)

Narrow, structured lookups over already-generated data — no new
mathematical work, no semantic search, no write access:

1. `axiom_status(declaration_name)` → proved / admitted (with citation,
   sourced from `index/sources/*.md`) / derived / absent.
2. `coverage_map(discipline)` → the relevant row(s) of
   `docs/8_MATHLIB_COVERAGE_MAP.md`.
3. `radar(axis)` → the relevant subject or assurance axis score and
   evidence from `docs/7_SGT_RADAR.md`.
4. `qa_scoreboard()` → the current generated counts from
   `docs/5_QA_SCOREBOARD.md`.

**Explicitly out of scope:** free-text or embedding-based semantic search
over declarations. That is a materially larger undertaking — "Lean
Finder: Semantic Search for Mathlib" (arXiv:2510.15940, surfaced in this
session's earlier research) is the closest existing prior art, built for
a corpus orders of magnitude larger than Scaffold's; rebuilding that
machinery here has no named consumer and fails the leverage test on its
own terms.

## The gate this needs, and why it is stricter than the code export

**A live service must only ever serve data generated from a tagged,
clean-room-exported release — never this quarantined repository's live
working tree.** This is the load-bearing constraint of the whole
proposal. A static tagged release is reviewed once, at a known point in
time, before publication. A live server that regenerates or proxies
against an evolving source is a standing disclosure channel: if it is
ever pointed at this repository instead of the export, or if the export
pipeline and the server's data source drift apart, it could surface
exactly the patent-sensitive material `clean-room-sgt-export.md` exists to
contain, continuously and without a further review gate. Treat "which
repository does the server's data source point at, and how is that
enforced" as a harder question than anything in the code export's own
approval gate, not an equivalent one.

## Hosting and maintenance

An always-on service is a different, ongoing commitment relative to a
one-time tagged release — uptime, cost, and who is on the hook for it
don't go away after launch the way a documentation artifact's cost does.
Recommend the cheapest viable version if Phase 2 is reached at all: a
read-only endpoint regenerated on each tagged release, not a live
database, with no user-supplied input beyond a declaration or axis name
(no free-text injection surface, since Phase 2 explicitly excludes
search).

## Build order

### 0. Outside this document's authority
The clean-room export must exist and be tagged before Phase 1 has
anything to point at. This cannot be scoped against the quarantined
repository's current state.

### 1. Static generated data in the export
Carry `scripts/{lint_axioms,check_citations,generate_qa_scoreboard}.py`'s
output (or a machine-readable variant — JSON alongside the existing
markdown) into the clean-room export itself, regenerated per release. No
server. This alone may satisfy the actual need: an AI coding assistant
with the export cloned can already read it directly.

### 2. A minimal read-only MCP server (only if Phase 1 proves insufficient)
Wrap Phase 1's static, per-release data with the four narrow tools listed
above. No write access, no search, no live proxy to this repository. Scope
as its own decision once there is a real, named consumer who cannot use
Phase 1's files directly — not a default continuation.

## Deferred and removed

- **Semantic/embedding search** — out of scope; no named consumer, existing
  prior art (Lean Finder) already covers the general problem at a scale
  this repository doesn't have.
- **Any write or mutation capability** — this is a discovery tool, not an
  editing interface; adding one would reopen every publication-gate
  question this proposal exists to close.
- **Serving live data from this quarantined repository** — removed
  entirely, not deferred. See the gate above.

## Operating instructions

This is not a Lean-proof proposal, so "one step per run, no new axioms"
does not directly apply — the equivalent discipline here is: no
deployment of anything past Phase 1 without an explicit decision that a
real consumer needs it, and no server configuration that can point at
this repository instead of a tagged clean-room export, checked
explicitly before any deployment, not assumed.

## Open next step

Decide whether Phase 1 (static generated files in the export) alone
satisfies the actual need before committing to scoping Phase 2 at all —
the honest default, per the calibration above, is that it probably does.
