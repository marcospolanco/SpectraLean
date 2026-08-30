# Proposal: Axiom Audit Tooling

**Status:** Proposed. Authorizes new Python scripts and ladder wiring only;
authorizes no axiom disposition changes, no adoption of quarantine
vocabulary, and no Lean proof work beyond what a survey needs to design the
checks.

**Provenance:** Split out of
[`axiom-stress-testing-and-quarantine.md`](axiom-stress-testing-and-quarantine.md)'s
§7 items 3–5, per an explicit operator decision (2026-08-30): adopt the
concrete tooling, not the full vocabulary/6-stage lifecycle that document
also proposes. This proposal is self-contained and does not require reading
or adopting that document to execute.

## Goal

Three independent, mechanizable checks, each catching a class of defect the
existing ladder (`lint_axioms.py`, `check_citations.py`,
`check_markdown_links.py`, `check_build_completeness.py`) does not:

1. **Negative-witness independence.** A refutation or fence QA declaration
   is only meaningful if its proof does not depend on the axiom it claims to
   refute — "a refutation cannot consume what it refutes" has been checked by
   hand in every delivery record so far (e.g. the Bernstein and
   `matrix_hoeffding` repairs' `#print axioms` passes), but no script
   verifies it automatically, so a future delivery could get this wrong
   without anyone noticing until an operator happens to check.
2. **Axiom replacement-path documentation.** Every public axiom should state,
   in its own docstring, what would need to be true for it to become a
   proved theorem (a source theorem to formalize, a Mathlib gap to fill, a
   named future engine). Several already do this in prose (e.g.
   `MasterBound.lean`'s "what is not here" section); this makes it a checked
   requirement rather than a convention some deliveries follow and others
   don't.
3. **Public-umbrella reachability against non-public modules.** No file
   under `wip/` (or any other explicitly non-public experiment directory)
   should be importable, directly or transitively, from any module reachable
   from the public umbrella. This is the concrete, vocabulary-free version of
   §7 item 5's "reject quarantined modules" — restated in terms of the
   `wip/` boundary that already exists, not a `quarantined` status that
   hasn't been adopted.

## Why now

All three are static checks, buildable independently of any policy decision
about axiom vocabulary — they enforce discipline the project already
practices by hand. The value is catching a slip before it ships, not
changing how axioms are admitted.

## Deliverable 1: negative-witness independence checker

**Step 0 survey (required before writing the check):** the repository has no
existing formal convention linking a QA declaration to the specific axiom it
refutes — naming is close but inconsistent (`old_matrix_hoeffding_refuted_uncentered_QA`,
`master_bound_fin0_unguarded_refuted_QA`, `old_bernstein_mgf_uncentered_refuted_QA`).
Survey the actual naming across `Scaffold/QA/**/*.lean` and decide, before
writing any checker code, between:

- (a) a naming-convention parser strict enough to extract the target axiom
  name from existing declaration names without false matches, with a
  documented allowlist for names the parser cannot resolve; or
- (b) a lightweight inline tag (e.g. a doc-comment line
  `-- @refutes: matrix_hoeffding`) added to each existing and future
  refutation/fence declaration, parsed exactly.

Prefer (b) if the survey finds (a) would need more than a small, auditable
set of naming exceptions — an unambiguous explicit tag is worth the one-line
annotation cost across roughly a dozen existing declarations.

**Check:** for every tagged/matched declaration, run (or reuse an existing)
`#print axioms`-equivalent dependency extraction and fail if the target
axiom's name appears in the dependency set.

**Acceptance:** the check runs against the current QA tree with zero
failures (every existing refutation is already axiom-independent by
convention); it is wired into the same five ladder locations as
`check_build_completeness.py`; a deliberately broken fixture (a refutation
made to depend on its own target axiom) is constructed once during
development and confirmed to fail the check, then reverted.

## Deliverable 2: axiom replacement-path documentation lint

**Check:** extend `scripts/lint_axioms.py` to require that every public
axiom's docstring contains a clearly labeled replacement-path note (a
sentence stating what would need to exist for the axiom to be retired — a
named theorem, a named engine, or an explicit "no known route" statement).
Survey the current ten... six... whatever the live count is at execution
time (`scripts/lint_axioms.py`'s own count) axioms' docstrings first: most
likely already contain this in prose (see `docs/2_ARCHITECTURE.md`'s
citation requirements); the check should recognize existing phrasing rather
than forcing a rewrite, and only fail axioms that are missing it entirely.

**Acceptance:** zero failures against the current axiom set without
rewriting any docstring that already states a replacement path in prose; a
per-axiom allowlist (matching the existing degenerate-corner-guard check's
pattern) for any axiom where "no known route yet" is the honest answer,
with a reason recorded.

## Deliverable 3: public-umbrella reachability check

**Check:** from the public umbrella's own import root, compute the
transitive import closure and fail if any module under `wip/` (or another
directory the repository already treats as non-public — confirm the exact
list from `docs/2_ARCHITECTURE.md` or `AGENTS.md` during Step 0) appears in
it. This is a straightforward Lean-import graph walk, no new vocabulary
needed.

**Acceptance:** the check passes against the current tree (no known
`wip/` leakage today — confirm this during Step 0 rather than assuming it);
wired into the same five ladder locations; a deliberately broken fixture (a
public module importing a `wip/` file) constructed once, confirmed to fail,
then reverted.

## Acceptance criteria (all three)

- No new axiom, `sorry`, or `admit` is introduced.
- Each check is a standalone script under `scripts/`, wired into the ladder
  at the same five locations `check_build_completeness.py` uses.
- Each check passes against the current repository state with zero
  unexplained failures — any allowlisted exception is recorded with a
  reason, not silently passed.
- `lake build`, `check_build_completeness.py`, `lint_axioms.py`,
  `check_citations.py`, `check_markdown_links.py`, and the map-freshness
  check all still pass after wiring.
- `docs/2_ARCHITECTURE.md`'s axiom admission policy (§5) gains a short
  cross-reference to the two new checks (independence + replacement-path),
  matching how the degenerate-corner guard check is already referenced
  there.
- The records ladder (`AGENT_ACTIVITY.md`, `EXECUTION_PLAN.md`, this
  proposal's own Delivered-table entry, README/radar/scoreboard/map stamps
  if QA count changes) is completed in the same delivery, not left for a
  follow-up run — see `docs/arch/commit-steward-protocol.md`'s
  records-gap discussion for why a partial delivery costs more to close
  than to avoid.

## Deferred / out of scope

- Adopting the `candidate`/`quarantined` disposition vocabulary from
  `axiom-stress-testing-and-quarantine.md` — explicitly not part of this
  decision.
- A promotion checklist for WIP experiments (§7 item 7 of the parent
  document) — not selected by the operator; a separate proposal if wanted
  later.
- Autonomous run reports recording per-axiom disposition (§7 item 6) — same,
  not selected here.

Each deliverable above is independently shippable; they do not need to land
in the same run or the same order. A single run may complete all three if
scope permits, or split them across runs, tracking partial progress in this
proposal's own status line rather than in a separate document.
