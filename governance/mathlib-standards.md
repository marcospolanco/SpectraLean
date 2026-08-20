# Mathlib Standards — Quality and Correctness at Scale

Scaffold intends its load-bearing spectral graph theory to be adoptable into
[Mathlib](https://github.com/leanprover-community/mathlib4) with minimal
friction. That means holding ourselves to Mathlib's standards, not merely our
own. This document articulates how Mathlib keeps a monorepo of over a million
lines of mathematics correct, consistent, and reviewable as it grows — and
what Scaffold adopts from each mechanism. The mechanism in one sentence: the
kernel, the human reviewers, and the CI machinery each check what the others
cannot, and each layer is configured so its checks cannot be quietly skipped.

## Provenance and method

Everything below was read directly from mathlib4 `master` via the GitHub API
on 2026-08-19 — not from secondary summaries or memory. Artifacts consulted:

- `bors.toml` — merge-queue, delegation, and label configuration
- `lakefile.lean` — linter and Lean-option configuration
- `.github/workflows/` — full directory listing (54 workflow files), with
  `build_template.yml` (the reusable build/test/lint pipeline) and
  `daily.yml` (scheduled expensive checks) read in detail
- `docs/workflows.md` — Mathlib's own catalogue of those workflows
- `Mathlib/Tactic/Linter/` — directory listing: 30 linter files plus the
  `TextBased/` subdirectory
- `.pre-commit-config.yaml`
- the live community guides on [values](https://leanprover-community.github.io/contribute/values.html),
  [PR review](https://leanprover-community.github.io/contribute/pr-review.html),
  [code style](https://leanprover-community.github.io/contribute/style.html),
  [naming](https://leanprover-community.github.io/contribute/naming.html), and
  [documentation](https://leanprover-community.github.io/contribute/doc.html)

This document is itself covered by `scripts/check_markdown_links.py` (it
passed at authoring time, and every local path it references was confirmed to
exist). Mathlib moves fast: re-verify specifics against `master` before
relying on mechanical details such as workflow names or the exact linter set.

## 1. The trust model: the kernel checks proofs, humans check statements

Lean's kernel guarantees that every theorem in Mathlib follows from its
premises. Mathlib's quality culture exists because that guarantee does *not*
extend to the two things the kernel cannot see:

- **That a definition defines what was intended.** As the review guide puts
  it: Lean confirms you defined *something*, not that you defined what you
  meant. Definitions receive the heaviest scrutiny of anything in review, and
  every new definition is expected to ship with *characterizing lemmas* — an
  API that both proves the definition is correct and makes it ergonomic.
- **That a theorem statement is the theorem a mathematician would recognize.**
  Both domain mathematicians and Lean experts review, so users can trust that
  statements match mathematical expectations.

Beyond the kernel, Mathlib holds a hard line on trusted primitives:

- **Zero `sorry` in Mathlib proper.** CI treats warnings as failures
  (`lake --iofail`), so a `sorry` cannot reach `master`. The maintainers'
  slogan: *"zero sorries is a starting point, not an end point"* — the
  surrounding API quality matters as much as the absence of holes.
- **No new axioms.** The only axioms in Mathlib are the three standard ones
  (`propext`, `Classical.choice`, `Quot.sound`); `axiom` declarations and
  `native_decide` do not ship.
- **Independent re-verification.** A daily job runs
  `lake env leanchecker --fresh Mathlib` to re-check built artifacts against
  sources, so a compromised or stale build cache cannot silently diverge from
  the proof text.

**Scaffold's position.** Scaffold is axiom-transparent by design: public
assumptions are explicit, cited axioms, never hidden behind `sorry`
(`governance/CONTRIBUTING.md`). This is the Mathlib-compatible posture — our
axioms are precisely the "sorries" Mathlib's slogan refers to, each one a
named, citation-backed target for future proof discharge. Anything submitted
to Mathlib must have those obligations actually discharged; an axiom with a
citation is a proposal in Mathlib's world, not a theorem. Our QA lemmas
(`Scaffold/QA/`) play the role of Mathlib's characterizing lemmas: witnesses
that would fail if the definition or interface were wrong.

## 2. Review: the human layer

Mathlib runs roughly 2,600 open PRs at a time, and every one of them is
reviewed before merge. The structure that makes this scale:

- **Merge authority is separated from review authority.** Only maintainers
  merge; *everyone* is encouraged to review. A recognized reviewer tier can
  approve with `maintainer merge` for faster queueing, and a track record of
  good reviews is the path into both tiers. Partial reviews are explicitly
  valued.
- **The review checklist is ordered easiest-to-hardest:** style →
  documentation → file placement → structural improvements → library
  integration. Library integration is the hardest and most valuable: sensible
  API (attributes, rewrite lemmas, constructors), sufficient generality for
  future needs, and alignment with Mathlib's design idioms (bundled morphisms
  with `FunLike`, subobjects with `SetLike`).
- **Delegation is earned and scoped.** Trusted contributors can be delegated
  merge authority for author-follow-up work, but `bors.toml` restricts
  delegation to library paths (`Mathlib/**`, `Archive/**`, …) with a two-week
  expiry — never to CI, scripts, or toolchain files.
- **Proofs are for humans.** Proofs of 50+ lines are expected to sketch the
  argument's shape, via interspersed comments. Code golf is welcome only when
  it does not hurt readability; shorter is not itself a goal.
- **Performance is reviewed as a correctness-adjacent property.** Raising
  heartbeat limits with `set_option` is a smell that the proof needs
  restructuring; changes to classes, instances, simp lemmas, imports, or
  `def`→`abbrev` conversions are benchmarked (`!bench`) before merge.
- **Typeclass diamonds are treated as defects.** New data-bearing instances
  are examined specifically for non-defeq instance diamonds.

**Scaffold's position.** `governance/MAINTAINERS.md` and
`governance/ADVERSARIAL_REVIEW.md` already encode this separation. The
Mathlib habit to import: review definitions hardest, demand characterizing
lemmas for every new definition, and treat `set_option`-based workarounds as
debt to retire, not fixes.

## 3. CI: the machine layer

Nothing reaches `master` except through the [bors](https://bors.tech) merge
queue. Every PR — and every batch of up to 16 PRs squashed together — must
pass the same gate on a `staging` branch before promotion. The required
checks are the full build, test-and-lint, style lint, and post-build steps,
with a two-hour timeout. PRs labeled `WIP`, `merge-conflict`, or
`blocked-by-other-PR` are blocked from the queue automatically.

Inside CI, three principles do the work:

1. **Warnings are failures.** Tests run with `lake --iofail`, so *any*
   diagnostic — a `sorry`, a linter hit, a missing docstring — fails the run.
   There is no yellow.
2. **The lint wall is enforced from `lakefile.lean`, not convention.** The
   package build enables `linter.mathlibStandardSet` plus explicit linters:
   file headers, `checkInitImports` (the import hierarchy may not be
   violated), all-scripts-documented, Python style for scripts, and a
   1,500-line file-size linter. `autoImplicit` is off globally. The linter
   library itself (`Mathlib/Tactic/Linter/`) covers docstrings, whitespace,
   multi-goal proofs, deprecated syntax, unused tactics, minimal imports,
   directory dependencies, overlapping instances, and more. Style lint runs
   with a 10-minute timeout — lint CI is not optional infrastructure.
3. **Suppressions are tracked debt, not permissions.** Lint exceptions live
   in `nolints.json`, which a weekly scheduled job *regenerates from scratch*
   and merges via an automated PR. A suppression that no longer applies
   disappears; the list can never silently grow stale.

Around the core: `pre-commit` enforces trailing-whitespace, final-newline,
and LF endings; PR titles are validated against conventions; commits marked
`transient:`/`x:` are verified; umbrella files (`Mathlib.lean`, …) are checked
to be up to date; even noisy stdout in the build fails the run.

**Scaffold's position.** We already run `lint_axioms.py`,
`check_citations.py`, `generate_qa_scoreboard.py`, and
`check_markdown_links.py` as our lint wall. The Mathlib standards to adopt:
warnings are failures (no partial credit in QA), suppressions are enumerated
and re-earned, and the gate runs on every change to anything load-bearing —
docs included, since `check_markdown_links.py` already treats prose as
checked artifact.

## 4. Scheduled hygiene: the library pays its debts on a clock

Mathlib's most distinctive practice is that maintenance is automated on
schedules, so technical debt is repaid even when no one volunteers:

| Cadence | Mechanism | Effect |
|---|---|---|
| Hourly | dependency updates | `lake update` bot PR; failures alert Zulip |
| Daily | `leanchecker` | independent re-verification of artifacts |
| Daily/nightly | toolchain bump + `lean-pr-testing-*` branches | Mathlib is fixed-toolchain, but continuously probes the next Lean so breakage surfaces early, with regression reports |
| Weekly | `lake shake --fix` | redundant imports removed automatically |
| Weekly | `rm_set_option` | unnecessary `set_option` escapes pruned |
| Weekly | `nolints.json` regeneration | lint suppressions re-derived |
| Weekly | long-file, tech-debt, late-import reports | metrics posted publicly to Zulip |
| Monthly | deprecated-declaration removal | retired names actually deleted |

Downstream breakage is watched too: a `DownstreamTest` suite, a downstream
repository dashboard, and per-PR downstream checks mean "this breaks a
consumer" is discovered before merge, not after.

**Scaffold's position.** Our equivalent clocks are the QA scoreboard
regeneration and the proposal backlog's placeholder-retirement items
(`retire-*`, `repair-*` in `proposals/`). The Mathlib lesson: give every
class of debt a scheduled repayment mechanism, so cleanup does not depend on
memory or goodwill.

## 5. Style and naming: consistency as infrastructure

Mathlib treats naming and formatting as load-bearing infrastructure, because
at scale they are what make the library greppable, teachable, and automatable
(`simp` normal forms only work if lemma names and statements are
predictable).

**Naming is derived from the statement.** A lemma name describes the
conclusion, with hypotheses appended via `of` in order (`C_of_A_of_B`);
infix operations appear infix in the name (`neg_mul_neg`); common
abbreviations (`pos`, `nonneg`, `ne`) replace their expansions; structural
patterns are fixed (`_ext`/`ext_iff`, `_injective` vs `_inj`, `induction_on`
vs `recOn` with a documented motive-type rule). Terms of `Prop` are
`snake_case`; types and classes are `UpperCamelCase`; other terms are
`lowerCamelCase` (an embedded `UpperCamelCase` name drops to
`lowerCamelCase`); files are `UpperCamelCase`; spelling is American.

**Statements have canonical forms.** All argument types are written
explicitly, even when inferable — statements must read on GitHub as much as
in an IDE. Hypotheses are named arguments, not conjunctions. For types with
a bottom element: `x ≠ ⊥` in assumptions, `⊥ < x` in conclusions. `Type*`
rather than `Type _` (a performance issue). Equivalent forms are settled
once (`s.Nonempty`) and reused everywhere.

**Formatting is mechanical so review can be mathematical.** 100-column
lines; `by` never alone on a line; one tactic per line (short semicolon
sequences representing one idea excepted); flush-left `·` for new goals;
`fun x ↦ …` with `λ` banned; `$` banned in favor of `<|`; a documented
unicode allow-list. Mechanical rules are exactly the ones the linter can
hold, freeing human review for mathematical content.

**Definitions default opaque, with reason.** `semireducible` by default;
`abbrev` needs justification; `irreducible_def` needs documented profiling
evidence; needing extra `rfl`/`erw` is read as a missing-API signal. The
`to_additive`/`to_dual` generators are used instead of hand-writing parallel
statements.

**Scaffold's position.** `AGENTS.md` already requires "use Mathlib types and
conventions where practical." This section is the concrete content of that
rule for anything destined for upstream: check the naming table before
naming, state lemmas in canonical form with explicit types, and let
formatting be uniform enough to diff cleanly against Mathlib files.

## 6. Documentation is part of correctness

Every file opens with copyright, authors, and a module docstring in a fixed
section order — title, summary, Main definitions, Main statements, Notation,
Implementation notes, References, Tags. Every definition requires a
docstring (`docBlame` linter); theorem docstrings are expected whenever there
is mathematical content. Docstrings state *mathematical meaning* and are
explicitly permitted to "lie slightly about the implementation." Citations go
through a shared `references.bib`; curated cross-references (`@[wikidata]`,
`@[stacks]`) are exported by CI. The bar is stated plainly: Mathlib should be
usable by someone whose only prior language is LaTeX.

**Scaffold's position.** Our citation index (`index/sources/`, `index/map/`)
and `check_citations.py` already exceed Mathlib's citation practice in
structure. What to adopt wholesale: the module-docstring section order and
the docstring-as-mathematical-statement bar, so that extracting a Scaffold
file into Mathlib carries its documentation with it. Check
`docs/8_MATHLIB_COVERAGE_MAP.md` before writing any "Mathlib lacks X" claim
in a docstring or proposal.

## 7. Architecture: one library, quarantined exceptions

Mathlib is a monorepo with a single standard, and it protects that standard
by *quarantining* everything that cannot meet it into sibling trees with
their own umbrellas: `Archive` (formalizations at lower review strength),
`Counterexamples`, `Wanted`, and `MathlibTest` — while `Mathlib` proper
admits nothing below full standard. Nothing intermediate exists; there is no
"mostly trusted" Mathlib directory.

The import hierarchy is defended mechanically (`checkInitImports`,
directory-dependency linters), files are kept small enough to compile in
parallel and placed so the import tree stays wide (which also reduces memory
footprint), and a per-file cloud cache of build artifacts makes the
monorepo tractable for contributors — correctness discipline and build
logistics are designed together. Evolution is handled by an explicit
deprecation cycle: renamed or removed public declarations get `@[deprecated]`
with a date and a migration path; deletion follows after six months, executed
by the monthly cleanup job. There is no semantic versioning — `master` is the
version, and downstream projects are supported through migration aids and
breakage monitoring rather than frozen APIs.

**Scaffold's position.** The center-out policy is our version of the
quarantine principle: the SGT core meets full standard (no placeholders, no
unproven claims), and outer layers may not dilute it — inner defects exposed
by outer work are repaired first. Our placeholder-retirement program is our
deprecation cycle; give retirements dates, as Mathlib does, so the debt list
can only shrink.

## 8. Community, conduct, and AI

Discussion lives on Zulip, with every PR mirrored there and its state synced
back automatically; scope questions are settled *before* PRs ("is this
mathlib-shaped? ask in `#mathlib` first"), and style-only drive-by PRs are
discouraged to protect reviewer bandwidth. The AI policy is explicit and
worth adopting verbatim in spirit: AI-assisted code is allowed but must be
disclosed in the PR description with tools and manner of use; substantial
LLM-generated code carries a label; the author must fully understand and be
able to justify every line; and LLM-written comments to reviewers or on
Zulip are not allowed — "use your own words."

**Scaffold's position.** Operator-facing records (`docs/AGENT_ACTIVITY.md`,
`docs/EXECUTION_PLAN.md`) already make machine work disclose itself. The
Mathlib bar to adopt: no artifact leaves the repo that a human author cannot
fully understand and defend line-by-line.

## 9. Adoption summary

| Mathlib mechanism | Scaffold commitment |
|---|---|
| Kernel checks proofs; review checks statements | Definitions reviewed hardest; QA/characterizing lemmas mandatory for new definitions |
| Zero `sorry`; no new axioms | Axioms explicit, cited, and scheduled for discharge; QA never contains `sorry`/`admit` |
| Characterizing-lemma API for new definitions | QA lemmas in `Scaffold/QA/` exercising each axiom nontrivially |
| Warnings are failures (`--iofail`) | QA scripts fail on any placeholder, missing citation, or broken link |
| Lint wall configured in the build (`lakefile.lean`) | `lint_axioms.py` / `check_citations.py` / `check_markdown_links.py` / scoreboard generation on every change |
| Suppressions regenerated weekly (`nolints.json`) | Any lint exclusion is enumerated, justified, and re-earned |
| bors merge queue; squash; batch | No unreviewed merges to load-bearing modules |
| Scheduled debt repayment (shake, deprecation, `rm_set_option`) | Dated placeholder retirements; scoreboard only shrinks |
| Naming and statement canonical forms | Follow the naming table and statement style for anything upstream-bound |
| Module docstrings; docBlame; `references.bib` | Module docstring section order; docstrings state mathematical meaning; citation index maintained |
| Quarantine of sub-standard content (`Archive`, …) | Center-out policy: core at full standard, outer layers never dilute it |
| Downstream breakage monitoring | Mathlib-coverage map kept current before claiming gaps |
| AI disclosure and author understanding | Machine work disclosed; humans can defend every line |

## 10. Direct reuse under Apache 2.0: what we can take, not just imitate

Sections 1–9 are practices to imitate. This section is different: mathlib4 is
Apache 2.0 (`LICENSE`, root of the repo) and so is Scaffold
(`LICENSE:178`, "Copyright 2024 Scaffold Contributors"). Same license, same
terms — reuse is a licensing non-event, not a negotiation. mathlib4 ships no
separate `NOTICE` file (confirmed by listing the repo root via the GitHub API
on 2026-08-19: only `LICENSE` appears), so the only obligation copying
anything triggers is License §4(b): keep each copied file's own
copyright/author header intact, and mark any file we modify as modified.
Every mathlib4 source file already carries that header individually (e.g.
`Mathlib/Tactic/Linter/TextBased.lean` opens "Copyright (c) 2024 Michael
Rothgang... Authors: Michael Rothgang, Jon Eugster, Adomas Baliuka") — so
"preserve the header" is concrete, not aspirational.

Provenance for this section specifically: `.pre-commit-config.yaml`,
`lakefile.lean`, the `Mathlib/Tactic/Linter/` and `scripts/` directory
listings, and `Mathlib/Tactic/Linter/TextBased.lean`'s header were fetched
directly via `gh api repos/leanprover-community/mathlib4/contents/...` on
2026-08-19. Scaffold's own tree was checked the same day: no
`.pre-commit-config.yaml` exists yet, and no Scaffold file writes a bare
`import Mathlib` — every one of our ~19 importing files names a narrow
submodule (`Mathlib.Analysis.CStarAlgebra.Matrix`,
`Mathlib.LinearAlgebra.Matrix.Spectrum`, …). That last fact matters below.

### 10.1 Zero-copy: turn on mathlib's own linters from our `lakefile.lean`

mathlib4's `lakefile.lean` doesn't hand-write its linters into a script —
it turns them on as `leanOptions` on `lean_lib Mathlib`, via a
`mathlibOnlyLinters` array (`linter.mathlibStandardSet`,
`linter.style.header`, `linter.checkInitImports`,
`linter.allScriptsDocumented`, `linter.pythonStyle`,
`linter.style.longFile 1500`), each prefixed `weak` so the setting applies
to Mathlib's own build without forcing itself on downstream consumers.

Scaffold already `require`s mathlib4 v4.14.0, so the linter *code* —
`Mathlib/Tactic/Linter/` (30 files: `Style.lean`, `DocString.lean`,
`DocPrime.lean`, `UnusedTactic.lean`, `Multigoal.lean`,
`OverlappingInstances.lean`, `MinImports.lean`, `Whitespace.lean`,
`EmptyLine.lean`, `Header.lean`, and 20 more) — is already sitting in our
build closure. Turning individual ones on costs a `lakefile.lean` edit, not
a file copy.

The catch is the import-narrowness fact from the provenance note above: a
Lean option is only settable once its declaring module is in scope, and
Scaffold never imports the bare `Mathlib` umbrella that would pull every
linter module in transitively. Before wiring any of these into
`lean_lib Scaffold`'s `leanOptions`, confirm which option-declaring modules
are actually reachable from our narrow imports (or add one explicit
`import Mathlib.Tactic.Linter.Style` etc. somewhere on the closure, e.g.
from `Scaffold.lean`) — don't assume the option exists just because the
package does.

Start with the general-purpose, content-agnostic linters — `Style`
(bundles the `longLine`/`cdot`/`dollarSyntax`/`lambdaSyntax` checks already
named in §5), `DocString` (our own docBlame-equivalent gap, per §6),
`DocPrime`, `UnusedTactic`, `Multigoal`, `OverlappingInstances` (the
typeclass-diamond defect §2 already names), `MinImports`, `Whitespace`,
`EmptyLine`. Hold off on the full `linter.mathlibStandardSet` bundle and on
`checkInitImports`/`allScriptsDocumented`/`pythonStyle` specifically — those
three encode mathlib's *own* directory and scripts conventions, not a
generic Lean-style bar, and would need adaptation rather than a flip.
Linter option names are not a stable API; re-verify each one against
`master` at wiring time, per this document's own opening caveat.

### 10.2 Small, self-contained files: copy with attribution

- **`.pre-commit-config.yaml`** — 12 lines, three hooks
  (`trailing-whitespace`, `end-of-file-fixer`, `mixed-line-ending --fix=lf`),
  sourced from the separate `pre-commit/pre-commit-hooks` project rather
  than mathlib's own authored logic. Scaffold has no such file today
  (confirmed above) — add it near-verbatim; there is essentially nothing to
  attribute beyond the hook repo's own pin.
- **`scripts/lint-style.lean`** — rather than growing a fourth bespoke
  Python checker alongside `check_citations.py` / `lint_axioms.py` /
  `check_markdown_links.py`, write a thin Scaffold
  `scripts/lint_style.lean` that *imports and calls*
  `Mathlib.Tactic.Linter.TextBased` (already vendored, per §10.1) against
  our own `Scaffold/` tree. This is a call site, not a fork: it carries
  `TextBased.lean`'s own copyright header forward by reference rather than
  duplicating the header into a copy.
- **`scripts/noshake.json`** — mathlib's exceptions-file format for
  `lake shake` (unused-import removal, §4's weekly `lake shake --fix`).
  Nothing to literally copy — the content is mathlib's own import graph —
  but the file *format* is worth mirroring exactly if/when Scaffold starts
  running `lake shake` for its own import hygiene.

### 10.3 A concrete gap this review surfaced

Checking whether Scaffold's own lint wall already behaves like §3's
"warnings are failures" turned up that it doesn't. `.github/workflows/ci.yml`
runs both lint checks through `|| true`:

```yaml
- name: Check new axioms have citations
  run: ./scripts/check_citations.py || true
- name: Check index files are updated
  run: ./scripts/lint_axioms.py || true
```

A PR that fails citation checks or axiom-index checks still shows green —
the exact opposite of mathlib's `lake --iofail`. That `lint` job is also
gated `if: github.event_name == 'pull_request'`, so a direct push to `main`
skips it entirely; and neither `generate_qa_scoreboard.py` nor
`check_markdown_links.py` — both in `AGENTS.md`'s own required verification
list — run in CI at all today, only locally/manually.

**Proposal:** drop `|| true` from both lint steps so they can actually fail
the run; add `generate_qa_scoreboard.py` and `check_markdown_links.py` as
required CI steps alongside the existing two; and drop the
`pull_request`-only gate so pushes to `main` are checked the same way PRs
are. This is section 3's own principle, not yet applied to our own gate.

### 10.4 Adoption table (additive to §9)

| Item | mathlib artifact (verified 2026-08-19) | Scaffold action |
|---|---|---|
| Lint-as-config, not lint-as-script | `lakefile.lean`'s `mathlibOnlyLinters` / `weak.` prefix | Add targeted `leanOptions` to `lean_lib Scaffold`; pilot `Style`/`DocString`/`DocPrime`/`UnusedTactic`/`Multigoal`/`OverlappingInstances`/`MinImports` before any full bundle (§10.1) |
| Pre-commit hooks | `.pre-commit-config.yaml` | Copy near-verbatim; currently absent from Scaffold |
| Text-based style checks | `Mathlib.Tactic.Linter.TextBased` + `scripts/lint-style.lean` | New `scripts/lint_style.lean` that imports and calls it, not a rewrite |
| Import hygiene | `lake shake` + `scripts/noshake.json` | Adopt the exceptions-file format when Scaffold starts running `shake` |
| Warnings are failures, for real | `lake --iofail` | Remove `\|\| true` from `ci.yml`'s lint job; drop the PR-only gate; add the two `AGENTS.md`-required scripts missing from CI (§10.3) |

Any file or substantial excerpt taken from mathlib4 keeps its original
copyright/author header, per License §4(b); any Scaffold-side modification
to a copied file gets a note marking what changed. Configuration lifted
wholesale (option names, hook lists) isn't copyrightable expression in the
first place, but the attribution habit costs nothing and keeps the
provenance trail this document itself depends on.
