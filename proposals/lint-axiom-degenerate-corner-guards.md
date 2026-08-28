# Proposal: Lint Every Axiom Signature for a Missing Degenerate-Corner Guard

**Status:** DELIVERED 2026-08-28 (run `20260828T154318Z-run-1`) — the
check, its allowlist mechanism, the acceptance-bar fixtures, and the
ladder wiring; no Lean, no axioms, no QA declarations. First-run output
on the post-repair tree: exactly the two anticipated findings
(`perron_frobenius`, `primitive_power_tendsto`), both carrying
provisional allowlist entries whose Lean-confirmed verdicts are the
companion audit's job
(`audit-perron-frobenius-family-degenerate-corner.md`, the Active
table's Medium row). See the delivery record at the end of this file.

## The incident this responds to

Two of ten admitted axioms were found genuinely defective this week, both
via the same shape of gap: a `Fintype`/`Fin n`-indexed object or a
`Measure` argument in the axiom's signature with no accompanying
niceness hypothesis (`[Nonempty V]`, `[IsProbabilityMeasure μ]`) —

- `matrix_hoeffding`/`matrix_bernstein`/`matrix_azuma_hoeffding`: all
  three quantified over `Matrix V V` with no `Nonempty V`, and were
  genuinely **inconsistent** (`1 ≤ 0`) at `Fintype.card V = 0` — every
  hypothesis stayed satisfiable while the conclusion's `card V` prefactor
  collapsed to `0`. Repaired 2026-08-28 with an explicit `[Nonempty V]`
  guard.
- `hoeffding_lemma`: quantified over an arbitrary `Measure μ` with no
  `IsProbabilityMeasure` constraint, and no measurability hypothesis on
  its random variable either — exactly the two structural gaps that had
  already broken a sibling axiom in the same file (`subgaussian_tail_bound`,
  repaired 2026-08-22). Repaired 2026-08-28.

Both gaps were *visible directly in the axiom's own signature* before
anyone built a spike or a refutation fixture — a `Matrix V V` argument
with no `Nonempty V` anywhere in the hypothesis list, or a `Measure μ`
with no `IsProbabilityMeasure μ` anywhere, is checkable by reading the
`axiom` declaration's type alone, with no proof effort at all. Neither
gap was caught until someone happened to build an adversarial fixture
targeting exactly that corner — once, during an unrelated consumer's
mandated Step 0, and once during a retroactive audit proposal written
because of a six-day-old unaddressed warning. `docs/2_ARCHITECTURE.md`
§5's admission policy now names this hazard class explicitly (added
2026-08-28), but a written policy is exactly the kind of thing this
project's own history shows gets missed under delivery pressure — see
`scripts/generate_scaffold_map_svg.py`'s docstring instruction to
"update both by hand," ignored for four days until an operator caught it.

## The ask

A mechanical check — most naturally a new function in `scripts/lint_axioms.py`
(already "lint axiom declarations for consistency"), not a new top-level
script — that, for every `axiom` declaration under `Scaffold/Mathlib`:

1. Parses the declaration's full signature (binders across multiple lines,
   the pinned Lean 4 grammar for `axiom name (args) : conclusion`).
2. Flags it if any binder's type mentions a `Fintype`/`DecidableEq`-carrying
   type variable used as a matrix/vector index (`Matrix V V _`, `V → _`,
   `Fin n → _`) **and no binder anywhere in the same declaration is a
   `Nonempty` instance or hypothesis over that same variable** (directly,
   or transitively through a hypothesis like `∃ i j, ...` that forces
   nonemptiness — see Non-goals on how far to chase this).
3. Flags it if any binder's type mentions `Measure` **and no binder is
   `IsProbabilityMeasure`, `IsFiniteMeasure`, or an explicit total-mass
   equation** on that same measure.
4. Prints each finding as `file:line: axiom NAME has a <kind> argument
   with no visible <guard> — confirm the degenerate corner is either
   guarded or genuinely harmless (hypothesis-unsatisfiable) and record
   which` — a prompt to look, not a claim the axiom is wrong. Exit
   nonzero on any finding without a matching entry in a small allowlist
   (see below).

This is a **linter, not a theorem prover.** It cannot determine whether a
flagged axiom is actually broken — `perron_frobenius` has no `Nonempty V`
either, but its own docstring already argues the corner is harmless (the
`hex : ∃ i j, 0 < A i j` hypothesis is unsatisfiable on an empty type, so
the axiom can never be instantiated there at all — a structurally
different, safe outcome from the matrix trio's, where every hypothesis
stayed satisfiable). The check's job is to force that argument to be
made and recorded, not to make it automatically.

**Allowlist, not silence.** An axiom that's flagged and found safe (like
the anticipated `perron_frobenius` outcome above, pending its own audit
— see `proposals/audit-perron-frobenius-family-degenerate-corner.md`)
gets a one-line allowlist entry naming *why*, checked into the script or
a sibling data file, not a silent pass. A flagged axiom with no allowlist
entry is exactly the state `matrix_hoeffding` and `hoeffding_lemma` were
in for weeks — the point of this tool is that state should be loud, not
quiet.

## Where this plugs in

Same ladder as `check_build_completeness.py` and
`check_scaffold_map_freshness.py`: `AGENTS.md` § Verification,
`scripts/opencode-pursue`'s `verify_for_commit`, `scripts/README.md`,
`docs/2_ARCHITECTURE.md` §10, `docs/AGENT_ACTIVITY.md`'s format block.
Also directly relevant to §5 (axiom admission policy, this document
just amended) — a **new** axiom's own admission should run this check
before it lands, not just at the next full-repo lint pass, so the
allowlist decision is made once, deliberately, at admission time.

## Acceptance bar

- Runs on the current tree and reports the historical incidents
  correctly: reconstruct the pre-repair `matrix_hoeffding` signature (no
  `[Nonempty V]`) and confirm it's flagged; reconstruct pre-repair
  `hoeffding_lemma` (no `IsProbabilityMeasure`, no measurability
  hypothesis) and confirm it's flagged.
- Running on the current (post-repair) tree: the three matrix axioms and
  `hoeffding_lemma` no longer flag (their guards are now present); the
  remaining axioms either don't trigger the pattern at all, or are
  flagged and carry an allowlist entry recording the reasoning (this
  proposal does not do that reasoning — see
  `audit-perron-frobenius-family-degenerate-corner.md` for the two
  candidates already known to trigger it, `perron_frobenius` and
  `primitive_power_tendsto`).
- False positives are expected and acceptable at the edges (the parser
  does not need to fully understand Lean's elaborator); false silence —
  a real missing-guard axiom the check doesn't flag because the pattern
  match missed its exact phrasing — is the failure mode to weight
  against, so prefer over-flagging with an easy allowlist entry over
  under-flagging.
- No Lean, no axioms, no QA declarations — this proposal's entire
  deliverable is the check, its allowlist mechanism, the ladder wiring,
  and documentation.

## Non-goals

- **Not a general axiom-soundness prover.** This only checks for the
  textual *absence* of a guard, not whether a present guard is the
  *right* one, or whether some other hazard class from
  `docs/2_ARCHITECTURE.md` §5 (a wrong constant, a strictness mismatch)
  is present — those need the kind of adversarial-fixture Step 0 this
  week's two repairs actually ran, which this linter cannot replace.
- **Not chasing transitive nonemptiness proofs.** If nonemptiness is
  implied by some other hypothesis in a way the parser can't see
  syntactically (e.g. an existential over the index type, as in
  `perron_frobenius`'s `hex`), the check should flag it anyway and let
  the allowlist entry record the argument — attempting to formally
  verify "this existential implies `Nonempty`" inside a linter is scope
  creep this proposal explicitly declines.
- **Not retroactively auditing the axioms it flags.** That is
  `audit-perron-frobenius-family-degenerate-corner.md`'s job, proposed
  separately. This proposal delivers the tool; the allowlist entries for
  currently-existing axioms are a follow-on once that audit's verdicts
  land, not blocking this proposal's own delivery (a fresh check that
  flags everything with no allowlist yet is still strictly more honest
  than no check at all, and is expected as this proposal's own
  first-run output).

## Delivery record (2026-08-28, run `20260828T154318Z-run-1`)

**The check.** `scripts/lint_axioms.py` gained
`check_degenerate_corner_guards(root='.')`, folded into `main()` so
every existing ladder invocation of `lint_axioms.py` runs it with no
new command to remember. Two finding kinds, exactly per the ask:

- `index-type-guard`: a type variable bound as `Type`/`Type*`/`Sort`
  that carries a `Fintype` instance, used in the effective signature as
  `Matrix V …`, a vector index `V →`, or a `Fintype.card V` prefactor,
  with no `Nonempty V` anywhere in the effective binders (instance or
  hypothesis form both recognized).
- `measure-guard`: a `Measure`-typed argument the declaration actually
  uses, with no `IsProbabilityMeasure`/`IsFiniteMeasure` instance or
  `m univ = 1`-style total-mass equation on that same measure.

Unallowlisted findings exit 1 with the mandated message shape
(`file:line: axiom NAME has a … — confirm the degenerate corner is
either guarded or genuinely harmless (hypothesis-unsatisfiable) and
record which`); allowlisted findings print as visible `Allowlisted:`
notes recording the reason, never silently.

**The signature model** (the parser approximates the elaborator, and
the approximations are recorded in the module docstring):

- Binders are parsed by bracket matching, not regex splitting, so
  multi-name groups (`{a v : ℝ}`) and anonymous instances
  (`[Nonempty V]`) work; `axiom` declarations span to the first blank
  line or next top-level command.
- `variable`/`variables` lines are tracked with namespace/section
  scoping — a variable inside a closed `namespace` dies at its `end`
  and cannot leak a guard past it (fenced below). This matters because
  six of the ten axioms carry their measure guard in a `variable`
  line, not in the declaration: Lean includes `{μ : Measure Ω}
  [IsProbabilityMeasure μ]` only when the declaration mentions `μ`, and
  the checker mirrors that name-mention inclusion (plus transitive
  inclusion through included binders' types, so an index type entering
  only through `variable {B : Matrix V V ℝ}` still triggers — probed).
- Identifiers are matched Unicode-aware: the first fixture run caught
  the scanner blind to Greek identifiers (`μ`, `Ω`, `ν`, `π`) under a
  Latin `[A-Za-z_]` pattern — the measure check could not see `μ` at
  all, i.e. exactly the false-silence failure mode the acceptance bar
  weights against, caught by the acceptance bar's own fixture before
  delivery.

**Scoping decision, recorded in the tool** (docstring): literal
sample-index binders `Fin n → _` over a visible `{n : ℕ}` are
deliberately not flagged — their degeneracy (`n = 0`) is named in the
signature itself, both incident repairs concerned abstract index types
whose emptiness the signature hides, and the proposal's acceptance bar
expects only the PF pair to flag post-repair. Extending the pattern
with the `Fin n` shape and its guard set (`0 < n`, `NeZero n`,
`Nonempty (Fin n)`) is a one-regex change with this note as the record
of the decision.

**The allowlist** (`ALLOWLIST` in the script): per-(axiom, kind) entries
recording why each accepted corner is safe. Two provisional entries
landed with the check — `perron_frobenius` (the `hex` witness argument)
and `primitive_power_tendsto` (the `hπsum` empty-sum argument), each
naming its reasoning as docstring-level and pointing at the companion
audit for the Lean-confirmed verdict; the audit's scope item 3 upgrades
them. Entries are load-bearing (removal re-flags — fenced) and are to
be *removed* when an axiom acquires a real guard, so the guard, not the
entry, is what silences the finding.

**Acceptance-bar fixtures** (`wip/axlint_fixtures.py`, gitignored
scratch; the list is preserved here):

1. Pre-repair `matrix_hoeffding` reconstructed verbatim from
   `a1e59ac~1` (no `[Nonempty V]`) → flagged, and nothing else in that
   file flags. ✔ (this is the fixture that exposed the Greek-identifier
   blindness on the sibling case)
2. Pre-repair `hoeffding_lemma` reconstructed verbatim from
   `a1e59ac~1` (variable block `{μ : Measure Ω}` with no probability
   instance anywhere) → flagged. ✔
3. Post-repair tree: the matrix trio and `hoeffding_lemma` do not flag
   (guards recognized — inline for the trio and `hoeffding_lemma`,
   variable-line for the other five measure axioms); exactly the PF
   pair allowlisted; exit 0. ✔
4. Guard-recognition fences: `[Nonempty W]` inline and `(hW : Nonempty
   W)` hypothesis both silence; `Matrix W W ℂ` (complex phrasing) and a
   `Fintype.card`-prefactor vector axiom with no guard both flag;
   `IsFiniteMeasure` and `m Set.univ = 1` guards recognized; an
   unguarded measure flags; a measure the declaration never mentions
   does not falsely trigger. ✔
5. Namespace-scope fence: `[Nonempty T]` inside a closed inner
   namespace must NOT silence an axiom after its `end` → still flags. ✔
6. Allowlist-expiry fence: removing `perron_frobenius`'s entry re-flags
   exactly it. ✔
7. Transitive-inclusion probe (`wip/axlint_probe.py`): an index type
   entering only through a variable binder's type
   (`variable {B : Matrix V V ℝ}`) still triggers. ✔

**Ladder wiring:** the check rides the existing
`python3 scripts/lint_axioms.py` invocation everywhere, and the five
documented ladder locations now name it — `AGENTS.md` § Verification,
`scripts/opencode-pursue`'s `verify_for_commit` (comment), and
`docs/AGENT_ACTIVITY.md`'s format block gained the check plus the new
admission-time rule (any entry reporting a new axiom admission must
record the check passing with the admission's allowlist decision);
`docs/2_ARCHITECTURE.md` §10 gained its paragraph and §5's hazard
checklist gained the mechanical-nudge sentence (run before an axiom
lands; settle the allowlist entry once, at admission time);
`scripts/README.md`'s row extended; `governance/CONTRIBUTING.md`'s
Axiom Addition checklist gained its line.

**Verification:** `python3 scripts/lint_axioms.py` exit 0 with exactly
the two `Allowlisted:` notes, deterministic across runs; the fixture
runner and transitive probe exit 0; `check_citations`,
`check_markdown_links` pass; scoreboard regeneration idempotent
(2785/10/0 unchanged — no Lean source touched, so no `lake build` was
run this run; the Lean tree's last verified state remains the prior
run's full build + 127/127 completeness); `check_scaffold_map_freshness`
exit 0 (mandatory — this delivery changes a proposal's status header;
the linter proposal is not a map station source, and the check
confirmed no drift). All ten axioms verified scanned at their correct
`file:line` positions.

**Residuals:** ~~the two allowlist entries are provisional by design;
upgrading them to Lean-confirmed verdicts (or repairs) is the companion
audit proposal's scope items 1–3, which is the Active table's next
actionable row.~~ **Resolved 2026-08-28, run `20260828T165900Z-run-1`:
the companion audit (`audit-perron-frobenius-family-degenerate-
corner.md`) confirmed both axioms safe by Lean-verified
unsatisfiability and upgraded both entries to cite the unconditional
QA proofs (`perron_frobenius_hex_unsat_card_zero_QA`,
`mass_one_unsat_card_zero_QA`); no entry remains provisional.** The
parser's elaborator approximation is documented,
not exact — over-flagging is the accepted direction, and the `Fin n`
scoping decision above is the known, recorded under-flag edge.
