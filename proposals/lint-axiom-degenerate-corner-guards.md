# Proposal: Lint Every Axiom Signature for a Missing Degenerate-Corner Guard

**Status:** Proposed 2026-08-28.

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
