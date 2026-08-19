# Adversarial Review

This document defines a standing audit methodology distinct from both the
automated hygiene scripts (`scripts/lint_axioms.py`,
`scripts/check_citations.py`, `scripts/check_markdown_links.py`,
`scripts/generate_qa_scoreboard.py`, and `lake build` itself) and the
lightweight PR review in [Contributing](CONTRIBUTING.md#review-process).
Those check that things compile, that citations exist, and that a change
follows convention. This document is for a different question: **are the
proofs and QA actually load-bearing, or do they only look like it?**

Originally drafted 2026-08-19 as a standalone review plan, absorbed here
2026-08-19 after a pilot run (see "Worked pilot" below) confirmed the
approach surfaces real findings quickly, not just in principle. Extended
2026-08-19 with Phase 6, once external exposure (Palomar submission,
`proposals/palomar-submission.md`; eventually the clean-room export) went
from hypothetical to concretely planned — Phases 1–5 ask "is this proof
actually sound," which is necessary but not sufficient once someone
outside this project starts reading, citing, or pinning it.

## Why this exists

Formal Lean libraries built through iterative or autonomous workflows
rarely fail as broken syntax. "Fake and weak work" hides as:

1. mathematically false or underspecified axioms that permit
   contradictory conclusions;
2. vacuous or tautological theorems, true only because of Lean's
   totalization fallbacks (`x / 0 = 0`, `Classical.choice` defaults) or a
   hypothesis set that is secretly `False`;
3. paper-tiger QA that tests symmetric coincidences on small fixtures
   (`K₂`, `K₃`) without exercising real failure modes or negative
   witnesses;
4. semantic or notation drift between cited literature and the formal
   Lean statement; and
5. ghost dependencies and roadmap inflation in proposal files.

This is not hypothetical for this repository. The pre-repair
`woodbury_identity` and `cheeger_lower_bound` both compiled while being
mathematically false (§9 of `docs/2_ARCHITECTURE.md`'s upstream-
replacement lifecycle exists partly because of the first). The
`spectral-graph-sparsification.md` proposal cited
`matrix_chernoff_upper_lower`, a theorem that does not exist anywhere in
this repository, discovered only by grepping for it directly rather than
trusting the citation. Every phase below is aimed at catching one of
these classes before it ships, not after.

## Relationship to the standing review dimensions

`docs/2_ARCHITECTURE.md` §7 already names five review dimensions
(Definitions, Statement shape, API design, Mathlib compatibility,
Documentation). This methodology operationalizes them with concrete,
runnable procedures, and adds two axes the existing five do not cover:

| Existing dimension | Extended by |
| --- | --- |
| Definitions | Phase 1 (axiom falsification), Phase 2's junk-domain injection |
| Statement shape | Phase 2's hypothesis-dropping and mutation testing |
| API design | Phase 5's dead-code / load-bearing classification |
| Mathlib compatibility | (unchanged — not this document's focus) |
| Documentation | Phase 4 (citation fidelity) |
| *(not covered)* | Phase 3 — whether QA is actually load-bearing, not just present |
| *(not covered)* | Phase 5's ghost-dependency check — whether the roadmap matches the code |
| *(not covered)* | Phase 6 — whether the project survives contact with a reader who has no context on it, and whether what gets pinned externally stays pinnable |

## The five phases

### Phase 1: Axiom falsification and trust-boundary stress-testing

- **Extremal fixture counter-example search.** Instantiate each admitted
  axiom against corner cases: one-vertex graphs, disconnected graphs,
  bipartite graphs, edgeless graphs, singular/degenerate matrices, zero
  variance, zero spectral gap. Attempt to derive a numerical contradiction
  (`1 ≤ 0`) from the axiom on an extremal instance without extra
  preconditions.
- **Hypothesis completeness and inconsistency audit.** Check every axiom
  for missing preconditions (symmetry, nonnegativity, strict positivity,
  dimension guards, invertibility, measurability), and check whether the
  hypothesis set is internally consistent — `H₁ ∧ H₂ → False` would make
  every downstream derivation vacuously valid.
- **Kernel and foundational leak check.** Run `#print axioms <decl>` on
  supposedly hard-crust theorems to confirm they depend only on
  `propext`, `Classical.choice`, `Quot.sound`, and explicitly declared
  trust boundaries — never a silent `sorry` or an axiom that should have
  been visible elsewhere.

### Phase 2: Definition degradation and junk-value exploitation

Lean functions are totalized; a partial operation on out-of-domain input
gets a default fallback (typically `0` or an arbitrary choice).

- **Junk-domain injection.** Probe core objects — `effectiveResistance`,
  `flowEnergy`, `leverageScore`, `fiedlerPartition` — on invalid inputs
  (disconnected vertices, zero conductances, `u = v`, zero-volume sets).
  Check whether any public theorem accidentally proves a statement about
  the fallback value rather than the mathematical entity.
- **Hypothesis dropping (soundness probe), with a correction.** The
  original version of this check was: delete one hypothesis from a core
  theorem and see if Lean still accepts the *same* proof term. **This
  catches only literally-unused hypotheses, not redundant-but-used
  ones** — the pilot run below found a real instance the naive version
  would have missed. Run both variants: (a) delete-and-recompile, which
  flags hypotheses the current proof never touches; and (b) attempt the
  goal using only the *other* hypotheses plus already-proved lemmas
  elsewhere in the file, which flags hypotheses that are true but
  logically implied by the rest of the signature.
- **Mutation testing.** Mutate constant factors (`1/2 → 1`, `n − 1 → n`,
  `≤ → ≥`, `δ → −δ`, `e_u − e_v → e_v − e_u`) in core definitions and
  statements. If no QA lemma fails to elaborate or type-check afterward,
  that definition is untested — sitting inertly beside the codebase
  rather than being exercised by it.

### Phase 3: QA suite deconstruction (hunting paper-tiger tests)

A high QA count (`docs/5_QA_SCOREBOARD.md`) should be treated with
skepticism until verified load-bearing.

- **Symmetry and small-fixture coincidence checks, with a correction.**
  On `K₂`, quantities like volume, degree, eigenvalue, and diameter often
  coincide, masking a missing normalization constant or index offset.
  **Do not search for fixture size by grepping literal `Fin n` tokens** —
  the pilot run below found this produces false positives when a fixture
  is defined once and referenced by name elsewhere (`Fin.sum_univ_three`
  fired in a file a literal-token search reported as `Fin 2`-only).
  Check what sizes are actually *exercised* — trace shared fixture
  definitions, don't pattern-match their call sites.
- **Tautological and self-referential QA.** Search for QA lemmas that
  prove a claim by rewriting with the definition itself rather than
  comparing against an independently computed ground truth. Audit
  whether any QA lemma asserts a bound that is trivially true at the
  value it evaluates to (`0 ≤ X` when `X` computes to `0`).
- **Negative-witness completeness.** Check whether each QA file contains
  explicit negative witnesses (refuted false bounds, reverse
  inequalities, disconnected/asymmetric fixtures). A module with only
  positive confirmations gets a refutation test constructed and run
  against the counter-claim before being accepted.

### Phase 4: Literature fidelity and citation gap audit

`scripts/check_citations.py` checks only that the literal string
`Source:` appears in an axiom's doc comment — **zero semantic
verification that the math matches the source.** This is the least
automated, highest-value phase; see "Operating modes" below for why it
cannot run the same way as the other four.

- **Theorem-to-source line-by-line reconciliation.** Cross-examine every
  public axiom against its cited paper or textbook: which matrix/operator
  norm the source uses (spectral, Frobenius, entrywise max); which
  Laplacian normalization convention (`D − A`, `I − D^{-1/2}AD^{-1/2}`,
  `D^{-1}L`); whether constants and multiplicities are exact (`2φ` vs.
  `√(2φ)` vs. `φ²/2`; single-pair vs. two-cluster Davis–Kahan).
- **Adapter and bridge representation integrity.** Inspect the impedance
  match between `SimpleGraph` and `Matrix V V ℝ` in
  `Scaffold/Mathlib/GraphTheory/SimpleGraphAdapter.lean`. Check whether
  self-loops, multi-edges, or directed edges create a silent semantic
  discrepancy across the adapter.

### Phase 5: Proposal and roadmap reality check (anti-vaporware)

- **Ghost-dependency and "delivered" verification.** Cross-check every
  proposal in `proposals/README.md` and `docs/EXECUTION_PLAN.md` against
  actual Lean code. Grep for references to declarations that do not
  exist — the precedent is exactly the `matrix_chernoff_upper_lower`
  discovery cited above.
- **Dead code and "height without weight" audit.** Identify modules or
  lemmas with zero downstream consumers from `Scaffold.lean` or
  `Scaffold/Derived/`. Classify every declaration as **load-bearing**
  (breaks a consumer if changed), **connective** (a usable adapter), or
  **inert crust** (added only for declaration counts).

### Phase 6: Public-exposure readiness

Phases 1–5 verify the repository is internally sound. None of them ask
whether it *survives being read by someone with no context on it* — a
different failure mode, and the one Palomar's own founding motivation
names directly: "unvetted claims about machine-assisted mathematical
breakthroughs... with poor vetting, insufficient transparency, and
inadequate context." This phase exists so that this project does not
become one of the claims that motivation is describing.

- **Cold-reader messaging audit.** Read every public-facing claim
  (`README.md`, module docstrings, and eventually `formalization.yaml`)
  as someone with zero context on this repository's internal conventions
  would — not as someone who already knows "proved" means "checked
  `#print axioms` shows only the three standard ones." For every
  declarative "X is proved" claim in public prose, verify mechanically:
  `#print axioms` on the specific named theorem, not the module it lives
  in. This turns `docs/traction-plan.md`'s Communication Rules ("never
  market an axiom-backed result as foundationally formalized") from a
  stated rule into a runnable check, mirroring exactly the discipline
  that catches false axioms in Phase 1 — applied to marketing prose
  instead of Lean statements.
- **Pinned-revision integrity.** Once any external party pins a commit —
  a Palomar entry, a downstream `require scaffold from git @ <sha>` — that
  commit must remain buildable and its cited declarations must never be
  silently renamed out from under it. Before any public touchpoint:
  confirm `main`'s history has never been force-pushed or rewritten
  (`git reflog`, checked for `reset`/`rebase`/force-push markers), and
  treat any commit that gets externally cited as permanent — never
  garbage-collected, never the target of a history rewrite, even in
  service of an otherwise-legitimate cleanup.
- **API-stability discipline for post-exposure changes.** Today, fixing
  a finding like the P4 `hconnB` redundancy is free — nothing external
  depends on the signature. Once a theorem is cited from outside this
  repository, the same fix becomes a breaking change for whoever pinned
  it. Palomar entries are pinned to one commit forever by Palomar's own
  design, so they are not at risk from later Scaffold changes — the real
  exposure is anyone using the `<verified-revision>` `require` pattern
  in `README.md`'s "Intended consumption" section and later advancing
  their pin. Before any tagged release: decide and document a
  deprecation-window policy for public theorem signatures, the same
  discipline `docs/2_ARCHITECTURE.md` §9 already applies to axioms,
  extended to cover renamed or restated *proved* declarations once they
  have external citers, not just axioms.
- **Disclosure-quality audit, Palomar-specific.** Any drafted
  `formalization.yaml` gets checked against Palomar's actual stated
  requirements (author/AI-role disclosure, source citations, fidelity
  gaps) with the same rigor Phase 4 applies to axiom citations — a
  `formalization.yaml` that undersells autonomous-agent authorship as
  "manual," or overstates review that did not happen, is exactly the
  "insufficient transparency" failure Palomar exists to catch, and
  catching it before submission is this project's responsibility, not
  something to leave for Palomar's own LLM reviewer to find.
- **Pinned-dependency sanity.** Public consumers inherit whatever Mathlib
  revision Scaffold pins. Before a public touchpoint, confirm (light
  spot-check, not exhaustive) that no Scaffold public theorem transitively
  depends on a pinned-Mathlib declaration later found broken or retracted
  upstream — the same re-survey discipline
  `docs/8_MATHLIB_COVERAGE_MAP.md` already applies to itself, extended to
  cover "did the ground move under something we're about to expose,"
  not just "is the map current."

**Explicitly out of scope, and why:** adversarial input handling
(injection, malformed data, resource exhaustion) — Scaffold is a proof
library, not a service; it has no runtime attack surface in the sense
those checks target. Noted here so the omission reads as considered, not
overlooked.

## Severity tiers and routing

| Severity | Definition | Example | Routes to |
| :--- | :--- | :--- | :--- |
| **P0: Critical soundness bug** | False axiom, inconsistent hypotheses, or a proven numerical contradiction | Axiom refutable on `K₂`; missing invertibility hypothesis | Emergency removal per `docs/2_ARCHITECTURE.md` §9 — do not wait for the deprecation window |
| **P1: Vacuous / degenerate proof** | True only because of a junk default, unconstrained choice, or a redundant `False` hypothesis | Bound evaluates to `0 ≤ 0` on the junk domain; proved without a hypothesis the statement claims to need | Restate and re-prove; treat as a correctness bug, not a style note |
| **P2: Inert / paper-tiger QA** | Tests that pass by small-fixture coincidence, tautology, or a missing negative witness | QA passes on `K₂` with a missing factor of 2; zero counter-examples in the file | Add real QA before trusting the theorem it guards |
| **P3: Documentation / citation drift** | Lean statement diverges from the cited source without explanation, or a proposal cites a phantom declaration | Cited page/theorem mismatch; a proposal names a lemma that was never written | Fix the citation or the statement; if the gap is load-bearing, treat as P1 |
| **P4: Hypothesis stronger than necessary** *(added 2026-08-19, from the pilot below — did not fit the original four tiers)* | A hypothesis is true and used by the current proof, but is provably redundant given the theorem's other hypotheses plus already-proved lemmas elsewhere in the repository | `effectiveResistance_le_of_le`'s `hconnB` — see "Worked pilot" | Not urgent; a real API-cleanup item, tracked with the proposal or module it belongs to, not an emergency |
| **P5: Public-exposure risk** *(added 2026-08-19, Phase 6)* | A public-facing claim overstates what is proved, a rewritten/rebased history invalidates an external pin, or a disclosure document (`formalization.yaml`) understates automation or overstates review | A README line saying "proved" for something with an admitted-axiom dependency; a force-pushed `main` after a commit was cited elsewhere | Blocks the specific public touchpoint (submission, tagged release, export) until fixed — urgent relative to that touchpoint, not relative to the whole repository the way P0 is |

## Operating modes: what can run autonomously, what needs a human

Phases 1, 2, 3, and 5 are mechanical — repo access and `lake env lean` are
sufficient, and an autonomous `scripts/opencode-pursue` run (or an agent
session with repo tools) can execute them directly.

**Phase 4 is different and should not be scheduled the same way.**
Reconciling a Lean statement against its cited paper's actual norm
convention, constant, or hypothesis set requires reading the source —
something a sandboxed autonomous Lean-work run has no access to. Phase 4
needs either a human maintainer with the cited text in hand, or an
assisted session with real literature access (e.g., a `WebSearch`-capable
session), run as its own deliberate pass — not folded into a routine
`opencode-pursue` milestone alongside Phases 1/2/3/5.

**Phase 6 needs a human even more than Phase 4 does.** Whether a claim
"overstates" what's proved, or whether a `formalization.yaml`'s framing
undersells automation, is a judgment call about how an outside reader
will parse language — not a fact an LLM or a script can check the way
`#print axioms` mechanically checks soundness. The mechanical sub-checks
inside Phase 6 (running `#print axioms` per public claim, checking
`git reflog` for history rewrites) can run autonomously; the actual
messaging judgment cannot, and should not be delegated to whichever
model is doing the drafting — it needs a second, skeptical reader.

## Worked pilot (2026-08-19)

A sample of this methodology was run against the repository as-is before
this document was written, specifically to test whether the approach
surfaces real findings or only sounds rigorous. Results:

- **Phase 1 — pass, independently reverified.** `#print axioms` on
  `foster_theorem` and `effectiveResistance_le_flowEnergy`: both depend
  on exactly `propext, Classical.choice, Quot.sound`.
- **Phase 2 — found a real P4.** `effectiveResistance_le_of_le`
  (`ElectricalFlow.lean:511`, Rayleigh monotonicity) hypothesizes
  `hconnB`, the reinforced network's connectivity. `ElectricalFlow.lean`
  itself, one step later, delivers `supportGraph_connected_of_le`, which
  proves exactly `hconnB` from `hA, hB, hle, hconnA` — no `hnonnegA`/
  `hnonnegB` needed. The naive delete-and-recompile check would **not**
  have caught this (the current proof genuinely uses `hconnB` as
  written); only variant (b) — attempt the goal from the other
  hypotheses plus the file's own later lemma — surfaces it. Recorded as
  an API-cleanup note against `proposals/electrical-flow-routing.md`.
- **Phase 3 — real coverage, with a methodology near-miss.** Roughly
  15 of 23 `Scaffold/QA/SpectralGraph/*.lean` files have explicitly
  named refutation/negative declarations. A literal `Fin n` grep flagged
  `EffectiveResistance_QA.lean` as `K₂`-only — false: it also exercises
  `Fin.sum_univ_three`/`_four` fixtures, just referenced by name rather
  than a literal token. The corrected Phase 3 procedure above exists
  because of this near-miss.
- **Phase 4 — confirmed by reading the script.**
  `scripts/check_citations.py` is exactly a `"Source:"` string-presence
  check, nothing more. No citation has been semantically reconciled by
  tooling; every citation in this repository is currently trusted on the
  strength of whoever wrote the doc comment.
- **Phase 5 — clean on a quick pass.** Every module under
  `Scaffold/Mathlib` is reachable from the `Scaffold.lean` umbrella; no
  orphaned top-level modules found. Declaration-level dead-code analysis
  (a real call graph, not a grep) was not attempted.
- **Phase 6 — sweep complete, 2026-08-19.** `#print axioms` run directly
  on every result `README.md`'s Status section names as "proved, not
  admitted": `cheeger_upper_bound`, `eigen_interlacing_principal_submatrix`,
  `woodbury_identity`, `sherman_morrison`, `foster_theorem`,
  `effectiveResistance_le_flowEnergy`, `expander_mixing_lemma`, and — for
  "Classical Laplacian facts," the closest thing to one target
  declaration — `laplacian_psd`, `laplacian_ones_in_kernel`,
  `laplacian_kernel_eq_span_onesVec`. All ten depend on exactly `propext,
  Classical.choice, Quot.sound`; the public claim is now checked in full,
  not just spot-checked. `git reflog show main` found no `reset`/
  `rebase`/force-push markers — history is clean, nothing currently
  pinned externally would be at risk. No `formalization.yaml` exists yet
  to audit (no Palomar submission has been drafted). While the sweep was
  running, a live cross-cutting gap was also caught outside Phase 6
  proper: `proposals/discharge-perturbation-axioms.md` was still citing
  a C*-algebra lead for Weyl's norm bridge that a sibling proposal,
  `resolvent-calculus-psd.md`, had already spiked and found structurally
  dead the same day — corrected, with the proved fallback bridge that
  proposal delivered instead (`l2OpNorm_eq_max_abs_evals`) substituted
  in as Weyl's actual next step. Not a Phase 6 finding by the letter of
  the phase definitions above (no public claim was wrong, no pin was at
  risk) but the same species of check: does a change in one part of the
  repo actually propagate to every part that depends on it.
- **Phase 2's redundancy variant, swept across other multi-step
  proposals, 2026-08-19 — no additional P4 found.** Checked
  `foster_theorem`'s `hconn` (genuinely independent of its other two
  hypotheses — no nonneg-symmetric graph is connected by construction),
  `lambda2_le_of_certificate`'s `hcard` (a definedness guard for index 1
  existing, not an alternate-route hypothesis), and
  `cheeger_upper_bound`'s `hdpos` (an edgeless `d`-regular graph is
  consistent with every other hypothesis and would make `d = 0`, so
  positivity is not implied by the rest). A spot check, not exhaustive
  the way the original pilot's single finding wasn't either — reported
  as "checked, clean" rather than invented to match the first pass's
  result.

## Recommended cadence

- **Phases 1, 3, 5**: cheap enough to run as a periodic sweep — a natural
  candidate for a new hygiene script alongside the existing four, or a
  standing item before any release tag.
- **Phase 2's redundancy variant**: fold into PR review for any theorem
  with more than two or three hypotheses, per
  `governance/CONTRIBUTING.md`'s Pull Request Checklist — a reviewer
  asking "is every hypothesis here actually necessary, not just used"
  costs little and this pilot shows it finds real things.
- **Phase 4**: scheduled deliberately, not routinely — a dedicated pass
  with real literature access, prioritized by axiom (start with the ones
  this repository's own history has already gotten wrong once: anything
  touching Woodbury-family identities or Cheeger-style constants).
- **Phase 6**: gated on events, not time — run in full immediately before
  any of: a Palomar submission (`proposals/palomar-submission.md`), a
  tagged release (`governance/RELEASES.md` — currently only a placeholder
  entry, so this has not yet triggered), or the clean-room export going
  live. The `#print axioms`-per-public-claim and `git reflog` sub-checks
  are cheap enough to also run as part of any routine README edit,
  independent of a real public-touchpoint trigger — treat that as good
  hygiene, not the full Phase 6 pass.
