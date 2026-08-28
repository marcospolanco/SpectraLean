# Proposal: Audit `perron_frobenius` and `primitive_power_tendsto` for the Degenerate-Cardinality Hazard

**Status:** **COMPLETE 2026-08-28** (run `20260828T165900Z-run-1`) —
both axioms **confirmed safe by Lean-verified unsatisfiability at the
degenerate dimension** (Step 0 below), both `card V = 1` adjacent
corners spot-checked satisfiable with conclusions pinned to hand data
(scope item 2), the two provisional linter allowlist entries upgraded
to cite the unconditional Lean proofs (scope item 3), **zero axiom
changes** (count stays 10; no hypothesis of either axiom moved). The
honesty note below stands unchanged and load-bearing: this audit
cleared the degenerate-cardinality mechanism only.

## The verdicts (the exact Lean arguments, not restated docstrings)

**`perron_frobenius` — SAFE at `Fintype.card V = 0`, by
unsatisfiability of `hex`.** Proved unconditionally as
`Scaffold.LinearAlgebra.QA.perron_frobenius_hex_unsat_card_zero_QA`
(`Scaffold/QA/LinearAlgebra/PerronFrobenius_QA.lean`): from
`hV : Fintype.card V = 0` and any `A : Matrix V V ℝ` and
`hex : ∃ i j, 0 < A i j`, derive `False` — `Fintype.card_eq_zero_iff`
turns `hV` into `IsEmpty V`, the existential supplies `i : V`, and
`isEmptyElim i` closes. `#print axioms`: exactly `propext,
Classical.choice, Quot.sound`. The axiom's hypothesis set therefore
has *no instantiation* at the empty dimension — structurally the same
safe outcome the structural read predicted, but now checked by the
kernel rather than asserted by a docstring.

**`primitive_power_tendsto` — SAFE at `Fintype.card V = 0`, by
unsatisfiability of `hπsum`.** Proved unconditionally as
`Scaffold.QA.SpectralGraph.mass_one_unsat_card_zero_QA`
(`Scaffold/QA/SpectralGraph/DirectedMixing_QA.lean`, Section D): from
`hV : Fintype.card V = 0` and any `π : V → ℝ` and
`hπsum : ∑ i, π i = 1`, derive `False` — the `IsEmpty V` from
`Fintype.card_eq_zero_iff` makes `Finset.univ = ∅`
(`Finset.univ_eq_empty`), so the sum is `0` (`Finset.sum_empty`)
against `1`. `#print axioms`: the standard three only.

**The `card V = 1` adjacent corners (scope item 2) — both
satisfiable, no clause broken:**

- `perron_frobenius` at `Fin 1` / `!![1]` (`perron_frobenius_S1_QA`):
  every hypothesis is satisfiable (`hex` witnesses at the single
  diagonal entry — the corner where it becomes *trivially*
  satisfiable), and the axiom instance's conclusion pins exactly to
  the hand Perron data: the root is `1` (derived from the
  eigen-equation on the axiom's unknown witness `x`:
  `1 * x 0 = r * x 0` with `x 0 > 0`), the simplicity clause reads
  exactly the hand-pinned `rootMultiplicity 1 (X − C 1) = 1`
  (`S1_charpoly_QA` via `Matrix.det_fin_one` +
  `Matrix.charmatrix_apply_eq`; `S1_rootMultiplicity_QA` via
  `Polynomial.rootMultiplicity_X_sub_C_self`) — the clause the scope
  item named as the risk — and the Perron direction is the constant
  one. `#print axioms`: `perron_frobenius` + the standard three, the
  honest conditional structure of an axiom-consumed pin.
- `primitive_power_tendsto` at `Fin 1` / `!![1]` (`P1_singleton_hand_QA`
  + `P1_singleton_axiom_QA`): every hypothesis is satisfiable
  (row-sum `1`, primitivity at `k = 1`, the constant-one stationary
  vector with mass one — `hπsum` trivially satisfiable at the
  singleton), and the axiom's conclusion shape is proved *by hand,
  no axiom*: the power sequence is constant (`!![1] = 1` so `P^t = 1`)
  and the limit vector `((π ⬝ᵥ x) • 1)` *is* the start `x` on one
  coordinate. The axiom instance is non-vacuous there and concludes
  a hand-provable statement. `#print axioms`: the hand pin standard
  three only; the instance carries `primitive_power_tendsto` alone.

**Technique findings** (the spike `wip/pfa_spike.lean`, iterated to
zero errors/warnings before any shelf edit): the pinned Mathlib's
`Fin 1` sum lemma is `Fin.sum_univ_one` (not `Finset.`); a one-shot
`rw [Matrix.charpoly, Matrix.det_fin_one, …]` chain misbehaves where
the step-by-step sequence elaborates cleanly (the singleton-charpoly
route is four separate rewrites); `rw [Subsingleton.elim i j]` closes
`ReflTransGen` goals outright via its post-`rfl`, so a trailing
`exact …refl` errors goalless; `linear_combination` needs `S1 0 0`
normalized to `1` first (`rwa [S1_00] at h0`) since it treats the
entry as an atom.

## Allowlist upgrade (scope item 3 — done)

`scripts/lint_axioms.py`'s two provisional entries are replaced by
Lean-confirmed entries citing the exact theorem names above
(`perron_frobenius_hex_unsat_card_zero_QA`,
`mass_one_unsat_card_zero_QA`) and the singleton checks;
`python3 scripts/lint_axioms.py` exits 0 with both findings reported
as allowlisted-confirmed rather than provisional.

## The obligation this discharges

All three matrix concentration axioms
(`matrix_hoeffding`/`matrix_bernstein`/`matrix_azuma_hoeffding`) were
found genuinely inconsistent (`1 ≤ 0`) at `Fintype.card V = 0` and
repaired 2026-08-28 with an explicit `[Nonempty V]` guard (see
`proposals/matrix-hoeffding-spectral-gap-estimation.md`'s delivery
record). That is one specific hazard class, now named in
`docs/2_ARCHITECTURE.md` §5's admission policy: *does every hypothesis
stay simultaneously satisfiable while a conclusion-side prefactor or
denominator collapses to something the hypotheses no longer justify?*
Clearing an axiom against the junk-integral hazard (already done for the
four scalar axioms, `proposals/audit-scalar-concentration-integrability-
hazard.md`) does not clear it against *this* hazard — they are
independent mechanisms. Two remaining axioms quantify over `Matrix V V`
or `V → ℝ` with no visible `Nonempty V` and have not been checked against
this specific corner: `perron_frobenius` and `primitive_power_tendsto`.

## The finding (structural read, not yet Lean-checked — this proposal's
own Step 0 is what would confirm or refute it)

Unlike the matrix trio, a first read of both axioms' exact hypothesis
lists suggests the degenerate corner may already be **safe by
construction** — but for a reason specific to each, not because
`Nonempty V` is unnecessary in general:

- **`perron_frobenius`** (`Scaffold/Mathlib/LinearAlgebra/PerronFrobenius.lean`):
  the module's own docstring already argues the empty-type corner is
  harmless — "It carries no `Fintype` assumption; on a type with at most
  one element it holds vacuously or by reflexivity, which is why
  `perron_frobenius` carries the explicit `hex` guard." At
  `Fintype.card V = 0`, the hypothesis `hex : ∃ i j, 0 < A i j` has no
  witness to supply (there is no `i` or `j`), so `hex` is
  **unsatisfiable** — the axiom can never be instantiated in this
  corner at all. This is structurally different from the matrix trio's
  failure, where every hypothesis (including the analogous boundedness/
  independence clauses) remained satisfiable simultaneously while the
  conclusion's own prefactor broke. An unsatisfiable hypothesis is a
  safe outcome (the axiom is vacuously never invoked there), not a
  defect — but this is exactly the kind of claim this project's own
  discipline says must be Lean-checked, not accepted from a docstring's
  prose, especially since the *same kind* of prose reasoning
  ("obviously fine at the edge") is what let the matrix trio's bug sit
  for as long as it did.
- **`primitive_power_tendsto`** (`Scaffold/Mathlib/LinearAlgebra/PrimitiveConvergence.lean`):
  the hypothesis `hπsum : ∑ i, π i = 1` requires `π : V → ℝ` to sum to
  `1` over `V`. At `Fintype.card V = 0`, `∑ i, π i = 0` unconditionally
  (the empty sum), so `hπsum` demands `0 = 1` — **unsatisfiable**, again
  a structurally safe (never-instantiable) outcome rather than an
  inconsistency, by the same reasoning pattern as above but through a
  different hypothesis.

**Important honesty note, not yet resolved:** this is exactly the same
shape of reasoning the scalar-concentration audit's own "honesty note"
used for `hoeffding_lemma` — predicting safety by tracing which
hypothesis becomes unsatisfiable — and that audit still found a real,
independent defect (a wrong classical constant) that this style of
reasoning could never have caught, because it only rules out *one*
mechanism. This proposal's structural read only checks the
degenerate-cardinality mechanism specifically; it says nothing about
whether either axiom's actual mathematical content (the Perron root
characterization, the convergence rate-free limit statement) is
correctly transcribed. Do not read a clean Step 0 verdict here as a
general clean bill of health for either axiom.

## Scope

1. **Step 0 (mandatory, not done by this document):** for each axiom,
   confirm in Lean (not by re-reading the docstring) that the identified
   hypothesis is genuinely unsatisfiable at `Fintype.card V = 0` — a
   short spike instantiating each axiom at the empty type and deriving
   `False` from the named hypothesis alone. If either spike instead
   finds the hypothesis satisfiable (e.g. if `V = Empty` admits some
   degenerate `π` or `A` this reasoning missed), that is exactly the
   kind of live defect this audit exists to catch, and the proposal's
   scope shifts to a repair-in-place per the Woodbury/subgaussian
   precedent.
2. **While Lean is open on these files, spot-check the adjacent
   corners** the same hazard class covers per `docs/2_ARCHITECTURE.md`
   §5's checklist for these two specific axioms only (not a general
   re-audit): `Fintype.card V = 1` (does `hex`/`hπsum` become trivially
   satisfiable in a way that breaks a different part of the conclusion,
   e.g. the `rootMultiplicity ... = 1` clause or the uniqueness clause
   at a 1-dimensional space?) — cheap to check alongside Step 0's spike,
   not a separate mandate.
3. **If both are confirmed safe:** record the verdict in this proposal
   (the exact Lean argument, not a restated docstring claim), add the
   allowlist entries `lint-axiom-degenerate-corner-guards.md`'s checker
   needs (once that proposal is delivered) so these two axioms stop
   showing as unresolved findings, and close this proposal with no
   Lean changes.
4. **If either is found unsafe:** repair-and-retire at the same name
   and conclusion with the added guard, per the Woodbury/subgaussian/
   matrix-trio precedent — same name, same conclusion, corrected
   hypotheses only.

## Acceptance bar

- Both axioms get an explicit, Lean-verified verdict recorded in this
  proposal — "confirmed safe, here is the exact unsatisfiability proof"
  or "found unsafe, repaired" — never a restated docstring assumption
  passed off as a check.
- If no axiom changes, the explicit axiom count stays 10 and
  `lint_axioms`/`check_citations`/`check_markdown_links`/a full
  `lake build` still pass (any new spike-derived safety lemmas worth
  keeping must build cleanly).
- The verdicts feed `lint-axiom-degenerate-corner-guards.md`'s allowlist
  once that proposal exists, so this audit's result isn't stranded in a
  document nobody re-reads.

## Non-goals

- **Not a general re-audit of either axiom's mathematical content.**
  Per the honesty note above, a clean verdict on the degenerate-
  cardinality corner says nothing about other hazard classes
  (a wrong constant, a strictness mismatch, an unstated genericity
  assumption). Those would need their own Step 0s if ever suspected;
  none is currently suspected for either axiom, and this proposal does
  not go looking for one.
- **Not a rate or genericity extension.** `primitive_power_tendsto`'s
  own documentation already records "no rate, Π topology" as an honest
  scope boundary; this proposal does not touch that boundary either
  direction.

## Delivery record (2026-08-28, run `20260828T165900Z-run-1`)

Delivered per the scope above, with the verdicts recorded in the
section above. Files: `Scaffold/QA/LinearAlgebra/
PerronFrobenius_QA.lean` (+3 theorems, +1 def: the empty-card verdict,
`S1_charpoly_QA`, `S1_rootMultiplicity_QA`,
`perron_frobenius_S1_QA`, fixture `S1`) and
`Scaffold/QA/SpectralGraph/DirectedMixing_QA.lean` Section D
(+10 theorems, +1 def: the empty-card verdict, the `P1`/`u1`
hypothesis stack, the hand pin, the axiom instance). Zero changes to
either axiom file — the audit's outcome was "both safe," so the
repair branch (scope item 4) never opened.

**Verification:** spike first (`wip/pfa_spike.lean`, all pieces to
zero errors/warnings before any shelf edit; the live unsatisfiability
arguments elaborated against the actual axioms); `lake env lean` zero
errors/zero warnings on both touched QA modules; explicit `lake
build` of both QA targets (2202/2202, "Build completed successfully");
`#print axioms` via `wip/pfa_axcheck.lean` on all seven new
declarations — the two verdict lemmas, the three hand pins exactly
`propext, Classical.choice, Quot.sound`, the two singleton instances
carrying exactly their named axiom; `lint_axioms` exit 0 with the
upgraded entries; full `lake build` + `check_build_completeness.py`,
`check_citations`, `check_markdown_links`, scoreboard regeneration,
and map freshness recorded in the run's activity entry. QA count
moves by the generator metric (2785 → 2800); the scoreboard and map
stats stamps were synced and re-checked.

**Honest residual:** the audit cleared the degenerate-cardinality
hazard class only, per the honesty note; the mechanical
signature-visible half of that class (and the measure-mass class)
remains enforced by `lint_axioms.py` on every admission. No further
residual is claimed or owed by this proposal.
