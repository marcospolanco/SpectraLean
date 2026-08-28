# Proposal: Audit `perron_frobenius` and `primitive_power_tendsto` for the Degenerate-Cardinality Hazard

**Status:** Proposed 2026-08-28.

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
