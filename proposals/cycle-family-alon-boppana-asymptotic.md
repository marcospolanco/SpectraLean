# The Cycle Family and the Asymptotic Alon–Boppana Corollary

**Status:** COMPLETE (same-run proposal, delivered 2026-09-02 by run
`20260902T021120Z-run-1`, session `ses_fa02a5eaaffemYEa5nqMLuq94z`)
**Type:** Hard-crust growth on a delivered program (backlog item 3's
own named follow-on) — zero new axioms (count stays 5)

## Summary

Backlog item 3's Step-5 completion note records the Alon–Boppana
program's natural follow-on as gated on a name: "the asymptotic
family corollary needs a named d-regular family with `diam → ∞` and
stays a Plan entry until one is named." This delivery names the
canonical family — the cycles `C_n` — and delivers the corollary:

- `alonBoppana_cycle`: `secondEval (2•1 − C_{4k+8}) ≤ 1/(k+1)` — the
  Alon–Boppana error term `d − 2√(d−1) = 0` at `d = 2`, attained with
  rate `1/(k+1)` on the family, with *every* hypothesis of Nilli's
  two-edge method (the `0`-or-`≥1` weight discipline, 2-regularity,
  both tree balls, the far-apart condition at `2(k+1) < distEdge`)
  discharged at arbitrary scale `k`.
- `alonBoppana_cycle_laplacian`: the same bound at the combinatorial
  Laplacian (`2•1 − A = L` on 2-regular input, the identity proved),
  through the shelf's proof-irrelevance bridge `secondEval_congr`.
- `alonBoppana_cycle_asymptotic`: `∀ ε > 0, ∃ k, λ₂(L(C_{4k+8})) ≤ ε`
  — the asymptotic Alon–Boppana reading on the named family.

The family is carried by **Mathlib's own `SimpleGraph.cycleGraph n`**
through the delivered `toWAdj` adapter (roundtrip, symmetry,
nonnegativity, and 2-regularity via `cycleGraph_degree_three_le` all
free), so no graph model is duplicated. The genuinely new mathematical
content is the **exact cycle distance formula**
`dist a b = min ((b−a).val) (n − (b−a).val)` — the walk route up (one
adjacency step appended at a time through the connectivity triangle)
and the **integer-potential route down** (any walk realizes a residue
representative of `b − start` of absolute value at most its length:
each step moves the potential by `±1` up to a multiple of `n`, in
`Int.ModEq`/`modEq_iff_add_fac` form, with the extraction case
analysis in ℤ) — from which the tree-ball level classes
(`levClass a (a+1) j = {a + (j+1), a + (n−j)}`) and the far-apart
condition reduce to arithmetic.

This is also the program's first **parametric** instantiation: until
now `IsTreeBall`/`distEdge`/`levE` had been exercised only on fixed
literal fixtures (`C₈` at radius `1`). Everything here holds for
arbitrary `n` at its natural threshold, with the QA pinning the
formula at `C₁₂` — a fixture size no literal-matrix QA had reached.

## Why this item, and what it is load-bearing on

- It closes a named follow-on of a complete program (priority item 5's
  "strengthen reusable SGT QA and bridge interfaces" under the
  center-out fall-through; the Active table was all Low/blocked and
  every other queue item consumer-less or operator-gated at selection
  time).
- The distance formula is load-bearing on the *exact* BFS structure:
  a wrong orientation, wraparound, or antipodal case breaks the
  formula's value at the QA pins (which include the wraparound pair
  `(7, 2)` and the antipodal tie `(5, 11)` where both orientations
  read `6`).
- The tree-ball cardinality is load-bearing on a real threshold the
  delivery discovered honestly: the natural-looking hypothesis
  `2(k+1) ≤ n` is **false at its boundary** — at `n = 2(k+1)` the
  level-`k` class is the single antipodal vertex (both offsets
  coincide) and the ball is not a tree. Theorems carry the strict
  `2(k+1) < n`. (The elaborator forced this correction during the
  spike: the first draft's `levClass_eq` at `2j+1 < n` had a
  counterexample-shaped hole at `n = 2j+2`.)
- `alonBoppana_cycle` is load-bearing on the whole Step-2–5 stack at
  every scale — it is the two-edge method's first consumer whose
  graph is not a fixed literal.

## Degenerate corners (checked at design time)

- **Small cycles:** the adjacency step `Adj a (a+1)` is false at
  `n = 1` (no distinct vertices) — the helper carries `2 ≤ n`. All
  public statements hold for their stated ranges; the family's
  `n = 4k+8 ≥ 8` is always far from every corner.
- **The level-cardinality boundary:** as above, strict `<` at
  `2(k+1) < n`; the far-apart condition needs the four cross
  distances `> 2(k+1)`, which the `4k+8` sizing supplies with slack
  `1` (pinned in QA as exactly the slack that fails on `C₁₂` at
  `k = 2`).
- No measures, no integrals, no strictness traps elsewhere; the
  statements are equational/ℕ-inequality shaped.

## Delivered

1. **Shelf** (`GraphTheory/AlonBoppana.lean`'s new `CycleFamily`
   section; new imports `SimpleGraphAdapter` +
   `Mathlib.Combinatorics.SimpleGraph.Circulant`; all proved, zero
   axioms): the private cyclic-`Fin` arithmetic layer
   (`fin_val_sub_eq` at `Fin.sub_def`'s own order, `mod_decomp` as the
   one-stop modulus-decomposition tool, decomposition/injectivity of
   `(z − a).val`, the swap and successor lemmas), the family interface
   (`cycleAdj`, `cycleAdj_isSymm/_nonneg/_apply/_h01`,
   `supportGraph_cycleAdj`, `cycleAdj_connected`,
   `cycleAdj_isDRegular`), the exact distance
   (`cycleAdj_dist_eq`, with the up-route bound
   `cycleGraph_dist_le_up`, the ℤ-potential invariant
   `cycle_walk_potential`, and the sInf half `cycleGraph_dist_ge_min`),
   the tree ball (`cycle_levE_eq`, `cycle_levClass_eq`,
   `isTreeBall_cycle` at `2(k+1) < n`), the far-apart condition
   (`cycleAdj_distEdge_gt`), and the three headline theorems plus
   `laplacian_cycleAdj`.
2. **QA** (`AlonBoppana_QA.lean`'s new Step-7 section, +6 nameable):
   the distance formula pinned at `C₁₂` in four shapes (short way
   `4`, wraparound `5`, antipodal tie `6`, self `0`); the level class
   `levClass (0,1) 3 = {4, 9}`; the theorem instance at `k = 1`
   (`secondEval (2•1 − C₁₂) ≤ 1/2`); the Laplacian spelling; the
   asymptotic corollary at `ε = 1/2`; and the far-apart fence — on
   `C₁₂` at `k = 2` both radius-`3` tree balls are genuine yet the
   antipodal edges `(0,1)`/`(6,7)` are only `5` apart, so `hfar`
   fails by exactly the slack the `4k+8` sizing buys (the parametric
   counterpart of the `C₈` `hfar` fence).
3. **Records:** this proposal, the `proposals/README.md` Delivered
   row, README (3618 + the Alon–Boppana highlight's asymptotic
   extension), the radar QA-axis sync (held at 4.0 per protocol, with
   the parametric note), `index/map/spectral_graph.md`'s cycle-family
   rows, the scoreboard verification row, both map data tables +
   regenerated SVG, the QA module's purpose header, backlog item 3's
   closure note, the execution plan, and the activity log.

## Verification

- Spike first: `wip/cyclefam_spike.lean` carried the shelf section,
  the full QA, and the audit, iterated to zero errors/zero warnings
  before any shelf edit. The elaborator caught one real statement
  defect during the spike (the level-cardinality boundary above) —
  the falsifiability discipline working.
- `lake env lean` zero errors and zero new warnings on both touched
  modules; explicit `lake build` targets ✔ on both (the QA-imports-
  shelf stale-olen boundary met once and remediated per the
  completeness script's docstring).
- **`#print axioms` via `wip/cyclefam_axcheck.lean` on all 23 nameable
  new declarations (17 shelf + 6 QA): every one exactly
  `propext, Classical.choice, Quot.sound` — pure hard crust, zero
  contact with any admitted axiom.**
- **Full `lake build` ✔ immediately followed by
  `check_build_completeness.py` — 133 source files, 133 fresh
  artifacts, 0 stale, 0 missing, exit 0** (after the documented
  single-module mtime remediation).
- `lint_axioms` exit 0 (5 axioms, both PF findings
  allowlisted-confirmed); `check_refutation_independence` (10-tag
  clean — no tags added, nothing here touches an axiom);
  `check_public_reachability` clean (63 repo modules);
  `check_citations` ("All axioms have proper citations!");
  `check_markdown_links` clean; `check_backlog_freshness` clean;
  scoreboard regenerated (**3618/5/0**) with the verification row;
  map-freshness exit 0 after the 3612 → 3618 stats sync in both map
  files and SVG regeneration (no station — no tier change).

## What is deliberately not here

- **The general asymptotic family statement** (`λ₂ ≥ 2√(d−1) − o(1)`
  at general `d`) — the two-edge method's shape is per-graph and
  diameter-dependent by design (`alonBoppana_diam_ge` records the
  honest constraint); a general-d family needs the same delivery at
  each `d` and stays unclaimed.
- **`cycleAdj` as a general-purpose cycle interface** beyond the
  Alon–Boppana consumer — e.g., exact spectrum pins of `C_n`
  (`2 − 2cos(2πk/n)`) are natural follow-ons for a consumer that
  needs them, not part of this delivery.
- The QA pins are at `C₁₂` (fixed `n`); parametric *QA instances*
  (the QA axis's full "parametric QA" gap) would mean checking
  properties at symbolic `n` — the theorems here are parametric, the
  QA witnesses are not.

## Technique findings (for the next run)

- **`Fin.sub_def` unfolds to `(n - b.val + a.val) % n`** — state all
  cyclic-difference lemmas at that order or fight `rw` everywhere;
  `Nat.add_mul_mod_self_right` (mod by the *second* factor) plus
  `Nat.mod_eq_of_lt` closes every residue computation once a
  `∃ q, X = c + q * n` witness is pre-built with `omega`.
- **`omega` does not relate `n * q` and `q * n`, nor `q * n` and
  `(q+1) * n`** — provide `ring`-proven product identities
  (`(q+1)*n = q*n + n`, `x*u = x + x*(u−1)`) as hypotheses before
  calling `omega`/`linarith` on goals carrying products-as-atoms.
- **`omega` treats `|x|` (ℤ) as an opaque atom** — no automatic abs
  splitting and no `|x| ≥ 0` knowledge: provide `abs_le`-decomposed
  facts or `rw [abs_of_nonpos/abs_of_nonneg]` yourself.
- **Walk induction with an outer walk in context** produces a broken
  IH (`Walk a✝ b → ...` instead of the tail's statement) — extract
  the induction into a standalone private theorem; the
  `| @cons u w b hadj tail ih` naming (three endpoint names for
  cons's `u v w`) then works and lets the case's endpoint shadow the
  fixed target.
- **`le_csInf` in this Mathlib takes `s.Nonempty`, not `BddBelow`** —
  supply a range witness (`Reachable = Nonempty (Walk u v)`, so
  `hconn.preconnected a b` provides it directly).
- **`Int.ModEq` is `a % n = b % n` with `Int.modEq_iff_add_fac` the
  cleanest extractor** (`∃ t, b = a + n * t`); `Int.emod_eq_of_lt`
  needs *both* `0 ≤ a` and `a < b` arguments.
- **`(⟨c, _⟩ : Fin n)` literals in statements**: the statement-
  position proof term (`by omega`) sees named binders only — write
  `(hc : c < n) →` not `c < n →`; and `↑(4 * k + 8)` needs an
  explicit `haveI : NeZero (4 * k + 8) := ⟨by omega⟩` in proof
  bodies (unification of `a + 1`-spelled vs `⟨c⟩`-spelled endpoints
  can whnf-explode — bridge spellings with an explicit `Fin.ext`
  equality rather than letting `exact` unify them).
- `Fin.val_one' n : ((1 : Fin n) : ℕ) = 1 % n` is the reliable
  one-value lemma (`Fin.val_one` is stated at `Fin (n+2)`); with a
  literal `n`, `decide` closes the residue.
