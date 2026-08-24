# The Resistance Metric: Definiteness and the Triangle Inequality

**Status:** COMPLETE (delivered 2026-08-24, the same run that wrote this
document — Steps 0+1 in one run; see the delivery record below)
**Added:** 2026-08-24
**Backlog anchor:** `docs/6_SGT_BACKLOG.md` item 7 — the electrical
family's two named non-gated residuals: "the definiteness residual
`R u v = 0 ↔ u = v`, the resistance metric (triangle inequality)";
Matrix–Tree and Kirchhoff network theorems remain separately gated on a
named consumer and are **not** in scope here.

**Why now / leverage:** the Active priority table holds no High/Medium
rows (every remaining row is a Low blocked on a human or technical
decision an autonomous Lean-work run cannot make), so the center-out
policy governs; of the standing candidates, two are gated (directed
mixing needs a primitivity-shaped admission; the wide-band minimax
filters need a named consumer) and one is honestly blocked (the pairwise
set shape). Backlog item 7 names these two residuals as the family's
remaining *unblocked* work. Completing them converts `effectiveResistance`
from a nonnegative symmetric function into a **genuine metric** on every
connected network — the classical "resistance distance" (Doyle–Snell
1984 §3.5 potentials; Gutman–Xiao 2004 for the metric statement) — which
is the interface every distance-based graph consumer (k-center,
clustering-by-distance, diameter bounds) would import. Both theorems are
pure hard crust and each is load-bearing by the falsifiability test: the
definiteness residual consumes the one-sided Dirichlet bound
`effectiveResistance_ge_sq_div_quadForm` and the kernel-free degree
argument; the triangle consumes the energy identity at solution level,
the reciprocity-based polarization `quadForm_laplacian_sub_smul`, the
agreement theorem, and — the new mathematical content — a **maximum
principle** for unit-demand potentials that would be false as stated if
any of `laplacian_mulVec_apply`, `supportGraph` walk induction, or the
existence theorem were misstated.

## Step 0: route survey (recorded before stating)

**Mathlib survey (pinned v4.14.0, checked 2026-08-24):** no
"resistance" declaration anywhere in the pin (re-confirmed; first
recorded at the Electrical module's own 2026-08-18 survey); no
maximum-principle or harmonic-extremum statement for graph potentials
("maximum principle" appears only in complex analysis and convexity;
`Combinatorics/SimpleGraph/` has no harmonic-function machinery at all).
Both ingredients are genuinely new; the route below is self-contained on
the shelf.

**Route decision.** The sharp triangle `R(u,w) ≤ R(u,v) + R(v,w)` cannot
be obtained from the eigenbasis/spectral route: there
`R(u,v) = ‖z_u − z_v‖²` in the `1/√λ`-weighted eigenbasis, and the
Euclidean triangle on the `z`-vectors yields only the **root**-triangle
`√R(u,w) ≤ √R(u,v) + √R(v,w)` — the cross term `2√(R·R)` is exactly
what must be cancelled for the sharp form. The cancellation is the
**maximum principle**: for `f` solving `L *ᵥ f = e u − e v`, the cross
term of the energy expansion of `h := f + g` (with `g` solving
`e v − e w`, so `h` solves `e u − e w`) is `f ⬝ᵥ (L *ᵥ g) = f v − f w`,
and `f v ≤ f w` because every value of `f` lies between its boundary
values `f v` and `f u`. Concretely:

- `R(u,w) = quadForm L (f+g)` (energy identity + agreement) `=
  quadForm L f + 2(f ⬝ᵥ L *ᵥ g) + quadForm L g` (polarization
  `quadForm_laplacian_sub_smul` at `t = −1`) `= R(u,v) + R(v,w) +
  2(f v − f w)`, and the bracketed term is `≤ 0` by confinement.
- **Confinement proof:** at a max-point `x₀ ∉ {u, v}` the diffusion form
  `∑ j, A x₀ j * (f x₀ − f j) = 0` (`laplacian_mulVec_apply`) is a sum of
  nonnegative terms (`hnonneg`, maximality), so each vanishes and the max
  value propagates across every positive-weight edge; walk induction
  floods the connected graph (the kernel-characterization argument run at
  an inequality), so a max strictly above both boundary values is
  impossible. The min side is the max side at `−f` (the demand negates
  and swaps). Pins: `Finite.exists_max` (Data/Fintype/Lattice.lean),
  `Finset.sum_eq_zero_iff_of_nonneg`, `Matrix.mulVec_single`,
  `Matrix.dotProduct_single`, `min_le_iff`/`le_max_iff`.
- **Definiteness without a max principle:** the Dirichlet bound at the
  indicator test potential `e u` gives `R u v ≥ (e u u − e u v)² / E`
  with `E = quadForm L e u = deg A u − A u u = ∑_{j ≠ u} A u j`, which is
  positive because connectivity gives `u` a positive-weight off-diagonal
  neighbor (first edge of any walk to `v ≠ u`).

**Statement-shape decisions (recorded before stating):**

1. Confinement is stated at the *equation* level
   (`(laplacian A).mulVec f = Pi.single u 1 − Pi.single v 1`), not inside
   `IsEffectiveResistance`, so potential-level consumers can use it
   directly — the module's own existing pattern
   (`quadForm_laplacian_eq_sub_of_mulVec_eq_single_sub_single`).
2. Confinement gives both bounds unconditionally as
   `min (f u) (f v) ≤ f x ≤ max (f u) (f v)` — no `u ≠ v` hypothesis, no
   ordering assumed; the ordering enters only in the triangle proof via
   `effectiveResistance_pos_of_ne`. This keeps each lemma hypothesis-minimal.
3. Both resistance-level theorems stated at connected strength
   (`hA`, `hnonneg`, `hconn`), matching the family's other function-level
   theorems (`effectiveResistance_symm`, `effectiveResistance_nonneg`).
4. Module placement: the confinement lemmas live in
   `GraphTheory.Electrical` beside their consumers rather than in the
   2889-line center `Spectral.lean` — they are potential tools for the
   resistance layer; the center's role (diffusion form, walk induction)
   is consumed, not extended.

## Step 1: the Lean content

New section "The resistance metric" in
`Scaffold/Mathlib/GraphTheory/Electrical.lean` (no new imports):

1. `laplacian_mulVec_eq_single_sub_single_le_max` — the maximum
   principle, top half.
2. `laplacian_mulVec_eq_single_sub_single_min_le` — the min side, by
   negation of the demand.
3. `effectiveResistance_pos_of_ne` — `u ≠ v → 0 < R u v`.
4. `effectiveResistance_eq_zero_iff` — `R u v = 0 ↔ u = v`.
5. `effectiveResistance_le_add` — the triangle inequality.

With the proved `effectiveResistance_nonneg`, `_symm`, `_self`, this
completes the four metric laws as proved theorems (a `MetricSpace`
instance is deliberately *not* registered: the vertex type is global and
the laws hold only under the connectedness hypothesis — recorded as a
follow-on packaging decision, not a gap).

## QA plan (`Scaffold/QA/SpectralGraph/ResistanceMetric_QA.lean`)

All four sections load-bearing, reusing covered fixtures:

1. **Equality case on the 3-path** (`connPathAdj` from
   `Connectivity_QA`): `R(0,1) = R(1,2) = 1` (new witnesses `![1,0,0]`,
   `![0,0,−1]`), joined with the pinned `R(0,2) = 2` — the triangle
   **attained with equality** at the middle vertex (the sharpness
   witness: a weaker route's constant would be caught here).
2. **Strict case on `K₃`** (`fosterTriAdj` pins from `Foster_QA`,
   QA-to-QA import precedent): `2/3 < 2/3 + 2/3` — the honest gap.
3. **Definiteness + confinement positive witnesses on the path**: the
   middle potential `![2,1,0]` (solves `e₀ − e₂`) with confinement
   instantiated at every vertex and the interior value pinned *strictly*
   between the boundary values; the `iff` instantiated at a
   distinct pair and at the diagonal.
4. **The signed fence** — one fixture fencing `hnonneg` across all three
   theorems: `signedAdj = (![0,1,1]; ![1,0,−1]; ![1,−1,0])`, symmetric,
   support graph connected (path `1—0—2`), **not** nonnegative. In-file
   entrywise analysis of the demand equations yields the
   solution-shape facts (`f 1 = f 0`, `f 2 = f 0 − 1` for the `e₀ − e₁`
   demand), value-pinning through the junk-free branch (`dif_pos` +
   the shape facts, since the shelf's uniqueness needs `hnonneg`), and
   then: `R(0,1) = 0` with `0 ≠ 1` (definiteness **refuted in proved
   form**), `R(0,2) = 0`, `R(2,1) = −2`, and
   `¬(0 ≤ 0 + (−2))` (the triangle **refuted**); confinement's
   hypothesis-free conclusion **refuted** at the interior vertex. With
   `hA` and `hconn` verified on the fixture, exactly the nonnegativity
   hypothesis is isolated for every new theorem.

## Pricing and follow-ons

- Cost: one module section (~180 lines) + one QA file (~230 lines); every
  consumed declaration verified on shelf above; no new axioms (count
  stays 9), no new imports, no umbrella change (Electrical already
  imported).
- Honest residual: the fence shows the theorems are *false* without
  nonnegativity — that is load-bearing, not a defect. The
  `MetricSpace`/`PseudoMetricSpace` packaging (and the
  resistance-*metric* API: balls, diameter) is a recorded follow-on
  needing its own consumer naming.
- Citation locators: Doyle–Snell (1984) §3.5 and Gutman–Xiao (TPA 2004)
  are route provenance for *proved* statements and carry the repo's
  standing verify-against-physical-copy caveat; no page numbers recorded
  until confirmed against physical copies.

## Delivery record (2026-08-24, run `20260824T192530Z-run-1`)

**Delivered as planned — pure hard crust, zero new axioms (count stays
9; `#print axioms` via `wip/rm_axcheck.lean` on all 5 public + 28 QA
declarations: `propext, Classical.choice, Quot.sound` only, every
one). QA 1971 → 1999 (`ResistanceMetric_QA` a new file at 28). The
electrical family's two named non-gated residuals are closed and
`effectiveResistance` is a metric on every connected network.**

- The module section landed exactly at the Step-1 shapes: the maximum
  principle `laplacian_mulVec_eq_single_sub_single_le_max` (with
  `Finite.exists_max`, `laplacian_mulVec_apply`, and the
  walk-induction flood — the induction stated over the walk's *start*
  so cons-peeling works), the min half
  `laplacian_mulVec_eq_single_sub_single_min_le` (negated demand),
  `effectiveResistance_pos_of_ne` (Dirichlet at `e u`; the connectivity
  neighbor from the first cons-edge of any walk),
  `effectiveResistance_eq_zero_iff`, and `effectiveResistance_le_add`
  (the `f + g` assembly, polarization at `t = −1`, cross term `f v − f w`
  closed by min-confinement + positivity, degenerate cases through
  `effectiveResistance_self`).
- QA: all four planned sections — the path equality case `2 = 1 + 1`
  with the degenerate `v = u` instantiation, the K₃ strict case `2/3 <
  4/3` on imported pins, the confinement/definiteness positive
  witnesses at the actual unit-current potential `![2,1,0]`, and the
  signed fence (all three hypothesis-free conclusions refuted with
  exactly `hnonneg` isolated).
- Pin-technique list (the elaboration rounds' recurring fixes): a
  numeral RHS against a `Pi.single` LHS leaves the dependent family
  metavariable stuck — ascribe the family
  (`(Pi.single u (1 : ℝ) : V → ℝ) u = 1`) or evaluate the applied RHS
  in place (`simp [Pi.sub_apply, Pi.single_apply] at h`, the Cheeger
  idiom); `(-f) x` is a function-negation *atom* to `linarith` —
  `simp only [Pi.neg_apply] at h` first; `rw [a, b] at h1 h2` fails
  when `a` is absent from `h2` — one lemma per rewrite per hypothesis;
  `Walk.cons`' induction case binds six names
  (`@cons a b c hadj wrest ih`); the repo's matrix-notation
  `vecTail`-leftover trap re-confirmed — the signed fixture uses the
  entrywise-if definition per `Foster_QA`'s precedent; `Finset.sum_erase`
  does not exist at this pin (`Finset.sum_erase_add _ _ h`, note the
  flipped orientation) and `Finset.single_le_sum` takes the
  `∀ i ∈ s` nonneg proof first; `funext i; simp` alone proves
  `f + g = f - (-1 : ℝ) • g` (Pi lemmas unfold function arithmetic).
- Verification: `lake env lean` on the module and the QA file — zero
  errors, zero warnings each; explicit `lake build` targets both ✔
  (2009/2009, 2015/2015); `#print axioms` on all 33 declarations —
  the standard three only; **full `lake build` ✔ (2261 targets, "Build
  completed successfully"; zero warnings in the changed modules)**;
  `lint_axioms` (**9**, unchanged), `check_citations`,
  `check_markdown_links` pass; scoreboard regenerated (**1999/9/0**,
  idempotent). Records updated: this document, `proposals/README.md`
  (the Delivered row; the progress paragraph), README (1999; the
  status paragraph's resistance-metric clause; the module-table row),
  the radar (QA axis synced 1971/50 → 1999/51 and the axis-6 delivery
  sentence, both held), the scoreboard (all four verification rows +
  the interpretation bullet), `index/map/spectral_graph.md` (5
  declaration rows), backlog item 7 (the delivery update), the
  execution plan, and the activity log.

**Open follow-ons (priced, not gaps in what is claimed):** the
`MetricSpace` packaging under a connectedness-carrying type synonym
(needs a consumer naming what it unlocks — balls/diameter
statements); the `R u v = 0 ↔ u = v` residual at *reachability-pair*
strength (the uniqueness theorem already holds there; positivity
currently derives from connectivity); the equality-characterization
of the triangle (`R(u,w) = R(u,v) + R(v,w)` iff `v` lies on every
u–w current path — a genuinely new statement needing
current-uniqueness machinery).
