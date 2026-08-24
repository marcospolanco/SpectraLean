# Proposal: Band Davis–Kahan — Perturbation Stability for Band Projectors

**Status:** **DELIVERED 2026-08-24** (run `20260824T081731Z-run-1`) —
Steps 0+1 in one run per the PageRank/PolyFilter precedent; see the
delivery record at the bottom. Zero new axioms (count stays 9;
`#print axioms` via `wip/bdk_axcheck.lean` on all 5 public + 20 QA
declarations reads only `propext, Classical.choice, Quot.sound`, every
one). QA 1832 → 1852 (`BandDavisKahan_QA` a new file at 20 by the
generator metric).

Assessed from `Scaffold/Mathlib/GraphTheory/Band.lean`,
`Scaffold/Mathlib/GraphTheory/Spectral.lean`,
`Scaffold/Mathlib/GraphTheory/PolyFilter.lean` (delivered 2026-08-24,
present in the worktree), and
`Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/Duhamel.lean`
(the exact statement shapes cited below), with the route worked through
by hand in Section "The crux" before any Lean was written.

## The obligation this discharges

`docs/6_SGT_BACKLOG.md` item 9 (opened 2026-08-21 by the Davis–Kahan
Step-0/1 survey of `proposals/discharge-perturbation-axioms.md`):
a **bounded-window ("band") Davis–Kahan theorem** — both projectors
select *finite* spectral windows, δ-separated — proved by the survey's
recorded algebraic commutator/shift technique, "a different, new,
axiom-free statement this technique proves cheaply with no calculus at
all." The survey explicitly forbade starting this inside its own
Step-1/2 runs and required exactly this document plus a Step-0 survey
first. This is that document; the run selection follows the recorded
handoff (the Active priority table held no High/Medium rows after the
PolyFilter delivery; of the three natural candidates on record —
directed-axis mixing (gated on a *new* primitivity-shaped axiom
admission), this item, and a wide-band minimax consumer (none named) —
this is the only one that is both backlog-named and zero-axiom).

**Leverage:** the first perturbation-stability result for
`GraphTheory.Band`'s projectors — the module's first
perturbation-theory consumer, exactly symmetric to the previous run's
PolyFilter being its first approximation-theory consumer. It is also
the second consumer of the just-delivered PolyFilter component-action
interface (`eigvecOf_dotProduct_bandProjector_mulVec`), and the first
composition of the Band and Perturbation areas. Load-bearing per the
strategy's falsifiability test: the proof consumes the exact shapes of
Band (idempotence, eigenbasis action), Spectral (Parseval,
`dotProduct_eigvecOf_mulVec`), PolyFilter (the band component action,
whose `a ≤ b` guard is load-bearing for the indicator form), and
Duhamel (the pairing engine `l2OpNorm_le_of_abs_dotProduct_le` +
Cauchy–Schwarz `abs_dotProduct_le`) in one statement.

Not in scope (recorded, not attempted): the *difference* form
`‖P_A(S) − P_B(S′)‖` for overlapping/complementary windows — that needs
the equal-rank projector identity (delivered:
`ProjectionGap.l2OpNorm_sub_eq_of_rank_eq`) and is the shape the
Duhamel route already covers at the half-line; and any eigenvalue-list
comparison statement. The product form below is the classical
primitive the survey priced.

## Source

Route provenance (the statement is *proved*, not admitted — this
proposal adds no axiom):

- Vershynin, R., *High-Dimensional Probability*, Cambridge University
  Press, 2018 — Thm 4.1.15–4.1.16 as recorded by the 2026-08-21 survey
  (`index/sources/vershynin_hdp.md`, Chapter 4 note: "a textbook
  packaging of a commutator/shift proof technique"). Locator carried
  with the repo's standing caveat (numbers to be confirmed against a
  physical or publisher copy; not invented here).
- The classical statement: Davis & Kahan 1970; Yu–Wang–Samworth 2015,
  Theorem 1 (the constant-1 operator-norm product form at
  eigenvalue-cluster separation) — both already indexed at
  `index/sources/davis_kahan_1970.md` for the half-line theorem. The
  band product form here is the window-separated specialization: no
  sorted-spectrum index `k`, separation stated on the *intervals*, the
  constant 1 preserved.

Statement differences from Vershynin's packaging (recorded before
stating): the windows are `bandProjector`'s own `(a, b]` convention
(not an arbitrary Borel set); the conclusion is the ℓ² operator norm
of the *product* `B_band * A_band` (not `sin Θ` between subspaces —
no rank hypothesis is needed or stated, and the product is what a
consumer multiplies by); separation is interval separation
(`b₁ + δ ≤ a₂`), from which eigenvalue-cluster separation follows by
interval arithmetic (delivered as part of the proof, so consumers
state only intervals).

## Step-0 survey findings (recorded before any statement was frozen)

### Shelf facts verified present

1. **Band component action, both slots.** PolyFilter (2026-08-24)
   delivers `eigvecOf_dotProduct_spectralProjector_mulVec` and
   `eigvecOf_dotProduct_bandProjector_mulVec`:
   `v i ⬝ᵥ (B_{a,b} *ᵥ y) = χ_{(a,b]}(λ i) * (v i ⬝ᵥ y)`, with the
   `a ≤ b` guard load-bearing (the total definition is the *negated*
   band at `a > b`). This is the per-mode engine of both the
   compression and the expansion steps below.
2. **Parseval + eigenaction.** Spectral's `dotProduct_eigvecOf`
   (`x ⬝ᵥ y = ∑ i (v i ⬝ᵥ x)(v i ⬝ᵥ y)`), `dotProduct_eigvecOf_mulVec`
   (`v i ⬝ᵥ (M *ᵥ x) = μ i (v i ⬝ᵥ x)`), and the eigen-equation
   extraction at `eigvecOf` (via `mulVec_eigenvectorBasis`).
3. **Idempotence + eigenbasis action of the band projector.** Band's
   `bandProjector_idempotent`, `bandProjector_mulVec_eigvecOf_self`,
   `_eq_zero_left`, `_eq_zero_right`, and the disjoint-band product
   zero `bandProjector_mul_bandProjector_eq_zero` (QA's ε = 0
   attainment consumes it).
4. **The norm/pairing engine.** Duhamel's
   `l2OpNorm_le_of_abs_dotProduct_le` (upper bound on `‖M‖` from
   pairings), `abs_dotProduct_le` (Cauchy–Schwarz in the plain
   packaging), `norm_euclidean_eq_sqrt` (the packaged-vector norm);
   Mathlib's `Matrix.cstar_norm_def` + `toEuclideanCLM` +
   `ContinuousLinearMap.opNorm_le_bound` (the Resolvent/PolyFilter
   spine, at the scoped `Matrix.L2OpNorm` instance this area uses).
5. **The 2×2 QA pinning idiom.** Band_QA's trace/determinant spectrum
   pins for `diag13` and the eigen-equation direction constraints; the
   threshold/band projector entrywise pins are importable (QA-to-QA
   precedent).

### Gaps priced (both to land in the new module)

1. **The vector action bound** `‖M *ᵥ v‖ ≤ ‖M‖ ‖v‖` in the plain
   sqrt-packaging. Absent from the pinned Mathlib at Matrix type (no
   `opNorm_mulVec_le` anywhere in the pin) and from the Scaffold
   shelf; derivable in ~10 lines through `cstar_norm_def` +
   `toEuclideanCLM_piLp_equiv_symm` + `ContinuousLinearMap.le_opNorm`.
   Landed as a public interface lemma (reusable by every future
   perturbation consumer).
2. **Operator↔projector vector commutation** `M *ᵥ (P_{a,b} *ᵥ u)
   = P_{a,b} *ᵥ (M *ᵥ u)` at `M`'s own band projector. The 2026-08-21
   survey spike-verified the threshold form but it was never landed
   (the Duhamel route did not need it). Componentwise proof: both
   sides' eigencomponents are `χ(μ i) μ i (v i ⬝ᵥ u)`; equality of
   vectors from equality of all eigencomponents (a 3-line helper via
   `eigvecOf_expansion_apply`). Landed as a public interface lemma
   with the threshold form.

### The crux — the shift argument worked through by hand

Let `P := bandProjector A hA a₁ b₁` (A's window), `Q := bandProjector B
hB a₂ b₂` (B's window), `c := (a₁+b₁)/2`, `r := (b₁−a₁)/2 ≥ 0`. The
interval hypothesis `b₁ + δ ≤ a₂` (right separation; the mirror case
below) gives, by interval arithmetic:

- every A-eigenvalue in `(a₁, b₁]` lies in `[c−r, c+r]`;
- every B-eigenvalue in `(a₂, b₂]` lies at distance `> r+δ` from `c`.

Two per-vector facts (both by PolyFilter's component action + Parseval
in the respective matrix's own basis):

- **(F1) compression:** `‖(A−cI) *ᵥ (P *ᵥ y)‖² ≤ r² (y ⬝ᵥ y)` — the
  shifted action's eigencomponents are `(λ i − c) χ_i (v i ⬝ᵥ y)`,
  each factor `|λ i − c| ≤ r` in-band and `χ i = 0` out-of-band.
- **(F2) expansion:** for `z` with `Q *ᵥ z = z`,
  `(r+δ)² (z ⬝ᵥ z) ≤ ‖(B−cI) *ᵥ z‖²` — the components of `z` itself
  are supported in-band (idempotence + component action), where
  `|μ j − c| > r+δ`.

**The trap, worked through before writing it down:** the naive
single-shift assembly

  `(B−cI) *ᵥ z = Q *ᵥ ((A−cI) *ᵥ (P *ᵥ y)) + Q *ᵥ ((B−A) *ᵥ (P *ᵥ y))`
  [vector commutation, B's side]

bounds the first term by `r ‖y‖` (F1 + contractivity), giving
`(r+δ) ‖Q P‖ ≤ r + ‖A−B‖` — the spread term *stranded*, exactly the
recorded catch that killed this technique for the half-line window
(there `r` is the unbounded lower-cluster spread). **The rescue, and
this theorem's mathematical content:** bound the first term by
`r ‖QP‖ ‖y‖` instead of `r ‖y‖`, via **range invariance** —
`w := (A−cI) *ᵥ (P *ᵥ y)` has all eigencomponents supported in A's
band (shift of a supported vector), so `P *ᵥ w = w` and
`Q *ᵥ w = (Q*P) *ᵥ w`, giving
`‖Q *ᵥ w‖ ≤ ‖Q*P‖ ‖w‖ ≤ ‖QP‖ · r ‖y‖`. The `r` now appears on both
sides and cancels:

  `(r+δ) ‖(Q*P) *ᵥ y‖ ≤ (r ‖QP‖ + ‖A−B‖) ‖y‖` for all `y`
  ⟹ `(r+δ) ‖QP‖ ≤ r ‖QP‖ + ‖A−B‖` [pairing engine]
  ⟹ `δ ‖QP‖ ≤ ‖A−B‖`.

Constant 1, purely algebraic — no integral, no `HasDerivAt`, no
sorting, no rank counting. The bounded window is load-bearing twice:
it makes `r` finite (F1) *and* it makes the invariance step available
(the half-line projector's range is not invariant under any shift
that would rescue the same assembly — which is why the two
Davis–Kahan statements are genuinely different theorems).

## Committed statements

Public (namespace
`Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation`, module
`Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean`, imports
PolyFilter + Duhamel, `open scoped Matrix Matrix.L2OpNorm`):

```lean
/-- B's band strictly above A's band. -/
theorem l2OpNorm_bandProjector_mul_bandProjector_le_of_lt
    {V : Type} [Fintype V] [DecidableEq V]
    {A B : Matrix V V ℝ} (hA : A.IsSymm) (hB : B.IsSymm)
    (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : a₁ ≤ b₁) (hb₂ : a₂ ≤ b₂)
    {δ : ℝ} (hδ : 0 < δ) (hsep : b₁ + δ ≤ a₂) :
    ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖ ≤ ‖A - B‖ / δ

/-- B's band strictly below A's band. -/
theorem l2OpNorm_bandProjector_mul_bandProjector_le_of_gt
    {V : Type} [Fintype V] [DecidableEq V]
    {A B : Matrix V V ℝ} (hA : A.IsSymm) (hB : B.IsSymm)
    (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : a₁ ≤ b₁) (hb₂ : a₂ ≤ b₂)
    {δ : ℝ} (hδ : 0 < δ) (hsep : b₂ + δ ≤ a₁) :
    ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖ ≤ ‖A - B‖ / δ
```

plus the two interface lemmas priced above (`l2OpNorm_mulVec_le` in
the sqrt-packaging; `mulVec_bandProjector_comm` and its threshold
parent), with private helpers (components-equality, band
contractivity of the action, F1, F2, range invariance, and the
eigenvalue-window engine shared by both orientations).

The junk-band guards `a₁ ≤ b₁`, `a₂ ≤ b₂` are load-bearing (the band
definition is the *negated* band at reversed endpoints — the PolyFilter
component-action guard).

## QA plan (`Scaffold/QA/Perturbation/BandDavisKahan_QA.lean`)

On the fixtures `diag13 = !![1,0;0,3]` (reused from `Band_QA` by
QA-to-QA import — its threshold/band projector entrywise pins come
along) and the rotated `B = !![1, 3/4; 3/4, 3]` (eigenvalues
`{3/4, 13/4}` pinned from trace `4` and determinant `39/16`, the
Band_QA idiom; `‖A − B‖ = 3/4` from the off-diagonal perturbation's
own `{±3/4}` spectrum):

1. **The rotated positive witness** (right separation): A's band
   `(1/2, 3/2]` (λ = 1), B's band `(3, 4]` (μ = 13/4), δ = 3/2 —
   theorem bound `‖QP‖ ≤ 1/2`; the raw route pins `‖QP‖ ≥ 1/√10`:
   `(Q*P) *ᵥ e₁ = Q *ᵥ e₁` (the imported diag13 pin `P *ᵥ e₁ = e₁`),
   its squared norm resolved through B's eigenbasis (PolyFilter's
   component action ×2) to `∑_in-band (v j 0)² = 1/10` — the
   coordinate pinned from the eigen-equation direction constraint
   (`v j 1 = 3 v j 0`, unit norm), no `eigvecOf` value assumed — and
   the norm lower bound closed through the delivered action bound at
   `e₁`. Cross-check `1/10 ≤ 1/4`.
2. **The ε = 0 attainment** (A = B = diag13, disjoint bands): the
   theorem reads `‖QP‖ ≤ 0`, so `‖QP‖ = 0` — attained — and the
   product is pinned zero entrywise through Band's
   `bandProjector_mul_bandProjector_eq_zero` (disjoint bands) plus
   raw literal multiplication.
3. **The fence — separation load-bearing, refuted in proved form**:
   A = B = diag13 with *identical* windows `(1/2, 3/2]` (every
   `hsep`-shaped hypothesis fails: `3/2 + δ ≤ 1/2` for no `δ > 0`):
   `QP = P = diag(1,0)` pinned from the imported pins, `0 < ‖QP‖`
   from the action bound at `e₁`, and the hypothesis-free conclusion
   `‖QP‖ ≤ ‖A−B‖/δ = 0` refuted.
4. **The mirror instance** (left separation, `_of_gt`): A's band
   `(2, 4]` (λ = 3), B's band `(1/2, 3/2]` (μ = 3/4), δ = 1/2 — bound
   `‖QP‖ ≤ 3/2`, raw lower `‖QP‖ ≥ 1/√10` at `e₂` (the `(3,−1)`
   eigen-direction), the mirror's interval arithmetic exercised.

## Verification plan

Spike first (`wip/bdk_spike.lean`), then `lake env lean` on the module
and QA (zero errors/warnings), explicit `lake build` targets, an
axiom check via a `wip/` file over every new public + QA declaration
(the standard three only — nothing conditional), full `lake build`,
`lint_axioms` (count stays 9), `check_citations`,
`check_markdown_links`, scoreboard regeneration. Records: this
document, `proposals/README.md`, README module table + counts, the
radar QA axis, the scoreboard, `index/sources/vershynin_hdp.md`
(Chapter 4 note updated from route-reference to the delivered
mapping), `index/map/perturbation.md`, backlog item 9, the umbrella
`Scaffold.lean`, the execution plan, the activity log.

## Delivery record (2026-08-24, run `20260824T081731Z-run-1`)

Delivered exactly at the committed shapes. The spike
(`wip/bdk_spike.lean`) took several rounds; the fixes that recur are
recorded here as the pin-technique list for future consumers of the
same idiom:

- **Pin techniques.** `Matrix.mulVec_mulVec` takes the vector FIRST
  (`v M N : M *ᵥ N *ᵥ v = (M * N) *ᵥ v`) and is right-associative in
  display — as a `rw` it fires on the first-unified instance only;
  nested associativity identities are robust only as explicit
  `calc` steps with fully-applied lemma arguments (underscore
  arguments cause `whnf` timeouts on these term sizes). `rw` rewrites
  *all* instances of the first-unified pattern — one `norm_pack_sq`
  call consumes both norms of a `‖x‖ ≤ r * ‖y‖` goal, but
  `mul_pow` must come first to expose the second. `rw`-chains that
  mix `if`-splitting with products strand when the two `if`s
  instantiate together: rewrite the eigenvalues first, then let
  **`norm_num` evaluate the `ite` conditions** (it reduces
  `(3 : ℝ) < 3 / 4` to `False` and normalizes `0 * v * (0 * v)` to
  `0`, leaving exactly the coordinate-square goal for the
  direction-constraint lemma). `abs_le_of_sq_le_sq` yields the abs on
  the LEFT side only — strip with one `abs_of_nonneg`, not two.
  `le_div_iff₀` is `(a ≤ b / c ↔ a * c ≤ b)`; both projection
  directions are needed in one proof (`.2` to divide the master
  inequality, `.1` to re-assemble) and neither is `div_le_iff₀`.
  The `pack`-packaging needs a small `pack_add`
  (`WithLp.equiv_add` + injectivity) before `norm_add_le` applies.
  QA-side: the `Fin 2` eta-expansion trap re-hit (the `show`-at-literal
  technique from Band_QA is load-bearing), and `linear_combination`
  with a fixed rational coefficient is the robust route for
  eigen-equation direction constraints (`(4/3) * h` for
  `v1 = 3 * v0` at the `13/4` mode, `4 * h` for `v0 = -3 * v1` at
  `3/4`).

- **QA delivered at the four mandated sections**, all on the rotated
  fixture `bdkB = !![1, 3/4; 3/4, 3]` (eigenvalues `{3/4, 13/4}` from
  trace `4` / determinant `39/16`) against `diag13` imported from
  `Band_QA`: (1) `bdk_rotated_QA` — raw lower `√(1/10) ≤ ‖Q * P‖`
  (the eigenbasis route with `bdk_QPe0_sq`: per-index band membership
  from the pinned spectrum, the surviving coordinate square from
  `bdkB_eigvec_top_sq`, the norm lower bound through the delivered
  `l2OpNorm_mulVec_le` at `e₀`) joined with the theorem upper bound
  `‖Q * P‖ ≤ ‖diag13 − bdkB‖ ≤ 3/4` (the perturbation norm bounded
  by the pairing engine with the swap trick); (2) the ε = 0
  attainment `bdk_zeroE_attained` (windows `(−1, 2]`/`(5/2, 4]`,
  bound `≤ 0`, norm `= 0`) with the independent zero pin
  `bdk_zeroE_raw` through Band's disjoint-band law and the new
  window pin `band_diag13_52`; (3) the fence `bdk_overlap_fence`
  (identical windows: `‖P * P‖ = ‖diag(1,0)‖ ≥ 1 > 0` = RHS, refuted
  in proved form) with `bdk_overlap_sep_impossible` exhibiting every
  `hsep`-shaped hypothesis unfulfillable; (4) the mirror
  `bdk_mirror_QA` at δ = 1/2 (`_of_gt`, raw lower `√(1/10)` at `e₁`
  through the bottom-mode constraint `v0 = −(3 * v1)`).

- **Verification.** `lake env lean` on the module and the QA file —
  zero errors, zero warnings each; `lake build
  Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan`
  ✔ (2192/2192) and `lake build
  Scaffold.QA.Perturbation.BandDavisKahan_QA` ✔ (2194/2194);
  `#print axioms` via `wip/bdk_axcheck.lean` on all 25 declarations —
  `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔
  (2260 targets, +1, "Build completed successfully"; zero warnings in
  the changed modules)**; `lint_axioms` (**9**, unchanged),
  `check_citations`, `check_markdown_links` pass; scoreboard
  regenerated (**1852/9/0**, idempotent). Records updated per the plan
  above. Nothing committed; prior runs' uncommitted deliveries and
  the untracked `docs/scaffold.jpeg` preserved untouched.

- **Open follow-ons.** The *difference* form `‖P_A(S) − P_B(S')‖` for
  overlapping/complementary windows (consumes the delivered
  equal-rank identity `ProjectionGap.l2OpNorm_sub_eq_of_rank_eq` —
  the natural next Band×Perturbation statement, not yet proposed);
  the eigenvalue-cluster-separated generalization (separation on the
  spectra rather than the intervals, closer to YWS Theorem 1's shape);
  the Vershynin locator confirmation against a physical copy
  (standing repo rule).
