# Proposal: Band Davis–Kahan Difference Form — the Equal-Rank Identity's First Consumer

**Status:** **DELIVERED 2026-08-24** (run `20260824T102440Z-run-1`) —
Steps 0+1 in one run per the sibling precedent; see the delivery
record at the bottom. Zero new axioms (count stays 9; `#print axioms`
via `wip/bdkd_axcheck.lean` on all 5 public + 21 QA declarations reads
only `propext, Classical.choice, Quot.sound`, every one). QA 1852 →
1873 (`BandDavisKahanDiff_QA` a new file at 21 by the generator
metric).

Assessed from `Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/
{BandDavisKahan,ProjectionGap}.lean`, `Scaffold/Mathlib/GraphTheory/
{Band,PolyFilter,Spectral}.lean`, and
`Scaffold/QA/Perturbation/BandDavisKahan_QA.lean` (the exact statement
shapes and reusable fixtures cited below), with the route worked
through by hand in Section "The assembly" before any Lean was written.

## The obligation this discharges

The delivered band Davis–Kahan product theorem's own recorded open
follow-on (`proposals/band-davis-kahan.md`, Delivery record, "Open
follow-ons", first bullet; the previous run's recorded next handoff;
`docs/6_SGT_BACKLOG.md` item 9's "What remains on this axis"): the
**difference form** `‖P_A(S) − P_B(S′)‖` — the statement shape
consumers of perturbation stability actually want (the
subspace-distance/sin-Θ form), as against the product form delivered
2026-08-24.

**Leverage, threefold:**

1. **The first consumer of the equal-rank identity.**
   `ProjectionGap.l2OpNorm_sub_eq_of_rank_eq` (`‖P − Q‖ = ‖(I−Q) * P‖`
   for equal-rank orthogonal projectors) was delivered 2026-08-21 as
   "the Davis–Kahan Step-1 component" for the *half-line* theorem —
   but the Duhamel route consumed it zero times and no other consumer
   exists. Per `docs/1_STRATEGY.md` § Load-bearing growth, a layer
   that has never carried weight is untested surface; this theorem
   consumes the identity's exact statement (both directions of the
   `le_antisymm` inside it, via the norm bound on `‖(I−Q) * P‖`), so
   a misstatement in the identity breaks this derivation loudly.
2. **The second consumer of the commutator/shift engine.** F1
   (compression) and range invariance are reused *verbatim* from the
   product delivery; only the expansion fact is re-derived at the
   complement projector. This tests the engine's modularity claim
   (recorded in the sibling proposal: "the per-mode engine of both the
   compression and the expansion steps").
3. **A rank-supplier interface.** The equal-rank hypothesis is the
   shape's one "supply-side" burden; this delivery lands
   `rank_bandProjector_eq_card` (rank = in-band eigenvalue count, via
   trace), making the hypothesis checkable by any consumer — the
   difference form becomes usable, not merely statable.

Run selection: the Active priority table held no High/Medium rows; of
the three natural candidates on record (directed-axis mixing — gated
on a *new* primitivity-shaped axiom admission; this item; wide-band
minimax filter designs — gated on scalar approximation theory absent
from the pinned Mathlib), this is the only one both named and
zero-axiom.

## Source

Route provenance (the statement is *proved*, not admitted — this
proposal adds no axiom):

- The classical statement: Davis & Kahan 1970, and Yu–Wang–Samworth
  2015 Theorem 1, in the **operator-norm difference (sin Θ) form** —
  the subspace distance bounded by the perturbation over the spectral
  gap (already indexed at `index/sources/davis_kahan_1970.md` for the
  half-line theorem).
- Kato, *Perturbation Theory for Linear Operators*, 2nd ed., 1976,
  Chapter I §4 — the equal-dimension gap identity consumed as the
  reduction step (already the cited source of
  `ProjectionGap.l2OpNorm_sub_eq_of_rank_eq`).
- Vershynin, *High-Dimensional Probability*, 2018, Thm 4.1.15–4.1.16
  — the shift technique's textbook packaging, re-run at the
  complement window.

Statement differences from the textbook packaging (recorded before
stating): windows are `bandProjector`'s own `(a, b]` convention; the
separation is **one-sided and eigenvalue-level** — B's *out-of-window*
eigenvalues lie δ-away from A's *window closure* `[a₁, b₁]` (the
classical one-sided-gap shape; no constraint on B's in-window
eigenvalues, which is the point — the clusters overlap); the
equal-dimension hypothesis is stated as equality of the projectors'
`Matrix.rank`; constant 1 at the one-sided gap (the classical
symmetric-gap statements carry 2 — we state exactly what is proved,
no overclaim). An interval-margin corollary (`a₂ + δ ≤ a₁`,
`b₁ + δ ≤ b₂` — B's window contains A's with δ-margin) discharges the
eigenvalue-level hypotheses for the common same-window-family case.

## Step-0 survey findings (recorded before any statement was frozen)

### Shelf facts verified present

1. **The equal-rank identity** `l2OpNorm_sub_eq_of_rank_eq` (public;
   handles the rank-0 corner internally — no positivity hypothesis to
   discharge), plus its parents
   `l2OpNorm_sub_eq_max_of_isSymm_idempotent` and
   `l2OpNorm_one_sub_mul_eq_of_rank_eq`.
2. **Projector algebra of the band projector.** Band's
   `bandProjector_symmetric`, `bandProjector_idempotent` (both needed
   to feed the identity and to make the complement `I − Q` an
   orthogonal projector); ProjectionGap's public
   `dotProduct_mulVec_self_le_of_isSymm_idempotent` (Pythagoras — the
   complement's contractivity) and
   `eigvalOf_isSymm_idempotent_mem` (the `{0,1}` spectrum — the rank
   supplier's key).
3. **The engine pieces** (same file, private — hence the decision to
   land in `BandDavisKahan.lean` as new sections rather than a new
   module): F1 compression
   (`norm_pack_shift_bandProjector_mulVec_le`), range invariance
   (`bandProjector_mulVec_shift_self`), the A/B split
   (`sub_one_mulVec_split`), the pack helpers, the band commutation
   (`mulVec_bandProjector_comm`, public) and the pairing engine
   (`l2OpNorm_le_of_abs_dotProduct_le`, Duhamel).
4. **Trace/eigenvalue counting.** Spectral's
   `eigvalOf_sum_eq_trace` (= trace), Mathlib's
   `Matrix.IsHermitian.rank_eq_card_non_zero_eigs` (rank = nonzero
   eigenvalue count; the `eigvalOf` bridge is definitional — the
   ProjectionGap idiom), `eigvecOf_inner` (unit eigenvectors) for the
   spectral-projector trace.
5. **QA fixtures.** `BandDavisKahan_QA`'s rotated `bdkB =
   !![1, 3/4; 3/4, 3]` (spectrum `{3/4, 13/4}` pinned from
   trace/determinant; eigen-direction constraints
   `bdkB_eigvec_{top,bot}_{dir,sq}` with the sign-independent
   coordinate squares `1/10`) and `bdkE_norm_le` (`‖diag13 − bdkB‖ ≤
   3/4`); `Band_QA`'s `diag13` pins (`diag13_eigvalOf_mem`,
   `band_diag13_low/high`, `spectralProjector_diag13_eq`) — all
   importable (QA-to-QA precedent).

### Gaps priced (to land in the delivery)

1. **Complement expansion** (the only genuinely new mathematical
   fact): for `z` fixed by `Q' := I − bandProjector B a₂ b₂`, the
   in-band eigencomponents vanish (idempotence + PolyFilter's band
   component action), so Parseval leaves
   `(r+δ)²‖z‖² ≤ ‖(B−cI)z‖²` under the eigenvalue-level separation.
2. **Complement commutation/contractivity**: `(B−cI) *ᵥ (Q' *ᵥ u) =
   Q' *ᵥ ((B−cI) *ᵥ u)` (pure algebra from the delivered band
   commutation) and `‖Q' *ᵥ w‖ ≤ ‖w‖` (Pythagoras at the complement
   projector).
3. **The rank supplier** `rank_bandProjector_eq_card` (public):
   trace of a threshold projector = count of eigenvalues ≤ c (the
   outer-product definition + `Finset.sum_comm` + unit eigenvectors);
   trace of the band projector = the in-band count (card split at
   `a ≤ b`); rank of a symmetric idempotent = its trace (the `{0,1}`
   spectrum + the nonzero-eigenvalue count).

### The assembly (worked through by hand)

Let `P := bandProjector A hA a₁ b₁`, `Q := bandProjector B hB a₂ b₂`,
`Q' := I − Q`, `c := (a₁+b₁)/2`, `r := (b₁−a₁)/2 ≥ 0`. The identity
gives `‖P − Q‖ = ‖Q' * P‖`. The product engine re-runs with `Q'` in
place of `Q`, verbatim except:

- `Q' * Q' = Q'` (complement idempotence — algebra from
  `bandProjector_idempotent`);
- the expansion fact at `Q'`-fixed `z`: components out-of-band only
  (gap 1 above), where the eigenvalue-level separation gives
  `|μ_j − c| ≥ r + δ` — the low side `μ ≤ a₂ → μ ≤ a₁ − δ` and the
  high side `b₂ < μ → b₁ + δ ≤ μ`;
- the split and contractivity steps at `Q'` (gap 2).

The master inequality `(r+δ) ‖(Q'*P) *ᵥ y‖ ≤ (r ‖Q'*P‖ + ‖A−B‖) ‖y‖`
transport through the pairing engine gives `δ ‖Q' * P‖ ≤ ‖A−B‖` —
the same r-cancellation as the product form, now with the
*two-component* window: the bounded A-window is load-bearing exactly
as before (finite `r` + invariance), and the complement window being
unbounded is harmless because the expansion side never needs a
containment radius — only the separation. This is the precise sense
in which the difference form is *easier* than the half-line product
form the Duhamel route had to work for.

## Committed statements

Public (namespace
`Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation`, new sections
of `Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean`, one new
import: ProjectionGap):

```lean
/-- Band projector rank = in-band eigenvalue count (the equal-rank
hypothesis supplier). -/
theorem rank_bandProjector_eq_card {V : Type} [Fintype V] [DecidableEq V]
    {M : Matrix V V ℝ} (hM : M.IsSymm) (a b : ℝ) (hab : a ≤ b) :
    (bandProjector M hM a b).rank =
      (Finset.univ.filter fun i =>
        a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b).card

/-- The difference form at eigenvalue-level one-sided separation:
B's out-of-window eigenvalues δ-away from A's window closure. -/
theorem l2OpNorm_bandProjector_sub_bandProjector_le
    {V : Type} [Fintype V] [DecidableEq V]
    {A B : Matrix V V ℝ} (hA : A.IsSymm) (hB : B.IsSymm)
    (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂)
    {δ : ℝ} (hδ : 0 < δ)
    (hrank : (bandProjector A hA a₁ b₁).rank
      = (bandProjector B hB a₂ b₂).rank)
    (hlo : ∀ j, eigvalOf B hB j ≤ a₂ → eigvalOf B hB j ≤ a₁ - δ)
    (hhi : ∀ j, b₂ < eigvalOf B hB j → b₁ + δ ≤ eigvalOf B hB j) :
    ‖bandProjector A hA a₁ b₁ - bandProjector B hB a₂ b₂‖ ≤ ‖A - B‖ / δ

/-- The interval-margin corollary: B's window contains A's with
δ-margin on both sides. -/
theorem l2OpNorm_bandProjector_sub_bandProjector_le_of_mem
    {V : Type} [Fintype V] [DecidableEq V]
    {A B : Matrix V V ℝ} (hA : A.IsSymm) (hB : B.IsSymm)
    (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂)
    {δ : ℝ} (hδ : 0 < δ)
    (hrank : (bandProjector A hA a₁ b₁).rank
      = (bandProjector B hB a₂ b₂).rank)
    (hlo : a₂ + δ ≤ a₁) (hhi : b₁ + δ ≤ b₂) :
    ‖bandProjector A hA a₁ b₁ - bandProjector B hB a₂ b₂‖ ≤ ‖A - B‖ / δ
```

The junk-band guards `a₁ ≤ b₁`, `a₂ ≤ b₂` are load-bearing twice:
for A's window (F1/invariance, as in the product form) and for B's
window — at `a₂ > b₂` the band projector is the *negated* band, `Q`
is not a projector, and both the identity's hypothesis and `Q'`'s
idempotence die.

## QA plan (`Scaffold/QA/Perturbation/BandDavisKahanDiff_QA.lean`)

On the reused fixtures (`diag13` with spectrum `{1, 3}`, `bdkB` with
spectrum `{3/4, 13/4}`, `‖diag13 − bdkB‖ ≤ 3/4`):

1. **The rotated positive witness** (eigenvalue-level form, equal
   windows `(−1, 2]` both): rank equality *supplied through the new
   rank lemma* (count `1` on each side, from the pinned spectra);
   separation at δ = 3/4 (B's out-of-window eigenvalue `13/4 ≥
   b₁ + δ = 2 + 3/4`; low side vacuous); theorem bound `‖P − Q‖ ≤
   ‖A−B‖/δ ≤ 1`; raw route pins `‖P − Q‖ ≥ 1/√10` completely
   independently: `(P − Q) *ᵥ e₀ = e₀ − Q *ᵥ e₀` with `Q *ᵥ e₀`
   resolved through B's eigenbasis to the sign-independent value
   `(9/10, −3/10)` (the `(3,−1)` direction + `1/10` coordinate
   squares), norm lower bound through the delivered action bound.
   Cross-check `1/10 ≤ 1`. Coherence witness: `((I−Q) * P) *ᵥ e₀`
   pinned equal to `(P−Q) *ᵥ e₀` — the identity's content exhibited
   numerically.
2. **The ε = 0 attainment** (A = B = diag13, identical windows
   `(−1, 2]`, δ = 1/2 — separation genuinely holds: eigenvalue `3 ≥
   5/2`): the theorem reads `‖P − Q‖ ≤ 0`, so `‖P − Q‖ = 0`,
   attained — `P = Q = diag(1,0)` pinned from the imported
   `band_diag13_low`.
3. **The margin-corollary instance**: B's window `(−2, 3]` (captures
   `3/4` only) at δ = 1 — margins `−2 + 1 ≤ −1`, `2 + 1 ≤ 3` —
   bound `≤ 3/4`, raw lower `1/√10` by the same eigenbasis route at
   the new window.
4. **The fence — rank load-bearing, refuted in proved form**:
   A = B = diag13, A's window `(3/2, 5/2]` (captures no eigenvalue →
   `P = 0`, rank 0), B's window `(5/2, 7/2]` (captures `3` → `Q =
   diag(0,1)`, rank 1); every *other* hypothesis verified (window
   guards, δ = 1/2 > 0, `hlo`: eigenvalue `1 ≤ a₂ = 5/2 → 1 ≤ a₁ − δ
   = 1` ✓, `hhi` vacuous); the hypothesis-free conclusion
   `‖P − Q‖ = 1 ≤ 0` refuted (norm ≥ 1 through the action bound at
   `e₁`); the rank difference proved through the new rank lemma
   (counts 0 vs 1) — exactly `hrank` isolated.

## Verification plan

Spike first (`wip/bdkd_spike.lean`), then `lake env lean` on the
module and QA (zero errors/warnings), explicit `lake build` targets,
an axiom check via a `wip/` file over every new public + QA
declaration (the standard three only — nothing conditional), full
`lake build`, `lint_axioms` (count stays 9), `check_citations`,
`check_markdown_links`, scoreboard regeneration. Records: this
document, `proposals/README.md`, README module table + counts, the
radar QA axis, the scoreboard, `index/map/perturbation.md`,
`index/sources/davis_kahan_1970.md` (the difference form noted),
backlog item 9, the execution plan, the activity log. (No umbrella
change — the content lands in an already-imported module.)

## Delivery record (2026-08-24, run `20260824T102440Z-run-1`)

Delivered exactly at the committed shapes, in new sections of
`Perturbation/BandDavisKahan.lean` (one new import: ProjectionGap) —
the decision to extend the existing module rather than open a sibling
paid off exactly as planned: the engine reuses the *private* helpers
(F1 compression, range invariance, the A/B split, the `pack`
machinery) verbatim, and the core assembly was green on its first
complete compile — the spike phase here was in-place module editing
with `lake env lean` on the file itself, the risk concentrated instead
in the rank supplier and QA (the rounds below).

- **Pin techniques (the recurring fixes).** The scalar-position trap:
  `(μ² − μ) • v` needs `sub_smul` (the subtraction is in the *scalar*),
  not `smul_sub` — and the goal's `(μ * μ) • v` must become
  `μ • μ • v` via `mul_smul` before the `← hL` rewrites of the
  eigen-equation chain. `sub_mul` at this pin is *left*-subtraction
  `(a − b) * c`; `a * (b − c)` is `mul_sub`. `Matrix.trace_def` does
  not exist — unfold with `Matrix.trace, Matrix.diag_apply`. The
  `Fin.mk`-index trap re-hit in the exact recorded form: `fin_cases`
  leaves `(fun i => i) ⟨0, ⋯⟩`-form indices that defeat positional
  `rw` against literal-indexed facts; the typed-`have` bridge
  (`have ha : eigvalOf … 0 = 3 / 4 := hi` — defeq by proof
  irrelevance) is the robust route (the Band_QA idiom), as is
  `show`-at-the-defeq-goal. Coefficient cleanup after `if_pos`/
  `if_neg` needs *iterating* `zero_mul` (`(0 * v₀) * vₖ → 0 * vₖ → 0`)
  — `simp only [one_mul, zero_mul, add_zero]` (which iterates) beats a
  `rw` chain that strands the second `0 * _`. And `rw` rewrites only
  the *first-matched instantiation*: two `‖pack xᵢ‖` occurrences with
  different vectors `x₁ ≠ x₂` need two `norm_euclidean_eq_sqrt`
  rewrites, not one.

- **The mathematical content, as delivered.** The complement-expansion
  lemma `norm_pack_shift_apply_ge_compl` is the mirror of the product
  form's F2 — for vectors fixed by `Q' = 1 − Q_band(B)`, the *in-band*
  components vanish (from `Q_band *ᵥ z = 0`, itself extracted from the
  fixpoint equation by `sub_sub_cancel`), so Parseval leaves exactly
  the out-of-band modes where `hfar` lives; the master inequality and
  r-cancellation then transfer unchanged. The rank supplier's key
  sub-fact is the *exact* spectrum `{0,1}` of a symmetric idempotent
  (`eigvalOf_isSymm_idempotent_sq`, new private: apply `S² = S` to the
  eigen-equation) — the shelf's `eigvalOf_isSymm_idempotent_mem` gives
  only `[0,1]`, which cannot identify count-nonzero with trace; with
  the exact form, rank = trace = in-band count.

- **QA delivered at the four mandated sections**, all on the reused
  fixtures: (1) `bdkd_rotated_QA` — the rank equality *supplied
  through the new supplier* (counts 1 = 1 from the pinned spectra),
  separation at δ = 3/4, theorem bound `≤ 1` against the raw lower
  `√(1/10)` (the eigenbasis route `bdkd_Qe0_of_mem` —
  window-parametric, sign-independent, `Q *ᵥ e₀ = ![9/10, −3/10]`
  from the `(3,−1)` direction and the `9/10`/`1/10` coordinate
  squares, no `eigvecOf` value assumed), plus `bdkd_coherence` pinning
  `((1−Q) * P) *ᵥ e₀ = (P − Q) *ᵥ e₀` by two independent raw routes —
  the consumed identity's content exhibited numerically; (2)
  `bdkd_zeroE_attained` (A = B, identical windows, separation
  genuinely holding at δ = 1/2 via the out-of-window eigenvalue 3)
  with the independent zero pin `bdkd_zeroE_raw`; (3) the margin
  instance `bdkd_margin_QA` at B's window `(−2, 3]`, δ = 1, bound
  `≤ 3/4` vs raw `√(1/10)`; (4) the rank fence `bdkd_rank_fence` —
  A = B = diag13, windows `(3/2, 5/2]` (empty, rank 0 via the
  supplier) vs `(5/2, 7/2]` (occupied, rank 1), every other
  hypothesis verified (`hlo` at `1 ≤ 5/2 → 1 ≤ 3/2 − 1/2` exact;
  `hhi` vacuous), the hypothesis-free conclusion `‖P − Q‖ ≤ 0`
  refuted with the norm lower-bounded by `1` at `e₁` — and
  `bdkd_fence_only_rank_fails` proving the rank equality is the
  *only* failing hypothesis.

- **Verification.** `lake env lean` on the module and the QA file —
  zero errors, zero warnings each; `lake build
  Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan`
  ✔ (2192/2192) and `lake build
  Scaffold.QA.Perturbation.BandDavisKahanDiff_QA` ✔ (2195/2195);
  `#print axioms` via `wip/bdkd_axcheck.lean` on all 26 declarations —
  `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔
  (2260 targets, +1 for the new QA module, "Build completed
  successfully"; zero warnings in the changed modules)**;
  `lint_axioms` (**9**, unchanged), `check_citations`,
  `check_markdown_links` pass; scoreboard regenerated (**1873/9/0**,
  idempotent). Records updated: this document, `proposals/README.md`,
  README (1873; module-table row), the radar (QA axis synced
  1852/46 → 1873/47, held 4.0), the scoreboard (all four verification
  rows + a new interpretation bullet + the previous product-form
  bullet's forward-looking clause de-staled), `index/map/perturbation.md`
  (section extended + 5 declaration rows + the Deferred-Work note
  de-staled), `index/sources/davis_kahan_1970.md` (the difference-form
  mapping row), backlog item 9, the execution plan, the activity log.
  No umbrella change (the content lands in an already-imported module).
  Nothing committed; prior runs' uncommitted deliveries and the
  untracked `docs/scaffold.jpeg` preserved untouched.

- **Open follow-ons.** The eigenvalue-cluster-separated generalization
  (separation stated between the clusters' spectra rather than through
  windows — closer to YWS Theorem 1's literal shape) would compose the
  delivered eigenvalue-level separation with a window-existence
  argument; a two-sided version (separation also from A's
  out-of-window side) would give the symmetric-gap constant-2 form;
  and the Kato/Davis–Kahan locators carry the standing
  verify-against-physical-copy caveat.
