# Proposal: Band Davis–Kahan Cluster Form — the eigenvalue-cluster-separated (pairwise) difference theorem

**Status:** **DELIVERED 2026-08-24** (run `20260824T122219Z-run-1`) —
Steps 0+1 in one run per the sibling precedent; see the delivery record
at the bottom. Zero new axioms (count stays 9; `#print axioms` via
`wip/bdkc_axcheck.lean` on all 3 public + 37 QA declarations reads only
`propext, Classical.choice, Quot.sound`, every one). QA 1873 → 1908
(`BandDavisKahanCluster_QA` a new file at 35 by the generator metric).

**Proposed** 2026-08-24 (run `20260824T122219Z-run-1`).

Assessed from `Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/
{BandDavisKahan,ProjectionGap,Duhamel}.lean` and the sibling QA files
(the exact statement shapes and reusable fixtures cited below), with the
route worked through by hand in Section "The assembly" before any Lean
is written.

## The obligation this discharges

The delivered difference-form theorem's own first recorded open
follow-on (`proposals/band-davis-kahan-difference.md`, Delivery record,
"Open follow-ons", first bullet; the previous run's recorded next
handoff; first-named candidate in both `docs/EXECUTION_PLAN.md` and the
activity log): the **eigenvalue-cluster-separated generalization** —
separation stated *between the clusters' spectra* rather than through
A's window closure, "closer to YWS Theorem 1's literal shape."

**Leverage, threefold:**

1. **Strictly weaker hypotheses, same constant.** The delivered
   `l2OpNorm_bandProjector_sub_bandProjector_le` hypotheses (B's
   out-of-window eigenvalues δ-away from A's *window closure*
   `[a₁, b₁]`) imply the pairwise hypothesis of this delivery, but not
   conversely: when A's cluster has an internal gap of width ≥ 2δ, a
   B eigenvalue can sit *inside the window* yet δ-away from *every*
   in-window A-eigenvalue — closure separation fails, pairwise
   separation holds. The new theorem covers exactly those
   configurations; the delivered one becomes a corollary-shape
   special case.
2. **The literal YWS Theorem 1 δ.** Per the shelf's own citation record
   (`DavisKahan.lean`, `davis_kahan_sin_theta` docstring), YWS
   Theorem 1's separation is `δ = inf{|λ̂ − λ| : λ in the population
   cluster, λ̂ in the sample outside-cluster set|}` at constant 1. The
   delivered band forms specialized that to interval/closure
   separation; this delivery states it at the literal pairwise form
   for band clusters (population = A's in-window spectrum, sample
   outside = B's out-of-window spectrum).
3. **A third load-bearing consumer of the same engine.** The
   complement-projector engine re-runs a third time, now with the
   shift `c, r` at the *cluster range* center/radius rather than the
   window's — testing the engine's modularity claim one step further
   (the core lemma takes arbitrary `c, r`, and here that generality is
   load-bearing: the window's own center/radius would strand `+ r`
   exactly as the product-form survey recorded).

Run selection: the Active priority table holds no High/Medium rows; of
the three natural candidates on record, this is the only one that is
both named and zero-axiom (directed-axis mixing is gated on a
*primitivity-shaped admission* — a decision a run cannot make;
wide-band minimax filter designs are gated on scalar approximation
theory absent from the pinned Mathlib).

## Source

Route provenance (the statement is *proved*, not admitted — this
proposal adds no axiom):

- Yu, Y., Wang, T., Samworth, R. J., "A useful variant of the
  Davis–Kahan theorem for statisticians", Annals of Statistics
  43(3):2028–2061, 2015, Theorem 1 — the pairwise mixed separation at
  constant 1 (already the cited statement source of
  `davis_kahan_sin_theta`; the paper read at arXiv:1405.0680 during the
  2026-08-21 Step-0 survey).
- Vershynin, *High-Dimensional Probability*, 2018, Thm 4.1.15–4.1.16 —
  the shift technique's textbook packaging, re-run at the cluster-range
  center/radius.

Statement differences from the textbook packaging (recorded before
stating): windows are `bandProjector`'s own `(a, b]` convention, and
the "cluster" on each side is the window's eigenvalue class (the band
projector's own cluster); the separation is **one-sided** (population =
A, sample = B; no constraint between A's out-of-window and B's
in-window spectra, exactly the one-sided shape of both delivered band
forms); the equal-dimension hypothesis stays as projector-rank equality
(checkable through the delivered `rank_bandProjector_eq_card`);
constant 1. The **interior configuration** (a B eigenvalue strictly
inside A's cluster range, in an internal gap) is handled *inside the
proof* by the trivial regime — it forces `δ ≤ ‖A − B‖`, after which
`‖P − Q‖ ≤ 1 ≤ ‖A − B‖ / δ` — so the consumer never sees it. This is
mathematically necessary, not a convenience: at an interior `μ` the
shift technique cannot work at *any* `c, r` (every in-window λ within
`r` of `c` forces `|μ − c| < r + δ`), which is exactly why the
delivered closure-separation form needed the interior excluded and this
delivery needs the counting/expansion argument instead.

## Step-0 survey findings (recorded before any statement is frozen)

### Shelf facts verified present

1. **The engine** (`BandDavisKahan.lean`, private, same module — hence
   landing as new sections of that file per the sibling precedent):
   `l2OpNorm_one_sub_bandProjector_mul_bandProjector_le_core` at
   **arbitrary `c, r`** (not just the window's center/radius — the
   public theorems instantiate, the core does not), F1 compression,
   range invariance, the A/B split, `pack`, the pairing engine
   (`l2OpNorm_le_of_abs_dotProduct_le`, Duhamel).
2. **The identity** `l2OpNorm_sub_le_one_of_isSymm_idempotent` and
   `l2OpNorm_sub_eq_of_rank_eq` (Duhamel / ProjectionGap, both public,
   both already consumed in the sibling section — the trivial-regime
   branch needs the ≤ 1 form, the engine branch the identity).
3. **Component algebra**: `eigvecOf_dotProduct_bandProjector_mulVec`
   (PolyFilter), `dotProduct_eigvecOf` Parseval,
   `dotProduct_eigvecOf_mulVec` eigenaction, the eigen-equation
   `(isHermitian_of_isSymm hM).mulVec_eigenvectorBasis`,
   `eigvecOf_inner` (unit norm), `eq_of_forall_dotProduct_eigvecOf_eq`
   (basis injectivity, private in the module) — the interior expansion
   and the capture-equality lemma are both built from exactly these.
4. **Extremal eigenvalues of a Finset**: `Finset.min'`/`max'` with
   `min'_le`/`le_max'` and membership extraction — the cluster range
   `λmin, λmax` from `Finset.univ.filter` (nonempty exactly when the
   band rank is positive, via the delivered rank supplier).
5. **QA fixtures**: `diag13` / `band_diag13_low` / `diag13_card_band_low`
   (Band_QA, BandDavisKahanDiff_QA) and the rotated `bdkB` with its
   pinned spectrum `{3/4, 13/4}`, `bdkd_diff_e0_dot_of_mem` (raw lower
   `√(1/10)`), `bdkd_rank_eq`, `bdkE_norm_le` (BandDavisKahan_QA /
   BandDavisKahanDiff_QA) — importable QA-to-QA within the same domain
   (the delivered precedent).

### Gaps priced (to land in the delivery)

1. **The projector-free expansion** (the only genuinely new
   mathematical fact): `δ * ‖z‖ ≤ ‖(A − cI) *ᵥ z‖` whenever *every*
   A-eigenvalue is δ-away from `c` — F2 with no projector condition
   (all eigencomponents survive). At an interior out-of-window B
   eigenvalue `μ` with eigenvector `v` (unit, `Bv = μv`), this gives
   `δ ≤ ‖(A − μI)v‖ = ‖(A − B)v‖ ≤ ‖A − B‖` — the interior case's
   trivial regime. **No Weyl/`evals` bridge is needed**: the survey
   initially priced a positionwise-Weyl route through
   `weyl_inequality` + `evals_mem_eigvalOf`, but the eigenvector route
   above stays entirely inside the module's component idiom and avoids
   both the `evals` machinery and an `A + E` matrix rewrite.
2. **Capture-equality** (public): `bandProjector M a b =
   bandProjector M a' b'` whenever the two windows select the same
   eigenvalues — basis injectivity on the component action. This is
   the window-existence argument's transfer step, and an independently
   useful interface fact ("the cluster is a window-mod-class, not a
   window").
3. **The empty-cluster corner**: rank 0 on both sides (via the rank
   supplier) forces both projectors to 0 — a component-action
   vanishing lemma plus `Matrix.eq_zero_of_mulVec_eq_zero`.

### The assembly (worked through by hand)

Let `P := bandProjector A hA a₁ b₁`, `Q := bandProjector B hB a₂ b₂`,
and suppose A's window class is nonempty with range `[λmin, λmax]`
(`λmin`/`λmax` = min/max in-window eigenvalues; `a₁ < λmin ≤ λmax ≤
b₁` by definition).

**Dichotomy** (per out-of-window B eigenvalue `μ`, from pairwise +
`a₁ < λmin ≤ λmax ≤ b₁`): either `μ ≤ λmin − δ`, or `λmax + δ ≤ μ`, or
`μ` is *interior* (`λmin + δ ≤ μ ≤ λmax − δ` — pairwise kills `μ =
λmin`, `μ = λmax`, and the near-boundary bands). In the interior case
*every* A-eigenvalue is δ-away from `μ`: in-window by pairwise;
out-of-window-below `≤ a₁ < λmin ≤ μ − δ`; out-above `> b₁ ≥ λmax ≥
μ + δ`. So gap 1 fires and `δ ≤ ‖A − B‖`.

**Case split**: if `δ ≤ ‖A − B‖` the conclusion is the trivial regime
`‖P − Q‖ ≤ 1 ≤ ‖A − B‖ / δ`. Otherwise *no* interior `μ` exists, so
every out-of-window `μ` satisfies the range separation `μ ≤ λmin − δ`
or `λmax + δ ≤ μ`. Shrink A's window: `ā := (a₁ + λmin)/2 ∈ (a₁,
λmin)` and `b̄ := λmax` select exactly A's cluster (capture-equality),
and the engine runs at `c := (λmin + λmax)/2`, `r := (λmax − λmin)/2`:
in-band λ ∈ `[λmin, λmax]` gives `|λ − c| ≤ r` (F1); range separation
gives `|μ − c| ≥ r + δ` for out-of-window μ (F2′ at the complement) —
*exactly*, with no slack, which is why `c, r` must be the cluster
range's and not the window's (the window's `r` strands `+ r`; the
recorded catch). The equal-rank identity reduces `‖P − Q‖` to
`‖(I − Q) P‖` at the *original* projectors, capture-equality rewrites
`P` to the shrunk window, and the core closes at constant 1.

## Committed statement

Public (namespace
`Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation`, new sections
of `Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean`, **no new
imports** — everything consumed is already in the module or its three
imports):

```lean
/-- Two windows selecting the same eigenvalues give the same band
projector (the cluster is a window-mod-class). -/
theorem bandProjector_eq_of_forall_mem_iff {M : Matrix V V ℝ}
    (hM : M.IsSymm) (a b a' b' : ℝ)
    (hiff : ∀ i, (a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b)
      ↔ (a' < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b')) :
    bandProjector M hM a b = bandProjector M hM a' b'

/-- **Band Davis–Kahan, difference form, pairwise (cluster) separation.**
If the band projectors of `A` (window `(a₁, b₁]`) and `B` (window
`(a₂, b₂]`) have equal rank and every eigenvalue of `B` *outside* its
window is δ-away from every eigenvalue of `A` *inside* its window —
the literal YWS Theorem 1 separation — then `‖P_A − P_B‖ ≤ ‖A − B‖ / δ`
at constant 1. -/
theorem l2OpNorm_bandProjector_sub_bandProjector_le_of_pairwise
    (hA : A.IsSymm) (hB : B.IsSymm)
    (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂)
    {δ : ℝ} (hδ : 0 < δ)
    (hrank : (bandProjector A hA a₁ b₁).rank
      = (bandProjector B hB a₂ b₂).rank)
    (hsep : ∀ j, ¬(a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂) →
      ∀ i, a₁ < eigvalOf A hA i → eigvalOf A hA i ≤ b₁ →
      δ ≤ |eigvalOf B hB j - eigvalOf A hA i|) :
    ‖bandProjector A hA a₁ b₁ - bandProjector B hB a₂ b₂‖
      ≤ ‖A - B‖ / δ
```

The junk-band guards `a₁ ≤ b₁`, `a₂ ≤ b₂` stay load-bearing (the band
projector's total definition is the negated band at reversed
endpoints, and both the identity's hypothesis and the complement's
idempotence die without them).

Strictly-generalizes check (recorded): the delivered
`hlo`/`hhi` (closure separation) imply `hsep` — `μ ≤ a₂ → μ ≤ a₁ − δ`
against in-window `λ > a₁` gives `|μ − λ| ≥ δ`, and the high side
mirrors — so every consumer of the delivered theorem is a consumer of
this one; QA instantiates both on the same fixture to exhibit the
equal bound.

## QA plan (`Scaffold/QA/Perturbation/BandDavisKahanCluster_QA.lean`)

Four sections, on the reused `diag13`/`bdkB` fixtures (QA-to-QA import)
plus one new Fin 3 fixture pair pinned in-file:

1. **The interior witness — new coverage, closure separation provably
   failing** (`A = diag(0, 4, 10)` window `(−1, 5]`, cluster `{0, 4}`;
   `B = diag(1, 2, 3)` window `(1/2, 5/2]`, cluster `{1, 2}`; B's
   out-of-window eigenvalue `3` sits in A's cluster gap, δ = 1):
   pairwise separation discharged on pinned spectra; ranks 2 = 2
   through the supplier; the delivered theorem's `hhi` shape *refuted
   in proved form* (`5 + 1 ≤ 3` is false at the 3-mode) — the
   configuration is unreachable by the delivered theorem and covered by
   this one; the projectors' actions pinned (`P y = ![y₀, y₁, 0]`,
   `Q y = ![0, y₁, y₂]`), so `‖P − Q‖ ≥ 1` raw at `e₀`, joined with
   the theorem's `≤ ‖A − B‖` (itself pinned `≤ 7` through
   `l2OpNorm_eq_max_abs_evals` + the membership pin).
2. **The rotated non-trivial witness** (the sibling's fixture,
   `bdkB` vs `diag13`, equal windows `(−1, 2]`, δ = 3/4): the new
   theorem's bound `≤ 1` against the imported raw lower `√(1/10)` —
   the two-route pattern at the new hypothesis shape.
3. **The ε = 0 attainment** (A = B = diag13, identical windows, δ =
   1/2, pairwise `|3 − 1| = 2`): `‖P − Q‖ ≤ 0`, attained.
4. **The fence — `hsep` load-bearing, refuted in proved form** (A = B
   = diag13, windows `(−1, 2]` vs `(2, 4]`, δ = 1/2: ranks 1 = 1,
   guards verified, but B's out-of-window eigenvalue 1 is at distance
   0 from A's in-window eigenvalue 1): the hypothesis-free conclusion
   `‖P − Q‖ ≤ 0` refuted with `‖P − Q‖ ≥ 1` at `e₀`, and `hsep`
   proved the *only* failing hypothesis — the mirror of the sibling's
   rank fence, isolating the new hypothesis.

Fin 3 spectral pins (in-file, the `diag310_hpar_QA` technique): the
eigen-equation forces every eigenvector of a distinct-entry diagonal
onto a single coordinate, giving both the eigenvalue membership pin
(`eigvalOf ∈ {entries}`) and the projector action pins. Rank counts
via the supplier with value-class singletons from the trace
(`eigvalOf_sum_eq_trace`).

## Verification plan

Spike in-place in the module (`lake env lean` on the file itself, the
sibling's in-place precedent — the private engine is inaccessible to a
separate spike file), then on the QA file (zero errors/warnings),
explicit `lake build` targets, an axiom check via a `wip/` file over
every new public + QA declaration (the standard three only — nothing
conditional), full `lake build`, `lint_axioms` (count stays 9),
`check_citations`, `check_markdown_links`, scoreboard regeneration.
Records: this document, `proposals/README.md`, README (counts; the
Perturbation module-table row), the radar QA axis, the scoreboard,
`index/map/perturbation.md`, `index/sources/davis_kahan_1970.md` (the
cluster-form mapping row), this execution plan, and the activity log.
(No umbrella change — the content lands in an already-imported
module.)

## Delivery record (2026-08-24, run `20260824T122219Z-run-1`)

Delivered at exactly the committed shape, in new `ClusterForm` sections
of `Perturbation/BandDavisKahan.lean` (**no new imports** — the
survey's decisive finding held: every consumed declaration was already
in the module or its three imports). One committed-statement deviation
recorded: `bandProjector_eq_of_forall_mem_iff` carries **two window
guards** (`a ≤ b`, `a' ≤ b'`) not present in the proposal draft — at
reversed endpoints the band projector is the *negated* band, so two
always-empty windows need not agree and the unguarded iff-form is
false (e.g. `(5,3]` vs `(7,3]`: both select nothing, the projectors
differ). The guards are vacuous in every intended use. A second
interface lemma landed beyond the committed list:
`bandProjector_eq_zero_of_forall_not_mem` (the empty-cluster corner),
public as the natural twin.

- **The mathematical content, as delivered.** The interior case's
  projector-free expansion `norm_pack_shift_apply_ge_any` (F2 with all
  eigencomponents alive — no projector condition) plus the eigenvector
  route `norm_sub_ge_of_far_eigvalof` (at `Bv = μv`, the shift
  `A − μI` and the perturbation `A − B` agree on `v`, the expansion
  lower-bounds, the delivered action bound upper-bounds) replace the
  Step-0-priced Weyl/`evals` route entirely: **no sorted-spectrum
  machinery enters the proof**. The dichotomy `hkey` case-splits each
  out-of-window B-eigenvalue at the cluster range endpoints
  (`λmin = SAv.min'`, `λmax = SAv.max'` over the image of A's
  in-window index filter), killing `μ = λmin`/`μ = λmax` by the
  pairwise hypothesis itself (distance 0 < δ). The boundary case's
  transfer window is `((a₁ + λmin)/2, λmax]` — the shrink is
  constructive (no choice of a "closest" gap point), the capture
  lemma moves the projector, and the engine runs at `c = (λmin +
  λmax)/2`, `r = (λmax − λmin)/2` where `hfar` is *exactly* the range
  separation (the hand-checked identities close by named `heq`
  linear-combination facts — one algebra slip, a `r + δ` vs
  `λmax + δ` conflation, was caught by `ring` at elaboration and
  corrected before any green).

- **Pin techniques (the recurring fixes).** The `rw [a, b, c]` with an
  embedded `by linarith` *term argument* elaborates all arguments
  against the un-rewritten state — extract named `have`s and split the
  `rw` chain (the three `abs_of_nonneg` sites). `Finset.min'_le` at
  this pin takes the element and its membership, building its own
  Nonempty — bridge to a fixed `min' hne` by
  `congrArg (s.min') (proof_irrel _ _)`. `sub_mul` is left
  subtraction (`(a − b) * c`) — use `← sub_mul` to factor
  `a * c − b * c`. Matrix equality from equal actions goes through
  the column route (`Pi.single j 1`, entrywise, `Matrix.ext` —
  `Matrix.eq_zero_of_mulVec_eq_zero` needs `det ≠ 0` at this pin).
  QA-side: the ASCII-identifier discipline has a *parsing* face —
  `hλ` is not an identifier (λ is the lambda keyword); and `rw`
  auto-closes goals that become `le_refl`-trivial after rewriting
  (`rw [h] <;> norm_num` tolerant form, or per-branch
  `le_of_eq h`). Eigenvector inner products of supported vectors
  resolve by `Finset.sum_eq_single` — literal-free, immune to the
  `Fin.mk` display trap that defeats `ring` on `fin_cases`-split
  three-term sums.

- **QA delivered at the four mandated sections** (35 declarations: the
  Fin 3 generic diagonal layer — entry-set membership, off-coordinate
  support, class-injectivity via orthonormality, the support pin —
  plus the fixtures): (1) `bdkc_interior_QA` on `diag(0,5,11)` vs
  `diag(1,2,4)` at δ = 1 (exact at the 4-mode vs the 5-mode) —
  `bdkc_interior_not_closure` refutes the delivered closure shape in
  proved form, both projectors pinned entrywise to `diag(1,1,0)` (the
  two-mode entrywise sum over the class singleton filter, ranks 2 = 2
  through the trace lemma + pinned values), the raw distance exactly
  `0` joined with the theorem bound `≤ ‖A−B‖ ≤ 7` (the norm pinned
  through the namespaced `l2OpNorm_eq_max_abs_evals` + the
  membership pin); (2) `bdkc_rotated_QA` at the sibling's fixture —
  the imported raw lower `√(1/10)` against the new theorem's `≤ 1`;
  (3) the ε = 0 attainment at genuinely distinct windows
  `(-1,2]` vs `(-1/2,5/2]` — `bdkc_capture_QA` exercises the new
  capture-equality lemma, `bdkc_zeroE_raw` pins the distance `0` by
  the raw route, `bdkc_zeroE_attained`/`_evaluated` read the theorem's
  bound as exactly `0`; (4) `bdkc_sep_fence` — the hypothesis-free
  conclusion refuted (`‖diag(1,-1)‖ ≥ 1 > 0` at `A = B`) with ranks
  1 = 1 and every guard verified, and `bdkc_fence_only_sep_fails`
  isolating exactly `hsep` (the out-of-window 1-mode at distance 0
  from the in-window 1-mode, against δ = 1/2).

- **Verification.** `lake env lean` on the module and the QA file —
  zero errors, zero warnings each; `lake build
  Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan`
  ✔ (2192/2192) and `lake build
  Scaffold.QA.Perturbation.BandDavisKahanCluster_QA` ✔ (2196/2196);
  `#print axioms` via `wip/bdkc_axcheck.lean` on all 40 declarations —
  `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔
  (2260 targets, +1 for the new QA module, "Build completed
  successfully"; zero warnings in the changed modules)**;
  `lint_axioms` (**9**, unchanged), `check_citations`,
  `check_markdown_links` pass; scoreboard regenerated (**1908/9/0**,
  idempotent). Records updated: this document, `proposals/README.md`,
  README (1908; the Perturbation module-table row; the status
  paragraph's cluster sentence), the radar (QA axis synced 1873/47 →
  1908/48, held 4.0), the scoreboard (all four verification rows + a
  new interpretation bullet), `index/map/perturbation.md` (the
  cluster-form section + 3 declaration rows),
  `index/sources/davis_kahan_1970.md` (the cluster-form mapping row),
  this execution plan, and the activity log. No umbrella change (the
  content lands in an already-imported module). Nothing committed;
  prior runs' uncommitted deliveries and the untracked
  `docs/scaffold.jpeg` preserved untouched.

- **Open follow-ons.** The two-sided version (separation also from
  A's out-of-window side) would give the symmetric-gap constant-2
  form; a set-valued (non-interval) cluster projector would leave the
  band interface entirely and needs its own definition + proposal;
  and the YWS/Kato locators carry the standing
  verify-against-physical-copy caveat.
