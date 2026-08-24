# Proposal: Band Davis–Kahan Symmetric Form — the two-sided (both-separations) constant-2 difference theorem without rank equality

**Status:** **DELIVERED 2026-08-24** (run `20260824T141936Z-run-1`) —
Steps 0+1 in one run per the sibling precedent; see the delivery record
at the bottom. Zero new axioms (count stays 9; `#print axioms` via
`wip/bdks_axcheck.lean` on both new public + all 17 public QA
declarations reads only `propext, Classical.choice, Quot.sound`, every
one). QA 1908 → 1925 (`BandDavisKahanSymm_QA` a new file at 17 by the
generator metric).

**Proposed** 2026-08-24 (run `20260824T141936Z-run-1`).

Assessed from `Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/
{BandDavisKahan,Duhamel,ProjectionGap}.lean`, the sibling QA files
(`BandDavisKahan_QA`, `BandDavisKahanDiff_QA`, `BandDavisKahanCluster_QA`
— the public fixture layers cited below), with the route worked through
by hand in Section "The assembly" before any Lean is written.

## The obligation this discharges

The cluster-form delivery's own first recorded open follow-on
(`proposals/band-davis-kahan-cluster.md`, Delivery record, "Open
follow-ons", first bullet): "the two-sided version (separation also from
A's out-of-window side) would give the symmetric-gap constant-2 form."
First-named candidate in both `docs/EXECUTION_PLAN.md`'s and the
activity log's recorded next handoffs after that delivery.

**Leverage, threefold:**

1. **The rank hypothesis drops out entirely.** The delivered
   difference-form theorems (closure and pairwise) both require
   projector-rank equality — an assumption the consumer must discharge
   through `rank_bandProjector_eq_card`, i.e. by counting eigenvalue
   classes on both sides. The two-sided separation at constant 2 needs
   **no rank hypothesis**: unequal ranks force `δ ≤ ‖A − B‖` (the
   interior/eigenvector argument, so the bound degrades to the trivial
   regime `1 ≤ 2‖A − B‖/δ`), while equal ranks are handled by the
   engine directly. This is exactly the YWS Theorem 1 selling point of
   the both-gaps variants: the consumer states spectral separation and
   nothing else — no multiplicity counting.
2. **A fourth and fifth consumer of the same engine.** The private
   complement engine
   (`l2OpNorm_one_sub_bandProjector_mul_bandProjector_le_core`) runs at
   *both* argument orders — the rank-free pairwise product bound below
   factors it once and is instantiated twice — testing the engine's
   modularity claim at its limit (the core takes arbitrary `c, r` and
   arbitrary argument roles; neither generality was exercised by the
   three previous consumers at swapped roles).
3. **A new public interface lemma fills a real shelf gap:**
   `l2OpNorm_transpose` (`‖Mᵀ‖ = ‖M‖` for the ℓ² operator norm) is
   absent from the pinned Mathlib *and* from every Scaffold module
   (surveyed: no `transpose`×`l2OpNorm` hit anywhere under
   `Scaffold/Mathlib/`). Every future consumer that bounds a
   right-action `Q * (I − P)` while the engine states the left-action
   `(I − P) * Q` — the exact situation of any two-sided perturbation
   argument — needs it.

Run selection: the Active priority table holds no High/Medium rows; of
the three natural candidates on record, this is the only one both named
and zero-axiom (directed-axis mixing is gated on a *primitivity-shaped
admission*; wide-band minimax filter designs are gated on scalar
approximation theory absent from the pinned Mathlib).

## Source

Route provenance (the statement is *proved*, not admitted — this
proposal adds no axiom):

- Yu, Y., Wang, T., Samworth, R. J., "A useful variant of the
  Davis–Kahan theorem for statisticians", Annals of Statistics
  43(3):2028–2061, 2015, Theorem 1 — the two-sided (both-gaps)
  variants at constant 2: separation assumed on *both* the population
  and sample spectra, no dimension hypothesis, bound `2‖Σ̂ − Σ‖/δ`.
  (Same paper already the cited source of `davis_kahan_sin_theta` and
  the cluster form; read at arXiv:1405.0680 during the 2026-08-21
  Step-0 survey.)
- Vershynin, *High-Dimensional Probability*, 2018, Thm 4.1.15–4.1.16 —
  the commutator/shift technique, already the recorded route of all
  three delivered band forms.

Statement differences from the textbook packaging (recorded before
stating): windows are `bandProjector`'s own `(a, b]` convention and the
clusters are the windows' eigenvalue classes (as in all three delivered
band forms); the separation is stated **pairwise** (eigenvalue against
eigenvalue, the literal YWS δ) in two mirror-shaped hypotheses — B's
out-of-window spectrum δ-away from A's in-window spectrum, *and* A's
out-of-window spectrum δ-away from B's in-window spectrum; constant 2;
**no rank hypothesis** (the both-gaps form's dimension-freeness). Where
YWS's Theorem 1 both-gaps parts take δ as the min of the two
*interval* gaps, the pairwise shape here is strictly analogous to the
relationship the cluster delivery already established between its
closure-form sibling and the literal YWS δ.

## Step-0 survey findings (recorded before any statement is frozen)

### Shelf facts verified present

1. **The engine** (`BandDavisKahan.lean`, private, same module —
   landing as a new section of that file, the sibling precedent):
   `l2OpNorm_one_sub_bandProjector_mul_bandProjector_le_core` at
   arbitrary `c, r` and — decisive here — at *arbitrary argument
   roles*: nothing in its statement ties "A" to the perturbation's
   minuend; instantiating it with the two matrices swapped is a plain
   application. The core carries **no rank hypothesis** (rank equality
   entered the delivered theorems only through
   `l2OpNorm_sub_eq_of_rank_eq`, the identity conversion of the
   difference to a product).
2. **The interior machinery**, all private in the module and thus
   reusable from a new section of the same file:
   `norm_pack_shift_apply_ge_any` (the projector-free expansion),
   `norm_sub_ge_of_far_eigvalOf` (a B-eigenvalue δ-far from A's whole
   spectrum forces `δ ≤ ‖A − B‖`), `bandProjector_eq_of_forall_mem_iff`
   and `bandProjector_eq_zero_of_forall_not_mem` (both *public* — the
   window-shrink transfer and the empty-cluster corner).
3. **The trivial regime**: `l2OpNorm_sub_le_one_of_isSymm_idempotent`
   (Duhamel, public) — `‖P − Q‖ ≤ 1` for symmetric idempotents.
4. **The pairing pieces** for the transpose lemma: 
   `l2OpNorm_le_of_abs_dotProduct_le` and `abs_dotProduct_le` and
   `norm_euclidean_eq_sqrt` (Duhamel, public), `l2OpNorm_mulVec_le`
   (BandDavisKahan, public), `Matrix.dotProduct_mulVec`,
   `Matrix.vecMul_transpose`, `Matrix.dotProduct_comm` (pin).
5. **QA fixture layers, all public and QA-to-QA importable** (the
   delivered precedent): from `BandDavisKahanCluster_QA` — `clusterA`
   = `diag(0, 5, 11)`, `clusterB` = `diag(1, 2, 4)` with the
   membership/injectivity/exists pins
   (`clusterA_mem`, `clusterA_inj`, `clusterA_exists_zero/five`,
   `clusterB_exists_one/two/four`, …), `bandClusterA_eq` (the
   `(−1, 6]` projector pinned entrywise to `diag(1,1,0)`),
   `clusterA_card_band`, `clusterDiff_norm_le` (`‖A − B‖ ≤ 7`); from
   `BandDavisKahanDiff_QA` — `diag13`, `bdkB` with the
   window-parametric action pins (`bdkd_Qe0_of_mem`:
   `Q *ᵥ e₀ = ![9/10, −3/10]`; `bdkd_diff_e0_of_mem`:
   `(P − Q) *ᵥ e₀ = ![1/10, 3/10]`), `bdkd_rank_eq`, `bdkd_rotated_QA`,
   `bdkE_norm_le`; from `Band_QA` — `band_diag13_low_e0`,
   `diag13_eigvalOf_mem`, `diag13_exists_one`, `bdkB_eigvalOf_mem`;
   from `Band.lean` — `bandProjector_eq_one`.

### Gaps priced (to land in the delivery)

1. **`l2OpNorm_transpose`** (public interface lemma): `‖Mᵀ‖ = ‖M‖` for
   the ℓ² operator norm — absent from the pin and the shelf. Route
   (two applications of the pairing characterization):
   `y ⬝ᵥ (Mᵀ *ᵥ x) = (M *ᵥ y) ⬝ᵥ x = x ⬝ᵥ (M *ᵥ y)` through
   `Matrix.dotProduct_mulVec` + `Matrix.vecMul_transpose` +
   `Matrix.dotProduct_comm`, then `abs_dotProduct_le` +
   `l2OpNorm_mulVec_le` give the pairing bound at `c := ‖M‖`; the
   reverse inequality is the same lemma at `Mᵀ`.
2. **The rank-free pairwise product bound** (private): under pairwise
   separation *and* the contentful regime `‖A − B‖ < δ`, the cluster
   theorem's dichotomy kills the interior case outright (interior
   forces `δ ≤ ‖A − B‖`), so every out-of-window B-eigenvalue is
   boundary and the engine runs at the cluster-range `c, r` — giving
   `‖(I − Q) * P‖ ≤ ‖A − B‖ / δ` with **no rank hypothesis** (the
   empty-cluster corner is `P = 0`, norm 0, not the delivered
   theorem's rank-transfer corner).

### The assembly (worked through by hand)

Let `P := bandProjector A hA a₁ b₁`, `Q := bandProjector B hB a₂ b₂`,
`E := ‖A − B‖`.

**Case split at `E = δ/2`.**

- **Trivial regime** (`δ/2 ≤ E`): `‖P − Q‖ ≤ 1` (symmetric
  idempotents) and `1 ≤ δ/δ ≤ 2E/δ` — done.
- **Contentful regime** (`E < δ/2 ≤ δ`): the two rank-free product
  bounds fire.
  - `‖(I − Q) * P‖ ≤ E/δ`: the pairwise hypothesis (B-out vs A-in)
    plus `E < δ`. If A's cluster is empty, `P = 0`. Otherwise the
    cluster range `[lmin, lmax]`: any out-of-window B-eigenvalue `μ`
    strictly inside `[lmin, lmax]` is δ-far from *every* A-eigenvalue
    (in-window by pairwise; the flanks because `a₁ < lmin`, `lmax ≤
    b₁`), so the delivered eigenvector route forces `δ ≤ E` —
    contradiction with `E < δ/2`. So every `μ` is boundary
    (`μ ≤ lmin − δ` or `lmax + δ ≤ μ`); the window-shrink
    (capture-equality) and the engine at `c = (lmin + lmax)/2`,
    `r = (lmax − lmin)/2` close exactly as in the cluster theorem —
    minus the identity conversion, which is simply not performed.
  - `‖(I − P) * Q‖ ≤ E/δ`: the same lemma at swapped roles (the
    pairwise hypothesis A-out vs B-in, `‖B − A‖ < δ`).
  - **The decomposition** (pure ring identity, no hypotheses):
    `P − Q = (I − Q) * P − Q * (I − P)`, and `Q * (I − P)` is the
    transpose of `(I − P) * Q` (P, Q symmetric), so
    `l2OpNorm_transpose` moves it under the second product bound.
    Triangle: `‖P − Q‖ ≤ E/δ + E/δ = 2E/δ`. **The constant 2 is
    exactly the triangle inequality at the decomposition** — no
    slack, no hidden loss.

**Why unequal ranks cannot break it:** if the ranks differ, some
cluster escapes — formally, if (say) B's cluster is empty while A's is
not, then *every* A-eigenvalue is an out-of-window B-side eigenvalue
δ-far from every B-eigenvalue... and conversely the contentful regime
derives its own contradiction: in the `E < δ/2` branch, an empty B
cluster with nonempty A cluster puts every B-eigenvalue outside B's
window, δ-far (by the B-out vs A-in hypothesis) from every in-window
A-eigenvalue; the eigenvector route at any B-eigenpair against the
in-window class forces `δ ≤ E` — contradiction. Symmetrically for the
other corner. So in the contentful regime both separations jointly
*force* the configuration the engine handles; nothing is assumed about
ranks anywhere.

## Committed statement

Public (namespace
`Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation`, a new
`SymmetricForm` section of
`Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean`, **no new
imports** — everything consumed is already in the module or its three
imports):

```lean
/-- The ℓ² operator norm is transpose-invariant. -/
theorem l2OpNorm_transpose (M : Matrix V V ℝ) : ‖Mᵀ‖ = ‖M‖

/-- **Band Davis–Kahan, difference form, two-sided (symmetric)
separation, no rank hypothesis.** If every eigenvalue of `B` *outside*
its window is δ-away from every eigenvalue of `A` *inside* its window,
and every eigenvalue of `A` *outside* its window is δ-away from every
eigenvalue of `B` *inside* its window, then `‖P_A − P_B‖ ≤ 2 ‖A − B‖ / δ`.
No hypothesis on the projectors' ranks. -/
theorem l2OpNorm_bandProjector_sub_bandProjector_le_two_of_symm
    (hA : A.IsSymm) (hB : B.IsSymm)
    (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂)
    {δ : ℝ} (hδ : 0 < δ)
    (hsepAB : ∀ i, ¬(a₁ < eigvalOf A hA i ∧ eigvalOf A hA i ≤ b₁) →
      ∀ j, a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂ →
      δ ≤ |eigvalOf A hA i - eigvalOf B hB j|)
    -- (inner shape corrected to the conjunction form at delivery; see
    -- the delivery record's committed-statement correction)
    (hsepBA : ∀ j, ¬(a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂) →
      ∀ i, a₁ < eigvalOf A hA i → eigvalOf A hA i ≤ b₁ →
      δ ≤ |eigvalOf B hB j - eigvalOf A hA i|) :
    ‖bandProjector A hA a₁ b₁ - bandProjector B hB a₂ b₂‖
      ≤ 2 * ‖A - B‖ / δ
```

The junk-band guards `a₁ ≤ b₁`, `a₂ ≤ b₂` stay load-bearing (as in
every delivered band form: the band projector's total definition is
the negated band at reversed endpoints). `hsepBA` is *verbatim* the
delivered pairwise theorem's `hsep` — a consumer holding both
separations can call either theorem; `hsepAB` is its mirror.

Relation to the delivered family (recorded): on equal-rank inputs the
delivered pairwise theorem gives the strictly better constant 1; the
new theorem's value is **uniformity** — it applies wherever the
two-sided separation holds, with no multiplicity counting, and is true
(however weakly) on unequal-rank inputs the delivered family's
hypotheses cannot even reach. When ranks differ, `δ ≤ ‖A − B‖` is
forced, so the bound reads `≥ 2` against `‖P − Q‖ ≤ 1` — the
degradation is the theorem's honest content, exactly as in the YWS
both-gaps form.

## QA plan (`Scaffold/QA/Perturbation/BandDavisKahanSymm_QA.lean`)

Four sections, all ASCII identifiers (the counter is ASCII-only), on
fixtures reused by QA-to-QA import (`BandDavisKahanCluster_QA`, which
transitively imports `BandDavisKahanDiff_QA` and `BandDavisKahan_QA`):

1. **The rank-free unequal-rank witness — the selling point** (`A =
   clusterA = diag(0, 5, 11)` window `(−1, 6]` (cluster `{0, 5}`,
   rank 2); `B = clusterB = diag(1, 2, 4)` window `(3/2, 3]` (cluster
   `{2}`, rank 1); δ = 1/2): every hypothesis discharged on the pinned
   spectra (B-out `{1, 4}` vs A-in `{0, 5}`: min distance `1`; A-out
   `{11}` vs B-in `{2}`: distance `9`); ranks pinned **2 ≠ 1** through
   the supplier + card pins — the delivered family's hypothesis
   exhibited failing on the very fixture the new theorem covers;
   `P` pinned entrywise through the imported `bandClusterA_eq`, the
   norm lower-bounded by `1` raw at `e₀` (B's 1-mode is out-of-window,
   so `Q *ᵥ e₀ = 0` by the component action + support pins — every
   component vanishes); the theorem bound evaluated `≤ 2 · 7/(1/2) =
   28` and joined with `‖P − Q‖ ≥ 1`. Plus the **constant comparison**
   on the equal-rank rotated fixture (`diag13` vs `bdkB`, equal
   windows, δ = 3/4): delivered bound `≤ 1` vs new bound `≤ 2` vs raw
   `√(1/10)` — the constant-2 cost visible numerically.
2. **The ε = 0 attainment** (A = B = `diag13`, genuinely distinct
   windows `(−1, 2]` vs `(−1/2, 5/2]` selecting the same cluster, δ =
   1/2, both separations at distance 2): the theorem reads `≤ 0`,
   attained — cross-checked by the imported raw zero pin
   (`bdkc_zeroE_raw`).
3. **The fence — `hsepAB` load-bearing, refuted in proved form, the
   mirror of the cluster QA's `hsepBA` fence** (A = B = `diag13`,
   windows `(−1, 2]` vs `(−1, 4]`: B's window selects everything, so
   `hsepBA` is *vacuous* and provably holds; A's out-of-window 3-mode
   sits at distance 0 from B's in-window 3-mode, so `hsepAB` fails;
   every other hypothesis verified): the hypothesis-free conclusion
   `‖P − Q‖ ≤ 2 · 0 / δ = 0` refuted with `‖P − Q‖ ≥ 1` at `e₁`
   (`Q = 1` through `bandProjector_eq_one`, `P = diag(1, 0)`);
   `hsepBA` exhibited as a *term* (vacuous), isolating exactly
   `hsepAB`. Together with the cluster QA's fence, both separation
   sides of the difference family are now isolated across the QA
   family.
4. **The decomposition-coherence witness** (the `bdkd_coherence`
   precedent, on the rotated fixture at `e₀`): `(P − Q) *ᵥ e₀` pinned
   `![1/10, 3/10]` by the imported raw route, and
   `(I − Q) P *ᵥ e₀ − Q (I − P) *ᵥ e₀` assembled independently from
   the imported action pins (`P *ᵥ e₀ = e₀`, `Q *ᵥ e₀ = ![9/10,
   −3/10]`, `Q (I − P) *ᵥ e₀ = 0`) — the consumed decomposition
   identity's content exhibited numerically on genuinely rotated
   input.

In-file support (small, public-lemma-only): the eigenbasis support
pins for `clusterB` (the eigen-equation at a diagonal matrix with
distinct entries forces off-coordinate support to vanish), the
component-collapse route through `eigvecOf_expansion_apply` (the
public expansion; the module's private basis-injectivity packaging is
unavailable QA-side).

## Verification plan

Spike in-place in the module (`lake env lean` on the file itself, the
siblings' precedent — the private engine is inaccessible to a separate
spike file), then on the QA file (zero errors/warnings), explicit
`lake build` targets, an axiom check via a `wip/` file over every new
public + QA declaration (the standard three only — nothing
conditional), full `lake build`, `lint_axioms` (count stays 9),
`check_citations`, `check_markdown_links`, scoreboard regeneration.
Records: this document, `proposals/README.md`, README (counts; the
Perturbation module-table row), the radar QA axis, the scoreboard,
`index/map/perturbation.md`, `index/sources/davis_kahan_1970.md` (the
two-sided mapping row), the execution plan, and the activity log. (No
umbrella change — the content lands in an already-imported module.)

## Delivery record (2026-08-24, run `20260824T141936Z-run-1`)

Delivered at the committed shape in a new `SymmetricForm` section of
`Perturbation/BandDavisKahan.lean` (**no new imports** — the survey's
finding held), with one committed-statement correction recorded below.
The module's engine ran **green on its first complete pass** (two
elaboration rounds only, both in QA), validating the proposal's
worked-through assembly: the private rank-free product bound
`l2OpNorm_one_sub_bandProjector_mul_bandProjector_le_pairwise` is the
cluster theorem's dichotomy/shrink/engine body minus the identity
conversion, factored once and instantiated twice; the headline's case
split at `δ/2 ≤ ‖A−B‖` and the decomposition
`sub_eq_one_sub_mul_sub_mul_one_sub` (closed by `sub_mul`, `mul_sub`,
`mul_one`, `one_mul`, `sub_sub_sub_cancel_right`) assemble the proof
exactly as written above.

- **Committed-statement correction (recorded):** `hsepAB`'s inner
  hypothesis is stated as a **conjunction**
  (`a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂`), not the committed
  draft's two-arrow form. The delivered pairwise `hsep` (and the
  family convention) puts the *negated* side in conjunction form and
  the positive side in two-arrow form; the delivered statement makes
  both separations conjunction-shaped on their positive sides
  (`hsepBA` keeps verbatim the pairwise `hsep` shape:
  negated-conjunction outer, two-arrow inner). A one-line bridge
  (`fun i hi j h1 h2' => hsepAB i hi j ⟨h1, h2'⟩`) adapts it to the
  engine at the swapped call. Vacuous in every intended use; caught
  when QA discharge at the committed two-arrow shape bound the first
  component where the conjunction was expected.

- **The mathematical content, as delivered.** The trivial regime
  closes through `l2OpNorm_sub_le_one_of_isSymm_idempotent` at
  `1 ≤ 2E/δ`. The contentful regime (`E < δ/2`) reuses the module's
  interior machinery verbatim (`norm_pack_shift_apply_ge_any`,
  `norm_sub_ge_of_far_eigvalOf`): an interior out-of-window
  B-eigenvalue forces `δ ≤ E < δ/2`, contradiction, so every such
  eigenvalue is δ-outside the cluster *range* and the complement
  engine runs at the cluster-range center/radius through the
  capture-equality shrink — the cluster theorem's third-consumer
  pattern, now at both argument orders (the engine's fourth and fifth
  consumers). The transpose move is the new public
  `l2OpNorm_transpose` (two applications of
  `l2OpNorm_le_of_abs_dotProduct_le` around
  `Matrix.dotProduct_mulVec` + `Matrix.vecMul_transpose` +
  `Matrix.dotProduct_comm`, with `abs_dotProduct_le` +
  `l2OpNorm_mulVec_le` closing the pairing bound); `Q * (I − P) =
  ((I − P) * Q)ᵀ` through `Matrix.transpose_mul` and the band
  projectors' symmetry.

- **Pin techniques (the recurring fixes, for the next sibling).**
  `rw ... at h` on a *conjunction* hypothesis silently normalizes it
  (decidable conjuncts collapse; the hypothesis can arrive at the use
  site as a bare comparison or `True`) — never rewrite the membership
  hypothesis; instead (a) `linarith [h, jin.2]` with the projection
  inline (the goal `eigvalOf = c` is linear in the atom and follows
  from the contradiction), and (b) for out-of-window derivations
  `exact absurd (And.intro (by rw [h]; norm_num) (by rw [h]; norm_num))
  hiout` — goal-side per-component rewrites are stable.
  `div_le_div_right` at this pin is a deprecated *iff* — use
  `(div_le_div_iff_of_pos_right hc).2`. `norm_num` does not evaluate
  `|9/4|` (fractional abs): `rw [abs_of_nonneg (by norm_num)]` first
  (as its own `rw`, after the value rewrites — the embedded-`by` term
  trap). `sub_self` under a norm leaves `‖0‖`: add `norm_zero` to the
  chain. The `rw [hi₃, hi₃, ...]` duplication fails — one `rw` at a
  fixed instantiation rewrites all occurrences. `bandProjector_eq_one`
  takes two separate bare ∀-hypotheses, not one conjunction.

- **QA delivered at the four mandated sections** (17 public
  declarations + one private support lemma): (1)
  `bdks_unequal_rank_QA` on the public cluster fixtures (`clusterA`
  window `(−1, 6]` rank 2 vs `clusterB` window `(3/2, 3]` rank 1,
  both separations discharged on the pinned spectra, δ = 1/2) — the
  ranks pinned **2 ≠ 1** through the delivered supplier (the
  delivered family's hypothesis exhibited failing on the very fixture
  the new theorem covers), the raw norm ≥ 1 at `e₀` (B's band action
  vanishing through the in-file eigen-equation support pin
  `bdks_eigvec_two_off` — the cluster QA's private technique
  re-derived at the one index needed — plus the component action and
  the public expansion `eigvecOf_expansion_apply`), joined with the
  bound `≤ 2·7/(1/2) = 28`; plus `bdks_rotated_two_QA` exhibiting the
  constant-2 cost numerically (delivered ≤ 1, new ≤ 2, raw `√(1/10)`)
  on the equal-rank rotated fixture; (2) `bdks_zeroE_attained` at
  genuinely distinct windows through both separations at distance 2,
  cross-checked by the imported `bdkc_zeroE_raw`; (3) the
  `hsepAB`-isolated fence — `bdks_fence_Qeq` (`Q = 1` through
  `bandProjector_eq_one`), `bdks_fence_lower` (`(P − 1) *ᵥ e₁ = −e₁`
  raw, norm ≥ 1), `bdks_sep_fence` (the hypothesis-free conclusion
  refuted at A = B), `bdks_fence_sepBA_holds` (the mirror separation
  *provably vacuous-holding*), `bdks_fence_sepAB_fails` (distance 0
  at the shared 3-mode), and `bdks_fence_only_sepAB_fails` collecting
  guards + holds + fails + refutation; (4) the decomposition
  coherence witness `bdks_decomp_part1/2` + `bdks_decomp_coherence` —
  `(I−Q)P *ᵥ e₀ = ![1/10, 3/10]` and `Q(I−P) *ᵥ e₀ = 0` computed from
  the imported pins, joined with the imported raw difference action.

- **Verification.** `lake env lean` on the module and the QA file —
  zero errors, zero warnings each; `lake build
  Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan`
  ✔ and `lake build Scaffold.QA.Perturbation.BandDavisKahanSymm_QA` ✔;
  `#print axioms` via `wip/bdks_axcheck.lean` on all 19 accessible
  declarations (2 public + 17 QA; the one private helper is
  inaccessible by design) — `propext, Classical.choice, Quot.sound`
  only, every one; **full `lake build` ✔ (2260 targets, +1 for the new
  QA module, "Build completed successfully"; zero warnings in the
  changed modules)**; `lint_axioms` (**9**, unchanged),
  `check_citations`, `check_markdown_links` pass; scoreboard
  regenerated (**1925/9/0**, idempotent). Records updated: this
  document, `proposals/README.md` (the Delivered row; the High row
  retired; the progress paragraph rewritten — the table empty again),
  README (1925; the Perturbation module-table row), the radar (QA axis
  synced 1908/48 → 1925/49, held 4.0), the scoreboard (all four
  verification rows + a new interpretation bullet),
  `index/map/perturbation.md` (the symmetric-form section + 2
  declaration rows), `index/sources/davis_kahan_1970.md` (the
  two-sided mapping row), this execution plan, and the activity log.
  No umbrella change (the content lands in an already-imported
  module). Nothing committed; the prior runs' uncommitted deliveries
  and the untracked `docs/scaffold.jpeg` preserved untouched.

- **Open follow-ons.** A set-valued (non-interval) cluster projector
  would leave the band interface entirely and needs its own
  definition + proposal (as recorded for the cluster form); the
  Frobenius-norm sin-Θ variants (YWS Theorem 1's other parts) would
  need a Frobenius pairing engine the shelf does not have; and the
  YWS/Kato locators carry the standing verify-against-physical-copy
  caveat.
