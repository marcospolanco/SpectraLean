# Sweep-Cut Extraction: the Explicit Fiedler Level-Set Cut

**Status:** COMPLETE (Steps 0+1 delivered in one run, 2026-08-24)  
**Added:** 2026-08-24  
**Scope:** `GraphTheory.Cheeger` (new sweep-extraction section), `GraphTheory.Fiedler` (Phase C), QA sections in `Cheeger_QA`/`Fiedler_QA`. Zero new axioms (count stays 9).

## Motivation

`GraphTheory.Fiedler.cheeger_cut_existence` (Phase B, 2026-08-23) certifies
that *some* nonempty proper cut satisfies `conductance S ^ 2 ≤ 2 λ₂ / d`, but
its witness is the conductance **minimizer** supplied by
`cheegerConstant_attained` — a Finset-powerset enumeration with no
algorithmic content. The classical spectral-partitioning algorithm does not
enumerate cuts: it **sweeps** the Fiedler vector's level sets. The Fiedler
module's own header records the gap: "certifying a specific Fiedler *level
set* — the sweep-extraction statement — is a strictly stronger, separately
scoped follow-on", and backlog item 4's Phase B update names "the
swept-level-set extraction the named strengthening". This proposal is that
follow-on.

**Named consumer:** the spectral-partitioning algorithm interface (backlog
item 4's "spectral algorithms" ring): a consumer that wants *the cut the
sweep returns*, not an existence statement over an uncomputable minimizer.
Secondary consumers: any future local-clustering / PageRank-sweep work,
whose statements are all "∃ threshold t such that the swept set …".

## Step 0 survey (pre-edit, recorded before stating)

### The theorem

**Per-part extraction (L1).** For `y : V → ℝ` whose nonempty closed
superlevel sets at positive levels are all minority-side (exactly
`coarea_core`'s hypothesis `hy`), with `0 < ∑ y i ^ 2`:

```
∃ S t, 0 < t ∧ (∀ i, i ∈ S ↔ t ≤ y i ^ 2) ∧ S.Nonempty ∧ Sᶜ.Nonempty ∧
  conductance A S ^ 2 ≤ (∑ i, ∑ j, A i j * (y i - y j) ^ 2) / (d * ∑ i, y i ^ 2)
```

i.e. **some closed superlevel set of `y ^ 2` at a positive level** attains
`φ(S)² ≤ E'(y) / (d · M(y))` where `M(y) = ∑ y i ^ 2`.

**Median assembly (L2).** For any `x ⊥ 1`, `x ≠ 0` (the `cheeger_sweep`
hypothesis pair):

```
∃ S, S.Nonempty ∧ Sᶜ.Nonempty ∧
  ((∃ t, ∀ i, i ∈ S ↔ t ≤ x i) ∨ (∃ t, ∀ i, i ∈ S ↔ x i ≤ t)) ∧
  conductance A S ^ 2 ≤ 2 * rayleigh (regularNormalizedLaplacian A d) x
```

— the same constant 2 as `cheeger_sweep` (`φ_min² / 2 ≤ R` ⟺ `φ_min² ≤ 2R`),
but the witness is an **explicit closed superlevel or sublevel set of `x`**
(the sweep family). This is a genuine strengthening of the sweep lemma's
content, not a corollary: `cheeger_sweep` controls the infimum over all
cuts, `L2` exhibits a swept member.

**Fiedler instantiation (L3).** On connected `d`-regular graphs, composing
at `x := fiedlerVector` through the delivered Rayleigh bridge
(`= lambda2 / d`): a swept Fiedler level set `S` with
`conductance A S ^ 2 ≤ 2 * lambda2 / d` — the algorithm-facing strengthening
of `cheeger_cut_existence`.

### The route, with constants (worked through before writing Lean)

**L1 by min-attainment, not averaging-by-contradiction.** The textbook
sweep argument is a pigeonhole ("some level is at most the average"), which
in Lean demands a *strict* integral inequality (the integrand difference is
strictly positive on a positive-measure set). The survey's key decision:
avoid strictness entirely by **attainment**, mirroring how `coarea_core`
itself integrates the non-strict per-level bound:

1. `F := (univ.image fun i => y i ^ 2).filter (0 < ·)` is nonempty
   (from `0 < M`). By `Finset.exists_min_image` over `F` of
   `c ↦ boundary A (S_c) / |S_c|` (attained; `S_c := filter (c ≤ y i²)`),
   fix `c* ∈ F` minimizing the boundary-to-size ratio `r`; `S* := S_{c*}`
   is nonempty (`c*` is an attained value) and minority (`hy c*`).
2. **Covering fact:** every closed superlevel set equals one at an attained
   value: for `t > 0` with `S_t ≠ ∅`, `c' := min' (image.filter (t ≤ ·))`
   satisfies `S_t = S_{c'}` and `c' ≥ t > 0` so `c' ∈ F`; minimality gives
   `boundary A S_t = boundary A S_{c'} ≥ r · |S_{c'}| = r · |S_t|`. For
   `S_t = ∅` both sides vanish. So `∀ t > 0, r · |S_t| ≤ boundary A S_t`
   — non-strict.
3. **Layer-cake integration** (a structural clone of `coarea_core`'s own
   proof, at the same `y`): `M = ∫₀ᴿ ∑ indicatorLE (y i²) t dt` and
   `TV := ∑ i j, A i j |y i² − y j²| = ∫₀ᴿ ∑_p A p.1 p.2 |ind − ind| dt`
   with the dictionaries `∑ indicatorLE = |S_t|`
   (`sum_indicatorLE_eq_card_filter`) and `∑_p A |ind − ind| = 2 boundary`
   (`sum_pairAbs_eq_two_boundary`); the per-level bound of step 2 holds
   a.e. (the single failure point `t = 0` absorbed exactly as in
   `coarea_core`), so `integral_mono_ae_restrict` yields
   `2 r M ≤ TV`.
4. **Component A composition:** `core_sum_abs_sq_sub_sq` gives
   `TV² ≤ E'(y) · 4 d M` (through `sum_deg_mul_eq_of_regular`), so
   `r² M ≤ d E'(y)`, and minority + regularity make
   `conductance A S* = boundary/(d |S*|) = r / d`, whence
   `conductance A S* ^ 2 = r² / d² ≤ E'(y) / (d M)`.

Constant check (why 2, not 4): the extraction rides the *same* two
inequalities the per-part bound of Step 1c uses (co-area + Cauchy–Schwarz
Component A); nothing in the chain loses a factor, and the averaging weights
(gap masses) cancel exactly against `M`. The final per-part constant matches
`hardDirection_perPart`'s `φ² d M ≤ E'` shape — indeed L1 *implies* the
per-part statement (the level set's conductance bounds `cheegerConstant`
from below), so L1 is the strictly stronger per-part theorem.

**L2 by the Step-1c assembly.** `exists_median` + `minority_posPart` /
`minority_negPart` supply `hy` for `y⁺ := (x − m)⁺` and `y⁻ := (m − x)⁺`
verbatim (the hypothesis shapes are identical). At least one part has
positive mass (`median_parts_norm` + `x ≠ 0`). L1 at that part gives a
level set of `y⁺²` (resp `y⁻²`) at a positive level `t`; the level
membership converts at `t > 0`:
`t ≤ (max (x i − m) 0)² ↔ m + √t ≤ x i` (resp
`t ≤ (max (m − x i) 0)² ↔ x i ≤ m − √t`) — a closed superlevel (resp
sublevel) set of `x`. The numeric chain, all on shelf:
`E'(part)/M(part) ≤ (E'⁺ + E'⁻)/(M⁺ + M⁻) ≤ E'(x)/‖x‖² = 2 R_{L_sym}(x)`
through `sum_edgeWeight_sq_posPart_add_sq_negPart_le` (fused contraction),
`median_parts_norm` (norm split), and
`rayleigh_regularNormalizedLaplacian_eq` (Step-1a normalization).

**L3** composes L2 at `x := fiedlerVector` with
`fiedlerVector_ne_zero`, `fiedlerVector_ortho_onesVec` (at
`lambda2_pos_of_connected`), and
`fiedlerVector_rayleigh_regularNormalizedLaplacian` (= `lambda2 / d`).

### Shelf check (all consumed declarations verified present)

Component A `core_sum_abs_sq_sub_sq`; the layer-cake family
`indicatorLE`, `indicatorLE_of_le/_of_lt`, `intervalIntegrable_indicatorLE`,
`intervalIntegrable_const_mul`, `integral_indicatorLE`,
`integral_abs_indicatorLE_sub`, `intervalIntegral.integral_finset_sum`,
`integral_mono_ae_restrict`; the dictionaries
`sum_indicatorLE_eq_card_filter`, `sum_pairAbs_eq_two_boundary`;
`boundary_ge_of_minority`'s min-vol pattern; `vol_eq_of_regular`;
`sum_deg_mul_eq_of_regular`; `exists_median`, `minority_posPart`,
`minority_negPart`, `median_parts_norm`,
`sum_edgeWeight_sq_posPart_add_sq_negPart_le`,
`rayleigh_regularNormalizedLaplacian_eq`; the Fiedler interface
(`fiedlerVector_ne_zero/_ortho_onesVec/_rayleigh_regularNormalizedLaplacian`,
`lambda2_pos_of_connected`). No Mathlib gaps: `Finset.exists_min_image`,
`Finset.min'` (`Finset.min'_le`, `Finset.min'_mem`) are the only new pin
entries, both already consumed in this repository (the bdkc run's recorded
`min'` technique).

### Statement-shape decisions (recorded before stating)

1. **Closed level sets** (`t ≤ y i²`, `t ≤ x i`, `x i ≤ t`), not strict:
   the co-area encoding runs on closed superlevel sets (`indicatorLE`),
   and the sweep family is stated to match what the proof actually
   certifies.
2. **L1's family conjunct is `∃ t` alongside the conductance bound** — the
   consumer-facing shape "the theorem returns a *swept* set", which is the
   entire point; `Sᶜ.Nonempty` is included (derivable from minority, but
   the `cheeger_cut_existence` shape carries it and consumers should not
   re-derive).
3. **No `hcard : 2 ≤ card V` in L1/L2**: minority + nonempty forces it
   (`2 |S| ≤ n`, `1 ≤ |S| ⇒ 2 ≤ n` and `|Sᶜ| ≥ |S| ≥ 1`). L3 carries
   `hcard` only because the `lambda2`/`fiedlerVector` interface does.
4. **L1 keeps `hy` in `coarea_core`'s exact shape** (value-level
   `∀ t, 0 < t → 2 * card ≤ n`) so the median parts supply it verbatim.
5. **No new axioms, no citations to add**: everything is proved; the
   mathematical provenance (classical sweep cut, cf. Chung CBMS 92 Ch. 2
   and the Cheeger hard-direction route already cited in-module) is noted
   in docstrings only.

## QA obligations (mandated)

1. **L1 positive witness on `C₄`** (`Cheeger_QA`): `y = ![1,0,0,0]` — the
   extracted `S` *forced* to `{0}` by the level-membership iff (`t ≤ 1` vs
   `1 < t` cases), its conductance computed to `1` raw, joined with the
   theorem bound `E'(y)/(d·M) = 4/2 = 2`.
2. **L2 witness at `cycSweepX = ![1,0,-1,0]`**: the sweep family
   *characterized* (whatever `S` the theorem returns, case analysis on `t`
   pins it to one of `{0}`, `{0,1,3}`, `{2}`, `{1,2,3}` — all conductance
   `1` on the pinned boundary/vol facts), `1 = φ² ≤ 2 · R = 2` with the
   pinned `R = 1`.
3. **L2 witness at `cycX2 = ![1,1,-1,-1]`**: the family is exactly
   `{{0,1}, {2,3}}` — the sweep finds a cut of conductance `1/2`, *tied
   with the known-best cut* `cyc_conductance_01`, against the honest
   bound `2 · R = 2` (the theorem does not promise optimality; the fixture
   exhibits it anyway).
4. **The orthogonality fence** (negative witness, proved refutation):
   `x = onesVec` on `C₄` — `R = 0`, so the hypothesis-free conclusion
   demands a nonempty proper swept set of conductance `≤ 0`; but the
   constant vector's sweep family has **no** nonempty proper member
   (superlevels: `univ` or `∅`; sublevels the same). Exactly `horth`
   isolated.
5. **L3 on `K₂`** (`Fiedler_QA`): the extracted `S` identified through the
   Fiedler antisymmetry pins (`fiedlerVector 1 = −fiedlerVector 0 ≠ 0`) to
   `{0}` or `{1}` (sign cases on the Fiedler value), conductance `1` both
   ways, bound `2 · 2 / 1 = 4`, and the optimality cross-check
   `conductance S = cheegerConstant K₂ = 1` — the sweep is exact on `K₂`.

## Steps

- **Step 0** (this document): the survey above — route, constants, shelf,
  statement shapes, QA plan.
- **Step 1**: spike L1+L2 in `wip/sweep_spike.lean`; on green deliver the
  Cheeger section, the Fiedler Phase C section, the QA sections, and the
  record sweep (README, radar, scoreboard, index map, backlog item 4, the
  plan and activity log). One run, the recent one-run precedent.

## Non-goals

- No sweep on `walkLaplacian`/normalized eigenvalues (the undirected
  regular case is the load-bearing one; irregular transfers are the mixing
  program's business).
- No `MetricSpace`-style packaging of the sweep family (no type synonym);
  the family is stated as a disjunction of level-set memberships.
- No change to `cheeger_cut_existence` (kept for compatibility; the new
  theorem strictly strengthens it and the old statement follows by dropping
  the family conjunct).

## Delivery record (Step 1, 2026-08-24)

**Delivered as pure hard crust** — zero new axioms (count stays 9;
`#print axioms` via `wip/sweep_axcheck.lean` on all 5 public + 22 QA
declarations: `propext, Classical.choice, Quot.sound` only, every
one). QA 1999 → 2021 (+22 across the two existing QA files, no new
file).

- **`GraphTheory.Cheeger`, new `SweepExtraction` section** (no new
  imports): `mem_of_posPart_sq` / `mem_of_negPart_sq` (the level-set
  conversions — a superlevel set of `(x−m)⁺²` at `t > 0` *is* a closed
  superlevel set of `x` at `m + √t`, and dually; stated as public
  theorems since the conversions are the family-membership interface),
  **`sweep_level_extract`** (L1, exactly the Step-0 statement), and
  **`cheeger_sweep_cut`** (L2, exactly the Step-0 statement).
- **`GraphTheory.Fiedler`, new Phase C section**:
  **`fiedler_sweep_cut`** (L3) — composed from `cheeger_sweep_cut` at
  the Fiedler vector through the delivered Rayleigh bridge, with the
  `2 · (lambda2 / d)` normalization matched by an explicit ring
  identity.
- **QA** (`Cheeger_QA` +18, `Fiedler_QA` +4), all five
  proposal-mandated witnesses: (1) `sweep_extract_cycle_QA` — the
  L1-extracted set *forced* to `{0}` on `C₄` at `cycPos = ![1,0,0,0]`
  by the level-membership iff (the subset route: the filter is a
  subset of `{0}` and nonemptiness rules out `∅`), conductance `1`
  computed raw, bound `1 ≤ 4/(2·1) = 2`; (2) `sweep_cut_cycle_QA` —
  the L2 family characterized at `cycSweepX` (`{0}`, `{2}`, `{0,1,3}`,
  `{1,2,3}`, all conductance `1` — honestly inside the bound `2·R = 2`,
  *not* the global optimum `1/2`); (3) `sweep_cut_cycle_optimal_QA` —
  at `cycX2 = ![1,1,−1,−1]` the family is exactly the two dominant
  halves and the swept cut **ties the exhaustively computed global
  optimum** `cyc_conductance_01 = 1/2` (the two fixtures mark both
  ends of the sweep's quality range; the theorem promises neither
  endpoint); (4) `sweep_cut_orth_dropped_refuted_QA` — the
  orthogonality fence **refuted in proved form**: at `x = onesVec`
  (whose Rayleigh quotient is `0`) the hypothesis-free conclusion is
  false for *every* candidate because the constant vector's sweep
  family has no nonempty proper member at all; (5) `k2_sweep_cut_QA` /
  `k2_sweep_family_QA` / `k2_sweep_optimal_QA` — on `K₂` the swept cut
  identified as a singleton of conductance `1`, the swept family
  characterized through the Fiedler antisymmetry pins (on an
  eigenvector with equal entries the family would be *empty*, so no
  theorem of this shape could hold), and the optimality tie
  `conductance S = cheegerConstant (K₂) = 1`.

### Route notes (what the spike actually needed)

The Step-0 route held verbatim: attainment over the positive values of
`y²` (`Finset.exists_min_image`), the covering fact by `Finset.min'`,
and the integration cloned from `coarea_core` (mass/pair layer-cakes,
the dictionaries, the `t = 0` endpoint absorbed a.e. — all identical
constructions at the same `y`). The one mathematical observation worth
recording beyond the survey: the per-part `hchain` numeric lemma is
uniform in the degenerate cases — the product test `E'u · Mv ≤ E'v · Mu`
makes the cross-multiplication `E'u/(d·Mu) ≤ (E'u+E'v)/(d·(Mu+Mv))`
valid whether or not the other part vanishes, so the case tree is
three leaves (⁺ wins / ⁻ wins / one part zero) rather than four.

### Pin-technique list (Lean traps hit, for future runs)

- `Finset.exists_min'` does not exist at this pin; use `Finset.min'`
  with `Finset.min'_mem` / `Finset.min'_le` (the bdkc-recorded
  membership-built-`Nonempty` bridging did not even arise — passing
  `hGne` directly to both worked).
- `rw [Finset.mem_filter] at h` on a hypothesis whose filter's *own*
  predicate contains the image predicate rewrites the outer membership
  only; destructuring `∃ i, i ∈ univ ∧ f i = c` from a filtered-image
  membership needs the two-step `(Finset.mem_filter.1 h).1` then
  `rw [Finset.mem_image] at` that projection.
- `Fintype.sum_prod_type'` applies cleanly *at a hypothesis* in the ←
  direction (`rw [← Fintype.sum_prod_type' f] at h`), matching the
  coarea_core precedent; rewriting the *goal* from the product form
  fails on higher-order unification.
- `sq_le_sq` at this pin is the abs form (`a² ≤ b² ↔ |a| ≤ |b|`);
  `abs_le_abs` is a two-argument implication, not an iff, and nested
  `|…|…|…||` breaks the parser — write `abs (...)` explicitly.
- `le_of_mul_le_mul_right` is syntactic about the shared factor's
  position; pre-massage with an explicit `ring` identity (`hring`)
  before applying, and keep division out of `nlinarith` goals by
  pre-stating the `field_simp [hkne]; ring` identities as named
  `have`s.
- `by norm_num` on `2 / min 2 6 = 1` strands `2 * 2 = 4`; resolve the
  `min` by `min_eq_left`/`min_eq_right` first and close with
  `div_self two_ne_zero` (plain `2 / 4 = 1 / 2` is norm_num-clean —
  the `min` was the obstruction).
- Set identifications from per-literal membership facts:
  `Finset.eq_univ_iff_forall.2` / `Finset.eq_empty_iff_forall_not_mem.2`
  with `fin_cases`, never `Finset.ext; intro i; simp [literal-facts]`
  (simp cannot use literal facts at a variable index). `Finset.subset_singleton_iff`
  is the clean route for "nonempty subset of a singleton".
- `add_pos`/`add_pos'` at this pin both take strict positivity on both
  sides; `by linarith` inside the `mul_pos` application is the robust
  replacement when one side is `≤ 0`.
- `hS.elim` on `(∅).Nonempty` elaborates to a wrong `Exists.elim`
  shape; `simp at hS` closes it.

### Open follow-ons (priced, not started)

- The *algorithmic* packaging: a computable sweep that enumerates the
  `O(n)` level sets and returns the best one (needs a sorted
  enumeration of the Fiedler values — the `Finset.sort` machinery this
  route deliberately avoided); gated on a consumer naming what it
  unlocks.
- The irregular (non-regular) conductance shape: the sweep family and
  extraction are volume-based in general; the current statements are
  `d`-regular because the Rayleigh/conductance conversion is. A
  consumer needing the irregular form should re-derive through
  `normalizedLaplacian`'s degree weights.
- The `MetricSpace`-style packaging of nothing here — the sweep family
  is already stated as the disjunction consumers need; no follow-on.
