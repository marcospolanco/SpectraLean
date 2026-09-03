# Adversarial Fence Audit of the Lazy Family

**Status:** COMPLETE — delivered 2026-09-02 (same-run proposal; run
`20260902T225627Z-run-1`, session `ses_f9bb3f57affeWs0Ep264nM0eze`).

**Goal.** The standing handoff's top-named continuation, executed as a
bounded audit: an adversarial re-read of the lazy family's QA
(`Mixing.lean`'s lazy sections — the operator/law layer, the
density/χ² layer, the signless engine, the decay engine, and the
headline `lazyChiSquareDistance_le_of_connected` with its TV/entropy
corollaries — plus `Oversmoothing.lean`'s `LazyMixingTime` section),
closing every hole it finds with the repository's hypothesis-form
negative-witness fences.

## Why this and why now

- **The named continuation.** The 2026-09-02 fence-completion delivery
  (`adversarial-fences-tv-dobrushin-engines.md`) explicitly left the
  remaining mixing-cascade families open and recorded the method; two
  consecutive handoffs had named the audit-shaped pass the top
  unstarted frontier before that run took the first family.
- **The audit method** (`governance/ADVERSARIAL_REVIEW.md`): for every
  hypothesis of every shelf lemma in the family, either produce a
  fixture where exactly that hypothesis fails and the conclusion is
  refuted at pinned values (a *fence*), or record why no fence is
  possible. Cross-checked against every existing fence so nothing is
  duplicated.
- **The family's leverage.** The lazy walk is the discrete mixing
  program's periodicity fix: on every connected bipartite graph
  (paths, trees, grids — the empirical-stationary capstone's own
  "agent that can only simulate the walk" setting), the plain
  family's `r < 1` certificate is provably unsatisfiable and the lazy
  rate `1 − λ₂/2` is the only route. A silent statement-shape
  regression in the family's hypothesis set (a dropped symmetry,
  degree-positivity, or nonnegativity clause) would propagate into
  `lazyChiSquareDistance_le_of_connected`, the entrywise/depth lazy
  ceilings, the lazy `t_mix` object, and the empirical lazy capstone.

## Audit findings

### Fenceable: load-bearing hypotheses with no negative witness

All fixture values hand-verified before any Lean is written.

| Lemma | Dropped hypothesis | Fixture (all other hypotheses hold) | Refutation |
| --- | --- | --- | --- |
| `lazyWalkTransitionMatrix_mulVec_one` | `hd` (positive degrees) | `zdAdj = !![0,0;0,1]]` (symmetric, nonnegative; `deg 0 = 0`) | `(P_L *ᵥ 1) 0 = 1/2 ≠ 1` (the zero-degree row of `P = D⁻¹A` is junk-zero, so the lazy half is `1/2·I`) |
| `sum_lazyWalkDistribution` | `hd` | same `zdAdj` | `∑ i, ν₁ 0 i = 1/2 ≠ 1` |
| `lazyChiSquareDistance_zero` | `hd` | same `zdAdj` | `χ²_lazy(0, 0) = 1 ≠ −1 = (π 0)⁻¹ − 1` (the zero-degree corner makes `π 0 = 0/1 = 0`, so the right side is `0⁻¹ − 1`, junk) |
| `lazyWalkTransitionMatrix_nonneg` | `hnn` (nonnegative entries) | `negOffAdj = !![2,−1;−1,2]]` (symmetric, `deg = 1`, negative off-diagonal) | `P_L 0 1 = −1/2 < 0`. The existing `negDiagAdj` (negative *diagonal*) cannot kill this clause: its off-diagonal `2` keeps every `P_L` entry nonnegative |
| `lazyWalkDistribution_nonneg` | `hnn` | same `negOffAdj` | `ν₁ 0 1 = P_L 0 1 = −1/2 < 0` |
| `stationaryVec_mul_lazyWalkTransitionMatrix` | `hA` (symmetry) | `asymLoopAdj = !![3,3;1,1]]` (nonnegative, degrees `(6, 2)`, `π = (3/4, 1/4)`) | detailed balance at `(0,1)`: `π 0 · P_L 0 1 = 3/16 ≠ 1/16 = π 1 · P_L 1 0` |
| `lazyWalkTransitionMatrixTranspose_mulVec_stationaryVec` | `hA` | same `asymLoopAdj` | `(P_Lᵀ *ᵥ π) 0 = 5/8 ≠ 3/4 = π 0` |
| `lazyWalkDistribution_add_stationary` | `hA` | same `asymLoopAdj` — and the attainment hypothesis is *genuine* here: `ν₁ 0 = row 0 of P_L = (3/4, 1/4) = π` exactly | conclusion at `s = 1`: `ν₂ 0 0 = 5/8 ≠ π 0` — the law passes through `π` at `t = 1` and leaves it at `t = 2` |
| `sum_stationaryVec_smul_sq_pow_lazyWalkTransitionMatrix_le` | `hrate` (the caller's rate certificate) | the triangle `triAdj`, `g = (1,−1,0)` (a genuine `3/2`-mode direction), `r = 1/8 < 1/4`, `t = 1` | `P_L *ᵥ g = (1/4)•g`, so `LHS = (1/3)(1/16 + 1/16) = 1/24 > 1/96 = (1/8)² · (2/3) = RHS` |
| `sum_stationaryVec_smul_sq_pow_lazyWalkTransitionMatrix_le` | `hmode` (zero-mode orthogonality) | `k2Adj`, `g = (1,1)` (the constant zero mode itself), `r = 0` (genuine: the only nonzero mode is `μ = 2` with lazy factor `0`), `t = 1` | `P_L *ᵥ 1 = 1`, so `LHS = ∑ π = 1 > 0 = 0² · ∑ π g² = RHS` |

The `hrate`/`hmode` fences are the lazy twins of the plain family's
C₄ mode-coverage fence: the contraction engine's certificates are
public interface, and the headline supplies them internally with the
intrinsic-rate supplier — a fence proves the clauses are not vacuous
decoration. The certificate-isolation companions verify the *other*
clause genuine at each fixture (K₂'s spectrum pinned by `M² = 2M`; the
triangle's by the existing `tri_eigvalOf_cases` + `tri_kernel_const`).

### Already fenced (verified, no duplication)

- **`hnn` of the signless certificate**
  (`quadForm_two_sub_normalizedLaplacian_nonneg`) —
  `sos_nonneg_fence_QA` at `negDiagAdj`. The derived
  `eigvalOf_normalizedLaplacian_le_two`,
  `secondEval_normalizedLaplacian_le_two`,
  `abs_one_sub_half_eigvalOf_le_one_sub_half_secondEval`, and the
  headline's `hnn` are all consumed through this certificate (the
  derived conclusions' `hnn` acts only through it at the same fixture
  class).
- **The plain family's own fences** (connectivity at `discAdj`, C₄
  mode coverage, the ℓ²→TV mass guard, Pinsker's q-guard) — different
  lemmas, checked for overlap; the lazy family shares none of them.

### Not fenceable (recorded, no action)

- **`hconn` of `lazyChiSquareDistance_le_of_connected`** (and its
  TV/entropy corollaries and both lazy ceilings): a strength-shaped
  hypothesis whose removal keeps the statement *true*. On a
  disconnected graph `λ₂ = 0`, the rate collapses to `1`, and the
  bound degenerates to `χ²_lazy(0, x)` — which still holds because
  every lazy factor `|1 − μ/2| ≤ 1` by PSD + the signless certificate
  alone (no connectivity). Same class as the prior audit's `0 < δ`
  verdict: the clause shapes the proof, not the truth.
- **`hslt` (`λ₂ < 2`) of `lazyWalkDistribution_tvDistance_le_of_depth`**:
  junk-prevention on the threshold's `log (1/rate)` denominator. On
  the connected `λ₂ = 2` class (essentially the single edge) the lazy
  law is exactly stationary after one step (`k2_lazy_law_one_QA`), so
  the conclusion holds anyway; no refutation exists.
- **`hd` of `lazyWalkTransitionMatrix_nonneg` /
  `lazyWalkDistribution_nonneg`**: not load-bearing — at zero degrees
  with nonnegative entries, `P = D⁻¹A` is still entrywise nonnegative
  (`(deg i)⁻¹ ≥ 0` including the junk `0⁻¹ = 0`), so both conclusions
  hold without degree positivity. A removable-hypothesis finding:
  the clause is proof-convenience inherited from
  `walkTransitionMatrix_nonneg`, not truth-shaped.
- **`lazyWalkDensity_succ` / `lazyWalkDensity_sub_one` /
  `lazyChiSquareDistance_eq_sum_smul`**: consumed through detailed
  balance (`fenced above`), row-stochasticity (`fenced above`), and
  `stationaryVec_pos` — no independent falsification surface beyond
  their engines'.
- **The `[Nonempty V]` instance-arguments** — structural (the volume
  positivity and `stationaryVec_pos` arguments need them).

### Priced follow-on (recorded, not this run unless cheap)

- The lazy object's `_spec` witness clause (`hne`) has no junk-corner
  fence: on a disconnected bipartite fixture (`K₂ ⊕ K₂` at `ε = 1/8`)
  the lazy witness set is empty (`TV_lazy(t) ≥ 1/2` at every `t`, the
  law converging to the component-stationary), `t_mix = sInf ∅ = 0`,
  and the dropped-`hne` conclusion fails at `s = 0` (`TV = 3/4`). The
  plain twin's junk corner is fenced (`k2_mix_junk_corner_QA`); this
  completes the pair at the cost of a 4-vertex closed form.

## Statement shapes (recorded before stating)

- Each fence is the **negation of the conclusion at a specific
  instantiation** of the lemma, with both sides computed to numerals —
  so a wrong constant or a dropped clause in a future restatement is
  caught by the fence no longer being about a true-able statement.
- Each fence is paired with an **isolation companion**: every *other*
  hypothesis verified to hold at the fixture, the dropped one verified
  to fail.
- The three new fixtures exist because the existing ones cannot kill
  these clauses: `pathAdj`/`triAdj`/`k2Adj` satisfy every clause;
  `discAdj` is symmetric nonnegative with positive degrees (kills only
  connectivity — non-fenceable here); `negDiagAdj` has a negative
  *diagonal*, which the lazy average `P_L = (P + 1)/2` washes out of
  every off-diagonal entry (its diagonal `P_L 0 0 = (−1 + 1)/2 = 0`
  stays nonnegative), so nonnegativity needs a negative
  *off*-diagonal; `asymLoopAdj`'s `ν₁ = π` structure is what makes the
  attainment-persistence fence's hypothesis genuine.

## Verification plan

Spike in `wip/lazyfences_spike.lean` (zero errors/zero warnings before
any shelf edit); land as `Mixing_QA.lean`'s `LazyFences` section;
`lake env lean` on the touched module; explicit `lake build` target;
`#print axioms` audit on every new declaration (expected: exactly
`propext, Classical.choice, Quot.sound`); full `lake build` +
`check_build_completeness.py`; the full records ladder (`lint_axioms`,
`check_refutation_independence` — no `-- @refutes` tags, these refute
*theorem* instantiations and consume nothing admitted;
`check_public_reachability`, `check_citations`,
`check_markdown_links`, `check_backlog_freshness`, scoreboard
regeneration, map stats sync in both data tables + SVG regeneration +
`check_scaffold_map_freshness`).

## Delivery record

Delivered as `Scaffold/QA/SpectralGraph/Mixing_QA.lean`'s
`LazyFences` section (+65 QA declarations by the generator metric,
3817 → 3882): two generic helpers (the adjoint-on-point-mass row
extraction `transpose_mulVec_single_apply`, the one-step lazy law in
adjoint form `lazyWalkDistribution_one`), the three new fixtures
(`zdAdj`, `negOffAdj`, `asymLoopAdj`) with entry/degree/π value pins,
the ten fences, four fixture isolation companions (including the
attainment fence's `ν₁ = π` genuineness pin `asym_lazy_law_one_QA`),
the triangle-mode companions (`tri_lazy_mulVec_mode_QA` pinning
`P_L *ᵥ g = (1/4) • g` at the `3/2`-mode direction,
`tri_lazy_mode_genuine_QA`, `tri_exists_pos_mode_QA`,
`tri_lazy_rate_fails_QA`), and the edge-mode companions
(`k2_eigvalOf_cases_QA` — every edge eigenvalue `0` or `2` via the
summed eigen equation `μ · (∑ v) = 0` (unit adjacency column sums)
plus the unit-eigenvector quadratic form `μ = 2 − (∑ v)²`, no basis
control, the K₂ twin of the triangle's existing
`tri_eigvalOf_cases`; `k2_lazy_rate_genuine_QA`;
`k2_lazy_mode_fails_QA` — the kernel eigenvector exists by
`exists_eigvalOf_eq_of_mulVec_eq_smul` at `(1,1)`, is constant by
the 2×2 eigen equation, nonzero by `eigvecOf_inner`, and pairs to
`2 · v 0 ≠ 0` against `√D *ᵥ (1,1)`).

Zero axiom contact: `#print axioms` via `wip/lazyfences_axcheck.lean`
on all 68 new declarations — every one exactly `propext,
Classical.choice, Quot.sound`. No `-- @refutes` tags added (these
refute *theorem* instantiations; nothing admitted is consumed, and
`check_refutation_independence` stays at its 9-tag clean state).

**Technique findings** (recorded for future QA runs):

1. `fin_cases` on a `Fin 2` hypothesis variable leaves an
   `id`-motive wrapper (`(fun i => i) ⟨0, ⋯⟩`) that `rw` cannot see
   through — the same trap the 2026-09-02 fence delivery recorded.
   The working idiom remains rewriting the *variable*:
   `rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]`
   (omega proves Fin-valued case splits in the pinned Mathlib).
2. A leading-dot method call split across lines
   `(x\n  .method arg)` inside an outer application parses the dot
   onto the *outer* term — `(isHermitian_of_isSymm h).mulVec_eigenvectorBasis i`
   must stay on one line, or be bound to a `have` first. The error
   ("function expected at …") points at the receiver, not the parse.
3. `eigvalOf M hM i` and the raw `(isHermitian_of_isSymm hM).eigenvalues i`
   are definitionally equal but never syntactically matched by `rw` —
   to rewrite an eigenvalue hypothesis into a raw
   `mulVec_eigenvectorBasis` fact, restate it in the raw spelling via
   `have hz : (….eigenvalues i) = 0 := hi` (defeq coercion) and
   rewrite with that.
4. `Finset.sum_ite_eq'` takes the Finset *first*
   (`Finset.sum_ite_eq' Finset.univ b _`); passing a membership proof
   where the set is expected produces a confusing metavariable type
   error. (Companion to the 2026-09-02 finding on `Finset.sup'_le`
   argument order.)
5. The pre-existing info-level `Try this: ring_nf` hints in
   `Mixing_QA.lean` (two with positions, one without) are on the HEAD
   baseline — verified this run by elaborating the HEAD copy of the
   module separately. They are not warnings and not introduced by new
   work; future runs should not chase them as regressions.
6. Fixture entry lemmas with `if i = j then _ else _` conditions
   close by `rfl` after `fin_cases` (the Fin decidable instances
   reduce definitionally); `∧`-shaped or numeral-comparison
   conditions do not — state them per concrete index or keep the
   `i = j` shape.

**Verification** (all commands run this delivery, before recording):
spike first (`wip/lazyfences_spike.lean`, iterated to zero
errors/zero warnings before any shelf edit); `lake env lean` on the
touched QA module — zero new errors/warnings (the two positioned
info-level `ring_nf` hints confirmed pre-existing on the HEAD
baseline); explicit `lake build Scaffold.QA.SpectralGraph.Mixing_QA`
✔; the 68-declaration axiom audit above; full `lake build` ✔
immediately followed by `check_build_completeness.py` (133 source
files, 133 fresh artifacts, 0 stale, 0 missing, exit 0); `lint_axioms`
exit 0 (4 current axioms, unchanged; only the allowlisted-confirmed
PF finding); `check_refutation_independence` (9-tag clean);
`check_public_reachability` clean (63 repo modules); `check_citations`
("All axioms have proper citations!"); `check_markdown_links` clean;
`check_backlog_freshness` clean; scoreboard regenerated (**3882/4/0**);
map stats synced 3817 → 3882 in both data tables, SVG regenerated,
`check_scaffold_map_freshness` exit 0 (45 stations, no station's
proposal status changed — this proposal has no station).

Records updated: this proposal, `proposals/README.md` (new Delivered
row), README (3882 + the walks-and-mixing row's lazy-fence clause),
the radar (QA axis synced 3817 → 3882, score held 4.5 per protocol —
negative witnesses of an already-counted family), `index/map/spectral_graph.md`
(the LazyFences paragraph + the QA-module count sync), the backlog
item-8 sixteenth update, the scoreboard verification row, both map
data tables + regenerated SVG, the execution plan, and the activity
log. Nothing committed; the prior runs' uncommitted deliveries
preserved.

**Remaining risk:** none owed by the delivery — QA-only, no axiom
disposition changed, no public statement changed. Honest scope: the
audit covered exactly one family (the lazy sections of `Mixing.lean`
plus `Oversmoothing.lean`'s `LazyMixingTime`); the conjugated-norm
contraction twin
(`dotProduct_self_degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix_contraction`)
shares both certificate clauses with the fenced ℓ²(π) twin but has no
fence of its own (priced follow-on: the same two fixtures refute it,
the computation is the √D-weighted mirror of the delivered pair); the
lazy object's `_spec` witness clause (`hne`) junk corner at a
disconnected bipartite fixture is priced above; the broader
audit-shaped pass over the *remaining* mixing-cascade families
(entropy, Poisson bridge, primitivity supplier) stays open with the
method now twice exercised.
