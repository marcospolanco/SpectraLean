# Proposal: The Lazy Random Walk — the Discrete Mixing Program's Periodicity Fix

**Status:** COMPLETE — proposed and delivered in the same run
(`20260901T202735Z-run-1`), per the same-run pattern of
`poincare-inequality.md` and `heat-variance-decay.md`. Zero new axioms
(count stays 5): every statement below is a corollary of proved shelf
engines plus one new elementary inequality (the signless-Laplacian
sum-of-squares). `#print axioms` on all 62 new declarations (38 shelf
+ 24 QA): exactly `propext, Classical.choice, Quot.sound`.

Companion to [Strategy](../docs/1_STRATEGY.md) and to the mixing
program (`mixing-time-bound.md`, `total-variation-mixing-conversion.md`,
`continuous-time-chi-square-mixing.md`), whose module
(`GraphTheory.Mixing`) hosts the delivery.

---

## Clean-room boundary

This planning document is internal prioritization and analysis. If
counsel approves a public repository export, restate the technical
specifications independently from standard textbook sources (lazy
Markov chains and their spectral analysis are classical; see Sources
below). Do not copy this proposal verbatim.

## The obligation this discharges

The discrete mixing program's every certificate family — the χ² decay
bound's caller-supplied rate `r < 1`, the depth-form oversmoothing
ceiling, the `t_mix` spectral ceilings (per-start and uniform), the
Dobrushin uniform witness — is **provably unsatisfiable on connected
bipartite graphs**: `λ_max(L_sym) = 2` there, so the top walk mode
carries factor `|1 − 2| = 1` and no `r < 1` certificate exists. This is
not a corner case; it is every path, every tree, every even cycle. The
QA program has fenced it repeatedly as a *never-decay* pin in three
metrics (χ² `≡ 1`, TV `≡ 1/2`, `D ≡ log 2` on `K₂`; the uniform
`d(1) = 1` maximal fence; the `P₃` oscillation cross-check) — always as
a boundary of the plain family, never with a discrete fix on offer.

The recorded fix so far was to leave discrete time and use the
continuous family, whose delivery record names its advantage: "the
continuous rate `e^{−λ₂t}` is intrinsic, where the discrete theorem
needs an `r` certificate". **This delivery brings that advantage back
to discrete time** through the field-standard time-change: the *lazy*
walk `P_L = (P + I)/2` (Levin–Peres–Wilmer ch. 5.2's canonical
convention for discrete-time mixing), whose mode factors are
`1 − λ/2 ∈ [0, 1]` — so on every connected graph the intrinsic rate
`1 − λ₂(L_sym)/2 < 1` holds with connectivity as the only graph
hypothesis, bipartite or not.

### Named consumers (the leverage case)

1. **The bipartite class.** On `K₂`, paths, trees, even cycles: the
   plain family's hypothesis sets are unsatisfiable (fenced on file);
   the lazy family's are satisfiable, and its rate is *computed* from
   the spectrum rather than hypothesized. On `K₂` the rate is exactly
   `0` — the lazy walk mixes in one step, and the delivered bound is
   attained at `0 = 0` (QA).
2. **LPW's canonical discrete treatment.** Levin–Peres–Wilmer develop
   discrete-time mixing on the lazy chain precisely to remove
   periodicity; the delivered uniform-`t_mix` and escalation families
   get non-vacuous discrete instances on bipartite input by
   composition with this section's rate corollary.
3. **The discrete/continuous parity.** The continuous family's
   recorded intrinsic-rate advantage now exists on both sides of the
   Poisson bridge; the lazy operator is the discrete object whose
   spectrum sits in `[0, 1]`, exactly as the heat kernel's sits in
   `[0, 1]` after `e^{−λt}`.

## Statement design (settled before any Lean)

- **Carrier**: `lazyWalkTransitionMatrix A := 2⁻¹ • (walkTransitionMatrix A + 1)`.
  LPW's convention (stay-or-move, probability `1/2` each). No new
  carrier type; the object lives beside `walkTransitionMatrix` in the
  same module.
- **Objects**: `lazyWalkDistribution` (recursive law, the plain
  object's exact idiom at the lazy matrix), `lazyWalkDensity`, and
  `lazyChiSquareDistance` stated *in the sum-div shape* so the
  delivered `klDiv_le_sum_sq_div` composes by `.trans` without a
  bridge lemma (the scoping lesson of the continuous twin's
  `_eq_sum_div`).
- **The rate is intrinsic and inline** — no hypothesis-shaped `r`. The
  headline mirrors `contChiSquareDistance_le`'s hypothesis set
  (`hA`, `hnn`, `hd`, `hcard : 2 ≤ card V`, `hconn`) rather than the
  plain family's, precisely because `secondEval` enters the statement.
  This is the delivery's point.
- **The mode hypothesis is derived, not assumed**, by *reusing the
  delivered connectivity mode derivation verbatim*
  (`eigvecOf_dotProduct_degreeSqrt_walkDensity_sub_one_of_eigvalOf_eq_zero`
  is a statement about the initial density, which the lazy walk
  shares).
- **The new engine piece**: the eigenvalue bound
  `eigvalOf_normalizedLaplacian_le_two`. Route: the signless-Laplacian
  sum-of-squares
  `xᵀ(2·I − L_sym)x = (1/2) ∑ i j, A i j (u i + u j)²` at
  `u = (1/√D) *ᵥ x` (the identity `D − L = A` making
  `2uᵀDu − uᵀLu = uᵀ(D + A)u`), evaluated at a unit eigenvector through
  `quadForm_eigvecOf_self`. Together with PSD (`0 ≤ μ`) and the
  delivered `secondEval_le_eigvalOf_normalizedLaplacian_of_ne_zero`
  (`λ₂ ≤ μ` for `μ ≠ 0`) this yields
  `|1 − μ/2| = 1 − μ/2 ≤ 1 − λ₂/2` — no sign hypothesis on the rate
  needed anywhere (the contraction engine's own recorded design
  decision).
- **Degenerate corners checked before stating**: `π i = 0` junk (same
  as the plain objects, `hd`-guarded); `t = 0` (the bound reads
  `χ²(0) ≤ 1 · χ²(0)`, trivially true, no special case);
  `card V ≤ 1` (excluded by `hcard`, mirroring the continuous family);
  disconnected input (`hconn` required — the mode hypothesis genuinely
  fails for a one-component start, exactly as in the plain family);
  and the `λ ≤ 2` engine's `hnn` (a negative-diagonal two-vertex
  fixture with positive degrees refutes the dropped form — fenced in
  QA).

## The Lean (delivered)

New `LazyWalk` section at the end of
`Scaffold/Mathlib/GraphTheory/Mixing.lean` (18 declarations):

- `lazyWalkTransitionMatrix` (def), `_apply` (entry formula),
  `_mulVec_one` (`P_L *ᵥ 1 = 1`), `_nonneg`;
- `lazyWalkDistribution` (def), `_zero`, `_succ`, `sum_`,
  `_nonneg`;
- `lazyWalkDensity` (def), `lazyWalkDensity_succ` (detailed-balance
  clone), `lazyWalkDensity_sub_one` (centered evolution);
- `lazyChiSquareDistance` (def, sum-div shape), `_eq_sum_smul`,
  `_zero`;
- the signless engine: `quadForm_two_sub_normalizedLaplacian_eq_sum`
  (the SOS identity), `quadForm_two_sub_normalizedLaplacian_nonneg`,
  `eigvalOf_normalizedLaplacian_nonneg`,
  `eigvalOf_normalizedLaplacian_le_two`;
- the lazy decay engine: `degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix`
  (conjugated-power transfer at `1 − (1/2)•L_sym`),
  `one_sub_half_normalizedLaplacian_mulVec_eigvecOf` (eigenaction),
  `eigvecOf_dotProduct_degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix`
  (eigencoordinate evolution at `(1 − μ/2)^t`),
  `dotProduct_self_degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix`
  (Parseval-exact identity),
  `sum_stationaryVec_smul_sq_pow_lazyWalkTransitionMatrix_le`
  (ℓ²(π) contraction, rate-shaped);
- the assembled intrinsic rate
  `abs_one_sub_half_eigvalOf_le_one_sub_half_secondEval`;
- **the headline**
  `lazyChiSquareDistance_le_of_connected`
  (`χ²_lazy(t, x) ≤ (1 − λ₂(L_sym)/2)^{2t} · ((π x)⁻¹ − 1)`);
- the corollaries `lazyWalkDistribution_tvDistance_le_of_connected`
  (`TV ≤ (1/2)·(1 − λ₂/2)^t·√((πx)⁻¹−1)`) and
  `klDiv_lazyWalkDistribution_le` (entropy decay at the same
  intrinsic rate).

QA: the new `LazyWalk` section of `Scaffold/QA/SpectralGraph/Mixing_QA.lean`
(17 declarations), on the file's existing fixtures:

- **`K₂` (bipartite, cert-free for the plain family)**: the law pin
  `ν_lazy(1) = (1/2, 1/2)`, **χ² `= 0` at every `t ≥ 1`** (attained:
  the rate is exactly `0` at the pinned gap `λ₂ = 2`, so the bound is
  `0 ≤ 0` — exact attainment at every time), TV `= 0`, and the
  **one-step contrast pair** against the plain walk on the same start
  (plain χ² `≡ 1` forever — proved here as the `P₃`-twin oscillation
  pin at `K₂` — against lazy `0`).
- **`P₃` (bipartite path, pinned gap `λ₂ = 1`)**: the center start is
  the pure periodic mode — **lazy χ² `(1) = 0`, TV `= 0`, the law
  exactly stationary in one step** (raw iteration), against the
  plain-witness **never-decay pin `χ²_plain(t, center) = 1` at every
  `t`** (the oscillation `P(h₀ − 1) = −(h₀ − 1)`, by induction — the
  same start, same graph, lazy exactly stationary); the corner start
  at `t = 1, 2` (`χ²_lazy = 1/2`, `1/8` — the honest intrinsic rate
  `1/2` at work) with both bound instances evaluated at the pinned gap
  (`1/2 ≤ 3/4`, `1/8 ≤ 3/16`, slack witnessed); the `t = 0`
  normalization `χ²_lazy(0) = 3`; the lazy matrix itself pinned raw.
- **The signless engine**: the tightness pin at the `K₂` top mode
  (`quadForm (2·I − L_sym) (1,−1) = 0` — the bipartite mode saturates
  `μ ≤ 2` exactly, the boundary the plain family dies on), and the
  **`hnn` fence** at the negative-diagonal two-vertex fixture
  (`!![−1, 2; 2, −1]`: symmetric, positive degrees, only the
  nonnegativity clause violated — `quadForm (2·I − L_sym) (1,−1) =
  −4 < 0`, the dropped conclusion refuted in proved form).

## Acceptance criteria — all met

- Zero new axioms: `#print axioms` on every new declaration (shelf and
  QA) reads exactly `propext, Classical.choice, Quot.sound`.
- The full ladder passes: direct elaboration of both touched modules,
  explicit build targets, full `lake build` +
  `check_build_completeness.py`, `lint_axioms.py`,
  `check_refutation_independence.py`, `check_public_reachability.py`,
  `check_citations.py`, `check_markdown_links.py`, scoreboard
  regeneration, `check_scaffold_map_freshness.py` after the stats
  sync.
- The `K₂` QA witnesses the headline attained exactly (`0 = 0` at the
  pinned gap) — the strongest QA shape a bound theorem can have, on
  the fixture where the plain family is provably certificate-free.
- The `hnn` hypothesis of the new engine lemma is fenced in proved
  form.

## Delivery record

**DELIVERED 2026-09-01** (run `20260901T202735Z-run-1`, session
`ses_fa1583607ffesbV61DnEEpEvRN`). The spike
(`wip/lazywalk_spike.lean`) held the shelf section, the QA section,
and the axiom audit together and was iterated to **zero errors / zero
warnings** before any shelf edit; landing transferred both sections
verbatim (the shelf into `Mixing.lean`'s new `LazyWalk` section, the
QA into `Mixing_QA.lean`'s new `LazyWalk` section), with `lake env
lean` clean on both touched modules afterwards.

**Landed inventory** (larger than the sketch above — the QA-driven
additions are marked): 38 shelf declarations — the objects
(`lazyWalkTransitionMatrix` + `_apply`/`_mulVec_one`/`_nonneg`,
`lazyWalkDistribution` + `_zero`/`_succ`/`sum_`/`_nonneg`,
`lazyWalkDensity` + `_zero`/`_succ`/`_sub_one`,
`lazyChiSquareDistance` + `_eq_sum_smul`/`_zero`), *QA-driven*
`stationaryVec_mul_lazyWalkTransitionMatrix` (lazy detailed balance),
`lazyWalkTransitionMatrixTranspose_mulVec_stationaryVec` and
`lazyWalkDistribution_add_stationary` (attainment persists — the
every-time pins' engine), the generic `quadForm_sub_eq` /
`quadForm_add_eq` / `quadForm_degreeMatrix_eq`, the signless engine
(`quadForm_degreeMatrix_add_eq_half_sum`,
`quadForm_two_sub_normalizedLaplacian_eq`/`_nonneg`,
`eigvalOf_normalizedLaplacian_nonneg`/`_le_two`), the lazy decay
engine (`degreeSqrt_mul_lazyWalkTransitionMatrix_eq`,
`degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix`,
`eigvecOf_dotProduct_one_sub_half_normalizedLaplacian_mulVec`,
`eigvecOf_dotProduct_degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix`,
`dotProduct_self_degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix`,
the `_contraction` twin,
`sum_stationaryVec_smul_sq_pow_lazyWalkTransitionMatrix_le`), the
rate assembly `abs_one_sub_half_eigvalOf_le_one_sub_half_secondEval`,
and the three consumers. QA: 23 theorems + the `negDiagAdj` fixture
family (5 helpers), exactly as planned above.

**Verification:** `lake env lean` zero errors/zero warnings on both
touched modules; explicit `lake build` targets ✔ on both; **`#print
axioms` on all 62 new declarations: every one exactly `propext,
Classical.choice, Quot.sound`** — zero contact with any admitted
axiom; **full `lake build` ✔ immediately followed by
`check_build_completeness.py` — 133 source files, 133 fresh
artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` exit 0 (5, both
PF findings allowlisted-confirmed); `check_refutation_independence`
(10-tag clean — no tags added, nothing here touches an axiom);
`check_public_reachability` clean (63 repo modules); `check_citations`
("All axioms have proper citations!"); `check_markdown_links` clean;
scoreboard regenerated (**3589/5/0**, +23) with the verification row;
**map-freshness exit 0** after the 3566 → 3589 stats sync in both map
files and SVG regeneration (the proposal has no station — no tier
change). Records updated: README (3589 + the walks-and-mixing row's
lazy-walk extension), the radar (QA axis synced 3566 → 3589 held at
4.0; axis 5's narrative extended, held 4.5),
`index/map/spectral_graph.md` (18 new rows in the new Mixing/lazy-walk
table), both map data tables + regenerated SVG, both QA modules'
purpose headers, the backlog item-2 update, this proposal,
`proposals/README.md` (new Delivered row), the execution plan, and
the activity log. Nothing committed; the previous runs' uncommitted
deliveries preserved.

### Technique findings (recorded at landing)

1. **`∑ i j, f i j` is not valid Lean 4 notation** — the big-operator
   `∑` takes at most one binder plus an optional `∈`; multi-binder
   sugar works for `∀` but not for `∑`. The double sums must be
   spelled `∑ i, ∑ j, f i j` (the shelf's own `quadForm_eq_sum` uses
   the fully explicit `∈` form).
2. **`λ` is a reserved token, not an identifier character** — `hλ`
   fails to parse ("unexpected token 'λ'") because λ lexes as the
   anonymous-function keyword; `hμ` (mu) is fine, `hλ` is not. The
   shelf's own convention of `hμ` had hidden this.
3. **`Matrix.diagonal`'s entries are a *dependent* `dite`** —
   `degreeMatrix` unfolds to `if h : i = j then deg A i else 0`, so
   `Matrix.diagonal_apply`/`if_pos` do not apply; `dif_pos rfl` /
   `dif_neg` are the right lemmas.
4. **The elaborator is a genuine arithmetic referee**: the first draft
   of the `P₃` lazy-matrix QA claimed `lazyP 0 1 = 1/4` (confusing row
   0 with row 1); `simp` reduced the wrong claim to `False` exactly as
   designed. Corrected to `1/2` (row 0 of `P` is `(0, 1, 0)`).
5. **Matrix-literal entry indexing under `fin_cases` can leave
   irreducible `vecHead (vecTail fun i => …)` residue** when the
   literal is compared entrywise against a computed expression — the
   robust QA idiom is concrete-index entry pins
   (`lazyWalkTransitionMatrix pathAdj 0 1 = 1/2`), not whole-matrix
   literal equalities.
6. **`funext i` under `fin_cases` produces beta-redex hypotheses**
   (`(fun i => i) ⟨0, ⋯⟩`) that defeat `rw [lemma i]` — `simp
   [lemma]` with the lemma left to instantiate is the reliable form.
7. **`norm_num` does not evaluate `|numeral|` in this pin's shape** —
   the absolute-value terms of the TV pin needed an explicit
   `rw [show |((0:ℝ) − 1/2)| = 1/2 from by norm_num]`.
8. **The stale-olen import-boundary recurrence, again**: `lake env
   lean` on the QA module after a shelf edit needs the shelf's `lake
   build` target rebuilt first — the QA module resolves new names only
   through the fresh olean, not the working tree.

## Deferred (named, not queued)

- The lazy twin of the depth-form oversmoothing ceiling and the
  `t_mix` objects (`Oversmoothing.lean` statements at
  `lazyWalkDistribution`) — one composition each once a consumer names
  a bipartite-input instance; the Mixing-local rate corollaries
  delivered here are the interface they would consume.
- The lazy uniform-`t_mix` (`walkMixingTime` at the lazy matrix) and
  its Dobrushin class — the delivered uniform family's statements
  transfer verbatim; gated on the same consumer naming.

## Sources

- Levin, Peres & Wilmer, *Markov Chains and Mixing Times* (2nd ed.),
  ch. 5 (lazy chains as the canonical discrete-time convention) and
  ch. 6 (the spectral bound `χ² ≤ (1 − λ₂/2)^{2t}` form at the lazy
  chain). Section-level locator; no page numbers recorded (repository
  policy: confirmed locators only).
- Montenegro & Tetali, "General bounds on the mixing time of Markov
  chains" — the lazy-chain spectral package.
- The signless-Laplacian identity `2·I − L_sym = D^{-1/2}(D + A)D^{-1/2}`
  and `Q = D + A` PSD on nonnegative weights is classical (Brouwer &
  Haemers, *Spectra of Graphs*, ch. 1 — `λ_max(L_sym) ≤ 2` with
  equality iff bipartite); only the inequality is used here, not the
  equality characterization.
