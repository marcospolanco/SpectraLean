# Proposal: Multiway Expansion — the Higher-Order Cheeger Easy Direction

**Status:** COMPLETE — Step 0 (the survey) + Step 1 (the easy direction's
every-family form) delivered 2026-08-26, and the priced follow-on — the
ρ_k partition-minimum packaging — delivered 2026-08-26 by run
`20260826T181445Z-run-1` (the delivery record at the bottom). Opened by
run `20260826T083858Z-run-1` (the Step-0 verdict below, recorded before
any shelf Lean, plus the full spike `wip/mw_spike.lean`), landed by
continuation `20260826T133118Z-run-1` (engine, application layer,
headlines, QA), and verified/recorded by continuation
`20260826T165654Z-run-1` after the middle session ended before
verification. Selected per the empty High/Medium Active table by the
center-out policy as the execution plan's named top candidate — the
irregular family's last priced follow-on, priced there as "a multi-run
program; a dedicated run should start with that Step-0, not with
definitions"; the Step-0 verdict below dissolved both priced
obstructions, collapsing the program to one delivery. Zero axioms
admitted, nothing committed, nothing published.

The remaining priced follow-on is the multiway *hard* direction only
(multi-run, gated on a named consumer) — this proposal's own scope
(the easy direction) is fully delivered regardless.

## The obligation this discharges

`docs/6_SGT_BACKLOG.md` item 3 records multiway expansion (higher-order
Cheeger, k-way conductance) as the expansion-interfaces item's only
remaining named residue, and `docs/7_SGT_RADAR.md` axis 4 records it as
the axis's remaining absent category. The delivered irregular Cheeger
pair (`cheeger_upper_bound_normalized`,
`cheeger_lower_bound_normalized`, the sweep extractions, the Fiedler
instantiation — all 2026-08-25/26) is the k = 2 instance of the
higher-order family; every statement in the family generalizes `k` to a
disjoint family of parts, and none of the k = 2 engines generalizes by
substitution (see Step 0).

## Step 0 — the survey (verdict recorded before any shelf Lean)

**Question 0.1 — what does the easy direction's honest proof actually
need?** The prior pricing (in the execution plan's Active block at the
last boundary and in backlog item 3) named two candidate routes:
quotient-matrix/interlacing, or an iterated 2-way assembly — and priced
the program as multi-run on the strength of two anticipated
obstructions: "(a) a partition-space definition with attainment, (b) the
centered-indicator test functions sum to zero, and linear combinations
re-introduce cross-part energy."

The survey's decisive finding: **both obstructions dissolve at the
every-family statement form.**

- (a) *Attainment is not needed.* The ρ_k form (the minimum of
  `max_i φ(S_i)` over k-way partitions) needs a partition-space
  attainment argument — but the strictly-more-usable **every-family
  form** ("for every disjoint nonempty k-family, `λ_k ≤ 2 · max_i φ`")
  certifies at any concrete family with no minimization at all. QA can
  instantiate concrete families; consumers get a usable certificate
  whenever they hold any disjoint family. The ρ_k packaging remains a
  priced follow-on (attainment over the finite partition space, the
  `sweep_level_extract_vol` pattern at partition level).
- (b) *Cross-part energy is absorbed, not eliminated.* The classical
  easy direction (Lee–Gharan–Trevisan, *Higher-Order Cheeger
  Inequalities*, STOC 2012 / JAMS 2014, the λ_k ≤ 2ρ_k half; the
  every-family form of its subspace argument) uses the **plain,
  uncentered part indicators** as the test family, with the subspace
  (Rayleigh–Ritz) engine in place of orthogonality-to-kernel. No
  centering is required — the pricing's "centered indicators sum to
  zero" concern was an artifact of trying to reuse the delivered k = 2
  kernel-based engine (`secondEval_le_rayleigh_of_ker`), whose
  hypothesis shape (orthogonality to one kernel vector) does not
  generalize to k dimensions. In the subspace engine, a linear
  combination `∑ cᵢ·1_{Sᵢ}` does re-introduce cross-part energy
  `2cᵢcⱼ·xᵀLxⱼ` — but each pair's contribution is bounded pointwise by
  `(a − b)² ≤ 2a² + 2b²`, so the total is absorbed at exactly constant
  2: `xᵀ L x ≤ 2 ∑ᵢ cᵢ² · boundary(Sᵢ)` for every combination. The
  constant-2 is the theorem's constant-2.

**Question 0.2 — what is genuinely new engine content?** Two pieces,
both k-general and both reusable beyond this theorem:

1. **The order-statistics ↔ counting bridge** for the sorted spectrum:
   `evals_le_of_card_eigvalOf_le` — if at least k+1 eigenbasis
   eigenvalues are ≤ t, the k-th sorted entry is ≤ t. The shelf has
   exactly the two endpoint instances (`evals_first_le_eigvalOf`,
   `eigvalOf_le_evals_last`); the middle is new, proved by an induction
   on the sorted list (all entries past an index > t are > t).
   Spin-off lemmas with independent QA value: `evals_sum_eq_trace`
   (∑ of sorted entries = trace — the trace-pinning technique the
   Cheeger_QA header documents, now at the sorted API) and
   `exists_eigvalOf_eq_of_mulVec_eq_smul` (an exhibited eigenvector at
   μ lands some basis eigenvalue at μ — the eigenvalue-witness bridge
   QA needs to pin spectra without computing them).
2. **The general-k subspace Rayleigh–Ritz engine**:
   `evals_le_of_linearIndependent` — a k-dimensional subspace on whose
   every combination `quadForm ≤ t · ‖·‖²` certifies `evals ⟨k−1⟩ ≤ t`,
   no PSD and no kernel hypothesis. Proof: the k−1 smallest-eigenvalue
   eigenvectors impose at most k−1 orthogonality constraints on the
   k-dimensional combination space, so a nonzero combination survives
   them (`LinearMap.ker_ne_bot_of_finrank_lt`); its eigen-expansion
   lives on eigenvalues > t, contradicting the bound strictly. This is
   the engine every future k-way statement (and any interlacing-shaped
   result) consumes; the delivered k = 2 engines are its `w`-kernel
   specializations.

**Question 0.3 — what exists already?** Confirmed by direct read:
`laplacian_quadForm` (the Dirichlet edge-sum form — the absorption
lemma's substrate), `quadForm_eigvalOf`/`dotProduct_eigvecOf`
(the eigenbasis expansion + Parseval — the engine's expansion step),
`quadForm_congr`/`quadForm_laplacian_eq_quadForm_normalizedLaplacian`/
`dotProduct_degreeSqrt_mulVec` (the irregular family's congruence
bridge — the headline's transfer, consumed verbatim),
`vol_pos_of_pos_deg`, `boundary_nonneg`, `eigvalOf_le_evals_last`,
`evals_mem_eigvalOf`, and the QA file's P₃/K₂ pin infrastructure
(`icPathAdj_secondEval_eq_one`, the K₂ `λ₂ = 2` pin). Mathlib (pinned
snapshot, re-checked this run): `Multiset.sort_eq` (the sort round-trip
— the counting bridge), `Multiset.filter_map`,
`LinearMap.ker_ne_bot_of_finrank_lt`, `Matrix.rank_le_card_height`;
no k-th-eigenvalue min-max or order-statistics fact anywhere in the pin
(the shelf's own `spectralGap` def confirms the API surface stops at
adjacent-index differences).

## The statement (the every-family form, volume-weighted measure)

On every symmetric nonnegative positive-degree graph, for every `k`
with `1 ≤ k ≤ card V` and every family of nonempty pairwise-disjoint
vertex sets `S₁, …, S_k` (a *disjoint family*, deliberately not a
partition — it need not cover `V`):

- **Main (boundary/volume form):**
  `evals (L_sym) ⟨k−1⟩ ≤ 2 · max_i (boundary A (S i) / vol A (S i))`.
- **Corollary (conductance form, `2 ≤ k` so complements are
  nonempty):** `evals (L_sym) ⟨k−1⟩ ≤ 2 · max_i (conductance A (S i))`,
  since `boundary/vol ≤ boundary/min(vol, volᶜ) = conductance`.

This is the higher-order generalization of the delivered
`cheeger_upper_bound_normalized` (its k = 2 instance, restated at the
family form, is recovered exactly: the disjoint pair `S, Sᶜ` gives
`λ₂ ≤ 2·max(b(S)/vol S, b(Sᶜ)/vol Sᶜ)` — the easy direction's
`2·boundary·volV/(volS·volSᶜ)` test-vector bound at the pair's two
singleton families' maximum). Provenance: the classical statement and
subspace route are Lee–Gharan–Trevisan (above) — provenance only; every
statement here is proved (zero new axioms).

## Non-goals

- The ρ_k partition-minimum constant and its attainment (a priced
  follow-on; needs the finite partition-space minimization).
- The multiway *hard* direction (λ_k's lower side /
  higher-order Cheeger from above: `ρ_k ≲ k³√λ_k`-shaped bounds) —
  genuinely multi-run, unchanged by this delivery.
- No new axioms, no changes to existing declarations, no directed or
  magnetic statements.

## QA obligations

1. **K₂, k = 2, singletons:** `λ₂ = 2 ≤ 2·1` — tight equality at the
   pinned exact `λ₂ = 2` (both statement forms).
2. **P₃, k = 2, the non-covering family `{0}, {2}`:** `λ₂ = 1 ≤ 2·1`
   joined to the file's exact pin — documents the every-family (not
   partition) scope.
3. **P₃, k = 3, the singleton partition:** `λ₃ = 2 ≤ 2·1` — equality,
   with `λ₃ = 2` pinned independently (trace `= 3` via
   `evals_sum_eq_trace` + the pinned `λ₂ = 1` + PSD nonneg + the
   eigenvector `![1, −√2, 1]` at 2 via
   `exists_eigvalOf_eq_of_mulVec_eq_smul` +
   `eigvalOf_le_evals_last`).
4. **C₄, k = 4, singletons:** `λ₄ = 2 ≤ 2·1` — equality at `k = n`
   (all-rational fixture: degrees 2 ⇒ `L_sym = I − A/2`).
5. **C₄ overlap fence (the load-bearing fence):** the cyclic-pair
   family `{0,1}, {1,2}, {2,3}, {3,0}` — every other hypothesis
   verified (nonempty, φ = 1/2 each, computed raw), disjointness
   provably fails, and the dropped conclusion is refuted: `λ₄ ≥ 2 > 1 =
   2·max φ`. Disjointness is exercised, not decorated.
6. **k = 1 edge instance** on P₃ (`evals ⟨0⟩ = 0 ≤ 2·φ`): exercises the
   engine's zero-constraint edge.

## Acceptance bar

- Zero new axioms; `#print axioms` on every new public and QA
  declaration reads exactly `propext, Classical.choice, Quot.sound`.
- Direct elaboration of every changed module; explicit build targets;
  full `lake build` + `check_build_completeness.py` fresh;
  `lint_axioms`, `check_citations`, `check_markdown_links` pass;
  scoreboard regenerated idempotent.
- QA non-circular: every spectral pin used by an instance predates the
  multiway family or is produced by an independent route (raw
  eigenvector checks, trace arithmetic), never by the theorem being
  instantiated.

## Delivery record

**Delivered 2026-08-26 (runs `20260826T083858Z-run-1` →
`20260826T133118Z-run-1` → `20260826T165654Z-run-1`, the last performing
the from-scratch verification and this record). Zero new axioms (count
stays 10; `#print axioms` via `wip/mw_axcheck.lean` on all 33 audited
declarations — 15 public + 18 QA headline/pin — reads exactly `propext,
Classical.choice, Quot.sound`, every one; zero contact with the ten
admitted axioms). QA 2349 → 2422 (+73, `MultiwayCheeger_QA` a new file,
75 theorem declarations by direct count).**

**Layer 1 — the engine (`Spectral.lean`, k-general and reusable beyond
this theorem):** `evals_le_of_card_eigvalOf_le` (the
order-statistics↔counting bridge: at least `k+1` eigenbasis eigenvalues
≤ `t` forces the `k`-th sorted entry ≤ `t`; the shelf had exactly the two
endpoint instances), `evals_le_of_linearIndependent` (the general-k
subspace Rayleigh–Ritz engine: a `k`-dimensional linearly independent
family whose every combination satisfies `quadForm ≤ t · ‖·‖²` certifies
`evals ⟨k−1⟩ ≤ t` — no PSD, no kernel hypothesis; the k−1
smallest-eigenvalue eigenvectors impose at most k−1 constraints on the
k-dimensional combination space, so a nonzero survivor exists by
`LinearMap.ker_ne_bot_of_finrank_lt`, and its eigen-expansion
contradicts the bound strictly), plus the two QA-support spin-offs
`evals_sum_eq_trace` (the sorted entries sum to the trace — the
trace-pinning technique at the sorted API) and
`exists_eigvalOf_eq_of_mulVec_eq_smul` (an exhibited eigenvector at `μ`
lands some basis eigenvalue at `μ` — the eigenvalue-witness bridge QA
needs to pin spectra without computing them).

**Layer 2 — the application (`Multiway.lean`, new module, umbrella
import):** `partIndicator`/`multiwayCombination` (the plain, uncentered
part indicators and their combinations), the per-part energy identity
`quadForm_laplacian_partIndicator` (`xᵀLx = boundary` at the indicator —
load-bearing on `laplacian_quadForm`), the weighted-norm identity
`dotProduct_degreeSqrt_mulVec_multiwayCombination` (`‖√D · ∑ cᵢ1_{Sᵢ}‖²
= ∑ cᵢ² vol(Sᵢ)`), **the absorption lemma**
`laplacian_quadForm_multiwayCombination_le` (`xᵀLx ≤ 2 ∑ cᵢ²
boundary(Sᵢ)` for every combination — each crossing pair's contribution
bounded pointwise by `(a−b)² ≤ 2a² + 2b²`; the theorem's constant 2 is
exactly this absorption constant), and the headlines
**`cheeger_upper_bound_multiway`** (`evals (L_sym) ⟨k−1⟩ ≤ 2 · maxᵢ
boundary(Sᵢ)/vol(Sᵢ)` for every disjoint nonempty k-family, at the
every-family form: no partition-space attainment, no ρ_k minimum) and
**`cheeger_upper_bound_multiway_conductance`** (the conductance form at
`2 ≤ k`, where every complement is nonempty). The linear independence of
the pulled-back family comes from `√D` invertibility (`hd`) plus parts
nonempty — no centering anywhere; the `k = 2` instance at the pair `S,
Sᶜ` recovers the delivered `cheeger_upper_bound_normalized`'s content.

**Layer 3 — QA (all six obligations, non-circular by independent
routes):** (1) K₂ `k = 2` singletons — tight equality `2 = 2·1` in both
statement forms, the `≥` side the raw anti-aligned-eigenvector pin
(`mwEdgeAdj_secondEval_ge_two`), the `≤` side the theorem; (2) P₃ `k = 2`
the non-covering family `{0}, {2}` — the certificate `λ₂ ≤ 2` from a
family that is provably not a partition, honest against the independent
counting pin `λ₂ ≤ 1` (`mwPathAdj_secondEval_le_one`); (3) P₃ `k = 3`
the singleton partition — `λ₃ = 2 = 2·1` equality with `λ₃` pinned by
*trace arithmetic* (`evals_sum_eq_trace` at trace `3`, the pinned
`λ₂ ≤ 1`, PSD nonneg, and the raw eigenvector `![1, −√2, 1]` at `2`
through `exists_eigvalOf_eq_of_mulVec_eq_smul` +
`eigvalOf_le_evals_last`); (4) C₄ `k = 4` singletons (the all-rational
fixture) — `λ₄ = 2 = 2·1` equality with `λ₄` pinned by the alternating
vector plus trace `4`; (5) **the overlap fence** — the cyclic-pair
family `{0,1}, {1,2}, {2,3}, {3,0}` with every other hypothesis verified
(each φ = 1/2 computed raw), disjointness provably failing, and the
dropped conclusion refuted at `2 ≥ λ₄ ≥ 2 > 1 = 2·max φ` — disjointness
exercised, not decorated; (6) the `k = 1` zero-constraint edge instance
on P₃ (`evals ⟨0⟩ = 0 ≤ 2·φ`). Plus the absorption anchors pinned at
*equality* on the fixtures (`mw_edge_absorption_eq`,
`mw_cycle_absorption_eq` — the constant-2 lemma is tight there) and the
per-part indicator energy identity as a theorem instance
(`mw_cycle_partIndicator_QA`).

**Verification (the closing run, from scratch):** `lake env lean` —
zero errors on `Spectral.lean` (all 8 warnings pre-existing, present in
HEAD; the new engine block adds none), `Multiway.lean`, and the QA file
(zero warnings); explicit `lake build` targets ✔; `#print axioms` via
`wip/mw_axcheck.lean` — the standard three only, all 33; **full `lake
build` ✔ immediately followed by `check_build_completeness.py` —
109/109 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no
issues), `check_citations`, `check_markdown_links` pass; scoreboard
regenerated idempotent (**2422/10/0**, md5-stable).

**Technique notes for future pins:** `Finset.univ.sup'` needs its
nonemptiness witness inline at `Fin 2`/`Fin 3`/`Fin 4` (the private
`sup'_const` helper collapses constant families); the `sup'` ≤/≥
interface (`Finset.sup'_le_iff`/`le_sup'_iff`) takes the nonemptiness
argument explicitly; entry-fact lemmas (`mwPathE00`…) beat depth-2
matrix-literal simp cascades inside inline arithmetic; the P₃/C₄ λ₃/λ₄
pins avoid any spectrum *computation* — trace + one raw eigenvector +
PSD nonneg is the complete recipe (the spin-off
`exists_eigvalOf_eq_of_mulVec_eq_smul` exists exactly for this).

**Priced follow-ons (not started):** the ρ_k partition-minimum packaging
(finite partition-space attainment, the `sweep_level_extract_vol`
pattern at partition level — the every-family form makes it a pure
attainment task); the multiway *hard* direction (λ_k from below,
higher-order Cheeger from above) — genuinely multi-run, unchanged.

## Delivery record — the ρ_k partition-minimum packaging (the priced follow-on)

**Delivered 2026-08-26 (run `20260826T181445Z-run-1`, one run: Step-0
pricing accepted as recorded above — a pure finite-attainment task at
the every-family form; no new survey needed). Zero new axioms (count
stays 10; `#print axioms` via `wip/rho_axcheck.lean` on all 34 audited
declarations — 9 public + 25 QA: exactly `propext, Classical.choice,
Quot.sound`, every one). QA 2422 → 2444 (+22 in
`MultiwayCheeger_QA.lean`, the file 73 → 95 by the generator's
metric).**

**Delivered** (a new "The ρ_k packaging: the partition minimum" section
of `GraphTheory/Multiway.lean`; no new imports, no umbrella change):
`IsMultiwayPartition` (nonempty, pairwise disjoint, covering — the
partition predicate the every-family form deliberately did not need),
`maxPartConductance` (the `sSup` of the part-conductance range; `k = 0`
is the documented junk value), `multiwayExpansion A k := sInf` over the
k-way partitions' maxima (the classical ρ_k / k-way expansion constant;
`k > card V` is the documented `sInf ∅ = 0` junk, hypothesis-gated),
`finset_univ_sup'_eq_sSup_range` (the join between the delivered
theorems' `sup'` statement shapes and the packaged definition),
`maxPartConductance_const`, `multiwayExpansion_le` (the `csInf` bound at
finiteness-supplied `BddBelow`), **attainment**
`exists_isMultiwayPartition_eq_multiwayExpansion` (`Set.Nonempty.csInf_mem`
at the value set's finiteness — a subset of the range over the Fintype
of k-part families; the every-family form makes attainment the *whole*
new content), the headline **`cheeger_upper_bound_multiway_rhoK`**
(`evals (L_sym) ⟨k−1⟩ ≤ 2 · ρ_k` at `2 ≤ k ≤ card V` with a partition —
the classical Lee–Gharan–Trevisan statement form, obtained by attaining
the minimum and consuming
`cheeger_upper_bound_multiway_conductance` at the minimizer; no new
engine), and the existence supplier
`exists_isMultiwayPartition_of_le_card` (injection `Fin k ↪ V` +
complement-absorbing last part, discharging the headline's `hex` in the
common case).

**QA (+22), non-circular by construction:**

- **The C₄ second-eigenvalue pin, both sides independent:**
  `mwCycleAdj_secondEval_le_one` (the counting bridge
  `evals_le_of_card_eigvalOf_le` at the kernel witness `√D·1` — through
  the shelf supplier `normalizedLaplacian_mulVec_degreeSqrt_onesVec` —
  and the raw-entrywise mode `![1,0,−1,0]` at `1`, two distinct
  eigenbasis indices) and `mwCycleAdj_secondEval_ge_one` (the sInf
  engine `secondEval_variational_of_ker` at `√D·1`, the quadratic-form
  identity `xᵀL_sym x = ∑xᵢ² − (x₀+x₂)(x₁+x₃)` verified entrywise, the
  constraint reducing to `∑x = 0`, so every constraint-set Rayleigh
  quotient is `‖x‖² + (x₀+x₂)² / ‖x‖² ≥ 1`; nonemptiness witnessed by
  the mode at Rayleigh exactly `1`) — the exact pin
  `λ₂ (L_sym C₄) = 1` with the multiway family nowhere in either side.
- **The star instance: `ρ₂(C₄) = 1/2` exact** — the `≤` side the
  adjacent-pair partition witness (conductance `2/min(4,4) = 1/2` per
  part, boundaries/volumes shared with the overlap-fence family's
  pins), the `≥` side *forced by the headline* joined to the pinned
  `λ₂ = 1`. A broken attainment (junk `sInf`), a wrong constant, or a
  wrong minimum breaks the equality.
- **The minimum is not vacuous:** `mw_cycle_rho_beats_diagonal` —
  `ρ₂ = 1/2 < 1 = maxPartConductance` at the diagonal partition
  `{0,2},{1,3}` (conductance `4/4 = 1` computed raw). The packaged
  minimum genuinely optimizes over the partition space; attainment is
  exercised, not decorated.
- `ρ₂(K₂) = 1` and `ρ₃(P₃) = 1` exact, the `≥` sides forced by the
  headline joined to the pre-existing independent pins (`2 ≤ λ₂` on K₂;
  the delivered obligation-3 `λ₃ = 2` on P₃); the K₂/P₃ conductance
  pins (`mwPathAdj_conductance_single`: `2/min(2,2)` at the middle,
  `1/min(1,3)` at the ends) computed raw through `vol_compl`.
- **The empty-set junk fence:** no 3-partition of two vertices exists
  (`mw_no_three_partition_on_edge` — a chosen point per part is an
  injection `Fin 3 ↪ Fin 2`, contradicting cardinalities), so
  `multiwayExpansion mwEdgeAdj 3 = sInf ∅ = 0` (`Real.sInf_empty`, the
  same junk convention the subgaussian repair documents): the
  partition-existence hypothesis of every ρ_k statement is
  load-bearing, not decorative.
- The supplier instance (`3 ≤ 4` on C₄, hypothesis-free
  instantiation).

**Verification:** spike first (`wip/rho_spike.lean`, the full routes
green before any module touched — module side and QA side in one file,
iterated to zero errors/warnings; technique findings: ℝ's conditional
completeness means no `iSup` syntax — `maxPartConductance` is `sSup` of
range with the `sup'`↔`sSup` bridge proved once; `csInf_le` needs the
finiteness-supplied `BddBelow`; `le_csInf` takes nonemptiness;
`Set.Nonempty.csInf_mem` for attainment; `Function.Embedding.nonempty_of_card_le`
for the supplier; `Finset.disjoint_insert_{left,right}` vs
`Finset.disjoint_singleton_{left,right}` argument orders;
`linear_combination hxorth` for the √2-factored constraint; the
namespace-reopening trap — a second `namespace
SpectralGraphTheory.MultiwayQA` inside a still-open
`SpectralGraphTheory` lands declarations in the *doubled* namespace and
silently unresolves every imported name; and the QA module's
`sup'`-shape H-witnesses block `rw` across statements from different
theorem statements — derive bounds by `le_trans` at one's own H
instead). Then `lake env lean` — zero errors/zero warnings on both
changed modules; explicit `lake build` targets ✔ (module 2191/2191, QA
2192/2192; the axcheck hit the stale-olean trap once, remediated by the
documented explicit QA-target rebuild before the audit); `#print
axioms` via `wip/rho_axcheck.lean` — the standard three only, all 34;
**full `lake build` ✔ (2385/2386, "Build completed successfully")
immediately followed by `check_build_completeness.py` — 109/109 fresh,
0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
idempotent (**2444/10/0**, md5-stable). Records updated: this record,
`proposals/README.md`, README (2444), the radar (QA axis synced), the
scoreboard (four verification rows + the interpretation bullet), the
index map, backlog item 3, the execution plan, and the activity log.
Nothing committed; the prior runs' uncommitted deliveries preserved
untouched.

**Remaining priced follow-on (not started):** the multiway *hard*
direction (λ_k from below, higher-order Cheeger from above) — genuinely
multi-run, gated on a named consumer. **Tracked as its own proposal as
of 2026-08-28: see `proposals/multiway-cheeger-hard-direction.md`**,
opened after an external review independently flagged the same gap;
gated on an operator adoption decision, mirroring
`alon-boppana-bound.md`'s pre-adoption lifecycle.
