# The Sparsification Core Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-04 by run `20260904T160913Z-run-1`,
session `ses_f92debbe6ffeU5TO6eNLX6pvSs`; see the delivery record).

## Scope

The prior terminal handoff's named next target: "the electrical
cluster's one remaining QA family (the `ResistanceMetric` consumer set
beyond the already-delivered metric-residual fences) … after which the
electrical cluster's falsification surface is complete." That consumer
set is the leverage-score sparsification program — the core audit's own
scope note names it ("the electrical cluster … feeding the
sparsification program"). This run audits the program's **deterministic
core**: the whole of `Scaffold/Mathlib/GraphTheory/Sparsification.lean`
— the rank-one algebra, the bilinear Dirichlet identity, the
Spielman–Srivastava edge vectors, the image projector, the
Finding-A-guarded sampling design (probabilities, summands, centering,
pointwise bound, variance), the sampled operator and its exact deviation
identity, and the transport layer — together with its QA file
`Sparsification_QA.lean` (delivered 2026-08-27/28, **predating** the
adversarial-review discipline: it carries three design fences — the
Finding-A saturation guard `findingA_fence_QA`, the `q ≤ 0` budget
corner `ssSummand_q0_fence_QA`, the rank-one norm lower bound — but no
hypothesis-form fence audit).

`SparsificationTail_QA.lean`'s signed-transport section (2026-08-28/31)
already fences exactly two of the shelf's clauses —
`quadForm_laplacian_eq_ssTransport`'s `hnn` (`sg_iso_fence`) and
`ssTransport_dot_ssEdgeVec`'s `hnn` (`sg_claimA_fence`) — at the
nonpositive-spectrum fixture `sg`; those two are screened as
already fenced, and `sg`'s delivered pins (`sg_laplacian`,
`sg_eigval_nonpos`) are reused as the survey's evidence that a *fully
nonpositive* spectrum zeroes every edge vector. The axiom-backed tail
theorems (`Derived/SparsificationTail.lean`, consuming
`matrix_bernstein`) keep their own delivered fence sections; re-reading
*their* hypothesis clauses is recorded below as a priced follow-on, not
part of this delivery.

Method: `governance/ADVERSARIAL_REVIEW.md`'s hypothesis-necessity pass
(ten precedents) — re-read every theorem's hypothesis clauses, identify
those with no negative witness anywhere in the repository, and close
each with a hypothesis-form fence (the dropped-hypothesis statement
refuted at a fixture where every other hypothesis is genuine, certified
by an isolation companion), or record a non-fenceable with its
mechanism.

## Step-0 findings: the priced fence list

Fifteen genuinely new fences at four new fixtures plus the delivered
`signedAdj` (from `ResistanceMetric_QA`, by QA-to-QA import) and the
`K₂` fixture already in `Sparsification_QA.lean`.

### The `hnn` clauses (six fences)

- **`eigvalOf_laplacian_nonneg`, `hnn`** — at `signedAdj` (symmetric,
  connected support, delivered): `quadForm L ![0,1,-1] = -2` is
  delivered (`signed_quadForm_01m1`), and the spectral resolution
  `quadForm_eigvalOf` forces some eigenvalue negative: the whole-family
  reading `¬ (∀ k, 0 ≤ eigvalOf L k)` refuted without locating the
  index.
- **`ssEdgeVec_dotProduct_self`, `hnn`** — at `signedAdj` pair `(2, 1)`:
  the edge vector is identically zero (`√(A 2 1 / 2) = √(-1/2)` is
  junk-zero at every nonzero-eigenvalue coordinate, the zero-eigenvalue
  coordinates drop by definition) while the right side is
  `(-1) · R 2 1 / 2 = (-1)(-2)/2 = 1` through the delivered
  `signed_R21_QA`. `0 ≠ 1`.
- **`sum_ssEdgeVec_dotProduct_self`, `hnn`** — at the **new rank-1
  signed 4-cycle** `cfR1Adj` (positive edges `(0,1),(0,2),(1,3),(2,3)`,
  negative edges `(0,3),(1,2)`, every degree `1` — the shape of the
  core audit's `sgnK4Adj`, re-defined locally): `L = s ⊗ s` with
  `s = (1,-1,-1,1)`, so the single nonzero eigenvalue is `‖s‖² = 4 > 0`
  (genuine `√`), every edge vector lives on the one eigen-coordinate
  `ŝ = s/2`, each positive ordered pair contributes
  `(1/2)(ŝ_u - ŝ_v)²/4 = 1/8`, and the eight positive ordered pairs sum
  to `1 ≠ 3 = card - 1`. Requires the eigenspace-dimension-1 argument
  (at most one nonzero eigenvalue; the nonzero eigenvector is `±ŝ`).
- **`trace_imageProjector_eq`, `hnn`** — at the **new nonpositive
  fixture** `cfSgAdj` (the shape of the tail QA's `sg`:
  `A₀₁ = A₁₂ = -2`, `A₀₂ = 1`, so `L = -(1,-2,1)(1,-2,1)ᵀ` with a
  two-dimensional kernel, re-defined locally): every eigenvalue is `≤ 0`
  so every edge vector is junk-zero and every coordinate of the
  projector-identity sum vanishes; `trace Π = #nonzero eigenvalues = 1`
  (at most one nonzero since `im L ⊆ span s`; at least one since
  `quadForm L s = -36 ≠ 0`) `≠ 2 = card - 1`.
- **`trace_imageProjector_eq`, `hconn`** — at the **new disconnected
  nonnegative fixture** `cfDiscAdj` (`K₂ ⊕ K₂` on `Fin 4`): the
  constants and the component indicator are two non-parallel kernel
  vectors, so the delivered Foster engine
  `ff_two_kernel_filter_card_ge_two` (Foster_QA, public, statement-level
  reusable) forces `≥ 2` zero eigenvalues, `trace Π ≤ 2 ≠ 3 = card - 1`.
- **`sum_rankOne_ssEdgeVec` and `quadForm_imageProjector_eq` and
  `ssSampled_sub_imageProjector`, `hnn`** — all three at `cfSgAdj`
  through the same zero-edge-vector mechanism: the rank-one sum is the
  zero matrix while `Π ≠ 0` (some eigenvalue `≠ 0` forces a projector
  diagonal entry `1`); the quadratic form at `x = s` reads
  `∑ (x ⬝ᵥ v_e)² = 0 < quadForm Π s`; and the deviation identity reads
  `0 - Π = 0`. Three fences, one mechanism.

### The `hA`, `hv`, `hpne` clauses (three fences)

- **`laplacian_dirichlet_bilinear`, `hA`** — at the **new asymmetric
  fixture** `cfAsymAdj = !![0,2;1,0]`: the double sum sees the two
  unequal off-diagonals (`2 + 1 = 3`) while the quadratic form sees the
  symmetrized row sums (`2 · 2 = 4`) at `x = y = ![1,0]`: `3 ≠ 4`.
- **`dotProduct_self_pos_of_ne_zero`, `hv`** — at `v = 0`: the dropped
  statement reads `0 < 0 ⬝ᵥ 0 = 0`. Trivial but genuine (the clause is
  the statement's only hypothesis).
- **`integral_bern_center_sq`, `hpne`** — at `ι = Fin 1`, `p = fun _ => 0`
  (mass clauses genuine): every outcome's summand is
  `(δ/0 - 1)² = (0 - 1)² = 1` (Lean's `x/0 = 0`), so the integral is
  `1` while the right side is `(1 - 0)/0 = 0`. `1 ≠ 0`.

### The `hq` clauses (six fences, all at the delivered `K₂` fixture
`spK2` with its pinned `‖v_{01}‖² = 1/2`)

- **`ssProb_nonneg`, `hq`** — at `q = -1`: `p = min 1 (-1/2) = -1/2 < 0`.
- **`ssWeight_nonneg`, `hq`** — at `q = -1`, the sampled outcome:
  `w = 1/p = -2 < 0`.
- **`integral_ssSummand_eq_zero`, `hq`** — at `q = 0` (the measure is
  the genuine `Bernoulli(0)` point mass on the all-false outcome, and
  the summand is the *constant* `-(v ⊗ v)` since `δ/0 - 1 = -1` on both
  branches): the integral is `-(v ⊗ v) ≠ 0` (`v ≠ 0` through the
  delivered norm pin).
- **`integral_ssSummand_mul_self`, `hq`** — at `q = 0`: the left side is
  `‖v‖² (v ⊗ v) = (1/2)(v ⊗ v) ≠ 0` while the right side's coefficient
  `((1-0)/0)‖v‖²` is junk-zero. `(1/2) ≠ 0`.
- **`ssVariance_coeff_nonneg` / `quadForm_ssVariance_nonneg`, `hq`** —
  at `q = -1`: the coefficient is `1/q - ‖v‖² = -3/2 < 0`, and at
  `x = v_{01}` the whole quadratic form is `-3/4 < 0` (both nonzero
  ordered pairs contributing).
- **`quadForm_ssLaplacian_nonneg`, `hq`** — at `q = -1`, the sampled
  outcome, `x = ![1,-1]`: both ordered pairs carry weight `1/p = -2`,
  contributing `(w/2)·A·Δ² = -4` each; total `-8 < 0`.

(``ssSummand_l2OpNorm_le`'s `hq` is already fenced by the delivered
`ssSummand_q0_fence_QA` — screened.)

### Recorded non-fenceables (with mechanisms)

- **`ssEdgeVec_dotProduct_self`, `hconn`** — on nonnegative input a
  positive weight `A u v > 0` puts `u, v` in the same support component,
  where the demand `e_u - e_v` is solvable and `R` is genuine (the
  identity holds per component); at `A u v = 0` both sides vanish. The
  dropped-`hconn` statement is true.
- **`quadForm_ssLaplacian_nonneg`, `hnn`** — the junk-√ zero edge
  vector is an *automatic sign guard*: at a negative-weight pair the
  edge vector is zero, hence the probability is `min 1 0 = 0`, hence
  the weight is `δ/0 = 0`, hence the pair contributes exactly `0` —
  negative weights cannot enter the sampled Laplacian's form. The
  dropped-`hnn` statement is true (given `hq` genuine).
- **`ssSampled_isSymm`, `hnn`** — truth-removable: the sampled operator
  is a sum of `weight • rankOne v_e` terms, each symmetric regardless
  of signs; the hypothesis is only consumed by the deviation-identity
  *route*, not the statement.
- **`ssVariance_coeff_le`, `hq`** and **`quadForm_ssVariance_le`,
  `hq`** — algebraic: below saturation the coefficient is exactly
  `1/q - ‖v_e‖²`, so the coefficient bound `≤ 1/q` and the form bound
  reduce to `‖v_e‖² ≥ 0` / a PSD subtraction — the dropped-`hq`
  statements hold at every `q ≤ 0` corner (checked at `q ∈ {0, -1/4,
  -1, -2}`: `q = 0` junk-zeroes the left side; `q < 0` gives
  `1/q - ‖v‖² ≤ 1/q`).
- **`ssTransport_dot_ssEdgeVec`, `hpos`** — at `A u v ≤ 0` both sides
  junk-vanish (`√(A/2) = 0` zeroes the right side; the edge vector is
  zero on the left).
- **`integral_bern_center_sq`, `hp0`/`hp1`** and the `ssMeasure`-carrying
  `hq` clauses of `indepFun_ssSummand` /
  `iIndepFun_ssSummand` — statement-entangled: `bernPMF`/`ssMeasure`
  consume the proofs in the display, so the dropped statements are not
  well-formed.

### Screened as already fenced

`quadForm_laplacian_eq_ssTransport` `hnn` (`sg_iso_fence`),
`ssTransport_dot_ssEdgeVec` `hnn` (`sg_claimA_fence`),
`ssSummand_l2OpNorm_le` `hq` (`ssSummand_q0_fence_QA`), the Finding-A
guard (a def-level design fence, `findingA_fence_QA`), and the
hypothesis-free algebra layer (rank-one lemmas, CS, the projector's
hypothesis-free form bounds, `quadForm_imageProjector_eq_of_mulVec_eq`,
`ssEdgeVec_self`/`_swap`, measurability/independence shape lemmas).

### Priced follow-ons (recorded, not landed)

- **`l2OpNorm_ssVariance_le` / `quadForm_ssVariance_le`, `hnn`** — the
  refutation exists at `signedAdj` for `q > 4`: there
  `Σ = (1/q - 1/4) ê⊗ê` on the single positive-eigenvalue axis, so
  `‖Σ‖ = 1/4 - 1/q > 1/q`; but pinning it needs the `signedAdj`
  eigen-structure (eigenvalues `{3, -1, 0}`, the `√6`-irrational
  eigenvector located at its index) — an index-resolved pin this run
  priced and deferred, exactly as the regular-Cheeger audit deferred its
  sweep-`hA` clause.
- **`quadForm_ssLaplacian_eq`, `hnn`** — fails at `cfR1Adj` at
  `x = e_0` (the per-pair claim-A correction `x ⬝ᵥ ŝ ≠ x_u - x_v` on a
  signed kernel; left side `16 ≠ 8` right at `q = 1`, all-true
  outcome); the weight/sum bookkeeping on top of the `cfR1Adj` engine
  is priced as its own increment.
- **The tail theorems' clause re-read** (`sparsification_graph_budget`,
  `sparsification_eigcoord_tail`, `sparsification_graph_vector` and
  their `ε`/`δ`/`q`/`hnn`/`hconn` clauses) — their QA carries
  delivered fence-shaped sections (cone, disconnected, signed
  transport, budget pins); a fresh hypothesis-necessity pass over the
  *axiom-backed* layer is the natural next audit after this one.

## Delivery plan

QA-only, zero axiom contact (count stays 4). Spike first in
`wip/spfences_spike.lean` to zero errors/zero warnings; land as a pure
insertion — the `CoreFences` section of
`Scaffold/QA/SpectralGraph/Sparsification_QA.lean` — with the four new
fixtures (`cfR1Adj`, `cfSgAdj`, `cfDiscAdj`, `cfAsymAdj`), hypothesis-form
fences plus isolation companions, `#print axioms` on every new
declaration via a `wip/` audit file, then the full verification ladder
and records updates.

## Delivery record (2026-09-04)

DELIVERED at the full priced scope — QA-only, zero axiom contact (count
stays 4; `#print axioms` via `wip/spfences_axcheck.lean` on all 57
public declarations — every one exactly `propext, Classical.choice,
Quot.sound`, the four private helpers audited transitively through
their consumers; no `-- @refutes` tags — theorem instantiations,
nothing admitted consumed). QA 4876 → 4931 (+55 by the generator
metric; 61 declarations: 59 theorems + the two new fixture `def`s
`cfAsymAdj`, `cfSgAdj`).

All fifteen fences closed with isolation companions, landing as a pure
insertion — the `CoreFences` section of `Sparsification_QA.lean`
(958/0 in numstat) — spiked first in `wip/spfences_spike.lean` to zero
errors/zero warnings (three fix rounds, all in recorded trap classes).
Fixture reuse per the isolation-cite-don't-duplicate discipline: the
signed fixture and its pins (`signedAdj`, `signed_R21_QA`,
`signed_quadForm_01m1`, `signed_fence_isolation_QA`), the rank-1 signed
4-cycle and its isolation companion (`sgnK4Adj`,
`sgnK4_fence_isolation_QA`), the disconnected `K₂ ⊕ K₂` with its
indicator-kernel pin (`connDiscAdj`,
`connDisc_indicator_in_kernel_QA`), the Foster kernel-count engine
(`ff_two_kernel_filter_card_ge_two`), and the `K₂` leverage pin
(`ssEdgeVec_dot_K2_QA`) — all by QA-to-QA import through
`ResistanceMetric_QA`; the tail QA's `sg` fixture is *re-derived
locally* (`cfSgAdj` + four pins) rather than imported, because
`SparsificationTail_QA` imports the Derived layer and would drag it
into the QA-to-QA graph.

**Technique findings** ( Lean-side, for future audits):

1. **`norm_num` destroys smul-heavy dot-product hypotheses into DNF.**
   Normalizing `(ck • s) ⬝ᵥ (ck • s)` with
   `norm_num [Matrix.dotProduct_smul, smul_eq_mul]` turns a clean
   equation into a disjunction of zero-factors
   (`ck = 0 ∨ cl = 0 ∨ s = 0`), unusable for `mul_ne_zero`. The robust
   route is the standalone helper `spF_dot_smul_smul`
   (`(a • x) ⬝ᵥ (b • y) = a * b * (x ⬝ᵥ y)` by `Finset.mul_sum` +
   per-term `ring`), rewritten once — third confirmation of the
   "compute through a named lemma, not a tactic" pattern after the
   Foster and regular-Cheeger engines.
2. **`rw` with a lambda inside a rewrite list is a parser trap**
   (`Finset.sum_congr rfl (fun e _ => by rw [...])` inside `rw [...]`):
   the `by`-block's `;`-sequences break the list grammar with
   misleading errors (`unexpected token 'λ'`). Hoist the function to a
   named `have` (`hrw : ∀ u v, ... := fun u v => ...`) and rewrite with
   the name, or use `Finset.sum_eq_zero` for the everywhere-zero case.
3. **`Finset.sum_eq_single` in this Mathlib takes three arguments**
   `(a) (h₀ : ∀ b ∈ s, b ≠ a → f b = 0) (h₁ : a ∉ s → f a = 0)` with
   the membership implicit — `refine ... ?_ ?_` with two bullets, not
   three; the error surfaces as "function expected", not as an arity
   mismatch.
4. **Grouped-multiplication shape discipline in `rw` chains**: a `have
   ... := by ring` stores the *stated* grouping, so
   `(c * c) * (d * d)` and `c * c * d * d` are interchangeable to
   `ring` but NOT to a later `rw [hdd]` that pattern-matches `d * d` —
   state intermediate identities with the grouping the next rewrite
   needs (the `hcd`/`hring` pair in `spF_sgnK4_edgeVec_dot`).
5. **`measure_univ` instance resolution does not fire through the
   `ssMeasure` def**: `rw [integral_const, measure_univ, ...]` fails
   with `failed to synthesize IsProbabilityMeasure (ssMeasure ...)`.
   `simp only [ssMeasure]` *before* the integral rewrites exposes the
   `(bernPMF ...).toMeasure` head and the instance resolves — the
   shelf's own `hone` proof works because it states the measure
   literally.

**Verification:** spike first (`wip/spfences_spike.lean` — the full
61-declaration delivery, iterated to zero errors/zero warnings before
any shelf edit, three fix rounds all in recorded trap classes); `lake
env lean` on the landed module (zero errors, zero warnings); explicit
`lake build Scaffold.QA.SpectralGraph.Sparsification_QA` ✔; the
57-public-declaration axiom audit above; **full `lake build` ✔
immediately followed by `check_build_completeness.py` — 133 source
files, 133 fresh artifacts, 0 stale, 0 missing, exit 0**;
`lint_axioms` exit 0 (4 current axioms, unchanged; only the
allowlisted-confirmed PF finding); `check_refutation_independence`
(9-tag clean — no tags touched); `check_public_reachability` clean (63
repo modules); `check_citations` ("All axioms have proper citations!");
`check_markdown_links` clean; `check_backlog_freshness` clean;
scoreboard regenerated (**4931/4/0**) with the verification row;
map-freshness exit 0 after the 4876 → 4931 stats sync in both map data
files and SVG regeneration (49 stations, no status change — none
owed). The landing verified a pure insertion (958/0 in numstat, plus
the one import line and the Purpose-block paragraph). Records updated:
this proposal (COMPLETE + this delivery record),
`proposals/README.md` (new Delivered row), README (4931 + the
sparsification row's audit clause), the radar (QA axis synced, held
4.5 per protocol — negative witnesses of an already-counted family,
not a named-gap closure), `index/map/spectral_graph.md` (the
`Adversarial fences` subsection), the backlog item-2
falsification-surface note (the electrical cluster now complete),
the scoreboard verification row, both map data tables + regenerated
SVG, the execution plan, and the activity log. Nothing committed; the
prior runs' uncommitted deliveries preserved.
