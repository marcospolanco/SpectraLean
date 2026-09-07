# Proposal: The Boundary Outflow Lemma

**Status:** COMPLETE. Step 1 delivered 2026-09-07 (run
`20260907T051321Z-run-1`, session `ses_f85e4fd87ffeIAk10HRoxt2F0J` —
the delivery record below); **Step 2 delivered 2026-09-07** (run
`20260907T053227Z-run-2`, session `ses_f85b4c94affebxh9q9Bec73k5W` —
the Part-2 delivery record at the file's end), via the companion's
Steps 0(m=0)/1/2 delivered under the named-consumer scope (see the
Part-2 record's gate note). Both parts hard crust, zero axioms.

Restated in pure-mathematics form 2026-09-06 from
an external request relayed by the operator (not tracked in this
repository — see `.gitignore`); no operational, product, or patent
framing survives into this document, only the underlying mathematical
asks. Authorizes no Lean changes, axiom admissions, document rewrites,
or transit-map edits.

Companion to [`global-semigroup-contraction.md`](global-semigroup-contraction.md)
(this proposal's Part 2 is a direct corollary of that document's Step 1/
Step 2, once delivered) and to the existing region/quadratic-form
machinery in `Scaffold/Mathlib/GraphTheory/Multiway.lean`
(`partIndicator`, `quadForm_laplacian_partIndicator`) and
`Scaffold/Mathlib/GraphTheory/Spectral.lean` (`laplacian_mulVec_apply`,
`boundary`) — this document's Part 1 makes the vector-level statement
those already prove at the scalar (quadratic-form) level.

## The claim this document is answering

The relayed request's framing was: combinatorial cut/boundary
definitions and the continuous heat semigroup exist in this project as
separate interfaces, with no theorem connecting them. Two connecting
facts were asked for — (1) an algebraic characterization of `L·1_S` as
supported exactly on the cut edges, and (2) a Cauchy–Schwarz "regional
dissipation" bound on how much heat flow can move in or out of a
region `S` in time `t`. Verified directly against the shelf: **(1) is
essentially already proved**, one `Finset` split away from an existing
general lemma; **(2) is a near-immediate three-lemma composition**
once `global-semigroup-contraction.md`'s order-0 contraction bound
exists — Cauchy–Schwarz, the heat kernel's own symmetry, and that
bound, chained. Neither part needs new mathematical machinery; this is
an assembly proposal, not a research one, which is why it is tracked
at **Medium** rather than alongside the Low/gated items in this
directory's Active priority table.

## What's already on the shelf

- **The general diffusion-form entrywise action of the Laplacian** —
  `laplacian_mulVec_apply` (`Spectral.lean:1311`): `(L *ᵥ f) i = ∑ j,
  A i j * (f i - f j)`, hypothesis-free, for *any* `f : V → ℝ`. This is
  the one lemma Part 1 needs; specializing `f` to a region indicator
  and splitting the sum over `j ∈ S` versus `j ∈ Sᶜ` is the entire
  proof.
- **The region indicator, already defined with its scalar companion
  identity** — `partIndicator S` (`Multiway.lean:69`, the `{0,1}`-
  valued indicator as a plain function) and `quadForm_laplacian_
  partIndicator` (`Multiway.lean:93`): `quadForm (laplacian A)
  (partIndicator S) = boundary A S` — the scalar identity `1_S^T L 1_S
  = boundary(S)` this proposal's Part 1 sits directly underneath at
  the vector level. `boundary A S := ∑ i in S, ∑ j in Sᶜ, A i j`
  (`Spectral.lean`, "Cuts, volume, conductance" section) is exactly the
  row-sum quantity the request's formula names.

  *Noted, not acted on:* a second, independently-defined indicator
  (`indicatorVec`, `Expander.lean:103`) and cut-weight function
  (`edgeWeight`, `Expander.lean:90`, identical in content to `boundary`
  restricted to `T = Sᶜ`) already exist elsewhere in this project under
  different names. This proposal deliberately builds on `partIndicator`
  /`boundary` rather than `indicatorVec`/`edgeWeight`, since the former
  pair already carries the companion quadratic-form identity this
  document extends; reconciling the duplication itself is out of scope
  here.
- **The heat kernel's symmetry** — `heatKernel_isSymm` (`Heat.lean:304`):
  on a symmetric network, `heatKernel A t` is symmetric at every `t`,
  transferred through `Matrix.IsSymm.exp` from `laplacian_symmetric`.
- **The symmetric dot-product swap** — the three-line idiom `Matrix.
  dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq` for any `hM :
  M.IsSymm`, already used identically at least five times in this
  project (`ClusterProjector.lean:194,379`, `Expander.lean:264,341`,
  `Heat.lean:1318,1334,1583`, `Krylov.lean:445`) and packaged as its
  own named lemma for the adjacency case, `dotProduct_mulVec_symm`
  (`AlonBoppana.lean:1377`). Part 2 needs exactly this pattern applied
  to `heatKernel A t` in place of the adjacency matrix.
- **Cauchy–Schwarz and the Euclidean-norm transfer** — `abs_dotProduct_
  le` and `norm_euclidean_eq_sqrt` (`Analysis/OperatorTheory/
  Perturbation/Duhamel.lean:248,234`), already proved and already the
  bridge `global-semigroup-contraction.md`'s Step 2 uses to produce a
  literal `‖·‖₂` statement.
- **The dependency this proposal's Part 2 sits on top of** —
  `global-semigroup-contraction.md`'s Step 1 (`heatKernel_
  globalContraction_dotProduct_le`) and Step 2 (its Euclidean-norm
  corollary): `‖x - heatKernel A t *ᵥ x‖ ≤ t * ‖laplacian A *ᵥ x‖` for
  `t ≥ 0` on a nonnegative-weight network. Instantiating that bound at
  `x := partIndicator S` is literally the norm factor Part 2's
  Cauchy–Schwarz bound needs.

## What's not on the shelf — and why it's small

Nothing in either part requires new mathematical content beyond
assembling the pieces above:

- **Part 1** needs one `Finset.sum` split (`j ∈ S` vs. `j ∈ Sᶜ`)
  applied to `laplacian_mulVec_apply` at `f := partIndicator S`, using
  `partIndicator_of_mem`/`partIndicator_of_not_mem` to resolve `f i`,
  `f j` in each branch. No induction, no new inequality, no
  eigenbasis.
- **Part 2** needs the three already-proved pieces above chained in
  the order: linearity of `dotProduct` over subtraction, the symmetric
  swap applied to `heatKernel A t`, Cauchy–Schwarz, then
  `global-semigroup-contraction.md`'s Step 2 supplying the norm bound
  on the swapped term. The one real dependency is that Step 2 has to
  exist first — this document does not re-derive it.

## Build order

### Step 1: The algebraic cut characterization (no dependency)

```
theorem laplacian_mulVec_partIndicator_of_mem (A : WAdj (V := V))
    {S : Finset V} {i : V} (hi : i ∈ S) :
    (laplacian A).mulVec (partIndicator S) i = ∑ j in Sᶜ, A i j

theorem laplacian_mulVec_partIndicator_of_not_mem (A : WAdj (V := V))
    {S : Finset V} {i : V} (hi : i ∉ S) :
    (laplacian A).mulVec (partIndicator S) i = -(∑ j in S, A i j)
```
Route: `laplacian_mulVec_apply A (partIndicator S) i` gives `∑ j, A i j
* (partIndicator S i - partIndicator S j)`; split the sum via
`Finset.sum_add_sum_compl S` (the same split
`quadForm_laplacian_partIndicator`'s own proof already performs, one
level up at the quadratic form); in the `i ∈ S` branch, `partIndicator
S i = 1` (`partIndicator_of_mem hi`) and the `j ∈ S` half's terms
vanish (`partIndicator_of_mem` again, giving `f i - f j = 0`), leaving
exactly the `j ∈ Sᶜ` half at `A i j * 1`; symmetric argument for `i ∉
S`. Directly delivers the request's case-split formula with `w_ij := A
i j`. A single combined corollary stating both cases as one `if i ∈ S
then _ else _` equation is a natural packaging choice, left to the
implementing run.

### Step 2: The regional dissipation bound (depends on
`global-semigroup-contraction.md` Step 2)

```
theorem abs_partIndicator_dotProduct_heatFlow_le (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j) {t : ℝ} (ht : 0 ≤ t)
    (S : Finset V) (x₀ : V → ℝ) :
    |Matrix.dotProduct (partIndicator S) (x₀ - heatKernel A t *ᵥ x₀)|
      ≤ t * ‖(laplacian A).mulVec (partIndicator S)‖ * ‖x₀‖
```
(Euclidean/`EuclideanSpace ℝ V` norms, matching `global-semigroup-
contraction.md`'s Step 2 notation.) Route: `Matrix.dotProduct_sub` to
split into `dotProduct (partIndicator S) x₀ - dotProduct (partIndicator
S) (heatKernel A t *ᵥ x₀)`; the symmetric-swap idiom (`Matrix.
dotProduct_mulVec, ← Matrix.mulVec_transpose, (heatKernel_isSymm A
hA t).eq`) turns the second term into `dotProduct (heatKernel A t *ᵥ
partIndicator S) x₀`; regroup via `Matrix.sub_dotProduct` into
`dotProduct (partIndicator S - heatKernel A t *ᵥ partIndicator S) x₀`;
apply `abs_dotProduct_le` (Cauchy–Schwarz); bound the first factor by
`global-semigroup-contraction.md`'s Step 2 instantiated at `x :=
partIndicator S`.

### Deferred and removed

- **Reconciling `partIndicator`/`boundary` with `indicatorVec`/
  `edgeWeight`** — a real but separate duplication-cleanup decision
  (see "Noted, not acted on" above), not this proposal's job.
- **A version of Part 2 that does not depend on
  `global-semigroup-contraction.md`** — possible in principle by
  substituting the existing *windowed* `heatKernel_firstOrder_
  remainder_apply_le`-style bound instead, but that would reintroduce
  the `|t·λᵢ| ≤ 1` restriction the request's formula does not carry;
  not pursued.

## QA plan

- Step 1: the K₂ and triangle fixtures already used throughout
  `Multiway_QA`/`Heat_QA` — pick a proper nonempty `S`, confirm the
  case-split formula against a direct hand computation of `L *ᵥ
  partIndicator S` on each fixture.
- Step 1 fence: confirm the two branches disagree in general (i.e. the
  theorem is not accidentally proving the same value on both sides of
  the partition) on an asymmetric-cut fixture.
- Step 2: instantiate on the same fixture at a concrete `t`, cross-
  checking the assembled bound's RHS against the already-QA'd closed-
  form heat-kernel values `Heat_QA` carries for K₂, per this project's
  standing adversarial-fence discipline
  (`governance/ADVERSARIAL_REVIEW.md`).
- Step 2 fence: an `hnonneg`-omission witness mirroring
  `global-semigroup-contraction.md`'s own fence, since Part 2 inherits
  that hypothesis transitively.

## Gate — Medium, sequenced but not human-gated

Unlike the Low items in this directory's Active priority table, this
proposal needs no operator sign-off or technical-direction decision:
Part 1 is immediately actionable (no dependency), and Part 2 is a
direct, low-risk assembly once `global-semigroup-contraction.md`'s
Step 1/Step 2 land. Tracked as **Medium** in `proposals/README.md`'s
Active priority table rather than Low, and rather than High since
nothing internal currently blocks on it — an autonomous run may pick
up Step 1 at any time, and Step 2 once its dependency clears.

## Operating instructions for an autonomous run

- Step 1 has no dependency and can be delivered standalone at any
  time.
- Step 2 requires `global-semigroup-contraction.md`'s Step 1 and Step
  2 to exist first; if picked up before that proposal is adopted,
  deliver Step 1 alone and record Step 2 as blocked on the companion
  proposal, rather than re-deriving its contraction bound inline.
- **No new axioms.** Both steps stay inside already-proved
  `Spectral.lean`/`Multiway.lean`/`Heat.lean`/`Duhamel.lean` machinery
  plus (for Step 2) whatever `global-semigroup-contraction.md`
  delivers; if either step needs something genuinely absent, stop and
  record the precise obstruction in `docs/6_SGT_BACKLOG.md` rather
  than admitting anything.
- Ship each step's adversarial fence (QA plan above) in the same
  delivery, not as a follow-on audit pass.

## Open next step

Step 1 is ready to pick up immediately, independent of any other
proposal's status. Step 2 waits on `global-semigroup-contraction.md`'s
Step 1/Step 2.

## Step 1 delivery record (2026-09-07)

DELIVERED at the full designed scope: 5 public theorems in
`Multiway.lean`'s new "boundary outflow lemma" section
(`laplacian_mulVec_partIndicator_of_mem`,
`laplacian_mulVec_partIndicator_of_not_mem`,
`laplacian_mulVec_partIndicator_apply`,
`sum_laplacian_mulVec_partIndicator`,
`quadForm_laplacian_partIndicator_unsymm`; functional 1359 → 1364)
plus 10 QA theorems in `MultiwayCheeger_QA.lean`'s new section
(QA 6615 → 6625) — hard crust, zero axiom contact (`#print axioms`
via `wip/bol_axcheck.lean` on all 18 declarations — the 5 shelf
theorems and the 13 QA declarations (10 theorems + 3 fixture `def`s):
every one exactly `propext, Classical.choice, Quot.sound`; the count
corrected from a first-draft 17 by the concurrent continuation run,
see `AGENT_ACTIVITY.md` 2026-09-07T05:21:51Z).

**The finding beyond the ask**: `quadForm_laplacian_partIndicator`'s
`hA : A.IsSymm` is **removable** — the vector-level outflow route
sums the membership case over `i ∈ S` and reaches `boundary A S`
definitionally, never flipping the region, so `boundary_compl` (the
symmetry consumer) never enters. The unsymm twin delivers the same
energy identity for ANY weights, asymmetric included; the delivered
symmetric version stays with its hypothesis set superseded.

QA per this document's own plan, fences in the same delivery: the K₂
membership and complement cases through the theorems (`bol_K2_mem`,
`bol_K2_notmem`, plus the combined-form consumer
`bol_K2_mem_via_casesplit`); the whole action vector computed RAW
(`bol_K2_raw` — matrix arithmetic through the Laplacian definition,
independent of the new theorems); the path fixture's three entries
(`bol_path_pin` — membership, crossing complement, and the
crossing-free branch at value `0`); **the asymmetric-cut disagreement
fence** (`bol_dir_fence`: arc weights `3`/`1`, case values `3` and
`-1`, provably different — the theorem is not one value restated with
a sign) plus the directed-input instantiation `L · 1_S = ![3, -1]`
(`bol_dir_action` — the no-hidden-symmetry fence: the theorems apply
on asymmetric `A` at all, since they are hypothesis-free); the
boundary row-sum tie through the delivered `mwEdgeAdj_boundary_single`
pin (`bol_sum_boundary`); and **the Dirichlet-energy two-route join**
(`bol_quadForm_unsymm_route` vs `bol_quadForm_symm_route`: the new
hypothesis-free identity and the delivered symmetric-`hA` identity,
one value `1` — they agree only if both proofs are right).

Verification: spike-first (`wip/bol_spike.lean` — green after three
fix rounds; the traps: `refine Finset.sum_congr` cannot unify against
a NEGATED sum (the stuck-`AddCommMonoid` symptom — the
`have`-with-explicit-type cure); the `fin_cases`-vacuous-case pattern
`first | exact absurd rfl h | norm_num [...]` for entry lemmas whose
by_cases hypotheses become contradictory; opaque-def Finset sums
needing `simp only [defName]` before `Finset.sum_singleton`; and the
Fin-eta `fin_cases` noise absorbed by `exact` through defeq); both
landed modules elaborate with zero errors/warnings; explicit builds ✔;
**full `lake build` + `check_build_completeness.py` — 135 source
files, 135 fresh artifacts, 0 stale, 0 missing, exit 0**;
`lint_axioms` exit 0 (4 axioms unchanged); `check_refutation_
independence` (24-tag clean); `check_public_reachability`
(63 modules); `check_citations`; `check_markdown_links`;
`check_qa_name_uniqueness` (the new `bol*` names collision-free);
`check_backlog_freshness` clean; scoreboard regenerated (1364/6625/4/0)
with the verification row; index coverage added
(`index/map/spectral_graph.md`); map freshness exit 0 after the
1364/6625 stats sync in both map data tables + SVG regeneration
(49 stations, no status change owed).

Step 2 remains BLOCKED on `global-semigroup-contraction.md`'s Steps
1–2, per this document's operating instructions — not re-derived
inline. When the companion clears its gate, Step 2 is a
three-lemma composition as priced above.

## Part 2 delivery record (2026-09-07, run `20260907T053227Z-run-2`)

**Gate note — the consumer-scope reading.** The companion's own gate
says its steps wait for "an explicit adoption decision, **or a
different named consumer**." This document — the operator-added Medium
row, whose row text says "no operator or technical decision gates it,
only a build-order dependency on that companion proposal's Steps 1–2
… once that lands" — is that named consumer. The delivering run
therefore treated the companion's Steps 0(m=0)/1/2 as unblocked at
exactly the consumer's scope, and left the companion's Steps 3–5 (the
order-`m` generalization and operator-norm restatement) gated. This
interpretation is recorded here, in the companion's status header, in
the execution plan, and in the activity log, so the operator can veto
it on review; everything is hard crust, uncommitted, and reversible.

**Delivered.** The companion's Steps 0(m=0)/1/2 in `Heat.lean`'s new
"global (window-free) contraction" section (functional 1364 → 1369):
the scalar engine `sq_one_sub_exp_neg_le` (`(1 − e^{−y})² ≤ y²` on the
half-line — from `Real.add_one_le_exp` and `Real.exp_le_exp`; the
order-0 instance of the companion's Step 0, whose general order-`m`
induction stays gated), the Step-1 dotProduct bound
`heatKernel_globalContraction_dotProduct_le` (`(x − e^{−tL}x) ⬝ᵥ (x −
e^{−tL}x) ≤ t² (Lx ⬝ᵥ Lx)` at every `t ≥ 0` on symmetric
nonnegative-weight networks — Parseval over the proved eigenbasis, the
per-mode coordinate `(1 − e^{−tλᵢ})` bounded by the scalar engine at
`y := tλᵢ ≥ 0` via the PSD extraction, reassembled through the
Laplacian's own Parseval), the Step-2 Euclidean corollary
`heatKernel_globalContraction_le` (`‖x − e^{−tL}x‖ ≤ t·‖Lx‖` — the
request's first formula verbatim), and this proposal's own Part 2:
the general-probe dissipation engine `abs_dotProduct_heatFlow_le`
(`|v ⬝ᵥ (x₀ − e^{−tL}x₀)| ≤ t·√(Lv ⬝ᵥ Lv)·√(x₀ ⬝ᵥ x₀)` — the
symmetric swap putting the semigroup on the probe, Cauchy–Schwarz,
the contraction at the probe) plus the `partIndicator` specialization
`abs_partIndicator_dotProduct_heatFlow_le` in `Multiway.lean` (the
request's second formula verbatim, the norm factor being the outflow
vector `L·1_S`'s own norm — Step 1's object).

**QA** (10 theorems; QA 6625 → 6635): per the companion's own plan,
the payoff pin — the global bound THROUGH the theorem at `t = 1` on
K₂, where `t·λ = 2` provably violates the windowed bound's
`|t·λᵢ| ≤ 1` (`heatKernel_edge_remainder_window_fenced_QA`'s own
fixture) — with both sides evaluated (LHS `2(1−e^{−2})² ≤ 2`, RHS
exactly `8`); the Euclidean form at the same point; the
general-probe dissipation pin (the probe `e₀`'s Laplacian action
pinned as the outflow vector `![1,−1]`); the Part-2 pin at the bol
fixture (`S = {0}`, `t = 1`, the norm factor through Step 1's own
`bol_K2_raw`); and **the `hnonneg` fence in the same delivery** (the
companion's standing instruction): on the signed K₂ fixture
(`!![0,−1;−1,0]]`, symmetric, Laplacian eigenvalue `−2`), the
conclusion GENUINELY fails at `t = 1` — the mode grows, `K₁m = e²•m`
with `3 < e²` by `Real.add_one_lt_exp`, LHS `2(e²−1)² > 8` = RHS —
with `hA` kept genuine, so the nonnegativity hypothesis is
load-bearing, not decorative.

**Verification.** Spike-first (`wip/gsc_spike.lean` — green after
five fix rounds; the traps: the pinned Mathlib's `sq_le_sq'` being
the `−b ≤ a ≤ b` form, not the `0 ≤ a ≤ b` form; `Finset.mul_sum`
refusing to rewrite under a metavariable-instantiated sum (the
term-mode calc route instead); Duhamel's lemmas living in the fully
qualified `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation`
namespace, not the bare name; `(1 : ?) • M` defaulting the scalar to
`ℕ` (annotate `(1 : ℝ)`); and `1 * √2 * √2` being left-associated so
`one_mul` must precede the `pow_two` reassociation). All four touched
modules build explicitly; the full ladder passes — `lake build` +
`check_build_completeness.py` (135/135 fresh), `lint_axioms` exit 0
(4 axioms unchanged), `check_refutation_independence` (24-tag clean),
`check_public_reachability` (63 modules), `check_citations`,
`check_markdown_links`, `check_qa_name_uniqueness` (the new `gsc*` /
`bol_dissipation_K2` names collision-free), `check_backlog_freshness`
clean; scoreboard regenerated (1369 / 6635 / 4 / 0); map freshness
exit 0 after the stats sync in both map tables + SVG regeneration
(49 stations, no status change owed); the 16-declaration axiom audit
(`wip/gsc_axcheck.lean`: 5 shelf + 11 QA) — every one exactly
`propext, Classical.choice, Quot.sound`.

**Mid-run incident, recorded for the operator.** The delivering run's
operator (this agent) ran `git checkout` on `Multiway.lean` during
landing-script debugging — which silently discarded the *uncommitted*
Step-1 section (109 lines) from the prior run. No history was lost
(the content was reconstructed verbatim from the prior run's recorded
read and re-verified: `Multiway.lean` elaborates and
`MultiwayCheeger_QA.lean` — with all ten `bol_` theorems — builds
against it; the restored file now diffs +100 lines vs HEAD, the delta
being blank-line wrapping). Lesson recorded: `git checkout` on files
carrying uncommitted sibling-run deliveries is never safe; landing
thereafter used additive `edit` operations only.

**Residue.** The companion's Steps 3–5 (order-`m`) remain operator-
gated exactly as before. A dedicated asymmetric-`hA` fence for the
dissipation form is priced (the swap consumes `heatKernel_isSymm`;
every 2-vertex nonnegative asymmetric `D − A` has PSD spectrum
`{0, a₁₂+a₂₁}`, so a failing fixture needs either ≥ 3 vertices or
transient non-normal growth — heavier than this delivery's scope).
The `partIndicator` specialization is stated at `S` directly; a
`Sᶜ`-flipped form would go through `boundary_compl` as before.
