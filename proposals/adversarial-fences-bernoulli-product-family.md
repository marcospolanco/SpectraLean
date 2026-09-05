# The Bernoulli-Product Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-05 by run
`20260905T191343Z-run-1`, session `ses_f8d05c8e1ffetzzSvB5NA7IdOu`;
see the delivery record).

## Scope

The prior terminal handoff's first named natural next move — "by the
survey's numbers the next unaudited surfaces are `BernoulliProduct`
(7 transitive non-QA consumers — the sampling engine this delivery
itself consumed heavily) and the scalar concentration family" —
confirmed and picked by this run's own fresh reverse-import walk:
**`BernoulliProduct` at 8 transitive non-QA consumers** (the umbrella
plus `IIDProduct`, `EdgePerturbation`, `Sparsification`, and the
Derived `EdgePerturbationTail`, `EdgePerturbationDrift`,
`SparsificationTail`, `EmpiricalStationary` capstones) vs the scalar
concentration family's 5. The shelf is
`Scaffold/Mathlib/Probability/BernoulliProduct.lean` (616 lines, 21
public declarations): the product-Bernoulli sampling space `bernPMF`
and the interfaces that discharge the matrix concentration axioms'
`h_indep`/`h_mean`/`h_meas` clauses at a concrete measure. Everything
on the shelf is proved — no axiom — so this is a theorem-instantiation
audit (no `-- @refutes` tags; the fences refute dropped-hypothesis
statement shapes of proved theorems, consuming nothing admitted).

**SGT leverage:** this shelf is the instantiation layer of 3 of the 4
remaining admitted axioms. Every `h_indep`, `h_mean`, and `h_meas`
clause of `matrix_hoeffding`/`matrix_bernstein`/
`matrix_azuma_hoeffding` is discharged at exactly these interfaces
(`iIndepFun_coord_matrix`, `integral_coord_center_smul`,
`stronglyMeasurable_coord_matrix`) by the sparsification,
edge-perturbation, and derived capstone designs. A wrong product
structure here — a marginal that does not factor, an independence
transfer that survives a non-injective reindexing — would poison every
conditional tail bound downstream while every QA stayed green. The
audit makes each clause shape falsifiable at its source.

Its QA (`BernoulliProduct_QA.lean`, 342 lines) carries the positive
pin layer (four-atom mass enumeration, marginals, cylinders,
independence numeric, centering integrals, matrix layer) and exactly
two free-form fences — `bp_out_of_bounds_fence_QA` (the `[0,1]` bounds
at the mass level) and `bp_center_zero_fence_QA` (+ nonzero companion,
the centering hypothesis `p e ≠ 0`) — never reconciled into the
per-clause hypothesis-form discipline. Method:
`governance/ADVERSARIAL_REVIEW.md`'s hypothesis-necessity pass
(twenty-four precedents: TV/Dobrushin, lazy, entropy, Poisson-bridge,
primitivity-supplier (+ consumer follow-on), irregular Cheeger,
regular Cheeger, effective-resistance, electrical-flow, Foster,
sparsification-core, band-projector, Davis–Kahan core, normalized,
variational-transfer, resolvent, Perron–Frobenius, heat, random-walk,
stationary, irreducible-stationary, directed, spectral-core (Steps
0–4), matrix-concentration).

## Step-0 findings: the priced fence list

Clause census over the shelf's 21 public declarations — 16 carry
mathematical hypotheses; five are hypothesis-free (`jointMass_ne_top`,
`bernPMF_apply`, `measurable_coord`, `stronglyMeasurable_coord_matrix`,
`measurable_coord_matrix`; nothing to drop). Four clause shapes:

1. **`hp1 : ∀ i, p i ≤ 1` (and `hp0 : ∀ i, 0 ≤ p i`)** on the four
   ∑-theorems whose statements do not mention `bernPMF`:
   `sum_bern_eq_one`, `sum_jointMass_eq_one`, `sum_coord_mul`,
   `sum_coord2_mul`. Fenceable at out-of-bounds fixtures keeping the
   other bound genuine (`p = ![2]` breaks `hp1` only; `p = ![-1]`
   breaks `hp0` only — through the `ENNReal.ofReal` clamp, the
   negative-`p` corner zeroes the true-mass and doubles the
   false-mass, so the coordinate mass sum is `2 ≠ 1` from either
   side). The `Fin 1` fixtures suffice for the first two theorems;
   `sum_coord_mul` needs `Fin 2` (on `Fin 1` both sides of the
   marginal identity are the same two-atom sum, so the dropped
   statement is true there — the identity needs a *third* broken
   coordinate to fail); `sum_coord2_mul` needs `Fin 3` (both its
   quantified coordinates are consumed by the statement, so a broken
   coordinate must sit *outside* `{e, e'}`: at `![1,1,2]` with
   `e = 0, e' = 1` the third coordinate's mass sum `2` multiplies the
   left side only, `2 ≠ 1`; at `![-1,1,1]` with `e = 1, e' = 2` the
   broken coordinate `0` plays the same role).
2. **`hp0`/`hp1` on the eleven `bernPMF`-consuming theorems**
   (`toMeasure_cyl`, `indepFun_coord`, `integral_delta`,
   `integral_sq_delta_sub`, `toMeasure_cyl_inter`, `iIndepFun_coord`,
   `iIndepFun_coord_apply`, `iIndepFun_coord_matrix`,
   `indepFun_coord_matrix`, `integral_coord_smul`,
   `integral_coord_center_smul`): **signature-entangled** —
   `bernPMF p hp0 hp1` takes the proofs as arguments, so the dropped
   statement cannot be formed out of bounds; the sampling measure
   does not exist there (the module docstring says exactly this:
   "outside `0 ≤ p i ≤ 1` the joint masses simply fail to sum to `1`
   and `bernPMF`'s hypotheses cannot be discharged"). The mass-level
   fences of item 1 are that entanglement's visible boundary — the
   normalized object degenerates before any conclusion about it can
   fail.
3. **`hee : e ≠ e'`** on `sum_coord2_mul`, `indepFun_coord`,
   `indepFun_coord_matrix`: fenceable at the all-genuine fixture
   `Fin 1`, `p = ![1/2]`, `e = e' = 0`. For the double marginal the
   kill is **Cauchy–Schwarz strictness**: with `F = G` two-valued
   (`2` at false, `3` at true), `∑ F·G·bern = 13/2` against
   `(∑ F·bern)·(∑ G·bern) = 25/4` — a genuinely different mechanism
   from the bounds clauses: the hypothesis is load-bearing not because
   some normalization collapses but because a single coordinate
   cannot be independent of itself. The same mechanism kills both
   independence clauses: at `s = t = {true}`, `μ(A ∩ A) = μ(A) =
   1/2 ≠ 1/4 = μ(A)·μ(A)` (scalar codomain directly; matrix codomain
   at the entry cylinder `{N | 1/2 < N 0 0}`, measurable at the
   hand-rolled product σ-algebra through the nested
   `measurable_pi_apply` composition).
4. **`he : Function.Injective e`** on the mutual-independence
   transfer trio `iIndepFun_of_injective`, `iIndepFun_coord_apply`,
   `iIndepFun_coord_matrix`: fenceable at the constant reindexing
   `e : Fin 2 → Fin 1` (both indices land on coordinate `0`), making
   the reindexed family `(ω ↦ ω 0, ω ↦ ω 0)` — perfectly correlated,
   killed at `T = univ`, `sets = {true}, {true}` (scalar and `apply`
   forms) and at the entry cylinder (matrix form). This is the
   clause the sparsification designs actually exercise (they reindex
   edges into coordinates injectively); its necessity has no witness
   anywhere in the repository.
5. **`hpne : p e ≠ 0`** on `integral_coord_center_smul`: already
   fenced free-form (`bp_center_zero_fence_QA` computing the junk
   value `-M` at `p = ![0]`, with the `≠ 0` companion) — to be
   reconciled into the hypothesis-form discipline as a wrapper.

**Screened:** conclusion strengthening is not priceable per the
Perron–Frobenius audit's precedent. The `[Fintype ι]`/
`[DecidableEq ι]` binders are instance arguments, not mathematical
hypotheses.

## Fixtures (all rational, all new, file-uniquely named)

- `bpHalf = ![1/2]` (Fin 1) — the all-genuine base for every `hee`/
  `he` fence: in bounds, so `bernPMF` forms and every kept clause is
  dischargeable.
- `bpTwo = ![2, 2]` (Fin 2) — the `hp1` breaker for `sum_coord_mul`
  (kept `hp0` genuine).
- `bpNeg2 = ![-1, -1]` (Fin 2) — the `hp0` breaker for `sum_coord_mul`
  (kept `hp1` genuine).
- `bp3T = ![1, 1, 2]` (Fin 3) — the `hp1` breaker for `sum_coord2_mul`
  (broken third coordinate outside `{e, e'}`).
- `bp3N = ![-1, 1, 1]` (Fin 3) — the `hp0` breaker for `sum_coord2_mul`
  (broken coordinate `0` outside `{e, e'}` = `{1, 2}`).
- `![2]` / `![-1]` (Fin 1, anonymous) — the mass-level breakers for
  `sum_bern_eq_one`/`sum_jointMass_eq_one`.

## Delivery record

DELIVERED at the full priced scope — QA-only, an insertion before the
closing `end` of `BernoulliProduct_QA.lean` (the new
`AdversarialFences` section plus the file's Fin 1 enumeration helpers):
all fifteen hypothesis-form fences (the thirteen spikable ones plus the
two reconciliation wrappers consuming the file's delivered free-form
fences `bp_out_of_bounds_fence_QA` and
`bp_center_zero_fence_nonzero_QA` as their proof engines — both
pre-discipline witnesses are now inside the per-clause discipline),
the five fixture `def`s with their genuine-clause companions
(`bpTwo_nonneg`, `bpNeg2_le_one`, `bp3T_nonneg`, `bp3N_le_one`,
`bpHalf`'s bounds pair), and the shared kill engines
(`bpF_ofReal_ne_ofReal` private, `bpF_cyl_half`,
`bpF_matrix_entry_measurable` + `bpF_entry_cyl_measurable` +
`bpF_entry_cyl_preimage` — the entry-cylinder route at the hand-rolled
matrix product σ-algebra). 30 new declarations (25 public theorems
counted by the generator metric + 5 fixture `def`s; 3 private
helpers); QA 6114 → 6139 (+25). Zero axiom contact (`#print axioms`
via `wip/bpfences_axcheck.lean` on all 25 public declarations — every
one exactly `propext, Classical.choice, Quot.sound`; no `-- @refutes`
tags — theorem instantiations of an all-proved shelf, nothing admitted
consumed; the 24-tag independence check unchanged and clean).

The fences, each a first fence-form witness for its clause:

1. **`bpFence_sum_bern_le_one` / `bpFence_sum_bern_nonneg`** —
   `sum_bern_eq_one`'s `hp1` at `![2]` (kept `hp0` genuine:
   `0 + 2 = 2 ≠ 1`) and `hp0` at `![-1]` (kept `hp1` genuine:
   `2 + 0 = 2 ≠ 1`): the `ENNReal.ofReal` clamp zeroes negative masses
   and passes positive ones, so out of bounds the coordinate mass sums
   to the doubled false-mass from either side.
2. **`bpFence_sum_joint_le_one` / `bpFence_sum_joint_nonneg`** — the
   joint-mass twins at the same fixtures; the `hp1` wrapper *consumes*
   the delivered free-form fence (the reconciliation proper), the
   `hp0` fence computes the same value at `![-1]`.
3. **`bpFence_sum_coord_mul_le_one` / `bpFence_sum_coord_mul_nonneg`**
   — the one-coordinate marginal's bounds clauses at `Fin 2` fixtures:
   the broken coordinate's mass sum `2` multiplies the left side only
   (`4 ≠ 2` at the true-indicator, `e = 0`, `p = ![2,2]`; the
   false-indicator at `p = ![-1,-1]`). **Pricing finding:** on `Fin 1`
   both sides of the dropped statement are the same two-atom sum — the
   marginal identity holds there for ANY `p` (Fubini needs no
   normalization when no coordinate is left over) — so the bounds
   fences genuinely need a second coordinate.
4. **`bpFence_sum_coord2_le_one` / `bpFence_sum_coord2_nonneg`** — the
   two-coordinate marginal's bounds clauses at `Fin 3` fixtures
   (`![1,1,2]` with `e = 0, e' = 1`; `![-1,1,1]` with `e = 1, e' = 2`):
   both quantified coordinates are consumed by the statement, so the
   breaker must sit *outside* `{e, e'}` — the broken mass sum `2`
   multiplies the left side only (`2 ≠ 1`). Same finding one dimension
   up: on `Fin 2` the dropped statement is true at every `p`.
5. **`bpFence_sum_coord2_hee`** — the distinctness clause at the
   all-genuine `Fin 1` fixture `p = ![1/2]`, `e = e' = 0`, `F = G`
   two-valued (`2`/`3`): `∑ F·G·bern = 13/2` against
   `(∑ F·bern)·(∑ G·bern) = 25/4` — **Cauchy–Schwarz strictness on a
   two-point space**, a genuinely different mechanism from the bounds
   clauses: nothing degenerates, the hypothesis is load-bearing
   because a single coordinate cannot be independent of itself.
6. **`bpFence_indepFun_coord_hee` / `bpFence_indepFun_matrix_hee`** —
   the same clause at both independence statements: with `e = e' = 0`
   the two "independent" functions are identical, and
   `μ(A ∩ A) = μ(A) = 1/2 ≠ 1/4 = μ(A)·μ(A)` at `s = t = {true}`. The
   matrix twin's kill set is the entry cylinder
   `{N | 1/2 < N 0 0}` — measurable at the shelf's hand-rolled
   `MeasurableSpace.pi` matrix σ-algebra through the nested
   `measurable_pi_apply` composition (the `Matrix_QA` precedent route),
   whose preimage under `ω ↦ bpMat (ω 0)` is exactly the Bool
   true-cylinder.
7. **`bpFence_iIndep_injective_he` / `bpFence_iIndep_apply_he` /
   `bpFence_iIndep_matrix_he`** — the injectivity clauses of the
   mutual-independence transfer trio at the constant reindexing
   `e : Fin 2 → Fin 1` (both indices land on coordinate `0`): the
   reindexed family is `(ω ↦ ω 0, ω ↦ ω 0)` — perfectly correlated —
   killed at `T = univ` with both sets the true-cylinder (Bool) or the
   entry cylinder (matrix). This is the clause the sparsification and
   edge-perturbation designs actually exercise (they reindex edges
   into coordinates injectively); its necessity had no witness
   anywhere in the repository.
8. **`bpFence_center_hpne`** — the centering wrapper consuming the
   delivered `bp_center_zero_fence_QA` value (`-M` at `p = ![0]`) and
   its `≠ 0` companion: the junk quotient `0 / 0 = 0` makes the
   "centered" integrand the constant `-M`.

Technique findings recorded for future audits:

1. **`rw` with a ∀-equation under a `Finset.sum` binder fails where
   `simp only` succeeds.** Rewriting `g 0 ?b` into
   `∑ j : Bool, g 0 j` via `rw [hg0] at h` fails ("did not find
   instance of the pattern") while the displayed hypothesis plainly
   contains the term; `simp only [hg0] at h` performs the same
   rewrite (matching up to reducible defeq). The same medicine fixes
   the `sets := fun _ => {true}` beta-redexes left behind by applying
   `iIndepFun_iff_measure_inter_preimage_eq_mul`'s ∀-form: state the
   collapse lemma at the beta-reduced shape and apply it via
   `simp only`.
2. **`simp only` consumes innermost-first, so state auxiliary set
   rewrites at the POST-rewrite shape.** A collapse lemma
   `⋂ k, (matrix-cylinder) = (matrix-cylinder)` never fires when a
   cylinder-transfer simp lemma has already rewritten the body to the
   Bool form; stating the collapse at the Bool form and ordering it
   after the transfer fires both.
3. **`iIndepFun_iff_measure_inter_preimage_eq_mul` takes `sets` as a
   named implicit** — positional application silently elaborates the
   sets argument as the measurability hypothesis (the shelf's own
   `(sets := A)` idiom is load-bearing, and the hypothesis takes TWO
   binders: `fun _ _ => ...`).
4. **`ENNReal` has no `norm_num` instance at this pin** — every
   ℝ≥0∞ numeric kill must route through `ofReal`-bridges
   (`← ofReal_mul`/`← ofReal_add` with postponed `by norm_num` side
   goals, `ofReal_eq_zero.2` for the clamp, `(ofReal_natCast n).symm`
   to bridge numerals into `ofReal` form) with the ℝ-side arithmetic
   discharged by real `norm_num` after `congr 1`. Full `simp at h`
   both reduces the Bool ite-literals AND (unlike `simp only`) leaves
   `ofReal` numerals untouched, so it is safe mid-chain.

## Verification

Spike first (`wip/bpfences_spike.lean` — the thirteen spikable fences
plus helpers, iterated to zero errors/zero warnings over ~7 fix
rounds, all in the recorded trap classes above); `lake env lean` on
the landed module (zero errors, zero warnings — clean on the first
post-landing elaboration); explicit `lake build
Scaffold.QA.Probability.BernoulliProduct_QA` ✔ (2043/2043, the only
warnings the pinned Mathlib's own doc-string linter notes); the
25-public-declaration axiom audit above; **full `lake build` ✔
immediately followed by `check_build_completeness.py` — 134 source
files, 134 fresh artifacts, 0 stale, 0 missing, exit 0**;
`lint_axioms` exit 0 (4 current axioms, unchanged);
`check_refutation_independence` (24-tag clean — no tags touched);
`check_public_reachability` clean (63 repo modules);
`check_citations` ("All axioms have proper citations!");
`check_markdown_links` clean; `check_qa_name_uniqueness` clean (the
new `bp*` names collision-free); `check_backlog_freshness` clean;
scoreboard regenerated (**6139/4/0**) with the verification row;
map-freshness exit 0 after the 6114 → 6139 stats sync in both map
data tables and SVG regeneration (49 stations, no status change —
none owed: the audit's proposal is not a map station's cited source).
Records updated: this proposal (COMPLETE + delivery record), the
scoreboard verification row, README (6139), the radar (QA row synced,
held 4.5), the backlog item-2 falsification-surface ledger, both map
data tables + regenerated SVG, `index/map/probability_concentration.md`
(the audit-coverage note in the Bernoulli Product Space section), the
execution plan, and the activity log. Nothing committed; prior runs'
uncommitted deliveries preserved.
