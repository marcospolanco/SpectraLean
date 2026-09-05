# The Resolvent Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-05 by run `20260905T004138Z-run-1`,
session `ses_f90ff2f69ffeA3oqUOZajPQX4v`; see the delivery record).

## Scope

The prior terminal handoff's named top survey target — "the audit
method's natural next targets, by this run's fresh survey numbers:
`Resolvent` (16 consumers — the largest remaining unaudited shelf, its
1153-line QA already carrying free-form negative witnesses that a
Step-0 pass should reconcile into the fence discipline)" — confirmed by
this run's own independent reverse-import walk: **16 transitive non-QA
consumers** (the direct importers are `Weyl`, `ProjectionGap`,
`FunctionalCalculus`, `PolyFilter`, `Sparsification`, and
`MasterBound`; the transitive closure adds `DavisKahan`, `Duhamel`,
`BandDavisKahan`, `Fiedler`, `Poincare`, `EdgePerturbation`, and four
Derived capstones) — the library's most-consumed unaudited shelf. The
shelf is `Scaffold/Mathlib/Analysis/OperatorTheory/Resolvent.lean`
(14 public theorems: the operator-norm bridge in both directions and
both API forms, the extremal packaged equality, the shifted-PSD
invertibility pair, the resolvent identity, the general-`t` and `+1`
norm bounds, the Lipschitz bound, and the injectivity trio). Its QA
(`Resolvent_QA.lean`, 1153 lines, delivered 2026-08-19/20) predates the
adversarial-review discipline and carries five free-form negative
witnesses (`mat2_not_opNorm_le_one_QA`, `lap2_det_eq_zero_QA`/
`lap2_det_not_isUnit_QA`, `unshifted_inv_norm_not_le_one_QA`,
`hypothesis_guard_not_le_one_QA`,
`resolvent_injective_needs_invertibility_QA`) that had never been
reconciled into the fence discipline, and several load-bearing clause
classes with no negative witness anywhere.

Method: `governance/ADVERSARIAL_REVIEW.md`'s hypothesis-necessity pass
(fifteen precedents: TV/Dobrushin, lazy, entropy, Poisson-bridge,
primitivity-supplier (+ consumer follow-on), irregular Cheeger, regular
Cheeger, effective-resistance, electrical-flow, Foster,
sparsification-core, band-projector, Davis–Kahan core, normalized, and
variational-transfer) — re-read every theorem's hypothesis clauses,
identify those with no negative witness, and close each with a
hypothesis-form fence (the dropped-hypothesis statement refuted at a
fixture where every other hypothesis is genuine, certified by
pinned-value companions), or record a non-fenceable with its mechanism.

Consumer case (the leverage): the shelf is the load-bearing norm spine
(`cstar_norm_def` transport, `opNorm_le_bound`) under most of the
proved spectral layer — every `l2OpNorm` statement in the perturbation
chain, the polyfilter transfer bound, and the master-bound program
routes through the bridge or the resolvent bounds delivered here.

## Step-0 findings: the priced fence list

Clause census over the 14 public theorems (the private helpers
`norm_euclidean_sq`, `abs_dotProduct_le`,
`t_smul_dotProduct_self_le`, `abs_le_max_abs_of_le` are audited
transitively via the public consumers, per the audit convention):

1. **Both upper-bridge `hc` clauses** (`0 ≤ c` in
   `l2OpNorm_le_of_abs_eigvalOf_le` and
   `l2OpNorm_le_of_abs_evals_le`). Priced at a new `Fin 0` fixture:
   on a nonempty type the eigenvalue hypothesis already forces
   `c ≥ 0` through `|λ| ≥ 0`, so the *only* satisfiable failure corner
   is the empty index type, where every eigenvalue clause is vacuous
   while the operator norm is still `0` (the underlying space is
   trivial). The norm-zero pin must be independent of the bridge being
   fenced: `cstar_norm_def` (a `rfl` lemma) plus
   `ContinuousLinearMap.opNorm_le_bound` on the trivial space, through
   `Subsingleton.elim` — no eigenvalue machinery at all.
2. **The general-shift invertibility's `hpsd` and `ht` clauses**
   (`isUnit_det_add_smul_one_of_quadForm_nonneg`). `hpsd` at
   `M = -(1)`: the `t = 1` shift lands on the zero matrix (determinant
   `0`), with the quadratic form exhibited negative at `![1,0]` and
   `0 < 1` genuine. `ht` at `t = 0` on the delivered `lap2`: PSD
   genuine through the delivered `lap2_psd`, determinant `0` by the
   delivered pin — this fence makes explicit what
   `lap2_det_not_isUnit_QA` already establishes in value form.
3. **The `+1` invertibility's `hpsd` clause**
   (`isUnit_det_add_one_of_quadForm_nonneg`) — same `-1` witness.
4. **The resolvent identity's `hA` and `hB` clauses**
   (`resolvent_identity_sub`). Neither determinant hypothesis had a
   negative witness. The mechanism: with exactly one side's `+1` shift
   singular, that side's resolvent is the junk inverse `0` (pinned by
   the delivered `negOne_add_one_inv_eq_zero_QA`) while the other
   side's is the genuine `1` — and the identity's two sides separate
   (`0 - 1 = -1` against `0 * _ * 1 = 0` for `hA`; `1 - 0 = 1`
   against `1 * _ * 0 = 0` for `hB`), with the kept hypothesis genuine
   through the delivered `zero_add_one_isUnit_det_QA`. A pair where
   *both* shifts are singular would not serve (both sides collapse to
   `0` identically — the same trap the delivered injectivity guard
   navigates).
5. **The general-`t` norm bound's `ht` and `hpsd` clauses**
   (`l2OpNorm_inv_add_smul_one_le_inv_of_quadForm_nonneg`). `ht` at
   `t = 0` on the delivered `quartOne` (PSD genuine): the genuine
   inverse has pinned norm `4` (both pins delivered) against
   `0⁻¹ = 0`. Note the trap: at `t = 0` on a *singular* PSD matrix the
   statement holds by junk (the junk inverse is `0`, and `‖0‖ = 0 ≤
   0`), so the fixture must be invertible — `quartOne`, not `lap2`.
   `hpsd` at `t = 1` on the delivered `negThreeQuart` (positivity
   genuine, PSD violated and exhibited by the delivered
   `negThreeQuart_not_psd_QA`): the `+1` shift *is* `quartOne` (the
   delivered `negThreeQuart_add_one`), so the bound demands `4 ≤ 1`.
6. **Both Lipschitz `quadForm` clauses**
   (`l2OpNorm_resolvent_sub_le_of_quadForm_nonneg`). At
   `A = negThreeQuart`, `B = 0` (either clause dropped, the other
   side's PSD genuine through the delivered `zero_psd_QA`): the left
   side is `‖fourOne - 1‖ = ‖3I‖ = 3` and the right side is
   `‖negThreeQuart‖ = 3/4` — a `4×` separation. Requires two new
   diagonal spectrum pins (`threeOne = 3I` and `negThreeQuart`'s own
   spectrum `[-3/4, -3/4]`, both through the file's private
   two-point pin machinery) plus the connection pins
   `fourOne - 1 = threeOne` and `‖1 - fourOne‖ = 3` (by `norm_neg`).
7. **The injectivity trio's jointly dropped `hA`+`hB` clauses**
   (`eq_of_inv_add_one_eq_inv_add_one`,
   `resolvent_map_injective_of_quadForm_nonneg`,
   `inv_add_one_eq_inv_add_one_iff_of_quadForm_nonneg`). The delivered
   guard pair (`-1` vs `-1 + E`: both `+1` shifts singular, both
   resolvents the junk `0`, matrices distinct) refutes the jointly
   hypothesis-free statement of the packaged injectivity form; the
   core and iff forms' jointly-dropped equivalents follow. One new
   explicit fence composes the three delivered witnesses.

**Screened (delivered witnesses already establish the dropped
statement):** both upper-bridge `h` clauses
(`mat2_not_opNorm_le_one_QA` refutes `‖mat2‖ ≤ 1`, the bound by one
eigenvalue instead of all — at `c = 1` the hypothesis-free statement is
directly false); the `+1` norm bound's `hpsd`
(`hypothesis_guard_not_le_one_QA` *is* its dropped form at
`negThreeQuart`); the core injectivity's jointly-dropped form
(`resolvent_injective_needs_invertibility_QA`).

**Non-fenceable, with mechanisms:** the five `hM` clauses
(signature-entangled — `eigvalOf M hM` and `evals hM` cannot be stated
without the symmetry proof, so there is no dropped-hypothesis statement
to refute); `l2OpNorm_eq_max_abs_evals`'s `hcard`
(proof-term-in-display — the conclusion's `⟨0, by omega⟩` index proof
consumes `hcard`, so the dropped statement does not elaborate; the
Davis–Kahan core audit's precedent mechanism); and the injectivity
trio's *individually* dropped determinant clauses (**P4
truth-removable**: if one factor's `+1` shift is invertible and both
junk inverses coincide as `R`, then `R * (B+1) = 1` gives `R` a right
inverse, hence invertible in finite dimensions, and `R = (A+1)⁻¹` then
forces `A + 1` invertible unless `R = 0` — impossible since `R(B+1) =
1 ≠ 0` — so the kept theorem applies; only the joint drop is false,
which fence 7 witnesses).

## Delivery plan

QA-only, a pure insertion into `Resolvent_QA.lean` (a new
`AdversarialFences` section after `end Injective`, plus a
Purpose-block paragraph): 12 fences + 22 companion/pin theorems + 2
fixture `def`s (`rfZeroM` the empty matrix, `threeOne` the Lipschitz
left-side fixture). Spike in `wip/rfences_spike.lean` first (the
file's private two-point pin helpers re-declared locally, replaced by
the file's own at landing), then land, then the axiom audit via
`wip/rfences_axcheck.lean` (`#print axioms` on all 36 declarations),
then the full verification ladder and records.

## Delivery record

Delivered at the full priced scope: 12 fences, all closed. QA-only
(+34 by the generator metric, 5240 → 5274; 36 declarations = 34
theorems + 2 fixture `def`s), zero axiom contact (`#print axioms` via
`wip/rfences_axcheck.lean` on all 36 declarations — every one exactly
`propext, Classical.choice, Quot.sound`; no `-- @refutes` tags —
theorem instantiations, nothing admitted consumed).

The headline findings, each closing a clause class with no prior
negative witness:

- **The empty corner is the only `hc` failure corner.** Both upper
  bridges' `0 ≤ c` clauses are load-bearing *only* through `Fin 0` —
  on every nonempty type the eigenvalue hypothesis already forces
  `c ≥ 0`. The fence pins `‖0‖ = 0` on `Fin 0` by a route independent
  of the fenced theorem (the `cstar_norm_def`/`opNorm_le_bound`
  transport on the trivial space through `Subsingleton.elim`) and
  refutes the dropped statement at `c = -1`.
- **PSD is load-bearing for shifted invertibility, and so is the
  shift.** `M = -1` (form `-‖x‖²` exhibited at `![1,0]`) kills both
  `hpsd` clauses at `t = 1` / the `+1` form; `t = 0` on `lap2` kills
  `ht` with PSD genuine — the explicit-fence form of what
  `lap2_det_eq_zero_QA` pinned in value form.
- **The resolvent identity needs both determinant clauses, one-sided.**
  A singular shift on exactly one side separates the identity (`-1 ≠
  0` resp. `1 ≠ 0`); a both-singular pair collapses both sides to `0`
  identically and cannot serve — the pricing had to distinguish these.
- **The norm bound's `t > 0` is genuine, not vacuous.** The `t = 0`
  fence requires an *invertible* PSD fixture (`quartOne`): at `t = 0`
  on a singular PSD matrix the dropped statement is true by junk (the
  junk inverse is the zero matrix) — an instance of the
  junk-value-inverts-the-fence hazard class.
- **The Lipschitz `quadForm` clauses separate by 4×.** `3 ≤ 3/4` at
  `negThreeQuart` vs `0`, through two new diagonal spectrum pins.

Technique findings (for future audits):

1. **`Matrix.det_zero`'s `Nonempty` argument is explicit and unnamed**
   — `rw [Matrix.det_zero]` strands the side goal `⊢ Nonempty (Fin 2)`;
   the robust route is `exact Matrix.det_zero (n := Fin 2) ⟨⟨0, by
   decide⟩⟩`.
2. **`inv_zero` is ambiguous in `rw` under `open Matrix`** (both
   `_root_.inv_zero` and `Matrix.inv_zero` match `0⁻¹` even when the
   scalar is a `ℝ`); the robust route is the typed ascription
   `(_root_.inv_zero : (0 : ℝ)⁻¹ = 0)`.
3. **Numeric-literal precedence trap in hypothesis statements:**
   `= -3/4 * -3/4` parses as `((-3/4) * (-3))/4` (`*` and `/` share
   precedence, left-associative), which does not unify with a pin
   stated as a product of two literals — parenthesize every negative
   literal factor: `(-3/4) * (-3/4)`.
4. **`simp` closes `(-(1 : Matrix)) *ᵥ ![1,0] = ![-1,0]` unaided**
   (`Matrix.mulVec`/`dotProduct` unfolding at `Fin 2` evaluates the
   negated identity directly); a trailing `<;> norm_num` is dead and
   trips the `unreachableTactic` linter.
5. **`Fintype.card (Fin 0)` does not reduce for `isEmptyElim`** —
   `IsEmpty (Fin (Fintype.card (Fin 0)))` fails to synthesize; the
   robust vacuity route for sorted-spectrum hypotheses is
   `fun k => by have hk := k.isLt; simp at hk` (`Fintype.card_fin`
   plus `Nat.not_lt_zero`, both simp).

Verification: spike first (`wip/rfences_spike.lean` — the full
36-declaration delivery iterated to zero errors/zero warnings, three
fix rounds all in the recorded trap classes: the `open` line, the
`inv_zero` ambiguity, the literal-precedence trap); `lake env lean` on
the landed module (zero errors, zero warnings); explicit `lake build
Scaffold.QA.OperatorTheory.Resolvent_QA` ✔ (2021/2021); the
36-declaration axiom audit above; **full `lake build` ✔ immediately
followed by `check_build_completeness.py` — 133 source files, 133
fresh artifacts, 0 stale, 0 missing, exit 0** (the build's only
warnings are the pinned Mathlib package's own upstream doc-string
linter notes, present before this delivery); `lint_axioms` exit 0 (4
current axioms, unchanged); `check_refutation_independence` (9-tag
clean — no tags touched); `check_public_reachability` clean (63 repo
modules); `check_citations` ("All axioms have proper citations!");
`check_markdown_links` clean; `check_backlog_freshness` clean;
scoreboard regenerated (5240 → 5274) with the verification row;
map-freshness after the stats sync in both map data tables and SVG
regeneration. The landing verified as a pure insertion (535/0 in
numstat, plus the Purpose-block paragraph). Records updated:
`proposals/README.md` (new Delivered row), README (5274 + the
resolvent row's audit clause), the radar (QA row synced, held 4.5),
`index/map/perturbation.md` (the fences paragraph in the Resolvent
Calculus section), the backlog item-2 falsification-surface note, the
scoreboard, both map data tables + regenerated SVG, the execution
plan, and the activity log. Nothing committed; the prior runs'
uncommitted deliveries preserved.

Remaining scope: the shelf's falsification surface is now complete
(12 fences + 6 screened classes + the recorded non-fenceables). The
method's next targets by the standing survey numbers:
`PerronFrobenius` (7 transitive non-QA consumers, whose QA carries the
degenerate-corner findings but has not had a fresh hypothesis-necessity
pass) and `Exhaustive_QA.lean`'s free-form witness layer (recorded as
a separate audit target by the normalized audit).
