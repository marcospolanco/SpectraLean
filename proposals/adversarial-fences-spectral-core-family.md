# The Spectral-Core Family's Adversarial Fence Audit

**Status:** COMPLETE, Steps 0–4 (Step 0 + Step 1 delivered 2026-09-05 by
run `20260905T085238Z-run-1`, session `ses_f8f51ab63ffejbmt1S6crSM38S`;
Step 2 delivered 2026-09-05 by run `20260905T101522Z-run-1`, session
`ses_f8ef851dcffeKaCpgNq2UVT6Fu`; Step 3 delivered 2026-09-05 by run
`20260905T105038Z-run-1`, session `ses_f8ef851dcffeKaCpgNq2UVT6Fu`;
Step 4 delivered 2026-09-05 by run `20260905T120348Z-run-1`, session
`ses_f8e8be52fffeAmPqtzZrbeEP0Q`; see the delivery records).

## Scope

This run's fresh consumption survey (its actual purpose, per the
prior terminal handoff) found the enumeration method's own gap:
**`Scaffold/Mathlib/GraphTheory/Spectral.lean` — the library's root
shelf, the definitions every family consumes (`deg`, `degreeMatrix`,
`laplacian`, `quadForm`, `rayleigh`, `vol`/`boundary`/`conductance`,
`evals`, `eigvalOf`, `eigvecOf`, `spectralProjector`,
`initialProjector`, `supportGraph`, the padding/interlacing layer) —
carries 46 transitive non-QA consumers (24 direct), roughly triple
the next-largest unaudited shelf, and appears in no prior survey.**
The mechanism: every prior enumeration keyed on shelves with
dedicated same-name QA files (Heat 8, RandomWalk 5, Stationary 4,
IS 3, Directed 3 were ranked among *those*), while `Spectral.lean`'s
QA is scattered across ~10 per-topic files (`Basic_QA`,
`BasicProperties_QA`, `CourantFischer_QA`, `Cuts_QA`,
`Connectivity_QA`, `Projector_QA`, `Variational_QA`, `Interlacing_QA`,
`PotentialSolvability_QA`, `Exhaustive_QA`), none with a fence
section. A targeted grep confirms **zero fence lemmas name any of the
shelf's theorems** — the root's clause surface is entirely unfenced.

The shelf is all-proved (no axiom), so this is a
theorem-instantiation audit (no `-- @refutes` tags), the method's
twenty-third application and its largest single target.

## Step 0: the census (classification summary)

155 declarations; 105 hypothesis-bearing theorems; 214 named clauses.
Classification (the priced program):

1. **The Laplacian algebra / PSD / cut-duality cluster (~16 clauses,
   ~12 fenceable)** — `laplacian_symmetric` (`hA`),
   `laplacian_quadForm` (`hA`), `laplacian_psd` (`hA`, `hnonneg`),
   `laplacian_dotProduct_mulVec` (`hA`),
   `dotProduct_eq_zero_of_laplacian_mulVec_eq_zero` (`hA`),
   `boundary_compl` (`hA`), `conductance_compl` (`hA`),
   `vol_pos_of_pos_deg` (`hd`, `hS`),
   `degreeMatrix_diagonal_nonneg` (`hnonneg`),
   `boundary_nonneg`/`conductance_nonneg`/`cheegerConstant_nonneg`
   (`hnonneg`), `conductance_ge_cheegerConstant` (`hnonneg`, `hS`,
   `hSc`). **Step 1 (this run).**
2. **The connectivity / kernel cluster** — the `hconn` clauses of
   `exists_const_of_laplacian_mulVec_eq_zero`,
   `laplacian_mulVec_eq_zero_iff_exists_const`,
   `laplacian_kernel_eq_span_onesVec`,
   `exists_laplacian_mulVec_eq_of_sum_eq_zero`,
   `exists_laplacian_mulVec_eq_single_sub_single`, and the `hA`/
   `hnonneg` clauses interleaved with them; `Connectivity_QA`'s and
   `PotentialSolvability_QA`'s delivered disconnected witnesses
   reconcile here. **Step 2 (delivered 2026-09-05)** — including the
   `supportGraph`-entanglement classification (every `hA` clause of a
   `supportGraph`-carrying statement is non-fenceable: the dropped
   statement cannot be formed at an asymmetric fixture, the adapter's
   `symm` field deriving from the proof), the P4 settlement of
   `laplacian_mulVec_eq_zero_of_forall_reachable`'s `hnonneg`
   (**refuted — genuinely load-bearing**, correcting this census's own
   earlier "row-sum argument closes without signs" pricing note), and
   the Step-1 cut residuals `conductance_nonneg`/
   `cheegerConstant_nonneg` (`hnonneg`) plus the
   `conductance_ge_cheegerConstant` P4 companion (`hnonneg`
   truth-removable through set-finiteness).
3. **The spectral-theorem interface layer** — the `hM : M.IsSymm`
   cone over `evals`/`eigvalOf`/`eigvecOf`/`spectralProjector`/
   `initialProjector`. Mostly **signature-entangled** (conclusions
   consume `hM` through `evals hM`/`eigvalOf M hM`/`eigvecOf M hM`/
   `spectralProjector M hM` — the resolvent audit's recorded
   non-fenceable mechanism); the fenceable residue is the
   symmetry-free-conclusion minority (`dotProduct_mulVec_comm_of_isSymm`,
   `smul_isSymm`, `eq_of_isSymm_idempotent_of_forall_mulVec_eq`'s
   `hPs`/`hQs`/`hPi`/`hQi`/`h`, the `hcard`/`hne`/`heq`/`hq`-shaped
   side clauses). **Step 3 (delivered 2026-09-05)** — seventeen
   fences: the minority at `dirB` and a four-fixture idempotent
   family sharing the fixed line `{x | x 1 = 0}`; the side clauses at
   the identity/zero matrices through the shelf's own pins
   (`eigvalOf_one`, `eigvecOf_inner`, `dotProduct_eigvecOf` — the
   projector-threshold quartet killed by the *sibling* theorems'
   satisfiable hypotheses, the kernel-orthogonality quintet by a
   Parseval exclusion engine); the `hcard` clauses classified
   entangled (consumed through `⟨index, by omega⟩` Fin arguments);
   and three deferrals recorded (the `hne`/`heq`/congruence-`h`
   clauses gated on a concrete non-identity `eigvalOf`-at-index pin).
4. **The variational / Courant–Fischer cluster** —
   `secondEval_variational`/`_le_rayleigh`/`_smul_of_pos`/`_congr`,
   `evals_min_max`, `evals_le_of_linearIndependent`,
   `lambda2_variational`, `rayleigh_padVec`,
   `eigen_interlacing_principal_submatrix`. Partially fenced
   adjacently (the Alon–Boppana delivery's negative-`c` fence of
   `secondEval_smul_of_pos`'s `hc`; the transfer audit's fences over
   the transfer twins). **Priced as Step 4.**
5. **P4 candidates found by pricing** (to be settled in the later
   steps' records): `laplacian_mulVec_eq_zero_of_forall_reachable`'s
   `hnonneg` (the row-sum argument closes without signs) — **settled
   in Step 2: the pricing call was WRONG, the clause is genuinely
   load-bearing** (refuted at `sfNegEdge`: the edgeless support makes
   the component-constancy hypothesis trivially satisfiable while
   `L *ᵥ e₀ = (-2, 2) ≠ 0` — the negative weights are invisible to
   the support graph yet visible to the Laplacian); and the cut
   residuals' `hnonneg` clauses — **settled in Step 2:
   `conductance_nonneg`/`cheegerConstant_nonneg` are fenceable
   through the negative-min division-rescue fixture `sfSignedCut`
   (`2 / min(-2, 2) = -1 < 0`), while `conductance_ge_cheegerConstant`'s
   `hnonneg` is truth-removable** (the machine-checked companion
   `conductance_ge_cheegerConstant_hypothesis_free`: set-finiteness
   supplies the `BddBelow` the shelf derived from nonnegativity; the
   `hS`/`hSc` clauses stay load-bearing as membership witnesses, and
   remain unfenced-cheaply — a dropped-`hS` fence needs a
   `cheegerConstant > 0` pin, an infimum *lower* bound, the expensive
   direction).

Non-goals: no public statement changes; no axiom contact; QA-only.

## Step 1: the priced fence list (this run)

Kill fixtures: the delivered `dirA` (Fin 3 asymmetric, positive
degrees) and `dirB` (Fin 2 asymmetric nonnegative) from
`Directed_QA`; two new — `sfNegEdge = !![0, -2; -2, 0]]` (symmetric
signed edge: degrees `(-2, -2)`) and `sfStar = !![0, 1, 1; 0, 0, 0;
0, 0, 0]]` (nonnegative asymmetric star into the sink vertex 0 —
`L = diag(2,0,0) − A`, a two-dimensional harmonic kernel); plus the
Fin 2 zero matrix for the `hd` corner.

1. **`laplacian_symmetric`'s `hA`** at `dirA`: `L 0 1 = -3 ≠ -1 =
   L 1 0` — asymmetry survives the `D − ·` subtraction exactly as it
   survived `1 − ·` in the random-walk audit.
2. **`laplacian_quadForm`'s `hA`** at `dirA`, `x = e₀`: the quadratic
   form is `4` against the symmetrized double-sum's `6/2 = 3` — the
   `1/2` pairing genuinely consumes symmetry.
3. **`laplacian_psd`'s `hA`** at `dirB`, `x = (1, 2)`: `quadForm =
   -2 < 0` with `hnonneg` genuine (`dirB` is nonnegative) — the
   in/out-degree imbalance is a negative mode of the asymmetric
   walk structure.
4. **`laplacian_psd`'s `hnonneg`** at `sfNegEdge`, `x = (1, -1)`:
   `quadForm = -8 < 0` with `hA` genuine (symmetric) — the negative
   edge's alternating mode.
5. **`laplacian_dotProduct_mulVec`'s `hA`** at `dirB`, `w = e₀`, `f =
   e₁`: the two pairings separate `-4 ≠ -1` — self-adjointness is
   exactly symmetry.
6. **`dotProduct_eq_zero_of_laplacian_mulVec_eq_zero`'s `hA`** at
   `sfStar`: `L *ᵥ (1, 2, 0) = 0` (genuine kernel vector — the star's
   two-dimensional harmonic space) while `(1,2,0) ⬝ᵥ (L *ᵥ e₀) = 2 ≠
   0` — the kernel-certificate shape needs the self-adjoint route.
7. **`boundary_compl`'s `hA`** at `dirB`, `S = {0}`: `4 ≠ 1` — the
   two directions of the cut carry different weight.
8. **`conductance_compl`'s `hA`** at `dirB`, `S = {0}`: `4 ≠ 1`
   through the pinned volumes — cut canonicalization needs symmetry.
9. **`vol_pos_of_pos_deg`'s `hd`** at the zero matrix, `S = {0}`:
   `vol = 0` with `hS` genuine — positive volume needs positive
   degrees.
10. **`vol_pos_of_pos_deg`'s `hS`** at `dirA`, `S = ∅`: `vol = 0`
    with `hd` genuine (the delivered `dirA_deg_pos`) — nonemptiness
    is not decorative.
11. **`degreeMatrix_diagonal_nonneg`'s `hnonneg`** at `sfNegEdge`:
    `degreeMatrix 0 0 = deg 0 = -2 < 0` — signed input makes the
    degree diagonal negative.
12. **`boundary_nonneg`'s `hnonneg`** at `sfNegEdge`, `S = {0}`:
    `boundary = -2 < 0` — signed cut weight.

Non-fenceables in Step 1's scope, with mechanism: none — every
clause of the cluster's theorems has a state-able dropped statement
(`supportGraph` does not appear in this cluster; the entanglement
class starts at the connectivity cluster, recorded for Step 2).

## Delivery vehicle

A **new dedicated `Scaffold/QA/SpectralGraph/Spectral_QA.lean`** —
the root shelf's own QA home, which also closes the survey-method
gap structurally (future same-name-keyed enumerations will see it).
Imports `Directed_QA` for the delivered `dirA`/`dirB` fixtures and
their pins (the established cross-QA reuse pattern).

## Acceptance bar

- Every Step-1 clause carries a hypothesis-form fence, each killed
  at a named fixture with the dropped clause's genuine failure
  pinned (isolation) and every kept clause genuine.
- `#print axioms` on every new declaration reads exactly `propext,
  Classical.choice, Quot.sound`; no `-- @refutes` tags.
- QA-only, pure insertion (new file); the full verification ladder
  after the spike; records ladder updated.
- The census table (Steps 2–4 priced) recorded here for the
  successor runs.

## Step-0 + Step-1 delivery record

DELIVERED at the full priced Step-1 scope — QA-only, a NEW dedicated
module `Scaffold/QA/SpectralGraph/Spectral_QA.lean` (615 lines, pure
addition; the root shelf's first own QA home, closing the
survey-method gap structurally): twelve hypothesis-form fences
(`laplacian_symmetric_hA_fence_QA`, `laplacian_quadForm_hA_fence_QA`,
`laplacian_psd_hA_fence_QA`, `laplacian_psd_hnonneg_fence_QA`,
`laplacian_dotProduct_mulVec_hA_fence_QA`,
`dotProduct_eq_zero_of_laplacian_mulVec_eq_zero_hA_fence_QA`,
`boundary_compl_hA_fence_QA`, `conductance_compl_hA_fence_QA`,
`vol_pos_of_pos_deg_hd_fence_QA`, `vol_pos_of_pos_deg_hS_fence_QA`,
`degreeMatrix_diagonal_nonneg_hnonneg_fence_QA`,
`boundary_nonneg_hnonneg_fence_QA`), the isolation companions
(`dirB_not_isSymm`, `dirB_nonneg`, `sfNegEdge_isSymm` +
`sfNegEdge_not_nonneg`, `sfStar_not_isSymm`, `sfZeroAdj_not_hd`; the
delivered `dirA_not_isSymm` and `dirA_deg_pos` reused), and the
mechanism pins throughout (fourteen vector value pins; the
Laplacian-entry pins of every fixture via
`degreeMatrix_diagonal`/`degreeMatrix_off_diagonal`; the
complement-sum pins via `Finset.sum_add_sum_compl`; the volume,
conductance, and Finset-complement pins). Three new fixtures:
`sfNegEdge` (the symmetric signed edge), `sfStar` (the nonnegative
asymmetric star with the two-dimensional harmonic kernel
`{f | 2 f 0 = f 1 + f 2}`), `sfZeroAdj` (the Fin 2 zero matrix); the
delivered `dirA`/`dirB` reused through the `Directed_QA` import. 96
declarations (93 theorems + 3 fixture `def`s); QA 5760 → 5853 (+93 by
the generator metric). Zero axiom contact (`#print axioms` via
`wip/skfences_axcheck.lean` on all 96 — every one exactly `propext,
Classical.choice, Quot.sound`; no `-- @refutes` tags; the 12-tag
independence check unchanged and clean).

Technique findings recorded for future audits:

1. **Zero-multiplication pruning.** A quadratic form at a standard
   basis vector `e₀` only ever needs the `(0,0)` entry pinned: every
   other Laplacian entry is multiplied by a zero component, and
   `norm_num` kills `x * 0` and `0 * x` without knowing `x`. The
   same pruning halves the pin inventory for pairing/dot-product
   witnesses (only the entries multiplied by nonzero components of
   both vectors need pins). This is the Fin-2/Fin-3 generalization
   of the zero-row observation the stationary audit recorded.
2. **The `vecHead`/`vecTail` residue recurs under `funext` on
   matrix-vector products** (the stationary audit's trap class,
   in a new position): `funext i; fin_cases i` on `M *ᵥ v = 0`
   leaves `⬝ᵥ`-shaped eta-literals that named-entry pins cannot
   match. The robust route: prove per-entry `have`s at clean
   literal-index statements `(M *ᵥ v) 0 = 0` first, then assemble
   with `funext`/`fin_cases`/`exact` (defeq absorbs the eta).
3. **`by decide` closes concrete Finset complements on `Fin 2`**
   (`({0} : Finset (Fin 2))ᶜ = {1}`) — no `ext`/`fin_cases` needed;
   the decidability instances synthesize.
4. **The complement-sum idiom scales unchanged from Fin 3 to Fin 2**
   (`Finset.sum_add_sum_compl` + `Finset.sum_singleton` + the full
   row-sum pin + `linarith`) — the Cuts_QA pattern is
   fixture-size-independent.

## Verification

Spike first (`wip/skfences_spike.lean` — the full 96-declaration
delivery, iterated to zero errors/zero warnings in two fix rounds,
both in recorded trap classes: findings 2 above); `lake env lean` on
the landed module (exit 0, no output); explicit `lake build
Scaffold.QA.SpectralGraph.Spectral_QA` ✔ (2194/2194, the only
warnings the pinned Mathlib's own upstream linter notes in
`Stationary.lean`, pre-existing); the 96-declaration axiom audit
above; **full `lake build` ✔ immediately followed by
`check_build_completeness.py` — 134 source files, 134 fresh
artifacts, 0 stale, 0 missing, exit 0 (the new module included)**;
`lint_axioms` exit 0 (4 current axioms, unchanged);
`check_refutation_independence` (12-tag clean — no tags touched);
`check_public_reachability` clean (63 public modules — the new QA
file correctly unreachable from the umbrella); `check_citations`
("All axioms have proper citations!"); `check_markdown_links` clean;
`check_backlog_freshness` clean (reviewed-date current at September
5); scoreboard regenerated (**5853/4/0**) with the verification row;
map-freshness exit 0 after the 5760 → 5853 stats sync in both map
data tables and SVG regeneration (49 stations, no status change —
none owed: this proposal is not a map station's cited source).
Records updated: this file (Status + delivery record), the census
table above, `proposals/README.md` (new Delivered row), README
(5853), the radar (QA row synced to 5853/69 modules, held 4.5),
`index/map/spectral_graph.md` (the audit paragraph in the SGT-center
section), the backlog item-2 falsification-surface note, the
scoreboard verification row, both map data tables + regenerated SVG,
the QA file's own header, the execution plan, and the activity log.
Nothing committed; prior runs' uncommitted deliveries preserved.

## Step-2 delivery record

DELIVERED at the full priced Step-2 scope — QA-only, a new
`AdversarialFencesStep2` section of `Spectral_QA.lean` (a pure ~680-line
insertion riding two new QA imports, `Connectivity_QA` and
`PotentialSolvability_QA`, for the reconciliation fences): eighteen
hypothesis-form fences, the hypothesis-free P4 companion, and the
`supportGraph`-entanglement classification. New fixtures: `sfSignedPath`
(the symmetric signed Fin 3 path — support the connected path `0—2—1`,
degrees `(1,1,4)`, `L = !![1,1,-2;1,1,-2;-2,-2,4]]`, kernel
`{f | f 0 + f 1 = 2 f 2}` two-dimensional, containing the nonconstant
`![1,-1,0]` — every `hnonneg` fence keeps `hconn` genuine here) and
`sfSignedCut` (the negative-min division-rescue fixture); reused:
`sfNegEdge`/`sfStar` (Step 1), `connDiscAdj` + its delivered lemmas,
and `PotentialSolvability_QA`'s delivered unsolvability witness. 79
declarations (77 theorems + 2 fixture `def`s); QA 5853 → 5930 (+77 by
the generator metric). Zero axiom contact (`#print axioms` via
`wip/skfences2_axcheck.lean` on all 79 — every one exactly `propext,
Classical.choice, Quot.sound`; no `-- @refutes` tags; the 12-tag
independence check unchanged and clean).

The fences, each a first witness for its clause: **the `hconn`
reconciliations** (5 fences) at `connDiscAdj` — the existence, iff,
span, solvability-hinge, and unit-demand forms, each proof consuming
the delivered pre-discipline witnesses (`connDisc_indicator_in_kernel_QA`,
`connDisc_indicator_not_const_QA`, `connDisc_not_connected_QA`,
`disc_demand_sum_eq_zero_QA`, `disc_cross_demand_unsolvable_QA`);
**the `hnonneg` clauses** (7 fences) at `sfSignedPath` with `hconn`
kept genuine — the pos-weight engine and its walk propagation (`f 0 =
1 ≠ 0 = f 2` across the genuine weight-2 edge `0—2`), the existence/
iff/span kernel forms (the nonconstant kernel vector `![1,-1,0]`
survives connectivity), and the solvability hinge plus its unit-demand
specialization (the zero-sum demand `e 0 − e 1` pairs `2 ≠ 0` against
the kernel vector through the shelf's own certificate
`dotProduct_eq_zero_of_laplacian_mulVec_eq_zero` — load-bearing on
it); **the P4 settlement** (2 fences) at `sfNegEdge` —
`laplacian_mulVec_eq_zero_of_forall_reachable`'s `hnonneg` and the
component-iff's `hnonneg`, both killed through the edgeless-support
mechanism; **the pos-weight `hA` fence** at `sfStar` (kept `hnonneg`
genuine: `L *ᵥ (1,2,0) = 0` through the two-dimensional harmonic
kernel while `0 < A 0 1 = 1` is genuine and `f 0 = 1 ≠ 2 = f 1`);
**the cut residuals** (2 fences) at `sfSignedCut` —
`conductance_nonneg`'s and `cheegerConstant_nonneg`'s `hnonneg`
(boundary `2` over volume `-2`, conductance `-1 < 0`). Plus the P4
companion `conductance_ge_cheegerConstant_hypothesis_free`.

Technique findings recorded for future audits:

1. **The negative-min division rescue.** A division-shaped
   conclusion whose numerator and denominator both go negative at the
   obvious signed fixture is *rescued* there (`(-2)/(-2) = 1 ≥ 0`);
   the kill needs a fixture separating the signs (positive numerator,
   negative denominator). Generalizes: any `f/g`-shaped nonnegativity
   clause should be priced for sign separation, not just sign
   presence.
2. **Set-finiteness as the hypothesis-free `BddBelow`.** When a shelf
   proof derives `BddBelow` from a sign hypothesis but the set is
   finite for structural reasons (finitely many cuts of a finite
   type), `Set.Finite.bddBelow` + `csInf_le` discharges the same
   statement with the sign clause dropped — the P4 companion pattern
   at the *proof-route* level rather than the statement level.
3. **Kept-but-inert binders.** Dropping the only clause that consumed
   a kept binder (here `hconn` consuming `hA` through `supportGraph`)
   leaves the binder propositionally inert in the fence statement;
   the Resolvent audit's `(_hM : M.IsSymm)` convention suppresses the
   linter while keeping the theorem-minus-one-clause shape honest.
4. **The `csInf_le` signature trap.** This pin's `csInf_le` demands
   `BddBelow` (not the `s.Nonempty → b ∈ s` order of later Mathlib);
   probe before routing an infimum bound.

## Step-2 verification

Spike first (`wip/skfences2_spike.lean` — the full 79-declaration
delivery, iterated to zero errors/zero warnings in three fix rounds,
all in recorded trap classes: the eta-literal branch trap in
`fin_cases`d reachability goals — cured by standalone `have`s at clean
literal statements consumed by `exact`'s defeq; the `rw`-list
beta-redex residue on `Finset.sum_insert` chains — cured by
`simp only` for the singleton splits; and the `csInf_le` signature
trap above — plus one genuine logic bug the spike caught: the
connectedness proof's nil-walk branch initially sat in the `v = 1`
position); `lake env lean` on the landed module (exit 0, no output);
explicit `lake build Scaffold.QA.SpectralGraph.Spectral_QA` ✔
(2196 tasks); the 79-declaration axiom audit above; **full `lake
build` ✔ immediately followed by `check_build_completeness.py` — 134
source files, 134 fresh artifacts, 0 stale, 0 missing, exit 0**;
`lint_axioms` exit 0 (4 current axioms, unchanged);
`check_refutation_independence` (12-tag clean — no tags touched);
`check_public_reachability` clean (63 public modules — the QA file
correctly unreachable); `check_citations` ("All axioms have proper
citations!"); `check_markdown_links` clean; `check_backlog_freshness`
clean; scoreboard regenerated (**5930/4/0**) with the verification
row; map-freshness exit 0 after the 5853 → 5930 stats sync in both
map data tables and SVG regeneration (49 stations, no status change —
none owed: this proposal is not a map station's cited source).
Records updated: this file (Status + census settlements + this
record), `proposals/README.md` (the Delivered row extended),
README (5930), the radar (QA row synced, held 4.5),
`index/map/spectral_graph.md` (the Step-2 paragraph in the SGT-center
section), the backlog item-2 falsification-surface note, the
scoreboard verification row, both map data tables + regenerated SVG,
the QA file's own header, the execution plan, and the activity log.
Nothing committed; prior runs' uncommitted deliveries preserved.

## Step-3 delivery record

DELIVERED at the full priced Step-3 scope — QA-only, a new
`AdversarialFencesStep3` section of `Spectral_QA.lean` (a pure ~620-line
insertion): seventeen hypothesis-form fences plus the
signature-entanglement classification and three recorded deferrals.
New fixtures: `sfOneM` (the Fin 2 identity), `sfAsymIdem =
!![1,1;0,0]]` (asymmetric idempotent, fixed line `{x | x 1 = 0}`),
`sfProjE0 = diag(1,0)`, `sfProjE0two = diag(1,2)` (symmetric
non-idempotent, same fixed line), `sfProjE1 = diag(0,1)`; reused:
`dirB` + its delivered entries/asymmetry, `sfZeroAdj` (Step 1). 60
declarations (55 theorems + 5 fixture `def`s); QA 5930 → 5985 (+55 by
the generator metric). Zero axiom contact (`#print axioms` via
`wip/skfences3_axcheck.lean` on all 60 — every one exactly `propext,
Classical.choice, Quot.sound`; no `-- @refutes` tags; the 12-tag
independence check unchanged and clean).

The fences, each a first witness for its clause: **the
symmetry-free-conclusion minority** — `dotProduct_mulVec_comm_of_isSymm`'s
`hM` at `dirB` (`w = e₀`, `f = e₁`: the pairings separate `4 ≠ 1` —
coordinate self-adjointness at the raw matrix, the general-matrix
companion of Step 1's Laplacian fence); `smul_isSymm`'s `hM` at
`dirB`, `c = 1` (`1 • M = M` stays asymmetric — scaling preserves the
cone exactly, it does not widen it); and all five clauses of
`eq_of_isSymm_idempotent_of_forall_mulVec_eq` at the idempotent
family: `hPs`/`hQs` (the asymmetric idempotent and the symmetric
projector share the fixed line, every kept clause genuine, `1 ≠ 0` at
entry (0,1)), `hPi`/`hQi` (the symmetric non-idempotent `diag(1,2)`
shares the fixed line through `2·x1 = x1 → x1 = 0`, `2 ≠ 0` at entry
(1,1)), `h` (two orthogonal projectors). **The side clauses at the
identity/zero matrices** — `eigvalOf_le_of_quadForm_nonpos`'s `hq`
(the identity's uniform spectrum `eigvalOf_one` makes the dropped
statement demand `1 ≤ 0`); the projector-threshold quartet
(`spectralProjector_eq_zero`'s and `_eq_one`'s `h`, and both
`_mulVec_eigvecOf` specializations' `h`), each killed by the sibling
theorem's own satisfiable hypothesis at `c = 1`/`0` — the projector
pins to `1 ≠ 0` or `0 ≠ 1`, the eigenvector is nonzero by
orthonormality (`eigvecOf_inner`); and the kernel-orthogonality
quintet — `eigvecOf_ortho_of_mulVec_eq_zero`'s `hker` (at the
identity with `w` an eigenvector: the unit self-pairing demanded to
vanish) and `hne` (at the zero matrix, where every vector is a
kernel vector — the kept `hker` genuine at an eigenvector witness),
plus the onesVec trio's clauses through the **Parseval exclusion
engine** `sfOnesVec_not_all_orthogonal` (the eigenbasis resolves
`onesVec` whose self-pairing is `2 ≠ 0` — the engine is load-bearing
on the shelf's own `dotProduct_eigvecOf`, and its three consumers
keep their respective remaining clauses genuine).

Classifications recorded: every `hM` clause whose conclusion consumes
a spectral object's argument is signature-entangled (the resolvent
mechanism); every `hcard` clause is consumed through
`⟨Fintype.card V - 1, by omega⟩`-style Fin index arguments — the same
mechanism one level down. Deferrals: `evals_one_le_max_of_ne`'s `hne`
and `exists_ne_eigvalOf_of_evals_head_eq`'s `heq` need a concrete
non-identity `eigvalOf`-at-index pin (the identity's uniform spectrum
cannot kill — `1 ≤ max 1 1` holds); the congruence lemmas' `h`
(`evals_congr`, `secondEval_congr`, `initialProjector_congr`) need
`evals` pins at two distinct symmetric matrices (the shelf pins only
the identity; `Cheeger_QA`'s secondEval pins lack the index-level
transfer engine). Non-fenceables: `eigvalOf_one`/`evals_one`'s `hOne`
(provable outright — decorative; the dropped statement is a theorem).

Technique findings recorded for future audits:

1. **Sibling-theorem kills.** A threshold clause on a
   spectral-object-carrying statement (entangled `hM`) can still be
   fenced when the *sibling* theorem's hypothesis is satisfiable at
   the same instantiation — the pinned value (here `1 ≠ 0` via
   `spectralProjector_eq_one` at the identity) refutes the dropped
   statement without any concrete spectral computation.
2. **The identity/zero pair as universal spectral fixtures.** The
   shelf's own pins (`eigvalOf_one`, `eigvecOf_inner`) turn the
   identity into a fully pinned spectrum, and the zero matrix makes
   every kernel-vector hypothesis trivial — between them most
   side clauses of the interface layer fall without unfolding any
   spectral definition.
3. **Parseval exclusion (`not_forall` route).** "Not every
   eigenvector is orthogonal to `w`" needs only the shelf's
   resolution identity `dotProduct_eigvecOf` plus `w ⬝ᵥ w ≠ 0`;
   `not_forall.1` extracts the witness index. Consumed three times
   below at three different kept-clause sets.
4. **Fixed-line families for uniqueness lemmas.** Five clauses of a
   fixed-space-determination lemma fall to a family of 2×2
   idempotents sharing the fixed line `{x | x 1 = 0}`, each member
   failing exactly one structural clause — the shared-fixed-space
   hypothesis stays genuine throughout, isolating the dropped clause.

## Step-3 verification

Spike first (`wip/skfences3_spike.lean` — the full 60-declaration
delivery, iterated to zero errors/zero warnings in one fix round:
the dropped-`hM` statements of the two raw-matrix theorems carry no
symmetry premise — the conclusion never consumes it — and the first
draft wrongly kept it, a shape error the elaborator caught as a type
mismatch; the `fix_iff` entry evaluations route through `norm_num
[def, h]`; the Parseval engine's `¬∀` unfolds to an arrow, so the
witness index comes through `not_forall.1`); `lake env lean` on the
landed module (exit 0, no output); explicit `lake build
Scaffold.QA.SpectralGraph.Spectral_QA` ✔ (2196 tasks); the
60-declaration axiom audit above; **full `lake build` ✔ immediately
followed by `check_build_completeness.py` — 134 source files, 134
fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` exit 0
(4 current axioms, unchanged); `check_refutation_independence`
(12-tag clean — no tags touched); `check_public_reachability` clean
(63 public modules); `check_citations` ("All axioms have proper
citations!"); `check_markdown_links` clean; `check_backlog_freshness`
clean; scoreboard regenerated (**5985/4/0**) with the verification
row; map-freshness exit 0 after the 5930 → 5985 stats sync in both
map data tables and SVG regeneration (49 stations, no status change —
none owed). Records updated: this file (Status + census + this
record), `proposals/README.md` (the Delivered row extended), README
(5985), the radar (QA row synced, held 4.5), `index/map/
spectral_graph.md` (the Step-3 paragraph in the SGT-center section),
the backlog item-2 falsification-surface note, the scoreboard
verification row, both map data tables + regenerated SVG, the QA
file's header, the execution plan, and the activity log. Nothing
committed; prior runs' uncommitted deliveries preserved.

## Step-4 delivery record

DELIVERED at the full priced Step-4 scope — QA-only, a new
`AdversarialFencesStep4` section of `Spectral_QA.lean` (a pure ~530-line
insertion riding one new QA import, `Variational_QA`): **nineteen
hypothesis-form fences** plus the `rayleigh_padVec` hypothesis-free P4
companion, the adjacent-coverage citations, and the classifications. 42
declarations (41 public theorems + 1 private two-point pin, audited
transitively); QA 5985 → 6026 (+41 by the generator metric). Zero axiom
contact (`#print axioms` via `wip/skfences4_axcheck.lean` on all 41
public declarations — every one exactly `propext, Classical.choice,
Quot.sound`; no `-- @refutes` tags — theorem instantiations of an
all-proved shelf, nothing admitted consumed; the 12-tag independence
check unchanged and clean).

The fences, each a first witness for its clause: **`secondEval_variational`'s
`hpsd`** at `laplacian negAdj` (symmetric, `onesVec` genuinely in the
kernel through `laplacian_ones_in_kernel`): `λ₂ = 0` (pinned through
`lambda2_eq_secondEval` from the on-file `negAdj_lambda2_eq_zero`)
while every admissible test vector has Rayleigh quotient `-2`
(`negAdj_rayleigh_of_orth`) — the dropped statement reads `0 = -2`;
**its `hker`** at `sfProjE0 = diag(1,0)` (PSD genuinely): `λ₂ = 1`
against the constraint set's infimum `1/2` (a new parametric
rayleigh-of-orthogonal pin at `sfProjE0`); **`secondEval_le_rayleigh`'s
`hpsd`/`hker`/`hx0`/`hxorth`** (`0 ≤ -2` at the negative Laplacian;
`1 ≤ 1/2` at `sfProjE0` with `hpsd` genuine; the junk quotient
`2 ≤ 0` at `x = 0` on `L(K₂)`; and at `x = onesVec`, whose kernel
quotient `0 < 2 = λ₂(L(K₂))`); **the congruence pair's `h` clauses —
Step 3's recorded deferral resolved for both members**
(`secondEval_congr`: `λ₂(L(K₂)) = 2 ≠ 0 = λ₂(L(negAdj))`, both pins
derived through `lambda2_eq_secondEval` from the two on-file
`lambda2` pins — no new spectral computation needed;
`evals_congr`: the identity's uniform spectrum (`evals_one`) against
`sfProjE0`'s bottom entry `0`, from a new both-entries sorted-spectrum
pin `sf4_sfProjE0_spectrum` — trace `1`, determinant `0`, sortedness);
**`evals_le_of_linearIndependent`'s `hk1`/`hgi`/`hbnd`** (at `k = 0`
with the span bound vacuously genuine and the empty family independent;
at `k = 2` with the dependent all-zero family whose span bound is
genuinely `0 ≤ 0`; at `k = 1` with the independent singleton `![e₀]`
and the dropped bound genuinely failing — all three conclusions
demand `evals ⟨_⟩ = 1 ≤ 0` at the identity); **`lambda2_variational`'s
`hnonneg` — reconciled**: the 2026-08-18 pre-discipline refutation
`old_lambda2_variational_refuted_QA` (delivered with the axiom
retirement) is exactly the dropped statement's counterexample; the
wrapper consumes it; **the `_of_ker` twins' seven clauses**
(`secondEval_le_rayleigh_of_ker`'s `hwne`/`hker`/`hx0`/`hxorth`:
at `w = 0` the kernel and orthogonality clauses are trivially genuine
while `e₁`'s quotient `0 < 1`; at `w = onesVec` (nonzero genuinely,
not in `sfProjE0`'s kernel) the alternating quotient `1/2 < 1`; at
`x = 0` the junk quotient; at `x = e₁` the self-pairing `1 ≠ 0`;
`secondEval_variational_of_ker`'s `hpsd`/`hwne`/`hker`: the negative
Laplacian at `w = onesVec` (`0 = inf ≤ -2`); `w = 0` making the
constraint set all of the nonzero vectors (`e₁` attains `0`, so
`1 = inf ≤ 0`); and `w = onesVec` outside the kernel with the
alternating line's infimum `1/2`). **The P4 companion**
`rayleigh_padVec_hy_free`: the nonzero guard is decorative — at
`y = 0` both sides are the junk zero, so the hypothesis-free
statement is proved outright.

Adjacent coverage cited, not re-imported (the Alon–Boppana `hc`
precedent): `secondEval_smul_of_pos`'s `hc` is fenced by
`k2_secondEval_smul_neg_fence_QA`; `secondEval_le_rayleigh_of_ker`'s
`hpsd` is fenced as `icFence_psd_fence` in `IrregularCheeger_QA.lean` —
whose shelf docstring cited it under the **nonexistent** name
`icvQ_psd_fence`; repaired in this delivery to the real name.

Classifications: `hM`/`hA` clauses of every conclusion consuming the
symmetry proof (`secondEval M hM hcard`, `lambda2 A hA hcard`,
`evals hM k`) are signature-entangled (Step 3's mechanism);
`hcard`/`hkc`/`hn` are formation-entangled (consumed through `Fin`
index arguments — a `k > card` instantiation cannot even form the
conclusion's index); `secondEval_smul_of_pos`'s `hpsd`/`hker` are
truth-removable-not-fenceable: positive scaling commutes with
sorting, so the dropped statements hold at every fixture — matching
the theorem's own docstring note that the hypothesis-free
generalization is true but needs eigenvalue-multiset scaling
machinery the pinned Mathlib lacks; `evals_min_max` carries only the
entangled `hM`; `eigen_interlacing_principal_submatrix`'s `hn` is
formation-entangled.

Defects found by this step, recorded: (1) the shelf docstring's
nonexistent `icvQ_psd_fence` citation — repaired; (2) **the
`Cheeger_QA`/`PotentialSolvability_QA` `edgeAdj` collision**: both
QA modules define `SpectralGraphTheory.QA.edgeAdj` with a `_cstage2`
staging auxiliary, so the two cannot be co-imported (`import
Scaffold.QA.SpectralGraph.Cheeger_QA` fails with "environment already
contains 'SpectralGraphTheory.QA.edgeAdj._cstage2'" when
`PotentialSolvability_QA` is already imported). Latent until now —
no file had ever imported both. It blocked the planned
`IrregularCheeger_QA` reconciliation import (the section cites that
fence instead). The lattice repair — renaming the less-referenced
`edgeAdj` and rebuilding its consumers — is priced as a small
follow-up.

**Defect (2) RESOLVED the same day** (run `20260905T130214Z-run-2`,
session `ses_f8e8be52fffeAmPqtzZrbeEP0Q`): the repair went further
than the original pricing — the survey found FOUR QA modules defining
`SpectralGraphTheory.QA.edgeAdj` (`RandomWalk_QA`, `Cheeger_QA`,
`Heat_QA`, `PotentialSolvability_QA`), every pair non-co-importable,
so the less-referenced rename would have left the lattice broken
elsewhere. All four fixtures were renamed file-uniquely
(`rwEdgeAdj`/`cheegerEdgeAdj`/`heatEdgeAdj`/`psEdgeAdj`) across the
ten referencing files (1,129 prefix replacements, resolution domains
mapped empirically from the import graph — each referencing file
resolved to exactly one definer, since no file had ever co-imported
two). One genuine hazard the repair surfaced and fixed: the SHELF
also exports a public `edgeAdj (i j : V) (w : ℝ)` edge-indicator
constructor (`GraphTheory.EdgePerturbation`), and
`Derived/EdgePerturbation_QA.lean` references BOTH it (unqualified,
16 refs) and Cheeger_QA's fixture (fully qualified,
`SpectralGraphTheory.QA.edgeAdj*`, 3 refs) — the blanket rename
corrupted the shelf references and the build caught it; the file was
restored to reference the shelf name unqualified and the fixture by
its new qualified name. The renamed modules are outside the default
build target's closure, so the full `lake build` alone left ten
stale artifacts — `check_build_completeness.py` caught it (its
calibrated remediation path exercised as designed) and the explicit
module builds closed it (134/134/0/0). The follow-through landed
immediately: `Spectral_QA.lean` now imports `IrregularCheeger_QA`
(the previously-failing co-import, verified in
`wip/edgelattice_spike.lean`), and the `hpsd` clause of
`secondEval_le_rayleigh_of_ker` is fenced IN Step 4's section as
`secondEval_le_rayleigh_of_ker_hpsd_fence_QA` — a wrapper consuming
`icFence_psd_fence` (all five of the theorem's clauses now fenced
in-discipline; QA 6026 → 6027; the wrapper's `#print axioms` exactly
`propext, Classical.choice, Quot.sound`).

Technique findings recorded for future audits:

1. **Deferral resolution by pin transfer.** A deferral gated on "pins
   at two distinct matrices" can fall to existing pins in *other*
   spellings: `secondEval_congr`'s `h` needed no new spectral
   computation — the two on-file `lambda2` pins (K₂ and the negative
   fixture) transfer through `lambda2_eq_secondEval` (an `rfl`
   theorem), yielding two `secondEval` pins at distinct symmetric
   matrices for free. Before pricing a deferral as hard, check the
   neighboring API for `rfl`-transferable pins.
2. **Both-entries two-point pins.** A sorted two-point list with
   nonnegative sum and a zero product has BOTH entries determined
   (bottom `0`, top the sum) — one lemma (`sf4_two_point_both`) pins a
   whole 2×2 spectrum, which is what the `evals_congr` deferral
   needed (a full-spectrum pin at a second matrix, not just the top).
3. **Statement-position `by omega` cannot see `Fintype.card`.** In a
   fence statement, `evals hM ⟨0, by omega⟩` fails ("no usable
   constraints") — the statement's tactic block has no context and
   omega does not reduce `Fintype.card (Fin 2)`. Use `by simp`
   (`Fintype.card_fin` is simp) for statement-position Fin indices;
   `by omega` only in proof position where length/card facts are
   hypotheses.
4. **Junk-clause interplay fences need PSD-independent bounds.** The
   `hwne`-drop fence's constraint set is unbounded below in general,
   so its `BddBelow` must come from a genuine route (here PSD
   nonnegativity of the fixture, `rayleigh_nonneg_psd_QA`) — the
   shelf proof's own BddBelow derivation consumed the dropped clause.

## Step-4 verification

Spike first (`wip/skfences4_spike.lean` — the full 42-declaration
delivery, iterated to zero errors/zero warnings over three fix
rounds, all in recorded trap classes: statement-position omega
(finding 3), `linearIndependent_iff'`'s Finset signature (use
`Fintype.linearIndependent_iff`), and binder-renaming that broke
kept binders' types referencing the renamed variable (an `_w` rename
orphaned `w` in `_hker`'s type — kept binders' types count as uses);
plus the `edgeAdj` collision discovery itself, which reshaped the
adjacent-coverage strategy); `lake env lean` on the landed module
(exit 0, no output); explicit `lake build
Scaffold.QA.SpectralGraph.Spectral_QA` ✔ (2197 tasks); the
41-public-declaration axiom audit above (the private two-point pin
audited transitively through `sf4_sfProjE0_spectrum`); **full
`lake build` ✔ immediately followed by `check_build_completeness.py`
— 134 source files, 134 fresh artifacts, 0 stale, 0 missing, exit 0**
(the public `Spectral.lean` docstring repair included in the build);
`lint_axioms` exit 0 (4 current axioms, unchanged);
`check_refutation_independence` (12-tag clean — no tags touched);
`check_public_reachability` clean (63 public modules);
`check_citations` ("All axioms have proper citations!");
`check_markdown_links` clean (re-run after the records edits);
`check_backlog_freshness` clean (reviewed-date current at September
5); scoreboard regenerated (**6026/4/0**) with the verification row;
map-freshness exit 0 after the 5985 → 6026 stats sync in both map
data tables and SVG regeneration (49 stations, no status change —
none owed: this proposal is not a map station's cited source).
Records updated: this file (Status COMPLETE + this record),
`proposals/README.md` (the Delivered row extended to Steps 0–4),
README (6026), the radar (QA row synced, held 4.5),
`index/map/spectral_graph.md` (the Step-4 paragraph in the
SGT-center section), the backlog item-2 falsification-surface note
(Step 4 delivered, program complete, both congruence deferrals
resolved, the `edgeAdj` defect recorded), the scoreboard
verification row, both map data tables + regenerated SVG, the QA
file's header, the shelf docstring repair, this plan, and the
activity log. Nothing committed; prior runs' uncommitted deliveries
preserved.
