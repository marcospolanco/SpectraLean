# Proposal: Spectral Sparsification via Leverage-Score Sampling — Reopening the Blocked Phase B

**Status:** Step 0 **DELIVERED 2026-08-27 — verdict: tractable** (the
survey record below). **Step 1, Slice 1 (the sampling-space module)
DELIVERED 2026-08-27** — `Scaffold/Mathlib/Probability/BernoulliProduct.lean`
+ `Scaffold/QA/Probability/BernoulliProduct_QA.lean`, pure hard crust,
zero new axioms (the delivery record below). **Step 1, Slice 2 (the
deterministic SS algebra) DELIVERED 2026-08-27** —
`Scaffold/Mathlib/GraphTheory/Sparsification.lean` +
`Scaffold/QA/SpectralGraph/Sparsification_QA.lean`, pure hard crust,
zero new axioms (the delivery record below). **Step 1, Slice 3 (the
assembly + QA) DELIVERED 2026-08-27 — Step 1 COMPLETE, and with it the
program's strategic aim: `matrix_bernstein`'s first real theorem
consumer** — `Scaffold/Derived/SparsificationTail.lean` (the two
axiom-conditional tail theorems) + the `Sparsification.lean` Slice-3
deterministic sections +
`Scaffold/QA/Derived/SparsificationTail_QA.lean` (the delivery record
below; the tails are conditional on `matrix_bernstein` and reported as
such — never described as foundationally proved). **The two priced
follow-ons DELIVERED 2026-08-28** (run `20260828T183001Z-run-1`, the
follow-on delivery record below): the multiplicative `(1±ε)`
refinement `sparsification_multiplicative_tail` and the
`q ~ log n/ε²` budget corollary `sparsification_multiplicative_budget`
— the field-standard sparsifier sentence on the delivered base, zero
new axioms. This document authorizes no axiom admissions, commits, or
external publication on its own.

## The correction this proposal is built on

[`spectral-graph-sparsification.md`](spectral-graph-sparsification.md)
recorded Phase B as **blocked**, stating: *"no matrix-Chernoff result
exists in this repository"* and *"`Scaffold/Mathlib/Probability/
Concentration/MatrixChernoff.lean` does not exist; do not treat it as a
citable dependency for Phase B."* That check was path-literal and missed
the neighboring file: **`Scaffold/Mathlib/Probability/Concentration/
Matrix/Bernstein.lean` already exists**, is already imported by the
umbrella (`Scaffold.lean:38`), and is already one of the 9 counted
axioms — `matrix_bernstein`, Tropp's matrix Bernstein inequality
(spectral-norm tail bound for sums of independent centered bounded
Hermitian matrices; source: Tropp 2012, Theorem 1.1). It has exactly the
shape a Chernoff-family concentration result for sparsification needs.

This is also, independently, the strategic reason to do this now: of the
9 admitted axioms, **7 have zero theorem consumers** — `matrix_bernstein`,
`matrix_hoeffding`, `hoeffding_inequality`, `hoeffding_lemma`,
`bernstein_inequality`, `bernstein_bounded_variance`, `hoeffding_empirical`
are referenced only inside their own defining file and a single thin QA
file that instantiates each at the zero sequence. Only `perron_frobenius`
(now 2 theorem consumers, this session) and `matrix_azuma_hoeffding` (used
inside the event-stream frontier) have real downstream proof pressure.
An axiom with no consumer has never had its exact hypothesis shape
exercised by anything that would break if a clause were misstated — the
zero-sequence QA checks the statement parses and holds vacuously, nothing
more. `matrix_bernstein` is the single best target: it is the most
strategically valuable of the seven (a real, previously-recorded external
want) and the sparsification route below consumes its bound structurally,
not just its existence.

## Assessed from

`Scaffold/Mathlib/GraphTheory/Foster.lean` (`effectiveResistance`,
`leverageScore`, `sum_leverageScore_eq_two` — the leverage scores already
proved to sum to `2`, i.e. `n - 1` in the unordered-pair convention,
exactly the sampling-budget identity Spielman–Srivastava-style
sparsification needs), `Scaffold/Mathlib/Probability/Concentration/
Matrix/Bernstein.lean` (the axiom's exact hypothesis clauses — Hermitian,
independent, centered, uniformly spectral-norm-bounded summands), and
`spectral-graph-sparsification.md`'s own Phase B sketch (kept for
reference, not binding — its scope decisions were made under the false
premise that no matrix concentration axiom existed, so this proposal
re-derives the shape rather than inheriting that sketch verbatim).

## The obligation this discharges

Not a bug fix — a **corrected scoping decision**. The prior proposal's
Phase B is explicitly reopened here as its own document, per that
proposal's own instruction ("Phase B needs its own scoping proposal once
the matrix-Chernoff blocker... is resolved"). The blocker is resolved:
the axiom exists. This proposal's Step 0 is to verify that resolution is
real (confirm `matrix_bernstein`'s exact clause set actually supports the
sampling argument below) before any Lean is written.

## The statement (draft shape — subject to Step 0 correction)

For a connected weighted graph with symmetric nonnegative conductances,
sample each edge `e` independently with probability `p_e = min(1, q ·
leverageScore A e)` for a budget parameter `q`, reweighting sampled edges
by `1/p_e` (the standard unbiased Rademacher-style sparsifier
construction) to form a random sparse graph `Ã`. The target theorem: for
`q` large enough (order `log n / ε²`, the classical rate), the sampled
Laplacian's quadratic form uniformly approximates the original,

```
∀ x, (1 - ε) * quadForm (laplacian A) x ≤ quadForm (laplacian Ã) x
                                        ≤ (1 + ε) * quadForm (laplacian A) x
```

with probability at least `1 - δ`, via `matrix_bernstein` applied to the
centered per-edge sampling matrices (each term a rank-one Laplacian
contribution minus its expectation, bounded in spectral norm by the
leverage-score normalization).

**Step 0 must check, before this is trusted:** (1) whether
`matrix_bernstein`'s centering hypothesis (`∫ X i = 0`) and boundedness
hypothesis (`‖X i ω‖ ≤ R`) actually close for the per-edge sampling
matrices at the natural `R` — this is the classical argument's crux step
and the exact place a Chernoff-shaped bound can fail to transfer; (2)
whether `leverageScore`'s existing normalization (`sum_leverageScore_eq_2`)
supplies the sampling-probability budget in the form the tail bound
needs, or whether a rescaling lemma is a prerequisite; (3) whether the
random sparsifier as a random matrix-valued function needs measurability
infrastructure not yet in the shelf (`StronglyMeasurable` on a
finite-support random construction — likely cheap, but unverified).
"Not tractable at reasonable cost" is a valid recorded Step 0 outcome,
per the survey precedent (approximate spectral projection Step 0).

## QA obligations (draft — refine after Step 0)

1. A small positive fixture (a 4–6 vertex weighted graph with known
   leverage scores, e.g. a cycle or a two-triangle bridge) where the
   sparsifier is sampled at a fixed budget and the quadratic-form
   preservation is checked numerically alongside the proved probability
   bound, so the statement's constants are pinned against a concrete
   case, not asserted in the abstract.
2. A boundary/degenerate witness: `q` too small (below the leverage-score
   floor) should make the bound vacuous or the hypothesis unsatisfiable —
   refuted in proved form, not asserted.
3. The disconnected-graph fence, consistent with Foster's own scope note
   (effective resistance is graph-connectivity-dependent).

## Acceptance bar

- Step 0 delivers a written verdict (tractable at what cost, or
  iceboxed with the specific obstruction named) before any shelf Lean
  is written.
- If Step 1 proceeds: zero new axioms (the whole point is consuming
  `matrix_bernstein`, not adding a new one); public theorems report
  `matrix_bernstein` in `#print axioms` honestly, never described as
  unconditionally proved.
- `spectral-graph-sparsification.md` is updated to record this
  proposal as Phase B's actual successor and to correct its "does not
  exist" claim about matrix concentration machinery.
- `docs/7_SGT_RADAR.md` axis 6 (Electrical) and axis 7
  (Algorithms/Randomness) are the natural re-score targets if delivered.

## Companion

[Grow the Crust Through Electrical Structure](electrical-structure-crust.md),
[Spectral Graph Sparsification (Phase A, delivered)](spectral-graph-sparsification.md),
`docs/6_SGT_BACKLOG.md`, `docs/7_SGT_RADAR.md` axes 6 & 7.

---

## Step-0 delivery record (2026-08-27, run `20260827T123751Z-run-1`)

**Verdict: tractable.** Every clause of `matrix_bernstein` has a
discharge route at the classical Spielman–Srivastava design, and the
riskiest plumbing — which no shelf file and no pinned-Mathlib lemma
supplied — is now *proved* on the survey spike `wip/ss0_spike.lean`
(316 lines, `lake env lean` zero errors / zero warnings; a throwaway
verdict artifact, not shelf code). The proposal's three named checks:

**(1) Centering and boundedness at the natural `R` — close, with two
interface findings.** The clause set read from source:
`h_meas : StronglyMeasurable` (references only the codomain *topology*
— the L2OpNorm scoped instance, not any σ-algebra, so no BorelSpace
bridge is needed), `h_indep : pairwise IndepFun`, `h_herm`,
`h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0` (a Bochner integral at the
L2OpNorm normed-space instance — consumers must `open scoped
Matrix.L2OpNorm` for instance coherence), `h_bound : ∀ i ω, ‖X i ω‖ ≤ R`
(**unconditional in `ω`** — see finding A), and the variance statistic
`Σ = ∑ i, ∫ ω, X i ω * X i ω ∂μ` in exactly the classical form.

- *Finding A (the material one): the uniform `∀ ω` in `h_bound` forces a
  saturation guard into the summand design.* At `p_e = min(1, q ℓ_e) =
  1` the Bernoulli space still contains `δ_e = 0` outcomes, where the
  raw `Z_e = (δ_e/p_e − 1)(v_e ⊗ v_e)` has norm `ℓ_e`, not `≤ 1/q` —
  the bound would fail *pointwise*, not merely a.s. The Step-1 family
  must therefore build the guard in (`X_e := if p_e = 1 then 0 else
  (δ_e/p_e − 1) • (v_e ⊗ v_e)`; a identically-zero summand is centered,
  bounded, Hermitian, and independent trivially) or index only the
  unsaturated edges. Recorded as a statement-shape decision Step 1 must
  make explicitly.
- *Finding B:* the axiom indexes summands by `Fin n`, so the edge family
  needs an enumeration transport (`Fintype.equivFin`-style). Cheap, but
  it is plumbing the draft statement shape does not yet have.
- The centering arithmetic is spike-proved end to end at the scalar
  codomain (`integral_delta`: `∫ δ_e ∂μ = p e`, through
  `PMF.integral_eq_sum`, the one-coordinate marginal, and the
  `≠ ⊤`-guarded `← ENNReal.toReal_sum`); the matrix codomain follows by
  `Finset.sum_smul`-style linearity. `∫ X_e = 0` then needs `p_e ≠ 0` —
  true for unsaturated edges at `ℓ_e > 0` (positive weight, connected,
  `effectiveResistance` positive — Step 1 must consume this).
- The boundedness *value* is the classical `R = 1/q` at `p_e = q ℓ_e`;
  its deterministic input is the rank-one bound `‖v ⊗ v‖ ≤ ‖v‖²`, for
  which the shelf has two plausible routes (`l2OpNorm_le_of_abs_eigvalOf_le`
  + the eigen-action identity `(v ⊗ v)x = (v ⬝ x) v`, or the
  BandDavisKahan `l2OpNorm_mulVec_le`). Priced as Step-1 work; not
  spiked.

**(2) The leverage normalization — closes.** `Foster.lean` already
proves `(∑ i, ∑ j, A i j * effectiveResistance A i j) / 2 = card V − 1`
— *exactly* the unordered-pair sampling-budget identity (total
leverage `n − 1`) that `p_e = q ℓ_e` consumes. The shelf's
`leverageScore` is the `(n−1)`-normalized ordered-pair convention
(`sum_leverageScore_eq_two` : `∑ᵢⱼ ℓ̃ = 2`); a thin rescaling lemma
(divide by `n − 1`, or read Foster's identity directly) is the only
prerequisite — priced trivial. Connectivity is load-bearing
(`effectiveResistance` is junk off connected components, documented at
the definition), which is QA obligation 3's fence.

**(3) The measurability/independence infrastructure — did not exist
anywhere; the spike builds it.** The shelf's only concrete measure-level
work is constant-sequence QA; the event-stream consumers take their
hypotheses abstractly. Searched: the pinned Mathlib's
`Independence/Basic` has only π-system machinery, `Kernel.lean` no
`Measure.pi` route — no lemma supplies coordinate independence on a
product measure. The spike's construction (all proved, green): the
space `Ω := ι → Bool` at the product σ-algebra
(`@MeasurableSpace.pi` over `Bool`'s canonical one); the product PMF
`bernPMF` via `PMF.ofFinset` with total mass by the ∑-∏ swap
(`Finset.sum_prod_piFinset`); the one- and two-coordinate marginals
`sum_coord_mul` / `sum_coord2_mul` (through the `coordG1`/`coordG2`
if-family defs — see technique notes); cylinder measures `toMeasure_cyl`;
**`indepFun_coord`** — pairwise `IndepFun` of the coordinate
projections, the exact shape `h_indep` needs; and `integral_delta`
above. The matrix-codomain layer has confirmed source-verified routes
but was not spiked: `StronglyMeasurable` for finite-range matrix
functions via `SimpleFunc.ofFinite` + `SimpleFunc.stronglyMeasurable`
(which requires only `[TopologicalSpace β]` — no BorelSpace, which
matters because the shelf's `Basic.lean` matrix σ-algebra is a
hand-rolled pi instance, not a registered BorelSpace); `Measurable` at
that instance via `measurable_pi_iff` entrywise; the transfer
`IndepFun.comp` with `measurable_of_bool` (every function out of `Bool`
is measurable — `Bool.instMeasurableSingletonClass` + `Set.toFinite`).

**The three-slice decomposition Step 1+ should follow:**

1. **Slice 1 — the sampling-space module** (shelf Lean; the spike is its
   blueprint): promote `bernPMF`, the marginals, `indepFun_coord`, the
   matrix-layer transfer, and the centering integrals into a focused
   module (e.g. `Probability/BernoulliProduct.lean`) with QA. This is
   deliberately its own slice because a *second* Active-table row needs
   the same object: the empirical-stationary-distribution proposal's
   Step 0 asks exactly for an i.i.d.-sampling measure space over
   repeated finite walks.
2. **Slice 2 — the deterministic SS algebra**: the rank-one norm bound,
   the guarded sampling matrices, the variance PSD bound `‖Σ‖ ≤ 1/q`,
   and the identity `∑_e v_e ⊗ v_e = Π_{im L}` (the eigbasis machinery
   already in `Foster.lean`'s orbit).
3. **Slice 3 — assembly + QA**: apply `matrix_bernstein` at `t = ε`,
   transfer the norm event to the quadratic-form statement through the
   `L^{†/2}` pullback, and discharge this proposal's three QA
   obligations.

**Technique findings for Step 1 (the spike's iteration record):** bind
`p` explicitly in every theorem signature — a free `p` gets auto-bound
and silently breaks section-instance inclusion (the one *stuck
`Fintype ?m`* class of failures); `rw` cannot rewrite under a `∑`
binder — restructure as `Finset.sum_congr` tactic blocks or
pre-stated haves (`simp only [lemma]` goes under binders; `rw` does
not); higher-order-pattern unification fails when a lemma argument is a
lambda (`sum_coord2_mul ... _ _` leaves metavars) — pass `F`/`G`
explicitly or make the family an atom `def` (`coordG1`/`coordG2` exist
for exactly this); the ∑-split lemma is `Finset.mul_prod_erase` (`f a *
∏_{s.erase a} = ∏_s`), *not* `Finset.prod_erase` (that is the
erase-a-value-1-point lemma); `PMF.toMeasure_apply` takes `(p) (s)
(hs)` — the PMF and the set are explicit section variables;
`ENNReal.toReal_sum` carries a `∀ i ∈ s, f i ≠ ⊤` side goal (supply via
`ENNReal.prod_lt_top` + `ENNReal.ofReal_lt_top`); `Set.Finite.
measurableSet` with `Set.toFinite` is the every-subset-of-`Bool` route;
`stronglyMeasurable_iff_measurable` needs a `BorelSpace` codomain and
is *not* the route at the matrix σ-algebra — `SimpleFunc.ofFinite` is.

**Residual risk:** the matrix-codomain layer and the deterministic
Slice-2 bounds are confirmed-route but untried in Lean; Finding A's
guard decision shapes the Step-1 statement and must be made there. The
`q`-budget constants (`R = 1/q`, `‖Σ‖ ≤ 1/q`) are classical values the
survey asserts from the SS argument, not spike-verified arithmetic —
Slice 2 owns them.

---

## Step-1 Slice-1 delivery record (2026-08-27, run `20260827T142209Z-run-1`)

**DELIVERED — pure hard crust, zero new axioms** (count stays 10;
`#print axioms` via `wip/ss1_axcheck.lean` on all 42 audited
declarations — 18 public module + 24 public QA: exactly `propext,
Classical.choice, Quot.sound`, every one; zero contact with any
admitted axiom). QA 2585 → **2609** (+24, the new
`Scaffold/QA/Probability/BernoulliProduct_QA.lean`; the new
`Probability` QA domain first appears in the scoreboard).

**Delivered** in the new
`Scaffold/Mathlib/Probability/BernoulliProduct.lean` (namespace
`Scaffold.Mathlib.Probability.BernoulliProduct`; minimal imports —
the two PMF files, `Independence.Basic`, `SetIntegral`,
`CStarAlgebra.Matrix`, and the shelf's `Concentration/Matrix/Basic`
for the matrix σ-algebra; umbrella import added):

- the spike's blueprint promoted: `bern`/`jointMass`/`bernPMF` (with
  `sum_bern_eq_one`, `sum_jointMass_eq_one`, `bernPMF_apply`,
  `jointMass_ne_top`), the marginals `sum_coord_mul`/
  `sum_coord2_mul` (the `coordG1`/`coordG2` atom defs kept private),
  `toMeasure_cyl`, `indepFun_coord`, `integral_delta`,
  `measurable_coord`;
- **the Step-0 residual risk retired — the matrix-codomain layer,
  Lean-untried until this run, now proved**:
  `stronglyMeasurable_coord_matrix` (the `h_meas` clause at the
  L2OpNorm topology — Mathlib's `StronglyMeasurable.of_finite`, the
  topology-only route; the hand-rolled `SimpleFunc.ofFinite` plan was
  unnecessary because Mathlib already ships the finite-domain lemma),
  `measurable_coord_matrix` (the same at the shelf's matrix pi
  σ-algebra, by composition with `measurable_of_finite` out of
  `Bool`), `indepFun_coord_matrix` (the `IndepFun.comp` transfer —
  the `h_indep` clause at the matrix codomain), and the centering
  integrals `integral_coord_smul` (`∫ (δ_e : ℝ) • M ∂μ = p e • M`,
  through `integral_smul_const` joined to `integral_delta`) and
  `integral_coord_center_smul` (`∫ ((δ_e / p e) − 1) • M ∂μ = 0` at
  `p e ≠ 0` — the exact `h_mean` clause shape for the unguarded
  rank-one summand).

**QA (+24, the `Fin 2 → Bool` four-atom fixture at `p = ![1/2, 1/3]`
with the atom enumeration as the independent raw route):** the four
joint-mass values raw; **total mass `1` by two independent routes**
(the ∑-∏ theorem vs raw four-atom enumeration, no swap machinery);
the marginal pin; three cylinder-measure pins (`1/3`, `2/3`, `1/2`);
**independence pinned numerically through `indepFun_coord`** (the
intersection measure splits as `1/2 · 2/3 = 1/3`, joined to the two
cylinder pins — a wrong joint mass breaks the product form);
**`∫ δ_1 = 1/3` by two routes** (the theorem vs `PMF.integral_eq_sum`
raw enumeration); the matrix-layer interfaces instantiated at a
concrete `!![1,2;3,4]` family; the matrix centering pins
(`∫ (δ_0) • M = (1/2) • M`; the centered-affine zero at `p 1 ≠ 0`);
and **two fences** — the `[0,1]` bounds load-bearing for the mass
normalization (`p = ![2]` on `Fin 1` sums to `2 ≠ 1`, the clamp
visible), and **the `p e ≠ 0` centering hypothesis refuted at the
junk value** (`p = ![0]`: the "centered" integrand evaluates through
`0 / 0 = 0` to the constant `−M`, so the integral is `−M ≠ 0` —
the conclusion fails, not merely the hypothesis).

**Technique findings (the spike's iteration record, for Slice 2):**
`ENNReal.ofReal_mul` takes **one** side condition (`ofReal_add` takes
two — the mismatch behind every "function expected at
`ENNReal.ofReal_mul ?m`" failure); `ofReal`-equality goals close by
`congr 1; norm_num` (no norm_num ENNReal extension exists) and the
merge lemmas must be applied in **rw position with the pattern
present** (term-mode application leaves metavariable-typed side
goals); the matrix `CompleteSpace` resolves at the L2OpNorm scoped
instance (probe-verified before use — `integral_smul_const` needs
it); `Integral.of_finite` discharges every integrability side goal on
this space; `MeasurableSpace.pi` is already a global Mathlib instance
(the spike's `local instance` was shadowing — dropped in the shelf
module); `omit [inst] in` must precede the docstring (a docstring
demands the declaration keyword immediately after); no pi
`DecidableEq` instance exists in the pin — atom-disequality side
conditions need `congrFun`-at-an-index witnesses (`fin_cases x <;>
simp [h]` under a `funext`); matrix-literal `(1/2) • M` statements
need the scalar type ascribed `((1:ℝ)/2)` or the smul elaborates at
`ℕ`; `p12 0 = 1/2` is `rfl` but `rwa` still fails on
instance-sensitive integrals — `simpa only [p12, Matrix.cons_val_zero]`
is the robust join.

**Verification:** spike first (`wip/ss1_spike.lean` — the full module
plus the QA section, both sides iterated to zero errors/zero warnings
before any shelf Lean); `lake env lean` zero errors/zero warnings on
the module and the QA file; explicit `lake build` targets ✔
(2042/2042 module, 2043/2043 QA); `#print axioms` — the standard
three only, all 42; **full `lake build` ✔ (2398/2399, "Build
completed successfully") immediately followed by
`check_build_completeness.py` — 115/115 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**2609/10/0** —
this regeneration also repaired the generated-metrics block, which
the uncommitted prior deliveries had left at the committed
2549/2026-08-26 while their verification rows were swept: the
working-tree count is now truthful at 2609 = the Step-5 run's true
2585 + this delivery's 24).

**Remaining risk:** Slices 2–3 (the deterministic SS algebra and the
assembly) are next; Finding A's saturation guard is now a Slice-2
statement decision with the centering clause shape it must fit already
delivered (`integral_coord_center_smul`); Finding B's `Fin n` edge
transport belongs to Slice 3's assembly; the `R = 1/q` / `‖Σ‖ ≤ 1/q`
constants remain classical values owned by Slice 2.

---

## Step-1 Slice-2 delivery record (2026-08-27, run `20260827T161958Z-run-1`)

**DELIVERED — pure hard crust, zero new axioms** (count stays 10;
`#print axioms` via `wip/ss2_axcheck.lean` on all 72 audited
declarations — 48 public module + 24 public QA: exactly `propext,
Classical.choice, Quot.sound`, every one; zero contact with any
admitted axiom). QA 2609 → **2632** (+23, the new
`Scaffold/QA/SpectralGraph/Sparsification_QA.lean`).

**Delivered** in the new
`Scaffold/Mathlib/GraphTheory/Sparsification.lean` (namespace
`SpectralGraphTheory`; imports Foster, Resolvent, BernoulliProduct;
umbrella import added):

- **the rank-one algebra**: `rankOne` (the pinned Mathlib has no
  `outerProduct` at plain-function generality), its action
  `rankOne_mulVec`, quadratic form `rankOne_quadForm`, idempotence
  `rankOne_mul_self`, symmetry, `rankOne_neg`, the squared
  Cauchy–Schwarz `dotProduct_sq_le` (through the Euclidean inner
  product — the slice's only C–S), and **the norm bound
  `l2OpNorm_rankOne_le`** (`‖v vᵀ‖ ≤ v ⬝ᵥ v`, per-eigenvalue Rayleigh
  quotients at unit eigenvectors via `l2OpNorm_le_of_abs_eigvalOf_le`);
- **the polarized bilinear Dirichlet identity**
  `laplacian_dirichlet_bilinear` (`∑∑ A ΔxΔy = 2 xᵀLy` — polarization
  of `laplacian_quadForm` at `x+y`, the cross-symmetry through raw
  double sums);
- **the eigen-coordinate edge-vector family** `ssEdgeVec`
  (`√(w/2)·(v_k u − v_k v)/√λ_k`, zero-eigenvalue entries dropped — the
  Foster spectral machinery's own representation; no matrix
  pseudoinverse or square root anywhere), with `ssEdgeVec_self`,
  `ssEdgeVec_swap`, **`ssEdgeVec_dotProduct_self`** (`‖v_e‖² =
  w_e R_eff/2` — the ordered-pair half-share, through
  `effectiveResistance_eq_sum_eigbasis` verbatim), and **the Foster
  budget corollary** `sum_ssEdgeVec_dotProduct_self` (`∑_{u,v} ‖v_e‖² =
  card V − 1`);
- **the image projector** `imageProjector` (the eigen-coordinate form
  of `Π_{im L}`) with `Π² = Π`, `‖Π‖ ≤ 1`, the Rayleigh domination
  `quadForm Π x ≤ x ⬝ x`, **the trace identity
  `trace Π = card V − 1`** (through `card_filter_eigvalOf_laplacian_eq_zero`),
  and **the projector identity `sum_rankOne_ssEdgeVec`**
  (`∑_{u,v} v_e v_eᵀ = Π` *exactly* — the `1/√2` halving absorbing the
  ordered-pair double count, entrywise through the bilinear Dirichlet
  identity at two eigenvectors plus the orthonormality `δ_kl`);
- **the Bernoulli second moment** `integral_bern_center_sq`
  (`E[(δ/p − 1)²] = (1−p)/p`), linearized through the delivered first
  moment (`δ² = δ` pointwise) — no measure-level enumeration;
- **the Finding-A-guarded sampling design** on the Slice-1 space
  (`ssProb := min 1 (q‖v_e‖²)`, `ssDelta`, `ssSummand` with the
  saturation guard, `ssMeasure` = the delivered `bernPMF` at
  `ι = V × V`), and the three `matrix_bernstein` clause lemmas at the
  classical constants, now **proved rather than asserted** (retiring
  the Step-0 record's named residual risk):
  **`integral_ssSummand_eq_zero`** (`∫ X_e = 0` with no connectivity
  or nonnegativity hypothesis — zero-leverage pairs are absorbed by
  their zero rank-one factor; saturated pairs by the guard; the rest
  close through `integral_coord_center_smul` verbatim),
  **`ssSummand_l2OpNorm_le`** (`‖X_e ω‖ ≤ 1/q` for *every* outcome —
  the uniformity Finding A demanded), **`integral_ssSummand_mul_self`**
  + **`sum_integral_ssSummand_mul_self`** (`∑_e ∫ X_e X_e = Σ`, the
  axiom's exact statistic shape, through the rank-one idempotence), and
  **the headline `l2OpNorm_ssVariance_le`** (`‖Σ‖ ≤ 1/q`: coefficients
  `c_e ≤ 1/q` with the junk value at zero-leverage pairs landing
  exactly right, the residual rank-one sum *exactly* the projector, and
  the projector's Rayleigh form dominated by `x ⬝ x`; eigenvalue route
  — every eigenvector's Rayleigh quotient lies in `[0, 1/q]`).

**QA (+23, the `K₂` fixture):** the leverage budget by two independent
routes (the Foster corollary `∑ ‖v_e‖² = 1` vs the raw four-ordered-pair
enumeration `1/2 + 1/2 + 0 + 0`); the rank-one norm identity pinned
two-sided at a concrete vector (`‖![1,2]![1,2]ᵀ‖ = 5`, the lower side
through the eigenvector witness `v` itself — the same mechanism that
pins the `K₂` edge vector's norm `1/2` below); the projector trace
`= 1`; the centering and bound instances at `q = 1`; the exact variance
coefficient `c_(0,1) = 1/2` at `p = min 1 (1·1/2) = 1/2`; and three
proved fences — **the Finding-A fence** (the *unguarded* saturated
summand's norm `1/2` refutes the bound `≤ 1/q = 1/4` at the missed
outcome: the guard is load-bearing, not decorative), **the `q = 0`
fence** (every probability junk-zero through `min 1 0 = 0`, and the
conclusion refuted at `1/0 = 0`), and the saturation-guard instance
(the summand identically zero at `q = 4`).

**Technique findings (the spike's iteration record, for Slice 3):**
proof arguments are match-relevant — `eigvalOf (laplacian A) hL` with a
local `hL` does NOT match the def-spelled
`eigvalOf (laplacian A) (laplacian_symmetric A hA)` that `simp only
[ssSummand/ssEdgeVec]`-unfolding produces (proof irrelevance is not
reducible defeq for simp/rw matching) — spell the def form everywhere a
lemma's output must meet a def's unfolding; `λ` and `Σ` are reserved or
invalid identifier characters (`hλpos`/`hΣ` break parsing — use `hμpos`/
`hSum`); `rw [← h]` with `h : √x * √x = x` rewrites every `x` in the
goal (including *inside* other `√x`) — reorganize numerators by an
explicit ring-fact first and rewrite `h` *forward*; `Finset.sum_div`
exists in this pin but `Finset.mul_sum` must be instantiated explicitly
to avoid HO-pattern metavar failures at `∑ (c * f i)`; `norm_num` on
matrix-smul goals misbehaves (it can turn a coefficient computation
into a bogus `R = 0`) — keep norm_num on scalar goals and close smul
identities by explicit coefficient rewrites; `•` binds tighter than
`*` (`a * b • M` parses as `a * (b • M)`) — parenthesize
`((a * b) • M)` in statements; `integral_smul_const` (not
`integral_const_mul`) is the matrix-integral workhorse;
`le_div_iff` is deprecated for `le_div_iff₀`; pair literals in QA
statements need `(e : Fin 2 × Fin 2)` ascription beside a numeral `q`
argument or the elements default to `ℕ`.

**Verification:** spike first (`wip/ss2_spike.lean` — the full module
plus the QA section, iterated to zero errors/zero warnings before any
shelf Lean; the catch record is the technique-findings paragraph);
`lake env lean` zero errors/zero warnings on both new shelf files;
explicit `lake build` targets ✔ (2159/2159 module, 2160/2160 QA);
`#print axioms` via `wip/ss2_axcheck.lean` — the standard three only,
all 72; **full `lake build` ✔ (2399/2400, "Build completed
successfully") immediately followed by `check_build_completeness.py` —
117/117 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no
issues), `check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**2632/10/0**).

**Remaining risk:** Slice 3 (assembly + the proposal's three QA
obligations) remains: Finding B's `Fin n` edge-enumeration transport
(cheap, `Fintype.equivFin`-style), the norm-event → quadratic-form
transfer through the eigen-coordinate pullback (the statement decision
of how `xᵀL̃x` relates to the eigen-coordinate quadratic form — the
conjugation `y = eigenbasisᵀ x`), and the `q`-budget error-shape
calculus. One QA residual recorded: the exact matrix value
`ssVariance K₂ 1 = rankOne v_(0,1)` (hence `‖Σ‖ = 1/2` exactly) was
attempted and set aside — the four-term ordered-pair sum computation
fights elaboration quirks disproportionate to its QA value; the scalar
coefficient pin `c_(0,1) = 1/2` + the two-sided rank-one norm identity
carry the same falsification content.

---

## Step-1 Slice-3 delivery record (2026-08-27, run `20260827T193452Z-run-1`)

**DELIVERED — Step 1 COMPLETE; the program's strategic aim met:
`matrix_bernstein` now has a real theorem consumer** (the axiom count
stays 10 — the point was consuming one, not adding; `#print axioms` via
`wip/ss3_axcheck.lean` on all 43 audited declarations: the 14 new
module declarations and 25 of the 27 QA declarations read exactly
`propext, Classical.choice, Quot.sound`; the **two Derived tails and
their two QA interface pins read `propext, Classical.choice,
Quot.sound, matrix_bernstein`** — the conditional structure reported
honestly, never disguised as unconditional). QA 2632 → **2659** (+27,
the new `Scaffold/QA/Derived/SparsificationTail_QA.lean`, the Derived
QA domain's third file).

**Delivered, deterministic half** — `GraphTheory/Sparsification.lean`'s
two new sections (no new imports; the file's "adds no axioms" character
preserved):

- the quadratic-form transfer helpers `quadForm_add` /
  `quadForm_sub_matrix` (the name `quadForm_sub` was already taken by
  AlonBoppana's vector-pair expansion — the umbrella caught the clash)
  / `quadForm_smul`;
- the action bound **`l2OpNorm_mulVec_dotProduct_le`**
  (`(M x) ⬝ᵥ (M x) ≤ ‖M‖² (x ⬝ᵥ x)`) — a local dot-product route to the
  C*-norm spine (`toEuclideanCLM` + `cstar_norm_def`, the same two
  rewrites as BandDavisKahan's `l2OpNorm_mulVec_le`, kept local to
  avoid the heavy perturbation import);
- **the norm→form transfer `abs_quadForm_le_of_l2OpNorm_le`**
  (`‖M‖ ≤ t → |xᵀMx| ≤ t (x ⬝ᵥ x)`, symmetry-free: Cauchy–Schwarz on
  the action form `x ⬝ᵥ (M *ᵥ x)`) — the eigen-coordinate pullback
  step;
- the sampled design: **`ssWeight`** (`1` at saturated pairs — the
  deterministic guard: a pair sampled with probability one is not
  random — and `δ_e/p_e` otherwise; junk `0` at zero-leverage pairs,
  whose rank-one factor is zero anyway) and **`ssSampled`**
  (`∑_e g_e(ω) • (v_e v_eᵀ)`), with
- **the exact deviation identity `ssSampled_sub_imageProjector`**:
  `ssSampled ω − Π_{im L} = ∑_e X_e ω` *pointwise in ω* — the
  statement decision that makes the norm-event transfer exact at every
  outcome (no null-event caveats, the guard mirrored into the sampled
  object), per-pair `(g_e − 1) • (v_e v_eᵀ) = X_e ω`;
- the Bool-valued summand shape **`ssSummandBool`** with
  `ssSummand e ω = F_e (ω e)` by `rfl`, closing
  **`stronglyMeasurable_ssSummand`** (the `h_meas` clause) and
  **`indepFun_ssSummand`** (the `h_indep` clause) through the Slice-1
  transfer layer verbatim (`stronglyMeasurable_coord_matrix`,
  `indepFun_coord_matrix`).

**Delivered, axiom-conditional half** — the new
`Scaffold/Derived/SparsificationTail.lean` (umbrella import added;
the three-layer architecture's Derived home, following the
`eventStreamTail` precedent of proved-steps-plus-axiom-backed-theorem):

- **`sparsification_norm_tail`**: on the product-Bernoulli sampling
  space at budget `q > 0`, `μ {‖S(ω) − Π_{im L}‖ ≥ t} ≤
  2 d exp(−t²/(2/q + 2t/(3q)))` — the classical Spielman–Srivastava
  deviation tail at the *proved* constants (Slice 2's `R = 1/q` and
  `‖Σ‖ ≤ 1/q` substituted into the axiom's exact exponential, the
  substitution's monotonicity proved: `t = 0` collapses, `t > 0` runs
  the positive-denominator `div_le_div_iff₀` route). Finding B's
  `Fin n` transport is `Fintype.equivFin` + `Equiv.sum_comp` — the
  sum, the event set, and the variance statistic all reconciled along
  it, with beta-redex spellings mirrored where the axiom's
  instantiation leaves them. **No connectivity hypothesis** — centering
  is connectivity-free by the Slice-2 design, so the tail holds on
  disconnected input too (fenced in QA on both sides).
- **`sparsification_quadForm_tail`**: the same bound for the failure
  set of the uniform additive quadratic-form approximation
  `|xᵀ S(ω) x − xᵀ Π x| ≤ t (x ⬝ᵥ x)` for every vector — the
  eigen-coordinate pullback (set inclusion into the norm event +
  `measure_mono`; the nonzero-vector case by the transfer lemma, the
  zero vector excluded by `0 < 0` falsity).

**QA (+27, the K₂ fixture plus the zero-graph fixture):** the deviation
identity pinned at the all-true outcome with every piece visible (the
four-ordered-pair evaluation `0 + (v_e v_eᵀ) + (v_e v_eᵀ) + 0` — the
guard's junk-zero at loop pairs, the reweighting `δ/p = 2`, the swap
`rankOne (−v) = rankOne v`); **the deviation norm `= 1 = 1/q` exactly**
(tight both sides — the lower side through the eigenvector witness, so
the classical bound's constant is *attained* at a real outcome);
`quadForm_imageProjector_eq`'s first consumer (`qF(Π) v = 1/2` by the
four-pair evaluation); `qF(S) v = 1` (deviation on top of projector);
**the transfer lemma tight with equality** (`|qF(S)v − qF(Π)v| =
t·(v⬝v) = 1/2`, plus the same instance through the theorem); both tails'
interface instances; the nonempty-event witness (the all-true outcome
is in the `t = 1` event); and the two-sided connectivity content on the
zero graph — **the disconnected fence** (leverage budget `0 ≠ card − 1`
on two components: connectivity load-bearing exactly at the Foster
budget, per its own scope note) beside **the connectivity-free
positive** (the deviation identically zero there — the tail theorem
needs no connectivity anywhere).

**Technique findings (the spike's iteration record, `wip/ss3_spike.lean`):**
`Equiv.sum_comp`'s direction is `∑ i, g (e i) = ∑ i, g i` (no `.symm`
when transporting from `Fin n` to the product); instantiating the axiom
with `X := fun i ω => …` leaves *beta-redexes* in its conclusion —
`(fun i ω => …) i ω` — so any `rw` against `hmain` must mirror that
spelling (state the reindexed lemmas in the redex form, proved from the
reduced forms by defeq `fun ω => hsum ω`); `Matrix.dotProduct_sub` vs
`sub_smul`/`smul_sub` naming (the goal-side application determines which);
`Π` is a reserved identifier character like `λ`/`Σ` (`hΠ` breaks parsing
— use `hProj`); `Real.exp_le_exp` is an iff in this pin (`.mpr`);
`nlinarith` cannot square an inequality without the nonneg facts as
explicit hypotheses — give it `(t - m) * (t + m) ≥ 0` certificates or
`calc` chains; `mul_le_mul`'s argument order defeats `apply … <;>`
(plain `nlinarith [ht, norm_nonneg M]` is more robust for `m² ≤ t²`);
private file-local lemmas (`isSymm_finset_sum`) are invisible to a
sibling file — the Derived module's `ssSampled_isSymm` lives in
Sparsification.lean for exactly that reason; and the stale-olean trap
recurred (the Derived file saw the pre-edit module until the explicit
target rebuild).

**Verification:** spike first (`wip/ss3_spike.lean` — the module
additions, the Derived tails, and the QA in one file, iterated to zero
errors/zero warnings before any shelf Lean); `lake env lean` zero
errors/zero warnings on all three changed/new files; explicit `lake
build` targets ✔ (2159/2159 module — the name-clash rename rebuilt,
2165/2165 derived, 2166/2166 QA); `#print axioms` via
`wip/ss3_axcheck.lean` — 39 of 43 at the standard three, exactly the
two Derived tails and their two QA interface pins carrying
`matrix_bernstein`; **full `lake build` ✔ (2400/2401, "Build completed
successfully") immediately followed by `check_build_completeness.py` —
119/119 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no
issues), `check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**2659/10/0**). One build repair mid-run: the umbrella
caught `SpectralGraphTheory.quadForm_sub` already declared in
AlonBoppana.lean (a different, vector-pair notion) — renamed here to
`quadForm_sub_matrix` with all consumers updated.

**Remaining risk / priced follow-ons:** ~~the additive eigen-coordinate
form is the delivered statement; the *multiplicative* `(1±ε)`
refinement on `im Π`-coordinate vectors (vectors supported on
nonzero-eigenvalue coordinates, where `qF(Π) x = x ⬝ᵥ x`) and the
`q ~ log n/ε²` budget corollary (driving the bound below `δ`) are
one-slice follow-ons on the delivered base.~~ **Both DELIVERED
2026-08-28** (the follow-on delivery record below). The recorded
Slice-2 set-aside (`ssVariance K₂ 1 = rankOne v_(0,1)` exact matrix
value) stands. The proposal's draft statement's *graph-vector*
multiplicative form (`xᵀL̃x` vs `xᵀLx` for Laplacians rather than
eigen-coordinate operators) would additionally need the sampled
*Laplacian* object and its form-level correspondence — a further priced
follow-on, recorded here so the next run does not mistake the
eigen-coordinate form for it.

## Follow-on delivery record: the `(1±ε)` multiplicative refinement + the budget corollary (2026-08-28, run `20260828T183001Z-run-1`)

The proposal's two priced one-slice follow-ons, **DELIVERED** in one
run as zero new axioms (count stays 10; `#print axioms` via
`wip/ssmult_axcheck.lean` on all eleven audited declarations: the
engine lemma and six hard-crust QA lemmas exactly `propext,
Classical.choice, Quot.sound`; the two Derived theorems and their two
QA interface pins honestly carrying `matrix_bernstein` alone — the
same conditional structure as the delivered tails). QA 2800 → 2808
(+8, the new `(1±ε)` section of `SparsificationTail_QA.lean`).

**(1) The engine piece** — `quadForm_imageProjector_eq_of_mulVec_eq`
(`Sparsification.lean`'s Projector section, pure hard crust): at every
`im Π`-coordinate vector the projector's quadratic form is exactly the
squared norm. This is the identity that makes the multiplicative
reading *legitimate* — off the cone the zero-eigenvalue coordinates'
mass is dropped and the conversion is unsound, so the cone hypothesis
is load-bearing, not decorative (fenced in QA, below). It completes the
projector's quadratic-form interface beside `quadForm_imageProjector_
nonneg` / `_le` / `_eq` (the sum form).

**(2) `sparsification_multiplicative_tail`** (`Derived/
SparsificationTail.lean`) — the field-standard statement shape: the
failure of the two-sided bound `(1−ε)(x ⬝ᵥ x) ≤ xᵀ S(ω) x ≤
(1+ε)(x ⬝ᵥ x)` over vectors the image projector fixes obeys the same
exponential tail — a `measure_mono` from the delivered additive tail
at `t = ε`: on the cone `qF(Π) x = x ⬝ᵥ x` (the engine lemma), so each
disjunct yields `|qF(S) x − qF(Π) x| > ε (x ⬝ᵥ x)` with the sign
resolved by the disjunct itself. Any `0 < ε` (no upper guard — the
statement only weakens as `ε` grows).

**(3) `sparsification_multiplicative_budget`** — the sample-complexity
sentence: at `0 < ε ≤ 1` and `0 < δ`, budget
`q ≥ (8/3)·log(2 card V/δ)/ε²` drives the multiplicative failure
measure below `δ`. The `8/3` is exact, not decorated: the Tropp
exponent `ε²/(2/q + 2ε/(3q))` equals `qε²/(2 + 2ε/3)`, the
denominator is at most `8/3` on the stated regime, and the hypothesis
rearranges to `log(2d/δ) ≤ 3qε²/8` — so the exponent dominates the
log, `exp(−E) ≤ δ/(2d)` by `Real.exp_log`, and the `2d` prefactor
cancels. Note the corollary holds at *every* `δ > 0` including
`δ > 2d` (then `log(2d/δ) < 0` and the budget hypothesis is weak, but
the chain still closes — the exponent is positive regardless).

**QA (the new `(1±ε)` section, +8):** the edge vector's **im-Π
membership proved order-independently** (at a zero-eigenvalue basis
index the edge vector's own definition vanishes, so both sides are
zero; elsewhere the projector is the identity — no `eigvalOf` ordering
assumption anywhere, so the fact survives any eigenbasis choice); the
**engine identity's first instance** joined to the existing four-pair
pin of the same `1/2`; the **tight `ε = 1` two-sided instance** (the
upper bound attained with equality, consistent with the deviation norm
being exactly `1 = 1/q` at the all-true outcome); **failure-event
nonemptiness at `ε = 1/2`** with hand values (`qF(S) v = 1 >
(3/2)(1/2) = 3/4`); the **cone fence** — at the all-false outcome
nothing is sampled (`S = 0` proved: both cross-pair weights are
`δ/p = 0`, the loops' rank-one factors the zero matrix), and the
un-guarded pointwise claim is *refuted* there (`(1/2)·2 = 1 > 0 =
qF(S) ones`): the `im Π` restriction is exactly what the engine lemma
needs; and the **two interface pins** (the tail at `q = 1`,
`ε = 1/2`; the budget at `ε = δ = 1/2`, `q = 100`, with the hypothesis
`(8/3)·log 8/(1/4) ≤ 100` discharged by `log 8 ≤ 300/32` from
`Real.add_one_le_exp` — `8 = 7 + 1 ≤ exp 7 ≤ exp 9.375`).

**Technique findings (this pin's Mathlib):** the numerals in a
`Real.log` argument do not rewrite by `rw` across cast spellings
(`↑(Fintype.card (Fin 2))` vs `(2 : ℝ)`) — evaluate the argument first
(`hcard` by `simp`, then a `norm_num` identity for the arithmetic
inside), and normalize the constant prefactor by an explicit
`field_simp; ring` identity before `linarith` (it treats
`(8/3)·log 8/(1/2)^2` as an opaque nonlinear atom). `Real.log_le_iff_
le_exp` is this pin's spelling (`log_le_iff` does not resolve).
`Real.exp_neg` rewrites *forward* (`exp(−x) = (exp x)⁻¹`); the reverse
pattern match fails. `positivity` cannot use variable positivity
hypotheses (`0 < δ`, `0 < card V`) — those comparisons need explicit
`div_pos`/`mul_pos` terms.

**Verification:** spike first (`wip/ssmult_spike.lean`, all pieces
iterated to zero errors/warnings before any shelf edit); `lake env
lean` zero errors/zero warnings on all three touched modules; explicit
`lake build` targets ✔ (2159/2159, 2165/2165, 2166/2166); `#print
axioms` exactly as designed (above); **full `lake build` ✔
(2405/2406) immediately followed by `check_build_completeness.py` —
127/127 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, both
findings allowlisted-confirmed), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**2808/10/0**).

**Remaining priced follow-on (not started):** the *graph-vector*
multiplicative form above (the sampled-Laplacian object and its
form-level correspondence).
