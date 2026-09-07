# Proposal: Global (Window-Free) Semigroup Contraction Bounds

**Status:** Steps 0(m=0)/1/2 DELIVERED 2026-09-07 (run
`20260907T053227Z-run-2`, session `ses_f85b4c94affebxh9q9Bec73k5W` —
delivery record at the file's end) **under the named-consumer scope**:
the operator-added Medium row `proposals/boundary-outflow-lemma.md`
(Part 2) is the "different named consumer" this document's own gate
names as an alternative to explicit adoption. **Steps 3–5 (the
order-`m` generalization and the operator-norm restatement) remain
operator-gated** — the gate below is NOT resolved for them, and the
order-`m` scalar Taylor lemma (the full Step 0) remains unproved and
priced.

Restated in pure-mathematics form 2026-09-06 from
an external request relayed by the operator (not tracked in this
repository — see `.gitignore`); no operational, product, or patent
framing survives into this document, only the underlying mathematical
asks. Authorizes no Lean changes, axiom admissions, document rewrites,
or transit-map edits.

Companion to
[`reversibility-and-heat-semigroup.md`](reversibility-and-heat-semigroup.md)
(Phase C, COMPLETE 2026-08-23 — the heat-semigroup program this
document extends) and the delivered
`heatKernel_firstOrder_remainder_apply_le` /
`heatKernel_firstOrder_remainder_interval` pair in
`Scaffold/Mathlib/GraphTheory/Heat.lean` (the existing remainder-bound
machinery this proposal generalizes). `docs/6_SGT_BACKLOG.md` item 5
records the heat-semigroup instance opened 2026-08-19 and its Phase C
remainder bound as **complete**; this document does not reopen that
item, it proposes new machinery layered on top of it, in the same
relationship the mutual-information and Erdős–Rényi proposals have to
their own "complete" predecessors.

## The claim this document is answering

The relayed request's framing was: existing remainder bounds for the
heat semigroup `e^{-tL}` hold only under a smallness window
`|t·λᵢ| ≤ 1` on every eigenvalue; is a **global** (window-free) bound
over the entire half-line `t ≥ 0` available, both at first order
(`‖x₀ − e^{-tL}x₀‖₂ ≤ t‖Lx₀‖₂`) and for the general order-`m` Taylor
truncation? Verified directly against the delivered proof (below): the
window is not a fundamental limitation of the mathematics on this
project's actual graphs — it is a byproduct of `heatKernel_firstOrder_
remainder_apply_le` being proved for **any** symmetric weight matrix,
including networks with negative edge weights, where the Laplacian's
eigenvalues can be negative and `e^{-tλ}` genuinely blows up as
`t → ∞`. Every consumer this project actually has (`laplacian_psd`,
`heatKernel_decayFactor_le_one`, `heatKernel_variance_decay`) already
carries the nonnegative-weight hypothesis `hnonneg : ∀ i j, 0 ≤ A i j`.
Under that same hypothesis, the Laplacian is PSD, every eigenvalue is
`≥ 0`, and the window can be dropped entirely — a genuinely global
bound over `t ≥ 0` becomes available, at the cost of narrowing from
"any symmetric network" to the PSD case this project already lives in
for every other heat-semigroup consumer.

## What's already on the shelf

- **The eigenbasis expansion engine** — `heatKernel_mulVec_eq_sum`
  (`Heat.lean:737`), `eigvecOf_expansion_apply`,
  `dotProduct_eigvecOf_mulVec`, `dotProduct_eigvecOf` — the exact
  machinery `heatKernel_firstOrder_remainder_apply_le` and
  `heatKernel_variance_decay` both already use to turn a matrix
  statement into a per-mode scalar statement plus Parseval. This
  proposal's vector-level lemmas reuse it unchanged.
- **The PSD-eigenvalue extraction pattern** — `heatKernel_decayFactor_
  le_one`'s proof (`Heat.lean:714`) already does exactly the step this
  proposal needs: `quadForm_eigvecOf_self` plus `laplacian_psd A hA
  hnonneg` gives `0 ≤ eigvalOf (laplacian A) hL i` for every mode, from
  the same `hnonneg` hypothesis already standard across this file.
- **The global order-0 scalar inequality, already in the pinned
  Mathlib, unrestricted:** `Real.add_one_le_exp (x : ℝ) : x + 1 ≤
  Real.exp x` — no smallness hypothesis at all. At `x := -y` this is
  exactly `1 - y ≤ e^{-y}`, i.e. `1 - e^{-y} ≤ y` for every real `y`,
  in particular every `y ≥ 0`. This is the *global* engine the window-
  restricted `Real.abs_exp_sub_one_sub_id_le` (the pin the delivered
  remainder bound cites, `|x| ≤ 1 → |eˣ − 1 − x| ≤ x²`) was standing in
  for when the eigenvalue could be negative; on the PSD half-line it is
  strictly stronger and needs no hypothesis.
- **The Euclidean-norm transfer layer** — `norm_euclidean_eq_sqrt` and
  `abs_dotProduct_le` (`Analysis/OperatorTheory/Perturbation/
  Duhamel.lean:234,248`): the already-proved bridge from a
  `Matrix.dotProduct`/Parseval-shaped bound to a literal `‖·‖`
  (`EuclideanSpace ℝ V`) statement, and `l2OpNorm_le_of_abs_dotProduct_
  le` (`Duhamel.lean:269`) for restating a per-mode contraction as an
  honest operator-norm bound `‖M‖ ≤ c` if a consumer wants that form.
  The request's own formulas are written with `‖·‖₂` notation — this
  layer, not `Heat.lean`'s native sum-of-squares idiom, is what makes
  that literal notation available cheaply (see "Scope decision"
  below).
- **The induction-on-power-with-eigenbasis pattern** — `Mixing.lean`'s
  `eigvecOf_dotProduct_degreeSqrt_mulVec_pow_walkTransitionMatrix`
  (`Mixing.lean:525`) and its Parseval-transfer companion
  (`Mixing.lean:553`) already carry out, for the walk transition
  matrix, exactly the "expand `Mᵏ *ᵥ x` over the eigenbasis by
  induction on `k`" step the order-`m` generalization needs for
  `(laplacian A)ᵏ *ᵥ x`. No such lemma exists yet for `laplacian A`
  itself (checked: no `pow`-indexed `laplacian` lemma in `Heat.lean`
  or `Spectral.lean`), but the proof shape is a direct transfer, not
  new mathematics.

## What's not on the shelf — the real gap

**The global order-`m` Taylor-remainder scalar inequality itself is
genuinely new** — not in Mathlib (`Real.abs_exp_sub_one_sub_id_le` and
`Real.exp_bound`/`exp_bound'` are all restricted to `|x| ≤ 1` or a
`≤ 1/2` scaled variant; no unrestricted alternating-sign Taylor-
remainder lemma for `Real.exp` exists in the pinned Mathlib, checked by
grep across `Mathlib.Data.Complex.Exponential` and
`Mathlib.Analysis.SpecialFunctions.Exp`), and not yet stated anywhere
in this project. It is, however, true and cheap to prove with tools
already available:

**Claim.** For every `y ≥ 0` and every `m : ℕ`,
```
|Real.exp (-y) - ∑ k in Finset.range (m + 1), (-y) ^ k / k.factorial|
  ≤ y ^ (m + 1) / (m + 1).factorial
```
**Route (induction on `m`, no integral calculus — matching the
`HasDerivAt`-only level of tooling `Heat.lean`/`Duhamel.lean` already
use, e.g. `heatKernel_mulVec_apply_hasDerivAt_zero`,
`heatApply_hasDerivAt`):**

- Write `R m y := Real.exp (-y) - ∑ k in Finset.range (m+1), (-y)^k /
  k.factorial`. Term-by-term differentiation (the same finite-sum
  `HasDerivAt.sum` pattern `heatApply_hasDerivAt` already carries out)
  gives the **shift identity** `HasDerivAt (R (m+1)) (-(R m y)) y` for
  every `y` — differentiating shifts the truncation index down by one,
  since `d/dy [(-y)^k/k!] = -(-y)^{k-1}/(k-1)!`.
- **Base case `m = 0`:** `R 0 y = e^{-y} - 1`, and `Real.add_one_le_exp`
  gives `-y ≤ R 0 y ≤ 0 ≤ y` directly for `y ≥ 0` (no induction
  needed) — this *is* the request's first formula.
- **Inductive step:** given `|R m y| ≤ y^{m+1}/(m+1)!` for all `y ≥ 0`,
  form `g(y) := y^{m+2}/(m+2)! - R (m+1) y` and `h(y) := y^{m+2}/
  (m+2)! + R (m+1) y`. Both vanish at `y = 0`, and by the shift
  identity `g'(y) = y^{m+1}/(m+1)! + R m y ≥ 0` and `h'(y) =
  y^{m+1}/(m+1)! - R m y ≥ 0` for `y ≥ 0` — exactly the induction
  hypothesis. Mathlib's `monotoneOn_of_deriv_nonneg` (already in the
  pinned `Analysis.Calculus.MeanValue`) then gives `g, h` nonnegative
  on `[0, ∞)` from their derivative sign and their value at `0`, which
  is precisely `|R (m+1) y| ≤ y^{m+2}/(m+2)!`.

This closes the induction with nothing beyond finite-sum
differentiation (already this project's idiom) and one Mathlib
monotonicity lemma. It is the one piece of this proposal that is
actual new proof content rather than reassembly of existing lemmas —
sized similarly to `mutual-information-and-data-processing.md`'s
Step 3 (a real but bounded lemma, not a multi-run program).

## Scope decision: which norm notation to deliver

`Heat.lean`'s native idiom states bounds as `Matrix.dotProduct (v) (v)`
sums (squared-norm form, no `Real.sqrt`) — see `heatKernel_variance_
decay`. The request's own formulas are written with `‖·‖₂`. Rather
than pick one, deliver both, cheaply: the squared/`dotProduct` form is
the primary proof target (matches every existing Parseval-style lemma
in this file and needs no extra machinery), and a one-line corollary
applies `norm_euclidean_eq_sqrt` (already proved in `Duhamel.lean`) plus
monotonicity of `Real.sqrt` to produce the literal `‖x₀ − e^{-tL}x₀‖ ≤
t‖Lx₀‖` statement the request names verbatim. This mirrors the
mutual-information proposal's own "Scope decision" precedent of
choosing the idiom that matches existing consumers first and adding
notation-level convenience second.

## Build order

### Step 0: The global scalar Taylor-remainder lemma

The induction above, as a standalone real-analysis lemma with no
matrix content — `Real.exp_neg_taylor_remainder_le` (name TBD),
stated exactly as in "What's not on the shelf." Pure `ℝ`, testable in
isolation before any graph-theoretic content is touched.

### Step 1: The order-0 vector-level bound, dotProduct form

```
theorem heatKernel_globalContraction_dotProduct_le (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j) {t : ℝ} (ht : 0 ≤ t)
    (x : V → ℝ) :
    Matrix.dotProduct (x - heatKernel A t *ᵥ x) (x - heatKernel A t *ᵥ x)
      ≤ t ^ 2 * Matrix.dotProduct (laplacian A *ᵥ x) (laplacian A *ᵥ x)
```
Route: eigenbasis-expand both sides exactly as `heatKernel_variance_
decay` does; per mode, `(1 - e^{-tλᵢ})² ≤ (tλᵢ)²` follows from Step 0's
`m = 0` case (equivalently, directly from `Real.add_one_le_exp`) plus
`λᵢ ≥ 0` (the `heatKernel_decayFactor_le_one`-style PSD extraction);
sum termwise via Parseval.

### Step 2: The literal Euclidean-norm corollary

`‖x - heatKernel A t *ᵥ x‖ ≤ t * ‖laplacian A *ᵥ x‖` (`EuclideanSpace ℝ
V` norms, via `WithLp.equiv 2`), by `norm_euclidean_eq_sqrt` applied to
both sides of Step 1 plus `Real.sqrt_le_sqrt` and `Real.sqrt_mul_self`.
This is the request's first formula, delivered verbatim.

### Step 3: `(laplacian A) ^ k *ᵥ x` in eigenbasis form

Not currently on the shelf for `laplacian A` (only for the walk
transition matrix, in `Mixing.lean`). A direct induction on `k`
cloning `eigvecOf_dotProduct_degreeSqrt_mulVec_pow_walkTransitionMatrix`'s
shape: `laplacian A ^ (k+1) *ᵥ x = laplacian A *ᵥ (laplacian A ^ k *ᵥ
x)`, expand the inner factor by the induction hypothesis, transfer
through `dotProduct_eigvecOf_mulVec` once more. Needed as a
prerequisite for Step 4's `L^{m+1} x₀` term; not needed by Steps 1–2.

### Step 4: The order-`m` vector-level bound, dotProduct form

```
theorem heatKernel_globalTaylorRemainder_dotProduct_le (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j) {t : ℝ} (ht : 0 ≤ t)
    (m : ℕ) (x : V → ℝ) :
    Matrix.dotProduct
        (x - ∑ k in Finset.range (m + 1),
          ((-t) ^ k / k.factorial) • (laplacian A ^ k *ᵥ x))
        (x - ∑ k in Finset.range (m + 1),
          ((-t) ^ k / k.factorial) • (laplacian A ^ k *ᵥ x))
      ≤ (t ^ (m + 1) / (m + 1).factorial) ^ 2
        * Matrix.dotProduct (laplacian A ^ (m + 1) *ᵥ x)
            (laplacian A ^ (m + 1) *ᵥ x)
```
Route: eigenbasis-expand every term (Step 3's expansion for each power
of `L`), reduce to the per-mode scalar statement `|e^{-tλᵢ} - Σₖ
(-tλᵢ)^k/k!| ≤ (tλᵢ)^{m+1}/(m+1)!`, which is Step 0's general claim at
`y := t·λᵢ ≥ 0` (PSD again supplying `λᵢ ≥ 0`); sum termwise via
Parseval exactly as Step 1.

### Step 5: The literal Euclidean-norm corollary for order `m`

The request's second formula, by the same `norm_euclidean_eq_sqrt`
transfer as Step 2.

### Deferred and removed

- **A general operator-norm restatement `‖heatKernel A t‖ ≤ 1` via
  `l2OpNorm_le_of_abs_dotProduct_le`** — available cheaply from
  `heatKernel_decayFactor_le_one` if a future consumer wants the
  semigroup contraction property stated as an honest matrix operator
  norm rather than the per-mode form; not needed by Steps 1–5, which
  only use the per-mode bound directly.
- **The signed-weight (non-PSD) case** — deliberately out of scope;
  that is exactly the case the existing windowed
  `heatKernel_firstOrder_remainder_apply_le` already covers, and this
  proposal does not touch or weaken it. Both bounds coexist: the
  windowed one for arbitrary symmetric networks, the global one here
  for the PSD case this project's other heat-semigroup consumers
  already assume.
- **A general `Real.exp` remainder lemma proposed for upstreaming to
  Mathlib** — the scalar lemma in Step 0 is general-purpose real
  analysis with no graph-theoretic content and could plausibly be
  useful outside this project, but upstreaming is a separate decision
  outside this proposal's scope.

## QA plan

- Step 0's scalar lemma: numeric pins at small `(m, y)` (e.g. `m = 2`,
  `y = 3`) checked against a direct `norm_num`/`decide`-friendly
  evaluation of both sides.
- Step 1/2: reuse the existing K₂ fixture already carrying
  `heatKernel_edge_remainder_*_QA` in `Heat_QA.lean`. The concrete
  payoff worth pinning explicitly: `Heat_QA.
  heatKernel_edge_remainder_window_fenced_QA` already proves the
  *windowed* first-order bound's hypothesis fails at `t = 1` on K₂ —
  a new QA witness should show the **global** bound from Step 1/2
  holds at that same `t = 1` (and beyond) on the same fixture,
  demonstrating the actual value-add concretely rather than only in
  prose.
- Step 4/5: instantiate at `m = 0` and check it specializes to exactly
  Step 1/2's statement (a definitional/`ring`-level consistency check
  between the two deliveries, not a new proof).
- A `hnonneg` omission fence: exhibit a signed-weight K₂-style fixture
  where the global bound's conclusion genuinely fails (large `t`,
  negative eigenvalue), confirming `hnonneg` is load-bearing and not
  decorative, per this project's standing adversarial-fence discipline
  (`governance/ADVERSARIAL_REVIEW.md`).

## Gate — this needs an operator decision, not routine backlog treatment

`docs/6_SGT_BACKLOG.md` item 5 and `reversibility-and-heat-semigroup.md`
record the heat-semigroup program, including its Phase C remainder
bound, as **complete**. No open backlog item or proposal currently
names a global/window-free contraction bound as a blocking dependency
— this is new machinery proposed on the strength of an external
request relayed by the operator, not an internal named consumer,
matching the shape `mutual-information-and-data-processing.md` and
`erdos-renyi-random-graph-model.md` were both adopted-or-not under. An
operator should adopt this proposal explicitly (or name a different
consumer for it) before Step 0 begins.

## Operating instructions for an autonomous run

*(Apply only after the Gate above is resolved.)*

- Step 0 (the scalar lemma) is self-contained and could be spiked
  independently of a Gate decision at essentially no cost, exactly as
  `mutual-information-and-data-processing.md`'s Step 1 was flagged;
  Steps 1 onward should wait for explicit adoption.
- One step per run is likely comfortable for Steps 1–2 and separately
  for Steps 3–5; Step 0 and Step 1 could plausibly combine in a single
  run if proof friction is low.
- **No new axioms.** Every piece above stays inside already-proved
  `Heat.lean`/`Duhamel.lean`/`Mixing.lean` machinery, one already-proved
  unrestricted Mathlib lemma (`Real.add_one_le_exp`), and one already-
  proved Mathlib monotonicity lemma (`monotoneOn_of_deriv_nonneg`); if
  Step 0's induction turns out to need something genuinely absent from
  the pin, stop and record the precise obstruction in
  `docs/6_SGT_BACKLOG.md` rather than admitting anything.
- Ship the `hnonneg`-omission fence (QA plan, last bullet) in the same
  delivery as Step 1, not as a follow-on audit pass.
- Do not fold this delivery into `reversibility-and-heat-semigroup.md`'s
  own COMPLETE record; this is new machinery layered on top, not a
  missing piece of that program.

## Open next step

Blocked on the Gate above, not on any technical prerequisite. Step 0
could be spiked at any time at essentially no cost; Steps 1 onward
should wait for an explicit adoption decision, or a different named
consumer, per this project's standing "no new machinery ahead of a
decision" norm.

## Delivery record: Steps 0(m=0)/1/2 under the named-consumer scope (2026-09-07, run `20260907T053227Z-run-2`)

**Scope discipline.** Exactly the three steps the consumer
(`proposals/boundary-outflow-lemma.md` Part 2, the operator-added
Medium row) names as its build-order dependency — nothing more:

- **Step 0 at `m = 0` only** — `sq_one_sub_exp_neg_le`
  (`Heat.lean`): `(1 − e^{−y})² ≤ y²` for every `y ≥ 0`. Route
  simpler than the priced induction (which the order-`m` case will
  still need): the two one-sided bounds `1 − y ≤ e^{−y}`
  (`Real.add_one_le_exp`) and `e^{−y} ≤ 1 ≤ 1 + y`
  (`Real.exp_le_exp`) feed the pinned Mathlib's `sq_le_sq'`
  (`−b ≤ a ≤ b → a² ≤ b²`) directly. The general order-`m` Taylor
  remainder (the induction via `monotoneOn_of_deriv_nonneg`) remains
  **unproved and gated**.
- **Step 1** — `heatKernel_globalContraction_dotProduct_le`
  (`Heat.lean`): the dotProduct form, by the priced route (Parseval
  over the proved eigenbasis; the per-mode displacement coordinate
  `(1 − e^{−tλᵢ}) · cᵢ` from
  `eigvecOf_dotProduct_heatKernel_mulVec`; the PSD eigenvalue
  extraction `heatKernel_decayFactor_le_one`-style; the scalar
  engine at `y := tλᵢ`; the Laplacian's own Parseval
  `dotProduct_eigvecOf_mulVec` reassembling `t²·(Lx ⬝ᵥ Lx)`).
- **Step 2** — `heatKernel_globalContraction_le` (`Heat.lean`): the
  literal Euclidean-norm statement via `norm_euclidean_eq_sqrt` +
  `Real.sqrt` monotonicity, exactly as priced.

**Consumers.** The Medium row's own Part 2
(`abs_partIndicator_dotProduct_heatFlow_le` in `Multiway.lean`, plus
the general-probe engine `abs_dotProduct_heatFlow_le` in `Heat.lean`)
is the named consumer, delivered in the same run; the general-probe
engine is the reusable form.

**QA** (`Heat_QA.lean` + the Multiway pin): per this document's own
plan — the scalar pin at `y = 2`; **the payoff pin**: the global
bound through the theorem at `t = 1` on K₂ where
`heatKernel_edge_remainder_window_fenced_QA` proves the windowed
bound's hypothesis fails (`t·λ = 2 > 1`), both sides evaluated
(`2(1−e^{−2})² ≤ 2` vs RHS exactly `8`); the Euclidean form at the
same point; the general-probe dissipation pin; and **the `hnonneg`
omission fence in the same delivery** (this document's standing
instruction): the signed K₂ fixture `!![0,−1;−1,0]]` (symmetric,
`hnonneg` failing at the `−1` entries, Laplacian eigenvalue `−2`),
where the conclusion genuinely fails at `t = 1` — the mode GROWS
(`K₁m = e²•m`, `3 < e²` by `Real.add_one_lt_exp`, LHS `2(e²−1)² > 8`
= RHS).

**Verification.** Spike-first (`wip/gsc_spike.lean`, five fix rounds,
traps recorded in the consumer's Part-2 record); explicit builds of
all four touched modules; full ladder green (build + completeness
135/135; `lint_axioms` 0; 24-tag independence clean; 63-module
reachability; citations; links; name-uniqueness clean for `gsc*`;
backlog fresh; scoreboard 1369/6635/4/0; map freshness 0); the
16-declaration axiom audit (`wip/gsc_axcheck.lean`) — every one
exactly `propext, Classical.choice, Quot.sound`.

**Still gated (unchanged).** Steps 3–5 — the `(laplacian A)^k`
eigenbasis expansion, the order-`m` vector bound, its Euclidean
twin, and the deferred operator-norm restatement — wait on the
operator adoption decision exactly as before; the general order-`m`
scalar Taylor lemma is the one piece of genuinely new proof content
this document carries, and it remains unproved. A future consumer
stating an order-`m` need would be the same named-consumer route
this delivery used at order 0.
