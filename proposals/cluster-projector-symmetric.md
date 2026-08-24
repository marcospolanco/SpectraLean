# Cluster-Projector Symmetric Form — the Two-Sided (Both-Separations) Constant-2 Set-Form Difference Theorem without Rank Equality

**Status:** COMPLETE — Steps 0+1 delivered in one run (2026-08-24, run
`20260824T175747Z-run-1`); see the delivery record below  
**Proposed:** 2026-08-24, run `20260824T175747Z-run-1`  
**Axis:** Perturbation bridge (ring 2) consuming the SGT center's
eigenbasis layer (ring 1)  
**Backlog relation:** the recorded open follow-on of
`cluster-projector.md` ("the two-sided rank-free constant-2 *set* form
composes from the delivered pair (equal-rank dropped via the symmetric
form's both-orders trick) but was not re-derived here") and the set-form
completion of backlog item 9's difference family — the sibling shape of
`band-davis-kahan-symmetric.md` at sets.

## The gap

The delivered set-form pair is one-sided: the product bound
`‖Q_T * P_S‖ ≤ ‖A−B‖/δ` separates *one* cluster of `B` from *one*
cluster of `A`, and the difference form converts it through the
equal-rank identity, so its consumer must count multiplicities (through
the rank supplier) before applying it. The window family already has
the two-sided answer — `l2OpNorm_bandProjector_sub_bandProjector_le_two_of_symm`,
constant 2, no rank hypothesis, the Yu–Wang–Samworth Theorem 1
both-gaps selling point — but at windows only. A consumer holding
*both* flank separations between two non-interval clusters (e.g.
`S = {λ : |λ| ≥ 3}` vs `T = {λ : |λ| ≤ 1}`, two half-lines against an
interval) has no theorem to apply: the delivered set difference form
demands a rank equality those clusters need not have, and the window
symmetric form cannot express the sets.

## Step 0 — the worked route (surveyed this run, before any statement)

**The composition is exact, and the set form is *easier* than its
window sibling.** The window symmetric form needed a private rank-free
pairwise product bound (the cluster theorem's dichotomy/shrink/engine
body factored out, with an `‖A − B‖ < δ` contentful-regime hypothesis
excluding the interior case) instantiated at both argument orders, plus
the trivial-regime case split. The delivered set-form product bound
`l2OpNorm_clusterProjector_mul_clusterProjector_le` is **already
unconditional** — its center/radius membership hypotheses carry no
smallness regime — so the set symmetric form is a pure composition with
no case split at all:

```
P − Q = (I − Q_T) * P_S − Q_T * (I − P_S)          (ring identity, on shelf privately)
(I − Q_T) = Q_{Tᶜ},  (I − P_S) = Q_{Sᶜ}            (complement law — definition-level)
‖Q_{Tᶜ} * P_S‖ ≤ ‖A−B‖/δ                            (set product bound, order 1)
‖Q_T * Q_{Sᶜ}‖ = ‖Q_{Sᶜ} * Q_T‖ ≤ ‖B−A‖/δ           (l2OpNorm_transpose + both
                                                      projectors symmetric; set
                                                      product bound, order 2)
⇒ ‖P − Q‖ ≤ 2‖A−B‖/δ                                (triangle — the constant 2 exactly)
```

**Statement shape, recorded before stating.** The two product-bound
instantiations need *different* centers: order 1 measures B's
out-of-`T` cluster against A's `S`-cluster center; order 2 measures
A's out-of-`S` cluster against B's `T`-cluster center. The statement
therefore carries **two** center/radius pairs:

```
hnearS : ∀ i, λᵢ(A) ∈ S   → |λᵢ − cS| ≤ rS
hfarT  : ∀ j, μⱼ(B) ∉ T   → rS + δ ≤ |μⱼ − cS|
hnearT : ∀ j, μⱼ(B) ∈ T   → |μⱼ − cT| ≤ rT
hfarS  : ∀ i, λᵢ(A) ∉ S   → rT + δ ≤ |λᵢ − cT|
⇒ ‖P_A(S) − P_B(T)‖ ≤ 2 * ‖A − B‖ / δ
```

A single common `(c, r)` (both clusters within `r` of one `c`, both
complements `r + δ` outside) would also drive the composition, but it
excludes the natural unequal-rank witness — `A`'s out-of-`S` mode at
`5` sitting *between* the clusters `S = {0, 11}` and `T = {4}`: no
single `c` meets both flank separations at any `r`, while the two-pair
form covers it. The two-pair shape is the honest minimal hypothesis
set; the single-center variant is its consumer-facing corollary if one
is ever requested, not a separate theorem.

No dichotomy, no interior case, no rank hypothesis, no regime split —
every input is a delivered theorem at the exact needed shape (the Step-0
survey verified each name and signature against the shelf:
`one_sub_clusterProjector`, `clusterProjector_symmetric` (an `IsSymm`
proof, defeq to the transpose equation), `l2OpNorm_transpose`,
`Matrix.transpose_mul`, the private ring identity
`sub_eq_one_sub_mul_sub_mul_one_sub` in this module's `SymmetricForm`
section, and the set-form product bound itself).

## Step 1 — deliverable

1. The new theorem in the `SetForm` sections of
   `Perturbation/BandDavisKahan.lean` (**no new imports**) at exactly
   the Step-0 shape.
2. QA, a new symmetric-form section of
   `Scaffold/QA/Perturbation/ClusterProjector_QA.lean` (extending the
   set family's QA home; the public fixtures reused): (a) the
   **unequal-rank non-interval witness** — `S = {0, 5}` on `clusterA`
   (rank 2) vs `T = {5}` on `bm` (rank 1), both flank separations
   discharged at `cS = 5/2, rS = 5/2, cT = 5, rT = 0, δ = 1/2`, the
   delivered equal-rank family's hypothesis exhibited failing, theorem
   bound `≤ 4` through the imported `normABm_le`, raw lower `1` at
   `e₀` through two new entrywise pins (`P_A({0,5}) = diag(1,1,0)`
   composing from the already-exported `bandClusterA_eq`;
   `P_bm({5}) = diag(0,1,0)` through an extracted bm-side threshold
   pair); (b) the **ε = 0 attainment** at `S = T = {5}` through the new
   theorem with both flank separations genuinely discharged;
   (c) the **two-sided fence** on the interior-gap configuration
   (`A = B = clusterA`, `S = {0, 11}`, `T = {5, 11}`, `δ = 1/2`): both
   `hnear` sides verified, *both* `hfar` sides refuted in proved form
   (each at its own interior eigenvalue), the hypothesis-free
   conclusion refuted at norm `≥ 1` — the two-sidedness itself
   exercised, so neither separation is decoration; (d) the
   **ring-identity coherence witness** — `P − Q = (I−Q)P − Q(I−P)`
   verified entrywise on the pinned witness projectors, the
   composition's identity exhibited numerically.
3. Records: this document, `proposals/README.md` (High row at start,
   Delivered row at end), README (status counts + the Perturbation
   row's symmetric-set sentence), radar QA axis sync, scoreboard,
   `index/map/perturbation.md`,
   `index/sources/davis_kahan_1970.md` (the both-gaps-at-sets mapping
   row), the execution plan, and the activity log.

Zero new axioms; every new declaration `#print axioms`-clean at the
standard three.

## Leverage

- Closes the recorded follow-on of the newest delivery and completes
  the set-valued family to the window family's full shape
  (product/difference/symmetric), so the interval constraint is gone
  from the *whole* difference family, not just its one-sided half.
- The rank obligation disappears at exactly the consumer shape YWS
  Theorem 1 advertises: state both separations, conclude — no
  multiplicity counting.
- Load-bearing by the falsifiability test: the proof consumes the
  day-old complement law, the set-form product bound at *both* argument
  orders, the transpose lemma, and the ring identity — a misstatement
  in any one breaks it or its QA loudly. The QA's unequal-rank witness
  is engineered to be unreachable by the delivered equal-rank form (the
  point of the theorem) and the two-sided fence knocks over each
  separation side separately.
- Cost is minimal: one theorem (a four-step composition, every input on
  shelf) plus QA in the family's established idiom — the smallest
  coherent unit that makes the set family's rank-freeness real.

## Delivery record (2026-08-24, run `20260824T175747Z-run-1`)

Delivered at exactly the committed shape, in one run. The new
`SetForm` theorem of `Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean`
(**no new imports**) and the new symmetric-form section of
`Scaffold/QA/Perturbation/ClusterProjector_QA.lean` (28 → 46
declarations). Zero new axioms (count stays 9; `#print axioms` via
`wip/cps_axcheck.lean` on the new public theorem and all 18 new QA
declarations: `propext, Classical.choice, Quot.sound` only, every
one). QA 1953 → 1971.

- **The theorem** `l2OpNorm_clusterProjector_sub_clusterProjector_le_two_of_symm`
  at exactly the Step-0 shape (two center/radius pairs, four
  membership-separation hypotheses, conclusion `≤ 2 * ‖A − B‖ / δ`):
  the ring identity (the module's own private
  `sub_eq_one_sub_mul_sub_mul_one_sub`), the complement law at both
  residuals, the delivered set-form product bound at both argument
  orders, `l2OpNorm_transpose` moving the second, and the triangle
  inequality — the proof is the four-step composition the survey
  priced, with **no case split anywhere** (the window sibling's
  trivial-regime dichotomy is unnecessary here because the set product
  bound is unconditional; the delivery record of that sibling explains
  why *its* route needed the split — the set form's easier route is
  the finding).

- **QA delivered at the four mandated sections** (18 declarations): (1)
  the **unequal-rank non-interval witness** — `S = {0, 5}` on
  `clusterA` (rank 2, pinned `P = diag(1,1,0)` through capture to
  `Ioc(−1,6]` + the already-exported `bandClusterA_eq`) vs `T = {5}`
  on `bm` (rank 1, pinned `diag(0,1,0)` through the extracted
  threshold pair `spBm_four`/`spBm_six`, the latter the two-mode pin
  at the second fixture), `cpsQA_ranks_ne` exhibiting the delivered
  equal-rank family's hypothesis failing, both flank separations
  discharged at `cS = 5/2, rS = 5/2, cT = 5, rT = 0, δ = 1/2` (the
  two-pair shape load-bearing: the out-of-`S` eigenvalue `11` sits
  between the clusters — distance `6` from `cT` while `bm`'s
  out-of-`T` eigenvalues sit `7/2`/`17/2` from `cS`; no single center
  covers both flanks at any radius), the theorem bound evaluated
  `≤ 4` through the imported `normABm_le`, against the raw lower `1`
  at `e₀` from the entrywise pins — computed completely independently
  of the theorem; (2) the **ε = 0 attainment** through the new theorem
  at `S = T = {5}` with both flanks genuinely discharged (distances
  `5`, `6` at `δ = 1/2`); (3) the **two-sided fence** on the
  interior-gap configuration (`A = B = clusterA`, `S = {0, 11}`,
  `T = {5, 11}`, `cS = 11/2`, `rS = 11/2`, `cT = 8`, `rT = 3`): both
  `hnear` sides verified, *each* `hfar` side refuted in proved form at
  its own interior eigenvalue (the out-of-`T` `0`-mode inside A's
  cluster range — the cluster delivery's recorded obstruction,
  reusing `cpQA_fence_hfar_fails`; the out-of-`S` `5`-mode inside B's
  cluster range — the new `cpsQA_fence_hfarS_fails`), the
  hypothesis-free conclusion `≤ 2·0/(1/2) = 0` refuted at the imported
  raw lower norm `≥ 1`, and `cpsQA_fence_both_hfars_fail` collecting
  the isolation — the two-sidedness itself exercised, neither
  separation decoration; (4) the **ring-identity coherence witness**
  `cpsQA_ring_QA` — `(1 − Q)P − Q(1 − P) = P − Q` pinned entrywise on
  the witness projectors, independent of the module's private lemma.

- **Pin techniques (the run's elaboration fixes).** (1) `rw
  [l2OpNorm_transpose]` cannot fire on a goal whose norm is not yet
  syntactically under a transpose — the durable structure is an
  explicit transpose-equation `have` built from `Matrix.transpose_mul`
  plus the two symmetry equations (`clusterProjector_symmetric`
  returns an `IsSymm` proof, which is defeq to the transpose equation —
  a typed `have` bridges it, the module-side face of the QA idiom
  `show bmᵀ = bm`). (2) This pin's `le_abs : b ≤ |a| ↔ b ≤ a ∨ b ≤ -b`:
  the negative-side eigenvalue takes the *second* disjunct with the
  negated argument (`1/2 ≤ -(0-5)`), the positive-side one the first —
  and `norm_num` on a *false* arithmetic goal normalizes it to a bare
  `⊢ False`, so the diagnostic that first looks like a missing
  contradiction is actually a wrong-disjunct sign error (all seven
  first-pass QA errors were exactly this). (3) `norm_num at h` on a
  goal containing `‖A - A‖` over-unfolds the norm into a matrix
  equation — zero the norm explicitly (`rw [sub_self, norm_zero]`),
  then rewrite the arithmetic through a standalone
  `hrhs : (2:ℝ) * 0 / (1/2) = 0`, never `norm_num` a hypothesis that
  still carries a norm.

- **Verification.** `lake env lean` on both changed modules — zero
  errors, zero warnings each (the module after one fix, the QA after
  two rounds); explicit `lake build` targets — the perturbation module
  ✔ (2193/2193) and the QA module ✔ (2198/2198); `#print axioms` via
  `wip/cps_axcheck.lean` on all 19 accessible new declarations — the
  standard three only; **full `lake build` ✔ (2261 targets, "Build
  completed successfully"; zero warnings in the changed modules — the
  build log's Scaffold-tree diagnostics are the documented
  pre-existing set in untouched modules, and the docPrime notes are
  upstream Mathlib package replay notes)**; `lint_axioms` (**9**,
  unchanged), `check_citations`, `check_markdown_links` pass;
  scoreboard regenerated (**1971/9/0**, idempotent). Records updated:
  this document, `proposals/README.md` (the High row retired to the
  Delivered table; the progress paragraph rewritten), README (1971;
  the Perturbation row's symmetric-set sentence), the radar (QA axis
  synced 1953/50 → 1971/50, held 4.0), the scoreboard (all five
  verification rows + a new interpretation bullet),
  `index/map/perturbation.md` (the section note + the declaration
  row), `index/sources/davis_kahan_1970.md` (the both-gaps-at-sets
  mapping row), the execution plan, and the activity log. Nothing
  committed; the prior runs' uncommitted deliveries preserved
  untouched.

- **Open follow-ons.** None new: the YWS-literal *pairwise* set shape
  (no center/radius) remains honestly blocked exactly as recorded in
  `cluster-projector.md` Step 0 (an out-of-`S` A-eigenvalue can sit
  inside `S`'s range; whether the shape is true at all is open to this
  repo); a single-common-center consumer-facing corollary of this
  theorem is derivable on request but adds no coverage (it is the
  two-pair form at `cS = cT`, strictly fewer configurations); the YWS
  and Davis–Kahan locators carry the standing
  verify-against-physical-copy caveat.
