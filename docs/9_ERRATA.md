# Errata

**Status:** Canonical, append-only record of every instance where an
admitted axiom, or a theorem statement already sitting in the tree, was
found to be **materially false or internally inconsistent** — not
merely unproved — and repaired.

## Why this document exists

Scaffold's trust argument (`docs/2_ARCHITECTURE.md` §1) is not "nothing
here is ever wrong." It is: assumptions are explicit, cited, and
narrow; everything downstream is Lean-checked against them; and when
an assumption turns out to be wrong, that gets found, fixed in the
open, and recorded — rather than silently patched or left for a reader
to discover by accident. `docs/1_STRATEGY.md` § "Load-bearing growth"
already states the principle ("a layer that stays standing after real
weight is placed on it is evidence; a layer nobody has tested is not")
but principle is not the same as an audit trail a consumer can actually
read. This document is that trail.

**What belongs here:** an admitted `axiom`, or a `theorem` statement,
that was demonstrated false or inconsistent — by a concrete
counterexample or a derivation of `False` — after already being part
of the public API, together with how it was found, what was wrong, and
how it was repaired.

**What does not belong here:** a first proof of a previously-honest
axiom (an upstream-replacement retirement, `docs/2_ARCHITECTURE.md`
§9 — nothing was ever wrong, the axiom just became a theorem), a
newly-discovered gap that was never claimed proved, or a documentation/
tooling bug (those have their own record where relevant — e.g. the
transit-map staleness incident in
`docs/arch/commit-steward-protocol.md` §1 — because the claim being
corrected there is about a status label, not a mathematical
statement).

**How to read the count.** Six entries below is not a small number,
and it should not be read as one. It is also not evidence the project
is unusually error-prone — every entry was found by the project's own
deliberate practice of building adversarial fixtures against its own
axioms (`docs/1_STRATEGY.md`'s "load-bearing growth" policy), not by
an external user hitting the bug in production. Absence of an axiom
from this list is evidence nobody has yet built the fixture that would
break it, not evidence none exists — see §6.

## 1. Woodbury matrix identity

- **Found:** 2026-08-18.
- **What was wrong:** the admitted axiom's middle factor was
  `(C + V A⁻¹ U)⁻¹`, with no invertibility hypothesis on `C`. False:
  at the scalar instance `A = 1, U = V = 1, C = 0`, every hypothesis
  holds and the two sides evaluate to `1` and `0`.
- **How it was found:** a QA witness built specifically to instantiate
  the axiom at values chosen to break it —
  `Scaffold.QA.Core.MatrixUpdates_QA.old_woodbury_identity_refuted_QA`.
- **Repair:** same day. Middle factor corrected to `C⁻¹ + V A⁻¹ U`
  with three explicit `IsUnit` determinant hypotheses; the corrected
  statement was then *proved* from Mathlib's `Matrix.invOf_add_mul_mul`
  at zero further axiom cost — the axiom didn't just get a narrower
  hypothesis, it was retired outright the same day.
- **Commit:** `f66e5fb` — `fix(core): retire false Woodbury identity`.
- **Source:** `Scaffold/Mathlib/Core/MatrixUpdates.lean`'s own
  "Repair record" docstring, which the theorem still carries.
- **Status:** resolved.

## 2. Cheeger's hard direction (`cheeger_lower_bound`)

- **Found:** 2026-08-18.
- **What was wrong:** the admitted axiom's spectral side, instantiated
  on `K₂`, evaluated to `1/2 ≤ 0` — false regardless of any hypothesis
  interpretation.
- **How it was found:** a QA witness engineered to knock the axiom
  over — `old_cheeger_lower_bound_refuted_QA`, cited by name in
  `docs/1_STRATEGY.md` as the load-bearing-growth principle's own
  worked example.
- **Repair:** the spectral side was restated the same day at the
  source-faithful `secondEval (L_sym)` shape (replacing a
  `lambda2`-composed side QA had already refuted). The corrected
  axiom was later proved outright and retired — `φ²/2 ≤ λ₂` from the
  median-split route (Cauchy–Schwarz core, interval-integral co-area
  core, median/level-set assembly) — at its unchanged corrected
  statement, explicit axiom count 10 → 9.
- **Commit:** `f4ecf6c` — `feat(sgt): retire cheeger_lower_bound;
  deliver Fiedler Phase B certified conductance cut`.
- **Source:** `docs/1_STRATEGY.md` § "Load-bearing growth"; `docs/7_SGT_RADAR.md`
  axis 4's evidence entry.
- **Status:** resolved.

## 3. Subgaussian tail bound (`subgaussian_tail_bound`)

- **Found:** 2026-08-22, during the mandated Step 0 spike of
  `proposals/prove-subgaussian-tail-bound.md`.
- **What was wrong:** the pre-repair hypothesis
  `h_sub : subgaussianNorm X μ ≤ K` was false-enabling in two
  independent ways:
  1. `Real.sInf_empty` vacuity — at `μ = (3:ℝ≥0∞) • δ₀` (total mass
     `3`), every candidate MGF integral exceeds `2`, so the defining
     set is empty and `subgaussianNorm` evaluates to the junk value
     `0`, making `h_sub` hold for *every* `K ≥ 0` while the conclusion
     at `t = 0, K = 1` reads `3 ≤ 2` — false.
  2. `MeasureTheory.integral_undef` junk-zero — for a heavy-tailed `X`
     whose MGF is non-integrable at every scale, the same defining
     integral is the junk value `0`, making the set *full* rather than
     empty, `subgaussianNorm` again `0`, and the old conclusion falsely
     certify subgaussian tails for a polynomial-tailed variable.
- **How it was found:** the proposal's own mandated Step 0 spike,
  which is required to run before any shelf edit on this class of
  axiom — the spike's purpose is exactly to surface this kind of
  defect before it's built on.
- **Repair:** same run. `h_sub` replaced by the honest moment content
  Markov's inequality actually needs — `h_int : Integrable (fun ω =>
  exp (X ω²/K²)) μ` and `h_mom : ∫ ω, exp (X ω²/K²) ∂μ ≤ 2` — at the
  same name and conclusion (including the `2K²` constant). Proved via
  Markov's inequality plus a half-scale measurability transfer.
  Explicit axiom count 10 → 9.
- **Commit:** `d9b5678` — `feat(sgt): retire subgaussian_tail_bound;
  directed graph operators steps 0-1`.
- **Source:** `proposals/prove-subgaussian-tail-bound.md`'s delivery
  record (full mechanism, QA refutation family, and technique notes).
- **Status:** resolved.

## 4. Hoeffding's lemma (`hoeffding_lemma`)

- **Found:** 2026-08-28, during
  `proposals/audit-scalar-concentration-integrability-hazard.md`'s
  Step 0 — an audit opened specifically because entry 3 above left an
  explicit, six-day-old, unaddressed warning that sibling axioms in
  the same file might carry the same junk-integral hazard.
- **What was wrong:** two independent defects, neither the mechanism
  the audit went in looking for:
  1. **Wrong classical constant.** The axiom's conclusion used
     `subgaussianNorm X μ ≤ a`; the correct constant is `√6·a`.
     Refuted at a genuine, non-junk fair-coin Rademacher fixture where
     every hypothesis holds honestly and `subgaussianNorm ≥ 6/5 > 1 =
     a`.
  2. **Missing `IsProbabilityMeasure` guard.** With no constraint on
     the measure's total mass, no finite replacement constant repairs
     the statement — refuted at a mass-`19/10` rescaling with the mean
     still genuinely zero, forcing `subgaussianNorm ≥ 21/5`.
- **How it was found:** the audit's own structural read predicted
  `hoeffding_lemma` was the single highest-suspicion candidate of the
  four audited (same file as entry 3, missing both structural guards
  the other three carried) — but explicitly recorded, before checking,
  that the two *already-known* junk mechanisms from entry 3 probably
  did *not* apply here (the conclusion itself collapses to the junk
  value in the same direction as the hypothesis, so they can't
  decouple the way they did in entry 3). That hedge was correct — and
  the axiom was still false, via two mechanisms nobody had hypothesized
  in advance. The lesson, recorded in the audit's own delivery record:
  ruling out a suspected failure mode is not the same as clearing an
  axiom.
- **Repair:** same run. `[IsProbabilityMeasure μ]` added; constant
  corrected `a → √6·a`, derived from the two-sided tail / layer-cake
  argument at `K² = 6a²`. Same name; the axiom was not retired to a
  theorem, only repaired.
- **Commit:** `a1e59ac` — `feat(sgt): two axiom correctness repairs
  (hoeffding_lemma, matrix concentration trio) + transit-map freshness
  tooling`.
- **Source:** `proposals/audit-scalar-concentration-integrability-hazard.md`'s
  delivery record.
- **Status:** resolved.

## 5. The matrix concentration trio (`matrix_hoeffding`, `matrix_bernstein`, `matrix_azuma_hoeffding`)

- **Found:** 2026-08-28, during the Step 0 of
  `proposals/matrix-hoeffding-spectral-gap-estimation.md` — the very
  first thing checked before building `matrix_hoeffding`'s intended
  consumer.
- **What was wrong:** all three axioms were **inconsistent**, not
  merely false on some instance — a strictly worse defect. At
  `Fintype.card V = 0, t = 0`, the tail event is all of `Ω` (a
  probability measure gives it mass `1`), while the dimension prefactor
  `2 · card V` collapses to `0`; every hypothesis remains satisfiable
  at this corner, so each instantiated axiom reads `1 ≤ 0`. An
  inconsistent hypothesis set can be used to derive `False` inside
  Lean — worse than a merely-false statement, because it poisons
  everything conditional on it, silently, whether or not any consumer
  happens to exercise the bad corner.
- **How it was found:** the same Step-0-before-any-shelf-edit
  discipline as entry 3 and entry 4 — checked before, not after, a
  consumer was built on top.
- **Repair:** same run, all three axioms simultaneously. An explicit
  `[Nonempty V]` guard was added to each — matching the dimension
  assumption the cited Tropp source (*"User-friendly tail bounds for
  sums of random matrices"*, FoCM 2012) carries implicitly for
  dimension-`d` matrices. The guard was threaded through every existing
  consumer (`Derived/EventStream.lean`, `Derived/ProjectorDrift.lean`,
  `Derived/SparsificationTail.lean`) without changing their proofs —
  in `ProjectorDrift.lean`'s case, derived internally from an existing
  hypothesis rather than as a new public argument.
- **Commit:** `a1e59ac` (same commit as entry 4 — both found and
  repaired in the same run).
- **Source:** `proposals/matrix-hoeffding-spectral-gap-estimation.md`'s
  delivery record.
- **Status:** resolved.

## 6. The pairwise-independence defect (six axioms)

- **Found:** 2026-08-29.
- **What was wrong:** `hoeffding_inequality`, `hoeffding_empirical`,
  `bernstein_inequality`, `bernstein_bounded_variance`,
  `matrix_hoeffding`, and `matrix_bernstein` all hypothesized only
  **pairwise** `IndepFun`. Pairwise independence is not sufficient for
  the classical Hoeffding/Bernstein/matrix-Chernoff proofs, which need
  the mutual independence of the whole family
  (`iIndepFun`/`ProbabilityTheory.iIndepFun`) — the standard textbook
  gap between "pairwise" and "mutual." Refuted concretely: the 15
  nontrivial Walsh/XOR-parity characters of 4 fair coin flips (on
  `Fin 4 → Bool`) are pairwise independent, but their sum is `15` on
  the all-false outcome (probability `1/16`) and `−1` everywhere else
  — far more concentrated than a pairwise-only tail bound permits,
  refuting each axiom's conclusion at `t = 15` by a large factor.
- **How it was found:** this gap was named and explicitly deferred —
  not discovered blind — on 2026-08-22, in
  `proposals/prove-subgaussian-tail-bound.md`'s own scoping section
  ("Why this axiom, not one of the other nine"): "their hypothesis is
  only pairwise independence... `IndepFun.mgf_add` is two-at-a-time...
  That mismatch needs its own Step 0 before anyone touches either
  axiom; it is not scoped by this proposal." Seven days and several
  real theorem consumers later (entries built on `hoeffding_inequality`
  and the matrix trio in the interim — see the vertex-degree
  concentration and edge-perturbation work of 2026-08-28/29), that
  deferred Step 0 was finally run, confirming the concern was real for
  all six axioms sharing the pattern.
- **Repair:** complete, 2026-08-29 (runs `20260829T173340Z-run-1`,
  `20260829T195611Z-run-1`, and `20260829T222414Z-run-1`). All six axiom
  signatures tightened from pairwise `IndepFun` to `iIndepFun` (mutual
  independence — the hypothesis shape the cited Hoeffding/Bernstein/
  matrix-Chernoff sources actually carry); mutual-independence engines
  added to `BernoulliProduct.lean` (`toMeasure_cyl_inter`,
  `iIndepFun_coord`, `iIndepFun_of_injective`, `iIndepFun_coord_apply`,
  `iIndepFun_coord_matrix`) and `IIDProduct.lean` (the `iidPMF` analogue
  plus `iIndepFun_indicator_coord`); every consumer clause site threaded
  (`EdgePerturbation`, `Sparsification`, `EmpiricalStationary`, and the
  three Derived tail modules — public statements unchanged, `#print
  axioms` verifying each Derived tail conditional on its own axiom
  alone); the Walsh refutation family recorded in QA
  (`Scaffold/QA/Concentration/PairwiseIndependence_QA.lean`, six
  hypothesis-form refutations at exactly the standard three axioms — a
  refutation cannot carry the axiom it refutes); the pre-existing
  pairwise lemmas retained on the shelf as the refutation records'
  interface. The full verification ladder passed on the repaired tree
  (129/129 build completeness, axiom lint, citations, links, scoreboard
  3099, map freshness). Not yet committed at this entry's update —
  autonomous runs do not commit; the commit reference lands with the
  operator's commit per `docs/arch/commit-steward-protocol.md`.
- **Source:** `proposals/pairwise-independence-concentration-repair.md`
  (the delivery record with the full witness mechanics and consumer
  threading inventory); `docs/AGENT_ACTIVITY.md`'s 2026-08-29 entries
  (17:33:40Z, 19:56:11Z, 22:24:14Z).
- **Status:** resolved.

## Related: process and tooling self-corrections

A narrower category — not an axiom or theorem found false, but a
*documented claim about the process itself* found wrong — is tracked
separately since the audience and stakes differ:

- The transit map's hand-maintained status data drifted for four days
  while its own regeneration hook ran on every commit
  (`docs/arch/commit-steward-protocol.md` §1, commit `9c32a77`).
- A recorded honesty note claiming "no dropped-guard refutation
  fixture exists at fixture scale" for the edge-perturbation
  sweep-cut tail was itself found wrong via a different route
  (disconnectedness, not the eigenvalue floor originally tried) and
  corrected on the record, 2026-08-29 (`docs/AGENT_ACTIVITY.md`,
  the C₄ dropped-guard entry).
- The degenerate-corner guard linter's own acceptance-bar fixtures
  caught the linter itself blind to Greek identifiers (`μ`, `Ω`)
  before it shipped (`proposals/lint-axiom-degenerate-corner-guards.md`'s
  delivery record, commit `f94bc12`).

These are evidence of the same discipline applied to a different
surface, not mathematical errata, and are not numbered alongside §1–6.

## How this document is maintained

Any `docs/AGENT_ACTIVITY.md` entry, or any commit-steward verification
pass, that finds an admitted axiom or an existing theorem statement
materially false or inconsistent must add an entry here in the same
verification pass that repairs it (or, if the repair spans multiple
runs, an open entry per §6's own example, updated when it closes). An
axiom repair that never gets an entry here defeats the purpose of
keeping this list at all.

## See also

- `docs/2_ARCHITECTURE.md` §9 (Upstream replacement lifecycle) — the
  general policy this document is the evidence trail for; "an
  emergency removal is appropriate for a materially false statement,
  an inconsistent assumption set, or a declaration that creates
  unacceptable trust exposure" is the policy line every entry above
  instantiates.
- `docs/1_STRATEGY.md` § "Load-bearing growth: the path to
  falsifiability" — the strategic principle (build things whose
  success is contingent on the substrate being right) that produced
  most of the discoveries above.
- `docs/arch/commit-steward-protocol.md` — the verification procedure
  that runs before any of the repairs above are committed.
