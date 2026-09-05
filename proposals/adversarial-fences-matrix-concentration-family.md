# The Matrix-Concentration Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-05, runs `20260905T160854Z-run-1`
[intent + spike] and its continuation [landing]; sessions
`ses_f8db6d552ffeiYGmKkfwcqgjSH` and its successor)

## Why this family, why now

The prior terminal handoff's first named natural next move (the Active
priority table all-Low, decision-gated) was a fresh consumption survey
for a new audit target — "the audit method has no remaining named
pre-discipline QA." This run's survey (a reverse-import walk over every
public shelf, counting transitive non-QA consumers) found:

- `Probability.Concentration.Matrix` at **14 transitive non-QA
  consumers — the library's most-consumed unaudited surface**, ahead of
  Heat (8, audited) and every shelf audited since Resolvent (16,
  audited);
- second-tier unaudited: `Probability.BernoulliProduct` (7, the
  concentration subtree's own sampling engine).

The subtree is the axiom trust-center itself: home to 3 of the 4
remaining admitted axioms (`matrix_hoeffding`, `matrix_bernstein`,
`matrix_azuma_hoeffding`) plus the `MatrixMDS` structure. Its QA
carried only the repair-era refutations — the `Fin 0` corner ×3
(2026-08-28), the uncentered family (Errata §9, 2026-08-30), the
caterpillar (Errata §7, 2026-08-29) — with **no hypothesis-necessity
pass over the axioms' remaining clause surfaces**, exactly the
pre-audit state `PerronFrobenius_QA` had before the seventeenth
application. The repair history is itself the leverage argument: every
defect ever found in these axioms came from an adversarial fixture at
a hypothesis clause, and three of the axioms' clauses had never been
systematically fenced.

## The delivery

Twelve hypothesis-form fences in `Matrix_QA.lean`'s new
`AdversarialFences` section (QA-only, +53 theorems by the generator
metric, 6061 → 6114; 61 new `mc*` declarations including fixtures,
pins, and companions), each instantiating the axiom-minus-one-clause
shape at a fixture where every KEPT clause holds genuinely, deriving
`False`, tagged `-- @refutes` and axiom-independent by construction —
the repository's mechanically-independence-checked tag count rises
12 → 24.

### `matrix_hoeffding` (the `h_mean` clause was already fenced by the
2026-08-30 repair)

- **`h_herm`** at the alternating nilpotent family `X 0 = ±mcNil4`
  (`mcNil4 = !![0,4;0,0]]`, `N² = 0`, `‖N‖ ≥ 4` witnessed by the unit
  vector) on the coin space, with `A = 1`: the domination clause is
  genuine (`1 − N² = 1 ⪰ 0` through `N² = 0`), centering genuine by
  the Bernoulli mean, singleton independence trivial — and the tail
  event at `t = 4` is all of the space against `4 · e⁻⁸ < 1`. The
  asymmetric matrix escapes the Hermitian spectral pipeline entirely.
- **`h_indep`** at six IDENTICAL copies of the coin sign on `V = Fin 1`
  (`A = 1`, `t = 6`): perfect correlation makes the sum `±6`
  deterministically — full-measure tail against `2e⁻³ < 1`. The
  companion `mcHg_indep_not_iIndepFun_QA` records the failure
  mechanically: at the measurable entry cylinder `{M | M 0 0 > 1/2}`
  the two-point joint mass `1/2` is not the product `1/4`.
- **`h_bound`** at the coin family with `A = (1/10)·1` (`t = 1`): with
  the domination clause dropped, the variance proxy is unconstrained
  data — an arbitrarily small proxy buys `2e⁻⁵⁰ < 1` against the
  full-measure tail.
- **`ht`** at the constant-zero family (`A = 1`, `t = −3`): the tail
  event `{‖0‖ ≥ −3}` is all of any probability space against
  `2e^{−9/2} < 1`.

### `matrix_bernstein`

- **`h_mean`** at the deterministic uncentered family `X i = 1`
  (`n = 4`, `R = 1`, `t = 4`): every other clause genuine, the bound
  `2e^{−3/2} < 1` against the full-measure tail — the same hazard
  class Errata §9 found at the sibling.
- **`h_herm`** at three genuinely independent coordinate riders
  `X k = ±mcNil1` on the uniform Bernoulli cube (`Fin 3 → Bool`),
  `N = !![0,1;0,0]]` with `‖N‖ = 1` pinned both ways: independence by
  `iIndepFun_coord_matrix` (`mcCube_indep`), centering by the
  Bernoulli mean (`mcCube_mean`), and — through the nilpotency `N² =
  0` — the variance statistic identically zero; the all-true atom
  (mass `1/8` via the cylinder-intersection engine) has sum `3N` of
  norm `3` against `4e^{−9/2} < 1/8`.
- **`h_bound`** at the rare-value family (`99` with mass `1/100`,
  `−1` with mass `99/100`): genuinely centered (`mcRare_mean_zero`,
  the Bernoulli mean), variance statistic `99` exactly
  (`mcRare_var`, through `integral_sq_delta_sub` at `p = 1/100`), and
  the tail event at `t = 99` is the rare cylinder (mass `1/100`)
  against `2e^{−9801/264} < 1/100` — the exponent `37.1` dwarfs the
  `exp 6 > 200` anchor.
- **`h_meas` — the headline**: the variance statistic is ITSELF a junk
  integral. At the two-point trivial-σ-algebra space with `X =
  diag(1,0)/diag(0,−1)` (Hermitian of operator norm exactly one —
  both `mcDiagA_norm` and `mcDiagB_norm` pinned through the pairing
  bound and the vector-action bound — so the kept `h_herm` and
  `h_bound` at `R = 1` are genuine, and `h_mean` holds through the
  junk first moment), the SECOND moment `ω ↦ X ω · X ω` is a
  two-valued function with distinct squares (`A² = A ≠ B² = diag(0,1)`)
  — not almost-everywhere strongly measurable by the packaged
  `mcTwoBot_not_aeSM` (the `azDrift_cond_mean_zero_QA` pattern at
  `Fin 2`) — so `Σ = ∫ X²` evaluates to the junk zero and the bound
  collapses to `4e^{−3/2} < 1` against the full-measure tail at
  `t = 1`. Errata §7's mechanism class reaches the sibling axiom
  through the variance statistic, not the tail event.
- **`ht`** at the coin family with `R = 3`, `t = −9/10`: the negative
  threshold shrinks the mixed denominator `2‖Σ‖ + 2Rt/3` to `1/5` and
  the Gaussian term does the rest — `2e^{−81/20} < 1` against the
  full-measure tail (the variance statistic `1` is genuine through the
  constant square).

### `matrix_azuma_hoeffding` (the `measurable` field was already
fenced by the 2026-08-29 repair's caterpillar + exclusion fence)

- **`cond_mean_zero`** at the constant drift `X k = 1` (`R = 1`,
  `m = 8`, `t = 8`): the sum is `8` deterministically against
  `2e^{−64/64} = 2e⁻¹ < 1` — a nonzero conditional mean accumulates
  linearly while the bound's variance grows only through `m R²`.
- **`norm_bound`** at the constant drift `2•1` with the statement's
  `R = 1` (`m = 8`, `t = 16`): the sum is `16` against `2e⁻⁴ < 1`.
- **`ht`** at the constant-zero sequence (`R = 1`, `m = 1`, `t = −3`):
  `2e^{−9/8} < 1` against the full-measure tail.

### Shared infrastructure (all file-uniquely named, guard-checked)

The exp-bound helper set (`mc_two_lt_exp_one` through
`mc_thirtytwo_lt_exp_nine_halves`, riding the on-file
`Real.exp_one_gt_d9` decimal anchor and `Real.add_one_le_exp` splits);
the coin/rare/cube measures on `bernPMF` with `toMeasure_cyl` mass
computations; the two-point trivial-σ-algebra measure `mcTwoBot` with
its atom-positivity lemma; the public C*-spine vector-action route
`mcLe_norm` (the perturbation shelf's `l2OpNorm_mulVec_le` restated
without its private `pack` carrier, so QA pins can consume it) and
the entry-bound helper `mcEntry_abs_le`; the identity-norm pins
`mcOne_norm_fin1/fin2`; the ℕ/ℝ smul bridges `mcNatBridge`/
`mcNatBridge2` for `Finset.sum_const` conversions.

## Classifications and residuals

- **Kept-clause isolation**: the non-trivial kept clauses at the
  randomized designs are PROVED (the cube's independence and centering
  — `mcCube_indep`/`mcCube_mean`; the rare-value family's centering
  and exact variance statistic — `mcRare_mean_zero`/`mcRare_var`; the
  junk-variance fixture's Hermitianity and norm — `mcDiagA/B_herm`,
  `mcDiagA/B_norm`; the `h_herm` fixture's domination and centering
  through the on-file idioms). The trivial-constant kept clauses
  (const-strong-measurability, `iIndepFun_const_matrix_QA`
  singleton-independence, `PosSemidef 0/1`) at the deterministic
  fixtures are recorded here rather than packaged as separate lemmas —
  a formatting residual, not an evidence gap.
- **`[Nonempty V]`**: fenced by the repair-era `Fin 0` refutations
  (all three axioms) — not re-fenced.
- **`MatrixMDS` data fields (`R`, `X`)**: not hypotheses but data;
  the proof-carrying fields are `measurable` (fenced 2026-08-29),
  `cond_mean_zero`, `norm_bound` (both fenced here).
- **The tooling repair** (in-delivery): `scripts/check_refutation_independence.py`'s
  namespace tracker popped on ANY `end` line, so a named section's
  `end` (e.g. `end MasterBoundQA`) corrupted the namespace stack and
  the generated `#print axioms` file used bare names. Latent since the
  script's adoption; first exposed by this delivery's fences landing
  inside a named section. Repaired to name-aware `end` handling with
  the defect recorded in the script comment. Both before and after the
  repair, all tagged declarations verify axiom-independent.

## Verification

Spike-first discipline: the full delivery iterated to zero errors /
zero own warnings in `wip/mcfence_spike.lean` (across two runs — the
first landed 9 of 12 fences before hitting its step budget; the
continuation finished `h_meas`, `h_bound`, `h_herm`) before any shelf
edit; `lake env lean` on the landed module: zero errors, zero warnings
of its own (the two `unusedSectionVars` warnings verified
pre-existing at HEAD by elaborating `git show HEAD`'s copy); explicit
`lake build Scaffold.QA.Concentration.Matrix_QA` ✔; **full `lake
build` ✔ + `check_build_completeness.py` — 134 source files, 134
fresh artifacts, 0 stale, 0 missing, exit 0**; `#print axioms` via
`wip/mcfence_axcheck.lean` on all 61 new nameable declarations —
every one exactly `propext, Classical.choice, Quot.sound` (the four
`IsProbabilityMeasure` instances anonymous, audited transitively);
`lint_axioms` exit 0 (4 axioms unchanged); `check_refutation_independence`
— tag count 12 → 24, all mechanically verified axiom-independent
(after the namespace-tracker repair above); `check_public_reachability`
clean (63 modules); `check_citations` ("All axioms have proper
citations!"); `check_markdown_links` clean; `check_qa_name_uniqueness`
clean (all `mc*` names file-unique at introduction); scoreboard
regenerated (6114/4/0) with the verification row; map-freshness exit 0
after the 6061 → 6114 stats sync in both map data tables and SVG
regeneration.

## Remaining risk

None owed — QA-only plus one tooling repair; no axiom disposition
changed, no public statement changed. QA proves consequences relative
to the substrate; it does not prove the substrate (no axiom touched —
the fences refute axiom-minus-one-clause *shapes* without consuming
the axioms, as the 24-tag independence check mechanically confirms).
Honest scope: the three admitted matrix axioms' *named* hypothesis
clauses are now all fenced (repair-era + this delivery); the scalar
concentration subtree (all theorems since 2026-08-30) has not had the
same per-clause audit pass and remains available as a future target;
`BernoulliProduct` (7 consumers) is the next unaudited surface by the
survey's count.

## Next handoff

The Active table stays all-Low (decision-gated). By the survey's
numbers, the next unaudited surfaces are `BernoulliProduct` (7
transitive non-QA consumers — the sampling engine this very delivery
consumed heavily) and the scalar concentration family. The standing
frontiers (the QA axis's randomized half; the priced undirected
`walkTVPair` join; the sharp `|λ₂| = α` layer; the reverse TV → χ²
calculus) remain available, and the residual-pair rename watch
continues.
