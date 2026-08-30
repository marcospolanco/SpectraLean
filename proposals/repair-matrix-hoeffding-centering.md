# Proposal: Repair `matrix_hoeffding`'s Missing Centering Hypothesis

**Status:** COMPLETE from birth — created and delivered 2026-08-30 by run
`20260830T183850Z-run-1` (session `ses_fac107f4cffet1fz8wSKreQOYb`),
Errata §9. The finding, the repair, and the verification all landed in
one run. This document authorizes no further Lean changes beyond its
delivery record.

## Selection context

Priority item 0: no High rows in `proposals/README.md`'s Active table
(the one Medium-High row consumer-gated; all Low rows human-decision
gated). Priority item 4 (reduce the explicit trust surface) via the
standing handoff's first-named frontier — the matrix trio's own
retirement route — whose §5-mandated Step 0 (run the adversarial
hazard-class check *before* any engine work) is what found the defect.

## The finding

The admitted `matrix_hoeffding` (Tropp 2012, Theorem 1.4) hypothesized:

- `h_meas` strong measurability,
- `h_indep` mutual independence (`iIndepFun`, since the 2026-08-29
  pairwise repair),
- `h_herm` Hermitianity,
- `h_bound` semidefinite domination `X i ω * X i ω ⪯ A i * A i`,

and **no centering clause** — its statement-difference note asserting
"The source needs no centering hypothesis, and none is imposed." The
sibling `matrix_bernstein` has carried `h_mean` since admission, and the
2026-08-30 Errata §8 audit explicitly checked the sibling safe on the
centering axis while never running the axis on this file.

The defect is a one-line counterexample: the deterministic family
`X i ≡ 1` with `A i ≡ 1` at `V = Fin 1`, `n = 2`:

- every pre-repair hypothesis holds *genuinely* — domination at equality
  (`1*1 − 1*1 = 0 ⪰ 0`), constants are strongly measurable, mutually
  independent (`iIndepFun_const_matrix_QA`), Hermitian;
- the sum is `1 + 1` with spectral norm exactly `2`, so at `t = 2` the
  tail event is all of `Ω` (probability `1`);
- the variance statistic is `‖∑ A i * A i‖ = ‖1 + 1‖ = 2`, so the bound
  is `2 · card (Fin 1) · exp (−4/4) = 2·exp(−1) < 1` (from the pinned
  `2 < exp 1`).

Conclusion: `1 ≤ 2·exp(−1) < 1` — materially false, at a deterministic
fixture, with every other hypothesis *proved*, not assumed (the standard
this repository holds refutation records to since the Walsh-character
repair).

## The repair

Insert the sibling's clause, unchanged in idiom, between `h_herm` and
`h_bound`:

```lean
(h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
```

Axiom count stays 5. The engine for the consumer side is
`integral_perturbSummand_eq_zero` in `EdgePerturbation.lean` — the
matrix-codomain clone of the deg-design's
`integral_degPerturbSummand_eq_zero`: the summand factors as
`(δ_e − p e) • L_e`, `integral_smul_const` pulls the scalar out, and
`integral_delta` (∫ δ_e ∂μ = p e) cancels the constant — honest
integrability throughout (`integrable_of_bounded_measurable`; the
matrix codomain inherits it from the scalar coefficient, so no junk
integral is reachable).

Consumer threading (all conditional loads unchanged,
`#print axioms`-verified):

- `edgePerturbation_norm_tail` — internal `hmean` discharge added;
  **public statement unchanged**;
- every downstream member (the eval/lower/λ₂ tails, both Cheeger
  windows, the unconditional dissolution trio, both Fiedler-drift
  theorems) consumes the norm tail and needed no change;
- `matrix_hoeffding_quadForm` — the generic passthrough **gains the
  matching `h_mean` hypothesis** (the only public-statement change; it
  threads the axiom's clause set by design, exactly as it did for the
  pairwise repair);
- `matrix_hoeffding_zero_QA` re-instantiated at the repaired clause set
  (the zero family's integral is `0` by `simp`).

## Degenerate-corner analysis of the repaired clause set (§5 discipline)

- `h_mean` is an integral hypothesis; the junk-integral hazard (§5) is
  guarded: `h_meas` (strong measurability) is already a hypothesis, and
  the clause itself forces the integral to equal `0` — a non-measurable
  summand cannot present a junk-zero mean *and* pass `h_meas`, unlike
  the §7 `MatrixMDS` case where measurability was nowhere forced.
- Empty index `n = 0`: the sum is `0`, `h_mean` over an empty family is
  vacuous, the tail event at `t > 0` is empty — honest (unchanged from
  the 2026-08-28 analysis).
- `Fintype.card V = 0`: still excluded by `[Nonempty V]` (the 2026-08-28
  repair); the new clause does not interact with that corner.
- Strictness: the clause is an equation (`= 0`), not an inequality — no
  boundary-value subtlety.
- The repaired set is *strictly stronger* than the pre-repair set, so
  every statement proved from the pre-repair shape remains provable from
  the repaired one *provided* its consumers' summands are centered —
  which the design's centering (`(δ_e − p_e) • L_e`) supplies and the
  new engine lemma proves.

## QA delivered (+4, `Matrix_QA.lean`'s centering-repair section)

1. `norm_one_add_one_fin1_QA` — the exact two-sided `Fin 1` norm pin
   `‖1 + 1‖ = 2`, through the eigenvector equation at `onesVec`
   (`(1 + 1) *ᵥ x = 2 • x` for every `x`), the eigenvalue sandwich
   (`evals_first_le_eigvalOf`/`eigvalOf_le_evals_last`, collapsed by
   `Fin 1`'s unique index), and both operator-norm bridges — an
   independent computation of the fixture's variance statistic, joining
   the pre-existing `l2OpNorm_one_fin1_QA`.
2. `ones_family_old_clauses_QA` — every pre-repair hypothesis clause
   *proved* at the refuting family (the falsification standard: nothing
   assumed).
3. `old_matrix_hoeffding_refuted_uncentered_QA` — the hypothesis-form
   refutation (`False` from the old conclusion at the fixture).
4. `ones_mean_ne_zero_QA` — the exclusion fence: the repaired clause
   rejects exactly the refuting family (its integral is `1 ≠ 0` on every
   probability space), the `azDrift_not_stronglyMeasurable_QA` pattern —
   the repair does real exclusion work.

## Verification

Spike first (`wip/mhrepair_spike.lean`: the refutation, the fence, the
engine lemma, and the norm pin iterated to zero errors before any shelf
edit). Then: `lake env lean` zero errors on every touched module
(`Hoeffding.lean`, `EdgePerturbation.lean`, `EdgePerturbationTail.lean`,
`EdgePerturbationDrift.lean`, `Matrix_QA.lean`), with the `Matrix_QA`
warning multiset compared against the HEAD baseline by file-pair
elaboration (`wip/mhqa_base.lean`): identical except **one** new
statement-binder warning — the repair changes info-tree attribution so
the byte-identical `matrix_hoeffding_zero_QA` statement's
variance-statistic binder newly warns, the documented MatrixMDS-precedent
pattern, recorded not appeased. Explicit `lake build` targets ✔ on the
axiom module, the engine module, both Derived modules, and both QA
modules. **`#print axioms` via `wip/mhrepair_axcheck.lean` (19
declarations)**: the four new QA declarations and the engine lemma each
exactly `propext, Classical.choice, Quot.sound`; every audited consumer
conditional on `matrix_hoeffding` alone — the same single-axiom load as
before the repair. **Full `lake build` ✔ (2407 targets) immediately
followed by `check_build_completeness.py` — 129 source files, 129 fresh
artifacts, 0 stale, 0 missing, exit 0.** `lint_axioms` (5; both PF
findings allowlisted-confirmed; no guard-surface change — the added
clause only strengthens the hypothesis set), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**3167/5/0**);
map-freshness stats sync 3163 → 3167 in both map files, SVG regenerated,
exit 0 (no proposal status header changed — this proposal has no
station).

## Technique findings for future runs

- `Matrix.add_mulVec` followed by **one** `Matrix.one_mulVec` rewrites
  both summands in one call — a second `rw` of the same lemma fails with
  the pattern already consumed; the residual goal `x + x = 2 • x` closes
  by `exact (two_smul ℝ _).symm`.
- `Fin (Fintype.card (Fin 1))` is not syntactically `Fin 1`:
  `Subsingleton` does not fire, and `⟨0, by norm_num⟩` needs the type
  ascription to fix the metavariable. The working idiom: pin one index
  by `Fin.ext` + `simp only [Fintype.card_fin] at hlt; omega` on
  `k.isLt`, and collapse `⟨card − 1, _⟩ = ⟨0, _⟩` by `ext; norm_num`.
- `Real.exp_one_gt_d9` lives in `Mathlib.Data.Complex.ExponentialBounds`
  — not in the default import closure of the concentration QA files;
  import it explicitly.
- `rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one]` (not
  `one_mul`): after the cancellation the goal is `2 * 1 = 2`. The same
  line in a differently-shelved module can elaborate the other
  association — prefer the explicit `mul_one` spelling.
- Rewriting `rw [h] at h ⊢` when the goal is `False` is a no-op that
  *fails* (the pattern is not in the goal); compute event-set equalities
  as separate `have`s and rewrite only at the hypothesis.

## Residual honestly recorded

The axiom remains admitted — the repair fixes the hypothesis *shape*;
truth stays with the cited Tropp source, and every conditional Derived
tail remains conditional on `matrix_hoeffding` and must never be
described as foundationally proved. The statement-difference note's
source-fidelity claim is corrected to what is verifiable (the source's
own symmetrization machinery requires centered summands, so its
hypothesis set must exclude the deterministic uncentered family); the
locator-level confirmation against a physical copy stays open per the
standing locator rule. The matrix trio's retirement route (Lieb-class
mgf machinery) remains the named multi-run frontier, now with a
correctly-shaped target statement.
