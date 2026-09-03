# The Adversarial Fence Audit of the Entropy Family

**Status:** COMPLETE — delivered 2026-09-03 (same-run proposal)  
**Proposal kind:** QA-only, audit-shaped (the third mixing-cascade family audited by the
method of `proposals/adversarial-fences-tv-dobrushin-engines.md` and
`proposals/adversarial-fences-lazy-family.md`)  
**Scope:** the entropy family — `Scaffold/Mathlib/InformationTheory/Entropy.lean`'s
generic KL/entropy layer, `Mixing.lean`'s entropy leg (Pinsker, the decay
forms, the nonnegativity plumbing), and `Oversmoothing.lean`'s entropy floor
(`klDiv_walkDistribution_ge_of_eigenpair`) — the mixing program's third
distance, whose QA was delivered 2026-09-01 by
`proposals/entropy-mixing-pinsker.md` *before* the adversarial-review
discipline existed and has never been independently re-read.

## Why this and why now

The lazy-family handoff named the remaining audit-shaped families (entropy,
Poisson bridge, primitivity supplier) in that order; the entropy family is
the only one of the three whose QA predates `governance/ADVERSARIAL_REVIEW.md`'s
hypothesis-necessity pass entirely. Recon confirmed the expectation: exactly
one clause of the whole family was fenced (`tvDistance_le_sqrt_half_klDiv`'s
`hq`, via `pinsker_q_guard_refuted_QA`), while 28 load-bearing clauses —
every mass clause of the generic layer, both mass clauses of Pinsker, the
rate certificate of the decay form, `hnn`/`ht` of the continuous nonneg
plumbing, `hA`/`hd` of mass conservation, and the eigenpair/mode/sup clauses
of the entropy floor — had no negative witness anywhere in the repository.

## Delivered content

**28 hypothesis-form fences** (the negation of the conclusion at a specific
instantiation, both sides pinned), each with the fixture's genuine facts
recorded beside it, across two QA sections:

- `Entropy_QA.lean`'s Section F (the generic layer, 13 fences): the
  `hq'`/`hp'` mass clauses of `klDiv_nonneg` (the doubled measure `q = (1,1)`
  makes `D = −log 2`; the half-mass `p = (1/4,1/4)` makes
  `D = −(1/2)·log 2`); the `hq` **and** `hq1` clauses of
  `klDiv_eq_zero_iff` (at `p = (1,0)`, `q = (0,1)` the junk convention
  `klTerm 1 0 = log 0 = 0` kills both summands — the divergence of two
  *different* point masses is junk-zero; at `q = (1,1)` both summands vanish
  as `log 1 = 0` plus the zero-`p` branch); the `hp'` mass clause of
  `klDiv_apply_uniform` (`2·log 2 ≠ log 2 − 0` at `p = (1,1)`); the `hp'`
  mass clauses of all three entropy statements (`H(2,2) = −4·log 2 < 0`;
  `H(1/3,1/3,1/3,1/3) = (4/3)·log 3 > log 4` at mass `4/3`, by
  `3⁴ = 81 > 64 = 4³` through `Real.log_lt_log` + `Real.log_pow` — a
  genuinely transcendental fence in a finite computation; and
  `H(1/2,…) = log 4` exactly at mass `2` while `p` is not uniform, killing
  the equality-case identification); the `hb` clause of
  `klTerm_le_sub_one_mul` (at `b = 0`: the junk `klTerm (1/2) 0 = 0` meets
  the right side `(1/2)(0−1) = −1/2`); the `hp1` clause of the entropy–χ²
  bridge (`D(3/4,3/4 ‖ 1/2,1/2) = (3/2)·log(3/2) ≥ 1/2 > 1/4 = χ²` — the
  conversion is genuinely sum-level, as the docstring claims, and the fence
  exhibits exactly the `b − a` slack the termwise shapes differ by); the
  `hq` clause of the two-block log-sum bound (`klTerm 1 1 = 0 > −(1/2)·log 2`
  at `q = (0,1)`); and both strict-positivity clauses of the binary
  two-point Pinsker engine (`b = 0` and `b = 1` both collapse the right side
  to `−(1/2)·log 2` against the left side `1/2`).
- `Mixing_QA.lean`'s `EntropyFences` section (the walk level, 15 fences):
  both mass clauses of **Pinsker's inequality** (a negative divergence makes
  the junk square root `0`, so the dropped statements read `1/4 ≤ 0` and
  `1/2 ≤ 0`); the `hnn` clause of `walkDensity_nonneg` (at `negOffAdj`:
  `h(1) = −1/(1/2) = −2`); the `hnn` clauses of `contWalkDensity_nonneg`
  and `contWalkDistribution_nonneg` (at `negOffAdj`, `t = 1`: the
  closed-form heat kernel `1 + ((e²−1)/2)•(−L)` makes `h(1) = 1 − e² < 0`,
  through `Heat.lean`'s `exp_eq_one_add_of_mul_self_eq_smul` engine — the
  negative off-diagonal entries of `L_walk = 1 − A` survive the exponential);
  the `ht` clauses of both continuous nonneg statements (on the genuine
  `K₂` at `t = −1` — the *backward* semigroup: the same engine at the
  exponent `+L` gives `h(1) = 1 − e² < 0`); the `hA` clause of
  `sum_contWalkDistribution` (at the new asymmetric swap
  `asymSwapAdj = !![2,0;4,0]` — nonnegative, positive degrees, asymmetric;
  its walk Laplacian `[[0,0],[−1,1]]` is *idempotent*, so the heat kernel
  evaluates in closed form and the law's mass at `t = 1` is
  `3 − 2e^{−1} ≠ 1`); the `hd` clauses of `sum_contWalkDistribution` and
  `klDiv_contWalkDistribution_le` (at `zdAdj`: the start density is the
  junk `1/0 = 0`, the law is identically zero, mass `0 ≠ 1` — and the decay
  bound's right side carries the junk `(0⁻¹ − 1) = −1`, so the statement
  reads `0 ≤ −e^{−2λ₂}` for *whatever* `λ₂` is, by `exp_pos` alone, no
  eigenvalue pin needed); the `hrate` clause of `klDiv_walkDistribution_le`
  (on the genuine triangle at the failing certificate `r = 1/8`: the
  statement reads `log(3/2) ≤ 1/32`, refuted by Gibbs' `log(3/2) ≥ 1/3`,
  with the certificate's failure witnessed by the existing
  `tri_exists_pos_mode_QA`); and the four clauses of the **entropy floor**
  `klDiv_walkDistribution_ge_of_eigenpair`: `hμ` (the kernel eigenpair
  `(0, ![1,1,1])` is genuine and the sup bound attained with equality, but
  the floor reads `1/2 > (1/2)·log(9/8)`), `hv` (at `μ = 3` with the
  non-eigenvector `e₀` the floor inflates to `2 > log(3/2)` — without the
  eigen-equation the caller can amplify the mode factor arbitrarily), `hc`
  (the sup bound must *dominate*: at the undershooting
  `c = (√2)⁻¹/2` the floor inflates to `8`), and `hA` (at `asymSwapAdj`'s
  genuine `(1, ![0,1])` eigenpair of its asymmetric normalized Laplacian
  `[[0,0],[−√2,1]]`, at `t = 0` from `x = 1`: the floor reads
  `1/2 > D(δ₁ ‖ π) = log(3/2)` — strictly, via `log < x − 1` — because the
  floor's truth relies on `L_sym`'s self-adjointness for the Parseval step).

## Recorded non-fenceable, with reasons

- **Junk log-of-negative contamination** (no clean fixture exists): the
  `hp`/`ha` clauses of `klDiv_nonneg`, `klDiv_eq_zero_iff`,
  `tvDistance_le_sqrt_half_klDiv`, `klDiv_le_sum_sq_div`,
  `klTerm_le_sub_one_mul`, and `sum_klTerm_ge_klTerm` — a negative `p`
  entry puts `log(negative)` in every term.
- **Empty-type corners vacuous**: the `hn` (`0 < card`) clauses of
  `shannonEntropy_*` and `klDiv_apply_uniform` — no mass-`1` vector exists
  on an empty type, so the dropped hypothesis set is unsatisfiable.
- `klDiv_walkDistribution_le`'s `hconn` is proof-shaped, not truth-shaped
  (on disconnected input `λ₂ = 0` collapses the rate to `1` and the bound
  stays true — the same class as the lazy audit's `hconn` verdict); its
  `hnn` is contaminated; its `hA` is structural (`eigvalOf` needs the
  symmetry proof to typecheck); its `hd` is **implied by `hconn + hnn` at
  card ≥ 2** (connectivity forces an incident edge at every vertex) — the
  only genuine corner is the 1-vertex graph, where the bound's right side
  is the junk `−1` and the statement is refutable in principle, but the
  refutation needs a `1×1` `eigvalOf` pin — the same no-basis-control cost
  the lazy audit's `k2_eigvalOf_cases_QA` route avoids; recorded unfenced.
- `klDiv_contWalkDistribution_le`: `hcard` (the 1-vertex corner satisfies
  the conclusion), `ht` (the bound inflates at negative time — the
  conclusion survives), `hnn` (contaminated), `hA` (structural —
  `secondEval` typechecking).
- **Removable-hypothesis findings** (recorded, not acted on, matching the
  lazy audit's treatment): `walkDensity_nonneg`'s `hd` (`D⁻¹A` stays
  entrywise nonnegative at zero degrees since `(deg i)⁻¹ ≥ 0` including
  the junk `0⁻¹ = 0` — the plain twin of the lazy audit's finding); and the
  `hA` clauses of `contWalkDensity_nonneg` and
  `contWalkDistribution_nonneg` **given `hnn`** — the heat kernel is
  `e^{−t}·e^{tP}` with `P ≥ 0` entrywise, hence nonnegative for *every*
  nonnegative adjacency, symmetric or not; the delivered proofs use `hA`
  through the Poissonization identity, the truth does not.
- `sum_contWalkDistribution`'s `hnn`: the mass identity survives negative
  entries at symmetric fixtures (`π` remains stationary at `negOffAdj`) —
  only asymmetry (the fenced `hA`) or zero degrees (the fenced `hd`) break
  it.
- The entropy floor's `hc0` (at `c = 0` the sup bound forces `v' = 0` and
  the floor collapses to the junk `0 ≤ D`) and its `hd` (at `zdAdj` every
  zero-degree conjugate collapses to `v' = 0`, making `hc0` unsatisfiable
  alongside a genuine `hv`/`hμ`); its `hnn` is contaminated.

## Technique findings

1. **Entry pins fire under `rw` but not as `simp only` rules.** Ground
   equations of matrix entries (`asym_L_00 : walkLaplacian asymSwapAdj 0 0 = 0`)
   placed in `simp only` lists did not rewrite the goal's occurrences, while
   the same equations in `rw` chains did — consistently, in all three of
   this run's entrywise products. Rule of thumb: entry pins belong in `rw`.
2. **The Fin-literal shape mismatch, third confirmation, now for matrix
   entries.** `fin_cases` goals carry `⟨0, ⋯⟩`-tagged literals that do not
   match OfNat literals in stated pins; the repo idiom
   `rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]` is
   load-bearing for *every* 2×2 entry computation (the lazy audit found it
   for `fin_cases` id-motives; here it recurs for adjacency/Laplacian
   entries).
3. `Matrix.mul_apply` leaves the `⬝ᵥ` — `Matrix.dotProduct` must accompany
   it in every entrywise product computation.
4. **Mixed-precedence division defeats `div_self`.** `a * b / c` parses as
   `(a * b) / c`, so a `div_self` rewrite never applies to the subterm it
   visually targets. The working pattern: prove a *value pin*
   (`have hval : <the exact statement subterm> = <numeral>`) with
   `abs_of_pos`/`abs_of_nonpos` + `norm_num` (+ `field_simp` when
   transcendentals survive), then `rw [hval]` into the hypothesis.
5. `(by norm_num : (2:ℝ) ≠ 0)` as a lemma argument leaves a metavariable
   hole (`⊢ ¬?m = 0`); annotate with `show`:
   `(show (2:ℝ) ≠ 0 by norm_num)`.
6. `rw`'s trailing `rfl` auto-close is unstable — a following `ring` may
   find "no goals to be solved"; iterate empirically per site (this cost
   several flip-flops this run before the pattern was identified).
7. Vector-valued `mulVec` results need `Pi.add_apply`/`Pi.smul_apply`,
   *not* the Matrix entry lemmas (`Matrix.add_apply` is for matrices).
8. `Matrix.mulVec_zero` needs the zero vector syntactically — a literal
   `![0,0]` must be `show`-converted to `0` before the rewrite fires.

## Verification

Spike first (`wip/entropyfences_spike.lean` — the full 143-declaration
delivery, iterated to zero errors/zero warnings before any shelf edit);
`lake env lean` on both touched QA modules (Entropy_QA absolutely clean;
Mixing_QA's three `ring_nf` hints and the ProjectorDrift unused-variable
warning confirmed pre-existing by elaborating the HEAD baseline copies);
explicit `lake build Scaffold.QA.InformationTheory.Entropy_QA
Scaffold.QA.SpectralGraph.Mixing_QA` ✔; **the 143-declaration axiom audit**
(`#print axioms` via `wip/entropyfences_axcheck.lean` against the landed
modules — 54 Entropy_QA + 89 Mixing_QA declarations: every one exactly
`propext, Classical.choice, Quot.sound`, pure hard crust; no `-- @refutes`
tags, since these refute *theorem* instantiations and consume nothing
admitted); **full `lake build` ✔ immediately followed by
`check_build_completeness.py` — 133 source files, 133 fresh artifacts, 0
stale, 0 missing, exit 0**; `lint_axioms` exit 0 (4 current axioms,
unchanged); `check_refutation_independence` (9-tag clean — no tags touched);
`check_public_reachability` clean (63 repo modules); `check_citations`
("All axioms have proper citations!"); `check_markdown_links` clean;
`check_backlog_freshness` clean; scoreboard regenerated (**4012/4/0**);
map-freshness exit 0 after the stats sync.

Drive-by (same file, one word): the lazy-audit section header in
`Mixing_QA.lean` said "eight load-bearing hypotheses" where its own
delivery record and proposal both say ten — corrected to ten.

## Remaining risk

None owed by the delivery — QA-only, no axiom disposition changed, no
public statement changed. Honest scope: the audit covered exactly one
family; the Poisson-bridge and primitivity-supplier families remain the
open audit frontiers with the method now thrice exercised; the recorded
non-fenceables name their mechanisms precisely enough that a future engine
(e.g. a `1×1`/small-`eigvalOf` pin route, or a decided policy on junk
log-of-negative fixtures) could reopen them deliberately.
