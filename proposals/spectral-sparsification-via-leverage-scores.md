# Proposal: Spectral Sparsification via Leverage-Score Sampling — Reopening the Blocked Phase B

**Status:** Proposed; **priority:** High. This document authorizes no Lean
changes, axiom admissions, commits, or external publication on its own —
Step 0 (the survey below) must land and be confirmed before Step 1 begins,
per the one-step discipline.

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
