# Icebox: Matrix Chernoff / Golden–Thompson Formalization Gap

**Status:** Technical finding, not a proposal. No priority; not something an
autonomous run should act on. Written 2026-08-19 while reviewing
`proposals/spectral-graph-sparsification.md`, whose Phase B (the actual
Spielman–Srivastava sparsification guarantee) is blocked on exactly this
gap. Kept here rather than only in that proposal because the finding is
general — it applies to any future proposal that wants a matrix
concentration tail bound stronger than what's currently admitted, not just
sparsification specifically.

## The question this answers

"Why not just implement Matrix Chernoff?" — asked directly, and worth a
real technical answer rather than a wave at "it's hard."

## Where the scalar proof breaks

The classical Chernoff bound, for independent bounded scalar random
variables, proceeds by the exponential moment method: bound
`E[exp(t · ∑ Xᵢ)]`, factor it into `∏ E[exp(t · Xᵢ)]` using independence,
bound each factor, optimize over `t`, apply Markov's inequality to
`exp(t · S)`.

The factoring step is where the matrix version breaks. `exp(A + B) =
exp(A) · exp(B)` only holds when `A` and `B` commute — independent random
matrices generally do not. This is not a technicality to route around with
more linear algebra; it is the specific reason matrix concentration is a
distinct, harder subject than scalar concentration, not "the same proof
with matrices sprinkled in."

## What actually fixes it, in the literature

Two routes exist, both genuinely deep operator theory:

- **Golden–Thompson inequality**: `Tr(exp(A + B)) ≤ Tr(exp(A) · exp(B))`
  for Hermitian `A, B`. Recovers a usable substitute for the broken
  factorization at the trace level. Typically proved via the Lie–Trotter
  product formula or operator-monotonicity arguments — not elementary.
- **Lieb's concavity theorem** (1973): what Tropp's "User-Friendly Tail
  Bounds for Matrix Martingales" (the source `spectral-graph-sparsification.md`
  itself cites) actually builds its sharpest bounds on, because
  Golden–Thompson alone gives suboptimal constants. Harder than
  Golden–Thompson; usually proved via the Hadamard three-lines
  complex-interpolation lemma. Qualifying-exam-adjacent operator theory.

## Verified against the pinned Mathlib (2026-08-19)

Checked directly, not presumed:

- **Golden–Thompson**: zero hits anywhere in `.lake/packages/mathlib`,
  under any naming.
- **Lieb's concavity theorem**: zero real hits (`grep -rli "lieb"` returns
  one match, in `Analysis/Calculus/VectorField.lean` — unrelated to this
  theorem on inspection, almost certainly a coincidental name match).
- **The matrix exponential itself does exist**:
  `Analysis/Normed/Algebra/MatrixExponential.lean`. The basic object is
  there; the trace inequalities that make it useful for concentration are
  not.

## Why this is a different tier than everything delivered this session

Courant–Fischer, Cauchy interlacing, Thomson's principle, Foster's
theorem — every one of these is finite-dimensional, deterministic linear
algebra: eigenbasis expansions, quadratic forms, dimension counting.
Matrix concentration needs all of that *plus* a working theory of
matrix-valued random variables *plus* one of the two trace inequalities
above. Neither is "more of the same technique already working today," and
both are confirmed absent from Mathlib, not merely uncited.

## Three real paths forward, honestly ordered by cost

1. **Survey `matrix_bernstein`** (`Scaffold/Mathlib/Probability/Concentration/Matrix/Bernstein.lean`,
   currently an admitted axiom). If its exact hypotheses happen to cover
   what a given consumer needs, this could dissolve the problem for free.
   Check this before anything else.
2. **Admit a new, carefully-cited matrix-Chernoff axiom.** Legitimate
   under this project's own mushy-center philosophy — a Golden-Thompson-
   derived tail bound is exactly the kind of genuinely hard, well-published
   result the axiom boundary exists for, the same category as `weyl_inequality`
   or `davis_kahan_sin_theta`. Needs its own center-out leverage case and
   citation, scoped as its own proposal (the `admit-perron-frobenius.md`
   pattern), not folded silently into a downstream consumer's build order.
3. **Prove Golden–Thompson (or Lieb's) from scratch.** Real and valuable —
   but its own multi-week-plus, research-grade formalization project, not
   a means to an end for whichever downstream proposal wanted a matrix
   concentration bound. If ever attempted, it should be scoped and
   evaluated as a formalization contribution in its own right.

## Re-survey trigger

If the pinned Mathlib version advances, re-check the Golden–Thompson and
Lieb searches above before relying on this finding — per the same
discipline `docs/8_MATHLIB_COVERAGE_MAP.md` applies to its own rows.

**Re-verified 2026-08-28** (pin unchanged, `v4.14.0`): both searches
repeated verbatim against the current `.lake/packages/mathlib` — zero
Golden–Thompson hits under any naming; the same single coincidental
`Lieb` match in `Analysis/Calculus/VectorField.lean`, unrelated on
inspection. Finding unchanged. Prompted by an external SGT-specialist
review (no code access) independently naming matrix concentration's
axiom-boundary as this repository's "largest trust-surface liability,"
raised against `proposals/README.md`'s Active-table entries for
`matrix_bernstein`'s and `matrix_hoeffding`'s consumer proposals. Path 1
of the three below has since actually happened: `matrix_bernstein` got
its first real theorem consumer (`Derived/SparsificationTail.lean`,
delivered 2026-08-27) without needing Golden–Thompson or Lieb's
concavity at all — direct evidence the ordering below is the right one,
not just a plausible guess. Paths 2 and 3 remain open and un-costed;
neither is rejected, both stay exactly as priced above.
