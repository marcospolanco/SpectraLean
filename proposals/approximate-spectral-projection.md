# Proposal: Approximate Spectral Projection with Error Bounds

**Status:** Step 0 DELIVERED 2026-08-23 (run `20260823T132040Z-run-1`):
the **Lanczos/Kaniel–Paige shape is CLEARED** as the one tractable
shape — the exact finite-`k` statement, the full machinery checklist,
and a green axiom-clean skeleton spike are recorded in the Step-0
record below; Nyström is deferred with its obstruction named, and the
Chebyshev-filter shape is recorded as the natural second consumer of
the same Chebyshev layer (to be attempted only in its own run). Step 1
(the interface layer + spectral discharge + statement + QA, priced
below at ~600–800 lines across 2–3 runs) is authorized on the cleared
shape only. No new axioms anywhere in this proposal. Original scoping
header: proposed 2026-08-19, priority **Medium**, contingent on Step 0;
assistant's assessment of project direction, requested 2026-08-19,
promoted from `sgt-gaps.md` item 7. Authorizes no axiom admissions or
external publication.

## Clean-room boundary

Internal prioritization and analysis. If counsel approves a public
repository export, restate from standard numerical-linear-algebra sources
(Saad; Trefethen & Bau). Do not copy this proposal verbatim.

Assessed from `Scaffold/Mathlib/GraphTheory/Spectral.lean`
(`spectralProjector`, the exact eigendecomposition machinery this
proposal's subject approximates), `icebox/lyapunov-stability-
formalization-gap.md` (the closest precedent in this repository for
"a genuinely different kind of math than what's already here"), and a
search of the pinned Mathlib for Lanczos/Chebyshev/Nyström machinery
(none found).

## Step 0 record (2026-08-23)

### The exact finite-`k` statement (Lanczos/Kaniel–Paige, top eigenvalue)

Let `M : Matrix V V ℝ` be symmetric with largest eigenvalue `λ₁` and
let `λ₂` bound every other eigenvalue (`λ₂ < λ₁`; equivalently the top
eigenspace is simple — this is a *hypothesis*, with the guard QA'd by
refutation), `λₙ` the smallest eigenvalue. Fix `k ≥ 1` and a starting
vector `b` with unit norm, decomposed along the top eigenvector `u`
(`‖u‖ = 1`) as `b = cos φ • u + sin φ • g`, `g ⊥ u`. Then the `k`-th
Krylov space `K_k(M, b) = span{b, M b, …, Mᵏ⁻¹b}` contains a nonzero
`x` with

```
λ₁ − R_M(x) ≤ (λ₁ − λₙ) · tan²φ / (T_{k−1}(1 + 2γ))²,
  γ = (λ₁ − λ₂) / (λ₂ − λₙ),
```

where `T_{k−1}` is the Chebyshev polynomial and the affine map
`w(λ) = (2λ − λ₂ − λₙ)/(λ₂ − λₙ)` sends the "spectral band"
`[λₙ, λ₂]` to `[−1, 1]` and `λ₁` to `1 + 2γ`. This is the classical
Kaniel–Paige bound (Saad, *Numerical Methods for Large Eigenvalue
Problems*, §6; citation to be verified against the physical copy
before any committed use, per this proposal's clean-room note).

**Statement-shape decisions recorded before Step 1:**

- **Existence form, no sup.** The theorem asserts `∃ x ∈ K_k`; the
  Rayleigh–Ritz *value* `θ_k = sup{R_M(y) : y ∈ K_k}` (what the
  tridiagonal Lanczos recurrence computes in exact arithmetic) is
  equivalent for this bound but drags in a real-number `sSup` over an
  uncountable set for no mathematical gain. The sup/definition form,
  if a consumer needs it, is a one-line corollary of the existence
  form.
- **No Lanczos iteration.** The three-term recurrence, the
  tridiagonal `T_k = Qᵀ M Q`, and finite-precision orthogonality loss
  are all *outside this statement*. What is certified is the exact-
  arithmetic variational content: polynomial images of `b` attain the
  bound. The algorithm-to-quantity correspondence is deliberately not
  claimed.
- **Chebyshev value left explicit.** `T_{k−1}(1+2γ)` stays in the
  statement; the exponential-in-`k` lower bound on it (via
  `cosh(k · arcosh(1+2γ))`) is a non-vacuity corollary, not part of
  the bound.
- **`λ₁`/`λ₂`/`λₙ` enter as hypotheses** (`λ₂`-bounds-every-non-top-
  eigenvalue + strict `λ₂ < λ₁`), not by indexing `evals`; deriving
  them from the sorted spectrum is consumer/QA work. (Naming note:
  `λ₁` is not a lexable Lean identifier — `λ` is reserved; the Lean
  names will differ.)

### Machinery checklist — every dependency verified against pin and shelf

Present on the shelf (all proved, all consumed by the spike):

- the orthonormal eigenbasis `eigvecOf`/`eigvalOf` (`eigvecOf_inner`,
  `eigvecOf_complete`), `quadForm_eigvalOf` (eigenvalue-weighted
  quadratic form), `dotProduct_eigvecOf` (Parseval) — together these
  discharge the skeleton's spectral-layer hypotheses;
- the Rayleigh sandwich both ends: `quadForm_le_evals_last`
  (`xᵀMx ≤ λ_max‖x‖²`) and `evals_first_mul_dotProduct_le_quadForm`
  (`λ_min‖x‖² ≤ xᵀMx`) — the skeleton's `hbottom`;
- `rayleigh` (junk-0 total Rayleigh quotient), and `Heat`'s
  `pow_mulVec_smul` (`(Mⁿ) *ᵥ v = μⁿ • v` at an eigenvector).

Present in the pin:

- `Polynomial.Chebyshev.T` with `T_real_cos`
  (`T_n(cos θ) = cos (n θ)`) — the entire Chebyshev band bound
  `|T_n| ≤ 1` on `[−1,1]` follows from it at `θ = arccos x` with
  `Real.cos_arccos` + `Real.cos_mem_Icc` (**proved in the spike**,
  6 lines);
- the polynomial-action layer: `Algebra ℝ (Matrix V V ℝ)`,
  `Polynomial.aeval_monomial`, `as_sum_range'`, `eval_eq_sum_range`
  — `p(M) v = p(μ) • v` at an eigenvector and `p(M) b ∈ K_k` are
  both **proved in the spike**;
- the `dotProduct`/`mulVec` additive lemmas (`add_dotProduct`,
  `dotProduct_add`, `smul_dotProduct`, `dotProduct_smul`,
  `mulVec_add`, `mulVec_smul`, `smul_mulVec_assoc`,
  `mulVec_mulVec`).

Shallow gaps, all priced (none blocks):

- **no `Matrix.sum_mulVec`** in the pin (the `(∑ Aᵢ) *ᵥ b = ∑ (Aᵢ *ᵥ b)`
  push) — a 4-line `Finset.induction`, **proved in the spike**;
- **no `natDegree (T ℝ n) = n`** lemma found — needs a short induction
  (or `Polynomial.natDegree_comp` bound for the affine-composed band
  polynomial, giving `natDegree < k` for `T_{k−1} ∘ w`); ~15 lines;
- **no cosh-form growth lemma** for `T` beyond `1` — only needed for
  the non-vacuity corollary `1 ≤ T_m(x)` at `x ≥ 1` (two-step
  induction from `T_add_two`); ~25 lines, not on the critical path.

### The skeleton spike (the composition test, hypothesis form)

`wip/asp_step0_spike.lean` (git-ignored, per the Cheeger Step-0
precedent) — **four declarations, all green, every `#print axioms` the
standard three** (`propext, Classical.choice, Quot.sound`):

1. `abs_T_eval_le_one` — the Chebyshev band bound (real proof);
2. `aeval_mulVec_eq_eval_smul` — polynomial action on eigenvectors
   (real proof, consuming `Heat.pow_mulVec_smul`);
3. `aeval_mulVec_mem_krylovSpan` — Krylov-span membership (real
   proof);
4. `kanielPaigeSkeleton` — the full bound assembled in hypothesis
   form: the spectral layer enters as five *named* discharge sites
   (`hp₁ : p.eval λ₁ = Tv`, `horth`, `horthM` — orthogonal-
   complement invariance under `M`, dischargeable via symmetry —
   `hbottom`, `hband`), and the skeleton proves the exact bound
   `λ₁ − R_M(x) ≤ (λ₁−λₙ)·s²/(c²Tv²)` composes from exactly those
   plus pieces 1–3. Getting this green required only the pin-technique
   fixes listed below — no mathematical obstruction surfaced at any
   point, which is the tractability evidence.

### Cost estimate and Step-1 decomposition

~600–800 lines total (module + QA), 2–3 runs:

- **Step 1a — interface layer** (~150–200 lines): the spike's real
  lemmas hardened into a new `Scaffold/Mathlib/GraphTheory/` module
  (Krylov span, polynomial action, `sum_mulVec`, the Chebyshev band
  bound and degree lemmas). Low risk — everything already elaborated
  green in the spike.
- **Step 1b — spectral discharge** (~200–300 lines): the
  eigenbasis-expansion layer (b's decomposition, `horth`/`horthM`
  through `IsSymm`, `hbottom` through the Rayleigh-sandwich mirror,
  `hband` through `quadForm_eigvalOf` + Parseval + `|T ∘ w| ≤ 1` on
  the band). Medium risk — all inputs exist; the work is the
  expansion plumbing, on the pattern of the shelf's own
  `quadForm_eigvalOf` proofs.
- **Step 1c — statement + QA** (~150–250 lines): the theorem at the
  recorded shape, with QA per this proposal's QA plan — positive
  witness on a diagonal 3×3 fixture (diagonal ⇒ `p(M)b` computable
  entrywise both through the theorem and raw; the bound checked
  numerically), the `k = 1` degenerate case (recovers the plain
  Rayleigh gap), the tightness witness `b = u` (`tan φ = 0`, bound
  attained), and the simple-top-eigenvalue guard refuted on a
  `λ₁ = λ₂` fixture (the hypothesis-free form is false).

### Decisions per shape (the Step-0 gate, item 4)

- **Lanczos/Kaniel–Paige: CLEARED** — the only shape Step 1 may
  attempt; the others are dropped from this proposal's *active* scope
  as the proposal itself directs.
- **Nyström: deferred, obstruction named.** The error bound in sample
  size is inherently probabilistic: it needs
  sampling-without-replacement matrix concentration, which neither
  the pin nor the shelf has (the repo's `matrix_bernstein`/
  `matrix_azuma` are the wrong tool class — independent-sum/
  martingale forms, not negative-association sampling bounds); and the
  deterministic core needs `Matrix.pinv`, absent from the pin
  (verified by search), plus column-space machinery the shelf lacks.
  Re-scoping this shape is a *new-proposal* decision once a
  concentration surface and a pseudoinverse exist — not forced here.
- **Chebyshev/polynomial filters: recorded follow-on, not attempted.**
  Its gate ("composes with the not-yet-delivered
  `spectral-band-projectors.md`") has *dissolved* since this proposal
  was written — the band projectors shipped 2026-08-20/21 with the
  two-sided band projector, orthogonality, partition completeness,
  and the Hilbert-projection specialization. The shape would state
  `‖p_d(M) − bandProjector M hM a b‖₂ ≤ ε(d, gaps)` through the
  shelf's proved `l2OpNorm_eq_max_abs_evals`
  (`Analysis/OperatorTheory/Resolvent.lean:296`) — matrix-level
  functional calculus (heavier linear algebra, lighter geometry than
  Kaniel–Paige). It shares this proposal's entire Chebyshev layer, so
  it is the natural *second consumer*; per the proposal's own
  operating instructions (one shape per run), it is not started here.

### Pin-technique findings (recorded for Step 1)

- **The shelf's SGT interface is `V : Type` (Type 0), not `Type*`.**
  Working at `Type*` made `rayleigh` and `Heat.pow_mulVec_smul` both
  fail to apply with postponed-instance stuck elaboration — four
  apparent "elaboration traps" resolved at once by matching the shelf
  at Type 0. Downstream consumers must do the same (or the shelf must
  grow universes — a separate decision).
- `λ₁`/`λₙ` are not lexable identifiers (`λ` is a reserved token) —
  the spike uses `Ltop`/`Lbot`.
- This pin's `pow_succ` factors `a^(n+1) = a^n * a` (use `←
  mulVec_mulVec`, `mulVec_smul`, then `mul_comm` before the closing
  `← pow_succ`); `mul_pow` is `a^m * b^m = (a*b)^m` (forward, not
  reversed).
- `div_le_div_iff` is deprecated → `div_le_div_iff₀`;
  `div_div_eq_mul_div` at this pin is the `a/(b/c)` form — the
  `(a/b)/c = a/(b*c)` identity is a `field_simp` one-liner.
- `Finset.induction`'s `insert` case names exactly 2 binders
  (`| insert ha ih =>`).
- `Finset.sum_comm` at this pin has the dependent
  `∀ i ∈ s, ∀ j ∈ t` signature — bare application sticks an
  `AddCommMonoid` metavariable; a `Finset.induction` on the sum (as in
  the spike's `sum_mulVec`) avoids it entirely.
- `nlinarith` on association-heavy quotient terms times out (200k
  heartbeats) — normalize first with `set` abbreviations (`Q`, `R`,
  `A` in the spike's ending), then the final chain is instant; the
  skeleton carries `set_option maxHeartbeats 800000`.
- `rw [rayleigh]` (equation-lemma rewrite of the def) works on the
  *first* pass only; the robust route is `unfold rayleigh` inside a
  standalone `have` stated in `dotProduct` terms, then rewrite with
  the `have`.

## External consumer

Large-scale spectral clustering, where Lanczos, Chebyshev/polynomial
filters, and Nyström approximation are literally how the exact
eigendecomposition this repository builds on gets replaced at scale in
practice; GNN pooling layers using the same approximations (Saad,
*Numerical Methods for Large Eigenvalue Problems*; Trefethen & Bau for
the polynomial-filter view — **citations unverified**, confirm before
committed use).

## Why this needed a correction from the original triage, not exclusion

`sgt-gaps.md`'s first pass toward this item recommended iceboxing it
rather than writing a proposal, on the grounds that it is fundamentally
about *iterative numerical algorithms and their convergence rates* — a
different kind of formalization than everything else delivered so far
(closed-form identities over finite-dimensional linear algebra). That
diagnosis stands, but exclusion was the wrong response to it: every other
item promoted from `sgt-gaps.md` earned its priority by being scoped, not
by being easy, and this item deserves the same treatment — a mandatory
Step 0 that either finds a tractable finite slice or records precisely
why there isn't one, the same pattern `decidable-spectral-certificates.md`
and this session's other Step-0-gated proposals already use. Recommending
icebox was treating uncertainty as disqualifying; the honest move is to
scope the uncertainty instead.

## The candidate shapes, precisely

Each method needs an error bound relating approximation quality to
iteration count or sample size:

- **Lanczos**: after `k` iterations on a symmetric matrix, the Ritz
  values approximate the extremal eigenvalues with an error bound in
  terms of the spectral gap and `k`.
- **Chebyshev / polynomial filters**: a degree-`d` polynomial
  approximation to a spectral indicator function (e.g., a band
  projector), with an error bound in `d` and the target function's
  smoothness at the polynomial's approximation region.
- **Nyström**: a low-rank approximation to a PSD matrix from a sampled
  subset of rows/columns, with an error bound in sample size.

## Calibration — why "finite-iteration" is the load-bearing scoping choice

The original assessment's own honesty is the key signal: "nothing else
in this list depends on this item." Combined with the different-kind-of-
math diagnosis above, the right target is not general asymptotic
convergence theory (which would need real-analysis machinery on
sequences and limits closer to `icebox/lyapunov-stability-
formalization-gap.md`'s caution about calculus-on-a-parameter than to
anything this repository has built) but a **fixed, finite iteration
count** statement: for a specific `k` (or `d`, or sample size), state and
prove a concrete numerical bound, not a limiting statement as `k → ∞`.
This stays inside Scaffold's existing finite-dimensional idiom — Step 0
below is where this distinction gets tested for real, not assumed.

*Step-0 outcome on this calibration: it held exactly.* The cleared
statement is finite-`k`, quantitative, and closed-form — no limiting
sequence anywhere. The "different kind of math" reduced, on inspection,
to a polynomial-eigenbasis action layer plus scalar Chebyshev facts,
both inside the existing idiom.

## Build order

### Step 0: Scope and survey (mandatory; may find nothing tractable)

**DELIVERED 2026-08-23 — see the Step-0 record above.** Outcome:
Lanczos/Kaniel–Paige cleared (skeleton spike green, axiom-clean);
Nyström deferred with obstruction; Chebyshev filters recorded as the
second consumer.

### Step 1 (only for whichever shape Step 0 finds tractable)

**Authorized for the Lanczos/Kaniel–Paige shape only**, at the
recorded statement shape, decomposed 1a (interface layer) → 1b
(spectral discharge) → 1c (statement + QA) as priced above. Likely
needs its own sub-decomposition across multiple runs — treat as at
least as hard as the electrical program's harder steps were scoped to
be, per this repository's own calibration precedent.

## QA plan

- Positive witness: a small fixture with a known spectrum, the
  approximation computed at a small concrete `k`/`d`/sample size and
  compared numerically against the exact `spectralProjector` (or `evals`)
  output, with the error bound checked to hold.
- Tightness witness, if feasible: a fixture where the bound is close to
  attained, distinguishing a real bound from a vacuously loose one.

*Step-1 instantiation (recorded):* the diagonal 3×3 fixture (diagonal ⇒
`p(M)b` entrywise, two independent routes to one number), the `k = 1`
degenerate case, the `b = u` tightness witness (bound attained at
`tan φ = 0`), and the `λ₁ = λ₂` guard refutation.

## Operating instructions for an autonomous run

- Step 0 is mandatory and may legitimately terminate this proposal
  without any Lean code landing — that is a valid, recorded outcome, not
  a failure. *(Step 0 landed a green spike rather than iceboxing — the
  outcome the scoping found, not a forced one.)*
- **No new axioms.** If Step 0 finds a shape tractable but Step 1 later
  hits missing machinery, stop and record the precise obstruction rather
  than admitting anything.
- Do not attempt more than one of the three candidate shapes in the same
  run, and do not attempt Step 1 on a shape Step 0 did not explicitly
  clear.

## Open next step

**Step 1a** — the interface layer: transfer the spike's four real
lemmas plus the two priced shallow gaps (`natDegree T`, growth lemma)
into a new shelf module (`GraphTheory/Krylov.lean` or a section of the
appropriate existing module), with the module-level survey note and the
pin-technique record. One run. Then 1b (spectral discharge), then 1c
(statement + QA retiring the milestone).
