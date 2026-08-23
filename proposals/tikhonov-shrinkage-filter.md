# Proposal: Tikhonov Regularization in the Laplacian Eigenbasis

**Status:** **COMPLETE.** Original three build steps **DELIVERED
2026-08-20** and **Phase 2 (the hard-filter limit) DELIVERED 2026-08-23**
(both steps in one run — see the Phase-2 delivery record at the end).
Zero new axioms at every step; the explicit-axiom count was 12 at the
original delivery and 9 at Phase 2, unchanged by both. Original
assessment text follows.

**Assessment:** proposed 2026-08-19, priority **High**. Assistant's
assessment of project direction, requested 2026-08-19, promoted from
`sgt-gaps.md` item 4. Authorizes no Lean changes, axiom admissions, or
external publication.

Companion to `sgt-gaps.md` and `finite-relative-entropy.md` (comparable
cost profile — a direct corollary of already-proved eigenbasis machinery,
no new infrastructure). No backlog gate applies.

## Clean-room boundary

Internal prioritization and analysis. If counsel approves a public
repository export, restate from standard graph-signal-processing sources
(Shuman et al.). Do not copy this proposal verbatim.

Assessed from `Scaffold/Mathlib/GraphTheory/Spectral.lean`
(`eigvecOf_complete`, `quadForm`, the eigenbasis expansion machinery
already used by `prove-lambda2-variational.md` and the electrical
program), confirming the closed-form minimizer below is a direct
corollary with no missing Mathlib pieces.

## External consumer

Graph signal processing's standard smoothing operator — semi-supervised
label propagation, graph signal denoising, and any application wanting a
smooth-but-not-projected reconstruction. One of the most cited operators
in the graph signal processing literature (Shuman, Narang, Frossard,
Ortega & Vandergheynst, "The Emerging Field of Signal Processing on
Graphs," IEEE Signal Processing Magazine 30(3), 2013 — **citation
unverified**, confirm before use in a committed docstring).

## Recommendation

For `y : V → ℝ` and `π : ℝ` (`0 < π`), define the minimizer of
`‖x − y‖² + (1/π) · xᵀLx` over `x : V → ℝ` and prove its eigencoefficients
are

```
c_k(x*) = π / (λ_k + π) · c_k(y)
```

— a low-pass shrinkage filter: every mode attenuated by a factor strictly
in `(0,1)`, decreasing in `λ_k`, none exactly zeroed. State explicitly,
alongside the theorem, that this is **not** a projection (unlike
`spectralProjector`) — the two are easily conflated, and the distinction
(every mode survives, attenuated, vs. some modes are zeroed exactly) is
the entire point of the operator.

## Why this is cheap

The minimizer's existence and uniqueness are a direct strict-convexity
argument (the objective is a strictly convex quadratic in `x`, since `L`
is PSD and the `‖x-y‖²` term is strictly convex on its own). The
closed-form eigencoefficient identity falls out of expanding both terms
in the eigenbasis via `eigvecOf_complete` and minimizing termwise — each
mode decouples because `L`'s eigenbasis simultaneously diagonalizes both
quadratic terms. No new Mathlib machinery needed anywhere in this proof;
it is algebra over the already-proved eigenbasis expansion, the same
technique `Foster.lean` and `prove-lambda2-variational.md` already used.

## Build order

### Step 1: The minimizer and its existence/uniqueness

Define `tikhonovMinimizer (A : WAdj) (hA : A.IsSymm) (hnonneg : ...) (π :
ℝ) (hπ : 0 < π) (y : V → ℝ) : V → ℝ` (via `Classical.choice` over the
strict-convexity argument, or directly via the eigenbasis formula below —
decide which is cheaper before writing the statement, per this
repository's standing rule). Prove it is the unique minimizer of
`‖x − y‖² + (1/π) · quadForm (laplacian A) x`.

### Step 2: The closed-form eigencoefficient identity

Prove `⟪eigvecOf (laplacian A) hA k, tikhonovMinimizer A hA hnonneg π hπ
y⟫ = π / (evals hA k + π) * ⟪eigvecOf (laplacian A) hA k, y⟫` for every
`k`, by expanding both quadratic terms in the eigenbasis and minimizing
per-coefficient (each mode's minimization is a one-variable quadratic,
solved by `deriv = 0`).

### Step 3: The shrinkage-factor properties

Prove the attenuation factor `π / (λ_k + π)` is strictly in `(0,1)` for
every `λ_k ≥ 0` (from `π > 0` and `λ_k ≥ 0`), strictly decreasing in
`λ_k`, and never exactly `0` or `1` — the facts that make this a
shrinkage filter rather than a projection or the identity. State the
not-a-projection distinction explicitly as a corollary or docstring note.

## QA plan

- Positive witness: a small fixture (`K₂` or the 3-vertex path), `y`
  concrete, `tikhonovMinimizer` computed both from the definition and via
  the closed-form eigencoefficient identity, cross-checked to agree.
- Shrinkage witness: the attenuation factor computed numerically at two
  different `λ_k` values on the same fixture, confirming the ordering
  (larger `λ_k` ⇒ smaller factor).
- Negative/distinguishing witness: compare `tikhonovMinimizer` against
  `spectralProjector`'s output on the same fixture and `y`, showing they
  disagree — concrete evidence the two are not the same operator, guarding
  the "not a projection" claim rather than leaving it asserted.

## Operating instructions for an autonomous run

- One step per run; all three are small enough that a single run may
  cover more than one if the first lands cleanly.
- **No new axioms.** This proposal's entire cost case is that nothing
  here needs machinery beyond the already-proved eigenbasis expansion —
  if a step turns out to need something genuinely absent, stop and record
  the obstruction rather than admitting anything.
- Survey Mathlib's convexity/minimization API before Step 1 in case a
  ready-made strict-convex-minimizer-exists lemma is cheaper than the
  direct eigenbasis construction.

## Open next step

None — delivered. See the delivery record below.

## Delivery record (2026-08-20)

Delivered in `Scaffold.Mathlib.GraphTheory.Tikhonov` (namespace
`SpectralGraphTheory`), all proved, zero axioms:

- **Step 1** — `tikhonovObjective` (the total objective, junk-degenerate
  at `π = 0` documented), `tikhonovObjective_minimizer_le` (minimality),
  `eq_of_tikhonovObjective_eq_minimizer` (uniqueness in the strong
  vector-equality sense), both derived from the single
  **strict-convexity decomposition** `tikhonovObjective_sub_minimizer`
  (`obj(x) − obj(x*) = ∑_k (1 + λ_k/π)(d_k − d*_k)²`, positive weights).
  *Definition-route decision, per the standing rule:* the minimizer is
  `tikhonovMinimizer` **defined by the eigenbasis formula**
  `∑_k (π/(λ_k+π)) (v_k ⬝ᵥ y) • v_k`, not `Classical.choice` over
  strict convexity — every interface theorem becomes a computation and
  uniqueness a corollary of the decomposition. A Mathlib
  convexity-API survey was not needed on this route (nothing outside
  the eigenbasis machinery is consumed — the proposal's own
  cost case).
- **Step 2** — `tikhonovMinimizer_dotProduct_eigvecOf`, the closed-form
  eigencoefficient identity, proved hypothesis-free (pure
  orthonormality) through a *generic* workhorse
  `dotProduct_eigvecOf_filter` (any filter function `g`, reusable by
  other spectral-filter consumers), plus the **normal equation**
  `tikhonovMinimizer_add_smul_one_mulVec`
  (`(L + π•1) *ᵥ x* = π • y`) and its converse characterization
  `eq_tikhonovMinimizer_of_add_smul_one_mulVec` — the interface QA pins
  the spectral construction against a hand-solved linear system.
- **Step 3** — the shrinkage-factor arithmetic layer
  (`tikhonovShrinkage` with `pos`, `ne_zero`, `le_one`, `lt_one`,
  `eq_one_iff`, strict antitonicity), mean preservation
  `sum_tikhonovMinimizer_eq_sum` (symmetry + `π ≠ 0` only — each
  component's mean is preserved, the correct disconnected behavior),
  and the not-a-projection theorem
  `tikhonovMinimizer_ne_apply_self_of_eigvalOf_pos` (failure of
  idempotence at any positive-eigenvalue eigenvector; **hypothesis
  strengthened by deletion**: the nonnegativity hypothesis the sketch
  carried turned out unnecessary and was dropped).
- **Recorded statement-shape deviation 1:** the recommendation's
  "never exactly 0 or 1" is *half wrong*. The factor is never `0` ✓,
  but at `λ = 0` it is **exactly `1`** (`π/(0+π) = 1`) — and that is a
  feature: the kernel mode passes through untouched, which is precisely
  mean preservation. The delivered statements are the true ones:
  `0 < factor`, `factor ≤ 1`, `factor < 1 ↔ 0 < λ`,
  `factor = 1 ↔ λ = 0`, strict antitonicity on `λ ≥ 0`.
- **Recorded statement-shape deviation 2:** the "not a projection"
  claim is delivered as a *theorem*, not a docstring note: failure of
  idempotence `T(T v) ≠ T v` — the precise mathematical sense in which
  the filter differs from `spectralProjector`.

**QA** (`Tikhonov_QA.lean`, `K₂` fixture, signal `![1,0]`, `π = 1`):
the minimizer **pinned through the normal equation** — the candidate
`![2/3,1/3]` verified by hand (entrywise Gaussian elimination,
independent of the module) and promoted to
`tikhonovMinimizer = ![2/3,1/3]` by the converse characterization, so
the spectral-theorem construction and a hand-solved 2×2 system meet at
the same vector; the objective pinned (`obj(x*) = 1/3` exactly, against
`obj(y) = obj(0) = 1`, minimality instantiated at `1/3 ≤ 1` and
strictly better); the spectrum pinned (trace `2`, determinant `0`, PSD
⇒ every eigenvalue is `0` or `2`) so the shrinkage story is exact:
factor exactly `1` on the kernel mode, exactly `1/3` on every other,
`1/3 < 1` by antitonicity, `1/3 ∈ Ioo 0 1`; **not-a-projection
numerically**: a second hand-solved system pins `T(T y) = ![5/9,4/9] ≠
![6/9,3/9] = T y`; mean preservation instantiated twice (`1` both);
and the **`hπ` guard refuted-on-omission**: at `π = 0` the minimizer is
the zero vector and the hypothesis-free minimality would read `1 ≤ 0`.

**Verification:** `lake env lean` on the public module and QA — zero
errors, zero warnings; `#print axioms` on all 18 public and 14 headline
QA theorems — three standard axioms only; all thirty-three QA modules
batch-elaborated, zero errors (only the documented pre-existing
section-variable warnings in untouched modules); full `lake build` ✔;
`lint_axioms` (12), `check_citations`, `check_markdown_links` pass;
scoreboard regeneration (**890/12/0**, +30 QA declarations).

**Named residual:** `tikhonovMinimizer_eigvecOf` (eigenvector inputs
come out as `factor • v`) is proved generally but not numerically
instantiated in QA — `eigvecOf` entries are not kernel-computable on
the fixture; its content is covered transitively by the two
normal-equation pins. The unverified Shuman et al. citation stays
unverified and out of committed docstrings.
## Phase 2: The hard-filter limit (opened 2026-08-23/24, priority High)

**Status: DELIVERED 2026-08-23 (both steps in one run); see the Phase-2
delivery record below.** What follows is the opening assessment text.

**Status (opening):** Proposed — a real external named consumer,
`sgt-gaps.md` item 1 (from the independent `spectral-proof` clean-sheet
rewrite project), asks for the standard positive-eigenvalue limit of
`tikhonovShrinkage`. Promoted straight to High in
`proposals/README.md`: the same class of resolution as
`reversibility-and-heat-semigroup.md` Phase B — a different project
naming this exact interface by file path, not this proposal naming
itself.

**The ask, precisely (per `sgt-gaps.md`):** for `tikhonovShrinkage π lam
:= π / (lam + π)` (`Tikhonov.lean:79`) with `0 < lam` fixed,

```lean
Filter.Tendsto (fun π : ℝ => tikhonovShrinkage π lam) (𝓝 0) (𝓝 0)
```

plus a finite spectral-sum/Parseval corollary: for a finite selected
tail of modes each with `lam ≤ λᵢ` and `0 < lam`, the squared filtered
coefficient energy of that tail tends to zero as `π → 0⁺` (or along an
explicitly stated positive filter). **The requester is explicit that
this must be stated as suppression of the selected positive-eigenvalue
tail, not as convergence to an arbitrary two-sided band projector** —
ordinary (low-pass) Tikhonov cannot erase modes below a band's lower
endpoint, and the statement must not overclaim that it does.

**Cost, surveyed:** the scalar limit itself is immediate —
`tikhonovShrinkage π lam = π / (lam + π)` is a quotient of two
continuous functions of `π` with the denominator `lam + π` continuous
and nonzero at `π = 0` (equal to `lam > 0`), so `ContinuousAt` at `0`
plus evaluation (`π / (lam + π) → 0 / lam = 0`) closes it via
Mathlib's standard `Filter.Tendsto.div`/`ContinuousAt.tendsto`
machinery — no new definitions, a few lines. The Parseval corollary
composes this scalar limit with the already-proved
`tikhonovShrinkage_le_one`/`_pos` bounds and the shelf's eigenbasis
expansion (`eigvecOf_expansion_apply`, the same completeness fact
`Heat.lean`'s spectral-sum proof already consumes) over a **finite**
selected index set — `Finset.sum`/`Filter.Tendsto.finset_sum` over a
fixed finite tail, not a limit of an infinite series, so no new
convergence machinery is needed either.

**Build order:**

- **Step 1:** `tikhonovShrinkage_tendsto_zero` — the scalar limit above,
  stated for fixed `0 < lam`.
- **Step 2:** the tail-suppression corollary — for a `Finset` of modes
  each satisfying `lam ≤ λᵢ`, the sum of squared filtered coefficients
  `∑ i ∈ tail, (tikhonovShrinkage (λᵢ) π)² * cᵢ²` (or the natural
  eigenbasis-coefficient form) tends to `0` as `π → 0⁺`, by
  `Filter.Tendsto.finset_sum` over Step 1 composed at each fixed `λᵢ`
  (each term individually `→ 0`, since `lam ≤ λᵢ` and the shrinkage
  factor is monotone/bounded — reuse `tikhonovShrinkage_le_one`, do not
  reprove monotonicity from scratch unless the exact form needs it).
  **State the conclusion as tail suppression, per the requester's
  explicit non-overclaim instruction** — do not phrase it as convergence
  to a band projector.

**QA:** a positive witness (a small fixture with a concrete `lam` and a
two-mode tail, the filtered energy computed at a few `π` values
decreasing toward `0`); a boundary/negative witness confirming the
statement genuinely fails for a mode *below* `lam` (the low-pass
argument load-bearing, not vacuous) — directly requested by
`sgt-gaps.md`'s "must not be phrased as... an arbitrary two-sided band
projector" instruction.

**No new axioms; no proposal-scope change beyond this phase.** One step
per run, per this repository's standing operating instructions.

## Phase-2 delivery record (2026-08-23)

Delivered in `Scaffold.Mathlib.GraphTheory.Tikhonov` Section 5 and
`Tikhonov_QA.lean` (three new QA sections), all proved, zero axioms,
QA 1522 → 1546 (24 new QA declarations).

- **Step 1** — `tikhonovShrinkage_tendsto_zero`: the consumer's exact
  statement `Filter.Tendsto (fun π => tikhonovShrinkage π lam) (𝓝 0)
  (𝓝 0)` at fixed `0 < lam`, proved in three lines through
  `ContinuousAt.div` at the nonzero denominator `lam + 0 = lam`
  (`continuousAt_id.div (continuousAt_const.add continuousAt_id)`),
  with `simpa [tikhonovShrinkage]` evaluating the limit point
  `0 / lam = 0`. The delivered form is **two-sided** (the full
  neighborhood filter), strictly stronger than the requested
  `π → 0⁺` — the survey's continuity observation: at fixed `lam > 0`
  the denominator stays nonzero near `0` from both sides.
- **Step 2** — the tail-suppression corollary, in two forms.
  `tikhonovShrinkage_tail_energy_tendsto_zero` (the general form): on
  *any* symmetric matrix `M`, for a `Finset t` of modes each with
  `lam ≤ eigvalOf M i` (`0 < lam`), the filtered coefficient energy
  `∑_{i ∈ t} (tikhonovShrinkage π λᵢ * cᵢ)²` tends to `0` as `π → 0` —
  each term by Step 1 at that mode's own eigenvalue (`Tendsto.mul` at
  the constant coefficient, then `.pow 2`), the sum by
  `tendsto_finset_sum`. `tikhonovMinimizer_tail_energy_tendsto_zero`
  (the consumer-facing Laplacian form): the same conclusion with the
  minimizer's own coefficients `(vᵢ ⬝ᵥ tikhonovMinimizer A hA π y)²`,
  composed from the general form through the coefficient identity
  (`Tendsto.congr` at the pointwise `Finset.sum_congr`, the Heat run's
  recorded pointwise-∀ congruence pattern). **Suppression-stated per
  the requester's explicit non-overclaim instruction** — no
  band-projector convergence is claimed or implied anywhere; the
  docstrings say so and the QA's boundary refutation witnesses exactly
  the one-sidedness (below).
- **Statement-shape decisions recorded:** (1) the general form is
  stated for a symmetric matrix, not the Laplacian — nothing in the
  proof uses PSD (the `lam ≤ λᵢ` tail hypothesis carries the
  positivity), the module's own `dotProduct_eigvecOf_filter`
  generality precedent; the Laplacian packaging is the wrapper. (2) No
  `hnonneg` hypothesis anywhere in Section 5. (3) The tail set is an
  abstract `Finset`, not a threshold filter — the consumer constructs
  whatever selection it needs (the QA constructs both a `univ` tail
  and a filtered tail).
- **QA** (24 declarations): the **two-mode positive witness** on the
  diagonal fixture `diag13` *reused from `Band_QA`* (spectrum `{1,3}`,
  each eigenspace a coordinate axis — its eigenvector-direction lemmas
  supply the coefficient squares `1` and `0` without re-derivation):
  the tail energy pinned in **closed form**
  `diag13_tail_energy_eq : ∑ i, (…)² = tikhonovShrinkage π 1 ^ 2` at
  every `π`, evaluated exactly at `π = 1/10` (`1/121`) and `π = 1/100`
  (`1/10201`) — the energy visibly collapsing — and the corollary
  consumed at a concrete tolerance (`diag13_corollary_consumed`:
  `∃ δ > 0` forcing tail energy `< 1/100` near `0`, through
  `Metric.tendsto_nhds_nhds`); the **scalar `lam = 0` refutation**
  (`not_shrinkage_zero_tendsto`): the hypothesis-free form is false —
  the factor is `1` at every `π ≠ 0` and `0` at `π = 0`, so it has no
  limit at all (the ε-δ refutation at `ε = 1/2`, `π = min(δ/2, 1)`); the
  **tail-level boundary refutation on `K₂`**
  (`not_lapK2_univ_tail_tendsto`, the requester's mandated
  "mode below lam" witness): with the kernel mode included in the tail,
  the energy provably stays `≥ 1/2` at every nonzero `π`
  (`lapK2_energy_ge`, from the kernel-eigenvector line
  `v 0 = v 1` + unit norm ⇒ coefficient² `= 1/2`, and Parseval for the
  other mode) — the kernel mode passing through untouched is exactly
  why the statement fails, the `lam ≤ λᵢ` hypothesis load-bearing; and
  the **minimizer-form instantiation** (`lapK2_minimizer_tail`) at the
  filtered nonzero-mode tail (identified as exactly the eigenvalue-`2`
  singleton through a trace-based uniqueness lemma), with its `π = 1`
  energy pinned to `1/18` through the coefficient identity
  (`(1/3)² · 1/2`, Parseval + the kernel line).
- **Pin-technique notes (recorded for future runs):** `𝓝` needs
  `open scoped Topology`, not just `open Filter`; `λ₀`/`hλi` are not
  lexable identifiers (λ is a reserved token — the recorded ASP Step-0
  trap, re-hit); `tendsto_finset_sum` exists only as the `to_additive`
  child of `tendsto_finset_prod` (not greppable, but usable — the
  recorded `Finset.sum_neg_distrib` phenomenon, re-verified);
  `tendsto_const_nhds`'s value is *implicit*, so the constant must be
  pinned by an ascribed `have` before `.mul`; `Tendsto.congr` takes
  pointwise-∀ equality (the Heat note, re-verified); rewriting *under*
  a square needs the term-form coefficient lemmas (`term_of_eq_one`)
  since `simp only` cannot rewrite `(a * (b)) ^ 2` from a hypothesis
  about `b ^ 2`; `fin_cases` on an `obtain`ed witness leaves a
  beta-redex in the hypothesis — the robust fix is a type-ascribed
  `have hi' : … := hi`; and `Metric.tendsto_nhds_nhds`'
  ε-δ form wants `dist x 0 < δ` (rewrite `|π| < δ` through
  `Real.dist_eq, sub_zero`).

**Verification:** spike first (`wip/tikP2_spike.lean` green, zero
errors/warnings, several rounds — the fixes becoming the technique
list above), then transfer; `lake env lean` on the public module and
the QA file — zero errors, zero warnings each; explicit `lake build`
targets for both ✔; `#print axioms` via `wip/tikP2_axcheck2.lean` on
all three public and all 24 QA declarations — `propext,
Classical.choice, Quot.sound` only; full `lake build` ✔ (2252 targets,
"Build completed successfully"; zero warnings in the changed modules);
`lint_axioms` (9, unchanged), `check_citations`, `check_markdown_links`
pass; scoreboard regenerated (**1546/9/0**, idempotent). Records
updated: this proposal, `proposals/README.md`, README, the radar, the
scoreboard (three verification rows, lint row, a new interpretation
bullet), the SGT index map (+3 declaration rows, Phase-2 status note),
the execution plan, and the activity log.
