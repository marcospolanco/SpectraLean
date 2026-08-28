# Proposal: Fiedler Subspace Stability via Davis–Kahan

**Status:** **COMPLETE — Step 0 DELIVERED 2026-08-28 (verdicts recorded
below) + Step 1 DELIVERED 2026-08-28** (run `20260828T013901Z-run-1`,
pure hard crust, zero new axioms — `fiedlerSubspace_stability` in
`GraphTheory/Fiedler.lean`, `davis_kahan_sin_theta`'s first
graph-theoretic consumer) **+ Step 2 DELIVERED 2026-08-28** (run
`20260828T034649Z-run-1`, pure hard crust, zero new axioms —
`fiedlerLine_stability` in `Fiedler.lean` plus the kernel-projector
identification layer in `Spectral.lean`; the proposal's payoff slice,
closing the program). This document authorizes no commits or external
publication.

## Step 2 delivery record (2026-08-28, run `20260828T034649Z-run-1`)

**Delivered** (pure hard crust, zero new axioms; `#print axioms` via
`wip/fsd2_axcheck.lean` on all 24 audited declarations — 7 module + 17
QA — reads exactly `propext, Classical.choice, Quot.sound`, every one;
the statement consumes only *proved* theorems — Step 1's wrapper and
the kernel-characterization ecosystem — so the whole chain is
unconditional):

- `Spectral.lean`, the projector section: **`eq_of_isSymm_idempotent_of_forall_mulVec_eq`** (the Step-0-priced piece (i): symmetric
  idempotents are determined by their fixed spaces — `ker P = Fix(P)ᗮ`
  algebraically via the new self-adjoint helper
  `dotProduct_mulVec_comm_of_isSymm`, the fixed-space hypothesis
  transferring kernels, then `Q ∘ P = P` collapsing `Q` onto `P`;
  nothing in the pin supplies it), **`spectralProjector_mulVec_eq_sum`**
  (piece (ii)'s first half: the projector's action expanded in its own
  eigenbasis, `∑_{λᵢ ≤ c} (vᵢ ⬝ᵥ x) • vᵢ`), and
  **`eigvecOf_expansion`** (the second half: every vector is its
  eigenbasis expansion, `OrthonormalBasis.sum_repr'` restated at the
  shelf's plain-function eigenvectors).
- `Spectral.lean`, after `laplacian_evals_zero`:
  **`initialProjector_laplacian_zero_fix_iff`** — the index-0
  projector's fixed space is exactly the Laplacian kernel, with *no*
  connectivity hypothesis (forward: every filtered eigenvector has
  eigenvalue exactly `0`, pin from below and `evals_first_le_eigvalOf`
  from above; backward: above the threshold the eigenvalues are
  strictly positive so a kernel vector's coordinates vanish there, and
  the expansion reconstructs it inside the range) — and
  **`initialProjector_laplacian_zero_eq_of_connected`** — the
  identification: any two connected Laplacians carry the *same* index-0
  projector (the uniqueness lemma joined to
  `laplacian_mulVec_eq_zero_iff_exists_const` on both sides).
- `Fiedler.lean`: the headline **`fiedlerLine_stability`** — at Step
  1's hypothesis stack plus connectivity/nonnegativity of base and
  perturbed graph, `‖(P₁' − P₀') − (P₁ − P₀)‖ ≤ ‖laplacian E‖ / δ`. The
  common-kernel identification rewrites `P₀' = P₀`, the residual
  telescopes (`abel`) to the Step-1 projector difference, and Step 1
  finishes. The proposal's actual payoff: the rank-2 rotation is
  entirely attributable to the Fiedler component, because connected
  graphs never move their kernel direction.
- QA (`Fiedler_QA.lean`'s new `FiedlerLineStability` section, +17): the
  **P₃ → K₃ edge-addition headline instance** — separation `δ = 2`
  discharged against the two pinned spectra (`λ₃(L K₃) = 3`, `λ₂(L P₃)
  = 1`; only that difference admits `δ = 2`), the single-edge
  perturbation's Laplacian identified as `rankOne ![1,0,-1]`, and its
  norm pinned **exactly `2` from both sides** (`≤` by
  `l2OpNorm_rankOne_le` — the Sparsification delivery's algebra
  consumed cross-module; `≥` by the quadForm witness `4 ≤ 2 · 2` through
  `abs_quadForm_le_of_l2OpNorm_le`), so the derived bound is exactly
  `≤ 1` — and the perturbed side `K₃` sits on Davis–Kahan's own *tie*
  branch (`λ₂ = λ₃ = 3`), the branch whose proof route yields
  `≤ 1 ≤ ‖E‖/δ` with no slack at this instance; the **identification
  instance** at the genuine two-spectrum pair `P₃`/`K₃` (`{0,1,3}` vs
  `{0,3,3}` — operators that differ everywhere except on the
  constants); the **fix-iff pins** at vectors (`onesVec` fixed;
  `![1,2,3]` not fixed with the kernel computed by the diffusion form
  `L *ᵥ ![1,2,3] = ![-1,0,1] ≠ 0`); and the **disconnected fence** —
  the empty graph's index-0 projector provably ≠ `P₃`'s, witnessed by
  `e₀` fixed by the zero Laplacian's projector (kernel is everything)
  and not by   `P₃`'s (`L *ᵥ e₀ = ![1,-1,0] ≠ 0`): the connectivity
  hypotheses are load-bearing, with both fix-iff directions exercised
  on the way.

  Obligation 3's "Fiedler vector's angular movement computed by hand" is
  honestly narrowed the same way Step 1 narrowed obligation 1: entrywise
  `initialProjector` values at a fixture depend on the eigenbasis
  choices behind `eigvecOf`, so no hand-computable *value* of the
  residual distance exists at K₃/P₃ — the falsification content
  instead lives in the load-bearing separation discharge (only `3 − 1`
  admits `δ = 2`), the two-sided exact norm pin `2` (a wrong constant
  breaks exactly one side), the tie-branch instance with zero slack,
  and the disconnected fence.

**Technique findings** (spike `wip/fsd2_spike.lean`, iterated to zero
errors/warnings before any shelf Lean): the EuclideanSpace/Pi
elaboration seam at `sum_repr'` — the eigenbasis expansion must restate
the EuclideanSpace-typed sum at the Pi type *inside* a `have` before
`Finset.sum_apply`/`Pi.smul_apply` rewrites will match (rw patterns
miss PiLp instances; mirroring `eigvecOf_complete`'s on-file idiom, with
per-term `rfl` closing the smul-to-mul normalization); the
left-`smul`-of-`dotProduct` gap — `Matrix.smul_dotProduct` in the pin
is `x • (v ⬝ᵥ w)` (⬝ᵥ binds tighter than •), so converting
`(λ • v) ⬝ᵥ f` needs the dotProduct-unfold + `Finset.mul_sum` +
per-term `ring` route, not a named lemma; the self-referential-rewrite
trap — rewriting `Q *ᵥ (Q *ᵥ y) = Q *ᵥ y` backwards loops, so the
orthogonality chain is stated as four `have`s joined by `.trans` rather
than one `rw` chain; `sub_sub_sub_cancel_left`'s statement shape is
`c − a − (c − b)` in this pin, not `a − c − (b − c)` — `abel` is the
robust route for projector telescoping; `fin_cases` inside a
`by_cases hij : i = j` matrix-entry proof needs `first | exact absurd
rfl hij | (simp […]; try norm_num)` (the diagonal instantiations are
killed by the hypothesis, the off-diagonal evaluated); the
`deg`-at-fixtures pattern (`rw [deg, Fin.sum_univ_three] <;> norm_num
[edge02]`) is required again — plain `simp [deg]` leaves
`Finset.filter`-card goals `decide` cannot close; `laplacian_mulVec_apply`
(the diffusion form) is the cheap route for concrete `L *ᵥ x`
computations, avoiding degreeMatrix unfolding entirely; and the
recurrent stale-olen at the import boundary (module target rebuilt
before the consumer's elaboration — twice this run: Spectral → Fiedler,
Fiedler → QA).

**Verification:** spike first (zero errors/warnings before any shelf
Lean); `lake env lean` — zero errors/zero warnings on `Fiedler.lean`
and `Fiedler_QA.lean`, `Spectral.lean` at exactly its pre-existing
8-warning baseline; explicit `lake build` targets ✔ (Spectral
2205/2205, Fiedler 2205/2205, QA 2224/2224); `#print axioms` as above;
**full `lake build` ✔ (2402/2403, "Build completed successfully")
immediately followed by `check_build_completeness.py` — 123/123 fresh,
0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues),
`check_citations`, `check_markdown_links` pass after the record sweep;
scoreboard regenerated (**2731/10/0**).

## Step 0 verdict (2026-08-28, delivered before any shelf Lean)

1. **The premise correction.** The obligation section's "zero real
   theorem consumers anywhere in the shelf … nothing actually invokes
   `davis_kahan_sin_theta` by name in a proof term" was stale when
   written and is corrected here: `Scaffold/Derived/ProjectorDrift.lean`'s
   `davisKahanTwoPoint` invokes it by name in a proof term (feeding
   `eventStreamProjectorDrift`). The true gap — and the obligation this
   proposal delivers — is the *Mathlib-layer / graph-theoretic* one:
   `scripts/measure_load_bearing.py` counted zero `Scaffold/Mathlib`
   consumers for `DavisKahan.lean` (a structural valley), and the
   theorem's exact hypothesis shape had never been exercised at a graph
   spectrum, only at abstract matrix pairs.
2. **The Band-family subsumption check** (the Active-table row's named
   check): the delivered `Perturbation.BandDavisKahan` family does
   **not** subsume Step 1 as a one-line corollary, on two counts.
   (a) Its windows are two-sided (`bandProjector` between flanks) with
   both-flank or pairwise separation; the bottom-2 initial projector is
   *one-sided* (threshold `evals ⟨1⟩`), so a band-route derivation would
   first need a lower eigenvalue fence (Laplacian PSD supplies one) plus
   a window decomposition of the one-sided projector — strictly more
   plumbing than the direct instantiation. (b) The proposal's obligation
   is precisely to exercise `davis_kahan_sin_theta`'s own hypothesis
   shape; the band route would bypass the target theorem. Verdict:
   Step 1 stays a direct instantiation, and it is delivered as one.
3. **The Step-2 residual-projector route** (required by the acceptance
   bar before Step 2 is attempted): two of the three pieces are cheap —
   the subprojector law `P₀ * P₁ = P₀` at thresholds `evals ⟨0⟩ ≤ evals
   ⟨1⟩` IS the delivered master law
   `spectralProjector_mul_spectralProjector`; residual idempotence
   (`(P₁ − P₀)² = P₁ − P₀`) and the telescoping identity
   `(P₁ − P₀) − (Q₁ − Q₀) = P₁ − Q₁` (at a *common* `P₀ = Q₀`) are
   immediate algebra, so the Step-1 bound directly bounds the residual
   (Fiedler-line) projector difference. The genuinely priced piece is
   the **common-kernel identification** `initialProjector L 0 =
   initialProjector L' 0` for two connected Laplacians: it needs (i) a
   symmetric-idempotent-determined-by-fixed-space uniqueness lemma and
   (ii) the fixed-space characterization of `initialProjector … 0` from
   `laplacian_kernel_eq_span_onesVec` (an eigenbasis-expansion argument;
   nothing on file supplies either). Step 2 is deferred as its own slice
   with exactly this route; if it does not close cheaply, Step 1 stands
   alone as the delivered consumer (per the acceptance bar).

## Step 1 delivery record (2026-08-28, run `20260828T013901Z-run-1`)

**Delivered** (pure hard crust, zero new axioms; `#print axioms` via
`wip/fsd_axcheck.lean` on all 22 audited declarations — 5 module + 17
QA, private helpers and the `k3Adj` fixture covered transitively —
reads exactly `propext, Classical.choice, Quot.sound`, every one; the
wrapper consumes a *proved* theorem, so the whole chain is
unconditional):

- `Spectral.lean`: `laplacian_zero`, **`laplacian_add`** (the
  Laplacian-of-perturbed-adjacency identity the wrapper transports
  through — the statement-shape correction of the draft below, which had
  applied Davis–Kahan at `(laplacian A, E)` and concluded at
  `laplacian (A + E)`; those operators differ by the degree arithmetic,
  and `laplacian_add` is exactly the bridge), **`evals_congr`** (the
  general-index proof-irrelevance transport, sibling of the delivered
  `secondEval_congr` — carries the separation hypothesis across the two
  spellings of the perturbed operator), and **`laplacian_evals_zero`**
  (the bottom Laplacian eigenvalue is exactly `0` on symmetric
  nonnegative weights, no connectivity — the pin every exact
  Laplacian-spectrum fixture starts from; the multiplicity is what
  connectivity controls).
- `Fiedler.lean` (imports `Perturbation.DavisKahan`, no cycle): the
  headline **`fiedlerSubspace_stability`** — at exactly the draft's
  hypothesis stack corrected to the Laplacian perturbation:
  `‖initialProjector (laplacian (A + E)) 1 − initialProjector
  (laplacian A) 1‖ ≤ ‖laplacian E‖ / δ` at `3 ≤ card V` and `δ ≤
  evals (L(A+E)) ⟨2⟩ − evals (L A) ⟨1⟩`. No connectivity hypothesis
  (the bound is honest without it); connectivity is what interprets the
  projector as `span {onesVec, fiedlerVector}` via the kernel
  characterization, and the wrapper's docstring says so rather than
  carrying a decorative hypothesis.
- QA (`Fiedler_QA.lean`'s new `FiedlerSubspaceStability` section, +19):
  the exact combinatorial **P₃ spectrum pins** — `λ₂ = 1` (the `≤` side
  on file in `Variational_QA`; the `≥` side new, by the sum-of-squares
  identity `E(x) = ‖x‖² + 3 (x₀+x₂)²` on the zero-sum constraint
  through the `lambda2_variational` engine) and `λ₃ = 3` (by
  `laplacian_evals_zero` + the λ₂ pin + the trace identity
  `0 + 1 + λ₃ = 4`); the **two-route zero-perturbation cross-check**
  (obligation 1: the wrapper's instance at `δ = 2` — where the
  separation discharge is the load-bearing step, a wrong index or
  operator in the wrapper's `hsep` failing exactly there against the
  pinned spectrum `{0, 1, 3}` — cross-checked against the raw
  `P₃ + 0 = P₃` matrix-identity route, both meeting at distance exactly
  `0`); and the **K₃ tie-awareness witness** (obligation 2): `λ₂ = λ₃ =
  3` pinned both sides (the `≤` by the Rayleigh engine at `![1,-1,0]`;
  the `≥` by the identity `E(x) = 3‖x‖² − (x₀+x₁+x₂)²`, equality
  throughout — the whole `onesVec`-complement is an eigenspace), with
  the wrapper's separation hypothesis *provably unsatisfiable* for
  every positive `δ` — the statement is vacuous at the eigenvalue tie,
  the honest boundary Davis–Kahan's own proof case-splits on, rather
  than silently yielding a bound. (Obligation 1's "direct eigenvector
  computation" route is honestly narrowed: entrywise `initialProjector`
  values at a fixture need the Step-2 fixed-space machinery, so the
  independent route is the matrix-identity one; the spectrum pins carry
  the falsification content.)

**Technique findings** (spike `wip/fsd_spike.lean`, zero
errors/warnings before any shelf Lean): plain-numeral `k : Fin (card V)`
arguments (`initialProjector M hM 1`) fail to elaborate at abstract
`V` — the anonymous-constructor spelling `⟨1, by omega⟩` is required
(and `hk` side conditions phrased `by show (1:ℕ) + 1 < card V; omega`
so `omega` sees the literal); `evals`-typed sums over
`Fin (Fintype.card (Fin 3))` do not match `Fin.sum_univ_three`
syntactically — re-state the sum at `Fin 3` by a defeq `have` first
(the multiway QA's recorded idiom), then `simp only
[Fin.sum_univ_three]`; `deg` at `Fin 3` fixtures evaluates reliably as
`rw [deg, Fin.sum_univ_three] <;> norm_num [adjacency]` where plain
`simp` leaves classical `Finset.filter`-card goals that `decide`
cannot close; `le_csInf` in the pinned Mathlib takes
`(s.Nonempty) (∀ b ∈ s, a ≤ b)` — no `BddBelow` argument — while
`csInf_le` takes `(BddBelow) (a ∈ s)`; `one_le_div`/`le_div_iff₀` for
the Rayleigh quotients; `linear_combination hsum * (…)` for the
constraint-identities (P₃: `hsum3 * (-3*y 0 + y 1 - 3*y 2)`); the
stale-olen recurrence at the import boundary (rebuild the module target
before elaborating the consumer).

**Verification:** spike first; `lake env lean` — zero errors/zero
warnings on `Fiedler.lean` and `Fiedler_QA.lean`, `Spectral.lean` at
exactly its pre-existing 8-warning baseline; explicit `lake build`
targets ✔ (module and QA); `#print axioms` as above; **full `lake
build` ✔ (2402/2403, "Build completed successfully") immediately
followed by `check_build_completeness.py` — 123/123 fresh, 0 stale, 0
missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass after the record sweep; scoreboard
regenerated (**2714/10/0**).

## The obligation this discharges

*(Premise corrected by the Step-0 verdict above: the "zero consumers
anywhere" claim below was stale — the derived layer's
`davisKahanTwoPoint` does invoke the theorem; the delivered obligation
is the zero Mathlib-layer / graph-theoretic consumers gap, which
`measure_load_bearing.py` did and does report.)*

`davis_kahan_sin_theta`
(`Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/DavisKahan.lean`)
was retired from axiom to fully proved theorem on 2026-08-21 — real hard
crust, not conditional on anything. Per `scripts/measure_load_bearing.py`,
it has **zero real theorem consumers anywhere in the shelf**: every
other file that imports the module does so for something else (Weyl,
Duhamel, Resolvent live nearby and are separately consumed), and nothing
actually invokes `davis_kahan_sin_theta` by name in a proof term. For the
standard eigenvector/subspace-perturbation bound behind spectral
clustering stability and PCA robustness theory generally to sit proved
and never once called is the sharpest version of this session's
robustness concern: a load-bearing-looking result whose exact hypothesis
shape (the two-cluster separation `δ`, the rank/tie case split) has never
been exercised by anything that would break if it were misstated.

## Assessed from

`DavisKahan.lean`'s exact statement (`initialProjector`, the sorted-index
separation hypothesis `evals hAE ⟨k+1⟩ - evals hA ⟨k⟩ ≥ δ`, the ℓ² operator
norm bound `‖E‖ / δ`), `Scaffold/Mathlib/GraphTheory/Fiedler.lean`
(`fiedlerIndex`, `fiedlerVector`, `fiedlerVector_eigen`, both built over
the **combinatorial** Laplacian `laplacian A`, requiring only
`hA : A.IsSymm` and `hcard : 2 ≤ Fintype.card V` — no regularity), and
`Scaffold/Mathlib/GraphTheory/Heat.lean`'s connected-graph kernel fact
(`laplacian_kernel_eq_span_onesVec` — used already in Foster's proof —
the Laplacian's zero-eigenspace is *exactly* `span {onesVec}` on every
connected graph, perturbed or not, so long as both `A` and `A + E` remain
valid connected-graph Laplacians).

## The statement (draft shape — subject to Step 0 correction)

**Step 1 (direct instantiation, tightly scoped):** for a connected
weighted graph `A` and a symmetric perturbation `E` such that `A + E` is
also a valid symmetric adjacency matrix, with the Fiedler eigenvalue
`λ₂` (index 1, i.e. `k = 1` in `DavisKahan`'s convention: the bottom-2
cluster) separated from the perturbed graph's third eigenvalue by `δ`,

```
davis_kahan_sin_theta (laplacian A) E hA hAE 1 hk δ hδ hsep
  : ‖initialProjector (laplacian (A + E)) hAE' 1
      - initialProjector (laplacian A) hA' 1‖ ≤ ‖E‖ / δ
```

instantiated directly — the rank-2 subspace spanned by `{onesVec,
fiedlerVector A}` moves by at most `‖E‖ / δ` under the perturbation.
This is a mechanical instantiation (no new proof machinery), but it is
the first real exercise of `davis_kahan_sin_theta`'s exact hypothesis
shape by a genuine graph-theoretic object rather than an abstract
symmetric matrix pair, and it composes cleanly with either
[spectral-sparsification-via-leverage-scores.md](spectral-sparsification-via-leverage-scores.md)
or
[matrix-hoeffding-spectral-gap-estimation.md](matrix-hoeffding-spectral-gap-estimation.md)
as the "then bound the subspace rotation" half of a concentration → subspace-stability
pipeline, if either of those lands first (not required — this proposal
stands alone with `‖E‖` as a hypothesis, not a derived quantity).

**Step 2 (the sharper, deferred statement — the actual payoff, not
authorized in Step 1):** isolate the **Fiedler vector's own** rotation,
not the rank-2 subspace containing it. Since `laplacian_kernel_eq_span_onesVec`
pins the index-0 component to the exact same fixed line `span {onesVec}`
in both `A` and `A + E` (connected graphs never move their kernel
direction — only the Laplacian null space, not the perturbation, decides
it), the rank-2 rotation bounded in Step 1 is entirely attributable to
the Fiedler component. Making that precise needs a new lemma: for
`P, Q` rank-2 symmetric idempotents both containing a common fixed
rank-1 subprojector `Π₀` (`P * Π₀ = Π₀`, `Q * Π₀ = Π₀`), bound the
distance between the residual rank-1 projectors `P - Π₀` and `Q - Π₀` in
terms of `‖P - Q‖` — plausible linear algebra, not yet verified against
the pin. **Step 0 must check this residual-projector lemma's exact
proof route (or find it already in `Spectral.lean`/`Resolvent.lean`)
before Step 2 is authorized**; if it does not close cheaply, Step 1's
rank-2 statement stands alone as the delivered consumer and Step 2 is
iceboxed with the specific obstruction recorded.

## QA obligations (draft — refine after Step 0)

1. A small connected fixture (K₂, a 3-path, or a 4-cycle) with a
   concrete symmetric perturbation `E` (e.g. a single edge-weight
   change), the projector distance computed both by the theorem and by
   direct eigenvector computation on the fixture, cross-checked.
2. A boundary witness: `δ` too small or the perturbation large enough to
   force the trivial bound `‖P − Q‖ ≤ 1` (the tie-case branches in
   `davis_kahan_sin_theta`'s own proof) — instantiated on the fixture to
   confirm the graph-theoretic wrapper inherits the tie-awareness
   correctly, not just the generic-case branch.
3. If Step 2 lands: the residual-projector lemma exercised on the same
   fixture, with the Fiedler vector's own angular movement computed by
   hand and compared to the derived bound.

## Acceptance bar

- Step 0 delivers a written verdict on Step 2's residual-projector
  lemma before it is attempted; Step 1 alone is a complete, valid
  delivery if Step 2 does not close cheaply.
- Zero new axioms; `davis_kahan_sin_theta` becomes a real consumed
  dependency, not merely an imported module.
- `docs/7_SGT_RADAR.md` axis 4 (Cuts/Expansion) is the natural re-score
  target — this is the first stability statement about the Fiedler
  partition itself, distinct from Fiedler's existing static
  conductance-certificate content.

## Companion

[Fiedler Partitioning (delivered)](fiedler-partitioning.md),
[Discharge Perturbation Axioms (Davis–Kahan delivery record)](discharge-perturbation-axioms.md),
`docs/7_SGT_RADAR.md` axis 4.

### Companion consumer delivered: the concentration → subspace-stability pipeline (2026-08-28)

The named companion follow-on — composing these stability theorems
with a concentration tail — was **delivered the same day** by run
`20260828T132541Z-run-1` as `Derived/EdgePerturbationDrift.lean`'s
`edgePerturbation_fiedlerSubspace_drift` /
`edgePerturbation_fiedlerLine_drift` (composing
`fiedlerLine_stability`/`fiedlerSubspace_stability` with
`edgePerturbation_norm_tail`, the matrix-Hoeffding consumer, through
the packaging identity `laplacian (perturbWeight A p ω) = ∑ₑ
perturbSummand`; conditional on `matrix_hoeffding` via the tail alone,
with the Davis–Kahan side and this program's kernel identification
proved). See the matrix-Hoeffding proposal's follow-on delivery record
for the full account. This makes `fiedlerLine_stability` load-bearing
inside a probability bound — the Fiedler program's kernel
characterization ecosystem now exercises its content under a *random*
perturbation.
