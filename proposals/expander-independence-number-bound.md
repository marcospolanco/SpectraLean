# Proposal: The Hoffman-Type Independence Number Bound — a Real Consumer for the Expander Mixing Lemma

**Status:** COMPLETE — Steps 0+1 delivered 2026-08-25 by run
`20260825T064753Z-run-1` (see the delivery record at the end of this
document; zero new axioms, `Expander.lean`'s first theorem consumer,
QA +21 in `Expander_QA.lean`'s Step-5 section). Originally **Proposed;
priority:** Medium-High. This document authorizes
no Lean changes, axiom admissions, commits, or external publication on
its own — Step 0 (the survey below) must land before Step 1 begins.

## The obligation this discharges

`Scaffold/Mathlib/GraphTheory/Expander.lean`'s `expander_mixing_lemma`
(delivered `f45cf8e`, decidable-spectral-certificates Step 2) is a real,
substantial, classical result — 24 declarations of genuine spectral
discrepancy machinery — with **zero real theorem consumers anywhere in
the shelf**, confirmed by `scripts/measure_load_bearing.py`. It was
proved as the certificate program's payoff and then never built upon.
This is a sharper case than the concentration-axiom valleys addressed
earlier in this session: `expander_mixing_lemma` is fully proved hard
crust, not an axiom, so its exact hypothesis shape (`d`-regularity, the
`μ`-bound on both non-trivial ends of the spectrum, the specific
`edgeWeight`/discrepancy statement) has genuine mathematical content
sitting unexercised by anything that would break if a constant or
direction were misstated.

**A companion false lead, recorded so it is not re-investigated:**
`Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/ProjectionGap.lean`
was also found "never built" by the same completeness-check incident
that motivated this proposal's sibling
([verify-build-completeness.md](verify-build-completeness.md)). It is
**not** a valley — `measure_load_bearing.py` shows 5 real Mathlib
consumers (it is load-bearing inside the Davis–Kahan proof chain,
`discharge-perturbation-axioms.md`'s delivered route). Its QA file being
absent from any build artifact was purely the orphaning bug the
completeness check now catches; the module itself was never idle. Do
not propose a consumer for it on the strength of that incident alone.

## Assessed from

`Expander.lean`'s exact statement of `expander_mixing_lemma` (`d`-regular,
symmetric, nonnegative weights; `μ` bounding both `|d − λ₂|` and
`|d − λ_n|`; the discrepancy bound on `edgeWeight A S T`), and a direct
search of the pinned Mathlib
(`.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/`) for
independence-number machinery: **none exists** — no
`SimpleGraph.independenceNumber`, no `IsIndepSet` predicate, nothing.
This means the target statement must be defined natively over Scaffold's
own `WAdj`/`Finset V` conventions, matching how every other
combinatorial predicate in this shelf (`cutTestVector`, `conductance`,
`fiedlerPartition`) is already built — not adapted from an upstream
Mathlib definition that does not exist.

## The statement (draft shape — subject to Step 0 correction)

The classical Hoffman ratio bound, specialized to the mixing lemma
already delivered: for `S` an independent set (no edge weight within
it: `∀ i j ∈ S, i ≠ j → A i j = 0` — the natural nonnegative-weight
reading of "independent" over a weighted graph) of a `d`-regular graph
with second-eigenvalue bound `μ` exactly as `expander_mixing_lemma`
already hypothesizes,

```
(S.card : ℝ) ≤ μ * (Fintype.card V : ℝ) / (d + μ)
```

**Route (mechanical, one application):** instantiate
`expander_mixing_lemma` at `T = S`. Independence collapses
`edgeWeight A S S` to `0` (the sum of a zero function — a short lemma,
likely already close to `edgeWeight`'s existing algebra in
`Expander.lean`'s early sections). The inequality becomes
`d·|S|²/n ≤ μ·|S|·(n−|S|)/n` (the `√` collapses because `S.card = T.card`
makes the product under the root a perfect square — `Real.sqrt_sq` at a
nonnegative quantity). Cancel `|S|/n` (handling `S = ∅` as a trivial
`0 ≤ …` degenerate case first) and rearrange
`d|S| ≤ μ(n−|S|)` to the stated bound. This is genuinely a short,
mechanical derivation from the delivered lemma — the interesting content
is entirely already proved; this proposal's job is packaging it as the
named classical corollary, not new spectral mathematics.

**Step 0 must check, before stating:**
1. Whether `edgeWeight A S S = 0` under the independence hypothesis is
   a one-line consequence of `edgeWeight`'s definition
   (`Expander.lean:91`, a `Finset.sum`) or needs a short supporting
   lemma.
2. The exact degenerate-case handling at `S = ∅` (bound reads `0 ≤ …`,
   trivial) and at `S.card = Fintype.card V` (independent set on the
   whole graph forces `d = 0` — a companion fence worth stating, not
   just avoiding division by zero).
3. Whether `μ + d > 0` needs its own hypothesis or is already implied
   (on a nontrivial graph with `d > 0` and `μ ≥ 0` from `hμ`'s `abs`
   structure, likely free).

## QA obligations (draft — refine after Step 0)

1. A concrete `d`-regular fixture with a known independent set (e.g. a
   bipartite-flavored small graph, or the empty-edge complement of a
   clique) where the bound is evaluated numerically and the independent
   set's actual size checked against it — the fixture should make the
   bound non-vacuous (an independent set that is provably *close to* the
   bound, not trivially far under it, per this session's QA-tightness
   discipline).
2. The degenerate `S = ∅` case and the "independent set = whole graph"
   fence (forcing `d = 0`, refuted on a positive-degree fixture) as
   proved boundary witnesses, not just hypothesis guards.
3. A non-independent-set instantiation showing the hypothesis is load-
   bearing (`edgeWeight A S S ≠ 0` on a fixture with an internal edge,
   the conclusion's derivation genuinely blocked, not just unproved).

## Priced follow-on, not authorized here

**The spectral diameter bound** (`diam(G) = O(log n / log(d/μ))`,
the other classical Expander Mixing Lemma consequence) is explicitly
**not** in this proposal's scope — it needs an iterated ball-growth
argument over `SimpleGraph.dist`/walk-length machinery, a genuinely
harder combinatorial induction than this proposal's one-shot algebraic
corollary, and belongs in its own document if a named consumer prices
it, per the one-step discipline this shelf already follows for Cheeger
and Krylov.

## Acceptance bar

- Step 0 delivers a written verdict on the three checks above before
  any shelf Lean is written.
- Zero new axioms — this is a corollary of already-proved hard crust.
- `Expander.lean` gains its first real theorem consumer.
- `docs/7_SGT_RADAR.md` axis 4 (Cuts/Expansion) is the natural re-score
  target.

## Companion

[Verify Build Completeness](verify-build-completeness.md) (the
incident this proposal responds to), `proposals/decidable-spectral-certificates.md`
(the Expander Mixing Lemma's original delivery), `docs/7_SGT_RADAR.md`
axis 4.

---

## Delivery record (2026-08-25, run `20260825T064753Z-run-1`)

Steps 0+1 delivered in one run, per the one-run precedent of the recent
hard-crust deliveries. **Zero new axioms (count stays 10; `#print
axioms` via `wip/hoffman_axcheck.lean` on all 26 new declarations — 4
public + 22 QA: exactly `propext, Classical.choice, Quot.sound`, every
one). QA 2152 → 2173 (+21 in `Expander_QA.lean`'s new Step-5 section,
no new file).**

### Step 0 verdicts (each now a proved fact, not a design assumption)

1. **The collapse is one line — under the diagonal-inclusive reading.**
   `IsIndependentSet A S := ∀ i ∈ S, ∀ j ∈ S, A i j = 0` (self-loops
   count against independence — the looped-graph reading, and the exact
   reading that collapses the double sum). `edgeWeight A S S = 0` is
   then a single `Finset.sum_eq_zero`.
2. **The whole-graph corner is a real fence, not a division guard.**
   Delivered as `deg_eq_zero_of_isIndependentSet_univ` (independence
   of `univ` forces `deg ≡ 0`, no regularity needed), refuted on the
   all-degrees-`2` `C₄` by `expC4_univ_fence_QA`.
3. **`0 < d` is NOT free — it is an explicit, load-bearing hypothesis.**
   On the all-zero `2×2` adjacency every other hypothesis holds
   *including* independence of `univ` and the spectral hypothesis at
   `μ = 0` exactly (the whole Laplacian spectrum is pinned zero in QA
   through the eigen-action `0 = λ • v` at unit eigenvectors plus
   `evals_mem_eigvalOf`), yet the division-form conclusion reads
   `2 ≤ 0·2/(0+0) = 0` — refuted by `expZeroAdj2_fence_isolation_QA`
   with exactly `hd` isolated. The theorem therefore carries
   `hd : 0 < d` explicitly, consumed only through `0 < d + μ` (noted in
   the docstring: a consumer at `d = 0 < μ` may still take the trivial
   bound `|S| ≤ |V|` by other means).

### Step 1 (delivered)

The new section 8 of `Scaffold/Mathlib/GraphTheory/Expander.lean` (no
new imports, no umbrella change): `IsIndependentSet`,
`edgeWeight_self_eq_zero_of_isIndependentSet`,
`deg_eq_zero_of_isIndependentSet_univ`, and the headline
`hoffman_independence_bound` — `(S.card : ℝ) ≤ μ * (Fintype.card V : ℝ)
/ (d + μ)` at exactly the mixing lemma's hypothesis set plus `hd`. The
proof is the priced route verbatim: the lemma at `T = S`, the collapse,
`Real.sqrt_mul_self` at the nonnegative `|S|·(|V|−|S|)` (the perfect
square), clear the positive `n` (`div_le_iff₀` + `div_mul_cancel₀`),
cancel the positive `|S|` (`nlinarith`; the `|S| = 0` case closes as
`0 ≤ μn/(d+μ)`), divide by `d + μ > 0` (`le_div_iff₀` +
`linear_combination` with zero coefficient slack).
`expander_mixing_lemma` is consumed directly in the proof — its first
theorem consumer anywhere, which is the proposal's entire purpose.

### QA (+21, all four mandated obligations)

1. **Non-vacuous tight witnesses, both classical regimes:** `C₄`'s
   opposite pair `{0,2}` *attains the bound with equality* at the
   Step-4-exact `μ = 2` (`|S| = 2 = 2·4/(2+2)` — the bipartite
   Hoffman-equality case) and `K₃`'s singleton `{0}` attains it at the
   exact `μ = 1` (`1 = 1·3/(2+1)` — the clique case, where the bound
   pins the maximum independent set exactly on the least-expanding
   fixture). Both instantiations discharge `hμ` from the file's own
   exact pins (`expC4_mu_le_two_QA`, `expK3_mu_le_one_QA`), not
   assumed bounds.
2. **Degenerate boundaries as proved witnesses:** the `∅` instance
   (`expC4_hoffman_empty_QA`) and the whole-graph fence pair
   (`expC4_univ_not_indep_QA` raw refutation +
   `expC4_univ_fence_QA` through the corner lemma, `2 = 0` false).
3. **The independence hypothesis load-bearing, isolated:**
   `expC4_hoffman_fence_isolation_QA` verifies positive degree,
   cardinality, and the `μ = 2` hypothesis on `C₄`, refutes
   independence of `univ`, and refutes the hypothesis-free conclusion
   (`4 ≤ 2` false). The mechanism witness is explicit: the internal
   cut weight at `univ` is `8` (`exp_ew_univ_QA`) and at the half set
   `{0,1}` is `2` (`exp_ew_01_01_QA`) — nonzero, so the
   `edgeWeight = 0` collapse is genuinely blocked; on the half set the
   conclusion happens to hold numerically (`2 ≤ 2`), which is exactly
   why the fence must live at `univ` and at the mechanism rather than
   at the conclusion.
4. **The `d = 0` fence** (the Step-0 verdict-3 answer in proved form):
   the new `expZeroAdj2` fixture with
   `expZeroAdj2_fence_isolation_QA` — every hypothesis except `hd`
   verified, `hind` *included*, the conclusion refuted. Exactly `hd`
   is isolated.

### Verification

Spike first (`wip/hoffman_spike.lean`, several rounds to green before
any module touched; the recurring fixes are the pin-technique list
below). `lake env lean` on both changed modules — zero errors, zero
warnings each; explicit `lake build` targets ✔ (module 2009/2009, QA
2010/2010); `#print axioms` via `wip/hoffman_axcheck.lean` on all 26
new declarations — the standard three only; **full `lake build` ✔
(2264 targets, "Build completed successfully") immediately followed by
`check_build_completeness.py` — 104/104 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (2173/10/0,
idempotent by md5). Records updated: this document, the scoreboard
(all five verification rows + the interpretation bullet),
`index/map/spectral_graph.md` (the Expander section's header + 4
declaration rows), `proposals/README.md` (the High row retired to
Delivered), README (2173; the status-paragraph clause; the
module-table row), the radar (QA axis synced 2152/54 → 2173/55, held
4.0), `docs/6_SGT_BACKLOG.md` (the expansion item's update), the
execution plan, and the activity log. Nothing committed; the prior
runs' uncommitted deliveries preserved untouched.

### Pin-technique list (spike findings, for future runs)

- `Real.mul_self_sqrt` does not exist at this pin — the perfect-square
  collapse is `Real.sqrt_mul_self (h : 0 ≤ a) : √(a * a) = a` (the
  mixing lemma's own QA used it; the first-draft name was wrong).
- `0 - x` inside an `abs` after a hypothesis rewrite: `sub_zero` is
  `a - 0`; the needed pair is `zero_sub` then `abs_neg`.
- `add_pos` demands strict both sides; `0 < d + μ` from `0 < d` and
  `0 ≤ μ` goes through `linarith` (no `add_pos_nonneg` at this pin).
- `div_le_iff₀`/`le_div_iff₀` are iff with the positivity argument
  first; after `.mp` the multiplied-out denominator needs one
  `div_mul_cancel₀ _ hn.ne'` step.
- Fin-set literal membership: `fin_cases` on the indices FIRST, or
  better drive the split from the membership disjunction itself —
  `rcases hi with rfl | rfl` (the Exhaustive_QA pattern); simp at a
  variable-index membership produces `(fun i => i) ⟨0, ⋯⟩` beta-redex
  coercion goals that neither `simp` nor `decide` close.
- `(card : ℝ) = k` goals: decide the ℕ equation first (`({0,2} :
  Finset (Fin 4)).card = 2` by `decide`), then `exact_mod_cast` —
  `by decide` on the ℝ-cast goal gets stuck on `Classical.propDecidable`.
- Rewriting a matrix definition under proof-valued arguments (e.g.
  `rw [lap_zeroAdj2_eq_zero] at hev` where `hev` mentions
  `eigvecOf (laplacian A) (laplacian_symmetric A _) i`) fails on a
  dependent motive; the durable route is a `funext`-shaped
  entrywise `have` (`simp [Matrix.mulVec, entrywise_zero_lemma]`).
- `Matrix.sub_apply` does not fire under an un-folded `laplacian` —
  `show (degreeMatrix A - A) i j = 0` bridges definitionally first.
- The scoreboard's declaration counter is ASCII-only (the standing
  trap): all new QA identifiers are ASCII (`expZeroAdj2`, etc.).

### Priced follow-on (unchanged, not started)

The spectral diameter bound remains out of scope (its own document if
a named consumer prices it, per the one-step discipline). A
`MetricSpace`-free independence-number *packaging* (`α(A) := max |S|`
over the Finset powerset) is one `Finset.exists_max_image` away but
was not delivered — no consumer names it. The Hoffman bound's
`λ_min`-form (the non-regular generalization) is a separate statement
shape with no current consumer.
