# Proposal: The Ramanujan Expansion Ceiling — a Light Consumer Pairing Alon–Boppana with Cheeger

**Status:** COMPLETE — Step 0 (the verdict below) and Step 1 (the
delivery) both delivered 2026-08-27 by run `20260827T220230Z-run-1`,
selected per priority item 0 as the Active table's only High row.
Zero new axioms (count stays 10); `#print axioms` via
`wip/ram_axcheck.lean` on all 13 audited declarations (5 module + 8
QA) reads exactly `propext, Classical.choice, Quot.sound`, every one —
the ceiling consumes two *proved* theorems, so the whole chain is
unconditional hard crust. QA 2659 → 2666 (+7 theorem declarations;
the `abC8_half` cut fixture is a `def` and not counted). See the
delivery record at the end.

Original header: Proposed; **priority:** Medium-High in this document,
raised to the Active table's only **High** row 2026-08-27 when the
sparsification High row completed. Light, mechanical composition of
two already-proved theorems.

## Step 0 verdict (2026-08-27, before any shelf Lean)

All three checks answered from source evidence (`AlonBoppana.lean`,
`Cheeger.lean`, `Spectral.lean`, and the pinned Mathlib):

1. **Regularity predicates — identical, no bridge.**
   `AlonBoppana.lean`'s `IsDRegular A d` is *defined* as
   `∀ i, deg A i = d` (`GraphTheory/AlonBoppana.lean`, the `def` at the
   d-regularity interface section) — exactly `Cheeger.lean`'s `hd`
   hypothesis, definitionally. Cheeger's `hd : ∀ i, deg A i = d` can be
   passed where `IsDRegular A d` is expected and vice versa; the
   composition states `hd : IsDRegular A ((d : ℕ) : ℝ)` and hands it to
   both theorems unchanged.
2. **The scaling lemma — absent from shelf and pin; the variational
   route is cheapest.** No `eigenvalues_smul`/`charpoly_smul` anywhere
   in the pinned Mathlib (direct search of `Mathlib/LinearAlgebra/
   Matrix/`); no `secondEval`/`evals` scaling lemma in `Spectral.lean`
   (confirming this proposal's earlier direct search). The cheapest
   route is *not* an eigenvalue-multiset map but the variational one:
   rewrite both `secondEval (c • M)` and `secondEval M` through
   `secondEval_variational` (which requires PSD + `onesVec` kernel —
   hypotheses both the combinatorial and the regular-normalized
   Laplacian carry on file: `laplacian_psd`/`laplacian_mulVec_onesVec`,
   `regularNormalizedLaplacian_psd`/`regularNormalizedLaplacian_
   mulVec_onesVec`), then the sInf constraint set of `c • M` is the
   image of `M`'s under `r ↦ c r` (`rayleigh (c•M) x = c * rayleigh M x`
   at `x ≠ 0`), and `sInf (c • S) = c * sInf S` at `0 < c` by a
   two-direction ping-pong (`le_csInf`/`csInf_le`, BddBelow by 0 from
   PSD — the same support `secondEval_le_rayleigh`'s proof already
   builds). **Statement decision:** the lemma ships as
   `secondEval_smul_of_pos` in `Spectral.lean` at the PSD + kernel
   generality (not the fully general `secondEval (c • M) = c *
   secondEval M` for arbitrary symmetric `M`, which would need the
   absent eigenvalue-multiset machinery); both operators in this
   composition satisfy the hypotheses, so nothing is lost here and the
   hypothesis-free generalization stays priced as future work with a
   named need.
3. **`h01`/`hnonneg` — compatible, one line.** `h01 : ∀ i j, A i j = 0 ∨
   1 ≤ A i j` gives Cheeger's `hnonneg : ∀ i j, 0 ≤ A i j` by
   `Or.elim` + `zero_le'`/`le_of_lt one_pos`. No modification of either
   source theorem.

**One further piece identified (still light):** the operator identity
joining the two statements' homes — `((d:ℕ):ℝ) • 1 − A =
((d:ℕ):ℝ) • regularNormalizedLaplacian A ((d:ℕ):ℝ)` under `IsDRegular`
and `d ≠ 0`. Cheeger.lean already carries `smul_regularNormalizedLaplacian`
(`d • L_sym = laplacian A`); the missing half is `degreeMatrix A =
d • 1` under regularity, a one-`ext` entrywise proof. The identity
joins the two, and lives with the composition in `AlonBoppana.lean`
(which gains the `Cheeger` import — no cycle: Cheeger predates
AlonBoppana and imports neither it nor anything that does).

**Placement decisions:** the scaling lemma in `Spectral.lean`'s
`Lambda2Variational` section beside its engine siblings; the ceiling
(`ramanujan_expansion_ceiling`) in `AlonBoppana.lean`'s new closing
section so its QA sits beside the C₈ fixture stack it needs
(`abC8_h01`, `abC8_isDRegular`, `abC8_far01`, the tree-ball instances).
The scaling lemma's QA (K₂ two-route pin) goes to `Variational_QA.lean`
beside the existing K₂ λ₂ = 2 pins it clones.

**QA shape decision (fixture honesty):** C₈ hosts only `k = 0` — the
on-file `abC8_far_fence` proves `distEdge = 3 < 4`, so `k = 1` fails
`hfar` there, and no C₈ edge pair has `distEdge ≥ 5` (the maximum
cross-distance on an 8-cycle is 3). The two-`k` improvement obligation
is therefore discharged as arithmetic on the statement's own constants
(the ceiling expression at `d = 2` is `√(2/(k+1))`, strictly decreasing
in `k`, `1 = ceiling(1) < √2 = ceiling(0)`) with the honest note; a
larger fixture hosting `k = 1` (C₁₂: level oracles for 12 vertices plus
four ≥ 5 cross-distance refutations) is priced as a follow-on, not
built this run.


## The obligation this discharges

`GraphTheory.AlonBoppana` (delivered 2026-08-27, COMPLETE) proves an
**upper** bound on the shifted-adjacency second eigenvalue
(`secondEval (d•1 − A) ≤ d − 2√(d−1) + O(1/(k+1))`,
`alonBoppana_nilli_classical`) — the textbook statement that no
d-regular graph's spectral gap can be arbitrarily large: it establishes
an **obstruction**, a ceiling no graph can beat. (Ramanujan graphs are
the literature's separate answer to the matching question of whether
that ceiling is *tight* — whether some family actually gets close to
it — via their own construction/existence theory, e.g. Lubotzky–
Phillips–Sarnak. Alon–Boppana does not prove Ramanujan graphs exist or
attain anything; it only proves nothing can do *better*. This proposal
inherits that same scope — see "What this is not" below.) Per this
session's load-bearing discipline, a freshly-delivered theorem with
zero real downstream consumers is exactly the kind of gap
`scripts/measure_load_bearing.py` was built to catch — and
`AlonBoppana.lean` is one day old, so it has none yet. This proposal is
the natural, low-cost first consumer: pairing it with the already-proved
`cheeger_lower_bound` (`cheegerConstant A ^ 2 / 2 ≤ secondEval
(regularNormalizedLaplacian A d)`) turns two one-directional facts about
the same quantity (`secondEval`) into the field's actual textbook
punchline — **an explicit numerical ceiling on how good an expander any
d-regular graph satisfying Alon–Boppana's hypotheses can be**. This is
the sentence every SGT course states immediately after proving
Alon–Boppana; Scaffold currently proves the inequality but never says
the sentence.

## What this is, precisely — and what it is not

**Is:** the obstruction/ceiling direction only — a pure corollary
composing two already-proved theorems, stating that no graph satisfying
the hypotheses can have conductance exceeding an explicit numerical
value. This is the "Alon–Boppana establishes the ceiling" half of the
textbook picture.

**Is not**, and must not be described as, any claim about the ceiling
being *tight* or *attained*. Proving that some family of graphs (e.g.
Ramanujan graphs) actually approaches this ceiling is a separate,
much harder **construction/existence** program (naming an explicit
family, like LPS's number-theoretic construction, and proving *its*
spectral gap) that this proposal does not attempt and that is not a
byproduct of this composition. The name "Ramanujan Expansion Ceiling"
is chosen for communicative clarity — it names the concept the ceiling
is a ceiling *for* — not as a claim that this delivery says anything
about Ramanujan graphs themselves. If Scaffold ever pairs this ceiling
with a genuine attainment/tightness result on a named family, *that*
pairing would earn the word "tight," not this proposal alone.

## Assessed from

`AlonBoppana.lean`'s `alonBoppana_nilli_classical` (the cleaner
classical-form statement, stated on `secondEval (d•1 − A)` — the
unnormalized shifted-adjacency operator, i.e. the combinatorial
Laplacian `laplacian A` on a d-regular graph) and `Cheeger.lean`'s
`cheeger_lower_bound` (stated on `secondEval (regularNormalizedLaplacian
A d)`, where `regularNormalizedLaplacian A d := 1 − d⁻¹ • A`). The two
statements live on different but linearly related operators:
`d • regularNormalizedLaplacian A d = d•1 − A` exactly (unfold the
definition, `smul_sub`/`smul_smul`), so composing them needs one
scaling fact for `secondEval` under positive-scalar multiplication —
**checked absent from `Spectral.lean` by direct search** (no
`secondEval_smul` or equivalent) — plus routine algebraic rearrangement.

## The statement (draft shape — subject to Step 0 correction)

For a d-regular graph satisfying `alonBoppana_nilli_classical`'s exact
hypotheses (the 0/1-ish weight condition, two far-apart tree-ball
vertex pairs, connectivity, `1 < d`, `2 ≤ card V`):

```
cheegerConstant A ≤ Real.sqrt (2 * (1 - 2 * Real.sqrt (d - 1) / d
  + 2 * Real.sqrt (d - 1) / (d * (k + 1))))
```

**Route (mechanical, two compositions):**
1. Divide `alonBoppana_nilli_classical`'s conclusion by `d` and rewrite
   `secondEval (d•1 − A) / d = secondEval (regularNormalizedLaplacian A
   d)` via the priced scaling lemma plus the definitional identity —
   this gives the upper bound on `secondEval (regularNormalizedLaplacian
   A d)` in the statement above's radicand.
2. Combine with `cheeger_lower_bound`'s `cheegerConstant A ^ 2 / 2 ≤
   secondEval (regularNormalizedLaplacian A d)` — chain the two
   inequalities and take square roots (`Real.sqrt_le_sqrt` at the
   nonneg side, `Real.sqrt_sq`/`pow_two` bookkeeping).

Every step is routine real-arithmetic rearrangement once the scaling
lemma exists; the two source theorems are consumed exactly as
delivered, with no restatement.

**Step 0 must check, before stating:**
1. Whether `AlonBoppana.lean`'s `IsDRegular A d` and `Cheeger.lean`'s
   `∀ i, deg A i = d` hypothesis are the same predicate or need a
   one-line bridge — both should reduce to the same row-sum condition,
   but the exact defeq/lemma-form has not been checked.
2. The precise scaling lemma shape (`secondEval (c • M) hM' hcard = c *
   secondEval M hM hcard` for `0 < c`) and its cheapest proof route —
   likely a short consequence of `evals`'s sort-and-scale behavior
   already used elsewhere in `Spectral.lean`, not new machinery.
3. Whether `AlonBoppana`'s `h01` (0/1-ish weights) and `Cheeger`'s
   `hnonneg` (general nonnegative weights) hypotheses are compatible on
   the same input `A` without modification (they should be — `h01`
   implies `hnonneg` — but confirm before composing).

## QA obligations (draft — refine after Step 0)

1. A concrete fixture already used by both source files if one exists
   (otherwise a small new one) where the composed ceiling is evaluated
   numerically and checked against the fixture's actual `cheegerConstant`
   — confirming the composed bound is non-vacuous, not just formally
   well-typed.
2. A degenerate/boundary check: as `k → ∞` (informally, at increasing
   `k` values on a fixture where larger tree-balls remain valid), the
   ceiling should tighten toward the classical `√(2(1 − 2√(d−1)/d))` —
   at minimum, evaluate at two different `k` and confirm the bound
   improves, per this session's route-independence and non-vacuity
   discipline.

## Acceptance bar

- Step 0 delivers a written verdict on the three checks above before
  any shelf Lean is written.
- Zero new axioms — a pure corollary of two already-proved hard-crust
  theorems.
- `AlonBoppana.lean` gains its first real theorem consumer.
- No delivery record, docstring, or summary describes this result as
  showing the ceiling is *tight* or *attained* by any graph or family
  — see "What this is not" above; this is a hard acceptance-bar item,
  not a style note.
- `docs/7_SGT_RADAR.md` axis 4 (Cuts/Expansion) is the natural
  re-score target — this is the first statement in the shelf
  connecting the "how good can expansion be" upper-limit direction to
  the existing "how good is this graph's expansion" lower-bound
  machinery (Cheeger, Hoffman, the Expander Mixing Lemma).

## Companion

[The Alon–Boppana Bound for d-Regular Graphs (delivered)](alon-boppana-bound.md),
[Prove Cheeger's Easy/Hard Direction](discharge-perturbation-axioms.md),
`docs/7_SGT_RADAR.md` axis 4.

## Delivery record (2026-08-27, run `20260827T220230Z-run-1`)

Delivered in three pieces, spikable end to end before any shelf Lean
(`wip/ram_spike.lean`, zero errors / zero warnings):

1. **The engine** (`Spectral.lean`'s `Lambda2Variational` section,
   beside `secondEval_le_rayleigh`): `smul_isSymm` (public — consumed
   cross-module), the private support layer (`quadForm_smul_var`,
   `rayleigh_smul_of_ne`, `sInf_image_mul_pos`, the constraint-set
   nonemptiness clone and BddBelow-by-zero), and the two public
   lemmas **`secondEval_smul_of_pos`** (the Step-0 verdict's exact
   statement: both sides through `secondEval_variational`, the
   constraint set of `c • M` as the positive-scaled image, `sInf`
   commuting at `0 < c` by the two-direction ping-pong) and
   **`secondEval_congr`** (matrix equality respected at
   possibly-different symmetry proofs — proof irrelevance).
2. **The composition** (`AlonBoppana.lean`'s new `ExpansionCeiling`
   section; the file gains the `Cheeger` import — no cycle):
   `smul_one_sub_eq_smul_regularNormalizedLaplacian` (`d • 1 − A =
   d • L_sym` under regularity, via `smul_regularNormalizedLaplacian`
   plus the `degreeMatrix = d • 1` half) and the headline
   **`ramanujan_expansion_ceiling`** — `cheegerConstant A ≤
   √(2 (1 − 2√(d−1)/d + 2√(d−1)/(d (k+1))))` at exactly the
   Alon–Boppana hypothesis stack, both source theorems consumed
   verbatim with `h01 → hnonneg` the only bridge.
3. **The QA** (both obligations plus the engine's own):
   `Variational_QA.lean`'s new `ScalingK2` section —
   `k2_secondEval_smul_three_raw` (the sorted spectrum of `3 • L(K₂)`
   is `[0, 6]` by trace `3·2`, determinant `3²·0`, sortedness)
   against `k2_secondEval_smul_three_thm` (the lemma joined to the
   on-file `λ₂ = 2` pin) — two routes to `6` sharing no mechanism —
   and `k2_secondEval_smul_neg_fence_QA` (at `c = -1` the sorted
   spectrum is `[-2, 0]`, second entry `0 ≠ -2`: the conclusion
   refuted where the `0 < c` hypothesis fails); `AlonBoppana_QA.lean`'s
   new Step 6 — `abC8_ceiling_instance` (the ceiling evaluating
   numerically to `√2` on C₈ at `k = 0`),
   `abC8_cheegerConstant_le_quarter` (the fixture's actual Cheeger
   constant `≤ 1/4` by the exhibited half-set cut through
   `conductance_ge_cheegerConstant` — the independent cut-level route;
   the ceiling holds with strict slack: non-vacuous, never tight, per
   the hard acceptance-bar item), and `abC8_ceiling_improves_arith`
   (the two-`k` improvement pinned as `1 < √2` on the statement's own
   constants at `d = 2`, with the honest note that C₈ hosts only
   `k = 0` per the on-file `abC8_far_fence`).

**Technique findings** (for future composition-shaped work):

- `λ` is the `fun` keyword: an identifier like `h2λ` breaks parsing
  with a misleading "unexpected token" error at a distant column.
- Rewriting a *matrix equality* under a proof-carrying application
  (`secondEval M hM hcard`) fails ("motive is not type correct" or a
  silent no-op, depending on direction): the `hM` argument's type
  mentions `M`. The robust route is `secondEval_congr` stated with
  both proofs as *hypotheses* — then the resulting whole-application
  equation rewrites cleanly.
- `Matrix.smul_mulVec_assoc` in the forward direction (`(b • A) *ᵥ v =
  b • (A *ᵥ v)` is its RHS/LHS order to check — the `←` first
  instinct failed).
- `BddBelow` destructuring: the pin has no `lowerBounds_le`; use
  `mem_lowerBounds.1 hm r hr`.
- `rw [laplacian]`-style rewriting of a plain `def` needs the
  `rw [show laplacian A = degreeMatrix A - A from rfl]` equation
  form.
- `Real.sqrt_le_sqrt` in this pin is the single-argument globally
  monotone form; `Real.sqrt_lt_sqrt` takes `(hx : 0 ≤ x) (h : x < y)`
  in that order.
- `norm_num` *does* evaluate inside `√` at `d = 2` (it reduced
  `2 * (1 - 2√1/2 + 2√1/(2·1))` to `2`, leaving the goal `1 < √2`);
  close that by rewriting `1 = √1` backwards (`Real.sqrt_one.symm`)
  and applying `Real.sqrt_lt_sqrt`.
- Width-8 *Finset-literal* sums behave under `simp [setname]` (a
  `Finset.sum_insert` unfold plus `ring`): the recorded `vecCons`
  opacity trap is specific to *matrix* literals — the two sum-unfolding
  helpers (`abC8_sum_half`/`abC8_sum_half_compl`) were each three
  lines.
- The stale-olen recurrence: elaborating a consumer module right
  after editing its import requires the explicit target rebuild
  first (hit once, at the Spectral → AlonBoppana boundary; the
  documented remediation).

**Verification:** spike first (`wip/ram_spike.lean`, all pieces to
zero errors/warnings before any shelf Lean); `lake env lean` on all
four touched files — zero errors, and warnings exactly at the
pre-existing baselines (Spectral.lean's 8 pre-existing;
Variational_QA.lean's 7 pre-existing; AlonBoppana.lean and
AlonBoppana_QA.lean clean); explicit `lake build` targets ✔ (all four
modules, 2193/2193 among them); `#print axioms` via
`wip/ram_axcheck.lean` — all 13 audited declarations exactly the
standard three; **full `lake build` ✔ (2400/2401, "Build completed
successfully") immediately followed by `check_build_completeness.py`
— 119/119 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no
issues), `check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**2666/10/0**). Records swept: this proposal, the
Active-table retirement (`proposals/README.md`), README (2666), the
radar (axis 4's evidence clause + the ceiling noted with the score
held at 5.0 per protocol — a composition, not a new family; the QA
axis synced 2659 → 2666), the scoreboard (a verification row + the
interpretation bullet), backlog item 3 (the ceiling clause), the
index map (the new declarations), the execution plan, and the
activity log.

**Scope statement (repeated from the acceptance bar):** this delivery
is the obstruction/ceiling half of the textbook picture only. It
proves nothing about Ramanujan graphs, tightness, or attainment; no
downstream record may describe it as such.

**Priced follow-ons:** the hypothesis-free general scaling lemma
(`secondEval_smul` for arbitrary symmetric `M`, needs
eigenvalue-multiset machinery the pin lacks — no named consumer); a
`k = 1`-hosting fixture (C₁₂: twelve-vertex level oracles plus four
`≥ 5` cross-distance refutations) if ever wanted for instance-level
two-`k` QA; the asymptotic family corollary (a named d-regular family
with `diam → ∞` — the Alon–Boppana proposal's own deferred item).
