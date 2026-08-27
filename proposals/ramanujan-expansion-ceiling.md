# Proposal: The Ramanujan Expansion Ceiling — a Light Consumer Pairing Alon–Boppana with Cheeger

**Status:** Proposed; **priority:** Medium-High (light, mechanical
composition of two already-proved theorems — no new mathematical
content beyond algebraic rearrangement and one small scaling lemma).
This document authorizes no Lean changes, axiom admissions, commits, or
external publication on its own — Step 0 (the compatibility checks
below) must land before Step 1 begins.

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
