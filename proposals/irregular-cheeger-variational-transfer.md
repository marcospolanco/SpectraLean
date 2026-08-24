# Proposal: The Irregular Cheeger Inequality via Variational Transfer

**Status:** Proposed; **priority:** Medium-High. This document authorizes
no Lean changes, axiom admissions, commits, or external publication on
its own — Step 0 (the survey below) is mandatory and may find this is a
multi-phase program rather than a one-step delivery, per the Cheeger
easy/hard-direction precedent (which itself took a Step-0 survey plus
three bounded components).

## The obligation this discharges

`Scaffold/Mathlib/GraphTheory/VariationalTransfer.lean` was built
specifically to bridge the combinatorial and normalized Laplacians
(`rayleigh_normalizedLaplacian_degreeSqrt`, `normalizedLaplacian_psd`),
and its own module docstring names its intended purpose: *"the
variational interface through which Cheeger-type bounds and mixing
statements on irregular graphs are stated; the regular-only Cheeger
axioms of `GraphTheory.Cheeger` cannot express it"* and lists as an
explicit unlocked consumer *"statement shapes for a future irregular
Cheeger family."* Per `scripts/measure_load_bearing.py`, that consumer
has never been picked up — the module has zero real theorem consumers
anywhere in the shelf, eight proved lemmas sitting exactly as built,
never invoked. This proposal is that named, never-started follow-on.

## Assessed from

`Scaffold/Mathlib/GraphTheory/Cheeger.lean`'s exact regularity
dependence, confirmed by direct read: `cheeger_upper_bound` and
`cheeger_lower_bound` both take `d : ℝ`, `hd : ∀ i, deg A i = d` as
hypotheses; `regularNormalizedLaplacian A d := 1 - d⁻¹ • A` is defined
only for the constant-degree case; and — the load-bearing detail —
`cutTestVector_dotProduct_onesVec`'s orthogonality proof uses
`vol_eq_of_regular` to balance `|S| · vol(Sᶜ) = |Sᶜ| · vol(S)`, a
cardinality identity that is **specifically a regularity consequence**,
not a general volume fact. The whole cut-sweep/coarea machinery
(`cutTestVector`, `coarea_core`, `hardDirection_perPart`, the median
argument) is built on this cardinality-volume equivalence, not on
`deg A i` as a general function. **This means the existing Cheeger proof
does not generalize by substitution — it needs a genuinely
volume-weighted test vector and a re-derivation of the orthogonality and
energy identities in the weighted measure**, which is exactly the
content `VariationalTransfer.lean` supplies through
`rayleigh_normalizedLaplacian_degreeSqrt`'s general (non-regular) Rayleigh
form.

Also assessed from `Scaffold/Mathlib/GraphTheory/Normalized.lean`
(`degreeSqrt`, `degreeInvSqrt`, `normalizedLaplacian`, `vol`,
`walkTransitionMatrix` — the general irregular-graph machinery already
present) and the classical statement shape (Chung, *Spectral Graph
Theory*, 1997, Ch. 2 — the standard normalized-Laplacian Cheeger
inequality for irregular graphs, stated via `vol` not `card`).

## The statement (draft shape — subject to Step 0 correction)

The classical target, generalizing `cheeger_upper_bound`/
`cheeger_lower_bound` to arbitrary positive-degree weighted graphs (no
`d`-regularity):

```
secondEval (normalizedLaplacian A) hsym hcard ≤ 2 * cheegerConstant A
(cheegerConstant A) ^ 2 / 2 ≤ secondEval (normalizedLaplacian A) hsym hcard
```

where `cheegerConstant`/`conductance` are restated in **volume-weighted**
form (`vol A S` in place of `card S`, already how `Normalized.lean`'s
`vol` is defined — Step 0 must confirm whether `GraphTheory.Cheeger`'s
existing `conductance`/`cheegerConstant` definitions are already
volume-general or are themselves cardinality-specific and need their own
irregular restatement before the inequality can even be posed).

**Step 0's required deliverable, before any proof is attempted:**

1. Read `conductance`/`cheegerConstant`/`boundary` in `Cheeger.lean` and
   determine whether they are already stated in terms of `vol`/`deg`
   (general) or `card` (regular-specific) — this determines whether a
   *new* irregular definition is needed alongside the new inequality, or
   whether only the inequality is new.
2. Design the irregular test vector (the standard choice: `x i = vol(Sᶜ)`
   on `S`, `-vol(S)` off it, or the degree-stretched variant
   `degreeSqrt A *ᵥ (indicator)` that `VariationalTransfer.lean`'s bridge
   is shaped to consume) and verify its orthogonality to `onesVec` holds
   by a genuine volume identity (`vol S + vol Sᶜ = vol V`), not by
   appeal to any regularity fact.
3. Re-derive the Dirichlet-energy identity
   (`quadForm_laplacian_cutTestVector`'s analogue) for the new test
   vector using `quadForm_laplacian_eq_quadForm_normalizedLaplacian` as
   the transfer engine, and assess whether the coarea/median hard
   direction (`coarea_core`, `hardDirection_perPart` — the bulk of
   `Cheeger.lean`'s 1500+ lines) needs a full re-derivation in the
   volume-weighted measure or can be transported by a general change of
   measure lemma.
4. Cost estimate and recommendation — "the upper bound (easy direction)
   is a one-step transfer; the lower bound (hard direction, the coarea
   argument) needs its own multi-step program mirroring
   `discharge-perturbation-axioms.md`'s Cheeger Step 1a/1b/1c split" is
   a plausible and acceptable Step 0 verdict; splitting this proposal
   into an "easy direction" delivery now and a deferred "hard direction"
   follow-on, exactly as the original Cheeger discharge did, is
   explicitly authorized if Step 0 finds the hard direction's cost is
   large.

## QA obligations (draft — refine after Step 0)

1. An irregular fixture (a star graph, or a path of length ≥ 3 — genuinely
   non-regular, unlike every existing Cheeger fixture) where the
   volume-weighted conductance and the normalized-Laplacian spectral gap
   are both computed by hand and cross-checked against the delivered
   bound(s).
2. The regular case recovered as a corollary/consistency check: on a
   `d`-regular fixture, the new irregular statement should agree with
   the existing `cheeger_upper_bound`/`cheeger_lower_bound` numerically
   (both routes computing the same bound on the same graph) — a
   route-independence check in the spirit of this session's QA
   discipline, and a safety net against a mis-transferred definition.
3. If the irregular test vector's orthogonality or energy identity has
   its own boundary case (e.g. an isolated vertex, `deg = 0`), refute
   the hypothesis-free form on a fixture that violates it, per the
   established fence discipline.

## Acceptance bar

- Step 0 delivers a written verdict — including whether `conductance`/
  `cheegerConstant` already generalize — before any shelf Lean is
  written; a recorded multi-phase split is an acceptable outcome, not a
  failure.
- If delivered: zero new axioms; the regular case's existing theorems
  are either recovered as corollaries or explicitly left standing
  unmodified (no regression to `cheeger_upper_bound`/`cheeger_lower_bound`'s
  existing statements or proofs).
- `VariationalTransfer.lean` gains its first real theorem consumer.
- `docs/7_SGT_RADAR.md` axis 4 (Cuts/Expansion) is the natural re-score
  target — this closes the "regular graphs only" caveat that has stood
  on every Cheeger-family result since delivery.

## Companion

[Prove Cheeger's Easy Direction (delivered)](prove-cheeger-easy-direction.md),
[Discharge Perturbation Axioms (Cheeger hard-direction delivery record and
its Step 1a/1b/1c precedent)](discharge-perturbation-axioms.md),
`docs/6_SGT_BACKLOG.md`, `docs/7_SGT_RADAR.md` axis 4.
