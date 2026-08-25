# Proposal: The Irregular Cheeger Inequality via Variational Transfer

**Status:** COMPLETE (the easy direction) — Steps 0+1 delivered 2026-08-25
(run `20260825T045222Z-run-1`; found committed since `6cb2f20` but never
indexed in the Active priority table — indexed and pursued per priority
item 0). The hard direction is priced and deferred exactly as this
document's own Step-0 authorization permits; see the delivery record.
This document authorized no Lean changes, axiom admissions, commits, or
external publication on its own beyond that mechanism.

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

## Step 0 record (the survey, delivered 2026-08-25)

**Deliverable 1 — are the definitions volume-general?** Yes, all of
them, read directly from source: `vol`, `boundary`, `conductance`
(`boundary / min (vol S) (vol Sᶜ)`), and `cheegerConstant` (the infimum
over nonempty proper cuts) live in `GraphTheory.Spectral` and are stated
entirely in `deg`/volume terms — **no irregular restatement was needed;
only the inequality is new.** Moreover `cutTestVector` (the
volume-centered cut indicator) and its energy identity
`quadForm_laplacian_cutTestVector` (`= boundary · (vol V)²`) are already
regularity-free.

**Deliverable 2 — the irregular test vector.** The survey's decisive
finding improves on the drafted candidates: neither the σ-centered
indicator nor a bespoke construction is needed. The degree-weighted sum
of the *existing* cut indicator vanishes **without any regularity** —
`∑ i, deg A i * cutTestVector A S i = vol S * vol Sᶜ − vol Sᶜ * vol S
= 0` — so the correct irregular test object is the *degree-stretched*
vector `√D *ᵥ cutTestVector A S`: it is orthogonal to the normalized
Laplacian's **actual** kernel vector `√D · onesVec`
(`normalizedLaplacian_mulVec_degreeSqrt_onesVec`, delivered), which is
*not* `onesVec` on irregular input (this is precisely why the delivered
onesVec-based `secondEval_le_rayleigh` cannot express the route, and the
one genuinely new engine lemma — the general-kernel
`secondEval_le_rayleigh_of_ker` — was needed; the P₃ QA pins a test
vector with `dotProduct z onesVec = 2 − √2 ≠ 0`, the discrimination
witness).

**Deliverable 3 — the energy transfer.** The numerator is
`VariationalTransfer`'s own congruence engine
(`quadForm_laplacian_eq_quadForm_normalizedLaplacian`) composed with the
regularity-free cut energy identity, giving `quadForm L_sym (√D x) =
boundary · (vol V)²` at `x = cutTestVector`; the denominator is
`∑ i, deg A i * x i² = vol S · vol Sᶜ · vol V`. The Rayleigh quotient is
therefore *the same* `boundary · vol V / (vol S · vol Sᶜ)` the regular
family computes, and the closing `min`-arithmetic and infimum pass are
the delivered regular proof's verbatim.

**Deliverable 4 — verdict and split.** The upper bound (easy direction)
is a bounded one-step delivery as executed. The lower bound (hard
direction, `φ²/2 ≤ λ₂` in the volume-weighted measure) needs a genuine
volume-weighted re-derivation of the coarea/median machinery
(`coarea_core`, `hardDirection_perPart`, the median assembly), which is
built on the cardinality-volume equivalence that regularity supplies —
its own multi-step program mirroring the original Cheeger discharge's
Step 1a/1b/1c split. **Deferred per this document's own authorization.**

## Delivery record (Step 1, delivered 2026-08-25)

**Delivered as pure hard crust, zero new axioms (count stays 10;
`#print axioms` via `wip/icv_axcheck.lean` on all 36 new declarations —
10 public module + 26 QA headline: exactly
`propext, Classical.choice, Quot.sound`, every one). QA
2067 → 2152 (`IrregularCheeger_QA` a new file at 85 by the generator
metric).**

**Modules changed (no new modules, no umbrella change):**
`GraphTheory/Spectral.lean` — `eigvecOf_ortho_of_mulVec_eq_zero` (the
general-`w` form of the onesVec orthogonality engine),
`secondEval_le_rayleigh_of_ker` (the general-kernel Rayleigh domination:
every nonzero `x ⊥ w` at a nonzero kernel vector `w` of a PSD symmetric
matrix bounds `secondEval` — the delivered `secondEval_le_rayleigh` is
the `w = onesVec` instance), `vol_pos_of_pos_deg` (the regularity-free
positivity replacement for `vol_pos_of_regular`);
`GraphTheory/Normalized.lean` — `normalizedLaplacian_mul_degreeSqrt`
(the left-multiplied congruence) and
`normalizedLaplacian_mulVec_degreeSqrt_onesVec` (the kernel vector);
`GraphTheory/VariationalTransfer.lean` — the module's own docstring-
named irregular-Cheeger consumer, its first theorem consumers anywhere:
`dotProduct_degreeSqrt_mulVec_cutTestVector` (the volume identity,
hypothesis-free at `0 ≤ deg`),
`dotProduct_degreeSqrt_mulVec_cutTestVector_self` (the weighted norm),
`degreeSqrt_mulVec_cutTestVector_ne_zero`,
`rayleigh_normalizedLaplacian_degreeSqrt_cutTestVector` (the same
quotient as the regular family), and the headline
`cheeger_upper_bound_normalized`: for symmetric nonnegative
positive-degree `A` with `2 ≤ card V`,
`secondEval (normalizedLaplacian A) ≤ 2 * cheegerConstant A` — no
regularity, no connectivity. On the regular cone the spectral side
equals the regular family's by
`normalizedLaplacian_eq_regularNormalizedLaplacian`; the delivered
`cheeger_upper_bound` is neither replaced nor regressed.

**QA (all four mandated sections):** (1) the irregular fixture `P₃`
(degrees `1, 2, 1`): the conductance side by hand (all six cuts'
conductance `1`, `cheegerConstant = 1`), the test-vector layer verified
entrywise (the stretched vector `![3, -√2, -1]`, kernel orthogonality
by theorem and by raw arithmetic, norm `12` by raw arithmetic and as
`1 · 3 · 4`, energy `16` by three independent routes — raw
combinatorial arithmetic, the congruence engine, and the delivered cut
energy identity), the Rayleigh quotient `4/3`, and the spectral side
bounded **independently of the theorem** through the eigenpair witness
`![1, 0, -1]` at eigenvalue `1` (`λ₂ ≤ 1`, strictly stronger than the
theorem's `≤ 2` — non-circular cross-check) plus the same engine at the
theorem's own test vector (`λ₂ ≤ 4/3`); (2) the discrimination witness
`2 − √2 ≠ 0` — the stretched test vector is *not* orthogonal to
`onesVec`, so the old engine provably cannot consume it; (3) the
regular-recovery tight check on `K₂` through the cone agreement and the
delivered pin (`2 ≤ 2 · 1`); (4) two proved-form fences: the PSD drop on
the general-kernel engine (`diag(-1, 0)`, `w = e₁`, `x = e₀`: conclusion
`0 ≤ -1` false, exactly `hpsd` isolated, sorted spectrum and Rayleigh
quotient both pinned) and the degree drop on the headline (all-zero
adjacency: every conductance junk-zero, `λ₂ (normalizedLaplacian 0) =
λ₂ (1) = 1` by trace/determinant, conclusion `1 ≤ 0` false, exactly
`hd` isolated).

**Verification:** spike first (`wip/icv_spike.lean`, the full route
green before any module touched); `lake env lean` zero
errors/warnings on all three public modules and the QA file (the QA's
pre-existing-warning set: none — the file is warning-clean); explicit
`lake build` targets ✔ (Spectral/Normalized/VariationalTransfer;
IrregularCheeger_QA 2193/2193); `#print axioms` on all 36 (above);
**full `lake build` ✔ (2264 targets, "Build completed successfully")**
followed immediately by **`check_build_completeness.py`: 104/104 fresh,
0 stale, 0 missing, exit 0**; `lint_axioms` (10), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (2152/10/0).

**Pin-technique list (from the verification pass):** the recurring trap
is `simp only` with a def-unfold (`icPathAdj`) in the same list as a
lemma stated over that def (`icPathAdj_deg`, `hentry`) — the def wins
the rewrite race and the lemma's pattern stops matching; the durable
fixes are staged `simp only`s (engine lemma first, def-unfolds in a
second pass), standalone value-pin lemmas (`ic_deg_*`, `ic_vol_*`,
`ic_boundary_*` via explicit `Finset.sum_insert`/`sum_singleton`
chains), and a `hdeglit` copy of the deg lemma stated at the unfolded
matrix literal. `obtain`/`rcases` on a needed hypothesis clears it —
copy into a fresh `have` first. `Matrix.mulVec_mulVec` at this pin is
stated `M *ᵥ N *ᵥ v = (M * N) *ᵥ v` (nested on the left). `rw
[secondEval]` fails (no equation lemmas) — use the `rfl`-equation `have`
route. Numeric closers flip between `rw`-closes and needing `norm_num`
depending on upstream lemma success — `try norm_num` after long `rw`
chains. `Pi.single 1 (1 : ℝ)` without an index-type ascription defaults
to `ℕ`.

**Open follow-ons (priced, not started):** the irregular *hard*
direction (this document's own deferred half — the volume-weighted
coarea/median program); a connectivity-free `λ₂ > 0` transfer for
`normalizedLaplacian` (the kernel-vector lemma delivered here is its
natural entry); the `MetricSpace`-style packaging of nothing here.
