# Proposal: The Irregular Cheeger Inequality via Variational Transfer

**Status:** COMPLETE (both directions) — Steps 0+1 (the easy direction)
delivered 2026-08-25 (run `20260825T045222Z-run-1`; found committed
since `6cb2f20` but never indexed in the Active priority table —
indexed and pursued per priority item 0); the deferred hard direction
(the volume-weighted coarea/median program) delivered 2026-08-25/26
(opened by run `20260825T221207Z-run-1`, verified and recorded by
continuation run `20260826T010711Z-run-1`); see the delivery records.
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

## Delivery record (the hard direction, delivered 2026-08-25/26)

Opened by run `20260825T221207Z-run-1` (intent + Step-0 survey + the
full Lean drafted), verified, checked, and recorded by continuation run
`20260826T010711Z-run-1` after the opening session was interrupted
before any verification. **Delivered as pure hard crust, zero new
axioms (count stays 10; `#print axioms` via `wip/ich_axcheck.lean` on
all 40 audited declarations — 16 public + 24 QA: exactly
`propext, Classical.choice, Quot.sound`, every one). QA
2249 → 2280 (+31 in `IrregularCheeger_QA.lean`, the file 85 → 116 by
the generator metric).**

**The headline:** `cheeger_lower_bound_normalized` —
`cheegerConstant A ^ 2 / 2 ≤ secondEval (normalizedLaplacian A)` on
arbitrary symmetric nonnegative positive-degree graphs with
`2 ≤ card V`: no regularity, no connectivity, on exactly the easy
direction's hypotheses. With the delivered upper bound, **the full
Cheeger pair now holds in the volume-weighted measure on every
positive-degree weighted graph** — the last "regular graphs only"
caveat on the Cheeger family is removed (radar axis 4's held-back
absent clause retired).

**Modules changed (no new modules; one new import —
`VariationalTransfer.lean` imports `Cheeger`, acyclic in the import
graph):**

- `GraphTheory/Spectral.lean` — `secondEval_variational_of_ker`: the
  sInf Courant–Fischer form at an **arbitrary kernel vector** `w`
  (`λ₂ = sInf {R(x) : x ≠ 0, x ⊥ w}` for a symmetric PSD matrix with
  nonzero kernel vector `w`). The delivered
  `secondEval_le_rayleigh_of_ker` is exactly its hard half and is
  reused verbatim; the new content is the witness half — at
  `0 < λ₂` the eigenvector at the second sorted entry is orthogonal to
  `w` through `eigvecOf_ortho_of_mulVec_eq_zero`; at `λ₂ = 0` a kernel
  vector orthogonal to `w` is produced from the double bottom of the
  sorted spectrum (`exists_ne_eigvalOf_of_evals_head_eq`) by the same
  cross combination the onesVec proof uses. Every future irregular
  consumer (whose operator is killed by `√D·1`, not `1`) shares this
  engine.
- `GraphTheory/Cheeger.lean`, the new `VolumeHardDirection` section —
  the regular family's chain re-derived in the volume-weighted
  measure, each member load-bearing on the exact shape the regular
  proof bought with `sum_deg_mul_eq_of_regular`:
  `vol_le_vol_of_subset`/`vol_empty` (volume arithmetic);
  **`exists_median_vol`** (the volume median — a level `t` with
  `vol {y² > t} ≤ vol V/2` and `vol {y² ≥ t} ≤ vol V/2 ≤ vol {y² ≥ t}`
  — the same maximizing-vertex/minimal-member Finset argument at `vol`
  replacing `card`, pure Finset arithmetic, no sorting);
  `boundary_ge_of_minority_vol` (minority conductance at volume
  strength — `min (vol S) (vol Sᶜ) = vol S` is pure `vol_compl`
  arithmetic where the regular proof needed `vol_eq_of_regular`);
  `sum_deg_mul_indicatorLE_eq_vol` and `sum_pairAbs_ge_vol` (the
  degree-weighted mass side); **`coarea_core_vol`** (the degree-weighted
  layer-cake: `φ·∑ deg·y² ≤ ∑_{i,j} A i j |y i² − y j²|`, proved by the
  `indicatorLE` integrability layer with the threshold integral, the
  boundary inequality by `sum_pairAbs_ge_vol`, and the `t = 0` failure
  point absorbed measure-theoretically); `hardDirection_perPart_vol`
  (the per-part bound `φ²·∑ deg·y² ≤ E'(y)` — the fused contraction
  `sum_edgeWeight_sq_posPart_add_sq_negPart_le` and the core
  `core_sum_abs_sq_sub_sq` are *already degree-weighted* in the regular
  file and are consumed verbatim, no regularity bridge anywhere);
  `minority_posPart_vol`/`minority_negPart_vol` (the minority-side
  parts); `median_parts_norm_vol` (the weighted norm split).
- `GraphTheory/VariationalTransfer.lean` —
  `dotProduct_degreeSqrt_mulVec_mixed` (the general weighted inner
  product `∑ deg i * x i * y i` as a stretched dot product) and
  `dotProduct_degreeSqrt_mulVec_onesVec` (its consequence: the
  constraint the irregular variational set imposes — a stretched vector
  `√D x` is orthogonal to the kernel vector `√D·1` exactly when `x`
  has degree-weighted zero sum); **`cheeger_sweep_normalized`** (the
  sweep lemma at test-vector level: every nonzero degree-weighted
  zero-sum `f` has `φ²/2 ≤ R_{L_sym}(√D f)`, the volume median routing
  both parts to their volume-minority sides, the per-part bounds summed
  through the fused contraction, the norm split carrying the full
  weighted norm, and `rayleigh_normalizedLaplacian_degreeSqrt`
  normalizing); **`cheeger_lower_bound_normalized`** (the headline —
  `secondEval_variational_of_ker` at the true kernel vector `√D·1`
  reduces the spectral claim to the sweep lemma at every admissible
  vector; the un-stretched `f := (1/√D) x` of an orthogonal `x` has
  degree-weighted zero sum by the onesVec constraint lemma, and the
  sInf set's nonemptiness is witnessed by the easy direction's own cut
  test vector, whose orthogonality is exactly the easy delivery's
  volume identity — one test object, both directions of the pair).

**QA (+31, the new hard-direction sections of
`IrregularCheeger_QA.lean`):** the mandated obligations at volume
strength — (1) the irregular `P₃` fixture: the volume median pinned
and *forced* into its computed interval (`ichv_median_pin_QA`,
`ichv_median_forced_QA`), the cut-test-vector weighted sum and the
norm split pinned entrywise and as theorem instances
(`ichv_norm_split_instance_QA`), the coarea equality pinned raw on
`K₂` (`ichv_coarea_edge_eq_QA`, both sides `2` at `y = ![1, 0]`) and
as a theorem instance (`ichv_coarea_edge_instance_QA`), the per-part
bound pinned (`ichv_perPart_edge_QA`); (2) the sweep instances: on
`K₂` at `f = ![1, -1]` (`1/2 ≤ 2` against the independently pinned
`λ₂ (L_sym) = 2`) and on `P₃` at *the same cut test vector the easy
direction consumed* (`1/2 ≤ 4/3` — one test object, both bounds of the
pair); (3) **the headline joined to the easy direction's independently
pinned spectral bracket** (`ichv_p3_hard_bound_QA`: the theorem's
`φ²/2 = 1/2 ≤ λ₂` conjoined with the easy delivery's
eigenpair-witness `λ₂ ≤ 1` — non-circular, the spectral side bounded
by a witness, not by the theorem family) and the **`K₂` regular
recovery** (`ichv_k2_regular_recovery_QA`: `1/2 ≤ 2` with `λ₂ = 2`
pinned raw — the irregular theorem's conclusion agreeing with the
regular family's on the regular cone); (4) **proved-form fences**: the
minority-hypothesis refutations (`ichv_coarea_minority_fence_QA`,
`ichv_boundary_minority_fence_QA` — the hypothesis-free forms refuted
on the full vertex set of `K₂`, exactly the minority hypothesis
isolated) and **the nonnegativity fence** (`ichv_signed_fence_QA`: the
symmetric positive-degree signed adjacency `!![2, −1; −1, 2]]` with
`cheegerConstant` pinned at `-1` and `λ₂ (L_sym)` pinned raw refutes
the nonnegativity-dropped conclusion — exactly `hnn` isolated).

**Verification:** `lake env lean` — zero errors/zero warnings on all
three public modules and the QA file; `#print axioms` via
`wip/ich_axcheck.lean` on all 40 — the standard three only (above);
**full `lake build` ✔ (2385 targets, "Build completed successfully")
immediately followed by `check_build_completeness.py` — 107/107 fresh,
0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(**2280/10/0**, idempotent by md5).

**Open follow-ons (priced):** the connectivity-free `λ₂ > 0` transfer
for `normalizedLaplacian` was **delivered 2026-08-26** (see the
follow-on delivery record below); the volume-weighted *sweep-cut
extraction* was **delivered 2026-08-26** (the regular family's
`cheeger_sweep_cut`/`sweep_level_extract` ported to the volume
measure — see the sweep-extraction delivery record below); the
*irregular Fiedler instantiation* was **delivered 2026-08-26** (the
family's algorithm-facing capstone — see the Fiedler-instantiation
delivery record below); multiway expansion (radar axis 4's remaining
absent category) remains open, priced as a multi-run program (its easy
direction needs a partition-space definition with attainment plus
genuinely new engine content: the centered-indicator test functions sum
to zero, and linear combinations re-introduce cross-part energy — the
honest routes are quotient-matrix/interlacing or an iterated 2-way
assembly, each a Step-0 survey plus multi-slice program).

## Follow-on delivery record: the connectivity transfer (2026-08-26)

**Delivered** (run `20260826T024528Z-run-1`, pure hard crust, zero new
axioms — `#print axioms` via `wip/ctc_axcheck.lean` on all 31 audited
declarations — 7 public + 24 QA — reads exactly `propext,
Classical.choice, Quot.sound`, every one). In
`GraphTheory.VariationalTransfer.lean`'s new "The connectivity
transfer" section:

- `degreeSqrt_mul_normalizedLaplacian` (`√D · L_sym = L · D^{-1/2}`,
  the left-multiplied congruence) and
  `normalizedLaplacian_mulVec_degreeSqrt_of_laplacian_mulVec_eq_zero`
  (the kernel-cone lift) — the algebra layer;
- `normalizedLaplacian_mulVec_eq_zero_iff` — **the kernel
  characterization**: on connected input `L_sym *ᵥ x = 0 ↔ ∃ c, x =
  c • (√D · onesVec)`. The proposal's named "natural entry", now in
  iff form: forward by congruence + the electrical program's
  `laplacian_mulVec_eq_zero_iff_exists_const`, reverse by the delivered
  kernel-vector lemma;
- `secondEval_normalizedLaplacian_pos_of_connected` — the Fiedler
  mirror of `lambda2_pos_of_connected` (PSD pin + sorted + the double
  bottom's multiplicity pin + orthonormality contradiction on the
  stretched-constant line);
- `secondEval_normalizedLaplacian_eq_zero_of_not_connected` — `λ₂ = 0`
  exactly on disconnected input (component indicator → combinatorial
  kernel → cone lift → Gram–Schmidt against `√D·1` → the delivered
  `secondEval_le_rayleigh_of_ker` + PSD);
- `secondEval_normalizedLaplacian_pos_iff_connected` — the packaged
  equivalence `0 < λ₂(L_sym) ↔ connected`;
- `cheegerConstant_pos_of_connected` — the consumer corollary joining
  the delivered easy direction (`0 < λ₂ ≤ 2φ`): the Cheeger constant
  is positive on every connected irregular graph.

**QA (+50 in `IrregularCheeger_QA.lean`, the file 116 → 166):** the P₃
positive instance joined to the file's independent eigenpair bracket
(`0 < λ₂ ≤ 1`, the `≤` side eigenpair-witnessed without the
connectivity family — non-circular); the K₂ instance joined to the
pinned exact `λ₂ = 2`; the kernel iff exercised both directions on
genuinely irregular input (the span membership forced to `c = 1`;
`onesVec ∉ ker`, through the iff); the **disconnected two-edge
negative witness** with `λ₂ = 0` pinned by **two independent routes**
(the theorem; and the raw kernel witness + Gram–Schmidt + engine with
no connectivity statement anywhere); the **`hconn` fence** in proved
form (every other hypothesis verified, conclusion refuted); and the
**`hnn` fence on a connected signed fixture** (`0,2,2;2,0,-1;2,-1,0`:
support edges `0—1`, `0—2` positive, `A 1 2 = -1`) — both at the
kernel characterization (raw kernel vector not on the stretched line)
and at the headline, the latter through the engine with a
fixture-specific squares PSD supplier (`xᵀLx = (x₀ − x₁ − x₂)²`): the
shelf's `normalizedLaplacian_psd` needs `hnn`, the engine does not —
the fence isolates exactly where nonnegativity enters. Plus the
consumer-corollary joins (`0 < φ` against the pinned `φ = 1` on both
fixtures).

**Verification:** spike first (`wip/ctc_spike.lean` + the QA spike,
the full routes green before any module touched; the recorded
technique findings: `SimpleGraph.Reachable`'s protected `refl`/`trans`
constructors, `mul_inv_cancel₀`'s shape at this pin (a * a⁻¹), the
secondEval-vs-evals `show`-unfold in `hge`, the stale-olean
rebuild-before-QA trap hit once and remediated, and the
matrix-literal-at-depth-2 entry computation replaced by if-ladder
fixture definitions); `lake env lean` zero errors/zero warnings on both
changed modules; explicit `lake build` targets ✔ (module 2190/2190, QA
2193/2193); `#print axioms` on all 31 — the standard three only; **full
`lake build` ✔ (2384/2385 targets, "Build completed successfully")
immediately followed by `check_build_completeness.py` — 107/107 fresh,
0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(**2330/10/0**, idempotent by md5).

## Follow-on delivery record: the irregular Fiedler instantiation (2026-08-26)

**Delivered** (run `20260826T064300Z-run-1`, pure hard crust, zero new
axioms — `#print axioms` via `wip/ifc_axcheck.lean` on all 23 audited
declarations — 14 public + 9 QA — reads exactly `propext,
Classical.choice, Quot.sound`, every one). QA 2340 → 2349 (+9 in
`IrregularCheeger_QA.lean`): the family's algorithm-facing capstone —
`cheeger_sweep_cut_normalized` consumed at its first input that is not
a hand-built test vector but the object the spectral-partitioning
algorithm actually computes.

- The interface layer (a new "The irregular Fiedler instantiation"
  section of `VariationalTransfer.lean`; no new imports, no umbrella
  change): `fiedlerIndexNormalized`/`fiedlerVectorNormalized` — the
  `Fiedler.lean` pattern at `L_sym`, with the eigen equation, unit
  norm, nonvanishing, `quadForm` and `rayleigh` both equal to `λ₂` —
  and the sweep vector `fiedlerSweepVector := degreeInvSqrt A *ᵥ u`
  (the `D^{-1/2}` pullback, the generalized eigenfunction of `(L, D)`
  at `λ₂`), with the stretch cancellation
  `fiedlerSweepVector_degreeSqrt_mulVec` (`√D f = u` by
  `degreeSqrt_mul_degreeInvSqrt`), nonvanishing, and the constraint
  conversion `fiedlerSweepVector_sum_deg_eq_zero` (the sweep family's
  own hypothesis `∑ deg · f = 0` obtained from the eigen-hinge
  `eigvecOf_ortho_of_mulVec_eq_zero` at the true kernel vector `√D·1`
  through `dotProduct_degreeSqrt_mulVec_onesVec` — `0 < λ₂` from the
  delivered connectivity transfer is connectivity's exact entry point).
- The headline `fiedler_sweep_cut_normalized`: on every connected
  symmetric nonnegative positive-degree graph with `2 ≤ card V`, an
  explicit nonempty proper closed superlevel or sublevel cut **of the
  sweep vector itself** with
  `conductance A S ^ 2 ≤ 2 * secondEval (normalizedLaplacian A)` — the
  classical `√(2λ₂)` scale, exactly the regular family's
  `fiedler_sweep_cut` constant `2 lambda2 / d` on the regular cone
  (since `λ₂ (L_sym) = lambda2 / d` there). Load-bearing joins: the
  constraint shape (an unweighted zero-sum shape would fail the sweep
  hypothesis), the stretch cancellation and
  `fiedlerVectorNormalized_rayleigh` (the spectral side closes at the
  eigenvector, not at any test vector), and the connectivity-supplied
  gap.

**QA (+9):** the exact pin `icPathAdj_secondEval_eq_one` — `λ₂ (L_sym
P₃) = 1`, the new `≥ 1` side (`icPathAdj_secondEval_ge_one`) proved by
the sum-of-squares `2 x₁²` through `secondEval_variational_of_ker`
(every admissible Rayleigh at least `1`; the sInf set's nonemptiness
witnessed by the concrete eigenpair `![1, 0, -1]` at Rayleigh exactly
`1`), joined to the pre-existing `≤ 1` eigenpair side that predates
the whole Fiedler family — non-circular, and the family's Cheeger
bracket on `P₃` collapses to a point (`1/2 ≤ λ₂ = 1 ≤ 2`); the theorem
instances `ifc_p3_instance_QA` (against the exact pin and the
exhaustive all-cuts-are-`1` pin) and `ifc_edge_instance_QA` (against
the pinned classical `λ₂ = 2`, singleton conductance `1 ≤ 4` — the
regular family's own constant on the cone); the pullback algebra raw
at the concrete eigenpair (`ifc_pullback_cancel_raw_QA`,
`ifc_pullback_zero_sum_raw_QA` — the cancellation and the zero-sum by
direct arithmetic, the latter through the public pairing identity
joined to the file's independent orthogonality pin); and the
connectivity mechanism fenced (`ifc_disc_hinge_fence_QA` + the
block-indicator kernel witness and the degree pins): on the
disconnected fixture `λ₂ = 0` (the file's two-route pin) and a nonzero
kernel eigenvector of `L_sym` pairs to `2 ≠ 0` with `√D·1` —
kernel-ness provably does not supply the hinge, so the constraint
conversion genuinely needs the connectivity-supplied gap (the
conclusion-level statement is not falsifiable on that fixture since a
kernel vector's sweep may still find a conductance-`0` component cut —
the fence therefore lives at the mechanism, exactly where the
hypothesis enters).

**Verification:** spike first (`wip/ifc_spike.lean` + the QA spike
`wip/ifc_qa_spike.lean`, the full routes green before any module
touched; the technique findings: the scoped `Matrix` notation
(`*ᵥ`) needing `open scoped Matrix` in standalone files; `le_csInf`
taking the set's *nonemptiness* in this pin (witnessed by the concrete
eigenpair — itself a meaningful pin) rather than boundedness; the
matrix-literal/degree evaluation recipe `simp [icPathAdj, hdeglit,
Real.sqrt_one]` with the literal-matrix degree lemma;
`Real.sqrt_ne_zero'.mpr`; `linear_combination` for the `√2`-comm
rearrangements; unary-minus shaping in scalar lemmas so `rw` patterns
match; `Finset.sum_pos'` for dot-product positivity; the stale-olean
rebuild-before-axcheck trap hit once and remediated by the explicit
QA target); `lake env lean` zero errors/zero warnings on both changed
modules; explicit `lake build` targets ✔ (module 2190/2190, QA
2193/2193); `#print axioms` on all 23 — the standard three only,
re-run after the final source state; **full `lake build` ✔ (2384/2385,
"Build completed successfully") immediately followed by
`check_build_completeness.py` — 107/107 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**2349/10/0**,
idempotent by md5).

## Follow-on delivery record: the volume-weighted sweep-cut extraction (2026-08-26)

**Delivered** (run `20260826T045752Z-run-1`, pure hard crust, zero
new axioms — `#print axioms` via `wip/vsc_axcheck.lean` on all 13
audited declarations — 2 public + 11 QA — reads exactly `propext,
Classical.choice, Quot.sound`, every one). QA 2330 → 2340 (+10 in
`IrregularCheeger_QA.lean`, the file 166 → 176): the regular family's
sweep-cut extraction (`proposals/sweep-cut-extraction.md`, 2026-08-24)
ported to the volume-weighted world — the irregular Cheeger pair now
returns *the cut the spectral-partitioning sweep returns*, not just a
bound on the conductance infimum, on every symmetric nonnegative
positive-degree graph.

- `sweep_level_extract_vol` (in `Cheeger.lean`'s new
  `VolumeSweepExtraction` section): for any `y` whose nonempty closed
  superlevel sets at positive levels are volume-minority-side, a
  positive level `t` with `S = {i : t ≤ y i ^ 2}` nonempty, proper,
  and `conductance A S ^ 2 ≤ E'(y) / ∑ i, deg A i * y i ^ 2` — the
  attainment route at the `boundary / vol` ratio (the card denominator
  of the regular extraction replaced by the level set's volume,
  positivity from `vol_pos_of_pos_deg` at the attained witness); the
  degree-weighted layer-cake integration a structural clone of
  `coarea_core_vol`'s proof (`sum_deg_mul_indicatorLE_eq_vol` the mass
  side, `sum_pairAbs_eq_two_boundary` the pair side); closed by the
  already-degree-weighted Component A `core_sum_abs_sq_sub_sq` and the
  minority-volume conversion `min (vol S) (vol Sᶜ) = vol S` (pure
  `vol_compl` arithmetic — no `vol_eq_of_regular` anywhere). No
  `2 ≤ card V` hypothesis: minority at a nonempty level forces the
  complement nonempty.
- `cheeger_sweep_cut_normalized` (in `VariationalTransfer.lean`'s new
  "irregular sweep-cut extraction" section, placed with the family):
  every nonzero degree-weighted zero-sum `f` has a nonempty proper
  closed superlevel or sublevel cut `S` of `f` itself with
  `conductance A S ^ 2 ≤ 2 * R_{L_sym}(√D f)` — the volume median
  (`exists_median_vol`, `minority_{pos,neg}Part_vol` feeding the
  extraction's hypothesis verbatim), the product test with degenerate
  single-part cases, the fused contraction
  (`sum_edgeWeight_sq_posPart_add_sq_negPart_le`, consumed verbatim —
  already degree-weighted), the weighted norm split
  (`median_parts_norm_vol`), and the closing normalization
  `2 * R_{L_sym}(√D f) = E'(f) / ∑ deg f²`
  (`rayleigh_normalizedLaplacian_degreeSqrt` +
  `laplacian_quadForm`). Exactly the hard direction's own constraint
  shape — no regularity, no connectivity, no cardinality hypothesis.

**QA (+10):** the extraction witness *forced* on the genuinely
irregular `P₃` fixture at `y = ![1, 0, 0]` (the level-membership iff
pins the returned set to `{0}`, conductance `1` from the file's
exhaustive-cut pin, the bound `1 ≤ 2/1` with both sides computed
raw); the sweep-cut on the pair's shared `P₃` cut test vector (the
family characterization proved in-instance — `{0}` superlevel,
`{1, 2}` sublevel the only nonempty proper members — conductance `1`
against the file's pinned `R = 4/3`, so `1 ≤ 8/3`, one test object
now consumed by both Cheeger directions *and* the sweep); the `K₂`
regular recovery (`1 ≤ 4` at the pinned `R = 2`, both family members
characterized); and the degree-weighted zero-sum fence in proved form
(`f = ![1, 2]` on `K₂`: `∑ deg · f = 3 ≠ 0`, the sweep family has
exactly two nonempty proper members each of conductance `1`, the
demanded bound `1 ≤ 2 * (1/5)` computed raw — refuted for *every*
candidate, exactly `horth` isolated).

**Verification:** spike first (`wip/vsc_spike.lean`, both routes green
before any module touched — the per-part extraction on its first
elaboration after one tactic trim; the recorded technique findings:
the `Fin.exists_eq_zero_or_eq_one_or_eq_two` name gap closed by a
local `fin_cases` clone, entry-fact lemmas (`f 0 = 3` by
`rw [cutVec]; simp`) replacing depth-2 matrix-literal simp-only
reductions inside inline `linarith` blocks — the cons-lemma guessing
that failed — `▸`-direction equality transports at Fin cases, and
`laplacian_quadForm` needing its proof argument explicit in `rw`);
`lake env lean` zero errors/zero warnings on both changed public
modules and the QA file; explicit `lake build` targets ✔ (module
2190/2190, QA 2193/2193); `#print axioms` on all 13 — the standard
three only; **full `lake build` ✔ (2384/2385 targets, "Build
completed successfully") immediately followed by
`check_build_completeness.py` — 107/107 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**2340/10/0**,
idempotent by md5).
