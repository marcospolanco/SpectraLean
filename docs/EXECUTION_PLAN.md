# Execution plan

This is the compact, current-state ledger for sustained autonomous work. It is
updated at milestone boundaries; [`AGENT_ACTIVITY.md`](AGENT_ACTIVITY.md)
holds the append-only narrative.

## Active milestone

**Spectral Band Projectors, Step 2 — orthogonality of disjoint bands (run 1,
2026-08-20; `proposals/spectral-band-projectors.md`, the Active table's
only remaining High row, at its recorded open next step): DELIVERED.**
Pure hard crust — **zero new axioms** (count stays 11; `#print axioms`
on all four new public theorems reads only `propext, Classical.choice,
Quot.sound`). The proposal's one-step-per-run rule was honored —
Steps 3–4 untouched.

**Route (as recorded before stating):** exactly the paved path — the
Step-1 nestedness cross-law's ordered forms expand
`(P_b − P_a)(P_d − P_c)` to the four-term expression that collapses
under the ordering; the residue is literally `X − X`, closed by
`sub_self`. Hypotheses folded to `a ≤ b`, `c ≤ d`, `b ≤ c` — with
`b ≤ c` *exactly* interval disjointness of `(a, b]` and `(c, d]`,
load-bearing rather than decorative (the QA overlap guard refutes the
hypothesis-free form).

**Delivered in `GraphTheory.Band`** (public module elaborated clean on
the first pass, zero errors, zero warnings):

- `bandProjector_mul_bandProjector_eq_zero` — the forward composition
  law (each of the four products through
  `spectralProjector_mul_spectralProjector_of_le`);
- `bandProjector_mul_bandProjector_eq_zero'` — the flipped order, as a
  *direct* four-term expansion through `_of_le'` (not a transpose
  wrapper);
- `bandProjector_inner_eq_zero` — the consumer's vector-level form:
  `(B_{a,b} *ᵥ x) ⬝ᵥ (B_{c,d} *ᵥ y) = 0`, the first band moved across
  the dot product (`vecMul_transpose`, `dotProduct_mulVec`,
  `vecMul_vecMul`; its symmetry makes the transpose itself);
- `eq_zero_of_bandProjector_mulVec_eq_self` — the subspace-level
  reading of the step's "they share no eigenvector": a vector fixed by
  two disjoint bands is zero (the second band annihilates the first
  band's image).

**QA** `SpectralGraph/Band_QA.lean` (+16 by the generator metric, 43 in
file, 932 total): the disjoint low/high bands' composition to zero
checked **through the theorem and by raw literal multiplication** on the
pinned band values, in both orders; image orthogonality on concrete
vectors by both routes, with the **same-band counter-witness** (`1 ≠ 0`
— the vanishing is about disjointness, not the fixture's zero entries);
the composed action `B_high *ᵥ (B_low *ᵥ x)` annihilating a filtered
signal by both routes; a low-band range vector killed by the high band;
and the **overlap guard** — the bands `(−1, 3]` and `(1, 4]`, both
containing the eigenvalue `3`, compose to the provably nonzero
`diag(0,1)` (entry `1` at the shared mode's axis).

**Verification:** `lake env lean` on `Band` and `Band_QA` — zero
errors, zero warnings (public module first pass; three small QA proof
shape fixes during iteration, including the discovered `rw`-closes-
`3 ≤ 3`-by-itself behavior behind one linter warning);
`#print axioms` on the four public and twelve headline QA theorems ✔
(three standard axioms only); oleans produced directly during
iteration; **all thirty-four QA modules batch-elaborated, zero errors**
(BATCH-DONE fail=0); **full `lake build` ✔ (2186 targets, "Build
completed successfully", detached log + poll; the only diagnostic the
documented pre-existing `hγ` warning in `ProjectorDrift.lean`)**;
`lint_axioms` (**11**), `check_citations`, `check_markdown_links` pass;
scoreboard regeneration idempotent (**932/11/0**). Environment: the
pruned-oleans state recurred at run start; the interpreted cache fetch
restored 5387 (with the invocation note recorded in the scoreboard:
the `--run` file argument resolves relative to the cwd, not `--dir`).

**Records updated:** module/QA/umbrella docstrings, scoreboard
(932/11/0, both Direct rows prepended with the Step-2 slice, the
`lake build` row extended, the Step-2 interpretation bullet, the
cache-provenance invocation note, two stale narrative counts fixed —
the lint row's axiom count 12 → 11 and the QA-definition line
917 → 932), radar (axis 2 evidence extended with the orthogonality
layer, **score held at 4.0** per protocol — completion within the band
family counted at Step 1, Steps 3–4 the natural re-score triggers; QA
count synced 932/34 with the QA axis **held at 4.0**; both holds
logged), README (status table synced to the scoreboard authority
11/932; the proved list gains the disjoint-band orthogonality), SGT
index map (Band section extended, Steps 1–2; +3 rows), proposal
(status header Step 2 DELIVERED, delivery record with the route and
the overlap guard, open-next-step rewritten to Step 3),
`proposals/README.md` (High row note + Delivered row + progress
paragraph).

**Next milestone (open):** the same proposal's **Step 3 — completeness
under a partition** (a finite ordered threshold sequence covering the
spectral range sums to the identity; the two-band covering instance
`bandProjector_eq_one` already exists, and Step 2's orthogonality is
the pairwise half), then Step 4 (the Hilbert projection
specialization — survey `Analysis/InnerProductSpace/Projection.lean`
signatures first). Or the Medium rows (Fiedler Phase B — needs an
operator decision; mixing-time Step 1; Reversibility A and B; Relative
Entropy; Perron–Frobenius + directed operators; discharge-perturbation
— the Davis–Kahan Step 0 survey; approximate spectral projection).

---

**`spectral_persistence` removal (2026-08-20, operator-directed, interactive
session — not an `opencode-pursue` run): DELIVERED.** Editorial axiom
removal, not a proof-based retirement: the operator's stated criterion was
that the axiom is not well-established published math, distinct from
every prior retirement (all of which discharged a citation-backed axiom
by proof). Deleted `axiom spectral_persistence` from
`Scaffold/Mathlib/GraphTheory/Dynamics.lean` and its sole QA consumer
`persistence_zero_perturbation_QA` from `Scaffold/QA/SpectralGraph/Dynamics_QA.lean`;
fixed a dangling docstring reference in `Scaffold/Derived/ProjectorDrift.lean`.
`TimeVaryingGraph`/`laplacianSequence`/`IsEventDriven`/
`laplacianSequence_symmetric` are untouched (still consumed by
`Derived.EventStream`/`Derived.ProjectorDrift`, which already cover the
motivating persistence use without this axiom via the proved two-endpoint
chain). Explicit axiom count 12 → 11; QA declarations 917 → 916. Synced:
`index/map/spectral_graph.md`, `index/map/perturbation.md`,
`index/sources/davis_kahan_1970.md`, `docs/2_ARCHITECTURE.md`,
`docs/7_SGT_RADAR.md`, `README.md`, `docs/5_QA_SCOREBOARD.md` (regenerated
+ a new dated narrative bullet), `docs/6_SGT_BACKLOG.md` (appended, not
rewritten). `research/archive/` left untouched per `AGENTS.md`'s
archive-immutability rule — the earlier request in this session to also
scrub archive mentions was declined for that reason; this narrower
Lean-only removal was carried out instead.

**Verification:** `lake env lean` on the three touched modules — zero
errors (one pre-existing, unrelated unused-variable warning in
`ProjectorDrift.lean`, confirmed present before this change);
`scripts/generate_qa_scoreboard.py` regeneration reflects the new counts;
a full `lake build` was not run for this change (not requested, and the
three touched modules elaborate cleanly in isolation with no signature
changes to anything else imports).

---

**Spectral Band Projectors, Step 1 — the two-sided band projector (run 1,
2026-08-20; `proposals/spectral-band-projectors.md`, the Active table's
only remaining High row, at its recorded open next step "begin with
Step 1"): DELIVERED.** Pure hard crust — **zero new axioms** (count stays
12; `#print axioms` on all seven new public theorems reads only
`propext, Classical.choice, Quot.sound`).

**Pre-edit survey of `spectralProjector`'s lemma set (the proposal's
mandatory Step-1 check):** `spectralProjector_symmetric`,
`spectralProjector_idempotent`, `spectralProjector_eq_zero`,
`spectralProjector_eq_one` all exist and are proved — nothing to
reprove. **Route decision recorded before stating:** idempotence of the
*difference* `P_b − P_a` does not transfer from idempotence of each
factor (differences of idempotents are not idempotent in general); the
load-bearing missing piece is the **nestedness cross-law**
`P_{c₁} * P_{c₂} = P_{min c₁ c₂}`, proved entrywise by the same
orthonormal expansion as the existing idempotence proof with the two
threshold filters intersecting (the flipped order by transposing
symmetry). Delivered as the new master lemma
`spectralProjector_mul_spectralProjector` plus the two ordered
consumption shapes `_of_le` / `_of_le'`; the existing
`spectralProjector_idempotent` is **re-derived from the master at
unchanged statement** (its 50-line entrywise proof replaced by one
rewrite). Alongside it, the eigenvector-*action* layer: the complete
`spectralProjector_mulVec_eigvecOf`
(`P_c *ᵥ vᵢ = if λᵢ ≤ c then vᵢ else 0`) with its `_self` / `_of_lt`
specializations — the bandpass consumer interface.

**Delivered in the new `GraphTheory.Band`** (parameterized by interval
`(a, b]` per the design note, not by index; the definition is total
with the `a > b` negated-band junk documented rather than type-guarded;
every property carries `a ≤ b` exactly where needed): `bandProjector`,
`bandProjector_symmetric`, `bandProjector_idempotent` (through the
cross-law), the action interface
`bandProjector_mulVec_eigvecOf_self` / `_eq_zero_left` /
`_eq_zero_right`, the design note's named special case
`bandProjector_eq_spectralProjector_of_lt` (`spectralProjector` kept,
not re-derived), and the covering band `bandProjector_eq_one` (the
two-band instance of Step 3's completeness statement).

**QA** `SpectralGraph/Band_QA.lean` (27 declarations by the generator
metric, 917 total): the diagonal fixture `!![1,0;0,3]` — chosen over
the dense `!![2,1;1,2]` because one-dimensional eigenspaces make the
eigenvector *directions* computable from the eigen equations
(`λ = 1 ⇒ v = ![±1,0]`, sign-independent outer products, so no control
over Mathlib's classical choice is needed) — with the spectrum `{1,3}`
pinned from trace + determinant independent of the machinery under
test; the projector at any threshold in `[1,3)` pinned to the
hand-computed outer product `e₀e₀ᵀ = !![1,0;0,0]` (the proposal's
positive witness); band values computed independently (`B(−1,2] =
diag(1,0)`, `B(2,4] = diag(0,1)`, `B(−1,4] = 1`, and the
between-eigenvalues band `B(3/2,5/2] = 0` — the gapped-definition
guard); idempotence both through the theorem and by raw literal
multiplication; the cross-law instantiated numerically in both orders;
and mode selection witnessed in both directions — the excluded mode
**annihilated and provably not fixed** (`B(2,4] *ᵥ v₁ = 0 ≠ v₁` with
`v₁ ≠ 0` from unit norm), the strictly-interior mode (`λ = 3 ∈ (2,4]`)
fixed, the low-band mode fixed (theorem) and recomputed by raw
arithmetic.

**Verification:** `lake env lean` on `GraphTheory.Spectral`,
`GraphTheory.Band`, and `SpectralGraph/Band_QA` — zero errors, zero
warnings on the two new modules, `Spectral`'s only diagnostics the
documented pre-existing section-variable warnings; oleans produced
directly during iteration; `#print axioms` on the seven public and nine
headline QA theorems ✔ (three standard axioms only); **all thirty-four
QA modules batch-elaborated, zero errors**; the full `lake build`
detached from the tool timeout (log + poll) — see the terminal activity
entry for the final count; `lint_axioms` (**12**), `check_citations`,
`check_markdown_links` pass; scoreboard regeneration idempotent
(**917/12/0**; `Band_QA` a new file row at 27).

**Records updated:** module docstrings (Band + the Spectral additions),
umbrella (`Scaffold.lean` import + docstring), scoreboard (917/12/0,
the QA-module and public-module verification rows prepended with the
Band slice, the Step-1 interpretation bullet, the stale QA-declaration
count note fixed), radar (subject axis 2 evidence extended with the
band family and the QA axis count synced 917/34, **both held** per
protocol — the band projector is a second member of the
constructed-operator-family capability counted at the Tikhonov
re-score; Steps 2–4 are the natural re-score triggers; holds logged),
README (917; the proved list gains the band projectors), SGT index map
(new Band section, 8 rows; the Spectral section's projector-algebra
paragraph extended with the product-and-action layer; module list
updated), proposal (status header, Step-1 delivery record with the
route finding and the survey outcome, open-next-step rewritten to
Step 2), and `proposals/README.md` (High row note + Delivered row +
progress paragraph).

**Next milestone (open):** the same proposal's **Step 2 — orthogonality
of disjoint bands** (`a ≤ b ≤ c ≤ d`: the two band projectors compose
to zero; the route is paved — the cross-law's ordered forms expand the
product to `P_{min b d} − P_{min b c} − P_{min a d} + P_{min a c}`,
which collapses under the ordering), then Step 3 (partition
completeness) and Step 4 (the Hilbert projection specialization —
survey `Analysis/InnerProductSpace/Projection.lean` signatures first).
Or the Medium rows (Fiedler Phase B — needs an operator decision;
mixing-time Step 1; Reversibility A and B; Relative Entropy;
Perron–Frobenius + directed operators; discharge-perturbation — the
Davis–Kahan Step 0 survey; approximate spectral projection).

**Tikhonov Regularization in the Laplacian Eigenbasis (run 1,
2026-08-20; `proposals/tikhonov-shrinkage-filter.md`, the Active
table's top High row): DELIVERED — all three build steps in one run**
(the proposal's own "may cover more than one if the first lands
cleanly" clause). Pure hard crust — **zero new axioms** (count stays
12; `#print axioms` on all 18 public theorems reads only `propext,
Classical.choice, Quot.sound`).

**Definition-route decision (recorded before stating, per the standing
rule):** the minimizer is **defined directly by the eigenbasis
formula** `x* = ∑_k (π/(λ_k+π)) (v_k ⬝ᵥ y) • v_k`, not extracted by
`Classical.choice` from strict convexity — every interface theorem
(coefficient identity, normal equation, minimality) becomes a
computation and uniqueness a corollary of the strict-convexity
decomposition. A Mathlib convexity-API survey proved unnecessary on
this route (nothing outside the eigenbasis machinery is consumed —
the proposal's own cost case).

**Delivered in the new `GraphTheory.Tikhonov`:**

- **Step 2 first (the identity layer):** the closed-form
  eigencoefficient identity `tikhonovMinimizer_dotProduct_eigvecOf`
  (hypothesis-free — pure orthonormality), proved through a *generic*
  spectral-filter workhorse `dotProduct_eigvecOf_filter` (any filter
  function `g`; any graph-signal-processing consumer can reuse it),
  plus the expansion-injectivity `ext_of_dotProduct_eigvecOf_eq` and
  `eigvalOf_laplacian_nonneg`.
- **The normal equation both ways:** `tikhonovMinimizer_add_smul_one_mulVec`
  (`(L + π•1) *ᵥ x* = π • y`) and the **converse characterization**
  `eq_tikhonovMinimizer_of_add_smul_one_mulVec` — any solution of the
  normal equation *is* the minimizer. This is the interface that lets
  QA pin the spectral construction against a hand-solved linear
  system.
- **Step 1:** the objective `tikhonovObjective`, the
  **strict-convexity decomposition** `tikhonovObjective_sub_minimizer`
  (`obj(x) − obj(x*) = ∑_k (1 + λ_k/π)(d_k − d*_k)²`, positive
  weights by PSD + `π > 0`), and its two corollaries
  `tikhonovObjective_minimizer_le` (minimality) and
  `eq_of_tikhonovObjective_eq_minimizer` (vector-equality uniqueness).
- **Step 3:** the shrinkage-factor arithmetic layer
  (`tikhonovShrinkage` with `pos`, `ne_zero`, `le_one`, `lt_one`,
  `eq_one_iff`, strict antitonicity), mean preservation
  `sum_tikhonovMinimizer_eq_sum` (symmetry + `π ≠ 0` only — each
  component's mean is preserved on disconnected graphs),
  `tikhonovMinimizer_eigvecOf`, and the not-a-projection theorem
  `tikhonovMinimizer_ne_apply_self_of_eigvalOf_pos` (idempotence
  failure `T(T v) ≠ T v` at any positive-eigenvalue eigenvector; the
  sketch's nonnegativity hypothesis found unnecessary and deleted).
- **Two recorded statement-shape deviations from the proposal's
  Step 3:** (1) the claim "never exactly 1" is *false at λ = 0* — the
  factor is exactly `1` there, the kernel mode passes through
  untouched, and that **is** mean preservation; the delivered
  statements are `0 < factor`, `factor ≤ 1`, `factor < 1 ↔ 0 < λ`,
  `factor = 1 ↔ λ = 0`, strict antitonicity. (2) "not a projection"
  is delivered as a theorem (idempotence failure), not a docstring
  note.

**QA** `SpectralGraph/Tikhonov_QA.lean` (+30 by the generator metric;
`K₂`, signal `![1,0]`, `π = 1`): the minimizer **pinned through the
normal equation** — candidate `![2/3,1/3]` verified by hand (entrywise
Gaussian elimination, independent of the module) and promoted by the
converse characterization, so the spectral-theorem construction and a
hand-solved 2×2 system independently meet at the same vector; the
objective pinned exactly (`obj(x*) = 1/3` against `obj(y) = obj(0) =
1`, minimality instantiated, strict improvement certified); the
spectrum pinned (trace `2`, det `0`, PSD ⇒ eigenvalues ∈ {0,2}) making
the shrinkage story exact (factors `1` and `1/3`, ordering,
`1/3 ∈ Ioo 0 1`); **not-a-projection numerically** (`T(T y) =
![5/9,4/9] ≠ ![6/9,3/9] = T y` via a second hand-solved system);
mean preservation instantiated twice; and the **`hπ` guard
refuted-on-omission** (at `π = 0` the minimizer is the zero vector and
the hypothesis-free minimality would read `1 ≤ 0`). Named residual:
`tikhonovMinimizer_eigvecOf` not numerically instantiated (`eigvecOf`
entries are not kernel-computable; covered transitively by the two
normal-equation pins).

**Verification:** `lake env lean` on the public module and its QA —
zero errors, zero warnings; `#print axioms` on all 18 public and 14
headline QA theorems ✔ (three standard axioms only); oleans produced
directly during iteration; **all thirty-three QA modules
batch-elaborated, zero errors** (only the documented pre-existing
section-variable warnings in untouched modules); **full `lake build` ✔
(2185 targets, "Build completed successfully" — run detached from the
tool timeout after one invocation was killed at its tool timeout
mid-replay, the recorded hazard; the Mathlib oleans survived that
kill)**; `lint_axioms` (**12**), `check_citations`,
`check_markdown_links` pass; scoreboard regeneration idempotent
(**890/12/0**; `Tikhonov_QA` a new file row at 30).

**Records updated:** module/QA/umbrella docstrings, scoreboard
(890/12/0, the `lake build` row extended with the Tikhonov module and
the detached-build operational note, both Direct-rows prepended with
the Tikhonov slice, new milestone interpretation bullet, provenance
note), radar (subject axis 2 re-scored **3.5 → 4.0** — the axis's
first *constructed application-facing operator family*, the EML
re-score's precedent class; QA count synced 890/33 with the QA axis
**held at 4.0**; both logged in the re-scoring log), README (890;
proved list gains the Tikhonov family), SGT index map (new Tikhonov
section, 18 rows; module list updated), proposal (status header
DELIVERED + delivery record with both deviations + named residuals +
open-next-step none), and `proposals/README.md` (the High row moved to
Delivered; **Spectral Band Projectors is now the top High row**).

**Next milestone (open):** the Active table's remaining High row —
**Spectral Band Projectors** (`spectral-band-projectors.md`, no gate:
the two-sided band as the difference of two `spectralProjector`
calls); or the Medium rows (Fiedler Phase B — needs an operator
decision; mixing-time Step 1; Reversibility A and B; Relative
Entropy; Perron–Frobenius + directed operators; discharge-perturbation
— Davis–Kahan Step 0 survey; approximate spectral projection).

**Discharge the Weyl perturbation axiom (run 1, 2026-08-20; operator
direction: `proposals/discharge-perturbation-axioms.md`, `weyl_inequality`
only): DELIVERED.** Step 0's additive-bound spike returned a decisive
**positive** (recorded in the proposal before any module edit): the
additive window is *not* a free corollary of the norm bridge — it needs
both Courant–Fischer witness directions plus **both** Rayleigh
domination bounds, the bottom half (`evals_first_mul_dotProduct_le_quadForm`)
newly added to `GraphTheory.Spectral` as the mirror of the EML step's
`quadForm_le_evals_last` — but alongside them it is cheap (~120 lines).
Step 1 then executed per the direction: **`weyl_inequality` retired from
admitted axiom to proved theorem at the unchanged name, hypotheses, and
conclusion** (explicit axioms **13 → 12**; `#print axioms` reads only
`propext, Classical.choice, Quot.sound`). `davis_kahan_sin_theta` and
`cheeger_lower_bound` untouched, per the direction and the proposal's
own tractability ranking.

**Delivered in `Analysis.OperatorTheory.Perturbation.Weyl`:**

- `weyl_additive_upper` — `λᵢ(A+E) ≤ λᵢ(A) + λₙ(E)` (the witness
  subspace for `A` exhibited as a member of the competitor set defining
  `λᵢ(A+E)` through `evals_min_max`; `R_{A+E} = R_A + R_E` split by the
  local `quadForm_add'` copy, `R_E ≤ λₙ(E)` by `quadForm_le_evals_last`).
- `weyl_additive_lower` — `λᵢ(A) + λ₁(E) ≤ λᵢ(A+E)` (the competitor
  direction for `A` inside the `(i+1)`-dimensional witness subspace for
  `A+E`; the competitor vector's `R_A = R_{A+E} − R_E ≤ λᵢ(A+E) −
  λ₁(E)` by the new bottom domination).
- `theorem weyl_inequality` — the composed retirement (window →
  `l2OpNorm_eq_max_abs_evals` bridge; bridge's `1 ≤ card V` covered by
  vacuity at `card V = 0`).
- `spectral_gap_stability` — unchanged code, now fully hard crust.

**Downstream effect (verified by `#print axioms`):**
`davisKahanTwoPoint` conditional on `davis_kahan_sin_theta` alone;
`eventStreamProjectorDrift` on `davis_kahan_sin_theta` +
`matrix_azuma_hoeffding` — both shed the `weyl_inequality` dependency
without code changes.

**QA** `Perturbation/Weyl_QA.lean` (+14 by the generator metric, 18 in
file): the nonzero fixture `A = E = !![2,1;1,2]` with both spectra
pinned independently (trace/determinant/sortedness: `[1,3]`, `[2,6]`)
and `‖E‖ = 3` through the proved bridge — the bound instantiated at
both indices, **attained exactly** at the top (`|6−3| = 3 = ‖E‖`),
**strict** at the bottom (`1 < 3` — the proposal's required
non-vacuity witness), both additive bounds instantiated at both indices
with endpoint attainment, and the **window-endpoint guard**: the upper
additive bound with `λ₁(E)` in place of `λₙ(E)` refuted (`6 ≤ 4` is
false), so the window's endpoints are load-bearing and not
interchangeable. All nine QA theorems: three standard axioms only.

**Verification:** `lake env lean` on both changed public modules
(`GraphTheory.Spectral` + `Perturbation.Weyl`) and the QA module —
zero errors, zero warnings; oleans produced directly during iteration;
`#print axioms` on the four public theorems, nine QA theorems, and both
derived consumers ✔; **all thirty-two QA modules batch-elaborated, zero
errors**; **full `lake build` ✔ (2184 targets, "Build completed
successfully")**; `lint_axioms` (**12**), `check_citations`,
`check_markdown_links` pass; scoreboard regeneration idempotent
(**860/12/0**; `Weyl_QA` 4 → 18 by the generator metric). Environment
healthy at run start (5387 Mathlib oleans present; no cache fetch
needed).

**Records updated:** module/QA/derived docstrings (`ProjectorDrift`'s
dependency-status notes), scoreboard (860/12/0, verification rows
extended, Weyl-retirement interpretation bullet, derived-layer
provenance), radar (axes 2/7, proved-depth, downstream-reuse evidence
extended with scores **held** per protocol — assurance tracked through
the shrinking axiom count instead; QA count 860/32 with the holds
logged), README (860/12; Weyl moved to the proved list),
Mathlib coverage map (perturbation row: Weyl proved locally),
perturbation index map (Weyl section all-proved, 3 new rows),
probability index map (derived-chain dependency note), Weyl source
index (retirement annotation), proposal (Step-0 record + Step-1
delivery + status header + open-next-step), and
`proposals/README.md` (the Medium row's note rewritten).

**Next milestone (open):** back to the Active table's two ungated High
rows — **Tikhonov Regularization** (`tikhonov-shrinkage-filter.md`, a
corollary of the proved eigenbasis expansion) and **Spectral Band
Projectors** (`spectral-band-projectors.md`, the difference of two
`spectralProjector` calls) — or, on this proposal's track, the
**Davis–Kahan Step 0 survey** (its tractability is still genuinely
unknown even with the now-richer shelf). The other Medium rows (Fiedler
Phase B — needs an operator decision; mixing-time Step 1; Reversibility
A and B; Relative Entropy; Perron–Frobenius + directed operators;
approximate spectral projection) stay queued.

**Resolvent Calculus for PSD Matrices, Step 3 — injectivity (run 1,
2026-08-20): DELIVERED; the program is COMPLETE.** The Active
priority table's top High item (`proposals/resolvent-calculus-psd.md`)
at its recorded open next step — the final step, the proposal's item 5.
Pure hard crust — **zero new axioms** (count stays 13; `#print axioms`
on all three new public theorems reads only `propext,
Classical.choice, Quot.sound`).

**Delivered** in `Analysis.OperatorTheory.Resolvent`, exactly the
proposal's recorded route (contrapose the Step-1 resolvent identity:
equal resolvents collapse the identity's left side to `0`, so
`(A+1)⁻¹ * (B − A) * (B+1)⁻¹ = 0`; multiplying through by `A + 1` on
the left and `B + 1` on the right cancels both invertible outer
factors, leaving `B − A = 0`):

- `eq_of_inv_add_one_eq_inv_add_one` — the core algebraic form: equal
  resolvents of `+1`-invertible matrices force equal matrices. The two
  determinant hypotheses are exactly what the cancellation consumes
  (load-bearing — the QA guard refutes the hypothesis-free form).
- `resolvent_map_injective_of_quadForm_nonneg` — the proposal's item-5
  shape: `A ≠ B → (A+1)⁻¹ ≠ (B+1)⁻¹` on quadForm-nonneg matrices (the
  determinant hypotheses supplied by Step 1's
  `isUnit_det_add_one_of_quadForm_nonneg`).
- `inv_add_one_eq_inv_add_one_iff_of_quadForm_nonneg` — the packaged
  iff: resolvent equality as a *certificate* of matrix equality, for
  contrapositive consumers.

Load-bearing on Step 1 throughout — the factoring *is*
`resolvent_identity_sub`.

**QA** `OperatorTheory/Resolvent_QA.lean` (+19 declarations by the
scoreboard metric, 94 in file): the injectivity instantiated at **two
distinct PSD pairs** — `lap2` vs `0`, and the less degenerate `lap2`
vs `mat2` (neither zero; `mat2`'s PSD proved from the sum-of-squares
identity `xᵀ(mat2)x = (x₀+x₁)² + x₀² + x₁²`) — with both resolvents
independently pinned by left-inverse witnesses (`(mat2+1)⁻¹ =
(1/8)!![3,−1;−1,3]`, a new fixture), distinctness verified by entries
(`1/3 ≠ 0`, `2/3 ≠ 3/8`), bridge lemmas rewriting the theorem's
output to exactly those numeric facts, and the packaged iff consumed
contrapositively; plus the **invertibility guard** — the
hypothesis-free implication "equal resolvents → equal matrices"
**refuted** at `A = −1` vs `B = −1 + E` (`E` nilpotent, `B + 1 =
!![0,1;0,0]`, determinant `0` by a zero row): distinct matrices whose
`+1` shifts are both singular, so both resolvents are the junk inverse
`0` — equal while the matrices differ; the core theorem's determinant
hypotheses are load-bearing, not decorative.

**Verification:** `lake env lean` on the changed public module and its
QA module — zero errors, zero warnings; `#print axioms` on the three
new public theorems and eleven new QA theorems ✔ (three standard
axioms only); oleans produced directly during iteration; **all
thirty-two QA modules batch-elaborated, zero errors** (the only
diagnostics are the eight documented pre-existing section-variable
warnings in untouched modules); **full `lake build` ✔ (2184 targets,
"Build completed successfully")**; `lint_axioms` (13),
`check_citations`, `check_markdown_links` pass; scoreboard
regeneration idempotent (**846/13/0**; `Resolvent_QA` 75 → 94 by the
generator metric). Environment: the pruned-oleans state recurred at
run start; the recorded interpreted cache fetch restored the oleans.
Two mid-run operational events recorded in the scoreboard's
provenance note: `lake build` invocations interrupted at their tool
timeouts left the Mathlib olean dir wiped mid-replay (a re-fetch
restored it, and the final *uninterrupted* full build replayed the
trace residue and passed), and a macOS case-insensitivity trap was
diagnosed (creating `.lake/build/lib/lean/` in this workspace shadows
the toolchain's core `Lean/` tree and breaks all elaboration; this
repo's layout is `.lake/build/lib/Scaffold/...` directly).

**Records updated:** module/QA docstrings, scoreboard (846/13/0, the
QA-module and public-module verification rows extended, Step-3
interpretation bullet, provenance note), radar (axis 2, proved-depth,
and QA axis evidence extended with scores **held** — program
completion within counted interfaces, not a new capability family;
QA count 846/32; the holds logged in the re-scoring log), README
(846; the proved list gains the resolvent-map injectivity),
perturbation index map (3 new Resolvent rows; Deferred Work loses the
injectivity item), proposal Step-3 delivery record + status header
(program complete) + open-next-step (none; named residuals), and
`proposals/README.md` (the High row moved to Delivered; progress note
rewritten — **Tikhonov Regularization is now the top High row**).

**Next milestone (open):** the Active table's remaining High rows —
**Tikhonov Regularization** (`tikhonov-shrinkage-filter.md`, no gate:
a corollary of the proved eigenbasis expansion) and **Spectral Band
Projectors** (`spectral-band-projectors.md`, no gate: the two-sided
band as the difference of two `spectralProjector` calls). The Medium
rows (Fiedler Phase B — needs an operator decision; mixing-time Step
1; Reversibility A and B; Relative Entropy; Perron–Frobenius +
directed operators; discharge-perturbation; approximate spectral
projection) stay queued.

**Resolvent Calculus for PSD Matrices, Step 2 — the norm and Lipschitz
bounds (run 1, 2026-08-19): DELIVERED.** The Active priority table's
top High item (`proposals/resolvent-calculus-psd.md`), at the step its
Step-1 delivery record and the proposal's Open-next-step section both
named — pure hard crust, **zero new axioms** (count stays 13;
`#print axioms` on all three new public theorems reads only `propext,
Classical.choice, Quot.sound`). Step 3 (injectivity) was NOT started
(the proposal's one-step-per-run rule).

**Delivered** in `Analysis.OperatorTheory.Resolvent`, the proposal's
items 2 and 4, by the **recorded route deviation** (the proposal
sketched "the delivered bridge plus the shifted/inverted eigenvalue
transfer"; the *energy route* is strictly stronger and cheaper): for
`y = (M + t•1)⁻¹ *ᵥ x`, the quadratic-form hypothesis gives
`t‖y‖² ≤ quadForm M y + t‖y‖² = y ⬝ᵥ x ≤ ‖y‖‖x‖` (dot-product
Cauchy–Schwarz, transported to `EuclideanSpace` inner products through
the bridge's own `opNorm_le_bound`/`cstar_norm_def` spine), packaged
exactly as Step 0's upper direction was:

- `l2OpNorm_inv_add_smul_one_le_inv_of_quadForm_nonneg` — the
  **general-`t`** bound `‖(M + t•1)⁻¹‖ ≤ t⁻¹` with **no symmetry
  hypothesis** (the same strengthening style as Step 1's invertibility
  theorem; only the quadratic form at the resolvent's own argument is
  evaluated). Bonus strengthening recorded: the underlying energy
  inequality `t • (y ⬝ᵥ y) ≤ y ⬝ᵥ x` holds for *any* `t`
  (positivity enters only at the division step).
- `l2OpNorm_inv_add_one_le_one_of_quadForm_nonneg` — the `t = 1`
  instance, the proposal's item 2 (`‖(A+1)⁻¹‖ ≤ 1`).
- `l2OpNorm_resolvent_sub_le_of_quadForm_nonneg` — the proposal's item
  4, the **Lipschitz bound** `‖(A+1)⁻¹ − (B+1)⁻¹‖ ≤ ‖A−B‖`: the
  Step-1 resolvent identity, the scoped `NormedRing`
  submultiplicativity (`norm_mul_le` — resolving under
  `Matrix.L2OpNorm`, the instance Step 0 verified), and the norm bound
  on both factors — **load-bearing on Step 1 throughout** (both
  determinant hypotheses supplied by the Step-1 invertibility theorem;
  the factoring *is* `resolvent_identity_sub`).

The sorted-eigenvalue transfer for shifted/inverted matrices is
thereby not needed by this step and remains a named residual for a
consumer that genuinely needs eigenvalue pins of transformed matrices
(the mixing-time program's similarity transfer is the named such
consumer).

**QA** `OperatorTheory/Resolvent_QA.lean` (+45 declarations by the
scoreboard metric, 75 in file) — the proposal's three QA items plus
tightness: the norm bound **attained with route agreement**
(`‖(L(K₂)+1)⁻¹‖ = 1` exactly — the theorem's energy route and the
eigenvalue-bridge route, on the pinned spectrum `{1/3, 1}` of
`(1/3)!![2,1;1,2]`, independently meet at the value); the general-`t`
instance `‖(L+2•1)⁻¹‖ = 1/2` exactly (spectrum `{1/4, 1/2}`, the
`t = 2` resolvent `(1/8)!![3,1;1,3]` pinned by an independent
left-inverse witness) — also attained; the Lipschitz instance at
`A = L`, `B = 0` with **both sides independently pinned** (difference
spectrum `{-2/3, 0}` → norm `2/3`; `‖L‖ = 2` from spectrum `{0, 2}`;
the instantiated theorem reads `2/3 ≤ 2` — a reversed or badly-factored
statement would produce a falsehood); the **shift-load-bearing
witness** (the proposal's QA item 3): the invertible PSD `(1/4)I`
*without* the shift has `‖A⁻¹‖ = 4 > 1` (inverse `4I` by an
independent left-inverse witness, norm from the pinned spectrum
`{4,4}`); and the **hypothesis-load-bearing witness**: the symmetric
non-PSD `-(3/4)I` has `+1` shift equal to `(1/4)I` — invertible,
inverse norm `4 > 1` — with the violated hypothesis exhibited at
`![1,0]` (`quadForm = -3/4 < 0`).

**Verification:** `lake env lean` on the changed public module and its
QA module — zero errors, zero warnings; `#print axioms` on the three
new public theorems and eight headline QA theorems ✔ (three standard
axioms only); module oleans produced directly during iteration (the
recorded fast-`lean -o` path); **all thirty-two QA modules
batch-elaborated, zero errors** (the only diagnostics are the eight
documented pre-existing section-variable warnings in untouched
modules); full `lake build` ✔; `lint_axioms` (13), `check_citations`,
`check_markdown_links` pass; scoreboard regeneration idempotent
(**827/13/0**; `Resolvent_QA` 30 → 75 by the generator metric).
Environment: the pruned-oleans state recurred again at run start; the
recorded interpreted cache fetch restored the oleans (5685, ~4 min)
before any elaboration. Implementation notes recorded for future QA
work: the `Finset.prod_eq_multiset_prod` bridge (not `..._sum`) for
product pins; `det_eq_prod_eigenvalues` carries a `ℝ→𝕜` coercion that
only `simpa` normalizes away (the two-step `simpa` + `norm_num`
converts to the `lo * hi` pin shape); `norm_num` does not close
`|1/3| ≤ 1` — rewrite with `abs_of_nonneg (show (0:ℝ) ≤ 1/3 by
norm_num)` explicitly, and a trailing `try norm_num` absorbs `rw`'s
inconsistent auto-closing; `-2/3` parses as `(-2)/3`, so `abs_neg`
does not match — convert with `show (-2/3:ℝ) = -(2/3) from by
norm_num` first; `1/4 * 1/2` parses left-associatively as
`(1/4 * 1)/2` — parenthesize; the two-point spectrum pin is
generalized (`two_point_pin_of_sum_prod`, target roots `lo ≤ hi` with
sum/prod matching) and reused five times.

**Records updated:** module/QA docstrings, scoreboard (827/13/0, the
QA-module and public-module verification rows extended, Step-2
milestone bullet), radar (axis 2 evidence completed with the bounds,
score **held at 3.5** — family completion, not a new capability; QA
count 827/32 with the attainment/route-agreement and guard kinds; the
QA axis **held at 4.0**; both holds logged in the re-scoring log;
proved-depth hard-crust list extended), README (827; the proved list
gains the resolvent norm/Lipschitz bounds), perturbation index map
(3 new Resolvent rows; Deferred Work narrowed to Step-3 injectivity),
proposal Step-2 delivery record + status header + open-next-step
(Step 3), and `proposals/README.md` (the High row now points at Step
3).

**Next milestone (open):** Resolvent **Step 3** — injectivity
(`A ≠ B → (A+1)⁻¹ ≠ (B+1)⁻¹`, a one-line consequence of the Step-1
identity), which completes the program; or the two ungated High rows —
**Tikhonov Regularization** (a corollary of the proved eigenbasis
expansion) and **Spectral Band Projectors** (the difference of two
`spectralProjector` calls). The Medium rows (Fiedler Phase B — needs
an operator decision; mixing-time Step 1; Reversibility A and B;
Relative Entropy; Perron–Frobenius + directed operators;
discharge-perturbation — whose Weyl target now shares the bridge AND
the delivered norm/Lipschitz pattern; approximate spectral projection)
stay queued.

**Resolvent Calculus for PSD Matrices, Steps 0 and 1 (run 1,
2026-08-19): DELIVERED.** The Active priority table's top High item
(`proposals/resolvent-calculus-psd.md`), opened at its mandatory Step
0 gate and through Step 1 (the steps-0+1 precedent). Pure hard crust —
**zero new axioms** (count stays 13; `#print axioms` on every public
theorem reads only `propext, Classical.choice, Quot.sound`). Steps 2–3
(norm bound, Lipschitz bound, injectivity) were NOT started.

**Step 0 (the spike, decisive negative, then the fallback bridge):**
the C*-algebra thread `IsSelfAdjoint.spectralRadius_eq_nnnorm` is
**structurally inapplicable** to `Matrix V V ℝ` — it is stated
`[CStarAlgebra A]`, which extends `NormedAlgebra ℂ A` and
`StarModule ℂ A`, and `NormedAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℝ)`
fails to synthesize (elaboration-verified; the scoped
`Matrix.L2OpNorm` instances `NormedRing`/`CStarRing` resolve, but the
complex-algebra bundle cannot — a structural obstruction, not an
instance-search gap). The proposal's own contingency was adopted and
delivered in the new `Analysis.OperatorTheory.Resolvent`: the
from-scratch operator-norm bridge from the proved eigenbasis
machinery — `abs_eigvalOf_le_l2OpNorm` (unit eigenvector through
`toEuclideanCLM` + `ContinuousLinearMap.le_opNorm` +
`cstar_norm_def`), `l2OpNorm_le_of_abs_eigvalOf_le` (Parseval
`dotProduct_eigvecOf` + eigenaction `dotProduct_eigvecOf_mulVec`
resolving `‖M *ᵥ y‖²` termwise, then `opNorm_le_bound`), their
sorted-spectrum forms, and the packaged extremal identity
`l2OpNorm_eq_max_abs_evals` (`‖M‖ = max |evals hM 0| |evals hM last|`)
— the Step-0 target statement. One generic addition to the center:
`evals_first_le_eigvalOf` in `GraphTheory.Spectral` (the
first-sorted-entry mirror of `eigvalOf_le_evals_last`). The bridge is
the one-time cost the proposal identified — the shared route for
Step 2's norm/Lipschitz bounds and the
`discharge-perturbation-axioms.md` Weyl target.

**Step 1:** `isUnit_det_add_smul_one_of_quadForm_nonneg` — `M + t • 1`
invertible for *any* matrix with nonnegative quadratic form and
`t > 0` (kernel-vector route: a kernel vector would force
`quadForm M v + t (v ⬝ᵥ v) = 0`, both terms nonnegative, the second
positive — **no symmetry hypothesis needed**, a recorded strengthening
over the proposal's PSD-symmetric sketch), with the `t = 1` instance;
and `resolvent_identity_sub`
(`(A+1)⁻¹ − (B+1)⁻¹ = (A+1)⁻¹ * (B − A) * (B+1)⁻¹`) by pure
`nonsing_inv` algebra.

**QA** `OperatorTheory/Resolvent_QA.lean` (30 declarations, the first
OperatorTheory-domain QA file): the `!![2,1;1,2]` fixture with
spectrum `[1,3]` pinned from trace/determinant/sortedness independent
of the bridge; both directions composed to pin `‖mat2‖ = 3` exactly
(the literature spectral-norm value); the extremal form at
`max 1 3 = 3`; the **negative witness** `¬(‖mat2‖ ≤ 1)` — bounding by
one eigenvalue's absolute value is refuted, so the `∀ k` hypothesis is
load-bearing; the shifted-PSD invertibility cross-checked against
computed determinants (`3` at `t = 1`, `8` at `t = 2`) with the
**shift-load-bearing witness** (the unshifted `K₂` Laplacian's
determinant is exactly `0` — PSD alone gives no invertibility; the
`+1` is not decorative); and the resolvent identity at `A = L(K₂)`,
`B = 0` with `(L+1)⁻¹` computed to `(1/3)!![2,1;1,2]` by an
independent left-inverse witness, both sides of the identity
independently computed from the raw definitions to the same literal
matrix — a wrong factoring (order or sign) would fail the check.

**Verification:** `lake env lean` on both changed public modules
(`Spectral` + the new `Resolvent`) and the QA module — zero errors,
zero warnings; `#print axioms` on all eight public theorems and six
headline QA theorems ✔ (three standard axioms only); module oleans
produced directly during iteration; **all thirty-two QA modules
batch-elaborated, zero errors**; **full `lake build` ✔ (2184 targets,
"Build completed successfully")**; `lint_axioms` (13),
`check_citations`, `check_markdown_links` pass; scoreboard
regeneration idempotent (**782/13/0**, `OperatorTheory` a new QA
domain row). Environment: the pruned-oleans state recurred at run
start (Mathlib build dir empty); the recorded interpreted cache fetch
restored 5387 before any elaboration, and the full build replayed the
Mathlib trace residue (~35 min). Implementation notes recorded for
future L2OpNorm work: `CStarAlgebra` is the *complex* bundle — for
real matrices use the scoped `Matrix.L2OpNorm` instances plus
`cstar_norm_def`/`toEuclideanCLM_piLp_equiv_symm`/`toLin'_apply` as
the transport spine; `omit ... in` must precede doc comments; `rw`
with an equation whose LHS is a bare `1` rewrites every `1` in sight
(including inside `A + 1`); matrix entrywise computation is cheapest
via `Matrix.det_fin_two`/`det` on the *entries*
(`simp only [Matrix.add_apply, Matrix.one_apply, ...]` + `norm_num`),
not via literal-matrix rewriting; a numeral `2` in `2 • (1 : Matrix)`
elaborates as ℕ-smul unless written `(2 : ℝ)`.

**Records updated:** module/QA docstrings, umbrella (`Scaffold.lean` +
docstring), scoreboard (782/13/0, verification rows for the QA and
public module targets, milestone bullet), radar (subject axis 2
evidence extended with the bridge + steps-1 facts and the score **held
at 3.5** per protocol; QA count 782/32 with the pinned-norm/shift-guard/
identity-check kinds, the QA axis **held at 4.0** — both holds logged
in the re-scoring log; proved-depth hard-crust list extended), README
(782; the proved list gains the operator-norm/resolvent bridge),
Mathlib coverage map (the operator-norm row: the scoped L2OpNorm
instances exist but no real-matrix norm↔eigenvalue bridge — the
C*-thread's `NormedAlgebra ℂ` obstruction, elaboration-verified),
perturbation index map (new Resolvent section, 7 rows; Deferred Work
narrowed to steps 2–3), proposal Step-0 decision record + Step-1
delivery record + status header + open-next-step (Step 2), and
`proposals/README.md` (the High row now points at Step 2). The
operator's concurrent edits (`governance/ADVERSARIAL_REVIEW.md`,
`proposals/discharge-perturbation-axioms.md`) are preserved untouched.

**Next milestone (open):** the Active table's top High rows —
**Resolvent Step 2** (`‖(A+1)⁻¹‖ ≤ 1` and the Lipschitz bound
`‖(A+1)⁻¹ − (B+1)⁻¹‖ ≤ ‖A − B‖` through the delivered bridge plus the
shifted/inverted eigenvalue transfer, then Step 3's one-line
injectivity; or the ungated High items **Tikhonov Regularization**
(no gate — a corollary of the proved eigenbasis expansion) and
**Spectral Band Projectors** (no gate — the difference of two
`spectralProjector` calls). The Medium rows (Fiedler Phase B — needs
an operator decision; mixing-time Step 1; Reversibility A and B;
Relative Entropy; Perron–Frobenius + directed operators;
discharge-perturbation — whose Weyl target now shares the delivered
bridge; approximate spectral projection) stay queued.

**Decidable spectral certificates, Step 4 — QA and extraction
demonstration (run 1, 2026-08-19): DELIVERED; the program is
COMPLETE.** The Active priority table's top High item
(`proposals/decidable-spectral-certificates.md`) at its final step —
pure QA, **zero new axioms** (count stays 13; no public-module
changes), 688 → 752 QA declarations; `#print axioms` on all 22 new
headline theorems reads only `propext, Classical.choice, Quot.sound`.

**Delivered in the two QA modules:**

- `SpectralCertificates_QA.lean` (+17, 39 in file): the **`C₆`
  chain at the second required size** — kernel `decide` accept at the
  attained `1`, reject at `0`, fractional `3/2`/`1/2`, arithmetic
  pinned (`rawNumer = 8`, `denom = 4`, quotient `8/(2·4) = 1`), the ℚ
  specification through the proved bridge, end-to-end
  `lambda2 (C₆) ≤ 1` and `≤ 3/2`; and the **exact pin** — a C₄
  Poincaré inequality (`2‖x‖² ≤ xᵀLx` on `1⊥`; the `n = 4` Wirtinger
  identity `E = 2Σx² + 2(x₀+x₂)²` by `linear_combination`) through the
  **lower** half of `lambda2_variational` (`le_csInf` — its first
  `≥`-direction QA consumer) pins `lambda2 (C₄) = 2`, so the
  certificate chain is **exactly tight** (`cert4_certificate_exact_QA`:
  the kernel checker accepts precisely at the true `lambda2` and
  rejects the integer bound `1` below it).
- `Expander_QA.lean` (+47, 88 in file): the exact C₄ pins
  (`λ₂ = 2`, `λ_max = 4` — the latter via the alternating vector
  through `quadForm_le_evals_last`), so **`μ(C₄) = 2` exactly** and the
  Ramanujan bound `2√(d−1)` is *attained with equality*; the **`K₃`
  fixture** — the energy identity `xᵀLx = 3‖x‖² − (Σx)²` pinning
  `λ₂ = λ_max = 3`, `μ(K₃) = 1` (classical `μ(Kₙ) = 1`, strictly
  Ramanujan), with the EML **attained exactly on both cuts tested**
  (both sides compute to `2/3`); the **`C₆` EML** with derived `μ ≤ 2`
  (test vector + the identity `xᵀLx = 4‖x‖² − Σ_edges(xᵢ+xᵢ₊₁)²` +
  PSD), attained exactly on the alternating cut `({0,2,4},{0,2,4})`.

**Acceptance Criterion 4 (documentation):** scoreboard (752/13/0,
verification rows + step-4 milestone bullet), radar (QA count/kinds
synced; subject axes 4 and 7 evidence extended with scores **held** per
protocol and the holds logged in the re-scoring log), the
traction-plan extraction-gap note (the revisit precondition named there
is met — added as planning provenance respecting that document's
clean-room boundary), README count (752), proposal Step-4 delivery
record + status header (program complete, AC 1–4 all met), and
`proposals/README.md` (row moved to Delivered; progress note rewritten
— the three `sgt-gaps`-promoted High rows are now the top of the Active
table).

**Verification:** `lake env lean` on both changed QA modules — zero
errors, zero warnings; `#print axioms` on the 22 new headline theorems
✔ (three standard axioms only); all thirty-one QA modules
batch-elaborated, zero errors; **full `lake build` ✔ (2183 targets)**;
`lint_axioms` (13), `check_citations`, `check_markdown_links` pass;
scoreboard regeneration idempotent (752/13/0). Environment healthy at
run start (full Mathlib oleans present — the pruned-oleans state did
not recur; no cache fetch needed). Recorded implementation notes: the
`cons_val` simp family stops at index four (the `rfl`-provable
`vecCons_val_five` helper bridges index five when both indices are
`OfNat`-literals from sum expansion; `fin_cases` row indices defeat the
chain, so C₆ row sums are proved per row by `show` up to defeq); ℤ
structural facts evaluate by `decide` where ℝ ones cannot.

**Next milestone (open):** the Active table's top High rows are now the
three `sgt-gaps`-promoted items, each with its recorded entry point —
**Resolvent Calculus for PSD Matrices** (Step 0 first: the unverified
`IsSelfAdjoint.spectralRadius_eq_nnnorm` C*-algebra thread for the
operator-norm bridge, shared with `discharge-perturbation-axioms.md`'s
Weyl target), **Tikhonov Regularization in the Laplacian Eigenbasis**
(no gate — a corollary of the proved eigenbasis expansion), and
**Spectral Band Projectors** (no gate — the two-sided band is the
difference of two existing `spectralProjector` calls). The Medium rows
(Fiedler Phase B — needs an operator decision; mixing-time Step 1;
Reversibility Phases A and B; Relative Entropy; Perron–Frobenius +
directed operators; discharge-perturbation; approximate spectral
projection) stay queued.

**Decidable spectral certificates, Step 3 — the computable certificate
module (run 1, 2026-08-19): DELIVERED.** The Active priority table's
top High item (`proposals/decidable-spectral-certificates.md`), at the
step its Step-2 delivery record named as next. Pure hard crust —
**zero new axioms** (count stays 13; `#print axioms` on every public
theorem of the new module reads only `propext, Classical.choice,
Quot.sound`). Step 4 was NOT started this run.

**Delivered** in the new `GraphTheory.SpectralCertificates`, exactly
as the Step 0 re-scoping pinned — both halves, bridged: (a) the
ordered-field transport layer, whose hinge `algebraMap_apply`
(`algebraMap ℚ ℝ q = (q : ℝ)`) is `rfl`, carrying symmetry,
nonnegativity, dot products, and the Dirichlet energy
(`quadForm_laplacian_map_algebraMap` — the certificate's `rawNumer` is
exactly `quadForm (laplacian A ℝ) (toReal v)` halved, load-bearing on
the center's `laplacian_quadForm` convention); (b) the one-sided
Rayleigh consumer form `lambda2_le_rayleigh` — the division-form twin
of the Step-2 multiplication bound, proved straight from the proved
`lambda2_variational` (constraint-set membership + PSD
boundedness); (c) the ℚ specification checker
`isSpectralUpperBoundCertificate` with its soundness theorem
`lambda2_le_of_certificate` at exactly the proposal's sketched
statement shape — the flagship load-bearing consumer of
`lambda2_variational`: `rawNumer/2` is the Laplacian energy,
`dotOne = 0` is the constraint, `sInf ≤ rayleigh ≤ bound` follows
(two recorded implementation deviations: the cross-multiplied raw
inequality form so both checkers share one shape, and `decide`
conjuncts with public `rfl` unfolding lemmas because the `let`-shaped
bodies yield no usable simp equations); (d) the kernel-verifiable
**ℤ cross-multiplied twin** `isSpectralUpperBoundCertificateInt`
(exactly the Step 0 recorded shape, `== 0` included) and its
fractional-bound variant, with the proved bridges —
`...Int_iff` (sound *and complete* against the specification at an
integer bound) and `...IntFrac_iff` (the cross-multiplication bridge;
`0 < den` external, genuinely needed for the reverse direction — the
ℚ-side bound alone cannot see the sign of `den`); (e) the
kernel-facing corollaries `lambda2_le_of_certificateInt` /
`...IntFrac` (the executable chain: `decide`d integer data → proved
bridge → real bound; the matrix-equality transfer
`lambda2_le_of_matrix_eq` handles `lambda2`'s proof-valued symmetry
argument by `subst` + proof irrelevance).

**QA** `SpectralGraph/SpectralCertificates_QA.lean` (22 declarations,
fresh `C₄` fixture): kernel-`decide`d demonstrations on the twin —
accepted at the attained bound `2`, rejected at `1`, non-orthogonal
and zero test vectors rejected, fractional `5/2` accepted / `3/2`
rejected; the ℚ specification proved `= true` **only through the
proved bridge** (the Step 0 wall made explicit — the bridge is
load-bearing in QA); the end-to-end soundness instances
`lambda2 (C₄) ≤ 2` and `≤ 5/2` consuming `decide`d hypotheses; the
checker's arithmetic pinned (`dotOne = 0`, `denom = 2`, `rawNumer =
8`, Rayleigh quotient `4/2 = 2` — the certified bound is exactly the
test vector's quotient); and the **guard refutation** —
`lambda2 ≤ rayleigh onesVec` refuted on the connected cycle
(`0 < lambda2` via `lambda2_pos_of_connected`, `rayleigh onesVec = 0`
computed), so the orthogonality conjunct (and the zero-vector guard,
same junk value `0`) is load-bearing, exactly as the proposal's
Calibration 2 demands. Acceptance Criterion 2 thereby read against
the ℤ twin as re-scoped.

**Verification:** `lake env lean` on the new public module and its QA
module — zero errors, zero warnings; `#print axioms` on all eight
headline public theorems and the five key QA theorems ✔ (three
standard axioms only); module olean produced directly during
iteration; **all thirty-one QA modules batch-elaborated, zero
errors**; **full `lake build` ✔ (2183 targets, one more than before —
the new module; 6:27 wall)**; `lint_axioms` (13), `check_citations`,
`check_markdown_links` pass; scoreboard regeneration idempotent
(**688/13/0**). Environment: the pruned-oleans state recurred at run
start; the recorded interpreted cache fetch re-applied (5685 files
unpacked) before any elaboration.

**Records updated:** module/QA docstrings, umbrella (`Scaffold.lean`
+ its docstring), scoreboard (688/13/0, verification rows for the new
public and QA modules, step-3 milestone bullet), radar (subject axis
7 re-scored **3.0 → 3.5** — the axis's first verified
numerical/spectral algorithm driver, with the re-score logged; QA
count 688/31 with the kernel-`decide`d algorithmic QA kind described;
the QA axis **held at 4.0** per protocol — parametric/randomized QA
untouched), README (688, the proved list gains the
certificate-soundness layer, new module row, axis-7 cell 3.5), SGT
index map (new `SpectralCertificates` section, 11 rows + header;
module list updated), proposal Step-3 delivery record (with both
implementation deviations and the `0 < den` external-hypothesis
note) + status header, and `proposals/README.md` (High row now points
at Step 4).

**Next milestone (open):** proposal Step 4 — QA and extraction
demonstration: the `C₆` kernel-`decide` demonstrations, the
`Kₙ`/`Cₙ` Ramanujan fixture family per the Step 0 scope decision
(drop the label rather than expand scope if awkward), exact spectrum
pins for the derived-`μ`/certified-bound sharpness (the C₄ QA pins
the *quotient*, not `lambda2 = 2` itself — an exact lower-bound pin
is Step 4's natural completion), and the Acceptance-Criterion-4
documentation notes (scoreboard/radar/traction-plan). The Medium rows
(Fiedler Phase B — needs an operator decision; mixing-time Step 1;
Reversibility Phase A and Phase B; Relative Entropy; the new
resolvent/Tikhonov/band-projector High rows) stay queued.

**Decidable spectral certificates, Step 2 — the Expander Mixing Lemma
itself (run 1, 2026-08-19): DELIVERED.** The Active priority table's
top High item (`proposals/decidable-spectral-certificates.md`), at the
step its Step-1 delivery record named as next. Pure hard crust —
**zero new axioms** (count stays 13; `#print axioms` on all nine new
public theorems reads only `propext, Classical.choice, Quot.sound`).
Steps 3–4 were NOT started this run.

**Delivered route** (cheaper and stronger than the proposal's
eigenspace-expansion sketch — no eigenspace split of `A`, no
Cauchy–Schwarz, no kernel case analysis, no affine spectrum transfer):
(a) two generic additions to `Spectral.lean` — `eigvalOf_le_evals_last`
(sort membership + monotonicity) and the top Rayleigh domination in
multiplication form `quadForm_le_evals_last` (`xᵀ M x ≤ λ_max •
(x ⬝ᵥ x)` for every symmetric matrix, unconditionally in `x`), plus
`dotProduct_self_pos` made public; (b) the `d`-regular identity
`quadForm_add_quadForm_laplacian` (`xᵀAx + xᵀLx = d • ‖x‖²` — the
quadratic form of `A + L = D`), with generic support `quadForm_add`,
`quadForm_add_sub_eq` (polarization), `quadForm_degreeMatrix`;
(c) the Rayleigh sandwich on `1⊥` — `lambda2_mul_dotProduct_le_quadForm`
(the proved `secondEval_le_rayleigh` multiplied out) below,
`quadForm_le_evals_last` above — giving the operator bound
`abs_quadForm_le_of_ortho_onesVec`; (d) the sharp bilinear bound
`quadForm_bilinear_sq_le_of_ortho_onesVec` by the scaling trick
(`√Y•x ± √X•y` through polarization; `a² = Y, b² = X` attains AM–GM
equality — no slack); (e) the variance identity
`dotProduct_centeredIndicator_self` (`‖cS‖² = |S|(|V|−|S|)/|V|`);
(f) the headline `expander_mixing_lemma` at the Step 0 restated `√`
signature, squaring only inside the proof. **Statement-shape
strengthening recorded in the proposal:** the Step 0 sketch's `hloop`
hypothesis is dropped — the `A + L = D` identity needs regularity
only (self-loops sit on `D`'s diagonal either way).

**QA** `SpectralGraph/Expander_QA.lean` (+19 declarations, 41 in
file): the spectral hypothesis is **derived, not assumed** — `μ = 2`
proved on `C₄` from three independent bounds (test vector
`![1,0,−1,0]` with Rayleigh quotient `2` for `λ₂ ≤ 2` via
`secondEval_le_rayleigh`; a direct sum-of-squares estimate
`xᵀLx ≤ 4‖x‖²` routed to `λ_max ≤ 4` through `quadForm_eigvecOf_self`
+ `evals_mem_eigvalOf`; PSD lower bounds for both). The lemma is
instantiated on two cuts, and the bound is **attained exactly** on the
opposite cut (both sides independently compute to `2`: `|0−2| =
2√16/4`) and on the alternating vector in the operator bound
(`|xᵀAx| = 8 = 2‖x‖²`) — the derived `μ` is tight, the theorem not
vacuous; the half cut's deviation computes to `0`, and the variance
identity cross-checks against the pinned `±1/2` entries.

**Verification:** `lake env lean` on both changed public modules and
the QA module — zero errors, zero warnings; `#print axioms` on the
nine new public theorems ✔ (three standard axioms only); explicit
`lake build` of the two targets ✔; **full `lake build` ✔ (2182
targets)**; all thirty QA modules batch-elaborated, zero errors;
`lint_axioms` (13), `check_citations`, `check_markdown_links` pass;
scoreboard regeneration idempotent (**666/13/0**). Environment: the
pruned oleans state recurred at run start; the recorded interpreted
cache fetch restored Mathlib's oleans, then `lake build Batteries`
preceded iteration (direct `lake env lean -o` used for fast olean
updates during iteration; the final full `lake build` replayed the
trace chain and rebuilt cleanly).

**Records updated:** module/QA docstrings, umbrella (`Scaffold.lean`),
scoreboard (666/13/0, verification rows, step-2 milestone bullet),
radar (subject axis 4 re-scored **3.5 → 4.0** — a new theorem family,
spectral–combinatorial discrepancy, with the re-score logged; QA count
666/30 with the derived-hypothesis and sharpness QA kinds described;
the QA axis **held at 4.0** per protocol — parametric/randomized QA
untouched; proved-depth text; weakest-axes paragraph), README (666,
axis-4 cell 4.0, the proved list gains the EML, cuts-and-expansion
module row), SGT index map (8 new Expander rows + section header; 3
new Spectral rows), proposal Step-2 delivery record (+ the `hloop`
deviation) + status header, and `proposals/README.md` (High row now
points at Step 3). The operator's concurrent changes (README's
why-SGT section; untracked `governance/ADVERSARIAL_REVIEW.md` and six
new untracked proposals incl. `directed-graph-operators.md`; edits to
`1_STRATEGY.md`, `6_SGT_BACKLOG.md`, `CONTRIBUTING.md`,
`admit-perron-frobenius.md`, `electrical-flow-routing.md`) are
preserved untouched.

**Next milestone (open):** proposal Step 3 — the computable
certificate module, now scoped by the Step 0 record: deliver both the
ℚ-facing soundness statement (`isSpectralUpperBoundCertificate` /
`lambda2_le_of_certificate`, consuming `lambda2_variational` — the
proposal's flagship load-bearing consumer) and the kernel-verifiable
integer cross-multiplied twin, bridged by a proved cross-multiplication
lemma; then Step 4 (QA incl. the kernel `decide` demonstrations on
`C₄`/`C₆` and the Ramanujan fixture family). The Medium rows (Fiedler
Phase B — needs an operator decision; mixing-time Step 1; Reversibility
Phase A; Relative Entropy) stay queued.

**Decidable spectral certificates, steps 0 and 1 (run 1, 2026-08-19):
DELIVERED.** The Active priority table's top High item
(`proposals/decidable-spectral-certificates.md`) opened at its
recorded gate and through its first build step — the steps 0–1
precedent of the electrical-flow program. Zero new axioms (count stays
13); steps 2–4 were NOT started this run.

**Step 0 (the gate, recorded in the proposal before any Lean):** (1)
the adjacency-vs-Laplacian convention resolved **Laplacian-first
through the `d`-regular bridge** — survey evidence: no
adjacency-eigenvalue interface exists anywhere (adjacency is weights
and fixtures only; every spectral declaration is Laplacian-wrapped or
generic-symmetric), the certificate half (Step 3) is already
Laplacian, the generic symmetric engine applies to an adjacency matrix
for free (so the bridge `A = d•1 − L` needs no new interface), and no
named consumer wants adjacency eigenvalues; the restated
`expander_mixing_lemma` signature is pinned in the proposal with the
`√`-form as the mathematical statement and squaring as a recorded
Step-2 implementation option. (2) The ℚ-`decide` spike returned a
decisive **negative**: plain kernel `decide` cannot verify the
proposal's ℚ-arithmetic certificate — a reducibility wall, not
performance (`((2:ℚ) + 2) = 4` is already stuck at `(Rat.add 2 2).num`:
ℚ literals are opaque kernel literals, so `Rat.add`/`Rat.div`/
`Rat.blt` never unfold in elaborator reduction; `#eval` works via
native externs but is not kernel-checked; controls `Nat.gcd`,
ℕ-sums-over-`Fin`, and ℤ arithmetic all decide fine). Adopted fallback
(recorded): the **integer cross-multiplied twin** — all data in ℤ,
inequality `rawNumer ≤ 2 * bound * denom` — kernel-decided clean at
`C₄` (`Fin 4`, attained `λ₂ = 2`: accepted at `2`, rejected at `1`;
non-orthogonal and zero test vectors rejected) and `C₆` (`Fin 6`,
attained `λ₂ = 1`), plus the fractional-bound clearing form (`λ₂ ≤ 5/2`
accepted, `≤ 3/2` rejected); whole acceptance file ~15 s wall, almost
all `Mathlib.Tactic` import. Step 3 is thereby re-scoped: deliver both
the ℚ-facing soundness statement and the ℤ twin, bridged by a proved
cross-multiplication lemma; Acceptance Criterion 2 reads against the
twin. (3) Ramanujan QA scope resolved to the existing `Kₙ`/`Cₙ`
fixture family (both are small Ramanujan instances), with the
drop-if-awkward fallback per the proposal's own rule.

**Step 1 (hard crust):** the new `Scaffold/Mathlib/GraphTheory/Expander`
— `edgeWeight` (degenerate-cut guards, the degree-sum form
`edgeWeight A S univ = ∑ i ∈ S, deg A i`, the hypothesis-free matrix
form `edgeWeight_eq_dotProduct`, `edgeWeight_symm` by sum swap);
`indicatorVec`/`centeredIndicator` with the decomposition and the
orthogonality `sum_centeredIndicator_eq_zero` /
`centeredIndicator_dotProduct_onesVec` — both **unconditional** (the
empty-type case handled; no `Nonempty` hypothesis carried — a small
strengthening over the proposal's sketch); `mulVec_onesVec_eq_const`
(consuming `deg`'s row-sum shape); and the headline
`edgeWeight_eq_regular_add_centered` (`e(S,T) = d·|S|·|T|/n +
centered cross term`), symmetry load-bearing through
`Matrix.dotProduct_mulVec`'s transpose and regularity through the
`A *ᵥ onesVec = d` evaluation. `#print axioms` on all seven public
theorems: only the three standard axioms.

**QA** `SpectralGraph/Expander_QA.lean` (22 declarations, fresh `C₄`
fixture per the QA-independence convention): values computed from the
raw definitions (adjacent `1`, opposite `0`, half-and-half `2`, total
`8`, matrix form cross-checked, centered indicators pinned entrywise
with orthogonality computed from the pinned entries); the
decomposition instantiated on an adjacent cut (`1 = 1/2 + 1/2`) and an
opposite cut (`0 = 1/2 − 1/2`), cross terms computed independently;
three negative witnesses — main-term-only refuted (`0 ≠ 1/2`), wrong
degree refuted (`1 ≠ 3/4`), asymmetric weight breaks cut symmetry
(`2 ≠ 1`).

**Verification:** `lake env lean` on both changed modules — zero
errors, zero warnings (targeted `omit` clauses on unused section
variables; two `set_option linter.unnecessarySeqFocus false in` on the
cross-term lemmas where `simp` closes some `fin_cases` branches —
repo precedent); `#print axioms` on the seven public theorems ✔;
explicit `lake build` of both targets ✔; full `lake build` ✔ (2182
targets, one more than before — the new module); all **thirty** QA
modules batch-elaborated, zero errors (only the documented
pre-existing section-variable warnings in untouched modules);
`lint_axioms` (13), `check_citations`, `check_markdown_links` pass;
scoreboard regeneration idempotent (647/13/0). Environment: the pruned
oleans state recurred at run start (Mathlib empty, Batteries partial,
Scaffold empty) — the recorded interpreted cache fetch restored
Mathlib's 5685, then an explicit `lake build Batteries` (the fetch
does not cover Batteries' non-default facet modules that
`Mathlib.Tactic` needs) preceded the full `lake build` (~33 min cold
residue; recorded for the next run).

**Records updated:** module/QA docstrings, umbrella (`Scaffold.lean` +
docstring), scoreboard (647/13/0, verification rows, milestone
bullet), radar (QA 647/30 with the discrepancy-core QA kind described;
the QA axis **held at 4.0** per protocol with the hold recorded in the
re-scoring log — steps 0–1 are decisions and interface plumbing, the
parametric-QA gap untouched), README (647, cuts-and-expansion module
row), SGT index map (new `Expander` section, 6 rows + status line),
proposal Step-0 decision record + restated signature + Step-1 delivery
record, and `proposals/README.md` (High row now points at Step 2).

**Next milestone (open):** proposal Step 2 — **the Expander Mixing
Lemma** itself: the bridge layer (the eigenvalue hypothesis
`max |d − λ| ≤ μ` → the Rayleigh-form operator bound `|xᵀAx| ≤ μ xᵀx`
on `x ⊥ 1`, through the eigenbasis/Courant–Fischer machinery), then
the centered-cross-term bound by Cauchy–Schwarz, packaged as the
restated signature (with the recorded option to square both sides to
stay in ordered-field arithmetic); then Step 3 (the certificate
module, now scoped with the ℤ twin) and Step 4 (QA incl. the kernel
`decide` demonstrations on `C₄`/`C₆`). The Medium rows (Fiedler Phase
B — needs an operator decision; mixing-time Step 1; Reversibility
Phase A; Relative Entropy) stay queued. The operator's untracked
`adversarial.md`, `sgt-gaps.md`, and `why-sgt.md` are preserved
untouched.

**Foster's Theorem Phase A (run 1, 2026-08-19): DELIVERED.** The Active
priority table's top High item, `proposals/spectral-graph-sparsification.md`
**Phase A only**, delivered as pure hard crust in the new
`Scaffold/Mathlib/GraphTheory/Foster` — **zero new axioms** (count stays 13;
`#print axioms foster_theorem` reads only `propext, Classical.choice,
Quot.sound`). Phase B was NOT started (blocked in the proposal on the
unresolved matrix-Chernoff scope decision).

**Delivered** (all proved): `card_filter_eigvalOf_laplacian_eq_zero` (the
kernel of a connected Laplacian occupies exactly one eigenbasis index —
at most one by orthonormality against the one-dimensional kernel, at
least one because `onesVec` is a nonzero kernel vector — the counting
fact behind `n − 1`); `effectiveResistance_eq_sum_eigbasis` (the
per-pair spectral sum `R u v = ∑_k (v_k u − v_k v)²/λ_k` over nonzero
eigenvalues — the pseudoinverse-free Foster kernel); the headline
`foster_theorem` (`(∑ i, ∑ j, A i j * R i j)/2 = card V − 1` on every
connected symmetric-nonnegative network, stated at full strength with
no cardinality hypothesis); and the leverage-score objects
(`leverageScore` — the importance-sampling object of the blocked
Phase B, junk below `2 ≤ card V` documented — and
`sum_leverageScore_eq_two`, the probability-distribution corollary with
`hcard` as the division guard). Route exactly as the proposal's
"Correction" scoped: spectral resolution + double-sum swap +
per-eigenvector Dirichlet evaluation (`∑_{i,j} A i j (v_k i − v_k j)² =
2 λ_k` via `laplacian_quadForm`/`quadForm_eigvecOf_self`) + the
kernel-index count — reconciling (not reversing) the
`electrical-structure-crust.md` removal, which was of the `L⁺` route
only; no pseudoinverse or matrix square root anywhere.

**QA** `SpectralGraph/Foster_QA.lean` (53 declarations): the cliques
`K₃`/`K₄`, the path `P₃`, and the 3-leaf star — every resistance pinned
by an explicit potential witness (`K₄` through the general-pair
potential `(e i − e j)/4`, proved to solve the unit demand for *every*
pair via the entrywise `L = 4I − J` structure, so all twelve ordered
terms are pinned by one lemma); each ordered Foster sum computed
independently of the theorem (`4`, `6`, `4`, `6`) and cross-checked
against the theorem's `card V − 1` (`2`, `3`, `2`, `3`); the
**double-counting factor refuted-on-omission on both cliques** exactly
as the proposal's calibration demands (`4 ≠ 2` on `K₃`, `6 ≠ 3` on
`K₄` — a statement shape dropping the `/ 2` would be refuted);
non-edge pairs provably absent (zero conductance); leverage pinned
(`K₃` edge `1/3`, total `2`; `K₄` edge `1/6`).

**Verification:** `lake env lean` on both changed modules — zero
errors, zero warnings (the five `K₄`-adjacent QA lemmas where `simp`
closes some `fin_cases` branches carry targeted
`set_option linter.unreachableTactic/unusedTactic false in`
modifiers); `#print axioms` on all four public theorems confirms only
the three standard axioms; `lake build` of the Foster target ✔; full
`lake build` ✔ (2181 targets, one more than before — the new module);
all twenty-nine QA modules batch-elaborated, zero errors (only the
eight documented pre-existing section-variable warnings in untouched
modules); `lint_axioms` (13), `check_citations`, `check_markdown_links`
pass; scoreboard regeneration idempotent (625/13/0). Environment: the
pruned Mathlib-oleans state recurred at run start; the recorded
interpreted cache fetch restored 5387 oleans before any elaboration
(see the scoreboard's provenance note).

**Records updated:** module/QA docstrings, umbrella (`Scaffold.lean` +
its docstring), scoreboard (625/13/0, verification rows, Foster
milestone bullet), radar (subject axis 6 re-scored **4.0 → 4.5** — a
new theorem family, global network identities, not packaging — with
the re-score logged; QA 625/29 with the Foster QA kind; weakest-axes
paragraph; re-scoring log), README (625, axis-6 cell 4.5, Foster added
to the proved list and the electrical-structure module row), SGT index
map (new Foster section, 5 rows), backlog item 7 (Foster delivered;
family residuals unchanged), proposal Phase A delivery record + status
header, and `proposals/README.md` (Phase A row moved from Active to
Delivered; progress note rewritten — **decidable spectral certificates
is now the top High item**, Step 0 gate first).

**Next milestone (open):** the Active table's top High item is now
**decidable spectral certificates Step 0** (the convention decision +
ℚ-`decide` spike, both scoped in its own proposal — do not begin Step
1 before they are recorded); the Medium rows (Fiedler Phase B — needs
an operator decision; mixing-time Step 1; Reversibility Phase A;
Relative Entropy) are queued behind it. The operator's Medium/Low rows
and the untracked `why-sgt.md` are preserved untouched.

**Electrical-flow routing, step 5 — the ICP capacity-reinforcement
example (run 1, 2026-08-19): DELIVERED; the program is COMPLETE.** The
Active priority table's top High item `proposals/electrical-flow-routing.md`,
at its recorded final step, delivered as pure packaging of step 4 (zero
new axioms; the explicit count stayed 13 throughout the program).

**Delivered** in `GraphTheory.ElectricalFlow` (9 declarations, all
proved): `increaseConductance` (raise one undirected pair's conductance
by `δ`, both ordered entries together so symmetry/nonnegativity are
preserved) with the entry interfaces and structural lemmas
(`increaseConductance_apply_of_reinforced`/`_of_not_reinforced`,
`le_increaseConductance`, `increaseConductance_isSymm`,
`increaseConductance_nonneg`); the connectivity adapter pair the step-4
record named as step 5's natural companion — `supportGraph_le_of_le`
(support graphs grow along entrywise domination, **no nonnegativity
hypothesis** since `0 < A i j ≤ B i j`) and `supportGraph_connected_of_le`
(capacity growth preserves connectivity, via Mathlib's
`SimpleGraph.Connected.mono` — found in the pin, no local walk
induction needed); and the one-hypothesis headline
`effectiveResistance_le_increaseConductance`:
`effectiveResistance (increaseConductance A i j δ) u v ≤
effectiveResistance A u v` for `δ ≥ 0`, with only the *original*
network's connectivity hypothesized — the reinforced network's is
derived. This is the proposal's ICP-facing fact as a one-line consumable
theorem: adding capacity cannot worsen the certified energy cost of
electrical routing.

**QA** `SpectralGraph/ElectricalFlow_QA.lean` (+9 declarations, 88 in
file) — the release-facing proof example, on the Mathlib `Fin 3` path
graph through `SimpleGraph.toWAdj` (the proposal's suggested route):
the adapter weights bridged entrywise to the weighted-fixture world
(`path3_toWAdj_eq_connPathAdj`); the reinforcement computed to exactly
the concrete doubled-path matrix (`path3_reinforced_eq_pathDoubled_QA`);
the reinforced resistance `3/2` pinned by the independent potential
witness `![1/2, 0, −1]`, with the reinforced network's connectivity
proved by explicit walks — computed independently of the adapter the
headline consumes; the headline instantiated in the one-hypothesis form
(`path3_reinforcement_QA`); and the decrease certified strict
`3/2 < 2` against the adapter-bridged pinned original value
(`path3_reinforcement_strict_QA`).

**Verification:** `lake env lean` on both changed modules — zero
errors, zero warnings (targeted `omit [Fintype V]`/`[DecidableEq V]`
clauses where the section variables are unused); explicit `lake build`
of both targets ✔; all twenty-eight QA modules batch-elaborated, zero
errors; full `lake build` ✔ (2180 targets); `lint_axioms` (13),
`check_citations`, `check_markdown_links` pass; scoreboard regeneration
idempotent (572/13/0). One mid-run repair: a placeholder stub inserted
by a bad edit was replaced with the real section before any
verification ran (the policy forbids `True` placeholders; the delivered
module contains none).

**Records updated:** module/QA docstrings, scoreboard (572/13/0,
verification rows, step-5 milestone bullet), radar (QA 572/28 with the
step-5 kind; axis-6 evidence extended to program-complete with the
score **held at 4.0** — packaging, not new mathematics; the step-4
3.5 → 4.0 re-score added to the re-scoring log for continuity;
proved-depth completion clause; weakest-axes paragraph; header review
date), README (572), SGT index map (4 new rows; section header to
steps 0–5 complete), backlog item 7 (program-complete note), proposal
step-5 delivery record + status/open-next-step sections, and
`proposals/README.md` (row moved from the Active table to Delivered;
progress note rewritten — **Foster Phase A is now the top High item**).

**Next milestone (open):** the Active table's top High item is now
Foster's Theorem Phase A (`spectral-graph-sparsification.md`) — its
recorded scoping spike (the pseudoinverse-free statement shape:
eigenbasis expansion + the proved one-dimensional kernel
characterization) is the natural first run; or decidable-certificates
Step 0 (convention decision + ℚ-`decide` spike, both scoped in its
proposal). The operator's Medium/Low rows are preserved untouched.

**Electrical-flow routing, step 4 — Rayleigh monotonicity in conductance
form (run 1, 2026-08-19): DELIVERED.** The Active priority table's top
High item `proposals/electrical-flow-routing.md`, at its recorded next
step: entrywise `A ≤ B` ⇒ `effectiveResistance B u v ≤
effectiveResistance A u v` for connected symmetric nonnegative networks,
zero new axioms (count stays 13). The first *network-comparison* theorem
in the center (it relates two graphs, not two objects of one graph) and
the proposal's named ICP-facing fact — adding capacity cannot worsen the
certified energy cost of electrical routing.

**Delivered** in `GraphTheory.ElectricalFlow` (3 new declarations, all
proved): `isFlowOn_of_le` (flow-space growth — a flow supported on `A`
is a flow on every entrywise larger `B ≥ A ≥ 0`; support load-bearing: a
`B`-zero entry above a nonnegative `A` entry squeezes the latter to
zero), `flowEnergy_le_of_le` (raising conductances lowers dissipated
energy, termwise `θ²/B ≤ θ²/A`; support load-bearing a second time on
the `A i j = 0 < B i j` branch — the zero-conductance trap now guarding
the comparison), and the headline `effectiveResistance_le_of_le` —
exactly the proposed route: the `A`-unit-demand potential's current is a
unit flow *on `B`* (growth + Kirchhoff bridge), Thomson (step 3) on `B`
bounds `R_B` by its `B`-energy, the comparison bounds that by its
`A`-energy, and the step-2 identity evaluates it as `R_A`. Load-bearing
on solvability, the Kirchhoff bridge, support, Thomson, and the energy
identity — an error in any breaks the proof. Connectivity of both graphs
hypothesized per the proposal's initial-shape instruction; the optional
`supportGraph B`-from-`A` adapter deliberately not attempted (kept
non-blocking; noted for step 5 if its reinforcement shape wants a
one-hypothesis form).

**QA** `SpectralGraph/ElectricalFlow_QA.lean` (+20 declarations, 79 in
file): the proposal's QA item 2 — conductance `1 → 2` on the unit edge,
resistance certified to decrease `1 → 1/2` from an independent potential
witness, monotonicity instantiated, decrease certified strict, and the
**orientation guard** (reverse inequality `1 ≤ 1/2` refuted numerically —
weights are conductances; a resistance-direction statement would be false
here, exactly the statement bug the proposal's calibration names); the
competitor transfer instantiated on computed objects (the `edgeAdj`-current
is a unit flow on `edge2Adj`; cross-network energy `1/2 ≤ 1` computed from
the raw definitions on both sides); and a partial increase on the triangle
(one edge's conductance doubled: `2/3 → 2/5` strict, new value pinned by
the independent potential `![2/5, 0, 1/5]`).

**Verification:** `lake env lean` on both changed modules — zero errors,
zero warnings; `lake build` of both targets ✔; all twenty-eight QA
modules batch-elaborated, zero errors (only the documented pre-existing
linter notes in untouched modules); full `lake build` ✔ (2180 targets);
`lint_axioms` (13), `check_citations`, `check_markdown_links` pass;
scoreboard regeneration idempotent (563/13/0). Environment: the pruned
Mathlib-oleans state recurred at run start; the recorded interpreted
cache fetch restored all 5685 before the checks.

**Records updated:** module/QA docstrings, scoreboard (563/13/0,
verification rows, step-4 milestone bullet), radar (subject axis 6
re-scored **3.5 → 4.0** per the step-3 recorded reservation — Thomson
and Rayleigh have both now landed; QA count 563/28 with the step-4 kind;
proved-depth text; weakest-axes paragraph), README (counts + axis-6 cell
4.0 + last-assessed date), SGT index map (3 new rows; section header to
steps 0–4), backlog item 7 (the stale "deferred Rayleigh" note corrected:
the conductance-form theorem is delivered via the flow route; only the
Dirichlet-principle *route* remains deferred), proposal step-4 delivery
record (+ the adapter note), and `proposals/README.md` progress note.

**Next milestone (open):** proposal step 5 — the ICP capacity-reinforcement
example (`effectiveResistance (increaseConductance A i j δ) u v ≤
effectiveResistance A u v` on a small `SimpleGraph.toWAdj` or weighted
fixture, short enough for release documentation; a packaging of step 4,
not new mathematics — the proposal's final step, after which the
electrical-flow program is complete). Or the other High items: Foster
Phase A (needs its pseudoinverse-free statement-shape spike) or
decidable-certificates Step 0 (convention decision + ℚ-`decide` spike,
both scoped in its proposal). The operator's concurrently added Medium
rows (Reversibility Phase A, Relative Entropy) and the icebox additions
are indexed by the operator in the priority table and preserved
untouched.

## Superseded milestones (historical)

**Citation hygiene and broad-SGT reorientation.** The projector algebra is
proved in the center. The persistence package is retained as an existing
compatibility/example result, not a roadmap goal. The citation-hygiene
audit items below were completed on 2026-08-17 (see Last verified state):

1. **False provenance note (found by audit):** the Chung index claimed
   earlier revisions recorded page-level locators "Theorem 2.1 p. 42,
   Theorem 2.2 p. 44". Git history contradicted this: the initial commit
   cited only "Theorem 2.2" without a page, and no pre-rebuild index file
   exists. The note now records the accurate history; theorem and page
   numbering stay explicitly unconfirmed against the printed text (no
   local copy; page numbers were not invented).
2. **Weyl citation fidelity:** `weyl_inequality`'s doc now records that
   its Lean form is the spectral-norm corollary of the cited general Weyl
   inequality (obtained by combining the additive bound with
   `λ₁(E) ≤ ‖E‖` and `λₙ(E) ≥ -‖E‖`).
3. **Davis–Kahan hypothesis tightening:** the separation hypothesis is
   now the binding single-pair two-cluster form
   `λ_{k+1}(A+E) - λ_k(A) ≥ δ` (the form used by the cited
   Yu–Wang–Samworth Theorem 2); the derived wrapper simplified to one
   Weyl fact at the gap index, and the QA reduces the pairwise form via
   `evals_sorted`.

**Hard-crust conversion (same module):** `spectral_gap_stability` is now
a theorem proved from `weyl_inequality` (Weyl at both gap endpoints plus
arithmetic), reducing the explicit axiom count 19 → 18 with identical
statement shape (no consumer changes).

**Leverage delivered:** a false provenance claim removed from the
human-review surface; two axiom statements aligned with their sources;
the mushy center shrunk at zero trust cost.

**Next action:** with citation hygiene closed, the next milestone is the
broad-SGT backlog (ready queue item 1) — **delivered on 2026-08-17**:
(a) `docs/6_SGT_BACKLOG.md`, the bounded center-first backlog ranked by
concrete reuse (random-walk/Markov interfaces; irregular normalized
adapters; expansion/cut interfaces; spectral algorithms; conditional
dynamics and statistical-mechanics items), each naming consumers and
dependency paths, linked from the README canonical-docs list; and (b) its
top-ranked item implemented: `Scaffold.Mathlib.GraphTheory.RandomWalk`
— `transitionMatrix`, proved row-stochasticity for `d`-regular graphs,
`randomWalkLaplacian`, and proved bridges to both existing worlds
(`= regularNormalizedLaplacian`; `= d⁻¹ • laplacian`). Pure hard crust,
no new axioms; QA `SpectralGraph/RandomWalk_QA.lean` with a concrete
two-vertex instantiation. Umbrella, scoreboard, and SGT index map
updated.

**Next milestone:** backlog item 2, remainder — the irregular walk form —
**delivered on 2026-08-17 (run 8)**. Evidence check first: the walk
Laplacian `I − D⁻¹A` is *not symmetric* for irregular graphs, so
Scaffold's `evals` does not apply to it, and the deferred eigenvalue
transfer would need a charpoly-roots interface absent from the pinned
Mathlib. Delivered in `GraphTheory.Normalized` (all proved): general
`walkTransitionMatrix` (`D⁻¹A`) with `walkTransitionMatrix_row_sum`
(row-stochasticity under positive degrees — the named Markov consumer),
`walkLaplacian`, and the similarity identity
`degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt`
(`√D · L_walk · (1/√D) = L_sym`), with the eigenvalue-list transfer
recorded as the precisely named residual gap in the backlog. QA extended
at the 3-vertex path (row distributions, walk entries `1/2`/`1`, and the
similarity identity instantiated entrywise).

**Next milestone (open):** backlog item 3 — expansion and cut interfaces
(edge-boundary and uniform-weight conductance variants), each admitted
only with a named algorithm consumer.

**Active slice (run 10, 2026-08-17): cut duality — delivered.** The
existing cut surface (`vol`, `boundary`, `conductance`,
`cheegerConstant`) had nonnegativity but not the duality facts that
every cut-consuming algorithm assumes. Delivered in
`GraphTheory.Spectral` (all proved, no axioms): `vol_compl`
(`vol S + vol Sᶜ = vol univ`), `boundary_compl` (`boundary S =
boundary Sᶜ` for symmetric `A`, via `Finset.sum_comm` + symmetry),
`conductance_compl` (`conductance S = conductance Sᶜ` — Cheeger
minimizer canonicalization; the sweep-cut consumer interface),
`boundary_empty`/`boundary_univ` (degenerate-cut guards). QA at the
3-vertex path (`SpectralGraph/Cuts_QA.lean`, 11 declarations):
singleton boundary computes to `1`, duality and conductance invariance
instantiate, volume complementarity totals `4`, guards evaluate.
Backlog item 3's "Have" list updated.

**Next slice (open):** remaining backlog item 3 variants — edge-boundary
and uniform-weight conductance — each to be admitted only with a named
algorithm consumer; or backlog item 4 gating review.

**Active milestone (run 1, 2026-08-17): SGT coverage radar (operator
direction) — delivered.** `docs/7_SGT_RADAR.md` published with both
radars scored strictly from repository evidence (every score cites
declarations with proved/admitted/absent status): subject — models 2.5,
spectral algebra 3.5, variational 2.5, cuts/expansion 2.5, walks 2.5,
electrical **0.5** (entirely absent), perturbation/randomness 3.0,
adjacent systems 1.0; assurance — proved depth 3.5, axiom minimization
3.5, Mathlib interop 3.5, QA 3.0, citation fidelity 3.5, downstream
reuse **2.5** (RandomWalk/Normalized unconsumed). Includes a
re-scoring protocol (scores move only with usable, verified coverage,
recorded with the causing milestone). Backlog gains the radar-driven
gated candidate (item 7, electrical structure) and a downstream-reuse
standing decision; README canonical-docs list links the radar. No Lean
changes; hygiene suite passes.

**Next milestone (radar-driven): first downstream consumer for the
walk/normalized interfaces — delivered (run 2, 2026-08-17).** New
`Scaffold.Mathlib.GraphTheory.Stationary` (imports `Normalized`; all
proved, no axioms): `mulVec_one_eq_deg` (`A *ᵥ 1 = deg`),
`normalizedLaplacian_mulVec_sqrtDeg_eq_zero` (kernel of `L_sym` is
`√deg` — the normalized counterpart of `laplacian_ones_in_kernel`),
and `walkTransitionMatrix_transpose_mulVec_deg` (`Pᵀ *ᵥ deg = deg`:
the degree measure is stationary for the walk, `π ∝ deg` — the named
Markov-mixing consumer interface). QA
`SpectralGraph/Stationary_QA.lean` (6 declarations) at the 3-vertex
path. Radar: downstream reuse re-scored 2.5 → 3.0 with this milestone
recorded (protocol followed); remaining reuse gap: `RandomWalk`'s
regular-case bridges.

**Next milestone (open):** a consumer for `RandomWalk`'s regular
bridges — **delivered (run 3, 2026-08-17).** Evidence-based scoping:
the λ-transfer consumer needs `evals (c • M) = c • evals M`, but
Mathlib's `eigenvalues` is `irreducible_def` behind the eigenspace
decomposition — recorded as a named backlog candidate rather than
attempted. Delivered instead: `GraphTheory.Stationary` extended with
the walk-Laplacian kernel facts —
`randomWalkLaplacian_mulVec_one_eq_zero` (regular; consumes
`RandomWalk.transitionMatrix_row_sum`) and
`walkLaplacian_mulVec_one_eq_zero` (irregular; consumes
`Normalized.walkTransitionMatrix_row_sum`) — conservation of mass,
`(I − P) *ᵥ 1 = 0`, the base statement of diffusion/mixing arguments.
`Stationary` is now the demonstrated consumer of *both* interface
modules. QA at the regular edge and the irregular path. Radar: reuse
re-scored 3.0 → 3.5 (recorded); the constraint is now breadth of
reuse, and QA (3.0, degenerate-case skew) is the weakest assurance
axis.

**Next milestone (superseded — QA lever delivered below):** breadth
consumers for the walk/normalized interfaces (second consuming module —
e.g. variational Rayleigh bounds through the congruence bridge), or the
QA-assurance lever (property-based/falsification QA — delivered as the
run 1 slice below), or remaining backlog item 3 variants with named
consumers.

**Active slice (run 1, 2026-08-17): exhaustive/falsification QA for the
SGT center — delivered.** The QA axis was the weakest assurance axis
(3.0): existing QA instantiated theorems at one or two cuts and mostly
*applied* the general theorem (e.g. `path_boundary_compl_QA` rewrites
with `boundary_compl`), so a mis-defined `boundary`/`vol`/`conductance`
self-consistent with its own theorem family would not be caught.
Delivered `Scaffold/QA/SpectralGraph/Exhaustive_QA.lean` (87
declarations, hard crust, no axiom changes): (a) kernel-checked
exhaustive enumeration of **all** cuts of the 3-vertex path and the
4-cycle (`Finset.univ.powerset` equality by `decide` — `cuts3_eq`,
`cuts4_eq`), with `boundary`/`vol` values computed from the definitions
against hand-expected numbers; (b) duality recomposed from the
independently computed tables (`exh_boundary_duality_QA`,
`cyc_boundary_duality_QA`, `exh_vol_complementarity_QA`); (c) negative
witnesses — conductance separates adjacent-pair (`1/2`) from
opposite-pair (`1`) cuts on the cycle, Rayleigh separates `8/3` from
`0` on the path, and an asymmetric two-vertex weight shows
`boundary_compl`'s symmetry hypothesis is load-bearing (`2 ≠ 1`);
(d) walk row-stochasticity computed per row, independently of
`walkTransitionMatrix_row_sum`. Implementation note: `degreeMatrix`'s
diagonal conditional elaborates with a classical `Decidable` instance
(defined at generic `V`), so the Rayleigh checks compose the proved
Dirichlet identity and kernel theorem — the *values* are still fully
computed. Radar: QA re-scored 3.0 → 3.5 (recorded per protocol).

**Next milestone (delivered as the run 2 slice below):** breadth
consumers for the walk/normalized interfaces (second consuming module
— variational Rayleigh bounds through the congruence bridge). The
`evals (c • M) = c • evals M` Mathlib-excavation candidate and
backlog item 3 variants remain open.

**Active slice (run 2, 2026-08-17): variational transfer through the
congruence bridge — delivered.** The named breadth consumer from the
open milestone. Delivered
`Scaffold.Mathlib.GraphTheory.VariationalTransfer` (7 declarations,
all proved, no new axioms) plus QA
`SpectralGraph/VariationalTransfer_QA.lean` (15 declarations at the
3-vertex path): the generic congruence lemma
`quadForm (P M P) y = quadForm M (P *ᵥ y)` for symmetric `P`; the
Dirichlet-form transfer `yᵀ L y = (√D y)ᵀ L_sym (√D y)` consuming the
proved congruence; entrywise `√D *ᵥ y`; the degree-weighted
denominator `⬝(√D y, √D y) = ∑ deg i · y i²`; the headline
`rayleigh L_sym (√D y) = (yᵀ L y) / ∑ deg i · y i²` — the
irregular-graph normalized Rayleigh quotient the regular-only Cheeger
axioms cannot express; and `normalizedLaplacian_psd` transferred from
`laplacian_psd`. QA computes the classical value: at the path's
alternating vector, `8 / 4 = 2` — the largest eigenvalue of the
normalized path Laplacian, obtained without any spectral theorem.
`VariationalTransfer` is now the second consuming module of the
`Normalized`/`Spectral` interfaces (after `Stationary`). Radar:
downstream reuse 3.5 → 4.0, subject axis 3 (variational) 2.5 → 3.0,
both recorded per protocol. Umbrella and SGT index map updated.

**Next milestone (open):** the named `evals (c • M) = c • evals M`
Mathlib-excavation candidate (would connect `RandomWalk`'s regular
bridges to spectral statements); an irregular Cheeger statement shape
expressed through `rayleigh_normalizedLaplacian_degreeSqrt` (its
consumer interface is now available); or backlog item 3 variants with
named consumers.

**Decision milestone (run 9, 2026-08-17): `spectral_persistence`
deprecated — decision closed.** Consumer inventory (grep evidence): the
axiom had zero non-QA consumers — the derived layer mentioned it only in
a comment; its only use was the QA deliberately exercising the
compatibility surface; the derived two-endpoint chain
(`eventStreamProjectorDrift`/`davisKahanTwoPoint`) covers the motivating
persistence use. Per the architecture §9 lifecycle: `@[deprecated]` with
a migration note (probe-verified to apply to `axiom` declarations),
retained through the compatibility window — removal is a later release
decision, so the explicit axiom count remains 18 until then. The QA
exercises the deprecated surface with the linter silenced for that use
only. Indexes/docs updated (davis_kahan source, SGT/perturbation maps,
backlog standing decision, architecture debt, scoreboard). Bonus hygiene
in the same run: the derived module's use of Mathlib's deprecated
`div_lt_div_iff` upgraded to `div_lt_div_iff₀`; the full build now
carries zero deprecation warnings.

**Active milestone (run 1, 2026-08-18): Cheeger axiom statement-shape
repair — delivered.** Evidence found while scoping the
`evals (c • M)` candidate: both admitted Cheeger axioms state their
spectral side as `lambda2 (regularNormalizedLaplacian A d) …`, but
`lambda2` is defined as `evals (laplacian …) 1` — it wraps its argument
in the *combinatorial* Laplacian. The stated RHS was therefore the
second-smallest eigenvalue of `L(L_sym)`, not of `L_sym` itself; since
every `L_sym` row sums to zero, `L(L_sym) = -L_sym`, and on the
two-vertex edge the old lower-bound instance asserted `1²/2 ≤ 0` —
materially false. The docstring, index map, and source citation all
described the intended statement `φ²/2 ≤ λ₂(L_sym) ≤ 2φ`; only the
Lean RHS was defective. Delivered: new proved center interface
`secondEval` (second sorted eigenvalue of a symmetric matrix) plus the
bridge `lambda2_eq_secondEval`; both axioms restated with the corrected
RHS at unchanged names and hypotheses (emergency repair per
architecture §9); QA gains a **refutation of the old shape on the edge
graph** (`old_cheeger_lower_bound_refuted_QA`, via the new
`eigvalOf_le_of_quadForm_nonpos` Rayleigh bound and `cheegerConstant =
1`), an independent **value pinning of the corrected RHS**
(`edge_normLap_secondEval_eq_two_QA`: `λ₂(L_sym) = 2` on `K₂` from the
new `eigvalOf_sum_eq_trace` + `det_eq_prod_eigenvalues` +
sortedness), and `cheeger_bounds_edge_QA` instantiates the corrected
sandwich on the fixture. New center hard crust: `secondEval`,
`lambda2_eq_secondEval`, `evals_mem_eigvalOf`,
`eigvalOf_le_of_quadForm_nonpos`, `eigvalOf_sum_eq_trace`. This is the
first computational eigenvalue QA in the tree — the radar QA axis's
named residual gap (re-scored 3.5 → 4.0 per protocol). Axiom count
unchanged (18). Verification: `lake env lean` on both changed modules
(zero errors/warnings); all nineteen QA modules and the changed public
modules built directly; full `lake build` (2161 targets); all hygiene
scripts pass; scoreboard, radar, and both Cheeger indexes updated with
the correction record.

**Next milestone (open):** the `evals (c • M) = c • evals M`
Mathlib-excavation candidate (would connect `RandomWalk`'s regular
bridges to spectral statements — note the new trace/Rayleigh/membership
tools reduce its cost); an irregular Cheeger statement shape through
`rayleigh_normalizedLaplacian_degreeSqrt` (needs a precise source and
consumer); or backlog item 3 variants with named consumers.

**Active slice (run 1, 2026-08-18): electrical-crust step 1 —
connectivity and the kernel characterization — DELIVERED.** Operator
direction pinned `proposals/electrical-structure-crust.md` **step 1
only**: for a connected weighted graph, `ker (laplacian A)` is exactly
the constants — the converse of `laplacian_ones_in_kernel`
(`Spectral.lean`). Pure hard crust; **no new axioms** (count unchanged
at 18). Proposal steps 2–5 (effective resistance, Rayleigh
monotonicity, Foster) were NOT started — stopping here with a clean
proof is the successful outcome.

**Connectivity predicate decision (recorded before stating anything):**
adopted Mathlib's `SimpleGraph.Connected` through a `WAdj → SimpleGraph`
adapter `supportGraph A hA` with `Adj i j ↔ i ≠ j ∧ 0 < A i j`. The
`i ≠ j` conjunct is forced by `SimpleGraph` looplessness — positive
diagonal weights (self-loops) cancel in `D − A` and so must not create
adjacency. Tradeoff vs a native reachability inductive over `WAdj`: a
native predicate would duplicate Mathlib's `Walk`/`Reachable` machinery
with no consumer of the duplicate, and later proposal steps (component
structure, spanning trees) would need a bridge to Mathlib anyway. The
adapter reuses Mathlib's walk induction for the propagation argument,
takes the anchor vertex from `Connected`'s bundled `Nonempty` field
(discharging the empty-vertex-type case for free), and is the first
`WAdj → SimpleGraph` bridge — movement on the radar's standing
matrix-first interop deviation and the prerequisite shape for the
proposal's second recommendation (`SimpleGraph.toWAdj`). Cost: two new
Mathlib imports in `Spectral.lean` (`Combinatorics.SimpleGraph.Path`
for `Walk`/`Reachable`/`Connected`, `LinearAlgebra.Matrix.ToLin` for
`mulVecLin`), mitigated by the `supportGraph_adj` interface lemma
(`Iff.rfl`).

**Delivered statements** (all proved, in `GraphTheory.Spectral`):
`supportGraph` + `supportGraph_adj`; edge constancy
`eq_of_laplacian_mulVec_eq_zero_of_pos_weight` (zero Dirichlet energy
kills `(f i − f j)²` termwise on positive weights, via
`laplacian_quadForm` + nonneg weights); walk propagation
`eq_of_supportGraph_walk` (induction on `SimpleGraph.Walk`);
connected ⇒ kernel ⊆ constants
`exists_const_of_laplacian_mulVec_eq_zero`; `laplacian_mulVec_const`;
the iff `laplacian_mulVec_eq_zero_iff_exists_const`; the algebraic
headline `laplacian_kernel_eq_span_onesVec`
(`LinearMap.ker (Matrix.mulVecLin (laplacian A)) = span ℝ {onesVec}`).
QA `SpectralGraph/Connectivity_QA.lean` (15 declarations): connected
positive witness (3-vertex path — support graph connected by explicit
walks through the center, both iff directions, constant recovered and
pinned to its value, non-constant `![1,0,0]` computed out of the
kernel) plus a disconnected negative witness (two disjoint `Fin 4`
edges — component indicator `![1,1,0,0]` computed into the kernel yet
not constant, support graph proved not connected via a block invariant
over walks), showing the connectivity hypothesis is load-bearing.
Radar re-scored per protocol with this milestone (proof + QA landed):
subject axis 6 (electrical) 0.5 → 1.0, subject axis 1 (models)
2.5 → 3.0, assurance Mathlib interop 3.5 → 4.0; QA axis text updated
to 255 declarations / 20 modules. Backlog item 7 records step 1
delivered with named consumers for step 2.

**Next milestone (open):** proposal step 2 — effective resistance by
the potential equation (`IsEffectiveResistance A u v r ↔ ∃ f,
laplacian A *ᵥ f = e u − e v ∧ f u − f v = r`), whose
well-definedness consumes `laplacian_kernel_eq_span_onesVec`; or the
still-open earlier candidates: the `evals (c • M) = c • evals M`
Mathlib-excavation, an irregular Cheeger statement shape through
`rayleigh_normalizedLaplacian_degreeSqrt` (needs a precise source and
consumer), or backlog item 3 variants with named consumers.

**Active slice (run 1, 2026-08-18): the `SimpleGraph → WAdj`
interoperability adapter — DELIVERED.** The proposal's re-sequenced
step 1 (its "highest compounding multiplier"), completing the
two-directional adapter surface begun with `supportGraph`. Delivered
`GraphTheory/SimpleGraphAdapter` (all proved, **no new axioms**, count
unchanged at 18): `SimpleGraph.toWAdj` (defined as Mathlib
`adjMatrix ℝ` — no parallel matrix to drift), `toWAdj_apply`,
`toWAdj_symm`, `toWAdj_nonneg`; agreement family `deg_toWAdj`,
`vol_toWAdj_eq_sum_degrees`, handshake
`vol_toWAdj_univ_eq_two_mul_card_edges` (from Mathlib's degree-sum
formula), headline `laplacian G.toWAdj = G.lapMatrix ℝ`,
`boundary_toWAdj_eq_sum_neighbors` /
`boundary_toWAdj_eq_sum_card_neighbors` (crossing-edge count, each
crossing edge counted once); neutral re-exports
`laplacian_toWAdj_mulVec_eq_zero_iff_reachable` and
`finrank_ker_laplacian_toWAdj`; roundtrip
`supportGraph_toWAdj_eq_self` and connected-`G` corollary
`laplacian_toWAdj_kernel_eq_span_ones` (the delivered span theorem
applied to Mathlib graphs). QA
`SpectralGraph/SimpleGraphAdapter_QA.lean` (38 declarations): at the
3-vertex path, weights/degrees/Laplacian entries/both Laplacian
sides/boundary/handshake/kernel membership computed against
hand-expected numbers; disconnected `Fin 4` negative witness with the
component indicator computed *into* the kernel yet the kernel proved ≠
`span {onesVec}` (`twoEdge_kernel_ne_span_QA`) — connectivity is
load-bearing through the adapter. Umbrella, scoreboard (293 QA
declarations, 21 modules), SGT index map, backlog item 7, and radar
updated; radar re-scored per protocol after proof + QA landed: Mathlib
interop 4.0 → 4.5 (both directions, proved roundtrip, Mathlib
kernel/component results transferred), subject axis 1 (models)
3.0 → 3.5; README snapshot cell synced.

**Environment note (recorded):** the local `.lake/build` state was
found pruned at run start (Mathlib oleans down to 1795/5685, including
the modules this slice needs). The recorded interpreter-based cache
fetch (`lake env lean --run Cache/Main.lean get` from the mathlib
package) restored all 5685; `lake build` then recompiled the 2008
-target residue (~35 min) before the normal checks. Scoreboard
provenance note updated.

**Next milestone (open):** proposal step 3 — the kernel-equality
bridge `ker (laplacian A) = ker ((supportGraph A).lapMatrix ℝ)`,
inheriting Mathlib's `lapMatrix_ker_basis` and
`card_ConnectedComponent_eq_rank_ker_lapMatrix` for the *weighted*
Laplacian (the delivered `finrank_ker_laplacian_toWAdj` covers only
0/1 weights); then step 4 (potential solvability, the hinge — the
proposal forbids defining effective resistance before it). Or the
still-open earlier candidates: the `evals (c • M) = c • evals M`
Mathlib-excavation, an irregular Cheeger statement shape through
`rayleigh_normalizedLaplacian_degreeSqrt` (needs a precise source and
consumer), or backlog item 3 variants with named consumers.

**Active slice (run 1, 2026-08-18): electrical-crust step 3 — the
kernel-equality bridge — DELIVERED.** Operator direction: proposal
step 3 only; one step per run; step 4 not started. All proved, **no
new axioms** (count unchanged at 18).

**Delivered center facts** (`GraphTheory.Spectral`): the diffusion-form
identity `laplacian_mulVec_apply` (`(L *ᵥ f) i = ∑ j, A i j (f i − f
j)`; self-loop weights cancel — honest w.r.t. `supportGraph`'s
looplessness), `laplacian_mulVec_eq_zero_of_forall_reachable`
(component-constant ⇒ kernel, entrywise; **no connectivity
hypothesis**), and the component-form characterization
`laplacian_mulVec_eq_zero_iff_forall_reachable` — the weighted
counterpart of Mathlib's unweighted iff, generalizing step 2's
connected statement to disconnected graphs.

**Delivered bridge + inheritances**
(`GraphTheory.SimpleGraphAdapter`): the headline
`ker_laplacian_eq_ker_supportGraph_lapMatrix` (`ker (laplacian A) =
ker ((supportGraph A).lapMatrix ℝ)` — weights do not change the
kernel; both sides are the component-constant vectors, so the proof is
the two iff's composed),
`finrank_ker_laplacian_eq_card_supportGraph_components` (kernel
dimension = component count for *weighted* graphs — Mathlib's rank
theorem inherited; the delivered `finrank_ker_laplacian_toWAdj`
covered only 0/1 weights), and the transported component-indicator
basis `laplacian_ker_basis` + value interface
`laplacian_ker_basis_apply` (Mathlib's `lapMatrix_ker_basis` via
`Basis.map`/`LinearEquiv.ofEq`). One unforeseen prerequisite,
recorded in the proposal: Mathlib's `lapMatrix` API needs
`DecidableRel G.Adj`, invisible through the `supportGraph` projection
— discharged once as `supportGraphAdjDecidable` (`Real.decidableLT`).

**QA** `SpectralGraph/KernelBridge_QA.lean` (14 declarations, reusing
the `Connectivity_QA` fixtures): connected 3-path — bridge
instantiates, component count `1`, dimension `1`, basis vector
constantly `1`, all simultaneous with the connected span theorem (a
mis-stated bridge would contradict it); disconnected two-edge fixture
— component count computed to `2` **independently of the transferred
theorem** (block classification + `Nat.card_eq_two_iff`), dimension
`2`, basis vectors computed to `![1,1,0,0]`/`![0,0,1,1]`, kernel
strictly larger than the constants (connectivity load-bearing).
Radar re-scored per protocol (proof + QA landed): subject axis 6
(electrical) 1.0 → 1.5 — weighted component structure complete; the
score stays below 2.0 because no electrical quantity (resistance,
Matrix–Tree, Kirchhoff) is defined yet. Umbrella, scoreboard (307 QA
declarations, 22 modules), SGT index map, backlog item 7, and
proposal checklist updated.

**Active slice (run 1, 2026-08-18): electrical-crust step 4 — potential
solvability, the hinge — DELIVERED.** Operator direction pinned
`proposals/electrical-structure-crust.md` **step 4 only**; steps 5–6
were NOT started — landing the hinge cleanly is the successful
outcome. All proved, **no new axioms** (count unchanged at 18).

**Route decision (recorded before stating, per the proposal):** the
**constructive eigenbasis** route was taken. Survey (this run): the pin
still has no ready-made `range L = (ker L)ᗮ` lemma over these function
types; the center's proved eigenbasis tools are exactly sufficient.

**Delivered center declarations** (`GraphTheory.Spectral`):
`laplacian_dotProduct_mulVec` (reciprocity `w ⬝ᵥ (L *ᵥ f) = (L *ᵥ w) ⬝ᵥ
f`, from `Matrix.dotProduct_mulVec` + symmetry), the kernel certificate
`dotProduct_eq_zero_of_laplacian_mulVec_eq_zero` (unsolvability
witnesses), `mulVec_eigvecOf_sum_apply` (entrywise action on
eigenbasis combinations) and `exists_mulVec_eq_of_zero_comp`
(constructive spectral inversion `f = ∑_{λᵢ ≠ 0} (vᵢ ⬝ᵥ b/λᵢ) • vᵢ` —
the load-bearing consumer of the eigenbasis algebra), the headline
`exists_laplacian_mulVec_eq_of_sum_eq_zero` (zero-sum ⇒ solvable on
connected graphs; the zero-eigenvalue components of `b` die through
`laplacian_kernel_eq_span_onesVec`, step 2's theorem), and the
specialization `exists_laplacian_mulVec_eq_single_sub_single` (unit
demand `e u − e v` solvable — step 5's defining equation).

**QA** `SpectralGraph/PotentialSolvability_QA.lean` (12 declarations,
reusing `Connectivity_QA` fixtures + a new two-vertex edge fixture):
computed potentials on the edge (`L *ᵥ ![1,0] = e₀ − e₁`) and the
3-path (`L *ᵥ ![1,0,−1] = e₀ − e₂`, the vector is fixed by its own
Laplacian); theorem instantiations (unit-demand and a general
alternating zero-sum demand); and **proved unsolvability** witnesses —
demand `e₀` (sum `1`) has no solution on the connected edge (via the
all-ones kernel certificate), and the zero-sum cross-component demand
`e₀ − e₂` has no solution on the disconnected fixture (via the
component-indicator kernel certificate) — both hypotheses shown
load-bearing, exactly per the proposal's step-4 witness spec. Radar
re-scored per protocol (proof + QA landed): subject axis 6 (electrical)
1.5 → 2.0 — the potential equation is now *completely characterized*
on connected graphs; the axis stays modest because no electrical
quantity is defined yet. Umbrella, scoreboard (319 QA declarations, 23
modules), SGT index map, backlog item 7, README snapshot, and proposal
checklist updated.

**Active slice (run 1, 2026-08-18): electrical-crust step 5 —
effective resistance, uniqueness, and energy — DELIVERED.** Operator
direction pinned `proposals/electrical-structure-crust.md` **step 5
only**; step 6 (the one-sided Dirichlet bound) was NOT started; one
step per run. All proved, **no new axioms** (count unchanged at 18).
Both authorized halves (definitional plumbing and the energy identity)
landed in one run.

**Mathlib survey (recorded before stating, per the proposal):** no
effective-resistance or "resistance" declaration anywhere in the pin;
no Moore–Penrose pseudoinverse — the potential-equation definition is
the only available route (and the intended one).

**Delivered** in the new `Scaffold/Mathlib/GraphTheory.Electrical`
(17 declarations, all proved; keeps `Spectral.lean` bounded): the
relation `IsEffectiveResistance A u v r` (`∃ f, L *ᵥ f = e u − e v ∧
f u − f v = r`); `exists_isEffectiveResistance` (existence, consuming
step 4's `exists_laplacian_mulVec_eq_single_sub_single`);
`isEffectiveResistance_unique_of_reachable` (uniqueness of `r` stated
at **reachability-pair strength** via step 3's component-form
characterization — valid within a component of a disconnected graph,
strictly stronger than the proposal's connected sketch) with the
connected corollary; the total function `effectiveResistance A u v : ℝ`
by classical choice, junk fallback `0` **stated, not hidden**
(`effectiveResistance_eq_zero_of_not_exists`) and QA-witnessed;
agreement `effectiveResistance_eq_of_reachable` /
`effectiveResistance_eq`; the energy identity at solution level —
`quadForm (laplacian A) f = f u − f v` for *any* solution, **no
hypotheses** (definitional unfolding of `quadForm` plus
`Matrix.dotProduct_single`) — and at function level
(`effectiveResistance_eq_quadForm`: `R u v = energy of an actual
potential`); `effectiveResistance_nonneg` (from `laplacian_psd` through
the energy identity); `effectiveResistance_symm` (relation-level
symmetry is hypothesis-free: negate the potential;
`isEffectiveResistance_symm`); `isEffectiveResistance_self_iff`
(diagonal characterized exactly, no hypotheses) and unconditional
`effectiveResistance_self`.

**QA** `SpectralGraph/EffectiveResistance_QA.lean` (17 declarations,
reusing the `Connectivity_QA`/`PotentialSolvability_QA` fixtures):
values computed from the definitions — unit edge `R 0 1 = 1` (witness
`![1,0]`), 3-path `R 0 2 = 2` (witness `![1,0,−1]`; series edges add);
the energy identity cross-checked against an energy computed
independently from the raw definitions; the junk fallback pinned on
the disconnected fixture (cross-component pair: no value exists —
proved from the step-4 unsolvability witness — while the function
reads `0`: fallback, not measurement); and same-component witnesses —
two *distinct* potentials `![1,0,0,0]`/`![2,1,0,0]` both witnessing
`r = 1` between `0` and `1`, with the reachability-form agreement
pinning `effectiveResistance 0 1 = 1` where the connected-graph
theorem's hypothesis fails (uniqueness is about `r`, not `f`; a
two-dimensional kernel does not break the value).

**Named residual (cheap, deferred by the scope fence):**
definiteness — `R u v = 0 ↔ u = v` on a reachable pair.

Radar re-scored per protocol (proof + QA landed): subject axis 6
(electrical) 2.0 → 2.5 — the first electrical quantity, with its full
well-definedness package; below 3.0 because the variational Dirichlet
bound, Rayleigh monotonicity, the resistance metric, and
Matrix–Tree/Kirchhoff remain absent. Umbrella, scoreboard (336 QA
declarations, 24 modules), SGT index map, backlog item 7, README
snapshot, and proposal checklist updated.

**Active slice (run 1, 2026-08-18): electrical-crust step 6 — the
one-sided Dirichlet bound — DELIVERED.** Operator direction pinned
`proposals/electrical-structure-crust.md` **step 6 only**; the named
cheap residual (`R u v = 0 ↔ u = v`) was NOT started — one step per
run; with this step the proposal's program is **complete** (steps 1–6,
axiom count 18 throughout).

**Mathlib survey (recorded before proving, per the proposal):** the
pin's only Cauchy–Schwarz is the *definite* inner-product-space one
(`Analysis/InnerProductSpace/Basic.lean`); the Laplacian energy form is
merely semidefinite (constants have zero energy), so it is unusable
without first quotienting out the kernel; no `QuadraticForm` C–S exists
at these function types. **Route taken (recorded before stating):**
polarization of the PSD energy, in three proved layers.

**Delivered** in `GraphTheory.Electrical` (4 new declarations, all
proved, no axioms): `sq_le_mul_of_forall_zero_le_sub` (algebra core: a
real quadratic nonnegative everywhere has nonpositive discriminant
`c² ≤ Q·E`; minimum at `t = c/E`, degenerate `E = 0` forces `c = 0`);
`quadForm_laplacian_sub_smul` (polarization `quadForm L (f − t • g) =
quadForm L f − 2t·(f ⬝ᵥ L g) + t²·quadForm L g`; the mixed terms agree
through the proved reciprocity `laplacian_dotProduct_mulVec`);
`laplacian_cauchy_schwarz` (`(f ⬝ᵥ L g)² ≤ quadForm L f · quadForm L
g`, **no connectivity hypothesis** — reusable beyond resistance); and
the headline `effectiveResistance_ge_sq_div_quadForm`
(`(f u − f v)² / quadForm L f ≤ effectiveResistance A u v` for any test
potential of positive energy, division guarded per architecture §4).
The headline is load-bearing on the whole chain: its cross term is
`f u − f v` *through the step-4 demand potential*, its energy is `R u
v` *through the step-5 energy identity*, and its C–S is `laplacian_psd`
— an error in any of those breaks this proof rather than passing beside
it. No attained supremum is used (the reverse direction is the deferred
Dirichlet principle).

**QA** `SpectralGraph/EffectiveResistance_QA.lean` (+9 declarations,
345 total): equality *attained* at the harmonic potentials on both
connected fixtures (edge `1²/1 = 1`, path `4/2 = 2`; energies computed
independently from the raw definitions — `edge_energy_e0_QA`,
`path_energy_e00_QA` reuse `path_energy_value_QA`); *strictness* at the
non-harmonic `![1,0,0]` (`1 < 2`); a **negative witness** refuting the
reverse inequality numerically (`2 ≤ 1` false — the one-sided form is
forced; the upper direction genuinely needs the attained-supremum
principle the proposal keeps deferred); and the **`0 <` energy guard
witnessed load-bearing** on the disconnected fixture (component
indicator: zero energy — kernel membership — with voltage difference
`1`, so an unguarded bound would read junk `1/0 = 0 ≤ 0` on both
sides).

Radar re-scored per protocol (proof + QA landed): subject axis 6
(electrical) 2.5 → 3.0 — the first variational/electrical inequality
on the axis; below 3.5 because full Rayleigh monotonicity, the
resistance metric, and Matrix–Tree/Kirchhoff remain absent (recorded
with the milestone). Radar QA-axis count synced to 345/24. Umbrella
unchanged (module already in it), scoreboard, SGT index map (4 new
`Electrical` rows), backlog item 7 (program complete; residual named),
README snapshot, and proposal checklist (all six steps ✅) updated.

**Active slice (run 1, 2026-08-18): retire `lambda2_variational` —
prove it in the matrix world, repairing a false statement shape —
DELIVERED.** Operator direction "advance
`proposals/prove-lambda2-variational.md`". **Finding (recorded before
stating anything):** the axiom as admitted was *materially false* — it
assumed only symmetry, but on `Fin 2` with `A = [[0,−1],[−1,0]]` the
Laplacian `[[−1,1],[1,−1]]` has sorted spectrum `[−2, 0]`, so
`lambda2 = 0` while every `x ⊥ onesVec` is a multiple of `(1,−1)` with
Rayleigh quotient `−2`; the axiom would assert `0 = −2`. Same defect
class as the 2026-08-18 Cheeger repair. **Delivered:** the axiom is now
a proved theorem at the same name with the load-bearing hypothesis
`hnonneg : ∀ i j, 0 ≤ A i j` added (matching `laplacian_psd`;
emergency repair per architecture §9); explicit axiom count 18 → 17.

**Route decision (recorded before proving):** the proposal's open next
step was to spike the `Matrix.IsHermitian ↔ LinearMap.IsSymmetric`
bridge (operator route through `Rayleigh.lean`, calibrated as several
sessions). Survey found a cheaper matrix-world route through the
repo's own proved eigenbasis tools; the LinearMap bridge was never
built. New proved hard crust in `GraphTheory.Spectral` (13
declarations): `eigvecOf_expansion_apply` (entrywise completeness,
factored out of and now reused by `exists_mulVec_eq_of_zero_comp`),
`dotProduct_eigvecOf` (Parseval), `dotProduct_eigvecOf_mulVec`
(self-adjointness in coordinates), `quadForm_eigvalOf` (spectral
resolution of the quadratic form), `quadForm_eigvecOf_self`,
`eigvecOf_ortho_onesVec` (nonzero-eigenvalue eigenvectors ⊥ `onesVec`,
symmetry only), the two **multiplicity pins** that make Courant–Fischer
provable without operator restriction — `evals_one_le_max_of_ne` (no
two distinct eigenbasis indices sit strictly below `evals 1`) and
`exists_ne_eigvalOf_of_evals_head_eq` (a repeated bottom entry comes
from two distinct indices) — and the headline `lambda2_variational`.
Lower bound: spectral resolution + the upper pin (the unique
below-λ₂ eigenvector is parallel to `onesVec`, invisible to the
constraint); upper bound: the eigenvector at `evals 1` when `λ₂ > 0`,
and a kernel vector ⊥ `onesVec` from the lower pin when `λ₂ = 0`
(the disconnected case). Load-bearing chain: resolution consumes
`eigvecOf_complete`; the unique-i₀ argument consumes
`laplacian_ones_in_kernel`; PSD consumes `laplacian_psd`.

**QA** `SpectralGraph/Variational_QA.lean` (+26 declarations, 371
total): the pre-repair shape **refuted in proved form**
(`old_lambda2_variational_refuted_QA`: `λ₂ = 0` from
trace/determinant/sortedness while the constraint set is exactly
`{−2}` by a parametric Rayleigh computation — `hnonneg` witnessed
load-bearing); `K₂` exact instantiation with `λ₂ = 2` computed **twice
independently** (sorted-spectrum pin; and *through* the theorem from
the parametric Rayleigh side — two routes that must agree); the
disconnected instantiation `λ₂ = 0` on two disjoint edges (kernel
witness `![1,1,−1,−1]` ⊥ `onesVec` + PSD floor); the path bound
`λ₂(P₃) ≤ 1` at the harmonic alternating vector.

**Scope caveat (recorded in the proposal):** the Cheeger proposal's
named intermediate is the *normalized* instance `secondEval L_sym`;
this delivery proves the combinatorial instance, from which the
normalized one follows via the proved congruence transfer — that
transfer step remains to be written.

Radar re-scored per protocol (proof + QA landed): subject axis 3
(variational) 3.0 → 3.5 — the row's named admitted gap closed by a
proved theorem; assurance axiom-minimization 3.5 → 4.0 — the first
axiom removed by proof rather than deprecation (net trend 26 → 19 →
18 → 17); proved-depth and QA text updated (QA count 371/24).
Umbrella unchanged, scoreboard, both source indexes (Chung §1.3,
Horn–Johnson §4.2 rows marked theorem), SGT index map, README
snapshot, and both proposals' status notes updated.

**Active slice (run 1, 2026-08-18): retire `cheeger_upper_bound` —
prove the Cheeger easy direction from a generalized Courant–Fischer —
DELIVERED.** Selected from `proposals/README.md`'s Active priority
table (top High item; Fiedler Phase A, the other High item, stays
queued and is the natural next run). Explicit axiom count **17 → 16**;
all new code proved, no new axioms, no consumer changes (the theorem
keeps the axiom's exact name, hypotheses, and statement).

**Route decision (recorded before proving, per the proposal):** the
named missing intermediate was built as a *generalization*, not a
transfer — the `lambda2_variational` Courant–Fischer argument was
lifted from `laplacian A` to any symmetric PSD matrix with
`M *ᵥ onesVec = 0` (`secondEval_variational`), so the normalized
instance needs **no eigenvalue-scaling lemma** (the
`evals (c • M)` excavation stays unnecessary): under `d`-regularity,
PSD of `L_sym` scales from `laplacian_psd` through the entrywise
identity `d • L_sym = laplacian A`, and the kernel fact is the row-sum
identity under `deg = d`.

**Delivered in `GraphTheory.Spectral`:** the generic
`eigvecOf_ortho_onesVec_of_mulVec_eq_zero` (the Laplacian instance
re-derives the existing `eigvecOf_ortho_onesVec` at unchanged shape);
`secondEval_variational` (full generalized body of the former
monolithic proof); `lambda2_variational` re-proved as a two-line
corollary at unchanged name/statement; the consumer form
`secondEval_le_rayleigh` (`secondEval ≤ R(x)` for every admissible
test vector — the interface test-vector arguments actually call).

**Delivered in `GraphTheory.Cheeger` (all proved):** the scaling
bridges (`quadForm_smul`, `smul_regularNormalizedLaplacian`,
`quadForm_regularNormalizedLaplacian`, `regularNormalizedLaplacian_psd`,
`regularNormalizedLaplacian_mulVec_onesVec`,
`vol_eq_of_regular`/`vol_pos_of_regular`); the volume-centered cut
indicator `cutTestVector` with its interface —
`cutTestVector_dotProduct_onesVec` (orthogonality under regularity),
`cutTestVector_ne_zero`,
`quadForm_laplacian_cutTestVector` (the general weighted-graph cut
energy identity `xᵀLx = boundary S · (vol V)²`, **no regularity
needed** — consumes `vol_compl`/`boundary_compl` cut duality),
`dotProduct_cutTestVector_self`, and
`rayleigh_regularNormalizedLaplacian_cutTestVector`
(`R(x) = boundary · vol V / (vol S · vol Sᶜ)`); the headline
`cheeger_upper_bound` as a theorem: per-cut bound
`λ₂ ≤ 2 · conductance S` (min ≤ both volumes), then `le_csInf` over
nonempty proper cuts. Load-bearing chain: the bound consumes the
variational engine, PSD scaling, the kernel fact, and cut duality — an
error in any breaks the proof.

**QA** `SpectralGraph/Cheeger_QA.lean` (+7 declarations, 378 total,
now importing `Exhaustive_QA` for the `C₄` tables): the test vector
pinned to `![1,-1]` on `K₂`; its Rayleigh value computed to `2` —
exactly the independently pinned `λ₂(L_sym)`
(`edge_normLap_secondEval_eq_two_QA`), so the test-vector bound is
*attained*; `cheeger_upper_bound_edge_eq_QA` proves the theorem's
bound attained on `K₂` as `λ₂ = 2φ` from independently computed
values; on `C₄`, `cutTestVector_cycle_rayleigh_QA` computes the
adjacent-pair test-vector Rayleigh value to exactly `1` and
`cheeger_upper_bound_cycle_le_QA` instantiates the theorem to
`λ₂ ≤ 1` through the exhaustively computed conductance `1/2`.

Docs updated: scoreboard (16/378/0, verification rows, milestone note),
radar (subject axis 4 re-scored 2.5 → 3.0 per protocol — the axis's
first inequality engine proved; axiom-minimization trend
26 → 19 → 18 → 17 → 16; QA count synced; proved-depth and reuse text),
both Cheeger indexes, backlog item 3, README snapshot, and
`proposals/README.md` (the proposal moved to Delivered with residuals
named: the irregular generalization — which *does* need the
congruence-transfer route since the engine's constraint is `onesVec`,
not `√deg` — and the proposal's two supporting moves).

**Next milestone (open):** the Fiedler proposal's Phase A (A1/A2) —
the remaining High item, scoped as close to free, and now composable
with the proved easy direction; or the residuals above; or the
`evals (c • M)` excavation.

**Active slice (run 1, 2026-08-18): audit and finish the uncommitted
normalized-Cheeger milestone — DELIVERED.** Operator direction (via
`scripts/finish-cheeger-milestone`): audit only the current uncommitted
Cheeger work — the `cheeger_upper_bound` retirement on the normalized
Laplacian (`secondEval (L_sym)`), whose hard-direction twin
(`cheeger_lower_bound`) correctly remains the sole admitted Cheeger
axiom — and finish it: no new mathematics, no new proposal, no commit.
Audit findings: (a) the Lean changes and record updates are present and
mutually consistent (16 axioms, 378 QA declarations, Cheeger QA 33,
README/scoreboard/radar/index/proposal rows all synced); (b) the
activity log's uncommitted diff had introduced exactly 6
trailing-whitespace lines — the Run/Session/Status metadata of its own
two newest entries (17:01/17:32Z) — now stripped; older committed
entries and the template's illustrative hard breaks are unrelated
records and were left untouched. Re-verification, all green: direct
elaboration (`lake env lean`) of `GraphTheory.Spectral`,
`GraphTheory.Cheeger`, and `QA.SpectralGraph.Cheeger_QA` — zero errors
(Cheeger QA zero warnings; the handful of linter notes elsewhere sit
in declarations verified present unchanged in HEAD, outside the diff
hunks); explicit `lake build` of the three targets ✔; `lint_axioms`,
`check_citations`, `check_markdown_links` pass; scoreboard
regeneration is byte-identical (no drift — 16/378/0 re-derived from
source); full `lake build` ✔ (2178 targets). Unrelated working-tree
changes preserved; nothing committed.

**Active slice (run 1, 2026-08-18): Fiedler Phase A — the vector and the
sign partition (proposal `fiedler-partitioning.md`, the remaining High
item at run start) — DELIVERED.** Hard crust, **no new axioms** (count
stays 16); Phase B is a separate later run and is explicitly
axiom-backed, not hard crust. Selected from `proposals/README.md`'s
Active priority table (top High item).

**A1 statement-shape decision (recorded before stating):** the
proposal's sketch `eigvecOf (laplacian A) hL ⟨1, by omega⟩` is
ill-typed — `eigvecOf` is indexed by `V` (the eigenbasis listing), not
by sorted-spectrum positions. Delivered instead: `fiedlerIndex` (the
eigenbasis index carrying `lambda2`, fixed by classical choice through
`evals_mem_eigvalOf`) with the interface lemma `fiedlerIndex_eigvalOf`,
and `fiedlerVector` = the eigenvector there. Delivered A1 theorems:
`fiedlerVector_eigen` (the eigenvector equation — the statement every
consumer starts from), `fiedlerVector_norm`/`fiedlerVector_ne_zero`
(unit norm from the orthonormal basis), `fiedlerVector_quadForm`
(Fiedler energy = `lambda2`), `fiedlerVector_ortho_onesVec` and the
sum form `fiedlerVector_sum_eq_zero` (under `0 < lambda2`).

**A2 plus the named load-bearing dependency:** the connectivity
hypothesis's content is exactly `lambda2 > 0`, and that implication is
now itself a theorem — `lambda2_pos_of_connected` (connected + symmetric
nonnegative weights ⇒ `0 < lambda2`; the algebraic-connectivity
certificate). Route: PSD bounds every eigenbasis eigenvalue, a
nonpositive `lambda2` pins the first two sorted entries to `0`, the
lower multiplicity pin yields two *distinct* orthonormal kernel basis
vectors, and `laplacian_kernel_eq_span_onesVec` (electrical step 2)
says the kernel is one line — contradiction. Load-bearing on the kernel
characterization and both multiplicity pins: an error in any breaks
this proof. `fiedlerPartition` (the sign half-space) then comes with
sanity facts at two strengths — interface form under `0 < lambda2`
(`fiedlerPartition_nonempty_of_pos`/`_ne_univ_of_pos`, both through
the zero-sum identity, exactly where `0 < lambda2` is load-bearing) and
the connectivity corollaries (`fiedlerPartition_nonempty`/
`_ne_univ`).

**QA** `SpectralGraph/Fiedler_QA.lean` (57 declarations, +57 total,
25 modules) — the Fiedler vector is noncomputable (spectral theorem +
classical choice), so the witnesses pin it through its proved defining
properties rather than by deciding entries. Positive witness 1 (`K₂`,
reusing `Variational_QA` fixtures): entries antisymmetric by the zero
sum, leading entry nonzero by unit norm, partition pinned to
`{0} ∨ {1}`, card `1`, boundary `1`. Positive witness 2 (the `P₄`
barbell — two `K₂` near-cliques joined by one bridge, the proposal's
named example shape): support-graph connectivity by explicit walks,
`0 < λ₂` via the certificate theorem, `λ₂ ≤ 1` via the proved Rayleigh
engine `secondEval_le_rayleigh` at the cut indicator
`![1,1,-1,-1]` (energy `4`, norm `4`), `λ₂ ≠ 1` because the eigen
equations at `λ = 1` force the vector to vanish against unit norm,
and then the eigen equations force the sign relations
`f 1 = (1-λ)f 0`, `f 2 = (1-λ)f 3`, `f 3 = -f 0` — so the partition is
*derived* to be exactly the known good cut `{0,1}` or its complement:
boundary `1`, volume `3`, conductance `1/3`, card `2`. Negative
witness (two disjoint edges): support graph proved not connected
(block invariant over walks), `λ₂ = 0` (hypothesis fails), and
`onesVec` is a nonzero eigenvector at `λ₂` (satisfying exactly the
equation `fiedlerVector_eigen` states) whose sign filter is all of
`univ` — the degenerate pattern the hypothesis rules out.

Docs: umbrella + module docstring, scoreboard (435/16/0, verification
rows, milestone bullet), radar (subject axis 4 re-scored 3.0 → 3.5 per
the proposal's own protocol — Phase A scored alone, Phase B to be
scored separately at its axiom-backed level; QA-axis count synced
435/25 with the new QA kind recorded; proved-depth and reuse text
extended), SGT index map (new `Fiedler` section), backlog item 4
(Phase A delivered; Phase B named as the open remainder), README
snapshot (axis-4 cell 3.5), proposal delivery record, and
`proposals/README.md` (Fiedler moved to Medium with the Phase B
decision framing).

**Environment note:** a new High item
(`proposals/repair-and-retire-woodbury.md`) appeared in the priority
table *during* this run (concurrent operator addition; the file is
untracked and preserved untouched). This run had already committed to
Fiedler Phase A when it started; the Woodbury repair is the natural
next run.

**Active slice (run 1, 2026-08-18): audit and finish the uncommitted
Fiedler Phase A milestone — DELIVERED.** Operator direction pinned
this run to finishing only: audit the existing Fiedler module and QA
changes, preserve unrelated work (the untracked Woodbury proposal,
`scripts/next-steps`), directly build the changed Lean modules and the
closest QA consumer, run the standard hygiene checks and the full
`lake build`, update only the corresponding records; no new proposal,
no commit.

**Audit outcome:** the Lean/QA/umbrella/index/proposal records are
mutually consistent — 57 Fiedler QA declarations, 16 explicit axioms,
25 QA modules, all re-derived from source (scoreboard regeneration
byte-identical). Exactly one defect was found and repaired: the
radar's subject-axis-4 **score cell** still read `3.0` while its own
trailing prose, the README snapshot, this plan, the proposal delivery
record, and the activity log all recorded the protocol re-score to
`3.5` — the cell is now synced to the recorded decision (README and
radar agree again). No Lean changes were needed: direct elaboration of
`GraphTheory.Fiedler` and `Fiedler_QA` is clean (zero errors, zero
warnings), targeted `lake build` of both targets ✔, `lint_axioms`
(16), `check_citations`, `check_markdown_links` pass, and the full
`lake build` succeeds ("Build completed successfully"; the 22
Scaffold-side notes are the documented pre-existing linter notes in
untouched committed modules — none in the two new Fiedler files —
plus Mathlib-package `docPrime` notes from recompiled Mathlib residue,
the known pruned-cache environment debt). Unrelated working-tree
changes preserved; nothing committed. The Fiedler Phase A milestone is
closed as delivered.

**Active slice (run 1, 2026-08-18): repair and retire the Woodbury
identity axiom — the High item — DELIVERED.** Selected from
`proposals/README.md`'s Active priority table (its High entry at run
start). The admitted `woodbury_identity` was verified false
(`A=1, U=V=1, C=0` in the scalar case: every stated determinant
hypothesis holds while the two sides evaluate to `1` and `0`), so this
was a correctness repair of the trust base, not a leverage bet:
`GraphTheory/Dynamics.lean` names this exact identity as its intended
future consumer, and a false axiom inherited there would fail exactly
the way `cheeger_lower_bound`'s old shape did — after something was
built on it. Explicit axiom count **16 → 15**.

**Delivered** (all per the proposal's scope; `sherman_morrison` stays
admitted, out of scope): (1) the axiom replaced by a theorem at the
same name with the standard middle factor `C⁻¹ + V A⁻¹ U` and exactly
the three `IsUnit …det` hypotheses — the old `IsUnit (A + U C V).det`
was *dropped as derivable* (a deliberate strengthening beyond the
proposal's sketch: Mathlib's `invertibleAddMulMul` constructs the
sum's `Invertible` instance from the middle one); (2) the proof is
pure upstream reuse — `Matrix.invOf_add_mul_mul` plus the
`NonsingularInverse` bridges `invertibleOfIsUnitDet` /
`invOf_eq_nonsing_inv`, all reachable through the module's existing
imports (zero new axioms, zero `sorry`, no wrapper, no deprecated
compatibility declaration — it would restate a falsehood; zero
consumers existed); (3) QA `Scaffold/QA/Core/MatrixUpdates_QA.lean`
(the first Core-domain QA file, 8 declarations): the retired shape
negated at its own `Fin 1`/`ℚ` statement and refuted *without consuming
any axiom* (`old_woodbury_identity_refuted_QA`), the old middle and sum
hypotheses separately proved *satisfied* at the counterexample (the
refutation is of a genuinely applicable statement), the corrected
`IsUnit C.det` hypothesis proved to exclude that counterexample, and
positive instances at scalars (`(2+3)⁻¹ = 1/5`) and at a non-scalar
rank-one update (`diag 2 2` + all-ones rank one = `!![3,1;1,3]`, both
sides computed to `!![3/8,-1/8;-1/8,3/8]` through the computed middle
`(1+1)⁻¹ = 1/2`), the theorem-consumed right sides pinned against
independently computed left sides. Computational route recorded in the
proposal: `Matrix.inv` is not `decide`-evaluable (kernel reduction
sticks on `Ring.inverse`); 1×1 inverses go through
`Matrix.inv_eq_left_inv` cancellation, 2×2 through the adjugate
formula. (4) Records: both indexes, scoreboard (15/443/0, milestone
bullet, verification rows), radar (axiom-minimization re-scored
4.0 → 4.5 per protocol — the first retirement motivated by verified
falsity rather than unprovedness; QA count 443/26; proved-depth text
extended), README (15 axioms, 443 QA), proposal delivery record, and
`proposals/README.md` (moved to Delivered; the operator's mid-run
additions — Courant–Fischer High, Sherman–Morrison/Perron–Frobenius
rows — preserved).

**Next milestone (open):** the operator's new High item —
`proposals/prove-courant-fischer.md` (general Courant–Fischer min–max;
four named downstream consumers); or the Sherman–Morrison retirement
(Medium, now unblocked and the cheapest retirement in the backlog);
Fiedler Phase B stays Medium and decision-gated.

**Active slice (run 1, 2026-08-18): prove the general Courant–Fischer
min–max — DELIVERED.** Selected from `proposals/README.md`'s Active
priority table (top High item). The proposal's open next step — survey
the pin for the dimension-intersection lemma — resolved affirmatively
before committing: `Submodule.finrank_sup_add_finrank_inf_eq`,
`Finset.exists_subset_card_eq`, `finrank_span_eq_card` (Fintype-family
form), `Fintype.linearIndependent_iff`, `Module.finrank_pi`,
`Submodule.ne_bot_iff` all present in v4.14.0. Pure hard crust — **no
axiom changes (count stays 15**; general min–max was never admitted).

**Delivered in `GraphTheory.Spectral`** (new `CourantFischer` section):
the general-`k` multiplicity pins as public center API
(`card_filter_eigvalOf_lt_evals_le`: at most `k` eigenbasis indices
strictly below `evals k`; `succ_le_card_filter_eigvalOf_le`: at least
`k+1` at or below — the count-form generalizations of the `k = 1` pins
behind `lambda2_variational`, via new private sorted-list workhorses
plus a multiset-transfer bridge); the orthonormal-family tools
(`eigvecOf_dotProduct`, `linearIndependent_eigvecOf_finset`,
`finrank_span_eigvecOf_finset`); the component-form Rayleigh bounds
(`rayleigh_le_evals_of_forall_dotProduct_eq_zero`,
`evals_le_rayleigh_of_forall_dotProduct_eq_zero` — the Rayleigh
quotient as an eigenvalue-weighted average through the proved spectral
resolution `quadForm_eigvalOf` + Parseval); span-orthogonality
(`dotProduct_eigvecOf_eq_zero_of_mem_span`, via the dot-product linear
functional's kernel); and the three headline forms —
`exists_submodule_forall_rayleigh_le` (existence direction:
`Finset.exists_subset_card_eq` extraction of `k+1` below-threshold
eigenbasis vectors, dimension by orthonormality, Rayleigh bound by
components), `exists_ne_mem_rayleigh_ge_of_finrank_eq` (competitor
direction: every `(k+1)`-dimensional `W` meets the tail eigenspace
nontrivially by `finrank_sup_add_finrank_inf_eq` + `Module.finrank_pi`
dimension counting, and the intersection vector's below-threshold
components vanish), and `evals_min_max` (the packaged infimum equation,
both inequalities from the two witness forms — no compactness needed).
Only symmetry is assumed throughout — no positivity, kernel, or graph
structure (contrast `secondEval_variational`, the index-1
PSD-plus-kernel instance). The four named consumers remain separate
follow-ons, per the proposal.

**QA** `SpectralGraph/CourantFischer_QA.lean` (33 declarations, 476
total): the `!![2,1;1,2]` fixture's spectrum `[1,3]` pinned from
trace/determinant/sortedness independent of the theorem; the competitor
direction instantiated on a hand-checked line; the existence direction
at `k = 1` yielding — through `Submodule.eq_top_of_finrank_eq` — the
derived universal "every Rayleigh quotient ≤ top eigenvalue", with the
competitor witness then pinned to attain `evals 1 = 3` exactly through
both directions; negative witnesses: the existence-direction property
refuted on the wrong line (`3 ≤ 1`), the dimension hypothesis proved
load-bearing (conclusion false on a one-dimensional subspace at index
`1`), and at the interior index `k = 1 < n−1` on the three-vertex path
Laplacian a wrong two-dimensional subspace refuted (`4/3 ≤ evals 1`
vs. the theorem-derived `evals 1 ≤ 1`) with the older
`secondEval_le_rayleigh` engine cross-checking the same bound.

Docs updated: scoreboard (15/476/0, milestone bullet, count sync),
radar (subject axis 3 re-scored 3.5 → 4.0 per protocol with the
milestone recorded; QA-axis count synced 476/27 with the new QA kind
described; proved-depth text extended), README (axis-3 cell, 476 QA,
maturity prose), SGT index map (new `Spectral` rows), proposal
delivery record, and `proposals/README.md` (moved to Delivered; no
High items remain — note added for the next run's selection).

**Next milestone (open):** no High item remains in the priority table.
Candidates: the Sherman–Morrison retirement (Medium, cheapest remaining
axiom retirement); the min–max theorem's named consumers as separately
scoped runs (interlacing retirement via min–max over shared test
subspaces; full Rayleigh/Dirichlet monotonicity through the now-proved
attained characterization); Fiedler Phase B (Medium, decision-gated);
the electrical definiteness residual; the `evals (c • M)` excavation.

**Active slice (run 1, 2026-08-18): retire the Sherman–Morrison axiom —
DELIVERED.** The Medium item `proposals/retire-sherman-morrison.md`
(the named cheapest remaining axiom retirement, unblocked by the
Woodbury repair), scope items 1–6 only. Explicit axiom count **15 →
14**; no new axioms, no `sorry`.

**Finding recorded before any edit, per the proposal's acceptance
criteria:** this was a **proof task, not a correctness repair** — the
statement was verified correct against the corrected Woodbury shape
first (at `C = [1]` the rank-one middle factor is exactly the scalar
denominator `1 + v ⬝ᵥ (A⁻¹ *ᵥ u)`; the Woodbury `C`/`C⁻¹` defect is
invisible at rank one). The theorem keeps the axiom's exact name,
hypotheses, and statement; zero consumers existed, so no migration
surface.

**Route (as proposed, through Scaffold's own proved Woodbury theorem):**
`woodbury_identity` at `k = Fin 1` with `C = 1`; the packing lemma
`U * V = Matrix.of fun i j => u i * v j` (`Fin.sum_univ_one`, not
`rfl`, exactly as the proposal calibrated); the middle factor
identified with the 1×1 matrix of the scalar denominator (through
`Matrix.dotProduct_mulVec`); `hM` from `hv` via `Matrix.det_fin_one`;
the middle inverse via `Matrix.inv_eq_left_inv` + `inv_mul_cancel₀`;
the final entrywise↔matrix shape matched by the pin's
`Matrix.mul_smul`/`Matrix.smul_mul` algebra. Mathlib survey recorded:
`Matrix.inv_one` does *not* exist in the pin — `(1)⁻¹ = 1` derived via
`inv_eq_left_inv`. **Load-bearing:** the specialization consumes the
repaired Woodbury theorem, so a residual defect in that repair would
surface here rather than pass beside it.

**QA** `QA/Core/MatrixUpdates_QA.lean` (+4 declarations, 12 in file,
480 total): positive instance at the existing `A2 = diag 2 2` fixture
with `u = v = ![1,1]` — the update `!![3,1;1,3]`'s true inverse
`!![3/8,-1/8;-1/8,3/8]` computed independently by the adjugate formula
(`sherman_morrison_sum_inv_QA`), and the theorem-consumed right side
pinned to the same value with the denominator computed to `1` from the
definitions (`sherman_morrison_rhs_QA`); negative witness at the
excluded denominator — `A = !![1]`, `u = ![2]`, `v = ![-1/2]` attains
`v ⬝ᵥ (A⁻¹ *ᵥ u) = -1` exactly
(`sherman_morrison_excluded_denominator_QA`) and the update is the
singular zero matrix there (`sherman_morrison_singular_witness_QA`).

**Docs:** module docstring and theorem documentation, both indexes
(`higham_matrix_updates` retirement note + status; `perturbation` map
row marked proved), scoreboard (14/480/0, milestone bullet,
verification rows, QA-file count 8 → 12), radar (axiom-minimization
trend extended to 26 → … → 14 with the Core update-identity bridge now
axiom-free; QA-axis count synced 480/27 with the new QA kind
described), README (14 axioms, 480 QA), `proposals/README.md` (moved
to Delivered), and the proposal's delivery record. The operator's
concurrent working-tree changes (`.gitignore`, the two clean-room
proposal files, untracked `cdx-clean-assess.md` and
`proposals/clean-room-sgt-lemma-science-map.md`, the mushy-center
priority row) preserved untouched.

**Next milestone (open):** no High item remains. Candidates: the
remaining Medium items (Fiedler Phase B — needs its named operator
decision; the mixing-time program); the min–max theorem's named
consumers as separately scoped runs (interlacing retirement via
min–max over shared test subspaces; full Rayleigh/Dirichlet
monotonicity); the electrical definiteness residual; the `evals (c • M)`
excavation.

**Active slice (run 1, 2026-08-18): retire the Cauchy interlacing axiom
— the min–max theorem's first named consumer — DELIVERED.** Selected
from the center-out queue: `eigen_interlacing_principal_submatrix` was
one of the 14 remaining admitted axioms and the Courant–Fischer
proposal's first named consumer; retiring it both shrank the trust
surface (**14 → 13**) and made the brand-new min–max engine carry real
weight — its proof would fail if `evals_min_max`'s two witness
directions or the multiplicity pins were wrong (load-bearing growth,
per strategy §Load-bearing). Pre-check recorded: the statement is the
textbook two-sided window `λᵢ(M) ≤ μᵢ(B) ≤ λ_{i+d}(M)` and is true as
stated (the derivable `hn` aside) — a **pure proof task**, like
Sherman–Morrison, not a correctness repair. At unchanged
name/hypotheses/statement; zero consumers existed, so no migration
surface.

**Route (delivered as scoped, per the proposal's warning that the
subspace-intersection step is extra work):** the extend-by-zero padding
bridge `padVec`/`padVecLinear` (`↥S → ℝ` into `V → ℝ`) with proved
preservation of dot products (`dotProduct_padVec_self`), quadratic
forms (`quadForm_padVec`, no symmetry needed), and hence Rayleigh
quotients (`rayleigh_padVec`); lower bound via the CF existence
direction on the submatrix + `Submodule.map` image + the CF competitor
direction on the ambient; upper bound via the CF existence direction on
the ambient at index `i + d` + the dimension count
`finrank (U ⊓ range pad) ≥ i + 1` (the same
`Submodule.finrank_sup_add_finrank_inf_eq` + `Module.finrank_pi`
pattern the CF proof itself used — the proposal's warned extra step) +
exact-dimension extraction `exists_submodule_finrank_eq_of_le` (span
of `k` basis vectors, meeting the competitor direction's
equality-shaped hypothesis) + the comap dimension transfer
`finrank_comap_eq_of_le_range`. Pin survey recorded before proving:
`LinearEquiv.finrank_eq`, `LinearMap.finrank_range_of_inj`,
`finrank_span_eq_card`, `Module.finBasis`,
`Submodule.equivMapOfInjective` all present in the pin; one new import
(`Mathlib.Algebra.Module.Submodule.Range`, for `LinearMap.mem_range`).

**QA** `SpectralGraph/Interlacing_QA.lean` (+4 public declarations,
484 total): the `K₂` Laplacian spectrum `[0, 2]` and its
singleton-(`{0}`)-submatrix spectrum `[1]` both pinned from
trace/determinant/sortedness independent of the theorem; the theorem
instantiated to the **strict window `0 ≤ 1 ≤ 2`** (all three values
computed); and the negative witness — both collapsed one-sided bounds
(`μ₀ ≤ λ₀`, `λ₁ ≤ μ₀`) refuted in proved form, so the two-sided window
shape itself is witnessed. This supersedes the axiom-era note that no
thin QA of the inequality existed: computational eigenvalue QA
machinery (delivered with the Cheeger repair) did not exist when that
note was written.

Docs updated: module docstring and section header (Spectral.lean now
carries **zero** `axiom` declarations), scoreboard (13/484/0 +
milestone bullet + verification rows), radar (subject axis 2 evidence:
interlacing proved; assurance axiom-minimization trend
26 → … → 13; QA count 484/27; proved-depth and downstream-reuse text —
the retirement is the min–max engine's first *proof-level* consumer),
README (13 axioms, 484 QA, maturity bullet), Horn–Johnson source index
(interlacing row → theorem, §4.2 general min–max row added), SGT index
map (padding-bridge definitions + proved-status annotations), Mathlib
coverage map (interlacing now locally proved though still absent
upstream), Courant–Fischer proposal delivery note, and
`proposals/README.md` (additive record; the operator's concurrent
electrical-flow High item preserved untouched and acknowledged as the
next run's milestone).

**Next milestone (open):** the operator's new High item —
`proposals/electrical-flow-routing.md` (electrical flows, Thomson's
principle, Rayleigh monotonicity; step 0 is its representation/Mathlib
survey, per the operator's own indexing note). Or the remaining
Mediums (Fiedler Phase B, decision-gated; mixing-time step 1) and the
min–max engine's other named consumers (full Rayleigh/Dirichlet
monotonicity — now cheaper through the delivered padding bridge).

**Active slice (run 1, 2026-08-19): electrical-flow routing steps 0
and 1 — representation pinned and Kirchhoff conservation delivered —
DELIVERED.** Selected from `proposals/README.md`'s Active priority
table (its High entry at run start). Per the proposal's own operating
instructions: step 0 ran first (the pinned Mathlib re-surveyed; the
representation choice, zero-edge semantics, and target module recorded
in the proposal *before any Lean*), then the one Lean build step —
step 1. Zero new axioms (count stays 13); steps 2–5 (energy
agreement, Thomson, Rayleigh monotonicity, the ICP example) were
**not** started this run.

**Step 0 (survey and representation decision, recorded in the
proposal):** the pin has no network-flow/circulation/max-flow API
anywhere, no graph-native divergence (its only `Divergence` files are
the box/measure-integral divergence *theorems* on continua), no
electrical-network API (the `Rayleigh` hits are number theory and the
Rayleigh *quotient*), and the one oriented-edge type
`SimpleGraph.Dart` carries no flow/energy API and would force
`supportGraph` conversions with no upstream consumer — the matrix
representation `EdgeFlow V = Matrix V V ℝ` was pinned exactly as the
proposal sketched (conductance orientation; support as `IsFlowOn`'s
second conjunct; the ordered-pair `1/2` factor reserved for
`flowEnergy` in step 2), in a new focused module
`GraphTheory.ElectricalFlow` importing `Electrical` (keeps the
resistance module bounded; the flow interface has its own growth
path). Coverage map's electrical row re-surveyed with the
flow/divergence specifics (same absence verdict).

**Step 1 delivered** (all proved, `GraphTheory.ElectricalFlow`):
`electricalCurrent` (Ohm's law `A i j * (f i − f j)`), `flowDivergence`
(net outflow `∑ j, θ i j`), the predicates `IsFlowOn` (antisymmetry +
zero-conductance support — the guard against the proposal's named
zero-conductance trap) and `IsUnitFlow` (divergence exactly the unit
demand `e u − e v`),
`electricalCurrent_antisymm` (symmetry load-bearing),
`electricalCurrent_eq_zero_of_weight_eq_zero` (support,
unconditional), the **Kirchhoff bridge**
`flowDivergence_electricalCurrent`
(`flowDivergence (electricalCurrent A f) = laplacian A *ᵥ f` — a
one-line load-bearing consumer of the center's exact sign convention
`laplacian_mulVec_apply`), `isFlowOn_electricalCurrent`, and the
headline `isUnitFlow_electricalCurrent`: every unit-demand potential
induces a valid unit flow — the potential-based resistance API becomes
a routing object.

**QA** `SpectralGraph/ElectricalFlow_QA.lean` (16 declarations, 500
total, 28 modules): `K₂` — current matrix `!![0,1;-1,0]`, divergence
`![1,-1]`, both computed from the raw definitions independently of the
bridge, plus the unit-flow instantiation through the headline theorem;
3-path — unit flow `0 → 1 → 2` with the internal vertex's divergence
computed to `0` (Kirchhoff conservation away from source/sink) and
nothing on the non-adjacent pair; **negative witnesses for both
proposal-named traps** — the asymmetric network `!![0,2;1,0]` where
the current provably fails antisymmetry (`2 ≠ 1`: `A.IsSymm`
load-bearing), and the edgeless-network phantom `!![0,1;-1,0]` which
satisfies antisymmetry *and* the unit divergence yet is excluded by
`IsFlowOn`'s support conjunct alone (dropping it would admit a unit
flow on a network with no edges; the energy-level refutation is
deferred to step 2 with `flowEnergy`).

**Docs updated:** umbrella (new import), scoreboard (500/13/0,
verification rows, milestone bullet), radar (QA-axis count 500/28 with
the new QA kind; subject axis 6 evidence extended and the score
**held at 3.0** per protocol — the axis rises with Thomson/Rayleigh,
which this interface exists to carry; proved-depth text), README
snapshot (umbrella list, 500 QA, date), SGT index map (new
`ElectricalFlow` section), coverage map (electrical row re-survey),
proposal step-0 decision + step-1 delivery record, and
`proposals/README.md` progress note (the operator's uncommitted
interlacing-table edit preserved untouched).

**Next milestone (open):** proposal step 2 — flow energy
(`flowEnergy` with the explicit zero branch and the mandatory `1/2`
ordered-pair factor), the energy agreement
`flowEnergy A (electricalCurrent A f) = quadForm (laplacian A) f`
(load-bearing on the `1/2` conventions in both the current energy and
`laplacian_quadForm`), and its QA double-counting fixture; then steps
3–4 (Thomson, Rayleigh monotonicity) as separate runs. Or the
remaining Mediums (Fiedler Phase B, decision-gated; mixing-time step
1).

**Active slice (run 1, 2026-08-19): electrical-flow step 2 — flow
energy and the energy agreement — DELIVERED.** The Active priority
table's top High item (electrical-flow routing), continuing its
recorded next milestone. Scope held to the proposal's one-step rule:
steps 3–5 (Thomson, Rayleigh, the ICP example) were **not** started.
All proved, **no new axioms** (count stays 13).

**Delivered in `GraphTheory.ElectricalFlow`:** `flowEnergy` exactly as
the proposal pinned it — explicit zero branch (`if A i j = 0 then 0
else θ i j ^ 2 / A i j`), summed over ordered pairs, halved for double
counting; the **energy agreement**
`flowEnergy_electricalCurrent` (`flowEnergy A (electricalCurrent A f)
= quadForm (laplacian A) f` — termwise Ohm's-law algebra on the
nonzero branch, zero-on-zero on the branch, then `laplacian_quadForm`;
load-bearing on the `1/2` convention in *both* sums);
`flowEnergy_nonneg` (squares over positive conductances — the base
order fact steps 3–4 compare flows by); and the step-2 headline
`flowEnergy_electricalCurrent_eq_effectiveResistance` (on a connected
graph, a unit-demand current dissipates exactly the resistance it
routes — agreement composed with the crust's solution-level energy
identity and the total-function agreement theorem).

**Statement-shape deviation (recorded in the proposal):** the
agreement landed at **symmetry-only** strength — the proposal's
"must use nonnegative weights" is satisfied by the explicit zero-branch
handling; the nonzero-branch algebra `(c x)²/c = c x²` is pure field
algebra. QA witnesses both sides of the claim: the agreement
instantiates on a symmetric negative-weight network (both sides `-1`)
where `flowEnergy_nonneg` — which does hypothesize nonnegativity —
provably fails (energy `-1 < 0`).

**QA** `SpectralGraph/ElectricalFlow_QA.lean` (+25 declarations, 41 in
file, 525 total): energies `1`/`2` computed from the raw `flowEnergy`
definition on `K₂`/`P₃`, each cross-checked against the independently
computed Dirichlet energies and pinned resistance values (three routes
meeting at each number); the **mandatory double-counting fixture** —
raw ordered-pair sum computes to `2 ≠ 1` = Dirichlet energy, so
omitting the `1/2` factor would numerically break the agreement; the
step-1 phantom's deferred energy pinning (`0` on the edgeless
network); the **zero-energy competitor** — on a real edge plus an
isolated vertex, an antisymmetric unit-divergence flow routing through
zero-conductance pairs dissipates `0 < 1` = the real resistance and is
excluded by `IsFlowOn`'s support conjunct alone (over
flows-satisfying-everything-except-support, Thomson's step-3 statement
would assert `1 ≤ 0` on this fixture); and the hypothesis-set witness
above. Fixture note recorded: all-zero-row matrices use the repo's
entrywise-`if` definition pattern (the matrix notation's zero-function
normalization leaves `vecTail` leftovers otherwise).

**Verification:** `lake env lean` on both changed modules — zero
errors, zero warnings (one new `omit` clause for `flowEnergy_nonneg`);
`lake build` of both targets ✔; full `lake build` ✔; all 28 QA
modules batch-elaborated with zero errors (only the documented
pre-existing linter notes in untouched modules); `lint_axioms` (13
covered), `check_citations`, `check_markdown_links` pass; scoreboard
regenerated (525/13/0) and idempotent.

**Docs updated:** scoreboard (525/13/0, milestone bullet, verification
rows, reviewed date), radar (QA-axis count 525/28 with the step-2 QA
kind described; subject axis 6 evidence extended with the score **held
at 3.0** per protocol — an identity, not a new inequality; proved-depth
text), README snapshot (umbrella cell, 525 QA), SGT index map (4 new
`ElectricalFlow` rows, section re-titled), proposal step-2 delivery
record + statement-shape deviation, and `proposals/README.md` progress
note (the operator's uncommitted sparsification-split table rows
preserved untouched).

**Next milestone (open):** proposal step 3 — **Thomson's principle**
(`effectiveResistance A u v ≤ flowEnergy A θ` for every valid unit
flow `θ`, via the electrical current as the minimizer and
`flowEnergy_nonneg` on the divergence-free difference; the proposal
suggests splitting out the discrete integration-by-parts lemma if it
deserves a reusable interface); then steps 4–5 (Rayleigh monotonicity
in conductance form — orientation recorded as binding — and the ICP
capacity-reinforcement example). Or the remaining High items: Foster
Phase A (pseudoinverse-free eigenbasis route, needs its own
statement-shape spike) or the decidable-certificates Step 0
(convention decision + ℚ-kernel `decide` spike, both scoped in the
proposal).

**Active slice (run 1, 2026-08-19, IN PROGRESS): electrical-flow step
3 — Thomson's principle.** Selected from `proposals/README.md`'s
Active priority table (the electrical-flow High item, mid-program at
its recorded next step). Scope per the proposal's one-step rule: the
minimum-energy inequality over valid unit flows, stated as the
universal `effectiveResistance A u v ≤ flowEnergy A θ` (no `sInf`
packaging), plus QA (attainment at the electrical current; a strict
competitor witness). Steps 4–5 are NOT started this run.

**Active slice (run 1, 2026-08-19): electrical-flow step 3 —
Thomson's principle — DELIVERED.** The Active priority table's top
High item at its recorded next step; one-step rule held (steps 4–5 —
Rayleigh monotonicity and the ICP example — NOT started). All proved,
**no new axioms** (count stays 13).

**Delivered in `GraphTheory.ElectricalFlow`:** the flow-space
plumbing (`flowDivergence_sub` — divergence is linear;
`isFlowOn_sub` — the flow space is linear); the **divergence-free
superposition lemma**
`flowEnergy_add_of_flowDivergence_eq_zero` (a zero-divergence flow
perturbation of a current adds exactly its own energy — the discrete
integration-by-parts step, split out as its own reusable interface per
the proposal's suggestion); and the headline
`effectiveResistance_le_flowEnergy` (**Thomson's principle**: every
valid unit flow dissipates at least the resistance it routes — the
electrical current is the energy minimizer). Route exactly as
proposed: the competitor minus the unit-demand current is a flow with
zero divergence (Kirchhoff bridge + the demand equation — load-bearing
on the center's sign convention), the superposition lemma kills the
cross term (Ohm's law reduces it to `∑ i j, (f i − f j) * d i j`;
row sums vanish by zero divergence, column sums are the negated row
sums by antisymmetry), `flowEnergy_nonneg` discards the remainder, and
the step-2 identity evaluates the current's energy as the resistance.
**Statement-shape deviation (recorded in the proposal):** the
superposition lemma is stated with **no hypotheses on `A`** — not even
the symmetry the proposal's sketch assumed; only the perturbation's
flow properties enter. No `sInf` packaging, per the proposal's
explicit instruction.

**QA** `SpectralGraph/ElectricalFlow_QA.lean` (+18 declarations, 59 in
file, 543 total): the new triangle `K₃` fixture (the smallest network
with two parallel routes — unit flows non-unique) with the
unit-demand potential `![1, 1/3, 2/3]`, resistance `2/3`, and the
**split current** (`2/3` direct, `1/3` per path edge) whose energy
attains `2/3` from the raw definitions; the **detour competitor** (a
valid `IsUnitFlow` routing around the two-edge path, every conjunct
computed, energy `2`) with Thomson instantiated as the *strict* bound
`2/3 < 2` — the inequality is not vacuous on a network with competing
routes; the superposition decomposition composed as `2 = 2/3 + 4/3`
(all three energies computed independently of the lemma); and edge
attainment (`1 ≤ 1` with both values independently pinned). Fixture
note: the triangle and detour matrices use the entrywise-`if` pattern
(the matrix notation's zero-function normalization trap, already
recorded in step 2).

**Verification:** `lake env lean` on both changed modules — zero
errors, zero warnings; `lake build` of both targets ✔; full `lake
build` ✔ (2180 targets); all twenty-eight QA modules batch-elaborated
with zero errors; `lint_axioms` (13 covered), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (543/13/0) and
idempotent. Radar re-scored per protocol (the recorded reservation —
"the axis is reserved to rise with Thomson/Rayleigh" — fired):
subject axis 6 **3.0 → 3.5** with the milestone recorded in the
re-score log; QA-axis count synced 543/28 with the step-3 QA kind
(triangular variational witnesses) described; proved-depth text
extended. Umbrella unchanged (module already in it); SGT index map
(4 new `ElectricalFlow` rows, section re-titled), README snapshot
(axis-6 cell 3.5, 543 QA), scoreboard verification rows + milestone
bullet, proposal step-3 delivery record + statement-shape deviation,
and `proposals/README.md` progress note updated.

**Next milestone (open):** proposal step 4 — **Rayleigh monotonicity
in conductance form** (`A ≤ B` entrywise ⇒ `effectiveResistance B u v
≤ effectiveResistance A u v`, both graphs connected symmetric
nonnegative; route per the proposal: the `A`-electrical unit flow as
competitor on `B`, its `B`-energy at most its `A`-energy since every
denominator increased, Thomson on `B` closes; the orientation is
binding — conductances, not resistances — and QA plan item 2, the
capacity increase `1 → 1/2` fixture, belongs there); then step 5 (the
ICP capacity-reinforcement example). Or the remaining High items:
Foster Phase A (pseudoinverse-free eigenbasis route, needs its own
statement-shape spike) or the decidable-certificates Step 0 (convention
decision + ℚ-kernel `decide` spike, both scoped in the proposal).

## Ready queue

1. ~~Proposal step 6 — the one-sided Dirichlet bound~~ — delivered
   above (program complete). Still open, cheap: the definiteness
   residual `R u v = 0 ↔ u = v` (reachable pair; the natural completion
   of nonnegativity, reusing the step-2 zero-energy ⇒ constant
   argument).

1. Citation hygiene — completed 2026-08-17 (see Active milestone and Last
   verified state); Chung provenance corrected, Weyl/Davis–Kahan fidelity
   notes added, DK hypothesis tightened, `spectral_gap_stability` proved
   from Weyl (axioms 19 → 18).
2. Establish the first broad-SGT backlog — delivered 2026-08-17 as
   `docs/6_SGT_BACKLOG.md` with its top item implemented
   (`GraphTheory.RandomWalk`); next backlog item: irregular normalized
   adapters.
3. Do not let retained applications or compatibility packages determine the
   next SGT milestone.
4. `spectral_persistence` retain-or-deprecate — decided 2026-08-17:
   deprecated with a migration note (zero non-QA consumers; derived
   chain covers the motivating use), retained through the compatibility
   window; removal is a later release decision. Do not extend its
   theorem family.
5. Re-admit removed subgaussian statements (moment growth, linear
   combinations, centering, sums) only when a consumer names them.

## Last verified state

- 2026-08-19 (decidable-certificates steps 0–1: convention decision +
  ℚ-decide spike + the `GraphTheory.Expander` discrepancy core, no
  axiom change): `lake env lean` on `GraphTheory.Expander` and on
  `QA.SpectralGraph.Expander_QA` — both zero errors, zero warnings
  (targeted `omit` clauses; two targeted
  `set_option linter.unnecessarySeqFocus false in` lines on the
  cross-term lemmas per repo precedent); `#print axioms` on all seven
  public theorems — only `propext, Classical.choice, Quot.sound`;
  `lake build Scaffold.Mathlib.GraphTheory.Expander` and
  `Scaffold.QA.SpectralGraph.Expander_QA` ✔; full `lake build` ✔
  (2182 targets); all thirty QA modules elaborated directly in one
  batch (zero errors — only the documented pre-existing linter notes
  in untouched modules); 647 QA declarations (+22 in `Expander_QA`),
  no `sorry`/`admit` anywhere under `Scaffold/`; 13 explicit cited
  axioms (unchanged — pure hard crust); all hygiene scripts pass
  (`lint_axioms` 13 covered, `check_citations`,
  `check_markdown_links`); scoreboard regenerated (647/13/0) and
  idempotent after the prose edits; radar QA-axis count synced 647/30
  with the axis **held at 4.0** per protocol (hold recorded); README,
  SGT index map, proposal Step-0/Step-1 records, and
  `proposals/README.md` updated. The Step-0 spike artifacts were
  scratch files (removed after the outcomes were recorded in the
  proposal); environment recovery: mathlib interpreted cache fetch +
  explicit `lake build Batteries` (the fetch does not restore
  Batteries' modules needed by `Mathlib.Tactic`) + full build. The
  operator's concurrent untracked files (`adversarial.md`,
  `sgt-gaps.md`, `why-sgt.md`) preserved untouched. Nothing committed.

- 2026-08-19 (electrical-flow step 3: Thomson's principle, no axiom
  change): `lake env lean` on `GraphTheory.ElectricalFlow` and on
  `QA.SpectralGraph.ElectricalFlow_QA` — both zero errors, zero
  warnings (five no-`Fintype`/`DecidableEq`-needed lemmas silenced with
  `omit` clauses); `lake build
  Scaffold.Mathlib.GraphTheory.ElectricalFlow` and `lake build
  Scaffold.QA.SpectralGraph.ElectricalFlow_QA` ✔; full `lake build` ✔
  (2180 targets); all twenty-eight QA modules elaborated directly in
  one batch (zero errors — the only outputs are the documented
  pre-existing linter notes in untouched modules); 543 QA declarations
  (+18 in `ElectricalFlow_QA`, 59 in file), no `sorry`/`admit` anywhere
  under `Scaffold/` (textual matches are prose in comments/docstrings);
  13 explicit cited axioms (unchanged — pure hard crust; Thomson is
  proved from the step-1 Kirchhoff bridge, flow-space linearity, the
  superposition lemma, `flowEnergy_nonneg`, and the step-2 energy
  identity — an error in any would break the proof rather than pass
  beside it); all hygiene scripts pass (`lint_axioms` 13 covered,
  `check_citations`, `check_markdown_links`); scoreboard regenerated
  (543/13/0) and idempotent after the prose edits; radar re-scored per
  protocol (subject axis 6: 3.0 → 3.5 — the recorded reservation for
  Thomson fired — with the milestone in the re-score log; QA-axis count
  synced 543/28 with the step-3 QA kind; proved-depth text extended;
  weakest-axes paragraph updated), README snapshot (axis-6 cell 3.5,
  543 QA — a surgical count/score sync inside the operator's
  uncommitted rewrite, which is otherwise preserved untouched), SGT
  index map (4 new `ElectricalFlow` rows), proposal step-3 delivery
  record + statement-shape deviation (superposition lemma stated with
  no hypotheses on `A`), and `proposals/README.md` progress note
  updated. Nothing committed.

- 2026-08-19 (electrical-flow step 2: flow energy and the energy
  agreement, no axiom change): `lake env lean` on
  `GraphTheory.ElectricalFlow` and on
  `QA.SpectralGraph.ElectricalFlow_QA` — both zero errors, zero
  warnings (one new `omit` clause on `flowEnergy_nonneg`; the
  module's three step-1 clauses unchanged); `lake build
  Scaffold.Mathlib.GraphTheory.ElectricalFlow` and `lake build
  Scaffold.QA.SpectralGraph.ElectricalFlow_QA` ✔; full `lake build` ✔
  (2180 targets); all twenty-eight QA modules elaborated directly in
  one batch (zero errors — the only outputs are the documented
  pre-existing `unusedSectionVars` notes in untouched modules); 525 QA
  declarations (+25 in `ElectricalFlow_QA`, 41 in file), no
  `sorry`/`admit` anywhere under `Scaffold/` (textual matches are
  prose in comments/docstrings); 13 explicit cited axioms (unchanged —
  pure hard crust; the energy agreement and its corollaries are proved
  from `laplacian_quadForm`, the crust's solution-level energy
  identity, and the total-function agreement theorem); all hygiene
  scripts pass (`lint_axioms` 13 covered, `check_citations`,
  `check_markdown_links`); scoreboard regenerated (525/13/0) and
  idempotent after the prose edits; radar (QA-axis count synced
  525/28 with the step-2 QA kind; subject axis 6 evidence extended,
  score held at 3.0 per protocol with the hold recorded in the
  re-score log; proved-depth text extended), README snapshot, SGT
  index map, proposal step-2 delivery record + statement-shape
  deviation, and `proposals/README.md` progress note updated. The
  operator's uncommitted changes (`proposals/README.md` sparsification
  split rows, untracked `icebox/` and
  `proposals/spectral-graph-sparsification.md`) preserved untouched;
  nothing committed.

- 2026-08-19 (electrical-flow steps 0–1: representation decision +
  Kirchhoff conservation, no axiom change): `lake env lean` on
  `GraphTheory.ElectricalFlow` and on
  `QA.SpectralGraph.ElectricalFlow_QA` — both zero errors, zero
  warnings (the three no-`Fintype`-needed lemmas silenced with `omit`
  clauses); `lake build Scaffold.Mathlib.GraphTheory.ElectricalFlow`
  and `lake build Scaffold.QA.SpectralGraph.ElectricalFlow_QA` ✔;
  full `lake build` ✔; all twenty-eight QA modules elaborated
  directly in one batch (zero failures); 500 QA declarations (+16, the
  new `ElectricalFlow_QA`), no `sorry`/`admit` anywhere under
  `Scaffold/`; 13 explicit cited axioms (unchanged — pure hard crust;
  the flow interface is the routing plumbing the proposal's steps 2–4
  consume); all hygiene scripts pass (`lint_axioms` 13 covered,
  `check_citations`, `check_markdown_links`); scoreboard regenerated
  (500/13/0) with verification rows and the milestone bullet; radar
  (QA-axis count synced 500/28 with the new QA kind; subject axis 6
  evidence extended with the score **held at 3.0** per protocol and
  the hold recorded in the re-score log; proved-depth text), README
  snapshot, SGT index map (new `ElectricalFlow` section), coverage
  map (electrical row re-surveyed for flows/divergence, same absence
  verdict), proposal step-0 decision + step-1 delivery record, and
  `proposals/README.md` progress note updated. The operator's
  uncommitted `proposals/README.md` change (the interlacing delivery
  row moved into the Delivered table) preserved untouched; nothing
  committed.

- 2026-08-18 (interlacing retirement, axiom 14 → 13): `lake env lean`
  on `GraphTheory.Spectral` — zero errors; the new-code
  section-variable notes silenced with `omit` clauses (the remaining
  notes at lines 163/527/2291/2313 are the documented pre-existing
  ones in untouched code) — and on
  `QA.SpectralGraph.Interlacing_QA` — zero errors (its two warnings
  are pre-existing, in untouched declarations); `lake build
  Scaffold.Mathlib.GraphTheory.Spectral` and `lake build
  Scaffold.QA.SpectralGraph.Interlacing_QA` ✔; full `lake build` ✔
  (2179 targets); 484 QA declarations (+4 public: `edgeLap_evals`,
  `edgeLap_sub_evals_eq_one`, `interlacing_edge_window_QA`,
  `interlacing_edge_window_strict_QA`; private helpers not counted), no
  `sorry`/`admit` anywhere under `Scaffold/`; 13 explicit cited axioms
  (−1: `eigen_interlacing_principal_submatrix` retired to a proved
  theorem at unchanged name/hypotheses/statement, proved from the
  locally proved Courant–Fischer engine through the padding bridge and
  the subspace-intersection dimension count — a pure proof task per the
  recorded pre-check, not a correctness repair); all hygiene scripts
  pass (`lint_axioms` 13 covered, `check_citations`,
  `check_markdown_links`); scoreboard regenerated (13/484/0) and
  idempotent after the manual prose edits; radar (axis-2 evidence
  updated to proved; axiom-minimization trend → 13; QA 484/27;
  proved-depth and reuse text), README (13 axioms, 484 QA), both
  index files, coverage map, proposal delivery note, and
  `proposals/README.md` updated. The operator's concurrent
  working-tree additions (`proposals/electrical-flow-routing.md` — now
  the active High item and the next run's milestone — and its priority
  row) preserved untouched.

- 2026-08-18 (Sherman–Morrison retirement, axiom 15 → 14): `lake env
  lean` on `Core.MatrixUpdates` and on `QA.Core.MatrixUpdates_QA` —
  both zero errors, zero warnings; `lake build
  Scaffold.Mathlib.Core.MatrixUpdates` and `lake build
  Scaffold.QA.Core.MatrixUpdates_QA` ✔ (the QA file is the module's
  only direct consumer, verified by import search); full `lake build` ✔
  (2179 targets; the Scaffold-side linter notes are the documented
  pre-existing ones in untouched modules); 480 QA declarations (+4, the
  four new public Sherman–Morrison QA lemmas; the file's private
  helpers and defs are not counted), no `sorry`/`admit` anywhere under
  `Scaffold/` (textual matches are prose in comments/docstrings); 14
  explicit cited axioms (−1: `sherman_morrison` retired to a proved
  theorem at unchanged name/hypotheses/statement — the `k = Fin 1`
  specialization of the proved `woodbury_identity`, a pure proof task,
  not a correctness repair, per the proposal's pre-check); all hygiene
  scripts pass (`lint_axioms` 14 covered, `check_citations`;
  `check_markdown_links` reports only 4 broken links in the operator's
  untracked `cdx-clean-assess.md`, present before this run and outside
  this milestone's scope); scoreboard regenerated (14/480/0, QA file
  count 8 → 12) and idempotent after the manual prose edits; radar
  (axiom-minimization trend 26 → 19 → 18 → 17 → 16 → 15 → 14; QA-axis
  count 480/27), README (14 axioms, 480 QA), both indexes, proposal
  delivery record, and `proposals/README.md` updated (item moved to
  Delivered). Unrelated working-tree changes (the operator's
  `.gitignore`, `proposals/clean-room-sgt-export.md`,
  untracked `cdx-clean-assess.md` and
  `proposals/clean-room-sgt-lemma-science-map.md`, and the
  mushy-center priority row in `proposals/README.md`) preserved
  untouched; nothing committed.

- 2026-08-18 (general Courant–Fischer min–max proved, no axiom
  change): `lake env lean` on `GraphTheory.Spectral` — zero errors,
  zero new warnings (the one new-code linter note was silenced with an
  `omit` clause; the remaining notes are the documented pre-existing
  ones in untouched code) — and on
  `QA.SpectralGraph.CourantFischer_QA` — zero errors, zero warnings;
  `lake build Scaffold.Mathlib.GraphTheory.Spectral` and `lake build
  Scaffold.QA.SpectralGraph.CourantFischer_QA` ✔; full `lake build` ✔
  (2179 targets); all twenty-seven QA modules elaborated directly in
  one batch (zero failures); 476 QA declarations (+33, the new
  `CourantFischer_QA`), no `sorry`/`admit` anywhere under `Scaffold/`
  (textual matches are prose in comments/docstrings); 15 explicit
  cited axioms (unchanged — pure hard crust; general min–max was never
  admitted); all hygiene scripts pass (`lint_axioms` 15 covered,
  `check_citations`, `check_markdown_links`); scoreboard regenerated
  (15/476/0) with the milestone bullet and count sync; radar re-scored
  per protocol (subject axis 3: 3.5 → 4.0 recorded; QA-axis count
  synced 476/27; proved-depth text extended); README snapshot (axis-3
  cell 4.0, 476 QA); SGT index map (new `Spectral` rows); proposal
  delivery record; `proposals/README.md` (moved to Delivered with the
  four named consumers explicitly open; note added that no High item
  remains). Unrelated working-tree changes (the operator's
  `scripts/opencode-pursue` and `scripts/test_opencode_pursue.sh`
  modifications) preserved untouched.

- 2026-08-18 (Woodbury repair and retirement, axiom 16 → 15): `lake
  env lean` on `Core.MatrixUpdates` and on
  `QA.Core.MatrixUpdates_QA` — both zero errors, zero warnings; `lake
  build Scaffold.Mathlib.Core.MatrixUpdates` ✔; full `lake build` ✔
  (2179 targets); all twenty-six QA modules elaborated directly (zero
  errors — the only outputs are the documented pre-existing linter
  notes in untouched modules); 443 QA declarations (+8, the new
  Core-domain QA file), no `sorry`/`admit` anywhere under `Scaffold/`
  (textual matches are prose in comments/docstrings); 15 explicit
  cited axioms (−1: the verified-false `woodbury_identity` retired to a
  proved theorem at the standard middle factor `C⁻¹ + V A⁻¹ U` with the
  three `IsUnit` determinant hypotheses, the sum hypothesis dropped as
  derivable, proved from Mathlib's `Matrix.invOf_add_mul_mul` plus the
  `NonsingularInverse` bridges; the old scalar shape refuted in QA with
  its hypotheses proved satisfied at the counterexample); all hygiene
  scripts pass (`lint_axioms` 15 covered, `check_citations`,
  `check_markdown_links`); scoreboard regenerated (15/443/0) with the
  milestone bullet and verification rows; radar re-scored per protocol
  (axiom-minimization 4.0 → 4.5; QA count synced 443/26; proved-depth
  text extended); README snapshot (15 axioms, 443 QA); both indexes
  (`higham_matrix_updates` repair note; `perturbation` map row marked
  proved); proposal delivery record; `proposals/README.md` moved the
  item to Delivered while preserving the operator's concurrent
  additions (Courant–Fischer High row, Sherman–Morrison and
  Perron–Frobenius rows; the operator's `scripts/next-steps` deletion
  preserved untouched).

- 2026-08-18 (audit-and-finish of the uncommitted Fiedler Phase A
  milestone): the delivered Phase A records audited and closed. One
  record defect found and repaired: the radar's subject-axis-4 score
  cell was stale at `3.0` (every other record — the radar's own
  re-score prose, the README snapshot, this plan, the proposal
  delivery record, the activity log — recorded the protocol re-score
  to `3.5`); the cell is synced, no other content changed. No Lean
  changes: `lake env lean` on `GraphTheory.Fiedler` and
  `QA.SpectralGraph.Fiedler_QA` — zero errors, zero warnings;
  targeted `lake build` of both targets ✔; full `lake build` ✔
  ("Build completed successfully" — the 22 Scaffold-side linter notes
  are the documented pre-existing ones in untouched committed modules,
  none in the new Fiedler files; the ~2980 further notes are
  Mathlib-package `docPrime` warnings over recompiled Mathlib residue,
  the recorded pruned-cache environment debt, not Scaffold code);
  scoreboard regeneration byte-identical (435/16/0 re-derived from
  source); `lint_axioms` (16 covered), `check_citations`,
  `check_markdown_links` pass. Unrelated working-tree changes
  (untracked `proposals/repair-and-retire-woodbury.md`,
  `scripts/next-steps`) preserved untouched; nothing committed.

- 2026-08-18 (Fiedler Phase A: vector, algebraic connectivity, sign
  partition): `lake env lean` on `GraphTheory.Fiedler` and on
  `QA.SpectralGraph.Fiedler_QA` — both zero errors, zero warnings;
  `lake build Scaffold.Mathlib.GraphTheory.Fiedler` and
  `lake build Scaffold.QA.SpectralGraph.Fiedler_QA` ✔; full `lake
  build` ✔ (2179 targets — the new module in the umbrella); all
  twenty-five QA modules elaborated directly in one batch (zero
  failures; the only diagnostics are the documented pre-existing
  linter notes in untouched modules); 435 QA declarations (+57), no
  `sorry`/`admit` anywhere under `Scaffold/` (the only textual matches
  are prose in comments); 16 explicit cited axioms (unchanged — pure
  hard crust); all hygiene scripts pass (`lint_axioms`,
  `check_citations`, `check_markdown_links`); scoreboard regenerated
  (435/16/0) with verification rows and the milestone bullet; radar
  re-scored per protocol (subject axis 4: 3.0 → 3.5, recorded; QA-axis
  count synced 435/25; proved-depth and reuse text extended); README
  snapshot (axis-4 cell); SGT index map (new `Fiedler` section);
  backlog item 4; proposal delivery record; `proposals/README.md`
  (Fiedler → Medium). Concurrent additions preserved untouched
  (untracked `proposals/repair-and-retire-woodbury.md` and its
  priority-table row, which appeared mid-run).

- 2026-08-18 (audit-and-finish of the uncommitted normalized-Cheeger
  milestone): no source changes — re-verification of the delivered
  `cheeger_upper_bound` retirement and closure of the milestone's
  records. Direct elaboration (`lake env lean`) of
  `GraphTheory.Spectral`, `GraphTheory.Cheeger`, and
  `QA.SpectralGraph.Cheeger_QA` — zero errors (Cheeger QA zero
  warnings; remaining linter notes verified pre-existing in HEAD,
  outside the diff hunks); explicit `lake build` of the three targets
  ✔; full `lake build` ✔ (2178 targets); `lint_axioms` (16 covered),
  `check_citations`, `check_markdown_links` pass; scoreboard
  regeneration byte-identical (16/378/0 re-derived from source;
  Cheeger QA 33); activity log's 6 self-introduced
  trailing-whitespace metadata lines stripped (older entries'
  illustrative hard breaks untouched); unrelated working-tree changes
  preserved; no commit.

- 2026-08-18 (`cheeger_upper_bound` retirement: Cheeger easy direction
  proved, axiom 17 → 16): `lake env lean` on `GraphTheory.Spectral`
  and `GraphTheory.Cheeger` (zero errors; only pre-existing linter
  notes in untouched code) and on `QA.SpectralGraph.Cheeger_QA`
  (zero errors, zero warnings); `lake build
  Scaffold.Mathlib.GraphTheory.Spectral` and
  `lake build Scaffold.Mathlib.GraphTheory.Cheeger` ✔; full `lake
  build` ✔ (2178 targets); all
  twenty-four QA modules elaborated directly in one batch (exit 0,
  zero failures); 378 QA declarations (+7), no `sorry`/`admit`
  anywhere under `Scaffold/` (textual matches are prose in comments);
  16 explicit cited axioms (−1: `cheeger_upper_bound` retired to a
  proved theorem at identical name/hypotheses/statement, proved from
  the new general-operator `secondEval_variational` with
  `lambda2_variational` re-proved as a corollary at unchanged shape);
  all hygiene scripts pass (`lint_axioms`, `check_citations`,
  `check_markdown_links`); scoreboard regenerated (16/378/0) with
  verification rows and a milestone note; radar re-scored per protocol
  (subject axis 4: 2.5 → 3.0; axiom-minimization trend recorded; QA
  count synced 378/24; proved-depth and reuse text updated); README
  snapshot (16 axioms, 378 QA, axis-4 cell); both Cheeger indexes;
  backlog item 3; `proposals/README.md` (proposal → Delivered with
  residuals) and the proposal's delivery record updated. Unrelated
  concurrent working-tree changes (`.opencode/`, `AGENTS.md`,
  `scripts/opencode-pursue`, `scripts/README.md`,
  `proposals/sell-the-methodology.md`,
  `proposals/retire-the-mushy-center.md`,
  `scripts/test_opencode_pursue.sh`, untracked `proposals/README.md`)
  were preserved untouched.

- 2026-08-18 (`lambda2_variational` retirement: proved Courant–Fischer,
  axiom 18 → 17): `lake env lean` on `GraphTheory.Spectral` (zero
  errors; zero new warnings — the seven pre-existing linter notes are
  untouched code) and on `QA.SpectralGraph.Variational_QA` (zero
  errors); `lake build Scaffold.QA.SpectralGraph.Variational_QA` ✔;
  full `lake build` ✔ (2178 targets); all twenty-four QA modules
  elaborated directly in one batch (zero failures); 371 QA
  declarations (+26), no `sorry`/`admit` anywhere under `Scaffold/`
  (textual matches are prose in comments); 17 explicit cited axioms
  (−1: `lambda2_variational` retired to a proved theorem restated with
  the load-bearing `hnonneg` hypothesis); all hygiene scripts pass
  (`lint_axioms`, `check_citations`, `check_markdown_links`);
  scoreboard regenerated (17/371/0) with prose synced; radar re-scored
  per protocol (subject axis 3: 3.0 → 3.5; axiom minimization 3.5 →
  4.0; QA count synced 371/24); README snapshot (17 axioms, 371 QA);
  both source indexes and the SGT index map updated; both proposals'
  status notes updated with the delivery and the normalized-instance
  scope caveat.

- 2026-08-18 (electrical-crust step 6: one-sided Dirichlet bound,
  program complete): `lake env lean` on `GraphTheory.Electrical` and on
  `QA.SpectralGraph.EffectiveResistance_QA` — both zero errors, zero
  warnings; `lake build Scaffold.QA.SpectralGraph.EffectiveResistance_QA`
  ✔ (2012 targets); full `lake build` ✔ (2178 targets); all twenty-four
  QA modules elaborated directly in one batch (zero errors — the only
  outputs are pre-existing `unusedSectionVars` warnings in untouched
  modules); 345 QA declarations (+9), no `sorry`/`admit` anywhere under
  `Scaffold/` (the only textual matches are prose in comments); 18
  explicit cited axioms (unchanged — pure hard crust); all hygiene
  scripts pass (`lint_axioms`, `check_citations`,
  `check_markdown_links`); scoreboard regenerated and its prose synced;
  SGT index map (4 new `Electrical` rows), backlog item 7, radar
  (subject axis 6: 2.5 → 3.0 recorded per protocol; QA-axis count
  synced to 345/24), README snapshot, and proposal checklist (all six
  steps ✅) updated.

- 2026-08-18 (electrical-crust step 5: effective resistance): `lake
  env lean` on `GraphTheory.Electrical` and on
  `QA.SpectralGraph.EffectiveResistance_QA` — both zero errors, zero
  warnings; `lake build Scaffold.QA.SpectralGraph.EffectiveResistance_QA`
  and `lake build Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter`
  (downstream consumer of the changed dependency chain) ✔; full `lake
  build` ✔ (2178 targets — the new module in the umbrella); all
  twenty-four QA modules elaborated directly in one batch (exit 0,
  zero failures); 336 QA declarations (+17), no `sorry`/`admit`
  anywhere under `Scaffold/` (the only textual matches are prose in
  comments and the `Scaffold/Trusted/README.md` quarantine
  explanation); 18 explicit cited axioms (unchanged — pure hard
  crust); all hygiene scripts pass (`lint_axioms`, `check_citations`,
  `check_markdown_links`); scoreboard regenerated; SGT index map
  (new `Electrical` section), backlog item 7, radar (subject axis 6:
  2.0 → 2.5, recorded per protocol), README snapshot, and proposal
  checklist updated (steps 1–5 of 6 delivered).

- 2026-08-18 (electrical-crust step 4: potential solvability): `lake
  env lean` on `GraphTheory.Spectral` (zero errors, zero new warnings —
  the eight pre-existing linter notes are untouched code) and on
  `QA.SpectralGraph.PotentialSolvability_QA` (zero errors, zero
  warnings); `lake build Scaffold.QA.SpectralGraph.PotentialSolvability_QA`
  and `lake build Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter` (a
  downstream consumer of the changed module) ✔; full `lake build` ✔
  (2177 targets); all twenty-three QA modules elaborated directly in
  one batch (exit 0, zero failures); 319 QA declarations (+12), no
  `sorry`/`admit` anywhere under `Scaffold/`; 18 explicit cited axioms
  (unchanged — pure hard crust); all hygiene scripts pass
  (`lint_axioms`, `check_citations`, `check_markdown_links`);
  scoreboard regenerated; SGT index map, backlog item 7, radar (subject
  axis 6: 1.5 → 2.0, recorded), README snapshot, and proposal
  checklist updated. Environment note: ~300 Mathlib oleans were found
  pruned at run start (recorded environment debt); the modules needed
  by the changed files, their consumers, and the full default build
  were all present and used — no cache fetch was required this run.

- 2026-08-18 (electrical-crust step 3: kernel-equality bridge):
  `lake env lean` on `GraphTheory.Spectral` (zero errors; zero *new*
  warnings — the pre-existing linter notes are untouched code) and on
  `GraphTheory.SimpleGraphAdapter` and
  `QA.SpectralGraph.KernelBridge_QA` (both zero errors, zero
  warnings); `lake build Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter`
  ✔; full `lake build` ✔ (2177 targets); all twenty-two QA modules
  elaborated directly in one batch (exit 0, zero failures); 307 QA
  declarations (+14), no `sorry`/`admit` anywhere under `Scaffold/`;
  18 explicit cited axioms (unchanged — pure hard crust); all hygiene
  scripts pass (`lint_axioms`, `check_citations`,
  `check_markdown_links`); scoreboard regenerated; SGT index map,
  backlog item 7, radar (subject axis 6: 1.0 → 1.5, recorded), and
  proposal checklist updated.

- 2026-08-18 (SimpleGraph→WAdj adapter): `lake env lean` on
  `GraphTheory.SimpleGraphAdapter` and on
  `QA.SpectralGraph.SimpleGraphAdapter_QA` — both zero errors, zero
  warnings; `lake build` of both targets ✔; full `lake build` ✔
  (2177 targets); all twenty-one QA modules built directly in one
  batch (exit 0); 293 QA declarations (+38), no `sorry`/`admit`
  anywhere under `Scaffold/`; 18 explicit cited axioms (unchanged —
  pure hard crust); `lint_axioms`, `check_citations`,
  `check_markdown_links` pass; scoreboard regenerated; SGT index map,
  backlog item 7, radar (interop 4.0 → 4.5, models 3.0 → 3.5,
  recorded), and README snapshot/maturity synced. Environment: pruned
  `.lake/build` restored via the recorded interpreter cache fetch +
  2008-target residue recompile before checks.
- 2026-08-18 (electrical-crust step 1: connectivity/kernel): `lake env
  lean` on `GraphTheory.Spectral` (zero errors; zero *new* warnings —
  the six pre-existing linter notes are untouched code) and on
  `QA.SpectralGraph.Connectivity_QA` (zero errors, zero warnings);
  `lake build Scaffold.Mathlib.GraphTheory.Spectral` and
  `lake build Scaffold.QA.SpectralGraph.Connectivity_QA` ✔; full
  `lake build` ✔ (2171 targets); 255 QA declarations (15 new), no
  `sorry`/`admit` anywhere under `Scaffold/`; 18 explicit cited axioms
  (unchanged — pure hard crust); all hygiene scripts pass
  (`lint_axioms`, `check_citations`, `check_markdown_links`);
  scoreboard regenerated; SGT index map, backlog item 7, and radar
  updated with recorded re-scores (subject axis 6: 0.5 → 1.0, subject
  axis 1: 2.5 → 3.0, assurance Mathlib interop: 3.5 → 4.0).
- 2026-08-18 (Cheeger statement-shape repair): `lake env lean` on
  `GraphTheory.Spectral`, `GraphTheory.Cheeger`, and
  `QA.SpectralGraph.Cheeger_QA` pass with zero errors and zero
  warnings; all nineteen QA modules and the changed public modules
  built directly; full `lake build` passes (2161 targets); 240 QA
  declarations (19 new), no `sorry`/`admit`; 18 explicit cited axioms
  (unchanged); both Cheeger axioms restated at the corrected
  `secondEval (L_sym)` spectral side with the old shape refuted in
  proved form; radar QA axis re-scored 3.5 → 4.0 (recorded); all
  hygiene scripts pass; scoreboard, radar, `index/map/spectral_graph`,
  and `index/sources/chung_spectral_graph` updated.
- 2026-08-17 (variational transfer / second interface consumer):
  direct elaboration and `lake build` of
  `Scaffold.Mathlib.GraphTheory.VariationalTransfer` and
  `Scaffold.QA.SpectralGraph.VariationalTransfer_QA` pass clean; full
  `lake build` passes with the module in the umbrella (1997 targets);
  221 QA declarations (15 new), no `sorry`/`admit`; 18 explicit cited
  axioms (unchanged — pure hard crust); radar reuse 3.5 → 4.0 and
  subject axis 3 (variational) 2.5 → 3.0 recorded; all hygiene scripts
  pass; SGT index map updated.
- 2026-08-17 (exhaustive/falsification QA): `lake build` passes; direct
  elaboration and `lake build` of
  `Scaffold.QA.SpectralGraph.Exhaustive_QA` pass with zero errors and
  zero warnings; 206 QA declarations (87 new), no `sorry`/`admit`; 18
  explicit cited axioms (unchanged — pure hard crust); exhaustive
  decide-certified cut sweeps on both fixtures, duality recomposed from
  computed tables, negative witnesses (conductance `1/2` vs `1`,
  Rayleigh `8/3` vs `0`, asymmetric duality failure `2 ≠ 1`), walk row
  sums computed; radar QA re-scored 3.0 → 3.5 (recorded); all hygiene
  scripts pass.
- 2026-08-17 (walk-Laplacian kernel / RandomWalk consumer): `lake
  build` passes; 119 QA declarations, no `sorry`/`admit`; 18 explicit
  cited axioms (unchanged); `Stationary` consumes both interface
  modules; radar reuse 3.0 → 3.5 recorded; all hygiene scripts pass.
- 2026-08-17 (stationary structure): `lake build` passes with
  `GraphTheory.Stationary` in the umbrella; twenty public modules and
  seventeen QA modules (116 declarations) compile directly with no
  `sorry`/`admit`; 18 explicit cited axioms (unchanged); downstream
  reuse radar score 2.5 → 3.0 recorded; all hygiene scripts pass.
- 2026-08-17 (cut duality): `lake build` passes; 107 QA declarations
  (new `SpectralGraph/Cuts_QA.lean`), no `sorry`/`admit`; 18 explicit
  cited axioms (unchanged); cut duality proved in the center
  (`vol_compl`, `boundary_compl`, `conductance_compl`,
  `boundary_empty`, `boundary_univ`); all hygiene scripts pass.
- 2026-08-17 (irregular walk form): `lake build` passes; 96 QA
  declarations, no `sorry`/`admit`; 18 explicit cited axioms (unchanged);
  general `walkTransitionMatrix` with row-stochasticity, `walkLaplacian`,
  and the similarity identity `√D · L_walk · (1/√D) = L_sym` proved;
  all hygiene scripts pass.
- 2026-08-17 (irregular normalized Laplacian): `lake build` passes with
  `GraphTheory.Normalized` in the umbrella; nineteen public modules and
  fifteen QA modules (93 declarations) compile directly with no
  `sorry`/`admit`; 18 explicit cited axioms (unchanged — pure hard
  crust); `lint_axioms`, `check_citations`, `check_markdown_links` all
  pass.
- 2026-08-17 (broad-SGT backlog + random-walk interfaces): `lake build`
  passes with `GraphTheory.RandomWalk` in the umbrella; eighteen public
  modules and fourteen QA modules (82 declarations) compile directly
  with no `sorry`/`admit`; 18 explicit cited axioms (unchanged — the
  increment is pure hard crust); `lint_axioms`, `check_citations`,
  `check_markdown_links` all pass; `docs/6_SGT_BACKLOG.md` published and
  linked.
- 2026-08-17 (citation hygiene + tightening): `lake build` passes;
  explicit axioms reduced 19 → 18 (`spectral_gap_stability` now proved
  from `weyl_inequality`); `davis_kahan_sin_theta` separation tightened
  to the single-pair two-cluster form (derived wrapper simplified to one
  Weyl fact; QA reduces the pairwise form via `evals_sorted`); Chung
  index provenance note corrected against git history; Weyl doc records
  the norm-corollary relation; `lint_axioms`, `check_citations`,
  `check_markdown_links` all pass; 75 QA declarations, no `sorry`/`admit`.
- 2026-08-17 (projector algebra): `lake build` passes; all seventeen
  public modules and all thirteen QA modules (75 declarations) compile
  directly with no `sorry`/`admit`; eigenbasis orthonormality
  (`eigvecOf_inner`) and completeness (`eigvecOf_complete`) proved from
  the Mathlib spectral-theorem API; `spectralProjector_idempotent`,
  `initialProjector_idempotent`, `spectralProjector_eq_zero`,
  `spectralProjector_eq_one` proved; new QA
  file `SpectralGraph/Projector_QA.lean` (5 declarations).

## Blockers

- The native Mathlib cache executable fails on this macOS environment with a
  dyld segment error. Cached artifacts were obtained through the recorded Lean
  interpreter workaround; this is environment debt, not an SGT source failure.
