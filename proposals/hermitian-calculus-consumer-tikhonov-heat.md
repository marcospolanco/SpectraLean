# Proposal: Recovering Tikhonov / Heat as Functional-Calculus Instances

**Status:** **COMPLETE — both halves delivered 2026-08-25.** The
Tikhonov half (the smaller reconciliation gap, per the parent
proposal's Step-0 pricing) landed first; the Heat half — the one with
genuine mathematical content, a reconciliation of two independently
built proof stacks — landed later the same day as the sibling's own
separately-authorized follow-on (see the Heat delivery record below).
The gate was satisfied by the Hermitian functional-calculus bridge
delivery earlier that day.

## The ask, once unblocked

Pick **one** of `Tikhonov.lean`'s `tikhonovShrinkage`/`tikhonovMinimizer`
family or `Heat.lean`'s `heatKernel`, and prove it equals the general
calculus wrapper applied to the corresponding scalar function
(`π ↦ π/(λ+π)` for Tikhonov, `t ↦ e^{-tλ}` for heat) — an equality
theorem, not a restatement. This is the bridge's actual falsifiability
test at a real consumer: a wrong calculus specialization contradicts an
already-proved, independently-delivered definition.

Pick the one with the smaller reconciliation gap between its own proof
route and the calculus's unitary-diagonalization route — Step 0 of
the parent proposal should note which, if either, is obviously cheaper;
otherwise decide at the start of this proposal's own (future) Step 0.

## Explicit non-goals

Do not attempt both Tikhonov and Heat in one delivery — pick one,
finish it, and this document (or a sibling) covers the other as its own
separately-authorized follow-on. Do not restate this as "the calculus
generalizes Tikhonov/Heat" — the existing modules stay as delivered;
this is an equality theorem bridging them to the new interface, additive
only.

## Companion

[Hermitian Functional-Calculus Bridge](hermitian-functional-calculus-bridge.md)
(the gate), [Tikhonov Shrinkage Filter](tikhonov-shrinkage-filter.md),
[Reversibility and Heat Semigroup](reversibility-and-heat-semigroup.md).

## Delivery record (2026-08-25, run `20260825T145722Z-run-1`)

**Delivered, pure hard crust, zero new axioms (count stays 10;
`#print axioms` via `wip/tikcfc_axcheck.lean` on all 19 new
declarations — 3 public + 16 QA — reads exactly `propext,
Classical.choice, Quot.sound`, every one). QA 2189 → 2205
(+16 in `FunctionalCalculus_QA.lean`'s Section E, no new file).**

**The equality theorem** (`GraphTheory/FunctionalCalculus.lean`, the
"Recovered instances" section — `Tikhonov.lean` untouched per the
non-goals):

`tikhonovMinimizer_eq_spectralCalc_mulVec` — `x* = f(L) *ᵥ y` at
`f = tikhonovShrinkage π`, **hypothesis-free** (holds at every `π`,
both sides carrying the same junk values when `π` hits `-λ_k`; the
bridge's `spectralCalc_mulVec_apply` was stated in exactly the
minimizer's filter-sum shape, so the proof is the definition identity —
the reconciliation gap the parent pricing predicted, confirmed). The
supporting public helper `continuousOn_of_finite_real_spectrum`
(every function continuous on a matrix's finite real spectrum, via
`Finite.instDiscreteTopology` — the supplier future CFC consumers need,
since `cfc_cont_tac`'s `fun_prop` cannot discharge spectrum-restricted
continuity of spectral-data functions).

**The substantive second layer — the normal equation re-derived
through the calculus algebra:**
`add_smul_one_mul_spectralCalc_tikhonovShrinkage` —
`(L + π•1) * f(L) = π • 1` under the same PSD + `0 < π` hypotheses as
the delivered `tikhonovMinimizer_add_smul_one_mulVec`, but proved via
Mathlib's generic CFC algebra (`cfc_add_const`, `cfc_id'`, `cfc_mul`,
`cfc_congr`, `cfc_const`, all reached through
`Matrix.IsHermitian.cfc_eq`): the pointwise identity
`shrink π λ · (λ + π) = π` holds *on the spectrum* (PSD + `0 < π` keep
the division non-junk at spectral points), and `cfc_congr` promotes it
to the operator identity — an eigenbasis-free route to a statement the
shelf had only through the eigenbasis expansion. Two routes, one
nontrivial statement, independently proved.

**QA (Section E of `FunctionalCalculus_QA.lean`, +16, on the
`Tikhonov_QA` `K₂` fixture):** the sign-free structure pins (kernel
outer products all `1/2`; `λ = 2` outer products `±1/2` — no
basis-orientation choice surviving anywhere); the master entrywise
lemma `fc_lapK2_calc` (for *arbitrary* `f`:
`f(L) = !![(f 0+f 2)/2, (f 0−f 2)/2; …]`); the calculus instance
pinned to `!![2/3, 1/3; 1/3, 2/3]` at `π = 1`; the **reconciliation
witnessed numerically** — through the equality theorem the calculus
routes `![1,0]` to `![2/3, 1/3]`, exactly the hand-solved Gaussian
value `tik_K2_eq` pinned in the original Tikhonov delivery (two
constructions, one number); the normal equation by **two independent
routes** (`fc_lapK2_normal_calculus` through the public calculus
chain vs `fc_lapK2_normal_hand` through the pinned hand-solved system)
plus a raw matrix-arithmetic check of the matrix statement; the
kernel-mode action instantiation (factor exactly `1`); and the **fence**
at `π = -2` — the junk shrinkage `0` at the spectral point `2 = -π`
drives `f(L)` to the pure kernel average, and the hypothesis-free
normal equation is refuted in proved form at the `(-1) ≠ 0` entry: the
`0 < π` hypothesis is load-bearing, not decorative.

**Verification:** spike first (`wip/tikcfc_spike.lean` +
`wip/tikcfc_qa_spike.lean`, the full routes green before any module
touched); `lake env lean` zero errors/warnings on both changed files;
explicit `lake build` targets ✔ (2301/2301, 2305/2305); `#print
axioms` all 19 at the standard three; **full `lake build` ✔ (2385
targets, "Build completed successfully") immediately followed by
`check_build_completeness.py` — 106/106 fresh, 0 stale, 0 missing,
exit 0** (a mid-verification `touch` of the module tripped the STALE
fence exactly as calibrated; remediated by the documented
artifact-removal + re-elaboration route); `lint_axioms` (10),
`check_citations`, `check_markdown_links` pass; scoreboard
regenerated (2205/10/0, idempotent by md5).

**Pin-technique list (for the Heat sibling):** the generic CFC lemmas
key on the predicate — pass `IsSelfAdjoint` ascriptions explicitly
(`have hsa : IsSelfAdjoint M := hherm`), never the `IsHermitian`
proof directly, or `rw` silently fails to match; `cfc_add_const`'s
`ha`/`hf` auto-params *do* resolve (aesop finds `IsSelfAdjoint`), so
only the continuity supplier needs passing; `cfc_congr`'s EqOn proof
must `dsimp`/`show` the beta-redex before `mul_div_cancel₀` (order:
`(λ+π) * (π/(λ+π)) = π` is `mul_div_cancel₀`, not `div_mul_cancel₀`);
`algebraMap ℝ (Matrix) π = π • 1` entrywise via
`Matrix.algebraMap_matrix_apply` (no `Matrix.smul_one` at this pin);
`fin_cases` on `Fin 2` binders leaves `(fun i => i) ⟨0, ⋯⟩` redexes —
per-branch definitional `show` at numeral indices; outer-product pins
stated in raw `v a * v b` form (not `^2`) so `mul_assoc`-then-rewrite
matches the goal's `(f λ * v a) * v b` shape.

**Priced follow-ons:** the Heat half of this stub (`heatKernel A t =
spectralCalc L (fun λ => Real.exp (-(t) * λ))` — the `NormedSpace.exp`
route's reconciliation, expected a genuine proof not a definitional
identity, hence its own authorization); the resolvent identity
`f(L) = π • (L + π•1)⁻¹` under invertibility (one `cfc_inv` step from
the delivered normal equation); the general-symmetric normal equation
(spectrum-avoidance hypothesis in place of PSD + `π > 0`).

## Delivery record, the Heat half (2026-08-25, run `20260825T163517Z-run-1`)

**Delivered, pure hard crust, zero new axioms (count stays 10;
`#print axioms` via `wip/heatcfc_axcheck.lean` on all 15 new
declarations — 4 public + 11 QA — reads exactly `propext,
Classical.choice, Quot.sound`, every one). QA 2205 → 2216 (+11 in
`FunctionalCalculus_QA.lean`'s Section F, no new file). The parent
pricing's prediction confirmed: this reconciliation is the one with
mathematical content.**

**The equality theorem** (the "Recovered instances: the heat
semigroup" section of `GraphTheory/FunctionalCalculus.lean` —
`Heat.lean` untouched per the non-goals; one new import, Heat, no
cycle): `heatKernel_eq_spectralCalc_exp` —
`heatKernel A t = spectralCalc (laplacian A) hL (fun x => Real.exp
(-(t * x)))` under `A.IsSymm`. The two sides were built by independent
proof stacks: the LHS through `NormedSpace.exp` and `Heat.lean`'s
from-scratch entrywise series machinery (summability from scratch
because the pin had no Pi-type `HasSum` lemmas, the eigenvector
engine, the eigenbasis expansion), the RHS through Mathlib's `cfc`.
Their agreement — in effect the spectral mapping theorem for `exp` at
real-symmetric matrices — is joined at exactly the shared filter-sum
shape (`heatKernel_mulVec_eq_sum` vs `spectralCalc_mulVec_apply`),
with the new public helper `matrix_eq_of_forall_mulVec_eq`
(actions on `Pi.single j 1` recover entries) doing the matrix lift.

**The substantive second layer — the semigroup law through the
calculus algebra:** `spectralCalc_exp_mul`
(`f_s(M) * f_t(M) = f_{s+t}(M)` at the exponential family, via
`cfc_mul` then `cfc_congr` promoting pointwise `Real.exp_add` from the
spectrum — an eigenbasis-free route), composed into
`heatKernel_mul_heatKernel_of_spectralCalc`, a second proof technology
for `Heat.lean`'s hypothesis-free `heatKernel_mul_heatKernel` (the
`Matrix.exp_add_of_commute` route); the docstring records honestly
that this route needs `A.IsSymm` where the original does not, and the
original remains primary.

**QA (Section F, +11, on the same `Tikhonov_QA` K₂ fixture as Section
E — the two consumer reconciliations pinned against one shared,
independently delivered eigenbasis):** the closed form
`!![(1±e^{-2t})/2]` by **two independent routes**
(`fc_heat_K2_calculus_route` through the equality theorem + the
Section-E master lemma vs `fc_heat_K2_series_route` through
`heatKernel_mulVec_eq_sum` + the sign-free outer-product pins — no
`cfc` anywhere); the semigroup at times `1, 2` by **two independent
routes** (`_calculus` through the new chain vs `_commute` through the
delivered law) plus `_pin` (both routes deliver the entries
`(1±e^{-6})/2`) and `_raw` (the literal closed-form product check,
`Real.exp_add` at `e^{-2}·e^{-4} = e^{-6}` the only scalar input);
time zero preserved through the calculus (`fc_heat_K2_zero_calculus`);
eigenmode decay through the calculus action interface at both modes
(`fc_heat_K2_kernel_action` factor `1`; `fc_heat_K2_mode_two_action`
factor `e^{-2t}` — the calculus-side mirror of the series-route
`heatKernel_mulVec_eigvecOf`); and the **nontriviality fence**
`fc_heat_K2_not_one` — `heatKernel K₂ 1 ≠ 1` (entry
`(1 - e^{-2})/2 > 0` since `e^{-2} < 1` by `Real.exp_lt_exp`),
refuting in proved form any degenerate reading that collapses the
exponential family to a constant (a junk calculus evaluating `f` only
at the kernel eigenvalue would return exactly `1`).

**Verification:** spike first (`wip/heatcfc_spike.lean` +
`wip/heatcfc_qa_spike.lean`, the full routes green before any module
touched — the public spike's one nontrivial catch was `Real.exp_add`'s
direction at this pin, `exp (x+y) = exp x * exp y`, so the
product-to-sum step needs `← Real.exp_add`; the QA spike's was the
documented `fin_cases` redex trap closing the raw product lemma —
per-branch definitional `show`s at numeral indices after a
`Matrix.mul_apply`/`Fin.sum_univ_two` pre-rewrite, plus a factor-2
correction in the off-diagonal `linear_combination` certificates);
`lake env lean` zero errors/warnings on both changed files; explicit
`lake build` targets ✔ (module 2309/2309, QA 2313/2313);
`#print axioms` all 15 at the standard three; **full `lake build` ✔
(2385 targets, "Build completed successfully") immediately followed
by `check_build_completeness.py` — 106/106 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10), `check_citations`, `check_markdown_links`
pass; scoreboard regenerated (2216/10/0, idempotent by md5).

**Priced follow-ons (post-Heat):** the magnetic heat propagator (the
second bridge consumer stub, its complex-half precondition already
discharged by the bridge delivery's QA witness); the resolvent
identity `f(L) = π • (L + π•1)⁻¹` under invertibility (one `cfc_inv`
step from the delivered normal equation); the general-symmetric
normal equation (spectrum-avoidance hypothesis in place of PSD +
`π > 0`).
