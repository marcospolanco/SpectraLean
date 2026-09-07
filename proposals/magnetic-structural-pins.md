# Proposal: The Magnetic Structural Facts' Positive Pins

**Status:** COMPLETE (delivered in the opening run, run
`20260907T042503Z-run-1`, session `ses_f85e4fd87ffeIAk10HRoxt2F0J`;
delivery record below)

## Why this, why now

The compiler-derived consumption census's largest remaining inert
cluster (per `wip/census_20260907_post2.txt`, 50 never-touched): **the
six Magnetic structural theorems** — the complex Hermitian layer's
action-level half, never consumed by any QA proof. The prior handoff
named the selection keys explicitly (cluster size first, name-weight
second); this is the largest cluster left AND carries the module's two
headline theorems. This is the pins method's fourth application (the
census → targeted first-consumption loop, after Tikhonov's 11, the
mixing-time interfaces' 10, and sparsification's 9) and its first
complex-valued target.

The gap the census found is real: `Magnetic_QA.lean`'s sections A–D
pin the FORM-level facts (the energy identity's value `5`, the
form-level gauge iff `magneticQuadForm_eq_zero_iff`, the zero-phase
cone agreement, the PSD nonnegativity fence) — all *beside* the
action-level layer. The kernel characterization
(`magneticLaplacian_mulVec_eq_zero_iff`, the statement shape the
signed-graph balance theorem consumes at the π-flux), the PSD theorem
itself, the real-valuedness promotion, the row-algebra reverse
direction, the kernel-to-form helper, and the unit-phase pairing were
referenced by no QA proof term.

**SGT leverage:** the magnetic Laplacian is the shelf's first and only
complex-valued object — the directed-axis slice behind the signed-graph
balance program. Its kernel characterization is load-bearing for the
π-flux balance theorem's exact statement shape; its structural spine
was unexercised. The pins put weight on every layer: both directions of
the kernel iff (including on genuinely directed input the form-level QA
never touched at kernel level), the PSD at asymmetric input, and the
real-part → complex-value promotion that every downstream complex
equality statement needs.

## Step 0: the census (exact)

The six never-consumed theorems:
`conj_exp_I_mul_exp_I`, `hermQuadForm_eq_zero_of_mulVec_eq_zero`,
`magneticLaplacian_mulVec_eq_zero_iff`,
`magneticLaplacian_mulVec_eq_zero_of_forall_exp_mul_eq`,
`magneticQuadForm_im_eq_zero`, `magneticQuadForm_re_nonneg`.

## Step 1: the pins (12 QA theorems, one section)

All at the delivered fixtures (the asymmetric `magA`/`magTheta` pair,
the π-flux `K₂` `magSym`/`magThetaPi`, the frustrated triangle
`magTri`/`magThetaTri`, the zero-phase `magSym`/`magThetaZero`) —
eleven pins plus the `magA_nonneg` hypothesis helper that discharges
the PSD/kernel-iff weights clause on genuinely directed input:

1. **The pairing pins (2):** the unit-phase pairing at `π`
   (`magPairing_pi_pin`) and at the genuinely complex phase `π/2` — the
   numeric identity `conj (I) · I = 1` derived THROUGH the theorem, not
   by direct `I·I` arithmetic (`magPairing_I_pin`; the deliberate
   `simpa … using h` route keeps the theorem in the proof term where
   `simp` alone would sever the dependency).
2. **The real-valuedness promotion (`magIm_pin`):** at the genuinely
   complex test vector `![1, I]` the form's imaginary part vanishes by
   the theorem, and the full complex value `2` is ASSEMBLED from the
   raw real energy plus that vanishing imaginary part — the promotion
   is load-bearing: `.re = 2` alone does not give `= 2`.
3. **The PSD pin (`magPSD_pin`):** the weights hypothesis discharged on
   genuinely directed input (`0/2/1/0`), the bound nonvacuous against
   the pinned energy `5` (`magEnergy_pin`).
4. **The action-kernel pins (3):** the row-algebra reverse direction at
   the π-flux edge (`magK2_mulVec_zero`); the form-level kernel
   membership re-derived through the ACTION route —
   `magK2_antipodal_kernel`'s pinned conclusion via `M *ᵥ x = 0` plus
   the helper (`magK2_action_form_zero`); and the kernel iff's reverse
   direction at zero phase (`magZero_mulVec_kernel`).
5. **The classical join (`magZero_mulVec_kernel_classical`):** the SAME
   zero-phase action-kernel fact through the independent CONE-AGREEMENT
   route (entrywise the complexified classical Laplacian, whose
   constant-kernel property is raw `1 - 1 = 0` arithmetic) — two
   engines for one pinned fact, each failing if its own layer is wrong.
6. **The forward-direction pins (3):** the frustrated triangle's kernel
   forces every potential to vanish (`magTri_kernel_frustrated`); the
   NEGATIVE action-level witness — the constant potential is NOT
   killed, THROUGH the iff's forward direction (`magTri_const_action_
   ne_zero`, failing were the kernel larger than the aligned
   potentials); and **the directed-frustration headline**
   (`magAsym_kernel_trivial`): the asymmetric fixture's phase pair
   (`π` vs `π/2`) forces the trivial kernel on GENUINELY DIRECTED
   input (`x₀ = -x₁` and `x₁ = I·x₀` give `(1 + I)·x₀ = 0`) — the
   kernel characterization exercised on the module's own design
   fixture, never before touched at action level.

## QA obligation

The pins are the QA. No shelf change; zero axiom contact.

## Residue, priced

The kernel iff's `hA` clause is fenced on the PSD side already
(`magSigned_PSD_refuted`, Section D: the hypothesis-free conclusion is
false). A necessity fence for the IFF's `hA` on its forward half (a
signed fixture where `M *ᵥ x = 0` holds with the alignment failing)
is subtle: on the natural signed candidates the kernel equations force
the alignment anyway (the one-negative-edge `K₂` at zero phase has
kernel exactly the aligned constants), so a genuine breaker needs a
cancelation witness the energy identity's signed sums make possible
but not obvious. Priced as a follow-up; not blocking (the ⇐ half is
hypothesis-free, so the iff's statement shape is already exercised in
both directions by the pins).

## Delivery record (2026-09-07)

DELIVERED at the full designed scope in the opening run: 12 QA
theorems (the pin eleven plus the `magA_nonneg` hypothesis helper) in
`Magnetic_QA.lean`'s new `StructuralPins` section (16 → 28 by the
generator metric; QA 6594 → 6606), QA-only, zero axiom contact
(`#print axioms` via `wip/magpins_axcheck.lean` on all 12 — every one
exactly `propext, Classical.choice, Quot.sound`; no `-- @refutes`
tags — theorem instantiations of an all-proved shelf; the 24-tag
independence check unchanged and clean).

**Consumption closure, verified by the tool**: the census re-run
(`wip/census_20260907_post3.txt`) shows exactly the 6 targeted
theorems leaving the inert set — value-consumed 1307 → 1313,
never-touched 50 → 44, the `Magnetic (6)` line gone from the inert
list, every other module's inert set unchanged: no bonus, no
collateral.

Verification: spike-first (`wip/magpins_spike.lean` — green after three
fix rounds; the recorded traps: the pushed-coercion phase shape — the
energy sum's `Θ 1 0 = π/2` surfaces as `↑π/2`, needing the
`magExp_half_pi` form where the alignment discharges surface as
`↑(π/2)` needing `magExp_half_pi_raw`; `Complex.I_mul_I` (not
`mul_I`) as the pinned Mathlib name; `rw` rewriting ALL syntactic
occurrences at once so a doubled rw-list entry fails; the `fin_cases`
eta-expanded `Fin 2` binder needing an explicit `show` per branch; and
`norm_num … at h` closing its target outright, which severs a pin's
proof-term dependency — the `simpa … using h` route instead). The
landed module elaborates with zero errors/warnings; explicit build ✔;
**full `lake build` + `check_build_completeness.py` — 135 source files,
135 fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` exit
0 (4 axioms unchanged); `check_refutation_independence` (24-tag clean);
`check_public_reachability` (63 modules); `check_citations`;
`check_markdown_links`; `check_qa_name_uniqueness` (the new `mag*`
names collision-free); `check_backlog_freshness` clean; scoreboard
regenerated (6606) with the verification row; map freshness exit 0
after the 6594 → 6606 stats sync in both map data tables and SVG
regeneration (49 stations, no status change — none owed).

Remaining risk: none owed — QA-only, no axiom disposition changed, no
public statement changed. QA proves consequences relative to the
substrate; it does not prove the substrate (no axiom touched). Honest
scope: the pins are at the module's own four fixtures (`Fin 2`/`Fin 3`,
phases from `{0, π/2, π}`); the classical join at the one symmetric
zero-phase fixture; the iff's `hA` forward-half fence priced above.
