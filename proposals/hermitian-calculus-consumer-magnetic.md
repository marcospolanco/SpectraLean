# Proposal: A Genuinely Complex Magnetic-Laplacian Calculus Consumer

**Status:** COMPLETE — delivered 2026-08-25 (run `20260825T180957Z-run-1`),
one run, Steps 0+1 together. The gate below was satisfied by the
2026-08-25 bridge delivery (`proposals/hermitian-functional-calculus-bridge.md`,
Steps 1–3 delivered; complex half confirmed by its QA witness
`fcM2c_cfc_id`). Zero new axioms (count stays 10; `#print axioms` via
`wip/magcfc_axcheck.lean` on all 30 audited declarations — 8 public +
22 accessible QA — reads exactly `propext, Classical.choice,
Quot.sound`, every one). QA +22 (2216 → 2238,
`Scaffold/QA/SpectralGraph/MagneticCalculus_QA.lean` a new file).
Originally a gated stub — Step 5 of
[hermitian-functional-calculus-bridge.md](hermitian-functional-calculus-bridge.md),
named there as a separate consumer per the one-shape-per-proposal
discipline. The record of that gate (kept for provenance): do not
begin until the bridge's Steps 1–3 are delivered **and** the
complex-Hermitian half of the calculus (not just real-symmetric) is
confirmed working by Step 0's API-split check.

## What was delivered

The ask was: the operator via the calculus wrapper, its eigenvector
action at `magneticLaplacian`'s (complex) eigenbasis, and one QA
fixture on a small directed graph with nonzero phase checked against
a hand computation, the same two-independent-routes discipline used
throughout this shelf. All three, plus a general engine the complex
half was missing:

- **`cfc_mulVec_eq_smul_of_mulVec_eq_smul`** (public, `𝕜`-generic
  RCLike): the calculus acts at eigenvalues on **every** eigenvector —
  if `M *ᵥ x = (μ : 𝕜) • x` at a Hermitian `M` and real `μ`, then
  `hM.cfc f *ᵥ x = (f μ : 𝕜) • x` — by pure matrix algebra through
  the unitary diagonalization `Uᴴ * M * U = diagonal λ` (the shifted
  eigenvector equation transfers to the diagonal side via the
  unitary; support at the eigenvalue is read off entrywise; the
  diagonal action reassembled through the unitary again). No
  eigenspace-completeness machinery anywhere. Mathlib's
  `HermitianFunctionalCalculus.lean` has no such lemma; this is the
  interface every downstream complex consumer needs, and the
  delivered real-basis actions could not have expressed it.
- **`magneticHeat A Θ t`** (public definition): the propagator —
  `(magneticLaplacian_isHermitian A Θ).cfc (fun x =>
  Real.exp (-(t * x)))` at 𝕜 = ℂ through the `RCLike`-generic `cfc`
  directly, **no second wrapper** (the bridge's Step-0 verdict),
  hypothesis-free by the magnetic Laplacian's structural Hermiticity:
  defined for any real (asymmetric included) weights and any phases.
- The interface layer (all public, all in the new "magnetic heat
  propagator" section of `GraphTheory/FunctionalCalculus.lean`;
  `Magnetic.lean` untouched per the consumer pattern, one new import
  — Magnetic, no cycle): `magneticHeat_apply` (the entry form — the
  falsifiability anchor, the complex mirror of `spectralCalc_apply`),
  `magneticHeat_mulVec_of_eigen` (the arbitrary-eigenvector action —
  the consumer interface), `magneticHeat_mulVec_eigenvectorBasis`
  (the proposal's literal basis-action ask, as a corollary),
  `continuousOn_of_finite_spectrum` (the `𝕜`-generic continuity
  supplier), `magneticHeat_zero` (t = 0 ⇒ 1 through `cfc_const`),
  and `magneticHeat_mul_magneticHeat` (the semigroup through the
  generic calculus algebra — `cfc_mul`/`cfc_congr` at
  `Real.exp_add`, the complex instantiation of the delivered
  `spectralCalc_exp_mul` technology).

### QA (the new `MagneticCalculus_QA.lean`, five sections)

The fixture: the flux pair `K₂` at antisymmetric phase `π/2` —
`M = !![1, -I; I, 1]`, genuinely complex Hermitian (the conjugate-pair
off-diagonals pinned raw; Hermitian verified on directed-flux input).
The balanced potential `![I, 1]` is in the kernel (cross-checked
against the delivered gauge characterization **by two routes**: the
iff theorem at the verified balanced-potential condition, and the raw
energy collapse at the zero action); the frustrated mode `![I, -1]`
sits at eigenvalue `2` (raw arithmetic). The propagator's actions
come through the public eigen-action theorem (calculus route: the
kernel mode provably flux-invariant, `e⁰ = 1`; the frustrated mode
decaying at `e^{-2t}`), and the hand-derived closed form
`½ !![1+q, I(1-q); -I(1-q), 1+q]` at `q = e^{-2t}` is verified by
**raw matrix arithmetic** (route 2 — no calculus anywhere) and then
*reconciled*: `magC_heat_closed` derives the closed form from the
calculus route through the spanning-recovery helper (`magC2_eq_of_action`:
actions on a spanning pair determine the matrix; the explicit
combination certificate is a hypothesis, so the helper serves any
spanning pair). Pins: time zero (public theorem + raw cross-check at
`q = 1`), the semigroup law, Hermiticity of the propagator. Fences:
the **diffusion fence** `magneticHeat … 1 ≠ 1` — `e^{-2} < 1` forces
the off-diagonal entry `I(1-q)/2 ≠ 0`, so phase frustration provably
moves mass, refuting any constant-collapse reading. The **zero-phase
join**: at vanishing flux the magnetic propagator IS the
complexification of the delivered real `heatKernel` (`magC_coe`,
entrywise) — proved through the spanning family of the classical
eigenvectors, with the real side acting through `Heat.lean`'s series
engine `exp_mulVec_eq_smul_of_mulVec_eq_smul` (eigenvalue `0` and
`2` on `K₂`'s Laplacian, raw) — Mathlib's `cfc` and the exponential
series, two independent proof technologies agreeing on one operator.

## Verification

Spike first (`wip/magcfc_spike.lean` + `wip/magcfc_qa_spike.lean`,
several rounds to green before any module touched); `lake env lean`
zero errors/warnings on both the public module and the QA file;
explicit `lake build` targets ✔ (module 2325/2325, QA 2326/2326);
`#print axioms` via `wip/magcfc_axcheck.lean` — the standard three
only, all 30 audited; **full `lake build` ✔ (2385 targets, "Build
completed successfully") immediately followed by
`check_build_completeness.py` — 107/107 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (2238/10/0,
idempotent).

### Pin technique (the recurring traps this fixture recorded)

- `rw [RCLike.real_smul_eq_coe_smul]` on a coerced basis vector gets
  the instance search stuck (`IsScalarTower ℝ ?m (V → ℂ)`) — the
  durable route is entrywise: `funext i` then `Pi.smul_apply` twice
  plus `Complex.real_smul` on the entry.
- The generic-CFC lemma `cfc_const_one` leaves `R` ambiguous
  (`CommSemiring ?R` stuck) — name `R := ℝ` and pass the
  self-adjointness hypothesis explicitly, `cfc_const (1 : ℝ) M hsa`
  (the Tikhonov delivery's `cfc_const` pattern, not `cfc_one`).
- Full `simp` on flux-pair entries pushes `magC_q t` open to
  `Complex.exp (-(2 * ↑t))` and re-powers `I * I` to `I ^ 2`,
  defeating `ring` (atom mismatch) — the durable route for the
  closed-form action entries is controlled `simp only` at the matrix
  level plus `linear_combination (norm := ring_nf)` against
  `Complex.I_mul_I` (the ring_nf normalizer identifies `I * I` and
  `I ^ 2` on both sides of the certificate, so one certificate closes
  either surface form).
- `Complex.exp (I * (π/2))` is best evaluated by `mul_comm` then
  `Complex.exp_mul_I` (complex-typed at this pin) plus
  `Complex.cos_ofReal_re`/`sin_ofReal_re`; the negated phase by
  `Complex.exp_neg` at the positive-phase result (avoids the fragile
  `↑(−π/2)`-to-`−(↑π/2)` coercion shuffle).
- The QA spike initially saw the new public theorems through the
  stale pre-edit `.olean` — rebuild the public module before spiking
  QA against it (the Heat delivery's recorded trap, recurring).
- The ℕ-vs-ℂ elaboration of the bare literal `2 • v` in a statement
  (`(2 : ℕ) • v` was chosen where `(2 : ℂ) • v` was needed) — write
  the scalar's type explicitly in eigenvalue statements.

## Explicit non-goals (held)

No magnetic Cheeger inequality, synchronization/frustration
functional, or eigenvalue-gap statement for `M` — `Magnetic.lean`'s
own proposal priced these as separate, consumer-gated follow-ons.
This delivery is the calculus-built operator exhibited and proved
correct, nothing further.

## Priced follow-ons

- The **magnetic spectral layer** (eigenvalues of `M`, magnetic
  Cheeger, synchronization functionals) — still gated on a consumer
  naming a bound, per `magnetic-laplacian.md`'s standing note; this
  delivery's `cfc_mulVec_eq_smul_of_mulVec_eq_smul` is the interface
  such a consumer would enter through.
- A **magnetic resolvent** or square-root/positive-part construction
  (the proposal's own named alternatives if heat proved costly — heat
  did not; these remain unpriced alternatives).
- General-spectrum normal equations for the real calculus (the
  Tikhonov sibling's recorded follow-on), now with the complex
  action engine available for a complex analogue.

## Companion

[Hermitian Functional-Calculus Bridge](hermitian-functional-calculus-bridge.md)
(the gate), [The Magnetic Laplacian](magnetic-laplacian.md) (the
consumed object).
