# Proposal: Heat-Variance Decay — the Poincaré Follow-On

**Status:** COMPLETE — proposed and delivered in the same run
(`20260831T175959Z-run-1`), per the same-run pattern of
`poincare-inequality.md` and `total-variation-mixing-conversion.md`.
This is the Poincaré delivery's own named deferred follow-on (its
Deferred section: "Heat-variance decay `Var(e^{-tL}f) ≤ e^{−2tλ₂}Var(f)`:
the heat-family consumer named above; semigroup-plus-Poincaré route
needs derivative machinery not priced here") and the item the execution
plan's handoff named first. Zero new axioms: every statement below is a
corollary of proved shelf engines.

Companion to [Strategy](../docs/1_STRATEGY.md) and to the heat
semigroup program (`reversibility-and-heat-semigroup.md`, whose module
hosts the delivery).

---

## Clean-room boundary

This planning document is internal prioritization and analysis. If
counsel approves a public repository export, restate the technical
specifications independently from standard textbook sources (heat
semigroup variance decay is classical; see Sources below). Do not copy
this proposal verbatim.

## The obligation this discharges

The Poincaré delivery (2026-08-31) proved the *static* inequality
`λ₂·∑(f − mean f)² ≤ fᵀLf` and named, in its own Deferred section, the
*dynamic* consumer it feeds: variance decay under the heat semigroup,
`Var(e^{-tL}f) ≤ e^{−2tλ₂}Var(f)`. The Poincare module docstring and the
`GraphTheory.Heat` module docstring both record this as the heat
family's missing λ₂-consumer — the second load-bearing consumer of the
Poincaré delivery after `spectral_gap_edge_expansion`.

### The route decision (Step 0, settled before any Lean)

The Poincaré proposal priced this item as *not yet priced* on the
semigroup-plus-Poincaré differential route (Grönwall on
`d/dt ‖f_t − mean‖² = −2 f_tᵀL f_t`, which needs the derivative
machinery the heat module only partially carries — differentiation at
zero, not at all times). **This delivery dissolves that cost by route
choice**: the eigenbasis contraction, the exact technique of the mixing
program's proved ℓ²(π) contraction
(`dotProduct_self_degreeSqrt_mulVec_pow_walkTransitionMatrix_le`),
transferred from `P^t` to `e^{-tL}`. Every input it needs is already on
the shelf: `heatKernel_mulVec_eigvecOf` (mode damping),
`dotProduct_eigvecOf` (Parseval), `evals_sorted` +
`laplacian_evals_zero` (the eigenvalue comparison), and
`secondEval_le_rayleigh` (the zero-mode lemma). No derivatives anywhere.

### Statement design (settled before any Lean)

For symmetric nonnegative `A` with `2 ≤ card V` and `t ≥ 0`:

```
∑ i, ((heatKernel A t *ᵥ f) i − (∑ j, f j)/|V|)²
  ≤ Real.exp (-(2 * t * λ₂)) * ∑ i, (f i − (∑ j, f j)/|V|)²
```

- **Hypothesis-minimal on purpose**: no connectivity, no `0 < λ₂`. At
  `λ₂ = 0` (disconnected input) the statement is the *true* rate-1
  bound `Var(f_t) ≤ Var(f)` — every mode factor is at most `1` (PSD
  input, `t ≥ 0`) while `e^{0} = 1` — and QA pins this branch *exact*
  (a kernel vector attains it with equality at every time). The
  Poincaré division form's `0 < λ₂` guard is the boundary of the *static*
  region; the decay form needs no such guard because its rate collapses
  to the trivially-true `1` exactly there.
- **The mean on both sides is `f`'s own mean**, made honest by the
  proved mean-preservation lemma `sum_heatKernel_mulVec` (the sum is
  the `onesVec` pairing moved across by symmetry; QA pins it by two
  independent routes).
- Degenerate corners (the §5 hazard classes): `card V ∈ {0,1}` make the
  statement *unstateable* (`λ₂`'s index needs `2 ≤ card V`) — the
  engine guard is definitional, as in the Poincaré delivery. No
  measures, no integrals — the junk-integral hazard class does not
  reach these statements. `t = 0` reads `Var ≤ 1·Var` (QA corner pin).

### The proof architecture

Two branches over one Parseval identity
(`dotProduct_self_heatKernel_mulVec`: `‖e^{-tL}x‖² =
∑ᵢ (e^{-tλᵢ}(vᵢ ⬝ᵥ x))²`, no inequality lost):

1. **`0 < λ₂`**: zero modes carry no coordinate of a centered input
   (the new kernel lemma: at a positive gap every kernel eigenbasis
   vector is a multiple of `onesVec` — a nonzero *centered* kernel
   residual would have Rayleigh quotient `0`, forcing `λ₂ ≤ 0` through
   `secondEval_le_rayleigh`); every nonzero mode's factor `e^{-2tλᵢ}`
   is dominated by `e^{-2tλ₂}` through the new eigenvalue comparison
   `secondEval_le_eigvalOf_of_ne_zero` (an eigenvalue below
   `evals ⟨1⟩` sits at sorted index `0`, which is exactly `0` —
   below-gap eigenvalues *are* kernel eigenvalues).
2. **`λ₂ ≤ 0`**: every mode factor is at most `1` (PSD) while the rate
   `e^{-2tλ₂} ≥ 1` — no mode hypothesis needed at all.

## The Lean (delivered)

`Heat.lean`'s new "Variance decay" section — 7 declarations:
`eigvalOf_mem_evals`, `secondEval_le_eigvalOf_of_ne_zero`,
`eigvecOf_ker_eq_smul_onesVec_of_secondEval_pos`, `sum_heatKernel_mulVec`,
`eigvecOf_dotProduct_heatKernel_mulVec`,
`dotProduct_self_heatKernel_mulVec`, `heatKernel_variance_decay`.

`Heat_QA.lean`'s new variance-decay section — +19 (3382 → 3401):

- **K₂ exact attainment** (`heat_variance_edge_attained_QA`): at the
  Fiedler vector the decayed variance is exactly `2e^{-4t}` at *every*
  time (the hypothesis-free form holds for all `t ∈ ℝ` — even the
  backward/growing semigroup attains it), the theorem instance reading
  its gap from the independently pinned `edgeLaplacian_evals_QA`, the
  bound value pinned `2e^{-4t}` too — attained, no smaller constant.
- **P₃ exact attainment**: `2e^{-2t}` at the path's Fiedler vector, the
  instance closing at equality — the same shape at the *other* gap
  value (`1`, not `2`), on an irregular-degree graph (the combinatorial
  statement is not regularity-dependent).
- **The wrong-constant refutation**: the K₂ shape with gap `3` reads
  `2e^{-4} ≤ 2e^{-6}` at `t = 1` — refuted through `e^{-6} < e^{-4}`
  (`Real.exp_lt_exp`). The attained rate is load-bearing.
- **The λ₂ = 0 branch pinned exact**: on the disconnected `Fin 3`
  fixture (edge `{0,1}` + isolated vertex) at the component indicator
  (a kernel vector — `heatKernel_noLeakage_component_QA` fixes it at
  every time), both sides compute to exactly `2/3`, with the fixture's
  gap proved *exactly zero* (≤ 0 by the Rayleigh bound at the centered
  kernel vector `![1,1,−2]`, whose kernel equation and orthogonality
  are raw entrywise pins; ≥ 0 by `evals_sorted` +
  `laplacian_evals_zero`). The zero-gap branch is tight exactly where
  the theorem says nothing decays.
- **Mean preservation, two routes**: the lemma route
  (`sum_heatKernel_mulVec` instantiated: mass `4` for `![1,3]` at
  `t = 1` — a transpose slip in the symmetry transfer would move this
  number) and the raw route (the closed form `1 + ((e^{-2}−1)/2)•L` +
  hand arithmetic).
- **The `t = 0` corner**: `heatKernel_zero` + `one_mulVec` give the
  identity `Var(f) ≤ Var(f)` at every input on the fixture.

## Acceptance criteria — all met

1. **Seven shelf declarations proved**, zero new axioms, `#print axioms`
   via `wip/heatvar_axcheck.lean` on all 26 audited declarations (7
   shelf + 19 QA) exactly `propext, Classical.choice, Quot.sound`.
2. **The QA obligations landed** (+19, 3382 → 3401): two exact
   attainment families, the wrong-constant fence, the exact zero-gap
   branch, the two-route mean pin, the `t = 0` corner.
3. **Full verification ladder passes**: `lake build` ✔ (2408/2409) +
   `check_build_completeness.py` (133 source files, 133 fresh
   artifacts, 0 stale, 0 missing, exit 0, after the documented
   single-module mtime remediation); `lint_axioms` exit 0 (5 axioms,
   both PF findings allowlisted-confirmed); `check_refutation_independence`
   (10-tag clean — no tags added); `check_public_reachability` clean
   (63 modules); `check_citations` and `check_markdown_links` pass;
   scoreboard regenerated at **3401/5/0**; `check_scaffold_map_freshness`
   exit 0 after the 3382 → 3401 stats sync in both map files and SVG
   regeneration (this proposal has no station).
4. **No radar re-score**: this is a consumer composition of two
   already-counted families (Poincaré, axis 3 at 4.5; the heat program,
   axis 3/5's variational machinery) plus new negative-witness fences —
   the QA axis holds at 4.0 per protocol and axis 3 stays 4.5
   (log-Sobolev remains its named gap, consumer-gated as recorded).

## Delivery record

**Spike first** (`wip/heatvar_spike.lean` — both layers iterated to
zero errors/zero warnings before any shelf edit; the final state also
carries the `#print axioms` audit of every new declaration).

**Technique findings (recorded so they are not re-derived):**

1. The pinned Mathlib's first-argument dotProduct lemmas are
   `Matrix.sub_dotProduct` / `Matrix.smul_dotProduct` (the
   second-argument forms are `dotProduct_sub` / `dotProduct_smul`);
   likewise `Matrix.mulVec_sub` is the vector-difference form —
   `Matrix.sub_mulVec` is the *matrix*-difference form (`(M − N) *ᵥ v`).
2. `evals_sorted : Monotone (evals hM)` applies as a *single* argument
   (`evals_sorted hL hle` — the Fin pair is strict-implicit), and the
   Fin order is discharged by `Fin.le_def.2 hk1` (defeq alone does not
   elaborate under the implicit binder).
3. `List.mem_iff_get.1 hmem` destructures as `⟨p, hp⟩` with `p`
   carrying the bound (`obtain ⟨n, hn, hget⟩` fails dependent
   elimination) — the exact idiom of `eigvalOf_le_evals_last`'s proof.
4. `mulVec_eigenvectorBasis`'s statement lives at the `WithLp`-coerced
   vector: consume it by `exact` (defeq — the `eigvecOf` coercion
   unfolds), never by `rw` (no syntactic match); `rw ... at h` on the
   eigenvalue needs the `eigenvalues i = 0` form (`eigvalOf` defeq, but
   only the `.eigenvalues` spelling rewrites).
5. `Real.exp_lt_exp` is an *iff* at this pin (`.mpr`); `pow_le_one` is
   deprecated for `pow_le_one₀`; `rw`-closability of `a + a = a * 2` is
   unreliable — close with `ring` and do not chase the "Try this:
   ring_nf" hint into removing it.
6. The stale-olen import-boundary recurrence (the QA module cannot see
   new shelf declarations until `lake build` refreshes the imported
   module's olean) — hit again here, resolved by the documented explicit
   target rebuild before re-elaborating the QA file.

**Load-bearing notes:**

- `secondEval_le_eigvalOf_of_ne_zero` is the eigenvalue-comparison
  half that the DC-limit proof does internally per-index; extracted
  once, it is the reusable form any "every nonzero eigenvalue ≥ λ₂"
  consumer needs.
- `eigvecOf_ker_eq_smul_onesVec_of_secondEval_pos` is deliberately
  stated at the *positive-gap* hypothesis (not connectivity): the
  Rayleigh-bound argument needs only `0 < λ₂`, which is the exact
  boundary both this lemma and the Poincaré division form live on.
- The zero-gap branch's termwise domination uses *no* mode hypothesis —
  `x ⊥ 1` is unused there (the contraction `‖e^{-tL}x‖ ≤ ‖x‖` holds for
  every `x` on PSD input). This honesty is recorded in the proof, not
  hidden: the hypothesis is derived (centering), never assumed.

## Deferred (named, not queued)

- A π-weighted twin at `L_sym`'s gap (the `poincare_inequality_normalized`
  analogue for the heat kernel of `L_sym`): consumer-gated on a named
  walk/heat statement needing it (the mixing program's ℓ²(π) machinery
  is the natural source).
- The heat-kernel form of the `t_mix` depth packaging: consumer-gated
  on the TV proposal's own deferred `t_mix` object, unchanged.

## Sources

Heat semigroup variance decay at the spectral gap is classical; standard
references include Chung, *Spectral Graph Theory* (1997), §1.3 (the heat
kernel and its spectral representation) and Levin–Peres–Wilmer, *Markov
Chains and Mixing Times* (2009), Ch. 12 (the ℓ² variance-decay reading
for reversible chains). No statement is admitted on these citations —
everything here is *proved* from the shelf's delivered engines — so the
citations locate the statement *shape*, not trust boundaries. Page-level
locators stay unconfirmed per the standing locator rule until checked
against a physical copy.
