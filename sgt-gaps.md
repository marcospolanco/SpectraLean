# SGT formalization gaps with an external customer — resolved

**Written:** 2026-08-19, from an outside assessment of the same date.
**Reorganized:** 2026-08-19, restructured around priority and readiness.
**Resolved:** 2026-08-19 — every item promoted to a real `proposals/*.md`
document with a genuine priority tag; none left in `Low` limbo. This file
is now the historical record of that triage, not an active document —
the full technical content (external consumer, calibration, build order,
QA plan) lives in each proposal, not duplicated here.

## What this was, and how it differed from the standing backlog

`docs/6_SGT_BACKLOG.md` gates new work on a *named SGT consumer* — another
proposal or backlog item that states a concrete internal dependency. Every
item below was justified differently: by an established *external* field
that already uses the mathematics, the same justification track
`docs/traction-plan.md` uses for outreach. Two items' gates turned out to
require resolving that tension explicitly rather than treating "real
external field" as automatically equivalent to "named SGT consumer" — see
the resolution notes below.

## Resolution

| Item | Final priority | Proposal | What resolved the gate |
| --- | --- | --- | --- |
| 2. Resolvent calculus for PSD matrices | High | [`resolvent-calculus-psd.md`](proposals/resolvent-calculus-psd.md) | No gate existed |
| 4. Tikhonov regularization in the Laplacian eigenbasis | High | [`tikhonov-shrinkage-filter.md`](proposals/tikhonov-shrinkage-filter.md) | No gate existed |
| 5. Spectral band projectors | High | [`spectral-band-projectors.md`](proposals/spectral-band-projectors.md) | No gate existed; found cheaper than originally rated (reuses the delivered `spectralProjector`) |
| 1. Heat semigroup on a finite weighted graph | Medium | [`reversibility-and-heat-semigroup.md`](proposals/reversibility-and-heat-semigroup.md) Phase B | Backlog item 5's named-consumer gate resolved 2026-08-19: diffusion models / heat-kernel graph signatures accepted as the external consumer, an operator decision recorded in `docs/6_SGT_BACKLOG.md` item 5 |
| 3. Discharge Davis–Kahan / Weyl / Cheeger hard direction | Medium (Step-0-gated per axiom) | [`discharge-perturbation-axioms.md`](proposals/discharge-perturbation-axioms.md) | Not a decision gate — a tractability spike (Weyl found a real, unverified C*-algebra lead; Davis–Kahan and the Cheeger hard direction remain genuinely uncertain, gated on their own surveys, not on an operator choice) |
| 6. Directed and asymmetric graph operators | Medium (Step-0-gated) | [`directed-graph-operators.md`](proposals/directed-graph-operators.md) | Scope decision resolved 2026-08-19: `docs/1_STRATEGY.md`'s center-out policy now covers directed graphs (same decision as `admit-perron-frobenius.md`, upgraded from Low the same day) |
| 7. Approximate spectral projection with error bounds | Medium (Step-0-gated) | [`approximate-spectral-projection.md`](proposals/approximate-spectral-projection.md) | Not a decision gate — upgraded from an initial icebox recommendation once it was clear uncertainty about tractability should be scoped, not used to exclude |

## Verification status carried forward

The original assessment's literature citations were submitted as "from
memory and unverified." Spot-checked before promotion: the three axioms
item 3 targets, Scaffold's genuine lack of existing coverage for items
2/4/5/7, and Mathlib's Hilbert projection theorem and
`IsSelfAdjoint.spectralRadius_eq_nnnorm` were all confirmed present as
described. **The literature citations themselves (author, title, year,
page) remain unverified** in every promoted proposal — each one repeats
this caveat; confirm before any citation appears in a committed docstring.

## Confirmed present — not requested

Checked against the tree 2026-08-19, unchanged, so these did not generate
duplicate backlog items: `laplacian`, `laplacian_psd`,
`laplacian_ones_in_kernel`, `laplacian_kernel_eq_span_onesVec`, `evals`,
`evals_sorted`, `eigvecOf`, `eigvecOf_inner`, `eigvecOf_complete`,
`quadForm`, `rayleigh`, `vol`, `boundary`, `conductance`,
`cheegerConstant`, `cheeger_upper_bound`, `secondEval`,
`lambda2_variational`, `evals_min_max`, orthogonal-conjugation invariance,
and Parseval.
