# Proposal: The Higher-Order Cheeger Hard Direction (Lee–Gharan–Trevisan)

**Status:** Proposed 2026-08-28. **Gated — see below.**

## The obligation this discharges

`multiway-expansion.md` (delivered COMPLETE 2026-08-26 — the every-family
easy direction `cheeger_upper_bound_multiway` and the ρ_k
partition-minimum packaging `cheeger_upper_bound_multiway_rhoK`) names
its own remaining scope explicitly, twice, in its own delivery record:

> "Remaining priced follow-on (not started): the multiway *hard*
> direction (λ_k from below, higher-order Cheeger from above) —
> genuinely multi-run, gated on a named consumer."

`docs/6_SGT_BACKLOG.md` item 3 lists multiway expansion generally; with
the easy direction delivered, the hard direction is the item's only
remaining unclaimed half. Separately, an external SGT-specialist review
of this repository (2026-08-28, no code access — GitHub-browse level)
independently flagged the same gap unprompted: *"multiway spectral
partitioning relies on the lower bound to guarantee cluster quality;
this gap is very visible to anyone working in spectral clustering."*
Two independent sources naming the same specific, well-defined theorem
is why this proposal exists now rather than staying an unindexed note
inside another file's delivery record.

## The math (verify before writing anything — see Step 0)

Lee, Gharan, Trevisan, "Multiway Spectral Partitioning and Higher-Order
Cheeger Inequalities" (STOC 2012; journal version in *Journal of the
ACM*, 2014) prove, for the normalized Laplacian's k-th smallest
eigenvalue `λ_k` and the k-way expansion constant `ρ_k` (already
formalized in `Multiway.lean` as `multiwayExpansion`):

`ρ_k ≤ C · k² · √λ_k`

for an absolute constant `C` (this is the paper's own original bound;
later work sharpens the polynomial factor, out of scope here — see
Non-goals). **The exact theorem number, page, and constant must be
confirmed against the actual paper before this proposal's Step 0
proceeds** — this document is working from memory of the result's
shape, not a verified citation, and `check_citations.py` will not
accept a new axiom (if one turns out to be needed) without one.

This is the genuinely hard direction. The easy direction
(`cheeger_upper_bound_multiway`, delivered) is a one-shot algebraic
argument: exhibit k disjoint sets, form the corresponding subspace, and
bound the Rayleigh quotient — the engine
`evals_le_of_linearIndependent` (delivered in `multiway-expansion.md`'s
Step 0) does this cleanly with no probability, no geometry, no
existence argument. The hard direction runs the other way — **from a
spectral bound to a construction of k good sets** — and the classical
proof route is qualitatively different machinery: embed `V` into `ℝ^k`
via the bottom-k eigenvectors (data this repo already has, via the
delivered eigenbasis/`spectralProjector` machinery), then extract k
disjoint low-conductance sets by a **randomized rounding argument**
(a ball-growing or random-threshold procedure in the embedded space,
with an expectation/probabilistic argument bounding the extracted
sets' conductance). This is not the same kind of probability this repo
already has: `Scaffold`'s existing concentration axioms
(`hoeffding_*`, `bernstein_*`, `matrix_*`) are all sums-of-independent-
variables tail bounds; the LGT rounding argument needs **continuous
geometric probability** (sampling a random point or direction in a
Euclidean space and reasoning about expected geometric quantities) —
an apparatus not currently used anywhere in Scaffold, and not
confirmed present in the pinned Mathlib at the fidelity this argument
needs.

## Why this is gated, not simply scoped

`multiway-expansion.md` already named this "genuinely multi-run, gated
on a named consumer," and unlike Alon–Boppana at its own adoption
point, this proposal has **no internal Scaffold consumer** waiting on
it — nothing else in this repository currently needs the hard
direction to typecheck. Its case for adoption, if any, is the same one
Alon–Boppana's was: a landmark, universally-cited result that any SGT
practitioner would expect to see once the easy direction exists,
adopted on field-standard-expectation grounds rather than internal
load-bearing need. That is exactly the kind of judgment call this
repository's own process reserves for an explicit operator decision,
not something an autonomous run should authorize for itself — the
scale of new machinery here (a probabilistic-geometric argument, not
just a new axiom or a new finite-linear-algebra lemma) is larger than
any single theorem this project has adopted so far, Alon–Boppana
included.

## Scope, if adopted

1. **Step 0 (mandatory, not authorized by this document alone):**
   - Confirm the exact citation (theorem number, constant, edition/
     venue) against the actual paper.
   - Survey what the pinned Mathlib actually offers for continuous
     geometric probability (random point/direction sampling on a
     sphere or in `ℝ^k`, expectation of a geometric functional of a
     random threshold) — this is the load-bearing unknown. If nothing
     usable exists, the honest routes are: (a) find an alternate,
     more elementary proof of the same bound that avoids continuous
     randomization (some expositions give a derandomized or
     combinatorial variant — survey whether one is both correct and
     meaningfully cheaper), or (b) report "not tractable at reasonable
     cost" as an explicitly valid recorded outcome, exactly as this
     project already treats that verdict elsewhere.
   - Confirm how much of the delivered easy-direction engine
     (`evals_le_of_linearIndependent`, the eigenbasis embedding data,
     `IsMultiwayPartition`, `multiwayExpansion`) is actually reusable
     for the construction side, versus needing its own new interface.
   - Price the result honestly as single-run or multi-run before any
     shelf Lean, per this repository's standing Step 0 discipline.
2. **Gate:** record the Step 0 verdict here, then require an explicit
   operator adoption decision before Step 1 begins — mirroring
   `alon-boppana-bound.md`'s own pre-adoption lifecycle exactly (Gate
   section blocked → operator decision → "Open next step" rewritten
   from blocked to unblocked).
3. **If adopted and tractable:** Step 1+ delivers the construction,
   at the paper's original constant only (see Non-goals), with QA on
   at least one small fixture where both `λ_k` and an explicit
   k-way partition's conductance can be pinned independently (the
   existing C₄/P₃/K₂ fixtures already used by `multiway-expansion.md`
   are natural candidates).

## Acceptance bar (for Step 0 specifically — this proposal does not
authorize Step 1)

- The citation is verified against the actual paper, not memory.
- The continuous-geometric-probability question above is answered with
  actual evidence (a Mathlib file/lemma name, or a documented absence),
  not asserted.
- A route is priced (single-run / multi-run / not tractable), and the
  verdict is recorded here regardless of which it is.
- No axiom, no `sorry`, no `admit`, and nothing past a survey spike —
  Step 0 authorizes reading and a scratch spike, not a public module.

## Non-goals

- **Not the sharper follow-up bounds.** Improvements to LGT's original
  polynomial factor (by other authors, post-2012/2014) are explicitly
  out of scope; this proposal targets the original cited theorem only,
  per this repository's standing practice of proving the cited
  statement, not the best statement in the literature.
- **Not a general geometric-probability library.** If Step 0 finds the
  needed continuous-randomization machinery absent from the pin, the
  right response is the documented "not tractable at reasonable cost"
  verdict or an alternate elementary route (per Step 0 above) — not a
  standing commitment to build general-purpose geometric probability
  theory in Mathlib for this one consumer.
- **Not self-authorizing.** Per the Gate above, this document opens the
  question; it does not adopt the program. An autonomous run should
  survey (Step 0) only if explicitly directed to, and should not treat
  this proposal as license to begin Step 1 on its own judgment the way
  it would for an unblocked Medium/High row.

## Gate

Blocked on an operator decision. `multiway-expansion.md`'s own record
already priced this as genuinely multi-run with no named consumer;
Step 0 above should run (if authorized) before, not instead of, that
decision, since an honest tractability price is exactly what the
operator needs to decide against.
