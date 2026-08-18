# Proposal: Prove One Named Inequality

**Status:** Proposed. Assistant's assessment of project direction, requested
2026-08-17. Authorizes no Lean changes, axiom removals, document rewrites, or
external publication.

Companion to [Grow the Crust Through Electrical Structure](electrical-structure-crust.md),
which takes the opposite premise — the center stays fixed — and asks where
the hard crust should grow instead. The two are independent and either may be
adopted alone.

Assessed from the repository as of this date: `docs/1_STRATEGY.md`,
`docs/5_QA_SCOREBOARD.md`, `docs/6_SGT_BACKLOG.md`, `docs/7_SGT_RADAR.md`,
`docs/EXECUTION_PLAN.md`, `docs/traction-plan.md`, and the axiom surface in
`Scaffold/Mathlib`.

## What is working

The mushy-center / hard-crust discipline is real and uncommon: 18 cited
axioms, zero `sorry` or `admit`, every bridge proved, and QA that does
decide-certified exhaustive cut sweeps with negative witnesses
(`Scaffold/QA/SpectralGraph/Exhaustive_QA.lean`). The recent sequence
`Normalized` → `Stationary` → `VariationalTransfer` is good structural work:
a congruence identity proved once, then consumed twice.

## The finding

Every mathematically substantive statement in the repository is an axiom.
The admitted list is Weyl, Davis–Kahan, interlacing, the λ₂ variational
characterization, both Cheeger bounds, and all six concentration
inequalities. What is proved is connective tissue — definitions, symmetry,
kernels, row sums, congruences, cut duality.

That tissue is valuable, but the radar's "proved depth 3.5" is scoring the
tissue rather than the organs. A skeptical outside reader will observe that
the theorems anyone would import Scaffold *for* are assumptions.

### Relation to the stated mushy-center policy

The README's "mushy center and hard crust" section anticipates this
condition: published background results are *supposed* to enter as cited
axioms, and the trust-model table already refuses to call an axiom-backed
result formalized. So "the substantive statements are axioms" is not a
violation of the design — it is the design working as written.

The finding above is therefore narrower, and it is the README's own second
instruction: *"Ongoing work should shrink and strengthen the mushy center
while expanding the hard crust. Prefer proving or upstreaming an existing
axiom … over adding a new assumption."* Recent runs have expanded the crust
without shrinking the center — the one exception, `spectral_gap_stability`
(19 → 18), is the shape this proposal asks to repeat on a harder target.
Cheeger's easy direction is the largest available shrink, and the policy
already ranks it above the interface work that has been displacing it.

## Recommended direction

Stop widening the neighborhood and prove one named textbook inequality.

**Target:** `cheeger_lower_bound` (`λ₂/2 ≤ h`), derived from
`lambda2_variational` rather than admitted alongside it.

Rationale:

1. **Reachable.** The easy direction is a test-vector argument: take the
   minimizing cut, build its centered indicator, evaluate the Rayleigh
   quotient, bound. The pieces are already on the shelf — `quadForm`, the
   Dirichlet identity, `laplacian_psd`, `conductance_compl` for
   canonicalizing the minimizer, and `boundary`/`vol` with their arithmetic.
2. **Emblematic.** "Scaffold proves the easy direction of Cheeger from the
   variational characterization" means something to a Mathlib contributor.
   "Scaffold has proved row-stochasticity of `D⁻¹A`" does not.
3. **Collapses two axioms into one dependency.** 18 → 17, and more
   importantly it reframes the remaining Cheeger axiom as *the hard
   direction only*, which is the honest statement of what is actually
   unformalized.
4. **Forces the irregular generalization.** `cheeger_lower_bound` is
   regular-only; `VariationalTransfer` now supplies the irregular Rayleigh
   quotient. Proving the easy direction in the general normalized setting
   retires the regular-graph restriction the radar flags as axis 4's ceiling.

**Correction (2026-08-18): this plan is under-specified as written.** After
the Cheeger statement-shape repair of the same date, the axioms are stated at
`secondEval (regularNormalizedLaplacian A d)` — the second sorted eigenvalue
of the **normalized** Laplacian. But `lambda2_variational`
(`Spectral.lean:785`) characterizes `lambda2`, which is
`evals (laplacian ·)` — the **combinatorial** Laplacian.
`lambda2_eq_secondEval` is `rfl` and bridges the two names for one operator;
it does not bridge combinatorial to normalized. So deriving the Cheeger bound
from `lambda2_variational` requires an intermediate that does not exist: a
variational characterization of `secondEval L_sym`. The degree-weighted
Rayleigh transfer in `GraphTheory.VariationalTransfer` is the natural route.
Scope the missing intermediate before adopting this proposal; it is strictly
harder than originally stated, which strengthens the case for running
[the electrical proposal](electrical-structure-crust.md) first.

This is a hard slice — likely several sessions of real Lean work rather than
one run. That is the point. Recent milestones have each landed within a
single run, which suggests work selected for tractability rather than for
leverage.

**Update (2026-08-18):** the combinatorial-Laplacian variational
characterization now *exists and is proved* — `lambda2_variational` was
retired from axiom to theorem (see [the λ₂ proposal's delivery
note](prove-lambda2-variational.md)). The intermediate this correction
calls missing is the *normalized* instance `secondEval L_sym`; it
follows from the proved combinatorial instance plus the proved
congruence transfer
(`VariationalTransfer.rayleigh_normalizedLaplacian_degreeSqrt`), but
that transfer step is not yet written. Scoping estimate reduced
accordingly.

## Supporting moves

**Cut the meta-work in half.** Five governance documents are rewritten every
run; `docs/EXECUTION_PLAN.md` alone carries roughly eight milestone entries
dated 2026-08-17. The self-scoring apparatus has grown larger than the
artifact it scores, and re-scoring downstream reuse 2.5 → 3.0 → 3.5 → 4.0
within one day is measurement, not progress. Freeze radar re-scoring to
milestone boundaries and let `docs/AGENT_ACTIVITY.md` carry the narrative.

**Get one thing outside the repository.** `docs/traction-plan.md` is a sound
plan with no execution against it, and every measure it names — outside
imports, external issues, downstream packages, upstream adoption — is
currently zero. The highest-information available action is a single Mathlib
PR for something small and independently useful: `walkTransitionMatrix`
row-stochasticity, or the diagonal-square-root congruence. One review from a
Mathlib maintainer will reveal more about whether these interfaces are usable
than another radar pass will.

## Short version

Recent runs have proved that things *connect*. The next stretch should prove
that something is *true*: take Cheeger's easy direction, accept that it takes
a while, and let the radar sit still while it happens.

## Open next step

Scope the Lean proof path for `cheeger_lower_bound` in detail — which
existing lemmas compose, and where the gaps are — before committing to the
slice.
