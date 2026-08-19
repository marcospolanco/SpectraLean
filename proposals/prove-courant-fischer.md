# Proposal: Prove General Courant–Fischer Min-Max (Not Admit It)

**Status:** Delivered 2026-08-18. All three planned theorem forms landed
in `Scaffold/Mathlib/GraphTheory/Spectral.lean` (new `CourantFischer`
section) as pure hard crust — no axioms (general min–max was never
admitted; count stays 15): the two witness directions
(`exists_submodule_forall_rayleigh_le`,
`exists_ne_mem_rayleigh_ge_of_finrank_eq`) and the packaged infimum
equation `evals_min_max`, plus public center API (general-`k`
multiplicity pins `card_filter_eigvalOf_lt_evals_le` /
`succ_le_card_filter_eigvalOf_le`, component-form Rayleigh bounds,
`eigvecOf_dotProduct`, `linearIndependent_eigvecOf_finset`,
`finrank_span_eigvecOf_finset`,
`dotProduct_eigvecOf_eq_zero_of_mem_span`). The open next step below was
resolved first: the dimension-intersection lemma is present in the pin
(`Submodule.finrank_sup_add_finrank_inf_eq`), together with
`Finset.exists_subset_card_eq`, `finrank_span_eq_card`,
`Fintype.linearIndependent_iff`, `Module.finrank_pi`, and
`Submodule.ne_bot_iff`. QA: `Scaffold/QA/SpectralGraph/
CourantFischer_QA.lean` (33 declarations) — spectrum pinned from
trace/determinant/sortedness on a `!![2,1;1,2]` fixture, both directions
instantiated (including the derived top-eigenvalue-domination universal
through `Submodule.eq_top_of_finrank_eq` and exact attainment of
`evals 1`), negative witnesses (wrong subspace refuted; the dimension
hypothesis load-bearing at index `1`; interior-index wrong
two-dimensional subspace refuted on the path Laplacian with a
cross-check against the older `secondEval_le_rayleigh` engine).
**The four named follow-ons below are NOT delivered by this proposal**
(interlacing retirement, full Rayleigh/Dirichlet monotonicity, the
Cheeger hard direction, Fiedler Phase B) — each remains separate
follow-on work exactly as the proposal states.

Assistant's assessment of project direction, requested
2026-08-18 — companion to [Admit Perron–Frobenius for Irreducible
Nonnegative Matrices](admit-perron-frobenius.md), generated from the same
"biggest single unlock" question, but reaching a **different kind of
recommendation**: this one argues for proving the target, not admitting
it. Authorizes no Lean changes, axiom admissions, or external
publication.

Companion to [Prove λ₂'s Variational
Characterization](prove-lambda2-variational.md) — this proposal
generalizes that proof's technique from the second eigenvalue to an
arbitrary one, and its delivery record is the direct evidence this route
is tractable, not a speculative analogy.

Assessed from `Scaffold/Mathlib/GraphTheory/Spectral.lean` (`evals`,
`eigvecOf`, `eigvecOf_complete`, `eigvecOf_inner` — the proved orthonormal
eigenbasis), `prove-lambda2-variational.md`'s route and delivery record,
the pinned Mathlib's `Analysis/InnerProductSpace/{Rayleigh,Spectrum,
Symmetric}.lean`, and `docs/8_MATHLIB_COVERAGE_MAP.md`.

## Correction to the verbal version of this idea

Raised earlier in conversation as "admit general Courant–Fischer, then
derive interlacing/Weyl/monotonicity/the Cheeger hard direction from it."
Closer analysis below shows the *proof* is more directly reachable than
that framing assumed — Scaffold already has the one ingredient the λ₂
proof needed real plumbing for (a bridge into Mathlib's
`LinearMap.IsSymmetric`/inner-product-space world), and this route
doesn't need that bridge at all. Admitting something this tractable would
be the wrong move under this project's own stated preference: "prefer
proving or upstreaming an existing axiom... over adding a new
assumption" (`README.md`, mushy-center policy).

## The finding

The pinned Mathlib has no general min-max theorem for an arbitrary
eigenvalue index — confirmed again this session, no change from the
survey in `prove-lambda2-variational.md`. But Scaffold's own delivery
record for that proposal contains a detail worth re-reading closely: "The
LinearMap bridge was never built and is no longer needed for this
result." The delivered proof did **not** go through Mathlib's
`InnerProductSpace` restriction machinery (`hasEigenvalue_iInf_of_finiteDimensional`,
`invariant_orthogonalComplement_eigenspace`) as originally sketched — it
found a more direct route using Scaffold's own already-proved orthonormal
eigenbasis (`eigvecOf_complete`, `eigvecOf_inner`, and the spectral
resolution lemmas `quadForm_eigvalOf`, `dotProduct_eigvecOf`). That same
direct route generalizes cleanly from "the second eigenvalue" to "the
k-th eigenvalue, for any k" — it was never actually specific to k=2.

## Route

For symmetric `M` with sorted eigenvalues `evals 0 ≤ evals 1 ≤ ... ≤
evals (n-1)` and the proved orthonormal eigenbasis, the claim is
`evals k = min` over `(k+1)`-dimensional subspaces `W` of `max` over
nonzero `x ∈ W` of `rayleigh M x` (index conventions to be nailed down
exactly during implementation — Scaffold's `evals` is `Fin`-indexed from
`0`, and off-by-one here is exactly the kind of error this repository has
been burned by before; treat the precise statement as scoping work, not
a detail to wave at).

**Direction 1 (some subspace achieves it).** Take `W = span {v_0, ...,
v_k}`, the bottom `k+1` eigenvectors. For `x ∈ W`, expand
`x = Σ_{i≤k} c_i v_i`; the spectral resolution already proved
(`quadForm_eigvalOf`) gives `rayleigh M x` as the variance-weighted
average `Σ c_i² (evals i) / Σ c_i²`, which is `≤ evals k` since every term
averaged is `≤ evals k`, with equality at `x = v_k`. So `W` achieves
`max = evals k` exactly — this is a direct computation from
already-proved lemmas, not new machinery.

**Direction 2 (every subspace is at least that large).** Take **any**
`W` with `dim W = k+1`. The "tail" eigenspace `T = span {v_k, ..., v_{n-1}}`
has dimension `n-k`. Since `dim W + dim T = (k+1) + (n-k) = n+1 > n`,
standard dimension-counting in an `n`-dimensional ambient space forces
`W ∩ T ≠ {0}`. Take nonzero `x` in the intersection: since `x ∈ T`, the
same spectral-resolution computation gives `rayleigh M x ≥ evals k`
(a weighted average of eigenvalues all `≥ evals k`); since `x ∈ W`, this
lower-bounds `max_{y ∈ W} rayleigh M y`. This holds for every `(k+1)`-
dimensional `W`, giving the `min` side.

Both directions route entirely through algebra already proved in
`Spectral.lean` — the eigenbasis expansion and the spectral-resolution
identity — plus one general fact needed as new plumbing: **two subspaces
of an `n`-dimensional space whose dimensions sum to more than `n`
intersect nontrivially.** Survey Mathlib's `Submodule`/`FiniteDimensional`
API for this before proving it directly (the standard form is
`finrank (W ⊓ T) ≥ finrank W + finrank T - finrank ⊤`, a corollary of the
dimension formula for `W ⊔ T`); this is exactly the kind of standard fact
likely already on the shelf, unlike the InnerProductSpace bridge the
original λ₂ sketch needed and ultimately didn't use.

## Calibration

This looks more tractable than `prove-lambda2-variational.md` was
initially calibrated to be, for a specific, checkable reason — it reuses
proved algebra instead of needing a new cross-API bridge — but do not
treat "found a clean route" as "found a cheap one." Two real costs
remain: getting the `Fin`-indexed bookkeeping exactly right for a general
`k` (harder than the fixed `k=1` case `lambda2_variational` handled), and
locating or proving the dimension-intersection lemma, which is standard
but unverified against this specific pinned Mathlib version until someone
actually searches for it. Treat this as a real, multi-session proof
project, not a quick corollary — closer to `prove-lambda2-variational.md`'s
actual difficulty than to its post-hoc-simple-looking route sketch.

## What it unlocks beyond λ₂

This is the largest-surface-area *proof* candidate currently identified,
because the general form directly generalizes what `lambda2_variational`
delivered only for a fixed, special case:

- **`eigen_interlacing_principal_submatrix`** — the currently admitted
  Cauchy interlacing axiom is a classical corollary of general min-max
  applied to a matrix and its principal submatrix over shared test
  subspaces. A real target for retirement once this lands, not a
  guaranteed one — the interlacing argument needs an additional
  subspace-intersection step of its own, so scope it as a separate
  follow-on proposal, not an automatic consequence.
  **Delivered 2026-08-18 (later the same day):** the axiom was retired
  to a proved theorem at the same name and statement (a pure proof
  task — the admitted window was the true textbook statement). The
  extra subspace-intersection step is exactly the dimension count
  `finrank (U ⊓ range pad) ≥ i + 1` through the same
  `Submodule.finrank_sup_add_finrank_inf_eq` the min–max proof itself
  used, plus an exact-dimension extraction
  (`exists_submodule_finrank_eq_of_le`) to meet the competitor
  direction's equality-shaped hypothesis. The bridge between the two
  spaces is the extend-by-zero padding `padVec`/`padVecLinear`, proved
  to preserve dot products, quadratic forms, and Rayleigh quotients.
  This is this proposal's first named consumer, consuming both witness
  directions. The former axiom's "no thin QA exists" note is also
  superseded: the computational eigenvalue machinery delivered with the
  Cheeger repair pins the window numerically on `K₂` with a singleton
  submatrix (`0 ≤ 1 ≤ 2`, both collapsed one-sided bounds refuted) in
  `Scaffold/QA/SpectralGraph/Interlacing_QA.lean`.
- **Full Rayleigh/Dirichlet monotonicity** — `electrical-structure-crust.md`
  deferred this explicitly because it "needs the Dirichlet principle as
  an attained variational characterization," which is exactly what this
  proposal would supply.
- **`cheeger_lower_bound`'s hard direction** — the remaining Cheeger
  axiom, currently admitted, needs an attained (not just infimum) spectral
  characterization at the shape this proposal targets.
- **`fiedler-partitioning.md` Phase B**, transitively, through the Cheeger
  hard direction above.

None of these are delivered by this proposal — each is real, separate
follow-on work this document explicitly does not claim to complete by
proving the min-max theorem alone.

## Sequencing note

This does not compete with `admit-perron-frobenius.md` for the same run —
they are different kinds of bets (proof vs. admission) on different
territory (existing symmetric-matrix axis vs. new directed-graph axis).
Both can proceed independently. Within this repository's existing axis,
this is the higher-leverage of the two proof-shaped options currently on
the table, since — unlike most single-theorem proposals — it names four
separate existing admitted-or-deferred items as potential downstream
consumers rather than one.

## Open next step

Survey the pinned Mathlib specifically for the dimension-intersection
lemma (`finrank (W ⊓ T) ≥ finrank W + finrank T - finrank ⊤` or an
equivalent form) before committing a run — this is the one piece of this
route not already sitting in `Spectral.lean`, and its presence or absence
materially changes the proposal's cost.
