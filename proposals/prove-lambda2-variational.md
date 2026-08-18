# Proposal: Prove λ₂'s Variational Characterization

**Status:** Delivered 2026-08-18 (see the delivery note at the end).
The original proposal text follows for the record.

Assistant's assessment of project direction, requested
2026-08-18. Authorizes no Lean changes, axiom removals, document rewrites,
or external publication.

Companion to [Prove One Named Inequality](prove-cheeger-easy-direction.md)
and [Grow the Crust Through Electrical
Structure](electrical-structure-crust.md). This proposal supplies exactly
the "missing intermediate" the Cheeger proposal's 2026-08-18 correction
identifies as blocking it — but goes further: the target here is to
**retire** `lambda2_variational` as an axiom, not merely build a corollary
that consumes it alongside. It also directly consumes the electrical
proposal's delivered step 2 (`laplacian_kernel_eq_span_onesVec`) as a
load-bearing piece of the argument, which is why this document did not
exist before that step landed.

Assessed from `Scaffold/Mathlib/GraphTheory/Spectral.lean` (`evals`,
`lambda2`, `secondEval`, `lambda2_variational`),
`Scaffold/Mathlib/GraphTheory/VariationalTransfer.lean`, the 2026-08-18
correction in `proposals/prove-cheeger-easy-direction.md`, step 2 of
`proposals/electrical-structure-crust.md`, and the pinned Mathlib's
`Mathlib/Analysis/InnerProductSpace/{Rayleigh,Spectrum,Symmetric}.lean`.

## The finding

The pinned Mathlib has no general Courant–Fischer min-max theorem (a
repository-wide search under `.lake/packages/mathlib/` for "courant" or a
min-max eigenvalue shape returns nothing) — so "just prove Courant–Fischer"
is not a scoped target; it would mean building min-max theory for arbitrary
eigenvalue index `k` essentially from scratch. But Scaffold does not need
the general theorem. It needs exactly one instance: the **second-smallest**
eigenvalue, and Mathlib already has the two pieces that make that instance
tractable:

- `LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional`
  (`Analysis/InnerProductSpace/Rayleigh.lean:249`) — the infimum of the
  Rayleigh quotient of a symmetric operator on a finite-dimensional space is
  itself an eigenvalue. This is the extreme-eigenvalue variational
  principle (Courant–Fischer's base case, `k = 1` or `k = n`), proved in
  general.
- `LinearMap.IsSymmetric.invariant_orthogonalComplement_eigenspace`
  (`Analysis/InnerProductSpace/Spectrum.lean:65`) and
  `IsSymmetric.restrict_invariant` (`Analysis/InnerProductSpace/Symmetric.lean:127`)
  — the orthogonal complement of a single eigenspace is invariant under a
  symmetric operator, and restricting to an invariant subspace preserves
  symmetry.

Composed, these give the textbook route to a second eigenvalue: restrict
the Laplacian to the orthogonal complement of its 0-eigenspace, and apply
the extreme-eigenvalue principle *there*. That route needs one fact Scaffold
already proved and Mathlib does not supply generically: that the
0-eigenspace is **exactly** `span {onesVec}` — not merely contains it — so
the restriction's bottom eigenvalue really is the graph's second-smallest,
not some other point still tied for the bottom. That is
`laplacian_kernel_eq_span_onesVec`, delivered 2026-08-18 as step 2 of the
electrical proposal. Before that step existed, this proposal's route did
not have a proved multiplicity pin and would have needed one of its own.

## Recommendation

Target `lambda2_variational` itself (`Spectral.lean:927`), not a fresh
axiom-consuming corollary. If it lands: **18 axioms → 17**, and
`prove-cheeger-easy-direction.md`'s stated blocker — "a variational
characterization of `secondEval L_sym`... does not exist" — stops being
true as stated, because the congruence-transfer machinery already proved in
`VariationalTransfer.lean` (`degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt`,
the degree-weighted Rayleigh quotient identity) is sitting on the shelf
ready to carry a proved `lambda2_variational` the rest of the way to
`secondEval(L_sym)`.

## Route sketch

Not a proof — a scoping sketch, since the honest answer below is that step
5 is real work.

1. **Bridge to the inner-product-space world.** `evals`/`lambda2` are
   defined via `Matrix.IsHermitian.eigenvalues` (`Spectral.lean:180-184`) —
   the *matrix* spectral theorem. The Rayleigh/restriction machinery above
   lives on `LinearMap.IsSymmetric` over an inner product space. Mathlib's
   `Matrix.toEuclideanLin` (referenced in
   `LinearAlgebra/Matrix/Spectrum.lean`) is the documented bridge; this step
   is plumbing, not new mathematics, but it is real plumbing.
2. **Pin the 0-eigenspace.** `laplacian_kernel_eq_span_onesVec` (connected
   graphs) gives the 0-eigenspace as exactly `span ℝ {onesVec}`, dimension 1
   — already proved, no new work.
3. **Restrict.** `invariant_orthogonalComplement_eigenspace` +
   `restrict_invariant` give a symmetric operator on
   `(span {onesVec})ᗮ`.
4. **Apply the extreme-eigenvalue principle.** `hasEigenvalue_iInf_of_finiteDimensional`
   on the restriction gives: the infimum of the Rayleigh quotient over that
   subspace is an eigenvalue of the restricted operator.
5. **Identify it as `lambda2`.** This is the step without an off-the-shelf
   Mathlib lemma found in this survey: showing the restricted operator's
   bottom eigenvalue equals the *second* sorted eigenvalue of the
   unrestricted operator — standard textbook material (it follows from the
   0-eigenspace being one-dimensional, so every other eigenvalue lives in
   the complement), but it is an argument to write, not a citation to make.
6. **Match statement shape.** `lambda2_variational` is phrased as an `sInf`
   over `{r | ∃ x ≠ 0, x ⬝ onesVec = 0 ∧ rayleigh (laplacian A) x = r}`
   (`Spectral.lean:930-931`), not as an `iInf` over a subtype — reconciling
   `sInf`-of-image with the restricted operator's `iInf`-eigenvalue
   statement is bookkeeping, but is the last mile before the axiom can be
   discharged rather than restated.

## Calibration

Do not undersell step 5 and step 1 by pointing at the Mathlib citations
above and calling this reachable. `prove-cheeger-easy-direction.md` was
already corrected once (2026-08-18) for underscoping a "requires an
intermediate" gap into something that looked like a small transport lemma;
the same risk applies here in the other direction — having found the right
Mathlib file is not the same as having scoped the multiplicity argument in
step 5. Treat this as at least as hard as the Cheeger easy-direction slice,
likely several sessions, not a single run.

## What it unlocks beyond Cheeger

- **Axis 3 (variational and functional methods), currently 3.0** — the
  radar names `lambda2_variational`'s admitted status as this axis's
  explicit gap (`docs/7_SGT_RADAR.md` row 3). This is the direct, named
  consumer.
- **Backlog item 4 (spectral algorithms)** — gated on "items 1–3 mak[ing]
  the inner interfaces credible"; a *proved* variational principle is a
  materially stronger foundation for a Fiedler-vector existence statement
  than an admitted one, since the minimizer constructed in step 4 above
  literally is the Fiedler vector, not merely asserted to exist.
- **Backlog item 5 (mixing/diffusion, conditional)** — any mixing-time
  argument that needs a spectral-gap lower bound inherits this for free
  once proved.
- **A strictly larger shrink than consuming the axiom would give.**
  `prove-cheeger-easy-direction.md`'s own version of this move (deriving
  the Cheeger bound *from* `lambda2_variational`) collapses two axioms into
  one dependency — 18 stays 18 until the underlying axiom itself is
  removed. This proposal removes the axiom outright.

## Sequencing note

If adopted, attempt this before committing a run to
`prove-cheeger-easy-direction.md` as currently scoped — success here
removes that proposal's stated blocker entirely rather than requiring it to
scope its own intermediate. If this does not land in a reasonable number of
sessions, the Cheeger easy direction can still, worst case, be admitted
alongside `lambda2_variational` as originally planned; there is no
regression from attempting this first.

## Open next step

Spike step 1 (the `Matrix.IsHermitian` ↔ `LinearMap.IsSymmetric` bridge) in
isolation before committing a full run — it is the piece with the least
existing evidence in this repository (`SimpleGraphAdapter.lean` and
`VariationalTransfer.lean` both bridge within the matrix world; nothing yet
crosses into Mathlib's inner-product-space operator API), so it is the
step most likely to reveal this route is costlier than sketched above.

## Delivery note (2026-08-18)

**Delivered** — with two material deviations from the sketch, both
recorded here because they change what any future reader should
conclude from this document.

1. **The route was the matrix world, not the operator bridge.** The
   proposal's "Open next step" was to spike the
   `Matrix.IsHermitian` ↔ `LinearMap.IsSymmetric` bridge (route steps
   1–6 through `Rayleigh.lean`/`Spectrum.lean`). A pre-implementation
   survey found a cheaper route through the repository's own proved
   eigenbasis tools (`eigvecOf_inner`, `eigvecOf_complete`,
   `mulVec_eigvecOf_sum_apply`) plus new lemmas proved in
   `Scaffold/Mathlib/GraphTheory/Spectral.lean`:
   `eigvecOf_expansion_apply` (entrywise completeness),
   `dotProduct_eigvecOf` (Parseval), `dotProduct_eigvecOf_mulVec`
   (self-adjointness in coordinates), `quadForm_eigvalOf` (spectral
   resolution), `quadForm_eigvecOf_self`,
   `eigvecOf_ortho_onesVec`, and the two multiplicity pins the
   proposal's step 5 flagged as "an argument to write, not a citation
   to make" — `evals_one_le_max_of_ne` (no two distinct indices below
   `evals 1`) and `exists_ne_eigvalOf_of_evals_head_eq` (a repeated
   bottom entry comes from two distinct indices), both by
   `Multiset.sort_eq`-based counting rather than operator restriction.
   The LinearMap bridge was never built and is no longer needed for
   this result.

2. **The admitted axiom was materially false, and this run repaired
   the shape.** The pre-repair axiom assumed only symmetry. With
   negative weights `onesVec` need not be a bottom eigenvector, and on
   `Fin 2` with `A = [[0,−1],[−1,0]]` the axiom asserted `0 = −2`
   (refuted in proved form by
   `QA.old_lambda2_variational_refuted_QA`). The theorem is stated
   with the load-bearing hypothesis `hnonneg : ∀ i j, 0 ≤ A i j`
   (matching `laplacian_psd`). Emergency repair per architecture §9;
   explicit axiom count 18 → 17.

**Scope caveat for the companion proposal.** The correction inside
`prove-cheeger-easy-direction.md` names its missing intermediate as "a
variational characterization of `secondEval L_sym`". This delivery
proves the **combinatorial** Laplacian instance
(`lambda2_variational` for `laplacian A`); the normalized instance
follows from it plus the proved congruence transfer
(`VariationalTransfer.rayleigh_normalizedLaplacian_degreeSqrt`), but
that transfer step still needs to be written and is not delivered
here. The major missing piece is supplied; the proposal's scoping
work is reduced, not eliminated.

QA delivered with the theorem (in
`Scaffold/QA/SpectralGraph/Variational_QA.lean`): the old-shape
refutation above; the exact `K₂` instantiation with `λ₂ = 2` computed
twice independently (trace/determinant/sortedness, and through the
theorem from the parametric Rayleigh computation); the disconnected
instantiation `λ₂ = 0` on two disjoint edges; and the path bound
`λ₂(P₃) ≤ 1` at the harmonic alternating vector.
