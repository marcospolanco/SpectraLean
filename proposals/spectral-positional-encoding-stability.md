# Proposal: Certified Stability for Laplacian Positional Encodings

**Status:** Proposed. Authorizes Lean proof work generalizing an
already-delivered theorem family from a fixed rank to an arbitrary rank;
no new axioms, no changes to public statements that already exist.

**Provenance:** New-capability direction chosen by the operator (2026-08-30)
from a menu of AI/network-science intersection ideas — this was ranked #1
as "closest to a demo you could show someone this week" because almost all
of the required mathematics is already proved in this repository under a
different name.

## The capability, and an honest correction about its novelty

Graph transformers that use Laplacian eigenvectors as positional encodings
— Dwivedi & Bresson's LapPE, Kreuzer et al.'s Spectral Attention Networks
(SAN) — have a known, mostly empirical robustness problem: the bottom-`k`
Laplacian eigenvectors used as node coordinates can rotate arbitrarily
within a near-degenerate eigenspace. Those two papers themselves handle it
with sign-flip data augmentation and empirical robustness testing, not a
closed-form guarantee.

**This is not new mathematics, and an earlier draft of this proposal
overclaimed on that point.** Davis-Kahan sin-θ is 1970s perturbation
theory; applying it to graph Laplacians for stability is well established
— von Luxburg's spectral clustering tutorial (2007) uses the same style of
argument for clustering stability, and a real line of GNN-theory work
(Gama & Ribeiro; Levie et al. on the stability/transferability of spectral
graph filters) derives closed-form stability bounds for graph filters and
GNN outputs under graph perturbation using essentially this spectral-
perturbation machinery, on paper, already. The specific move used here —
subtracting the shared kernel projector on connected graphs to isolate just
the informative `k`-dimensional component before applying Davis-Kahan — is
a clean trick but is closer to folklore than a citable novel result; no
claim of first-ever proof is being made for it.

What this proposal actually contributes is narrower and still worth
having: **a machine-checked instance of a known class of result**, not a
new theorem. Nobody, as far as a search of this repository and the cited
literature shows, has formalized this specific bound in a proof
assistant — the contribution is verification and a closed-form artifact a
practitioner can cite and check, not mathematical discovery. Given a base
graph, a bounded edge perturbation, and a verified eigenvalue-gap
separation at the encoding's cutoff rank, this produces a certified upper
bound on how far the resulting `k`-dimensional positional-encoding
subspace can move — the same content the Gama/Levie-style literature
already argues informally, now Lean-checked and specialized to the LapPE
kernel-isolation case.

## Why this is nearly free: the hard math is already done

Three pieces already exist on the shelf, and all three are already stated
at **arbitrary rank**, not just the rank this repository has previously
consumed them at:

1. **`davis_kahan_sin_theta`**
   (`Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/DavisKahan.lean:111`) —
   for symmetric `A`, `A + E`, and *any* index `k : Fin (Fintype.card V)`
   with a valid gap, `‖initialProjector (A + E) hAE k - initialProjector A hA k‖ ≤ ‖E‖ / δ`.
   This is already fully general in `k`; it is not a rank-2-only result.
2. **`initialProjector`**
   (`Scaffold/Mathlib/GraphTheory/Spectral.lean:457`) — the projector onto
   the span of eigenvectors with eigenvalue `≤ evals hM k`, i.e. the
   bottom-`(k+1)` eigenspace. This is exactly the subspace a `(k+1)`-
   dimensional (or `k`-dimensional, dropping the trivial constant
   eigenvector) Laplacian positional encoding spans.
3. **`initialProjector_laplacian_zero_eq_of_connected`**
   (`Scaffold/Mathlib/GraphTheory/Spectral.lean`, consumed at
   `Fiedler.lean:622`) — on two *connected* graphs, the index-0 (kernel)
   projector is the same matrix on both sides. This is what lets
   `fiedlerLine_stability` isolate the informative Fiedler component from
   the trivial constant-eigenvector component, and it does not depend on
   which rank `k` is being isolated — the kernel is the kernel regardless.

`Fiedler.lean`'s `fiedlerSubspace_stability` (line 558) and
`fiedlerLine_stability` (line 605) are graph-native wrappers of pieces 1–3
**instantiated at `k = 1`** — the rank-2 case, because the immediate
consumer at the time was the Fiedler vector. Nothing in the proof of either
theorem uses `k = 1` specifically except the literal index passed to
`davis_kahan_sin_theta` and to `initialProjector`. Generalizing both to
arbitrary `k` is a mechanical re-parameterization of an existing proof, not
new mathematics.

## Deliverable

In `Scaffold/Mathlib/GraphTheory/Fiedler.lean` (or a new file if the module
is judged to have outgrown its name — that call belongs to whoever executes
this, informed by how the existing file is organized), add the
general-rank versions:

```lean
theorem spectralEncodingSubspace_stability (A E : WAdj (V := V)) (hA : A.IsSymm)
    (hE : E.IsSymm) (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : δ ≤ evals (laplacian_symmetric (A + E) (hA.add hE)) ⟨(k : ℕ) + 1, hk⟩
        - evals (laplacian_symmetric A hA) k) :
    ‖initialProjector (laplacian (A + E)) (laplacian_symmetric (A + E) (hA.add hE)) k
      - initialProjector (laplacian A) (laplacian_symmetric A hA) k‖
      ≤ ‖laplacian E‖ / δ
```

and, isolating the informative (non-constant) part of a `k`-dimensional
encoding on connected graphs, exactly as `fiedlerLine_stability` does for
`k = 1`:

```lean
theorem spectralEncoding_stability (A E : WAdj (V := V)) (hA : A.IsSymm)
    (hE : E.IsSymm) (hnnA : ∀ i j, 0 ≤ A i j) (hnnAE : ∀ i j, 0 ≤ (A + E) i j)
    (hconnA : (supportGraph A hA).Connected)
    (hconnAE : (supportGraph (A + E) (hA.add hE)).Connected)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : δ ≤ evals (laplacian_symmetric (A + E) (hA.add hE)) ⟨(k : ℕ) + 1, hk⟩
        - evals (laplacian_symmetric A hA) k) :
    ‖(initialProjector (laplacian (A + E)) (laplacian_symmetric (A + E) (hA.add hE)) k
        - initialProjector (laplacian (A + E)) (laplacian_symmetric (A + E) (hA.add hE)) ⟨0, by omega⟩)
      - (initialProjector (laplacian A) (laplacian_symmetric A hA) k
        - initialProjector (laplacian A) (laplacian_symmetric A hA) ⟨0, by omega⟩)‖
      ≤ ‖laplacian E‖ / δ
```

(Names above are proposals, not requirements — pick whatever fits the
module's existing naming, e.g. matching `fiedlerLine_stability`'s pattern.)
`fiedlerSubspace_stability`/`fiedlerLine_stability` themselves become
one-line corollaries at `k = 1`, or are left alone and cross-referenced —
either is fine; do not delete or silently change their existing public
statements.

**What this buys, stated for the ML audience:** given a graph, a bounded
edit (edge additions/removals/reweightings summarized by `‖laplacian E‖`),
and a verified eigenvalue gap `δ` at the encoding's cutoff rank, the
`k`-dimensional Laplacian positional encoding's subspace moves by at most
`‖laplacian E‖ / δ` in operator norm — a number a practitioner can compute
before trusting a positional encoding near a small eigenvalue gap.

## Honest scope limits (state these in the delivered docstring, not just here)

- This bounds **subspace** (projector) distance, not a sign-resolved,
  entrywise distance between the actual `k`-column encoding matrix a
  transformer consumes. Subspace distance is the right invariant quantity
  precisely because individual eigenvectors have a sign/rotation ambiguity
  within tied or near-tied eigenvalues — the same ambiguity LapPE papers
  handle with sign-flip augmentation — so a subspace bound is not a weaker
  substitute for an entrywise one, it is the well-posed version of the
  question. Say this plainly; do not imply the bound controls the encoding
  matrix entrywise.
- Requires connectivity of **both** the base and perturbed graph (for the
  kernel-isolation form) — inherited unchanged from `fiedlerLine_stability`.
- Requires the caller to supply (or separately verify) the eigenvalue gap
  `δ`. This proposal does not include a method for computing or certifying
  `δ` itself beyond what `evals` already gives; that remains the caller's
  obligation, exactly as it already is for `fiedlerSubspace_stability`.
- Not a restatement of a theorem from the cited ML papers — Dwivedi &
  Bresson and Kreuzer et al. motivate *why* this bound is useful; they do
  not state or prove it. But it is also not new mathematics: it is a
  machine-checked instance of the Davis-Kahan-based graph-perturbation
  stability arguments already published informally (von Luxburg 2007;
  Gama & Ribeiro; Levie et al.). Cite the LapPE/SAN papers as motivation
  for *why this matters*, and the stability-theory line as the actual
  mathematical precedent — not as an unclaimed first proof.

## QA

Extend `Fiedler_QA.lean`'s pattern to a `k = 2` (or `k = 3`) instance on a
small graph family analogous to the existing P₃→K₃ headline instance,
exercising a case the `k = 1` QA does not: a genuine rank-3 (or rank-4)
subspace, an eigenvalue separation computed independently at that rank, and
the same connected-kernel / disconnected-fence pattern already proved for
`k = 1`. Reuse the existing norm-pinning technique
(`l2OpNorm_rankOne_le`/`abs_quadForm_le_of_l2OpNorm_le`) for the
perturbation norm where the fixture allows it.

## Acceptance criteria

- No new axiom, `sorry`, or `admit`.
- `#print axioms` on both new theorems reads exactly
  `propext, Classical.choice, Quot.sound` (pure hard crust, matching every
  theorem it's built from).
- The existing `fiedlerSubspace_stability`/`fiedlerLine_stability` public
  statements are unchanged (either superseded-but-kept as `k = 1`
  corollaries, or left standing and cross-referenced — no silent removal).
- At least one QA instance at `k ≥ 2` that could not have been produced by
  the existing `k = 1` theorems alone.
- The delivered docstring states the "honest scope limits" section above
  in the module itself, not only in this proposal.
- Full ladder: `lake build`, `check_build_completeness.py`, `lint_axioms`
  (no new axioms — count unchanged), `check_citations`, `check_markdown_links`,
  map-freshness stats sync (QA count up), records ladder (this proposal's
  own Delivered-table entry, README/radar/scoreboard/map stamps,
  `AGENT_ACTIVITY.md`/`EXECUTION_PLAN.md`) completed in the same delivery.

## Deferred / out of scope

- Exposing this bound through the Python certificate bridge
  (`docs/arch/python-certificate-bridge.md`) so a NetworkX/PyGSP/PyTorch-
  Geometric user could get a certified numerical stability radius directly
  — a natural follow-on, not part of this proposal.
- Any method for finding or tightening `δ` automatically (e.g. via
  Weyl-type single-eigenvalue perturbation bounds already in the shelf) —
  a separate proposal if wanted.
- Extending the bound to individual eigenvector coordinates rather than
  the subspace — flagged above as the wrong question, not a deferred
  version of the right one.
