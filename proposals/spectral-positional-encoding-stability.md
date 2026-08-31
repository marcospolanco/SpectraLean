# Proposal: Certified Stability for Laplacian Positional Encodings

**Status:** COMPLETE (delivered 2026-08-31, run
`20260831T011543Z-run-1` — see the delivery record at the end). The
general-rank pair is on the shelf with the `k = 1` pair re-proved as
corollaries; the `k ≥ 2` QA exceeds the acceptance criteria (the bound
is exactly attained at the fixture). Zero new axioms.

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

## Delivery record (2026-08-31, run `20260831T011543Z-run-1`)

Delivered in one run, spike-first (`wip/lappe_spike.lean` iterated to
zero errors before any shelf edit).

**The theorems** (`Scaffold/Mathlib/GraphTheory/Fiedler.lean`, the new
"Spectral-encoding stability: the general-rank Davis–Kahan family"
section):

- `spectralEncodingSubspace_stability` — the general-`k` form, at the
  proposal's sketch shape modulo the mechanical index bookkeeping (the
  separation's upper index `⟨(k : ℕ) + 1, hk⟩` replacing the literal
  `⟨2⟩`; the `3 ≤ card` hypothesis subsumed by `hk`).
- `spectralEncoding_stability` — the kernel-isolated general-`k` form,
  hypothesis stack exactly as sketched.
- `fiedlerSubspace_stability` and `fiedlerLine_stability` **re-proved as
  one-line corollaries at unchanged public statements** — the option the
  proposal left open, chosen deliberately: it machine-checks the claim
  that nothing in either proof used `k = 1` specifically. Technique
  note (recorded for future re-parameterizations): the corollary
  instantiation needs `show (1 : ℕ) + 1 < Fintype.card V; omega` for the
  `hk` argument — a bare `by omega` there sees the goal through the
  opaque double coercion `↑↑⟨1, ⋯⟩` of the not-yet-elaborated `k`
  binder and fails.
- The section docstring carries the full honest-scope-limits block
  (subspace-not-entrywise; both graphs connected for the isolated form;
  `δ` the caller's obligation; not a restatement of the ML papers) plus
  the citations the proposal's scope-limits section required: LapPE
  (Dwivedi & Bresson, AAAI 2021) and SAN (Kreuzer et al., NeurIPS 2021)
  as motivation; von Luxburg 2007 and the Gama & Ribeiro / Levie et al.
  line as the informal mathematical precedent.

**The QA** (`Fiedler_QA.lean`, the new SpectralEncodingStability
section, +53 counted declarations) — the star `K₁,₃ → K₄` fixture on
`Fin 4` at `k = ⟨2⟩`, a rank the existing `k = 1` theorems cannot
express:

- The full star spectrum `{0, 1, 1, 4}` pinned: `⟨0⟩ = 0`
  (`laplacian_evals_zero`), `λ₂ = 1` (variational `≥` on the zero-sum
  constraint `E = ‖x‖² + 4x₀²`; `≤` inherited from the `⟨2⟩ ≤ 1` bound
  by sortedness), `⟨2⟩ = 1` (Rayleigh–Ritz engine
  `evals_le_of_linearIndependent` at the test family
  `{ones, v₁, v₂}` — on its span `E = ‖x‖² − 4·(kernel coefficient)²`,
  the RR bound tight off the kernel), `⟨3⟩ = 4` (eigenvector witness
  `![3, −1, −1, −1]` through `exists_eigvalOf_eq_of_mulVec_eq_smul` +
  `eigvalOf_le_evals_last`; `≤` side by the RR engine at the full
  standard basis with the universal `E ≤ 4‖x‖²` via Cauchy–Schwarz).
- The separation `3 ≤ λ₄(L K₄) − λ₃(L star)` pinned independently at
  that rank: the `K₄` top `4` by the same two-sided machinery (its
  `⟨2⟩ = 4` additionally by trace arithmetic — `⟨1⟩ + ⟨2⟩ = 8` with
  `⟨1⟩ ≤ ⟨2⟩ ≤ 4` forces both to `4`).
- The perturbation norm `‖L(triangle)‖ = 3` two-sided: `≤ 3` through
  the bracketed triangle spectrum `{0, 0, 3, 3}` (its `⟨1⟩ = 0` by the
  RR engine at the kernel family `{ones, e₀}`) and
  `l2OpNorm_le_of_abs_evals_le`; `≥ 3` by the quadForm witness at the
  top eigenvector `![0, 1, −1, 0]` (`6 ≤ 2 · 3`).
- The rank-3 witness: `rank P_star⟨2⟩ = 3` through
  `rank_spectralProjector_evals_of_lt` at the strict gap `1 < 4` — the
  bounded subspace is genuinely rank 3.
- Both theorem instances, bounds evaluating to `‖L(triangle)‖ / 3 = 1`;
  the kernel-isolated instance threads both connectivity hypotheses,
  with the common-kernel identification instantiated at the fixture.
- **The exact-attainment pin**
  `seSubspace_star4_K4_distance_eq_one_QA`:
  `‖P_{K₄}⟨2⟩ − P_star⟨2⟩‖ = 1`, not merely `≤ 1`. The `K₄` projector
  at its threshold `4` is the identity (`spectralProjector_eq_one`,
  `evals⟨2⟩(K₄) = 4` from the trace route); the star projector kills
  the top unit eigenvector `u` (the eigenvalue `4` exceeds the
  threshold `1`, so every filtered eigenbasis coordinate vanishes by
  `eigvecOf_inner`); the difference acts as the identity on `u`, so
  `quadForm D u = u ⬝ᵥ u = 1`, and the norm→form transfer
  (`abs_quadForm_le_of_l2OpNorm_le`) closes the lower side. The
  general-rank bound is tight at this fixture — the strongest QA shape
  a bound theorem can have.

**Acceptance criteria check:** no new axiom/`sorry`/`admit` ✓;
`#print axioms` on all 18 audited declarations (both new theorems, both
re-proved corollaries, the load-bearing QA members) exactly
`propext, Classical.choice, Quot.sound` via `wip/lappe_axcheck.lean` ✓;
the two existing public statements unchanged (re-proved, not removed) ✓;
QA at `k ≥ 2` not producible by the `k = 1` theorems (every declaration
bounds or pins a `⟨2⟩`-indexed object) ✓; honest scope limits stated in
the module itself ✓; full ladder in the scoreboard verification row
(direct elaboration of both modules with zero warnings — the QA warning
baseline compared zero-against-zero with the HEAD file by pair
elaboration — explicit build targets, full build + completeness
130/130/0/0, `lint_axioms` 5, refutation-independence 10-tag clean with
no tags added since nothing touches an axiom, citations, links,
scoreboard 3172 → 3225/5/0, map-freshness exit 0 after the stamp sync)
✓.

**Records closed:** this proposal, `proposals/README.md` (the Medium-High
row retired to the Delivered table), README (3225 + the highlights
bullet), the radar QA axis (3172 → 3225, score held at 4.0 per
protocol — a new-rank instantiation of the already-counted Davis–Kahan
consumer family), `index/map/spectral_graph.md` (the general-rank
section's two rows), the scoreboard verification row, both map stamps +
the regenerated SVG, the execution plan, and the activity log.

**Deferred as proposed:** the Python certificate bridge, automatic `δ`
certification, and any entrywise extension — all recorded in the
proposal's own Deferred section, none started.
