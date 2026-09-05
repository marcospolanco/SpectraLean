# Adversarial Fence Audit of the Normalized-Laplacian Family

**Status:** COMPLETE (delivered 2026-09-04, run `20260904T211519Z-run-1`,
session `ses_f91be1675ffeQoVWVaTEPa5fHp`; all 27 priced fences closed —
see the delivery record)
**Method:** `governance/ADVERSARIAL_REVIEW.md` (fourteenth application)
**Family:** `Scaffold/Mathlib/GraphTheory/Normalized.lean` — the
general (irregular) normalized Laplacian program's root shelf: the
diagonal degree square roots, the congruence bridge
`√D L_sym √D = L`, the degenerate-degree corners, the walk transition
matrix and walk Laplacian, the eigenpair transfer through the
similarity, and the conjugated-power transfer — plus its pre-discipline
QA (`Scaffold/QA/SpectralGraph/Normalized_QA.lean`, 391 lines:
positive instantiations at the 3-path and the 2-edge plus two guard
lemmas, zero hypothesis-form fence sections).

## Step-0: selection survey (run in full, correcting the prior survey's scope)

The prior terminal handoff (Davis–Kahan core audit, 2026-09-04) named
the remaining pre-discipline QA families as "`BandDavisKahan`'s
shelf-clause surface, `Poincare_QA` (0 consumers, 663 lines), and
`SpectralCertificates_QA` (0, 498 lines) — a fresh Step-0 consumption
survey should again pick." Its own survey table, however, priced only
the candidates the handoff named, and its delivery record claims the
four Davis–Kahan shelves are "the four most-consumed unaudited surfaces
in the library." That claim was an artifact of the candidate list. A
fresh reverse-import walk over **every** shelf whose QA carries no
fence section (not just the named ones) gives:

| Candidate shelf | transitive non-QA consumers | QA state |
| --- | --- | --- |
| `GraphTheory/Normalized` | **20** (Directed, Heat, IrreducibleStationary, PageRank, Poincare, Stationary, VariationalTransfer + derived capstones) | `Normalized_QA.lean` pre-discipline |
| `OperatorTheory/Resolvent` | 16 | several free-form negative witnesses, never adversarially re-read |
| `GraphTheory/VariationalTransfer` | 13 | 170 lines, zero negative witnesses |
| `LinearAlgebra/PerronFrobenius` | 7 | pre-discipline |
| `GraphTheory/Directed` + `Stationary` | 3 + 4 | pre-discipline |
| `GraphTheory/RandomWalk` | 5 | pre-discipline |
| `GraphTheory/Heat` | 8 | already fenced (entropy/heat audits) |
| `Perturbation/BandDavisKahan` | 0 | four delivery-scoped fences |
| `GraphTheory/Poincare` | 0 | pre-discipline |
| `GraphTheory/SpectralCertificates` | 0 | pre-discipline |

`Normalized.lean` wins decisively and is also the *root* of the
irregular/mixing program: `VariationalTransfer` (13) consumes it
directly, and the shelf's congruence bridge and similarity transfer
sit under every normalized statement the mixing cascade, the Poincaré
program, and the derived capstones state. Its QA file predates the
adversarial-review discipline (first fence audits landed 2026-09-02)
and carries zero fence sections.

## Step-0 findings that shaped the pricing (recorded before any Lean)

Two pricing findings, both from hand analysis of the junk arithmetic at
nonpositive degrees (`Real.sqrt` of a nonpositive number is `0`, and
`0⁻¹ = 0`, so `degreeInvSqrt` vanishes at every nonpositive degree):

1. **Zero-degree corners junk-collapse the forward-transfer family
   both-sidedly.** At a fixture whose only defect is a zero-degree
   vertex (e.g. `!![0,1,1;1,0,1;0,0,0]]`, degrees 2/2/0), the dropped-`hd`
   statement of `walkLaplacian_mulVec_degreeInvSqrt` is *provable*: on
   rows with positive degree the transfer equation is the `L_sym`
   eigen-equation rescaled (the junk column terms are `0` on both
   sides — `L_sym i j` is junk-zero at `deg j = 0` exactly when the
   transfer's `A i j v j /√(deg j)` term is junk-zero), and on
   zero-degree rows both sides vanish. The truth-removable (P4) corner
   class the companion-audit discipline warns about, first at this
   scale: **pricing a transfer `hd` clause at a zero-degree fixture
   would have produced a fence that cannot exist.**
2. **Negative-degree rows are the genuine breaker.** At a vertex with
   `deg < 0`, `√(deg) = 0` kills the `degreeInvSqrt` column *and* the
   `degreeSqrt` row, but `(deg)⁻¹` in the walk matrix is *genuine*
   (nonzero!). The walk Laplacian's row then moves mass off the
   conjugated vector while both normalized-side terms vanish. The Fin 2
   mixed-sign fixture `!![-2, 1; 1, 0]]` (degrees −1, 1; `L_sym`
   degenerates to the *identity*, so every vector is a genuine
   eigenvector at `μ = 1`) kills the whole transfer trio's `hd` clauses
   with clean junk-free arithmetic.

## Priced clause inventory

Fixtures (all new, `nf`-prefixed, no namespace collisions — the QA
namespace `SpectralGraphTheory.QA` is shared with the other SpectralGraph
QA files):

- `nfAdj = !![0,1,1;1,0,1;0,0,0]]` — symmetric, degrees (2,2,0), both
  positive vertices adjacent to the zero-degree vertex. `L_sym` is the
  block matrix `!![1,−1/2,0;−1/2,1,0;0,0,1]]` (the junk kills row/col 2).
- `nfNegEdge = !![-2,1;1,0]]` — symmetric, degrees (−1,1), one genuine
  negative row. `degreeInvSqrt = diag(0,1)`, `L_sym = 1` (identity),
  `P = !![2,−1;1,0]]`, `L_walk = !![−1,1;−1,1]]`.
- `nfNegI = !![-1,0;0,-1]]` — symmetric, degrees (−1,−1).
- `nfAsymAdj = !![0,2;1,0]]` — asymmetric, degrees (2,1) both positive.
- the delivered `edgeAdj2` (K₂) reused.

### The diagonal layer — 5 fences

| # | Theorem | Clause | Refutation (all other clauses genuine) |
| --- | --- | --- | --- |
| A1 | `degreeSqrt_mul_degreeSqrt` | `hdeg : 0 ≤ deg` | `nfNegI`: `√D = 0` so LHS `= 0`, but `degreeMatrix = diag(−1,−1) ≠ 0` |
| A2 | `degreeSqrt_mul_degreeInvSqrt` | `hd : 0 < deg` | `nfAdj` entry (2,2): `√0 · (1/√0) = 0 ≠ 1` |
| A3 | `degreeInvSqrt_mul_degreeSqrt` | `hd` | mirror of A2 |
| A4 | `degreeInvSqrt_mulVec_ne_zero` | `hd` | `nfAdj`, `v = e₂ ≠ 0`: `D⁻¹ᐟ² *ᵥ e₂ = 0` |
| A5 | `degreeInvSqrt_mulVec_ne_zero` | `hv : v ≠ 0` | `v = 0` anywhere: image is `0`, claim `0 ≠ 0` |

### The normalized layer — 7 fences

| # | Theorem | Clause | Refutation |
| --- | --- | --- | --- |
| B1 | `normalizedLaplacian_symmetric` | `hA : A.IsSymm` | `nfAsymAdj` (degrees positive, no junk): `L_sym 0 1 = −√2 ≠ −1/√2 = L_sym 1 0`. **The family's only signature-free symmetry clause** — every other `hA` is consumed by an `eigvecOf`/`walkEvals` display |
| B2 | `degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt` | `hd` | `nfAdj` entry (0,2): LHS `= √2·0·0 = 0`, RHS `= −A 0 2 = −1` |
| B3 | `normalizedLaplacian_mul_degreeSqrt` | `hd` | `nfAdj` entry (0,2): LHS `= L_sym 0 2 · √0 = 0`, RHS `= (1/√2)·(−1)` |
| B4 | `normalizedLaplacian_mulVec_degreeSqrt_onesVec` | `hd` | `nfAdj`: `√D *ᵥ 1 = (√2,√2,0)`, `L_sym` maps it to `(√2/2,√2/2,0) ≠ 0` |
| B5 | `normalizedLaplacian_eq_one_of_forall_deg_nonpos` | `hdeg` | `edgeAdj2`: `L_sym = 1 − A ≠ 1` |
| B6 | `normalizedLaplacian_eq_regularNormalizedLaplacian` | `hd` | `edgeAdj2` with claimed `d = 2` (`hdpos` genuine): `1 − A ≠ 1 − ½A` at entry (0,1) |
| B7 | `normalizedLaplacian_eq_regularNormalizedLaplacian` | `hdpos` | `nfNegI` with `d = −1` (`hd` genuine): `L_sym = 1` (junk identity) vs `1 − (−1)⁻¹(−1·1) = 0` |

### The walk layer — 9 fences

| # | Theorem | Clause | Refutation |
| --- | --- | --- | --- |
| C1 | `walkTransitionMatrix_row_sum` | `hd` | `nfAdj`, `i = 2`: every entry `0⁻¹·A 2 j = 0`, sum `0 ≠ 1` |
| C2 | `walkTransitionMatrix_mulVec_one` | `hd` | `nfAdj`: `(P *ᵥ 1) 2 = 0 ≠ 1` |
| C3 | `degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt` | `hd` | `nfAdj` entry (2,2): LHS `= √0·(…)·0 = 0`, RHS `= L_sym 2 2 = 1` |
| C4 | `walkLaplacian_mulVec_degreeInvSqrt` | `hd` | `nfNegEdge`, `v = ![0,1]`, `μ = 1` (`h` genuine — `L_sym = 1`): `L_walk *ᵥ ![0,1] = ![1,1] ≠ ![0,1] = 1 • ![0,1]` |
| C5 | `walkLaplacian_mulVec_degreeInvSqrt` | `h : L_sym *ᵥ v = μ • v` | `edgeAdj2` (`hd` genuine), `v = e₀`, `μ = 0`: claim `L *ᵥ e₀ = 0` but `= ![1,−1]` |
| C6 | `normalizedLaplacian_mulVec_degreeSqrt` | `hd` | `nfNegEdge`, `w = ![1,1]`, `μ = 0` (`h` genuine — `L_walk *ᵥ ![1,1] = 0`): `√D *ᵥ w = ![0,1]`, `L_sym *ᵥ ![0,1] = ![0,1] ≠ 0` |
| C7 | `normalizedLaplacian_mulVec_degreeSqrt` | `h` | `edgeAdj2`, `w = e₀`, `μ = 0`: `L_sym *ᵥ e₀ = ![1,−1] ≠ 0` |
| C8 | `walkTransitionMatrix_mulVec_degreeInvSqrt` | `hd` | `nfNegEdge`, `v = ![0,1]`, `μ = 1` (`h` genuine): `P *ᵥ ![0,1] = ![−1,0] ≠ 0 = (1−1)•![0,1]` |
| C9 | `walkTransitionMatrix_mulVec_degreeInvSqrt` | `h` | `edgeAdj2`, `v = e₀`, `μ = 0`: `P *ᵥ e₀ = ![0,1] ≠ ![1,0] = (1−0)•e₀` |

### The eigenbasis layer — 4 fences (hA clauses signature-entangled: `eigvecOf`/`walkEvals` displays)

| # | Theorem | Clause | Refutation |
| --- | --- | --- | --- |
| D1 | `walkLaplacian_mulVec_eigvecOf` | `hd` | `nfNegEdge`, witness index `i₀` = 0 if `(u₀) 1 ≠ 0` else 1 (exists by `eigvecOf_inner` orthonormality — if both basis vectors had vanishing second coordinate they would be parallel multiples of `e₀`): at `i₀`, `D⁻¹ᐟ² *ᵥ u = (0, u 1)` with `u 1 ≠ 0`, `L_walk *ᵥ (0, u 1) = (u 1, u 1)` whose coordinate 0 `= u 1 ≠ 0` while the RHS's coordinate 0 is `λᵢ·0 = 0` — **no eigenvalue pin needed** |
| D2 | `walkTransitionMatrix_mulVec_eigvecOf` | `hd` | same witness: `P *ᵥ (0, u 1) = (−u 1, 0)` whose coordinate 1 is `0 = (1−λᵢ)·u 1 ≠ 0` |
| D3 | `walk_eigvec_expansion` | `hd` | `nfNegEdge`, `w = e₀`: `√D *ᵥ e₀ = (√(−1)·1, √1·0) = 0`, so every coefficient `u i ⬝ᵥ 0 = 0` and the sum is `0 ≠ e₀` — no Parseval needed |
| D4 | `exists_eigenvector_walkTransitionMatrix_eq_walkEvals` | `hd` | `nfNegEdge`, `k = ⟨0⟩`: `L_sym = 1` transported by `evals_congr` + `evals_one` gives `walkEvals = 1 − 1 = 0`; the claim `∃ w ≠ 0, P *ᵥ w = 0` dies by row equations (`2w₀ = w₁`, `w₀ = 0` ⟹ `w = 0`; `det P = 1 ≠ 0`) |

### The power layer — 2 fences

| # | Theorem | Clause | Refutation |
| --- | --- | --- | --- |
| E1 | `degreeSqrt_mul_walkTransitionMatrix_eq` | `hd` | `nfAdj` entry (0,2): LHS `= √2·(1/2) = √2/2`, RHS `= (1−L_sym) 0 2 · √0 = 0` |
| E2 | `degreeSqrt_mulVec_pow_walkTransitionMatrix` | `hd` | `nfAdj`, `t = 1`, `g = e₂`: LHS `= √D *ᵥ (P *ᵥ e₂) = (√2/2, √2/2, 0)`, RHS `= (1−L_sym) *ᵥ (√D *ᵥ e₂) = (1−L_sym) *ᵥ 0 = 0` |

### Non-fenceables, mechanism recorded

- `eigvecOf_ne_zero`'s `hM`: display-entangled (`eigvecOf M hM i`).
- Every `hA` clause whose display carries
  `eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA)`
  or `walkEvals A hA` (D-layer statements, `walk_eigvec_expansion`,
  `exists_eigenvector_…`): the signature-entanglement class. **B1 is
  the family's one exception** and is fenced.
- The hypothesis-free entry forms (`degreeSqrt_mulVec_apply`,
  `degreeInvSqrt_mulVec_apply`, `walkTransitionMatrix_apply`,
  `degreeInvSqrt_apply_eq_zero_iff`): no clause surface.

Total: **27 priced fences** + per-fixture isolation companions (packaged
per fixture where several fences share one kept-genuineness set) +
fixture/entry pins.

## Plan

QA-only, zero axiom contact (count stays 4; every fence is a theorem
instantiation — nothing admitted is consumed, so no `-- @refutes`
tags). Spike first in `wip/nfences_spike.lean` to zero errors/zero
warnings, then land as a pure insertion: a new `AdversarialFences`
section in `Normalized_QA.lean`. Full verification ladder after the
landing, `#print axioms` audit on every new declaration via a generated
`wip/` file.

## Delivery record (2026-09-04)

DELIVERED at the full priced scope — all 27 fences closed with packaged
isolation companions. QA-only, pure hard crust: QA 5045 → 5116 (+71 by
the generator metric; 75 declarations = 71 theorems + 4 fixture `def`s),
zero axiom contact (`#print axioms` via `wip/nfences_axcheck.lean` on
all 75 declarations — every one exactly `propext, Classical.choice,
Quot.sound`; no `-- @refutes` tags — theorem instantiations, nothing
admitted consumed). Landed as a pure insertion (+903/0 in numstat): the
`AdversarialFences` section of `Normalized_QA.lean`, spiked first in
`wip/nfences_spike.lean` to zero errors/zero warnings.

**A pricing revision the spike itself forced, recorded as the audit's
headline finding.** The originally priced Fin 3 fixture
`!![0,1,1;1,0,1;0,0,0]]` was accidentally *asymmetric* (`A 0 2 = 1 ≠ 0 =
A 2 0`), breaking the `hA`-genuineness requirement of every
matrix-identity fence priced there. Repairing the symmetry (an isolated
vertex in a symmetric matrix has no incident edges at all) exposed a
sharper truth, recorded here as a P4-class finding at scale: **at
symmetric zero-degree fixtures, the dropped-`hd` statements of the
congruence bridge, the left-multiplied congruence, the commutation
form, and the conjugated-power transfer are *provable* — the junk kills
both sides of each identity identically** (`L_sym`'s junk-zero entries
at `deg j = 0` cancel exactly the `√(deg j)` column factors, and the
isolated row/col of `L` is zero on both sides). Pricing those four
fences at a zero-degree fixture would have produced fences that cannot
exist. The genuine breaker is the **negative-degree row**: there
`(deg)⁻¹` in the walk matrix is *genuine* (nonzero) while
`degreeSqrt`/`degreeInvSqrt` vanish, so the two sides of every identity
separate. One Fin 2 fixture carries almost the whole delivery:

**`nfNegEdge = !![-2, 1; 1, 0]]`** (symmetric, degrees (−1, 1)):
`degreeSqrt = degreeInvSqrt = diag(0, 1)`, `L_sym` degenerates to the
identity, `P = !![2, −1; 1, 0]]`, `L_walk = !![−1, 1; −1, 1]]` — all
rational, no `√` atoms. It kills: B2 (the bridge `diag(0,1) ≠ L` at
(0,0): `0 ≠ 1`), B3 (`(1,0)`: `0 ≠ −1`), B4 (the stretched constant
`√D *ᵥ 1 = ![0,1]` survives the identity `L_sym`), C3 (the similarity
`diag(0,1)·L_walk·diag(0,1) = diag(0,1) ≠ 1`), C4/C6/C8 (the transfer
trio: the `L_sym`-eigen-hypotheses genuine — `L_sym *ᵥ ![0,1] = 1•![0,1]`
and `L_walk *ᵥ ![1,1] = 0` — while `L_walk *ᵥ ![0,1] = ![1,1] ≠ ![0,1]`,
`L_sym *ᵥ ![0,1] = ![0,1] ≠ 0`, `P *ᵥ ![0,1] = ![−1,0] ≠ 0`),
D1/D2 (the eigenbasis instantiations at an orthonormality-witness index
— `nf_basis_second`: some `u i 1 ≠ 0`, else both basis vectors are
parallel multiples of `e₀` against `eigvecOf_inner` — with the
conjugated vector `![0, u 1]` whose transfer fails at coordinate 0
*without any eigenvalue pin*), D3 (the expansion at `w = e₀`: the
coefficient vector `√D *ᵥ e₀ = 0` collapses the whole sum to `0 ≠ e₀`),
D4 (the transferred spectrum `walkEvals = 1 − 1 = 0` via
`evals_congr`+`evals_one`, the existential dead by the pinned `P`'s row
equations `2w₀ = w₁, w₀ = 0`), and E1/E2 (the commutation at `(1,0)`:
`1 ≠ 0`; the power transfer at `t = 1, g = e₀`: `![0,1] ≠ 0`).

**The other fixtures:** `nfIso` (symmetric `K₂ ⊕ isolated`, degrees
(1,1,0)) kills A2/A3 (the product entry `√0·(1/√0) = 0 ≠ 1`), A4 (the
conjugation annihilates `e₂`), C1/C2 (the junk row of `P` sums to `0
≠ 1` and `(P *ᵥ 1) 2 = 0 ≠ 1`) — the zero-degree corner's genuine
separations; `nfNegI = diag(−1,−1)` kills A1 (`√D·√D = 0 ≠ diag(−1,−1)`)
and B7 (`L_sym = 1` vs `1 − (−1)⁻¹•A = 0` at `d = −1` with `hd`
genuine); `nfAsymAdj = !![0,2;1,0]]` (degrees (2,1), no junk) kills B1
— `L_sym 0 1 = −√2 ≠ −1/√2 = L_sym 1 0`, the family's only
signature-free symmetry clause; the delivered `edgeAdj2` (K₂) kills B5
(`1 − A ≠ 1`), B6 (wrong `d = 2` with `hdpos` genuine), A5 (`v = 0`),
and the transfer trio's `h` clauses C5/C7/C9 (non-eigenvector `e₀` at
`μ = 0`, `hd` genuine). Non-fenceables recorded with mechanisms: the
`eigvecOf`/`walkEvals` display-entangled `hA` clauses and
`eigvecOf_ne_zero`'s `hM` (the signature-entanglement class).

**Technique findings** (for the next audit's trap list):

1. **Constant rows defeat `simp`'s entry reduction** — `![0,0,0]`-rows
   of literal matrices normalize to `vecHead (vecTail (fun i => 0))`
   which no `cons_val` lemma matches; the robust route is the explicit
   chain `Matrix.cons_val_zero/one/two + Matrix.tail_cons +
   Matrix.head_cons` in a `simp only` set (empirically necessary at
   every isolated-vertex fixture).
2. **`norm_num [Matrix.transpose_apply, fixture]` closes literal-matrix
   symmetry where `simp [fixture]` does not** — the Fin 3 isSymm goals
   that survived `simp` closed uniformly under `norm_num` with the same
   lemma arguments.
3. **A deg-pin lemma and the fixture name cannot share one
   `simp only` set** — the def-unfold rewrites `deg fixture i` before
   the pin can match; unfold `deg` inline (with `Fin.sum_univ_two` +
   cons lemmas + `norm_num`) instead of carrying named degree pins.
4. **`decide +kernel` does not exist in the pinned Lean** —
   `![1−1, 1−1] = 0`-style function equalities close by `funext` +
   the index-disjunction `rcases` + `simp only [cons lemmas]`.
5. **`Matrix.mul_eq_mul`/`Matrix.pow_one` are not constants here** —
   matrix-power-one is plain `pow_one`; entry access after rewriting
   diagonal pins goes through `Matrix.diagonal_mul`/`Matrix.mul_diagonal`
   directly.
6. **`push_neg` on `¬∃ i, P i` yields a ∀ that must be applied, not
   projected** — `hcon.0` on the pushed form is invalid field notation;
   use `hcon 0`/`hcon 1`.

**Verification:** spike first (`wip/nfences_spike.lean` — the full
75-declaration delivery, iterated to zero errors/zero warnings over six
fix rounds, all in recorded trap classes); `lake env lean` on the landed
module (zero errors, zero warnings); explicit `lake build
Scaffold.QA.SpectralGraph.Normalized_QA` ✔ (the build's only warning is
the shelf `Normalized.lean`'s own pre-existing `congr 1` linter note,
untouched by this delivery); the 75-declaration axiom audit above; the
**full `lake build` ✔ immediately followed by `check_build_completeness.py`
— 133 source files, 133 fresh artifacts, 0 stale, 0 missing, exit 0**;
`lint_axioms` exit 0 (4 current axioms, unchanged; only the
allowlisted-confirmed PF finding); `check_refutation_independence`
(9-tag clean — no tags touched); `check_public_reachability` clean (63
repo modules); `check_citations` ("All axioms have proper citations!");
`check_markdown_links` clean; `check_backlog_freshness` clean;
scoreboard regenerated (**5116/4/0**) with the verification row;
map-freshness exit 0 after the 5045 → 5116 stats sync in both map data
files and SVG regeneration (49 stations, no status change — none owed).
The landing verified a pure insertion (903/0 in numstat). Records
updated: this proposal, `proposals/README.md` (new Delivered row),
README (5116 + the walks-and-mixing row's audit clause), the radar (QA
row synced, held 4.5), `index/map/spectral_graph.md` (the audit
paragraph in the Normalized section), the backlog item-2
falsification-surface note, the scoreboard verification row, both map
data tables + regenerated SVG, the execution plan, and the activity
log. Nothing committed; the prior runs' uncommitted deliveries
preserved.
