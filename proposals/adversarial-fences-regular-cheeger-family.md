# The Regular Cheeger Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-04 by run `20260904T081201Z-run-1`,
session `ses_f94971976ffeQBnoJ3RSeT9ZJQ`; delivery record below)
**Opened:** 2026-09-04
**Method:** `governance/ADVERSARIAL_REVIEW.md` (hypothesis necessity per
clause, cross-checked against every existing fence in the repository)

## Scope

The audit-shaped adversarial pass over the **regular Cheeger family** —
`Scaffold/Mathlib/GraphTheory/Cheeger.lean`'s regular layer (lines up to
the volume-weighted sections, which the 2026-09-04 irregular audit
already covered):

- the proved inequality pair at the normalized spelling
  (`cheeger_upper_bound`, `cheeger_lower_bound`);
- the combinatorial spelling twins (`cheeger_lower_bound_laplacian`,
  `cheeger_upper_bound_laplacian`);
- the sweep lemma (`cheeger_sweep`);
- the PSD engine (`regularNormalizedLaplacian_psd`);
- the cheapest bridge/junk corners of the cut-test-vector layer
  (`cutTestVector_ne_zero`).

This is the SGT center namesake cluster: the strategy document's first
working ring. It is the **most-consumed unaudited cluster in the
library** — six non-QA import consumers (`Normalized`, `Fiedler`,
`RandomWalk`, `AlonBoppana`, `VariationalTransfer`,
`Derived/EdgePerturbationTail`) — and its QA
(`Scaffold/QA/SpectralGraph/Cheeger_QA.lean`, last touched 2026-08-24)
predates the adversarial-review discipline (2026-09-02). The prior
terminal handoff names exactly this class of target: "the audit method's
natural next targets, if no gate opens, are the other pre-discipline QA
families outside the mixing cascade."

Already fenced (delivery-scoped, recorded not duplicated):
`core_sum_abs_sq_sub_sq`'s `hA`
(`core_sum_abs_sq_sub_sq_asymmetry_refuted_QA`),
`sum_edgeWeight_sq_posPart_add_sq_negPart_le`'s `hnn`
(`pair_contraction_refuted_QA`), `coarea_core`'s minority clause
(`coarea_minority_refuted_QA`), `cheeger_sweep_cut`'s `horth`
(`sweep_cut_orth_dropped_refuted_QA`), and the historical
`old_cheeger_lower_bound_refuted_QA` (the 2026-08-18 statement repair).

## Step-0 findings: the priced fence list

21 core fences plus 4 cheap junk corners. Every fence is a
hypothesis-form negative witness (the negation of the conclusion at a
specific instantiation, both sides pinned to rationals) plus an
isolation companion (every other hypothesis verified genuine at the
fixture, the dropped one verified failing). All fixtures are 2×2 or 3×3
with rational spectra, pinned through the shelf's own engines — the
subspace Rayleigh–Ritz engine `evals_le_of_linearIndependent` (no PSD,
no kernel — the upper-bound direction), the eigenvalue-witness bridge
`exists_eigvalOf_eq_of_mulVec_eq_smul` + `eigvalOf_le_evals_last`
(the lower-bound direction at two vertices, where `secondEval` is the
top entry), and `secondEval_variational` (PSD supplied by hand through
the three-term SOS identity at the 3-vertex fixture).

Fixtures (new, all in the QA section):

- `rcSAdj = !![3, -1; -1, 3]` — signed, symmetric, genuinely
  `d = 2`-regular (`deg = 3 - 1`), `A 0 1 = -1 < 0`: kills every `hnn`
  clause. Spectrum of `I - A/2`: `{-1, 0}`, `λ₂ = 0`; `φ = -1/2`.
- `rcNegDAdj = !![-3, 1; 1, -3]` — signed, genuinely `d = -2`-regular:
  kills every `hdpos` clause of the normalized statements. `I + A/2`
  has spectrum `{-1, 0}`, `λ₂ = 0`; `φ = -1/2`.
- `rcPosAdj = !![2, 1; 1, 2]` — nonnegative, symmetric, genuinely
  `d = 3`-regular: kills every `hd` clause at a *claimed* wrong degree
  (`d' = 4`, `d' = 1`, `d' = 1/8`, `d' = 40` per statement).
  `φ = 1/3`; `L = [[1,-1],[-1,1]]` with `λ₂(L) = 2` (witness
  `(1,-1)`); `quadForm (I - A/1) x = -(x₀ + x₁)²` (SOS).
- `rcTriAdj = !![1, -1, -1; -1, 1, -1; -1, -1, 1]` — signed 3-vertex,
  genuinely `d = -1`-regular: kills the lower-bound twin's `hdpos`.
  `L = J - 3I`, `λ₂ = -3` pinned from the ⊥1 plane (`R = -3` there,
  the subspace engine at `k = 2`); `φ = 1`; `d·φ²/2 = -1/2 > -3`.
- `rcTri2Adj = !![-3, 1, 1; 1, -3, 1; 1, 1, -3]` — signed 3-vertex
  with positive off-diagonal, genuinely `d = -1`-regular: kills the
  upper-bound twin's `hdpos`. `L = 3I - J` (PSD by the three-term SOS),
  `λ₂ = 3` pinned from `secondEval_variational` (R ≡ 3 on ⊥1);
  `φ = -1`; `2dφ = 2 < 3 = λ₂`.
- `rcAsymPsdAdj = !![4, 1; 3, 2]` — nonnegative, row sums `5 = 5`
  (regular), **not symmetric**: kills the PSD engine's `hA` (the
  quadratic form sees the symmetric part `(A + Aᵀ)/2 = [[4,2],[2,2]]`,
  whose `(2,1)`-Rayleigh is `26/5 > 5`, so
  `quadForm (I - A/5) (2,1) = -1/5 < 0`).
- `rcZeroAdj` (the `2×2` zero matrix) — kills the cut-test-vector
  layer's `hd` (at claimed `d = 1`) and `hdpos` (at `d = 0`, regular:
  both degrees are `0`): `cutTestVector ≡ 0` on both sides of the cut.

The 21 core fences:

| # | Statement | Clause | Fixture / instantiation |
| - | --- | --- | --- |
| 1 | `cheeger_upper_bound` | `hnn` | `rcSAdj`, `d = 2`: `λ₂ = 0 ≤ 2φ = -1` false |
| 2 | `cheeger_upper_bound` | `hd` | `rcPosAdj` claimed `d' = 4`: `λ₂ = 3/4 > 2φ = 2/3` |
| 3 | `cheeger_upper_bound` | `hdpos` | `rcNegDAdj`, `d = -2`: `λ₂ = 0 > 2φ = -1` |
| 4 | `cheeger_lower_bound` | `hnn` | `rcSAdj`: `φ²/2 = 1/8 ≤ λ₂ = 0` false |
| 5 | `cheeger_lower_bound` | `hd` | `rcPosAdj` claimed `d' = 1`: `λ₂ = 0 < 1/18` |
| 6 | `cheeger_lower_bound` | `hdpos` | `rcNegDAdj`: `1/8 ≤ 0` false |
| 7 | `cheeger_sweep` | `hx0` | `edgeAdj`, `x = 0`: junk `R = 0 < 1/2` |
| 8 | `cheeger_sweep` | `horth` | `edgeAdj`, `x = 1`: `R = 0 < 1/2` |
| 9 | `cheeger_sweep` | `hnn` | `rcSAdj`, `x = (1,-1)`: `R = -1 < 1/8` |
| 10 | `cheeger_sweep` | `hd` | `rcPosAdj` claimed `d' = 1`, `x = (1,-1)`: `R = 0 < 1/18` |
| 11 | `cheeger_sweep` | `hdpos` | `rcNegDAdj`, `x = (1,-1)`: `R = -1 < 1/8` |
| 12 | `cheeger_lower_bound_laplacian` | `hnn` | `rcSAdj`: `d·φ²/2 = 1/4 ≤ λ₂(L) = 0` false |
| 13 | `cheeger_lower_bound_laplacian` | `hd` | `rcPosAdj` claimed `d' = 40`: `20/9 > λ₂(L) = 2` |
| 14 | `cheeger_lower_bound_laplacian` | `hdpos` | `rcTriAdj`, `d = -1`: `-1/2 ≤ λ₂(L) = -3` false |
| 15 | `cheeger_upper_bound_laplacian` | `hnn` | `rcSAdj`: `λ₂(L) = 0 ≤ 2dφ = -2` false |
| 16 | `cheeger_upper_bound_laplacian` | `hd` | `rcPosAdj` claimed `d' = 1/8`: `λ₂(L) = 2 > 1/12` |
| 17 | `cheeger_upper_bound_laplacian` | `hdpos` | `rcTri2Adj`, `d = -1`: `λ₂(L) = 3 > 2dφ = 2` |
| 18 | `regularNormalizedLaplacian_psd` | `hA` | `rcAsymPsdAdj`: `quadForm (I - A/5) (2,1) = -1/5` |
| 19 | `regularNormalizedLaplacian_psd` | `hnn` | `rcSAdj`: `quadForm (I - A/2) (1,-1) = -2` |
| 20 | `regularNormalizedLaplacian_psd` | `hd` | `rcPosAdj` claimed `d' = 1`: `quadForm (I - A) 1 = -4` |
| 21 | `regularNormalizedLaplacian_psd` | `hdpos` | `rcNegDAdj`: `quadForm (I + A/2) (1,-1) = -2` |

Plus the four cut-test-vector junk corners (22–25: `hd`, `hdpos` at
`rcZeroAdj`; `hS` at `S = ∅` and `hSc` at `S = univ` on `edgeAdj`,
where `cutTestVector ≡ 0` both times).

## Recorded non-fenceables (with mechanisms)

- **`hA` of `cheeger_upper_bound`, `cheeger_lower_bound`, and both
  `_laplacian` twins — structural.** The conclusions consume the
  symmetry proof itself (`regularNormalizedLaplacian_symmetric A hA d`
  inside `secondEval`, `lambda2 A hA hcard`), and
  `regularNormalizedLaplacian A d = 1 - d⁻¹ • A` is symmetric iff `A`
  is, so no asymmetric instantiation can supply the proof the
  conclusion demands. The same class as the prior audits' structural
  `hA` verdicts.
- **`hcard : 2 ≤ Fintype.card V` of all five spectral statements —
  structural** (consumed by the `secondEval`/`lambda2` signatures; the
  dropped statement is unstateable).
- **`cheeger_sweep`'s `hA` — genuinely mathematical, priced follow-on.**
  Unlike the five above, `cheeger_sweep`'s conclusion (`rayleigh`) is
  symmetry-free, so an asymmetric `d`-regular instantiation is
  stateable. The 2-vertex analysis closes negatively: with
  `A = !![a, p; q, b]]`, regularity forces `a + p = q + b = d`, and on
  the only ⊥1 direction `x = (1,-1)` the quotient is
  `R = (p + q)/d` while `φ = min(p,q)/d`, so
  `R ≥ 2·min(p,q)/d ≥ min(p,q)²/(2d²) = φ²/2` whenever `0 < min ≤ d` —
  the dropped statement holds on every 2-vertex instantiation. A
  refutation needs a ≥ 3-vertex asymmetric nonnegative regular fixture
  where the co-area pair-counting (`sum_pairAbs_eq_two_boundary`,
  itself `hA`-gated) fails against the one-sided directed boundary —
  the same shape as the irregular audit's priced sweep-`hA` follow-on.

## Priced cheap follow-ons (not pursued this run unless budget allows)

- `smul_regularNormalizedLaplacian`'s `hd` (at `edgeAdj`, claimed
  `d' = 2`: entry `2 ≠ 1`) and `hdne` (at `!![1,-1;-1,1]]`, genuine
  `d = 0`-regular, `LHS = 0 ≠ RHS = [[-1,1],[1,-1]]`).
- `vol_eq_of_regular`'s `hd` (`edgeAdj` claimed `d' = 2`: `1 ≠ 2`).
- `cutTestVector_dotProduct_onesVec`'s `hd` (irregular `!![1,1;1,2]]`:
  dot `1 ≠ 0`).
- `quadForm_regularNormalizedLaplacian`'s `hd`/`hdne`.

## Pricing revision (recorded at delivery)

The Step-0 pricing below was written before the spike and revised
during implementation by the isolation-companion audit, and the
revision is itself the survey's decisive finding: **`hnn` is a
co-hypothesis of every `hdpos` clause in this family** (both are
hypotheses of all five inequality statements and the PSD engine), so a
signed negative-degree fixture cannot fence `hdpos` — its companions
cannot be genuine. The satisfiable corner of the remaining hypotheses
(`hnn` + genuine `hd`) forces `d ≥ 0`, and `d = 0` with nonnegative
row sums forces the zero matrix, where the junk conductance `0/0 = 0`
makes four of the five dropped `hdpos` conclusions survive (sweep
`0 ≤ R = 1`; lower bound `0 ≤ 1`; both `_laplacian` twins `0 ≤ 0`;
PSD via `regNL = 1`). Only `cheeger_upper_bound`'s `hdpos` fails at
the corner (`λ₂ = 1 > 2φ = 0`), and it is fenced there. The four
surviving clauses moved to the non-fenceable list with this mechanism;
the 3-vertex signed fixtures (`rcTriAdj`, `rcTri2Adj`) were dropped
from the delivery accordingly, and everything landed at `2×2` fixtures
plus the existing `edgeAdj`.

## Discipline

QA-only: zero axiom contact (the family is pure hard crust — both
directions proved 2026-08-18/2026-08-23; `#print axioms` on every new
declaration must read exactly `propext, Classical.choice, Quot.sound`),
no `-- @refutes` tags (these refute *theorem* instantiations; nothing
admitted is consumed), no `sorry`/`admit`. Spike first in
`wip/regcheegerfences_spike.lean` to zero errors/zero warnings; land as
a pure insertion (a single `RegularFences` section appended to
`Cheeger_QA.lean` before the closing `end`s). The prior runs'
uncommitted deliveries preserved untouched.

## Delivery record (2026-09-04, run `20260904T081201Z-run-1`)

Delivered in full at the companion-audit-revised scope: **17 core + 4
junk-corner fences, each with an isolation companion**, as the
`RegularFences` section of `Cheeger_QA.lean` (a pure insertion, 939/0
in numstat; spiked first in `wip/regcheederfences_spike.lean` to zero
errors/zero warnings). 120 new declarations (117 public; the three
private pinning helpers audited transitively): the five fixtures
(`rcSAdj`, `rcPosAdj`, `rcAsymPsdAdj`, `rcZeroAdj`, and the reused
`edgeAdj`), the structural/conductance/operator-literal pins, the two
private Fin 2 pinning engines (eigenvalue-witness and
whole-space-subspace), the spectrum/Rayleigh pins, and the fences.
QA 4535 → 4648 (+113 by the generator metric). Zero axiom contact:
`#print axioms` via `wip/regcheederfences_axcheck.lean` on all 117
public declarations — every one exactly `propext, Classical.choice,
Quot.sound`; no `-- @refutes` tags (theorem instantiations, nothing
admitted consumed).

Verification: `lake env lean` on the landed module (zero errors, zero
warnings); explicit `lake build Scaffold.QA.SpectralGraph.Cheeger_QA`
✔; the axiom audit above; full `lake build` ✔ immediately followed by
`check_build_completeness.py` — 133 source files, 133 fresh
artifacts, 0 stale, 0 missing, exit 0; `lint_axioms` exit 0 (4
current axioms, unchanged; only the allowlisted-confirmed PF finding);
`check_refutation_independence` (9-tag clean — no tags touched);
`check_public_reachability` clean (63 repo modules); `check_citations`
clean; `check_markdown_links` clean; `check_backlog_freshness` clean;
scoreboard regenerated (4648/4/0) with the verification row;
map-freshness exit 0 after the 4535 → 4648 stats sync in both map
data files and SVG regeneration (49 stations, no status change — none
owed). Records: this proposal, `proposals/README.md` (new Delivered
row), README (4648 + the cuts-and-expansion row's regular-audit
clause), the radar (QA axis synced, held 4.5),
`index/map/spectral_graph.md` (the RegularFences section), the
backlog item-2 falsification note, both map data tables + regenerated
SVG, the execution plan, and the activity log. Nothing committed; the
prior runs' uncommitted deliveries preserved.

Technique findings (five):

1. **The companion-audit trap in pricing** (headline): a fence's
   fixture must keep every *co-hypothesis* of the dropped clause
   genuine, not merely the dropped clause failing — the initial
   `hdpos` pricing at signed negative-degree fixtures was invalid
   because `hnn` is a co-hypothesis of every `hdpos` clause here, and
   no signed fixture can serve. The satisfiable-corner analysis
   (nonnegative + genuinely regular forces `d ≥ 0`; `d = 0` forces
   the zero matrix) then converts four would-be fences into recorded
   corner-survives non-fenceables — the same discipline class as the
   prior audits' proof-shaped findings, now caught at pricing time.
2. `!![...]` matrix literals on `Fin 3` evaluate under plain
   `simp [name]` for symmetric/degree goals (the `icPathAdj` idiom
   works verbatim), but the `(0,2)`/`(2,0)` entries need `simp only
   [name] <;> rfl` — defeq evaluation closes what simp's eta-collapsed
   normal form (`Matrix.vecHead (Matrix.vecTail fun i => …)`) cannot.
3. **Operator literals before sums**: an `if i = j` inside a `∑ j`
   with `i` bound by an enclosing dotProduct cannot be simp-case-split
   — the working idiom is pinning `regularNormalizedLaplacian A d` /
   `laplacian A` as a `!![...]` literal first (where `fin_cases` can
   split the ext goals), after which every quadratic-form identity is
   `simp only [literal, cons lemmas]` + `ring`.
4. At `Fin 2`, `secondEval` is the top sorted entry, so the
   eigenvalue-witness bridge + `eigvalOf_le_evals_last` gives lower
   bounds by *defeq* index coercion (`⟨card − 1⟩` vs `⟨1⟩` — no index
   surgery needed, `exact hlast` accepts across the defeq since
   `le_refl 2` already proves `Fintype.card (Fin 2) ≡ 2`); upper
   bounds ride `evals_le_of_linearIndependent` at `k = 2` with the
   identity family, where the combination hypothesis collapses to the
   pointwise `∀ x, quadForm M x ≤ t · (x ⬝ᵥ x)`.
5. Numeral smul scalars default to `ℕ` in `M *ᵥ v = μ • v` statements
   (`0 • v` picks the `ℕ`-smul instance and then fails to unify with
   the ℝ-witness) — every smul scalar in an eigen-equation pin needs
   an explicit `(μ : ℝ)` ascription; and mixed simp/norm_num branches
   must be sequenced `all_goals simp […]` then `all_goals norm_num`
   (a trailing `<;> norm_num` warns as never-executed on the branches
   simp already closed).
