# Adversarial Fence Audit of the Davis–Kahan Core Perturbation Family

**Status:** COMPLETE (delivered 2026-09-04, run `20260904T192751Z-run-1`;
20 of 22 priced fences closed, 2 deferrals with recorded mechanisms —
see the delivery record)
**Method:** `governance/ADVERSARIAL_REVIEW.md` (thirteenth application)
**Family:** the Davis–Kahan retirement chain's load-bearing surface —
`Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/DavisKahan.lean`
(the sin-Θ theorem), `Weyl.lean` (the additive window pair, the norm
inequality, the gap-stability corollary), `Duhamel.lean`'s four
Davis–Kahan-proof theorems (the Duhamel bound, the no-tie rank pin, the
trivial endpoint, the sorted-step lemma), and `ProjectionGap.lean`'s two
equal-rank headline identities — plus their pre-discipline QA
(`Scaffold/QA/Perturbation/DavisKahan_QA.lean`, 2026-08-21;
`Weyl_QA.lean`, 2026-08-19; `ProjectionGap_QA.lean`, 2026-08-21).

## Step-0: selection survey

The prior terminal handoff (band-projector audit, 2026-09-04) named the
remaining pre-discipline QA families — "`Poincare_QA` (0 non-QA
consumers, 663 lines), `SpectralCertificates_QA` (0, 498 lines), and the
shelf-clause surfaces of the Davis–Kahan QA files themselves — with a
fresh Step-0 consumption survey to pick." Transitive non-QA
import-consumer counts (reverse import-graph walk over every non-QA
module in the repository):

| Candidate shelf | transitive non-QA consumers |
| --- | --- |
| `Perturbation/ProjectionGap` | 7 — `BandDavisKahan`, `Duhamel`, `DavisKahan`, `Fiedler`, `Poincare`, `ProjectorDrift`, `EdgePerturbationDrift` |
| `Perturbation/Weyl` | 6 — `DavisKahan`, `Fiedler`, `Poincare`, `ProjectorDrift`, `EdgePerturbationDrift`, `EdgePerturbationTail` |
| `Perturbation/Duhamel` | 6 — same six minus `EdgePerturbationTail` |
| `Perturbation/DavisKahan` | 4 — `Fiedler`, `Poincare`, `ProjectorDrift`, `EdgePerturbationDrift` |
| `Perturbation/BandDavisKahan` | 0 (QA-only consumers: its five QA files) |
| `GraphTheory/Poincare` | 0 |
| `GraphTheory/SpectralCertificates` | 0 |

The Davis–Kahan core chain wins decisively: its four shelves are the
four most-consumed unaudited surfaces in the library, feeding both
derived-layer projector-stability capstones (`ProjectorDrift`,
`EdgePerturbationDrift`) and the ring-1 Fiedler/Poincaré programs. The
`BandDavisKahan` shelf (the band layer proper) ranks at 0 by this
metric and already carries four delivery-scoped fences across its QA
family; it stays a separate future audit. All three QA files in the
picked family predate the adversarial-review discipline (first fence
audits landed 2026-09-02) and carry **zero hypothesis-form fence
sections** — the rotation fixture (`DavisKahan_QA`) instantiates only
positive consequences.

## Priced clause inventory

Fixtures: the delivered rotation fixture (`dkA = diag(0,2)`,
`dkE = [[0,3/4],[3/4,0]]`, with every needed pin already proved:
`dkA_evals_pin` [0,2], `dkE_norm` 3/4, `dkAE_evals_pin` [−1/4, 9/4],
`dkA_projector_pin` diag(1,0), `dkAE_projector_pin`
(1/10)·!![9,−3;−3,1], `davis_kahan_rotation_strict_QA` ‖Q−P‖ = √(1/10));
the delivered `Weyl_QA` two-point machinery (`two_point_pin_of_sum_prod`);
the delivered `ProjectionGap_QA` rotation pair (`pDiag`, `qRot`, with
`pDiag_rank`, `qRot_rank`, `diff_opNorm_QA` 3/5, `resid_opNorm_indep_QA`
3/5); and new trivial fixtures (diag perturbations, asymmetric
idempotents) priced below. Norm lower bounds all route through the
witness-vector lemma `dotProduct_mulVec_norm2_le_l2OpNorm_sq`; rank pins
route through `Matrix.rank_diagonal` (diag fixtures) and the
`qRot_rank` range-span pattern (asymmetric fixtures).

### DavisKahan.lean — 2 priced fences + 3 non-fenceables

| # | Theorem | Clause | Refutation (all other clauses genuine) |
| --- | --- | --- | --- |
| D1 | `davis_kahan_sin_theta` | `hδ : 0 < δ` | rotation fixture, `δ = −1/2`: `hsep` genuine (−1/2 ≤ 9/4 − 0); conclusion `‖Q−P‖ = √(1/10) ≤ (3/4)/(−1/2) = −3/2` — a nonneg norm below a negative bound |
| D2 | `davis_kahan_sin_theta` | `hsep` | rotation fixture, `δ = 100`: `hδ` genuine; conclusion `√(1/10) ≤ 3/400`, false by `nlinarith` on the pinned norm |

Non-fenceable, mechanism recorded: `hA`/`hAE` (signature-entangled —
`initialProjector A hA k` consumes the symmetry proofs in the display,
so the dropped statement is not well-formed) and `hk` (entangled through
`hsep`'s own Fin index `⟨(k:ℕ)+1, hk⟩`).

### Weyl.lean — 2 priced fences + a distinct entanglement record

| # | Theorem | Clause | Refutation |
| --- | --- | --- | --- |
| W1 | `spectral_gap_stability` | `hnorm : ‖E‖ ≤ ε` | `A = diag(0,2)`, `E = diag(0,−1)` (gap 2 → gap(A+E) = 1, `‖E‖ = 1`), `γ = 2` genuine, `ε = 1/4`: conclusion `1 ≥ 2 − 1/2 = 3/2` false |
| W2 | `spectral_gap_stability` | `hγ : spectralGap A ≥ γ` | `E = 0`, `γ = 100`, `ε = 1` genuine: conclusion `gap(A) = 2 ≥ 98` false |

Non-fenceable, mechanism recorded: `weyl_additive_upper`/`_lower`'s
`hcard : 1 ≤ Fintype.card V` is consumed **inside the conclusion's own
elaboration** — the Fin index `⟨Fintype.card V − 1, by omega⟩` closes
its proof term using `hcard` from the statement's local context, so the
dropped-`hcard` statement does not elaborate (a distinct subclass of
the signature-entanglement mechanism: proof-term-in-display). The
`hA`/`hE` clauses of all four Weyl theorems are signature-entangled the
usual way (`evals (hA.add hE)` consumes the proofs); `hk` likewise
through `spectralGap`'s display.

### Duhamel.lean — 8 priced fences

| # | Theorem | Clause | Refutation |
| --- | --- | --- | --- |
| H1 | `l2OpNorm_one_sub_spectralProjector_mul_spectralProjector_le` | `hab : a < b` | rotation fixture, `a = 1`, `b = 0`, `c' = 0` (`hcl` genuine: the only `>0` eigval of `dkA+dkE` is `9/4 ≥ 0`): conclusion `‖(1−Q)P‖ ≤ (3/4)/(0−1) = −3/4` vs norm ≥ 0 |
| H2 | same | `hcl : ∀ i, c' < λ' i → b ≤ λ' i` | rotation fixture, `a = 0` (P = the pinned diag(1,0)), `c' = 1` (new pin: Q at threshold 1 = the same (1/10)·!![9,−3;−3,1]), `b = 100` (`hab` genuine): `(1−Q)P *ᵥ e₀ = ![1/10, 3/10]` gives `‖(1−Q)P‖² ≥ 1/10 > (3/400)² = ‖dkE‖²/(b−a)²` |
| H3 | `rank_spectralProjector_evals_of_lt` | `h : evals k < evals (k+1)` (no tie) | zero matrix on `Fin 2` (tie: both evals 0): `spectralProjector 0 hM 0 = 1` by `spectralProjector_eq_one` (every eigvalOf = 0), rank `2 ≠ 1 = k+1` |
| H4 | `l2OpNorm_sub_le_one_of_isSymm_idempotent` | `hP : P.IsSymm` | `P = !![1,2;0,0]]` (asymmetric, idempotent), `Q = 0` genuine: `P *ᵥ ![1,2] = ![5,0]` gives `‖P‖² ≥ 5 > 1` |
| H5 | same | `hPP : P * P = P` | `P = diag(2,0)` (symmetric, non-idempotent), `Q = 0`: witness `e₀` gives `‖P‖² ≥ 4 > 1` |
| H6 | same | `hQ` | mirror of H4 (`Q = !![1,2;0,0]]`, `P = 0`) |
| H7 | same | `hQQ` | mirror of H5 (`Q = diag(2,0)`, `P = 0`) |
| H8 | `evals_succ_le_of_lt` | `h : evals k < eigvalOf i` | `dkA`, `k = 0`: some index has `eigvalOf = 0` (membership in the pinned eigenvalue multiset), so the conclusion reads `2 ≤ 0` |

Non-fenceable: H1/H2's `hA`/`hAE` (projector displays), H3's `hM`/`hk`,
H8's `hM`/`hk` (index displays) — the signature-entanglement class.

### ProjectionGap.lean — 10 priced fences

The two headline identities have **signature-free** clause surfaces
(`P`, `Q` arbitrary matrices; no display consumes a proof) — the most
fenceable class in the library. `sub_eq` is
`l2OpNorm_sub_eq_of_rank_eq : ‖P − Q‖ = ‖(1−Q)·P‖`; `core` is
`l2OpNorm_one_sub_mul_eq_of_rank_eq : ‖(1−Q)·P‖ = ‖(1−P)·Q‖`.

| # | Theorem | Clause | Refutation (kept clauses genuine) |
| --- | --- | --- | --- |
| P1 | `sub_eq` | `hP` | `P = !![1,1;0,0]]` (asymm. idempotent, rank 1), `Q = pDiag`: `‖P−Q‖ ≥ 1` (witness `e₀`/`e₁`) vs `‖(1−Q)P‖ = ‖0‖ = 0` |
| P2 | `sub_eq` | `hPP` | `P = diag(2,0)`, `Q = pDiag`: `‖P−Q‖ = ‖diag(1,0)‖ ≥ 1` vs `(1−pDiag)·diag(2,0) = 0` |
| P3 | `sub_eq` | `hQ` | `Q = !![1,1;0,0]]`, `P = pDiag`: `‖P−Q‖ ≥ 1` (witness `e₀`/`e₁`, entry −1) vs `(1−Q)P = 0` |
| P4 | `sub_eq` | `hQQ` | `Q = diag(0,2)` (symm. non-idempotent, rank 1), `P = pDiag`: `‖P−Q‖ ≥ 2` (witness `e₁`) vs `‖(1−Q)P‖ = ‖diag(1,0)‖ = 1` — both sides nonzero but unequal |
| P5 | `sub_eq` | `hrank` | `P = 0`, `Q = qRot` (both genuine orthogonal projectors, ranks 0 ≠ 1): `‖0−qRot‖ ≥ 1` (witness `u = (4/5,3/5)`, `qRot *ᵥ u = u`) vs `‖(1−qRot)·0‖ = 0` |
| P6 | `core` | `hP` | `P = !![1,1;0,0]]`, `Q = qRot`: `‖(1−Q)P‖ = 0` (as P1) vs `‖(1−P)Q‖ > 0` (witness: a nonzero column of `(1−P)qRot`) |
| P7 | `core` | `hPP` | `P = diag(2,0)`, `Q = pDiag`: `‖(1−Q)P‖ = 0` vs `‖(1−P)Q‖ = ‖diag(−1,0)‖ ≥ 1` |
| P8 | `core` | `hQ` | `Q = diag(2,0)`, `P = pDiag`: `‖(1−Q)P‖ = ‖diag(−1,0)‖ ≥ 1` vs `‖(1−P)Q‖ = ‖diag(0,1)·diag(2,0)‖ = 0` |
| P9 | `core` | `hQQ` | `Q = diag(0,2)`, `P = pDiag`: `‖(1−Q)P‖ = 1` vs `‖(1−P)Q‖ = ‖diag(0,2)‖ ≥ 2` |
| P10 | `core` | `hrank` | `P = 0`, `Q = qRot`: `‖(1−Q)·0‖ = 0` vs `‖(1−0)qRot‖ = ‖qRot‖ ≥ 1` (the P5 witness) |

Companions: rank pins for the new fixtures (`Matrix.rank_diagonal` for
the diag ones; the `qRot_rank` range-span pattern for `!![1,1;0,0]]`),
idempotence/symmetry pins for the kept clauses, and the witness-vector
norm pins. Isolation companions packaged per fixture (several fences
share one fixture's genuineness set, mirroring the lazy follow-on
delivery's packaged isolation).

## Plan

QA-only, zero axiom contact (count stays 4; every fence is a theorem
instantiation — nothing admitted is consumed, so no `-- @refutes` tags).
Spike first in `wip/dkfences_spike.lean` to zero errors/zero warnings,
then land as pure insertions: a new `AdversarialFences` section in each
of `DavisKahan_QA.lean` (D1–D2, H1–H8), `Weyl_QA.lean` (W1–W2), and
`ProjectionGap_QA.lean` (P1–P10). Full verification ladder after the
landing, `#print axioms` audit on every new declaration via a generated
`wip/` file.

## Delivery record (2026-09-04)

DELIVERED at 20 of the 22 priced fences, with the two deferrals
recorded below as priced follow-ons precise enough to reopen
deliberately. QA-only, pure hard crust: QA 4974 → 5045 (+71 by the
generator metric; 79 declarations — 77 public = 71 theorems + 6 fixture
`def`s, plus 2 private helpers audited transitively), zero axiom contact
(`#print axioms` via `wip/dkfences_axcheck.lean` on all 77 public
declarations — every one exactly `propext, Classical.choice,
Quot.sound`; no `-- @refutes` tags — theorem instantiations, nothing
admitted consumed). Landed as pure insertions: the fence sections of
`DavisKahan_QA.lean` (+481), `Weyl_QA.lean` (+256), and
`ProjectionGap_QA.lean` (+378, plus one import line — it consumes the
H4–H7 layer's `dkfDiag2` fixture, imported rather than duplicated
because same-namespace QA files cannot re-declare shared names).

The landed content, by section. **D (the sin-Θ bound):** `hδ` refuted at
the negative-`δ` corner (separation genuine at `−1/2`, the bound's right
side `−3/2` below every norm) and `hsep` at the inflated `δ = 100` (the
delivered exact distance `√(1/10)` against `‖dkE‖/100 = 3/400`). **W
(gap stability):** `hnorm` at the gap-shrinking `diag(0,−1)` (gap
`2 → 1` at norm `1`; the dropped statement at `ε = 1/4` demands
`1 ≥ 3/2`) and `hγ` at the inflated `γ = 100` with `E = 0`. **H (the
Duhamel quartet):** `hab` at the negative-denominator corner with `hcl`
genuinely trivial (`b = 0`, `c' = 0`); `hcl` at the inflated window
`b = 100` through the new threshold-`1` projector pin
(`dkAE_filter_one_eq_low` + `dkAE_projector_one_pin`: the window
`(−∞,1]` captures exactly the `−1/4` eigenspace, so `Q` at `1` *is* the
delivered pin's matrix — the fence needed no new eigenvector analysis),
with the witness `(1−Q)P *ᵥ e₀ = ![1/10, 3/10]` squaring the left side
at `≥ 1/10 > (3/400)²`; the rank pin's no-tie clause at the zero matrix
(`spectralProjector_eq_one` + `Matrix.rank_one`: `rank 2 ≠ 1`); the
trivial endpoint's four clauses at the asymmetric idempotent
`!![1,2;0,0]]` (`‖P‖² ≥ 5`) and the symmetric non-idempotent
`diag(2,0)` (`‖P‖² ≥ 4`); and the sorted-step clause at `dkA`'s pinned
bottom eigenvalue (`2 ≤ 0`). **P (the equal-rank identities):** eight
fences at the asymmetric idempotent `!![1,1;0,0]]` (its rank pin via the
`qRot_rank` range-span pattern), `diag(2,0)`, `diag(0,2)`, and the zero
matrix against the delivered `qRot` — every refutation through
witness-vector norm bounds (`dotProduct_mulVec_norm2_le_l2OpNorm_sq`)
or an exact projector-norm sandwich
(`l2OpNorm_le_one_of_isSymm_idempotent` above, witness below — the P4
route that avoided evals pins entirely).

**The two deferrals (the core identity's `hP`/`hQ`), mechanism
recorded:** an idempotent `P` with `rank P = rank Q` (against an
orthogonal projector `Q`) whose residual `(1−Q)P` vanishes must have
`range P ⊆ range Q`, hence (equal finite ranks) `range P = range Q`,
and then `P` acts as the identity on `range Q`, forcing `(1−P)Q = 0`
as well — both residuals vanish together. Both computed rank-1 oblique
cases (`P = [[1,1],[0,0]]` against `pDiag` and against `qRot`-rotated
axes) came out with *equal* norms (`0 = 0` and `3√2/5 = 3√2/5`),
suggesting the dropped-`hP`/`hQ` statements of the core may be provable
from the kept clauses (the P4 truth-removable class). A genuine
refutation, if one exists, needs unequal ranks-are-equal oblique
geometry beyond rank 1; reopening is deliberate work, not a routine
pass. The other ten clauses of the two identities are fenced.

**Non-fenceables recorded with mechanisms:** the signature-entangled
`hA`/`hAE`/`hM`/`hk` clauses throughout the family (projector/evals
displays consume the proofs — the established class); and — a distinct
subclass first isolated by this audit — the Weyl additive pair's
`hcard : 1 ≤ Fintype.card V`, consumed by the *conclusion's own proof
term* (`⟨Fintype.card V − 1, by omega⟩` elaborates against `hcard` from
the statement's local context), so the dropped statement does not
elaborate at all: proof-term-in-display entanglement, strictly stronger
than the usual signature entanglement (the hypothesis is consumed by
elaboration, not merely mentioned in it).

**Technique findings** (for the next audit's trap list):

1. **`norm_num at hcon` drifts `Fin`-literal displays** — it normalizes
   `⟨0, by simp⟩` to `0` inside the hypothesis, breaking any later
   term-level match against the original expression. The robust route:
   `have h0 := le_trans (norm_nonneg _) hcon` (unifying by elaboration)
   and numeric work on separate closed goals.
2. **A term-mode type mismatch can surface as a whnf *timeout* anchored
   at the theorem's statement line** — `le_antisymm (by linarith) hge`
   with `hge` about the wrong atom produced a 200k-heartbeat elaboration
   failure reported at the `theorem` header, sending the search in the
   wrong direction. When a statement-line timeout has no
   statement-level cause, audit the term-mode `by` blocks first.
3. **`lake env lean` resolves imports from existing oleans** — after
   landing QA file B importing newly-landed QA file A, B's check sees
   A's *old* olean until `lake build A` runs (the failure reads
   `unknown constant`, not `stale import`). Build changed QA
   dependencies before env-leaning their consumers.
4. **Same-namespace QA files cannot duplicate fixture names** — all
   three landing files share
   `…Perturbation.QA`, so a fixture used by two files must land once
   and travel by import (`ProjectionGap_QA` now imports
   `DavisKahan_QA` for `dkfDiag2`), not be redeclared.
5. **Anonymous constructors with nested multi-tactic `by` blocks break
   in term position** (`⟨i, by rw [h]; norm_num, fun hle => by …⟩`) —
   restructure to `exact (hcon' ⟨…⟩).elim` or `refine` with goal
   positions.
6. **The `Multiset.mem_map` eigenvalue-index extraction fails dependent
   elimination** through the `Finset.univ.val` coercion
   (`equivOfCardEq` is not reducible) — the robust existence argument
   for "some index carries the top eigenvalue" is the *trace* route:
   if all indices carried the bottom value, the pinned trace would be
   wrong (`simp only [hall] at hsum` rewrites inside the `∑` body
   faithfully).
7. **Zero-warning landings need per-site tactic trimming** — the
   `simp […] <;> norm_num` idiom warns (`unusedTactic`) wherever simp
   closes everything, so each site is trimmed individually (the spike
   iterates these away; the landing keeps the trimmed forms).

**Verification:** spike first (`wip/dkfences_spike.lean` — the full
delivery, iterated to zero errors/zero warnings before any shelf edit,
seven fix rounds all in the recorded trap classes); `lake env lean` on
all three landed modules (zero errors, zero warnings each); explicit
`lake build` on all three QA targets ✔; the 77-public-declaration axiom
audit above (both private helpers audited transitively); **full
`lake build` ✔ immediately followed by `check_build_completeness.py` —
133 source files, 133 fresh artifacts, 0 stale, 0 missing, exit 0**
(the build's only warnings are the pinned Mathlib package's own upstream
doc-string linter notes, present before this delivery);
`lint_axioms` exit 0 (4 current axioms, unchanged);
`check_refutation_independence` (9-tag clean — no tags touched);
`check_public_reachability` clean (63 repo modules); `check_citations`
("All axioms have proper citations!"); `check_markdown_links` clean;
`check_backlog_freshness` clean; scoreboard regenerated (**5045/4/0**)
with the verification row; map-freshness exit 0 after the 4974 → 5045
stats sync in both map data files and SVG regeneration (49 stations, no
status change — none owed). The landings verified as pure insertions
(481/0, 256/0, 378/0 in numstat plus one import line). Records
updated: this proposal, `proposals/README.md` (new Delivered row),
README (5045 + the perturbation row's audit clause), the radar (QA axis
synced, held 4.5), `index/map/perturbation.md` (audit paragraphs in the
four affected sections), the backlog item-2 falsification-surface note,
the scoreboard verification row, both map data tables + regenerated
SVG, the execution plan, and the activity log. Nothing committed; the
prior runs' uncommitted deliveries preserved.
