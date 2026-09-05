# Adversarial Fence Audit of the Band-Projector Family

**Status:** COMPLETE (delivered 2026-09-04, run `20260904T175635Z-run-1`, session `ses_f9274ad0fffe9WGfaQ7Wf2bO1d`)
**Method:** `governance/ADVERSARIAL_REVIEW.md` (twelfth application)
**Family:** `Scaffold/Mathlib/GraphTheory/Band.lean` + `ClusterProjector.lean`
and their pre-discipline QA (`Scaffold/QA/SpectralGraph/Band_QA.lean`,
2026-08-21; `Scaffold/QA/Perturbation/ClusterProjector_QA.lean`, 2026-08-24).

## Step-0: selection survey

The prior terminal handoff (sparsification core audit, 2026-09-04) named
"the remaining pre-discipline QA families outside the electrical cluster —
the `SpectralCertificates`/`Band`/`ClusterProjector` neighborhood and the
Poincaré family are the plausible candidates, and a fresh Step-0 consumption
survey should pick." Non-QA import-consumer counts:

| Candidate | direct non-QA consumers | transitive |
| --- | --- | --- |
| `Band` | `PolyFilter`, `ClusterProjector` (2) | + `BandDavisKahan` (3) |
| `ClusterProjector` | `BandDavisKahan` (1) | 1 |
| `SpectralCertificates` | 0 | 0 |
| `Poincare` | 0 | 0 |

The band-projector neighborhood wins: `Band` + `ClusterProjector` feed
`PolyFilter` and the set-form Davis–Kahan pair in
`Perturbation/BandDavisKahan.lean` — the ring-2 perturbation bridge. Both
QA files predate the adversarial-review discipline (first fence audits
landed 2026-09-02) and carry **no hypothesis-form fence sections** for the
shelf's own clause surface (the existing "guards" cover three clauses only,
catalogued below).

## Priced clause inventory

Fixtures: `diag13 = !![1,0;0,3]` on `Fin 2` (spectrum `{1,3}`, all pins
already delivered: `band_diag13_low/high/full/gap/four_zero/zero_four`,
`overlap_low/high`, `spectralProjector_diag13_one/zero`,
`eigvecOf_diag13_one/three/ne_zero`, endpoint-guard families `gap_hi`,
`part2`, `nonmono`); `clusterA = diag(0,5,11)` on `Fin 3` (pins
`cpA_zeroEleven = diag(1,0,1)`, `cpA_zeroFive = diag(1,1,0)`,
`spClusterA_eq : P_6 = diag(1,1,0)`, existence/injectivity lemmas).

### Band.lean — 22 priced fences

| # | Theorem | Clause | Refutation (all other clauses genuine) |
| --- | --- | --- | --- |
| B1 | `bandProjector_idempotent` | `hab : a ≤ b` | `B(4,0] = −1`: `(−1)² = 1 ≠ −1` |
| B2 | `bandProjector_mulVec_eigvecOf_self` | `h₂ : λ i ≤ b` | band `(−1,2]`, λ=3 mode: axis-1 eigenvector killed ≠ fixed (`h₁` genuine: `−1 < 3`) |
| B3 | `bandProjector_mulVec_eigvecOf_eq_zero_left` | `hab` | `a=4,b=0`, λ i ≤ 4 genuine: `B(4,0]*ᵥv = −v ≠ 0` |
| B4 | `bandProjector_mulVec_eigvecOf_eq_zero_right` | `hab` | `a=4,b=0`, `0 < λ` genuine: `−v ≠ 0` |
| B5 | `bandProjector_eq_spectralProjector_of_lt` | `h : ∀ i, a < λ i` | `a=1` (an eigenvalue), `b=4`: `B(1,4] = diag(0,1) ≠ 1 = P_4` |
| B6 | `bandProjector_eq_one` | `ha` | `a=1, b=4`, `hb` genuine: `diag(0,1) ≠ 1` |
| B7 | `bandProjector_eq_one` | `hb` | `a=−1, b=2`, `ha` genuine: `diag(1,0) ≠ 1` |
| B8 | `bandProjector_mul_bandProjector_eq_zero` | `hab` | `B(4,0]·B(1,3] = −diag(0,1) ≠ 0` (`hcd`,`hbc` genuine) |
| B9 | same | `hcd` | `B(−1,3]·B(4,1] = diag(0,−1) ≠ 0` |
| B10 | `…eq_zero'` (flipped) | `hab` | `B(1,3]·B(4,0] = diag(0,−1) ≠ 0` |
| B11 | flipped | `hcd` | `B(4,1]·B(−1,3] = diag(0,−1) ≠ 0` |
| B12 | flipped | `hbc` | `B(1,4]·B(−1,3] = diag(0,1) ≠ 0` |
| B13 | `bandProjector_inner_eq_zero` | `hab` | `x=y=![0,1]`: `(−y)⬝ᵥy = −1 ≠ 0` |
| B14 | same | `hcd` | `B(−1,3]=1`, `B(4,1]=diag(0,−1)`: dot `−1` |
| B15 | `eq_zero_of_bandProjector_mulVec_eq_self` | `hbc` | shared λ=3 mode `![0,1]` fixed by both `B(−1,3]=1` and `B(1,4]=diag(0,1)`, ≠ 0 |
| B16 | `…eq_zero_of_monotone` | `ht : Monotone` | `nonmono`: `B(4,0]·B(0,4] = −1 ≠ 0` at `k=0<m=1` |
| B17 | same | `hkm : k < m` | `k=m=0` on `part2`: `B(0,2]² = diag(1,0) ≠ 0` |
| B18 | `sum_range_bandProjector_mulVec_eq_self` | `hb` | `gap_hi` at `x=![1,0]`: sum `= ![0,0] ≠ x` |
| B19 | same | `hc` | `part2` truncated `n=1` at `x=![0,1]`: `![0,0] ≠ x` |
| B20 | `bandProjector_residual_dotProduct_eq_zero` | `hab` | `B(4,0]=−1`, `x=z=![1,0]`: residual `2x` against `−x`, dot `−2 ≠ 0` |
| B21 | `bandProjector_toEuclidean_apply_eq_orthogonalProjection` | `hab` | `B(4,0]=−1`: range is everything (surjective), projection `= x ≠ −x = RHS` |
| B22 | `norm_sub_bandProjector_apply_le` | `hab` | `hy` at `−1` forces `y=0`: claim reads `‖2x‖ ≤ ‖x‖`, false at `![1,0]` |

Screened (negative witness already in the repository): `self`'s `h₁`
(`band_diag13_high_not_fix_low_mode`); `eq_zero_left`'s `h`
(`band_diag13_high_fixes_high_mode` + `eigvecOf_diag13_ne_zero`);
`eq_zero_right`'s `h` (`band_diag13_low_fixes_low_mode` + ne_zero);
forward `eq_zero`'s `hbc` (`band_diag13_overlap_mul_ne_zero`, the delivered
overlap guard); `inner`'s `hbc` (`band_diag13_low_not_orthogonal_self`);
`sum_range_bandProjector_eq_one`'s `hb`/`hc` (the delivered endpoint
guards `gap_hi` / `part2`-truncated); `norm_sub_bandProjector_apply_le`'s
`hy` (`band_diag13_hilb_guard`).

Non-fenceable, mechanism recorded: every `hM` clause (signature-entangled:
`bandProjector M hM a b` consumes `hM` in the display, so the dropped
statement is not well-formed); `eq_zero_of_bandProjector_mulVec_eq_self`'s
`hab` and `hcd` — a negated band `B(a,b) = P_b − P_a` (`a > b`) has
spectrum in `{−1, 0}`, so `B *ᵥ w = w` already forces `w = 0` and the
dropped-guard statement is *provable* (truth-removable, the P4-class
finding of the electrical-flow audit).

### ClusterProjector.lean — 7 priced fences

| # | Theorem | Clause | Refutation |
| --- | --- | --- | --- |
| C1 | `clusterProjector_mulVec_eigvecOf_self` | `h : λ i ∈ S` | `S={0,11}` at `clusterA`, λ=5 index: killed ≠ fixed |
| C2 | `clusterProjector_mulVec_eigvecOf_eq_zero` | `h : λ i ∉ S` | same set, λ=0 index: fixed ≠ 0 |
| C3 | `clusterProjector_eq_zero_of_forall_not_mem` | `h` | `S={0,11}`: pinned `diag(1,0,1) ≠ 0` |
| C4 | `clusterProjector_eq_one_of_forall_mem` | `h` | `S={0,5}`: pinned `diag(1,1,0) ≠ 1` |
| C5 | `clusterProjector_mul_clusterProjector_eq_zero_of_disjoint` | `hST` | `S=T={0,11}`: `P² = P ≠ 0` |
| C6 | `clusterProjector_eq_of_forall_mem_iff` | `hiff` | `S={0,11}` vs `T=Ioc(−1,6)`: `diag(1,0,1) ≠ 1` |
| C7 | `clusterProjector_eq_bandProjector` | `hab : a ≤ b` | `a=6>b=−1`: `Ioc 6 (−1) = ∅` so cluster side `0`, band side `P_{−1} − P_6 = −diag(1,1,0) ≠ 0` (the docstring's own corner, both pins delivered) |

Companions: an eigenvector-ne-zero pin at `clusterA` (unit-norm route) and
the genuineness isolations (`h₁`/`hb`/etc. at the chosen fixtures), plus the
new band pins `B(1,3] = diag(0,1)` and `B(4,1] = diag(0,−1)` (each two
rewrites from delivered threshold pins).

## Execution plan

QA-only, zero axiom contact (count stays 4): pure insertions — a
`BandFences` section at the end of `Band_QA.lean`, a `ClusterFences`
section at the end of `ClusterProjector_QA.lean`. Spike first in
`wip/bpfences_spike.lean` to zero errors/zero warnings; land; verify per
the standard ladder (`lake env lean`, explicit builds, `#print axioms` audit
of every new declaration, full `lake build` +
`check_build_completeness.py`, `lint_axioms`,
`check_refutation_independence`, `check_public_reachability`,
`check_citations`, `check_markdown_links`, `check_backlog_freshness`,
scoreboard regen, map-freshness sync of both data tables + SVG, README,
radar, `index/map/spectral_graph.md`, backlog note, this proposal's
delivery record, execution plan, activity log).

## Delivery record (2026-09-04)

**Delivered at the full priced scope** — all 22 band fences (B1–B22)
and all 7 cluster fences (C1–C7) landed with isolation companions, as
a pure insertion in each QA file (`Band_QA.lean`'s `BandFences`
section, 35 declarations; `ClusterProjector_QA.lean`'s `ClusterFences`
section, 9 declarations; 44 total, 43 public). QA-only, zero axiom
contact: `#print axioms` via `wip/bpfences_axcheck.lean` on all 43
public declarations — every one exactly `propext, Classical.choice,
Quot.sound` (the private transport helper `bfF_toEuclideanLin_apply`
audited transitively through `bfF_hilbIdent_hab_fence`); no `-- @refutes`
tags (these refute *theorem* instantiations — nothing admitted is
consumed). QA 4931 → 4974 (+43 by the generator metric).

The two new band pins (`band_diag13_one_three = diag(0,1)`,
`band_diag13_four_one = diag(0,−1)`, each two rewrites from delivered
threshold pins) carry the disjointness-family fences; the numeric pin
`bfF_four_zero_mulVec` (`B(4,0] *ᵥ ![1,0] = −![1,0]`) is shared by the
Step-4 pair; `cfF_eigvec_ne_zero` (unit-norm route) is the cluster
action fences' companion. The Step-4 Hilbert fences reuse the QA
file's own private norm/transport helpers (the spike carried local
copies — module-private declarations are invisible across imports; the
documented restatement pattern).

**Technique findings:**

1. **Headline — per-branch `norm_num [h]` discharges.** Threshold
   hypotheses (`∀ i, λ i ≤ c`) over a pinned spectrum discharge in one
   tactic per rcases branch by handing the branch equation to
   `norm_num` as a rewrite — no `rw`, so no rw-directionality, no
   rw-closes-goal trap, no branch-count assumptions. Every
   `rw [h]; norm_num` variant failed one way or another: as
   `tac <;> rw [h]; norm_num` it misparses (`(tac <;> rw [h]); norm_num`
   — the norm_num drops off the second branch, leaving `3 ≤ 4`
   unsolved); as `tac <;> (rw [h]; norm_num)` it errors "no goals" on
   any branch where the rewrite itself closes the goal.
2. **simp's numeric-contradiction boundary is sign-asymmetric.**
   `simp at h` reduces matrix-literal entry equations fully but closes
   only the `0 = 1`/`1 = 0` forms (`zero_ne_one`); signed falsehoods
   (`1 = -1`, `-1 = 0` — every fence at the negated band) survive simp
   and need `linarith`. The defensive `all_goals linarith` closer
   fires the unreachable-tactic linter on the branches simp closed —
   zero-warning runs must pick the closer per the pinned entry's sign.
3. **The self-substitution rewrite trap has an `←`-direction twin.**
   `rw [← hfix] at hkill` with `hfix : P *ᵥ v = v` rewrites the `v`
   inside `hkill : P *ᵥ v = 0` *into* `P *ᵥ (P *ᵥ v) = 0` — the
   forward direction was wanted. A cousin of the Foster audit's
   recorded `rw [hg₂]` trap; the fix is checking which side of the
   equation the target term sits on before choosing `←`.
4. **Function-literal application can halt simp at composition goals.**
   Proving `!![0,0;0,1] *ᵥ ![0,1] = ![0,1]` by bare `simp` strands at
   `vecHead ∘ vecTail ∘ ![![0,0],![0,1]] = ![0,1]`; the robust route
   is explicit `funext k; fin_cases k <;> simp [full literal set]` —
   the recorded eta/Fin-literal trap class, now on the function side
   rather than the index side.
5. **WithLp injection refutes packaged-vector equalities by
   `congrArg`**: from `symm x = symm (−x)`, `congrArg (WithLp.equiv 2 _)
   hclaim` then `congrFun · 0` lands at `1 = -1` (the equiv∘symm
   cancellation is rfl/simp-level) — no `WithLp` API needed beyond the
   two transports already in the QA file.

**Verification:** spike first (`wip/bpfences_spike.lean` — the full
delivery iterated to zero errors/zero warnings before any shelf edit,
five fix rounds all in the recorded trap classes above); `lake env
lean` on both landed modules (zero errors, zero warnings); explicit
`lake build Scaffold.QA.SpectralGraph.Band_QA` and
`Scaffold.QA.Perturbation.ClusterProjector_QA` ✔; the 43-declaration
axiom audit above; full `lake build` ✔ immediately followed by
`check_build_completeness.py` — 133 source files, 133 fresh artifacts,
0 stale, 0 missing, exit 0; `lint_axioms` exit 0 (4 current axioms,
unchanged; only the allowlisted-confirmed PF finding);
`check_refutation_independence` (9-tag clean — no tags touched);
`check_public_reachability` clean (63 repo modules); `check_citations`
("All axioms have proper citations!"); `check_markdown_links` clean;
`check_backlog_freshness` clean; scoreboard regenerated (4974/4/0)
with the verification row; map-freshness exit 0 after the 4931 → 4974
stats sync in both map data files and SVG regeneration (49 stations,
no status change — none owed). The landings verified as pure
insertions in both Lean files (zero deletions in numstat, modulo the
Purpose-block sentence each). Records updated: this proposal,
`proposals/README.md` (new Delivered row), README (4974 + the cluster
projector row's audit clause), the radar (QA axis synced, held 4.5),
`index/map/spectral_graph.md` (the fences paragraphs in the Band and
ClusterProjector sections), the backlog item-2 falsification-surface
note, the scoreboard verification row, both map data tables +
regenerated SVG, the execution plan, and the activity log. Nothing
committed; the prior runs' uncommitted deliveries preserved.
