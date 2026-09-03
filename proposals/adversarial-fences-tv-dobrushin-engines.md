# Adversarial Fence Completion for the TV/Dobrushin Engine Family

**Status:** COMPLETE — delivered 2026-09-02 (same-run proposal; run
`20260902T212609Z-run-1`, session `ses_f9bffd049ffeZuJLtzRCQXynTv`).

**Goal.** The standing handoff's top unstarted frontier, executed as a
bounded audit: an adversarial re-read of the 2026-09-02 directed
TV/Dobrushin engine family's QA, closing every hole it finds with the
repository's hypothesis-form negative-witness fences.

## Why this and why now

- **The named frontier.** Two consecutive run handoffs named the
  audit-shaped pass over mixing-cascade QA surfaces the deliveries
  never adversarially re-read as the top unstarted item. The
  2026-09-02 directed-rate deliveries (`doeblintv-tv-contraction-pagerank-rate`,
  `directed-mixing-time-object`, `directed-uniform-mixing-time`) landed
  three QA sections in days, each self-certified by its own delivering
  run — exactly the configuration `docs/1_STRATEGY.md`'s
  load-bearing-growth section warns about: nothing independent has
  tried to knock the blocks over since.
- **The audit method** (`governance/ADVERSARIAL_REVIEW.md`: "for a
  theorem with several hypotheses, reviewers should also ask whether
  each one is actually necessary, not just used by the proof as
  written"): for every hypothesis of every shelf lemma in the family,
  either produce a fixture where exactly that hypothesis fails and the
  conclusion is refuted at pinned values (a *fence*), or record why no
  fence is possible. Cross-checked against every existing fence so
  nothing is duplicated.
- **The substrate's leverage.** `Mixing.lean`'s Dobrushin-coefficient
  section is the mixing program's newest *reusable* engine — consumed
  by the directed uniform object, priced for the undirected
  `walkTVPair` join. A silent statement-shape regression here (a
  dropped mass clause, a weakened row-sum clause) would propagate into
  every future consumer. The fences are the cheapest permanent tripwire.

## Audit findings

The family: `Mixing.lean`'s zero-sum interval pinning
(`abs_dotProduct_le_half_entryRange_mul_sum_abs`), row-action TV
non-expansiveness (`tvDistance_vecMul_le`), the Doeblin TV contraction
(`tvDistance_vecMul_le_of_pos_entries`, with the iterated and
positive-power assembly forms), the promoted pairing core
(`abs_sum_mul_le_of_pairwise`), the Dobrushin coefficient
(`tvDobrushinCoeff` with the sharp contraction
`tvDistance_vecMul_le_tvDobrushinCoeff`), and generic power
submultiplicativity (`tvDobrushinCoeff_pow_add_le`).

Hypothesis-necessity verdicts (each fixture hand-verified before any
Lean was written):

| Lemma | Hypothesis | Verdict | Refuting fixture (all other hypotheses hold) |
| --- | --- | --- | --- |
| `abs_dotProduct_le_half_entryRange_mul_sum_abs` | `hwsum : ∑ w i = 0` | **load-bearing, unfenced** | `w = e₀`, `h = (1, 0)`: `LHS = 1 > (1/2)·1·1 = RHS` |
| `abs_sum_mul_le_of_pairwise` | `hc : ∑ c z = 0` | **load-bearing, unfenced** | `c = e₀`, `g = (1, 0)`, `D = 1`: `LHS = 1 > 1/2` |
| `tvDistance_vecMul_le` | `hrow` (row sums `1`) | **load-bearing, unfenced** | `M = 2·I`, `μ = e₀`, `ν = e₁`: `TV = 2 > TV₀ = 1` |
| `tvDistance_vecMul_le` | `hnn` (entries `≥ 0`) | **load-bearing, unfenced** | `M = !![2, −1; −1, 2]` (row sums `1`), `μ = e₀`, `ν = e₁`: `TV = 3 > 1` |
| `tvDistance_vecMul_le_of_pos_entries` | `hsum` (equal mass) | **load-bearing, unfenced** | `Qh` = all-half matrix, `δ = 1/2`, `μ = 2•e₀`, `ν = e₀`: `LHS = 1/2 > (1 − 2·(1/2))·(1/2) = 0` |
| `tvDistance_vecMul_le_tvDobrushinCoeff` | `hmass` (equal mass) | **load-bearing, unfenced** | same `Qh` (identical rows ⟹ `δ(Qh) = 0` exactly): `LHS = 1/2 > (1/2)·0 = 0` |
| `tvDobrushinCoeff_pow_add_le` | `hrow` (row sums `1`) | **load-bearing, unfenced** | `Qx = !![1, 1; 1, −1]` (row sums `2, 0`), `s = t = 1`: `δ(Qx²) = δ(2I) = 2 > δ(Qx)² = TV((1,1),(1,−1))² = 1` |

Already fenced (verified, no duplication): the entries-floor clause of
the Doeblin contraction (`P2_tv_no_floor_refuted_QA` +
`P2_quarter_le_refuted_QA`), the `δ` hypothesis of the range engine
(`Qd_wrong_delta_refuted_QA`), the witness clause of the uniform
object's per-start domination, and the `ε = 0` junk corners of the
mixing-time objects. The equal-mass clause of the *generic* ℓ²→TV
conversion has its own fence (`tv_conversion_mass_guard_refuted_QA` in
`Mixing_QA.lean`) — the idiom this delivery extends to the contraction
family; the mass clauses audited here are *different clauses of
different lemmas* delivered later.

Not fenced and not fenceable (recorded, no action): `0 < δ` in the
Doeblin contraction is a strength hypothesis, not a truth hypothesis —
at `δ ≤ 0` the statement remains true (the coefficient
`1 − |V|δ ≥ 1` and the conclusion follows from non-expansiveness), so
no refutation exists. The `[Nonempty V]` instance-arguments are
structural (the `sup'`-based coefficient and the pairing minimum need
it); the degenerate-cardinality audit shape (`mass_one_unsat_card_zero_QA`)
does not apply because no mass-one clause appears in the family's
hypotheses.

## Statement shapes (recorded before stating)

- Each fence is the **negation of the conclusion at a specific
  instantiation** of the lemma (the repo's `P2_tv_no_floor_refuted_QA`
  shape), with both sides computed to numerals — so a wrong constant or
  a dropped clause in a future restatement of the shelf lemma is
  caught by the fence no longer being about a true-able statement.
- Each fence is paired with an **isolation companion** (the
  `P2_fence_isolation` shape): every *other* hypothesis of the lemma
  verified to hold at the fixture, and the dropped one verified to
  fail — proving the hypothesis is exactly what the refutation
  isolates, not an artifact of a degenerate fixture.
- Fixtures are new (`Qh`, `Mx`, `Mn`, `Qx`) because the existing ones
  cannot kill these clauses: `Qd` and `Gd` are strictly positive with
  distinct rows (their contractions are the *attainment* pins), and
  `P2` kills the floor clause but is a genuine permutation (row sums
  `1`, mass-compatible — the mass-dropped conclusion still holds
  there, which is precisely why the delivered fence could not double
  as a mass fence).

## Verification plan

Spike in `wip/fences_spike.lean` (zero errors/zero warnings before any
shelf edit); land as `DirectedMixing_QA.lean`'s Section I; `lake env
lean` on the touched module; explicit `lake build` target; `#print
axioms` audit on every new declaration (expected: exactly
`propext, Classical.choice, Quot.sound`); full `lake build` +
`check_build_completeness.py`; the full records ladder
(`lint_axioms`, `check_refutation_independence`, tags untouched —
these fence theorems, being refutations of *theorem* instantiations,
consume nothing they refute and touch no axiom;
`check_public_reachability`, `check_citations`,
`check_markdown_links`, `check_backlog_freshness`, scoreboard
regeneration, map stats sync in both data tables + SVG regeneration +
`check_scaffold_map_freshness`).

## Delivery record

Delivered as `Scaffold/QA/SpectralGraph/DirectedMixing_QA.lean`'s
Section I (+49 QA theorems, 3768 → 3817 by the generator metric; the
module 131 → 180). Five new fixtures (`Qh`, `Mx`, `Mn`, `Qx`, `twoE0`)
with raw value pins, the `tv_lit` two-point TV computation interface,
the three fixtures' Dobrushin coefficients pinned exactly
(`δ(Qh) = 0` by identical rows — the refutation engine; `δ(Mx) = 2`,
`δ(Qx) = 1`), the seven fences, and the five isolation companions.
Zero axiom contact: `#print axioms` via `wip/fences_axcheck.lean` on
all 62 audited declarations — every one exactly `propext,
Classical.choice, Quot.sound`. No `-- @refutes` tags added (these
refute *theorem* instantiations; nothing admitted is consumed, and
`check_refutation_independence` stays at its 9-tag clean state).

**Technique findings** (recorded for future QA runs):

1. `Finset.sup'_le`'s argument order in the pinned Mathlib does not
   match the apparent signature reading — the reliably working call
   shape is exactly the QA's own: the `Nonempty` witness first, then
   `(f := fun p => …)` *named*, then the bound function. Passing
   `Finset.univ_nonempty` positionally where `s` is expected produces
   a confusing metavariable type error (the lambda elaborated against
   a *type* argument).
2. `rintro ⟨a, b⟩` on a `Fin 2 × Fin 2` goal followed by `fin_cases`
   leaves `((⟨0, ⋯⟩, ⟨1, ⋯⟩)).1` projections unreduced — `rw` then
   cannot find `Mx 0`. The working idiom: `simp only []` (reduces the
   projections) then `rcases (show a = 0 ∨ a = 1 by omega) with h | h
   <;> rw [h]` (rewriting the *variable*, so no projection ever
   appears) — the shape `PRU_pair_tv_le_QA` already used.
3. `norm_num` **does** evaluate `|·|` of numerals in `tv_lit`-shaped
   goals: `rw [tv_lit]; norm_num` closes
   `(|2 − 0| + |0 − 2|)/2 = 2` and `(|1 − 1/2| + |1 − 1/2|)/2 = 1/2`.
   This refines the 2026-09-02 Doeblin-TV record's note ("norm_num
   does not evaluate |·| of numerals"): the distinction is the
   argument's shape — abs applied to a *subtraction of numerals*
   normalizes fine; the recorded failure was abs of a bare cast.
   The explicit `abs_of_nonneg`/`abs_neg` idiom remains the fallback.
4. Turning an equality value into the lower bound of a `sup'` maximum
   needs the symmetric direction: `tv_Mx_01.symm.le.trans hle`
   (`2 ≤ TV ≤ coeff`), not `tv_Mx_01.le.trans hle` — `Eq.le` orients
   `a = b` as `a ≤ b`, and the mistake type-errors one step later
   than expected.
5. A final `rw [entryRange, hs, hi]` on `1 - 0 = 1` does not close by
   the rewrite's trailing `rfl` (numeral subtraction is not
   `rfl`-transparent) — append `; norm_num`.

**Verification** (all commands run this delivery, before recording):
spike first (`wip/fences_spike.lean`, iterated to zero errors/zero
warnings before any shelf edit); `lake env lean` zero errors/zero
warnings on the touched QA module; explicit `lake build
Scaffold.QA.SpectralGraph.DirectedMixing_QA` ✔; the 62-declaration
axiom audit above; full `lake build` ✔ immediately followed by
`check_build_completeness.py` (133 source files, 133 fresh artifacts,
0 stale, 0 missing, exit 0); `lint_axioms` exit 0 (4 current axioms,
unchanged); `check_refutation_independence` (9-tag clean);
`check_public_reachability` clean (63 repo modules); `check_citations`
("All axioms have proper citations!"); `check_markdown_links` clean;
`check_backlog_freshness` clean (0 days); scoreboard regenerated
(**3817/4/0**); map stats synced 3768 → 3817 in both data tables, SVG
regenerated, `check_scaffold_map_freshness` exit 0 (45 stations, no
station's proposal status changed — this proposal has no station).

Records updated: this proposal, `proposals/README.md` (new Delivered
row), README (3817 + the walks-and-mixing row's fence-completion
clause), the radar (QA axis synced 3768 → 3817, score held 4.5 per
protocol — negative witnesses of an already-counted family, not a
named-gap closure), `index/map/spectral_graph.md` (the Section-I
paragraph + the QA-module count de-staled 132 → 180), the backlog
item-8 fifteenth update, the scoreboard verification row, both map
data tables + regenerated SVG, the execution plan, and the activity
log. Nothing committed.

**Remaining risk:** none owed by the delivery — QA-only, no axiom
disposition changed, no public statement changed. Honest scope: the
audit covered the TV/Dobrushin family's *hypothesis clauses*; the
broader audit-shaped pass over other mixing-cascade surfaces (the
lazy, entropy, Poisson-bridge, and primitivity-supplier families' QA)
remains open — this delivery closes exactly the one family it audited
and records the method for the rest. The undirected `walkTVPair` join
onto the Dobrushin engine (the priced follow-on) would build on a now
fully fenced engine.
