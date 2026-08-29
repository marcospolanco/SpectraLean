# Pairwise-independence repair of the concentration axioms

**Status:** COMPLETE — the audit, the in-place repair, the consumer
threading, and the Walsh refutation family all delivered on
2026-08-29 (runs `20260829T173340Z-run-1` and
`20260829T195611Z-run-1`; independently re-verified and its records
closed by run `20260829T222414Z-run-1`, which also cleaned the new QA
file to zero linter output — six unused-binder notes, two deprecated
`div_lt_iff`/`lt_div_iff` calls, and one positionless
`Try this: ring_nf` traced by bisection to a `ring` call — and synced
the transit-map stats stamps 3008 → 3099).

## The finding

A Step-0 audit (2026-08-29, run `20260829T173340Z-run-1`) found that
all six independence-carrying concentration axioms
(`hoeffding_inequality`, `hoeffding_empirical`, `bernstein_inequality`,
`bernstein_bounded_variance`, `matrix_hoeffding`, `matrix_bernstein`;
`matrix_azuma_hoeffding`'s `MatrixMDS` martingale shape is unaffected)
hypothesized only *pairwise* `IndepFun` (`∀ i j, i ≠ j → IndepFun …`) —
and pairwise independence does not suffice for Hoeffding/Chernoff
bounds: the classical Walsh-character counterexample.

## The witness

The fifteen nonempty Walsh characters of the fair `BernoulliProduct`
on `Fin 4 → Bool` — `walsh v ω = ∏_{i ∈ supp v} (−1)^{ω i}` indexed by
the nonzero `v : Fin 4 → Bool` (`nzEnum`, the explicit 15-row table):

* pairwise independent under the fair coin: the xor-translation group
  action (`bxor`, an involution per `u`) both preserves the measure
  (`wμ_cell_transport`, via the uniform atom mass `2⁻⁴` and sum
  reindexing) and acts on characters multiplicatively (`walsh_mul`),
  which forces all four joint sign cells of any genuinely distinct
  nontrivial pair to a common mass `q` with `4 q = 1`
  (`wcell_common_mass`); the ±1 `indepFun_sign_fibers` helper then
  upgrades the four cell masses to full `IndepFun`;
* centered: a single-coordinate flip is a measure-preserving
  involution negating the character (`walsh_sum_zero`,
  `walsh_mean_zero`);
* bounded by `1`, but their sum is `15` on the all-false atom (mass
  `1/16`) and `−1` elsewhere (`walsh_total_sum`, `wFam_sum`);
* so at the stated thresholds every old tail event contains an atom
  of mass `1/16`, while the old bounds are below `1/16` by elementary
  arithmetic (`exp_half_ge`, `exp_one_ge`, `add_one_le_exp`, `ring`,
  `norm_num` — no external numerics; `e^{1/2} ≥ 3/2` gives
  `e^{15/2} > 64`, `e^{45/8} > 64` from `e ≥ 9/4` and
  `e^{5/8} ≥ 13/8`).

The six hypothesis-form refutations live in
`Scaffold/QA/Concentration/PairwiseIndependence_QA.lean`
(`old_*_pairwise_refuted_QA`), the same pattern as the 2026-08-28
degenerate-dimension refutations: the hypothesis is exactly the old
statement's conclusion instance at the fixture, all old hypothesis
clauses are *proved* at the fixture (the pairwise clause included —
that is the point), and `False` follows. All six are exactly
`propext, Classical.choice, Quot.sound` (`wip/pairwise2_axcheck.lean`)
— a refutation cannot carry the axiom it refutes. The matrix pair
lifts the scalar family through the rank-one idempotent `E` with
`‖E‖ = 1` proved from `‖Eᴴ E‖ = ‖E‖²` and idempotence.

## The repair

All six axioms repaired in place: the pairwise clause became
`iIndepFun` (mutual independence), the exact hypothesis shape of the
cited sources (Tropp's "independent random matrices", Vershynin's and
Wainwright's "independent" — the pairwise weakening was a
transcription artifact, not a source difference). Zero new axioms
(count stays 10). Consumer threading, public statements unchanged:

* `BernoulliProduct`: `toMeasure_cyl_inter` (finite cylinder
  intersections), `iIndepFun_coord`, `iIndepFun_of_injective`
  (generic), `iIndepFun_coord_apply`, `iIndepFun_coord_matrix`;
* `IIDProduct`: the same package for `iidPMF`
  (`iIndepFun_indicator_coord` the `hoeffding_empirical` clause);
* `EdgePerturbation`: `iIndepFun_perturbSummand`,
  `iIndepFun_degPerturbSummand`;
* `Sparsification`: `iIndepFun_ssSummand`;
* `Derived/EmpiricalStationary`, `Derived/SparsificationTail`,
  `Derived/EdgePerturbationTail`: clause sites threaded; the pairwise
  lemmas remain on the shelf as the two-point consequences (they are
  the refutation records' interface);
* QA re-instantiations: the constant-family zero-sequence pins now
  through `iIndepFun_const_real_QA` / `iIndepFun_const_matrix_QA`
  (a constant family is trivially mutually independent — the
  pre-existing `indepFun_const_*_QA` pairwise pins remain).

## Verification

Spike-first (`wip/pw_a.lean`, `wip/pw_d.lean`, both iterated to zero
errors/warnings); `lake env lean` zero errors on all touched modules;
explicit `lake build` targets on
`IIDProduct`, `Sparsification`, `EmpiricalStationary`,
`SparsificationTail`, `Scalar_QA`, `Matrix_QA`,
`EmpiricalStationary_QA`, `PairwiseIndependence_QA`;
`#print axioms` via `wip/pairwise2_axcheck.lean` (6 refutations +
engine, exactly the standard three); full `lake build` ✔ (2405/2406)
immediately followed by `check_build_completeness.py` — 129 source
files, 129 fresh artifacts, 0 stale, 0 missing, exit 0;
`lint_axioms` (10 axioms, both findings allowlisted-confirmed, the
repaired `iIndepFun` clauses carry no new guard surface),
`check_citations`, `check_markdown_links` pass; scoreboard
regenerated (3008 → 3099, generator idempotent).

## Degenerate-corner note

The repair changes the independence clause only; the `[Nonempty V]`
guards (2026-08-28) are untouched, and the new `iIndepFun` clause is
*stronger* than the old pairwise one, so the old refutations and
honesty pins carry over verbatim. The new QA file's engine has no
axiom contact at all.

## Open residues

None owed. `hoeffding_lemma` remains the one zero-consumer axiom (its
natural consumer is `bernstein_inequality`'s own proof — upstream
work).
