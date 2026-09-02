# The Cesàro stationary-existence engine — discharging the `perron_frobenius` consumer surface

**Status:** COMPLETE — delivered 2026-09-02 (run `20260902T125928Z-run-1`, session
`ses_f9dd39978ffeMCIXqi4ylgfxZX`)

## Motivation and leverage

`perron_frobenius` is one of the four admitted axioms, and its entire
non-QA consumer surface is the stationary-distribution layer:

- `GraphTheory/IrreducibleStationary.lean` — the engine
  `exists_walkPerronVector` plus four stationary theorems;
- `GraphTheory/PageRank.lean` — three PageRank theorems composed on it;
- every `GraphTheory/DirectedMixing` and
  `Derived/EmpiricalStationary` instantiation that *produces* `π`
  through them (`pageRank_powerIteration` already states convergence
  at a hypothesized `π`; the existence/uniqueness that instantiates it
  is the conditional layer).

The engine consumes only two clauses of the axiom (the nonnegative-
eigenvector eigenvalue identification and the uniqueness-up-to-scale
clause) at eigenvalue `1`. Neither needs Perron–Frobenius: the
stationary theory of a finite irreducible chain is classically
elementary, and the elementary route — the one this delivery prices —
is the Krylov–Bogoliubov/Cesàro-averaging argument plus two
irreducibility observations:

1. **Power positivity** (`ReflTransGen` induction): for a nonnegative
   irreducible `M`, every index pair `(i, j)` has a power `M^m` with
   `0 < (M^m) i j` — strong connectivity gives an arc path, and the
   entry of a power dominates the product along any path.
2. **Existence** (Cesàro averaging): for any nonnegative
   row-stochastic `M` — *no irreducibility* — the Cesàro means
   `μ_t := t⁻¹ • ∑_{s<t} (1 ᵥ* M^s)` live in the compact simplex
   `{x | 0 ≤ x ∧ ∑ x = |V|}` (Tychonoff `isCompact_univ_pi`, pi
   topology, no metric machinery), and the telescoping identity
   `μ_t − μ_t ᵥ* M = t⁻¹ • (1 − 1 ᵥ* M^t)` bounds every entry of the
   defect by `(|V| + 1)/t → 0`. A subsequential cluster point
   (`IsCompact.tendsto_subseq`) is stationary by entrywise continuity.
3. **Strict positivity**: a nonzero nonnegative stationary `σ`
   satisfies `σ = σ ᵥ* M^m` for every `m`; if `σ j₀ = 0`, power
   positivity at `(i, j₀)` forces `σ i = 0` for every `i` (each
   single summand `σ i (M^m) i j₀ ≥ σ i · (positive)` would otherwise
   contradict the zero), so `σ = 0` — contradiction.
4. **Uniqueness up to positive scale** (the min-ratio trick): for
   nonzero nonnegative stationary `σ, τ`, both strictly positive by 3;
   at the minimizer `j*` of `j ↦ σ j / τ j` the difference
   `σ − c • τ` is nonnegative, stationary, and zero at `j*`, hence
   zero by 3, i.e. `σ = c • τ` with `c > 0`.

## Statement design

Every existing public statement keeps its exact name, shape, and
hypothesis set; only proofs and conditional-status docstrings change:

- `exists_walkPerronVector`, `exists_stationaryVec_of_irreducible`,
  `stationaryVec_smul_of_irreducible`,
  `existsUnique_stationaryVec_of_irreducible`,
  `stationaryVec_pos_of_irreducible` (IrreducibleStationary);
- `exists_pageRankVec`, `existsUnique_pageRankVec`, `pageRankVec_pos`
  (PageRank) — proofs unchanged (they already compose only the
  engine's conclusion).

Two new public reusable declarations join the shelf, stated at generic
matrices (the walk applications instantiate them):

- `exists_pow_pos_of_isIrreducible` — clause 1 above, the standard
  "irreducible ⇒ power-positive" companion fact;
- `exists_nonneg_stationary_of_row_stochastic` — clause 2, the
  Krylov–Bogoliubov engine at generic nonnegative row-stochastic
  matrices: `∃ σ, nonneg ∧ σ ≠ 0 ∧ σ ᵥ* M = σ`, `[Nonempty V]` (on the
  empty type no nonzero vector exists). No irreducibility hypothesis —
  existence holds for *reducible* chains too, which the QA pins as the
  honest scope statement.

## The axiom's disposition

`perron_frobenius` itself **stays admitted at its unchanged
statement**: the rootMultiplicity and complex-domination clauses are
untouched by this route, and its own QA (`PerronFrobenius_QA.lean`,
including the `-- @refutes` imprimitivity fence) keeps exercising the
axiom directly. What changes is its consumer state: after this
delivery it has **zero non-QA consumers**. That is a recorded state
change (the admission policy's first gate is a concrete downstream use
case), and the deprecation/removal decision — with its compatibility
window, per `docs/2_ARCHITECTURE.md` §9 — is an operator decision this
run explicitly does not make. Every records surface that counts the
axiom's load-bearing consumers (`index/load_bearing_axioms.md`, the
coverage map, README, the radar, the map data, the backlog) is updated
to the zero-consumer state with the flag.

## Corner analysis (pre-spike)

- **Empty `V`**: the engine carries `[Nonempty V]` (supplied at the
  walk layer by `hex`, exactly as the existing statements already do);
  on the empty type `σ ≠ 0` is unsatisfiable — the hypothesis is
  honest, not vacuous decoration.
- **`t = 0` in the Cesàro means**: `μ_0 = 0⁻¹ • 0` is junk, but the
  argument only ever uses `t ≥ 1` bounds `(|V|+1)/t`; the spike states
  the defect bound for `0 < t` explicitly (`Nat.pos_of_ne_zero` /
  `Nat.succ_pos` supply it).
- **Strict positivity divides by nothing**: clause 3's contradiction
  is at the *summand* level (no division); clause 4 divides by `τ j`
  under clause-3 strict positivity — the reducible fence (two disjoint
  edges, two non-multiple stationary vectors, already in
  `IrreducibleStationary_QA` as `A4_existsUnique_refuted_QA`) is
  exactly the hypothesis-dropped refutation for both.
- **Periodic chains**: the Cesàro route is *why* periodicity is
  survivable — `P^t` need not converge (`P2_no_limit_QA` in
  `DirectedMixing_QA`), the *averages* still converge; no convergence
  of powers is claimed anywhere.

## QA plan

A new mechanism section in `IrreducibleStationary_QA.lean`:

1. the telescoping identity pinned numerically on the asymmetric star
   `A₃`: `μ₃ − μ₃ ᵥ* P = (−1/2, 1/4, 1/4)` computed both from the raw
   definition and from the identity's right side `t⁻¹(1 − 1 ᵥ* P³)` —
   the engine's central computation falsifiable at fixed values;
2. power positivity instantiated on `A₃` (off-diagonal at `m = 1`,
   return at `m = 2` pinned to the raw entry);
3. the engine's output identified on `A₃`: any nonnegative mass-three
   stationary vector equals `3 • π₃` (joined to the file's existing
   hand-value identification);
4. the min-ratio clause pinned at the constant ratio `σ = (2,1,1)`,
   `τ = (6,3,3) ⇒ c = 1/3` — attained exactly;
5. the reducible-fence reuse: the existing `A4` refutation is cited as
   the uniqueness-dropped fence; the engine's *existence* instantiated
   unconditionally on the same reducible fixture (existence needs no
   irreducibility — the honest scope pin);
6. the full formerly-conditional consumer surface re-audited:
   `#print axioms` on the engine + four stationary theorems + three
   PageRank theorems + the QA consumers = exactly
   `propext, Classical.choice, Quot.sound`.

## Verification ladder

Spike first (`wip/cesaro_spike.lean`, zero errors/zero warnings before
any shelf edit); `lake env lean` on every touched module; explicit
`lake build` targets; the axiom audit; full `lake build` +
`check_build_completeness.py`; `lint_axioms` (4 axioms unchanged);
`check_refutation_independence` (9-tag clean); `check_public_reachability`;
`check_citations`; `check_markdown_links`; `check_backlog_freshness`;
scoreboard regenerated; map-freshness after the stats sync.

## Delivery record

**Everything landed as planned above.** The shelf
(`GraphTheory/IrreducibleStationary.lean`): four generic public
row-action helpers (`vecMul_mul` — the `ᵥ*`-shaped associativity the
pin lacks, `vecMul_entry`, `sum_vecMul_eq_of_row_sum`, `vecMul_sum`),
three power-entry facts (`pow_row_sum`, `pow_entry_nonneg`,
`pow_entry_le_one`), **`exists_pow_pos_of_isIrreducible`**, the
**Krylov–Bogoliubov cluster lemma `exists_cluster_stationary_of_orbit`**
(public, reusable), **`exists_nonneg_stationary_of_row_stochastic`**
(public, no irreducibility), two private matrix-level support lemmas
(strict positivity; min-ratio smul), and the re-proofs of
`exists_walkPerronVector` + the four stationary theorems at unchanged
statements. `PageRank.lean`'s three theorems: proofs unchanged, trust
boundaries de-staled. `DirectedMixing.lean`: the module docstring's
"producing `π` needs that axiom" lines de-staled. QA +22 (3712 → 3734,
`IrreducibleStationary_QA.lean`'s Section E): the orbit value pins
`g₁ = (2, 1/2, 1/2)` (entry-route + assembled) and `g₂ = 1` (through
`vecMul_mul` + `pow_two` + the pinned `g₁`), the **oscillation fence**
`g₁ ≠ g₂` (the engine's input sequence never converges — only its
averages do), **the one-period Cesàro mean exactly stationary**
(`μ₁ ᵥ* P = μ₁` by `Matrix.add_vecMul`/`vecMul_smul`/`vecMul_mul` at
the telescoped second step, with the value pin `μ₁ = 3•π₃` — the
averaging route's whole point on a fixture whose powers oscillate
forever), power positivity at the pinned return arc `(P²) 1 1 = 1/2`
plus the existence form, **the engine's output identified** (every
nonnegative mass-3 stationary vector = `3•π₃`, through the file's
existing hand-value uniqueness), **the min-ratio scalar pinned
exactly** (`c = 1/4` at `3•π₃` vs `12•π₃`, from the walk-level smul
theorem), and **reducible-input existence** (the honest scope pin:
existence instantiates on the two-block fixture where the existing
fences refute uniqueness and positivity).

**The axiom's disposition, delivered as planned:** `perron_frobenius`
stays admitted at its unchanged statement — its `lint_axioms`
allowlist entry, `-- @refutes` tags, and its own QA
(`PerronFrobenius_QA.lean`) are untouched — but now has zero non-QA
consumers; the state change is recorded in
`index/load_bearing_axioms.md` (with the deprecation decision
explicitly flagged as the operator's), the coverage map, README, the
radar's axiom-minimization axis, the backlog's item-8 twelfth update,
and both modules' docstrings.

**Verification:** spike first (`wip/cesaro_spike.lean` — the engine,
the downstream re-proofs, and the QA section iterated to zero
errors/zero warnings before any shelf edit); `lake env lean` zero
errors/zero warnings on both touched shelf modules and the QA module;
explicit `lake build` targets ✔; **`#print axioms` via
`wip/cesaro_axcheck.lean` on 37 audited declarations (10 engine +
5 re-proved stationary + 3 PageRank + 3 directed-mixing consumers +
16 QA): every one exactly `propext, Classical.choice, Quot.sound`**;
**full `lake build` ✔ immediately followed by
`check_build_completeness.py` — 133 source files, 133 fresh artifacts,
0 stale, 0 missing, exit 0**; `lint_axioms` exit 0 (4 current axioms,
unchanged; only the allowlisted-confirmed PF finding);
`check_refutation_independence` (9-tag clean — no tags touched);
`check_public_reachability` clean (63 repo modules); `check_citations`
("All axioms have proper citations!"); `check_markdown_links` clean;
`check_backlog_freshness` clean; scoreboard regenerated (**3734/4/0**);
map-freshness exit 0 after the 3712 → 3734 stats sync in both map
files and SVG regeneration (no station — no tier change).

**Technique findings (the run's recorded traps):**

1. `rw [Matrix.mul_apply]` fails on `(M ^ t * M) i j` even when the
   pattern is literally present — `simp only [Matrix.mul_apply]`
   matches fine; the same HO-flavored mismatch afflicts
   `Finset.sum_apply` and `Pi.sub_apply` under `rw`. When a
   first-order `rw` "should" fire on a higher-order-shaped lemma, try
   `simp only` before restructuring the proof.
2. The QA file's own header note is exactly right and worth repeating:
   under `fin_cases`, substituted `Fin` indices are defeq-but-not-
   syntactic to numerals, so entry lemmas at literal indices match
   `simp only` freely but the assembled vector equalities must go
   through per-entry lemmas + `funext` + `fin_cases` + `exact`
   (defeq-closed) — never `rw` with literal-index lemmas under
   `fin_cases`.
3. `A3_orbit_two_QA` needs `rw [pow_two, ← vecMul_mul, ...]` in that
   order: `← pow_two` first (searching for `?a * ?a`) finds nothing
   because the goal displays `P ^ 2`; the forward rewrite must come
   first, the associativity backward-rewrite second.
4. `div_mul_cancel₀` in this pin takes the numerator explicitly first:
   `div_mul_cancel₀ (σ j₀) (h : τ j₀ ≠ 0)`, not the hypothesis alone.
5. `squeeze_zero` composes cleanly with
   `tendsto_zero_iff_abs_tendsto_zero` only when the iff is *applied
   to the function* (it takes `f` explicitly); `.mpr` on the bare
   name elaborates against a metavariable and reports a confusing
   field-notation error.
6. `((k+1 : ℕ) : ℝ)⁻¹ → 0` has no single direct lemma in the pin at
   this shape; the robust route is
   `tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_atTop_of_monotone
   hmono hbdd)` with `hbdd` from `exists_nat_gt`.
7. `omit [DecidableEq V] in` must precede the docstring (re-confirmed),
   and must NOT be applied to declarations using matrix powers — the
   `Monoid (Matrix …)` instance consumes `DecidableEq` and the omit
   breaks it with an inscrutable `HPow` synthesis failure.

**Remaining scope, honestly:** the full Perron–Frobenius statement —
rootMultiplicity one and the complex-charpoly domination clause —
remains admitted and now zero-consumer; the QA pins exercising it
directly (`PerronFrobenius_QA.lean`) are its only remaining contact
with the repository. Retiring *that* would be a genuine
spectral-theory program (Frobenius normal form or a matrix spectral
radius, neither in the pin), not an elementary route — this delivery
claims nothing about it.
