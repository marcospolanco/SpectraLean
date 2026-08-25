# Proposal: Primitive Power Convergence — the Directed Mixing Gate Opened by Admission

**Status:** **DELIVERED 2026-08-24** (run `20260824T224813Z-run-1`) —
Steps 0 (this survey) and 1 (the axiom + consumer modules + QA) in
one run per the Steps 0+1 precedent of the PF-consumer deliveries;
see the delivery record at the bottom. One new axiom (count 9 → 10);
every other new declaration hard crust except the consumers
conditional on the new axiom exactly as recorded below — and
`#print axioms` verifies **zero `perron_frobenius` contact** in every
conditional theorem (the two axioms' trust costs independent).

Assessed from `Scaffold/Mathlib/LinearAlgebra/PerronFrobenius.lean`
(the existing axiom's exact carrier conventions and calibration
style), `Scaffold/Mathlib/GraphTheory/PageRank.lean` (the consumer
layer: `googleMatrix`, `googleMatrix_pos`, `googleMatrix_row_sum`, the
row-stochasticity bridge), `IrreducibleStationary.lean` (the
stationary interface `π ᵥ* P = π` and the transfer-lemma pattern), and
the pin's `Filter.Tendsto`/`Matrix.pow` lemmas.

## The obligation this discharges

The standing handoff (proposals README, execution plan, backlog item
8's closing note) names directed-axis **mixing/rate work** as the
natural next candidate, "gated on a primitivity-shaped admission —
`perron_frobenius` deliberately claims no strict dominance". The
`PageRank` module's own statement-shapes section records the same gate
from the consumer side: "Nothing about power iteration, rates, or
mixing: geometric convergence … needs strict spectral dominance, which
the axiom deliberately does not claim … those are separate future
obligations, not smuggled in here."

This proposal is that admission, plus its first consumer. The
deliberate no-dominance scope of `perron_frobenius` was a correctness
decision (the `strict_dominance_refuted_QA` imprimitivity fence), so
convergence — the statement every mixing and power-method result needs
— is genuinely missing from the axiom surface, and it cannot be
derived from the existing axiom: on the irreducible-but-periodic
directed 2-cycle the powers provably do not converge (the QA fence
below proves this), so any convergence statement *must* add a
hypothesis the existing axiom does not carry. Primitivity — H&J's
definition, some positive power strictly positive — is that missing
hypothesis, and it is exactly what the PageRank construction already
delivers structurally: the teleportation floor makes `googleMatrix`
strictly positive on every nonnegative input at `0 ≤ α < 1`
(`googleMatrix_pos`, hard crust), so primitive with `k = 1`. The loop
closes: the delivered layer proves the PageRank distribution *exists
and is unique*; this proposal proves it is *computable* — the power
iteration `Gᵗ *ᵥ x` converges to `(π ⬝ᵥ x) • 1`, the classical
PageRank algorithm.

## The statement (Step-0 recorded shape)

### The axiom (one new admission)

On a primitive row-stochastic matrix, with the stationary distribution
supplied as hypotheses (given-π form — consumers hold the delivered
unique vector; no `∃`, which would force a second uniqueness layer
through the new axiom):

```
axiom primitive_power_tendsto (P : Matrix V V ℝ)
    (hnn : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    (hprim : P.IsPrimitive)
    {π : V → ℝ} (hπnn : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* P = π) (x : V → ℝ) :
    Tendsto (fun t : ℕ => (P ^ t) *ᵥ x) atTop (𝓝 ((π ⬝ᵥ x) • 1))
```

with `Matrix.IsPrimitive P : Prop := ∃ k, 0 < k ∧ ∀ i j, 0 < (P ^ k) i j`
(H&J's definition of primitivity, verbatim).

Content: every row of `Pᵗ` converges to `πᵀ` (equivalently the column
action converges to the rank-one stationary projector `1 πᵀ` applied to
`x`). Carrier conventions match the shelf exactly: row-stochasticity as
`∀ i, ∑ j, P i j = 1` (the bridge `walkTransitionMatrix_eq_of_row_sum_one`
takes this form), stationarity in Mathlib's left-action form
`π ᵥ* P = π` (the `IrreducibleStationary`/`PageRank` convention).

### The unconditional transfer layer (hard crust, in the axiom's module)

1. `isPrimitive_of_pos`: a strictly positive matrix is primitive
   (`k = 1`) — the entire content of the PageRank consumer's discharge.
2. `isIrreducible_of_isPrimitive`: primitivity implies irreducibility —
   an entry of `P ^ k` is a sum over length-`k` walks, so a positive
   entry yields a positive-weight walk, i.e. `ReflTransGen` closure;
   the induction decomposes the power step by `pow_succ` +
   `Finset.sum_pos'`. Load-bearing on `Matrix.IsIrreducible`'s exact
   combinatorial shape — the connective tissue between the new axiom's
   hypothesis and the delivered PF-consumer layer's.
3. `rowStochastic_pow_mulVec_one`: powers of a row-stochastic matrix
   fix `onesVec` — the coherence engine (QA Section C) and the mass
   bookkeeping.

### The consumer layer (conditional on the new axiom; no PF contact)

In a new `GraphTheory.DirectedMixing` importing `PageRank` +
`PrimitiveConvergence`:

4. `googleMatrix_isPrimitive` (unconditional): `G` is primitive on
   every nonnegative input with positive degrees at `0 ≤ α < 1`,
   nonempty `V` — `isPrimitive_of_pos` at `googleMatrix_pos`.
5. **`pageRank_powerIteration`** (conditional on the new axiom alone):
   for every starting vector `x`, `(G ^ t) *ᵥ x → (π ⬝ᵥ x) • 1` at any
   nonnegative mass-one stationary `π`. Trust-boundary note: this
   theorem is *not* conditional on `perron_frobenius` — producing `π`
   needs PF, but the convergence statement takes `π` as a hypothesis,
   so the two axioms' trust costs are independent and separately
   consumable.
6. `pageRank_entrywise_tendsto`: `(G ^ t) i j → π j` — the column form
   (at `x = e j`, through `tendsto_pi_nhfs` coordinate projection).
7. `pageRank_walk_tendsto`: `ν ᵥ* (G ^ t) → π` for every nonnegative
   mass-one start `ν` — the Markov-chain mixing first slice
   (entrywise/Π-topology convergence; the ℓ²/TV rate forms are
   explicitly out of scope, below), assembled from 6 by finite-sum
   interchange.

## Admission-policy compliance (the eight conditions)

1. **Concrete downstream use:** the PageRank power iteration (the
   classical algorithm; delivered loop-closer with the 2026-08-24
   existence/`∃!` layer) and the directed axis' first mixing statement
   (7). The standing handoff named exactly this gate.
2. **Meaningful, composable conclusion:** `Tendsto` of the power
   action at an explicit limit vector — consumable by any rate,
   total-variation, or entrywise statement that comes later.
3. **Explicit assumptions:** nonnegativity, row-stochasticity,
   primitivity (the positivity form, not an undefined adjective), and
   the stationary distribution's nonnegativity/mass/stationarity.
4. **Precise citation:** Horn & Johnson, *Matrix Analysis*, 2nd ed.,
   §8.5 (primitive matrices), stated for primitive stochastic matrices
   as the standard Markov-chain convergence theorem (cf. Levin–Peres–
   Wilmer, *Markov Chains and Mixing Times*, Theorem 4.9, the
   stochastic specialization). Section-level locator recorded; the
   page/theorem-level locator is pending the same physical-copy review
   as the other Horn–Johnson rows — not invented here.
5. **Statement differences from source:** (a) the source states
   `lim (A/ρ(A))^m = x yᵀ` at the Perron data; this statement is the
   row-stochastic specialization at `r = 1` with `x = 1` (right
   Perron vector of a row-stochastic matrix is `onesVec`, the shelf's
   `walkTransitionMatrix_mulVec_one` shape) and `y = π` normalized —
   the specialization is one line of Perron-vector identification, and
   stating it directly keeps the blast radius small; (b) primitivity is
   H&J's positive-power definition verbatim; (c) the given-π form
   (source's `y` is existentially produced); (d) arbitrary `Fintype V`
   — no guard needed: on the empty type the `∑ π = 1` hypothesis is
   unsatisfiable (vacuous), and on a singleton the statement is
   trivially true.
6. **Small blast radius:** one statement, no bundled corollaries, no
   rate clause, no `∃!`.
7. **Indices:** `index/sources/horn_johnson_matrix_analysis.md` gains
   the §8.5 mapping row; `index/map/spectral_graph.md` gains the two
   new module sections and declaration rows.
8. **QA obligation:** three sections below — the positive witness (the
   reducible fixture's power iteration pinned to the raw-verified
   uniform value), the **periodicity refutation** (the mandated fence:
   the directed 2-cycle, irreducible and stochastic, powers provably
   oscillating — so the hypothesis-free conclusion is refuted in
   proved form and `hprim` is load-bearing), and the coherence join
   (the `onesVec` invariance vs the axiom's limit).

## Honest scoping decisions (recorded before stating)

- **No rate.** The geometric rate (`|λ₂|`-shaped bounds, total
  variation, χ²) needs the second-eigenvalue-modulus machinery, which
  for non-symmetric matrices needs the complex spectral theory the
  shelf does not have. Convergence alone is this admission; rates are
  a separate future admission gated on a consumer, not smuggled in.
- **`hrow` is a convenience, not a fence.** On a primitive nonnegative
  matrix with a positive mass-one stationary vector, Perron–Frobenius
  itself pins the spectral radius to `1`, so the row-sum hypothesis is
  implied in substance by the others; it is kept because it is the
  source's carrier, checkable structurally (`googleMatrix_row_sum`),
  and the form the bridge consumes. No refutation QA is possible or
  claimed for it — recorded here so the QA section's fence is read as
  `hprim`'s, not `hrow`'s.
- **`hnn` is part of the cited theorem's hypotheses** (PF theory is
  nonnegative-matrix theory); no small falsifying fixture is exhibited
  and none is claimed — same stance as the `perron_frobenius`
  admission's own `hnn`.
- **Coordinate/Π topology only.** The limit is entrywise (Pi-norm);
  operator-norm convergence of `Pᵗ − 1πᵀ` is not stated. On finite
  types these coincide, but stating the vector action is the honest
  consumer-facing form.

## Route survey (what the proofs consume; verified against the pin)

- The axiom needs only `Filter`/`Tendsto` statement forms — no
  analysis import chain beyond what `Heat` already showed sufficient
  (`Mathlib.Order.Filter.Tendsto` plus the Pi-topology instances).
- `isIrreducible_of_isPrimitive`: `Matrix.pow_succ`, `Matrix.mul_apply`,
  `Finset.sum_pos'` (nonnegative terms, positive sum ⇒ a positive
  term), `mul_pos`-splitting, `ReflTransGen.tail` — all present at the
  pin or on the shelf.
- The 2-cycle oscillation fence: `pow_succ` induction gives
  `P₂ ^ (2*k) = 1` and `P₂ ^ (2*k+1) = P₂`; non-convergence via
  subsequence composition (`Filter.Tendsto.comp`) with
  `t ↦ 2*k`, `t ↦ 2*k+1` both tending to `atTop` (proved from
  `mem_atTop`), plus `tendsto_const` and limit uniqueness.
- The walk form 7: entrywise 6 + `Finset.sum` interchange of two
  convergent finite sums (`Tendsto.add` induction or the pin's
  tendsto-sum lemma, spiked first).

## QA obligations (mandated sections)

- **A (positive witness, the reducible `A4` fixture at `α = 1/2`):**
  primitive at `k = 1` (all sixteen `A4G` entries pinned ≥ `1/8`,
  already on shelf from `PageRank_QA`); the power-iteration theorem
  instantiated at `e₀` with limit the uniform `u4` (whose
  stationarity, nonnegativity, and mass are raw-verified on shelf);
  the second-iterate pin `(A4G ^ 2) 0 3 = 3/16` computed raw, strictly
  inside `1/4` — the sequence visibly in motion toward its limit.
- **B (the periodicity refutation — the fence):** `P₂ = !![0,1;1,0]`:
  nonnegative, row-stochastic, *and irreducible* (proved), with
  `P₂ ^ t *ᵥ e₀` provably alternating between `e₀` and `e₁` — hence
  `¬ Tendsto` in proved form. This is simultaneously the fence for
  `hprim` (the hypothesis-free conclusion is false) and the
  documentation of the existing axiom's honest scope: irreducible +
  stochastic does not converge; exactly the primitivity/aperiodicity
  clause is what the no-dominance decision reserved.
- **C (coherence):** the `onesVec` join — `G ^ t *ᵥ onesVec = onesVec`
  unconditionally (the new `rowStochastic_pow_mulVec_one`) against the
  axiom's limit `(π ⬝ᵥ onesVec) • 1` at the fixture; limit uniqueness
  forces `π ⬝ᵥ onesVec = 1`, cross-checked against `hπsum` computed
  raw; plus the walk form 7 instantiated at a non-uniform start on the
  fixture (genuinely mixing toward uniform).

## Explicitly out of scope (gated, named)

Geometric rates / total-variation / χ² directed mixing (needs complex
spectral radius machinery — separate admission, gated on a consumer);
the transposed/column-stochastic axiom variant (no consumer named);
`Matrix.IsPrimitive` characterization theorems (aperiodicity ⇔
primitive; no consumer); the magnetic-Laplacian slice (backlog item 8
scope note).

## Delivery record (2026-08-24, run `20260824T224813Z-run-1`)

Steps 0+1 in one run, exactly as scoped. **One new axiom (count
9 → 10); QA 2021 → 2051 (`DirectedMixing_QA` a new file at 30 by the
generator metric).**

**Delivered:** (1) the new
`Scaffold/Mathlib/LinearAlgebra/PrimitiveConvergence.lean`
(namespace `Scaffold.LinearAlgebra`; the umbrella importing it) —
`Matrix.IsPrimitive` (H&J's positive-power definition, verbatim),
the admitted **`primitive_power_tendsto`** (given-π form exactly as
recorded above; the row-stochastic specialization of the H&J §8.5
primitive limit), and the unconditional transfer layer:
`isPrimitive_of_pos` (k = 1), `reachable_of_pow_pos` +
`isIrreducible_of_isPrimitive` (the entry-of-power walk decomposition
— an entry of `P ^ k` is a sum over length-`k` walks, positivity
yields a positive-weight path), `pow_mulVec_one` (row-stochastic
powers fix the constant-one vector), plus the two generic conditional
corollaries `primitive_entrywise_tendsto` (columns of `Pᵗ` → `π`, at
the basis vector through `Matrix.mulVec_single`) and
`primitive_vecMul_tendsto` (`ν ᵥ* Pᵗ → π`, through the private
finite-sum tendsto induction — the pin has no tendsto-sum lemma).
(2) The new `Scaffold/Mathlib/GraphTheory/DirectedMixing.lean`
(namespace `SpectralGraphTheory`; minimal imports PageRank +
PrimitiveConvergence; the umbrella importing it) — `googleMatrix_isPrimitive`
(the floor is primitivity: aperiodicity *derived*, strictly stronger
than the delivered irreducibility), **`pageRank_powerIteration`** (the
classical algorithm as a theorem), `pageRank_entrywise_tendsto`,
`pageRank_walk_tendsto` (all conditional on the new axiom alone), and
the graph-side mass translation `googleMatrix_pow_mulVec_onesVec`.
(3) `Scaffold/QA/SpectralGraph/DirectedMixing_QA.lean` (+30, reusing
`PageRank_QA`'s fixtures by QA-to-QA import): Sections A–C exactly as
mandated.

**The admission-policy checklist held:** concrete consumer delivered
in the same run; the statement composable (`Tendsto` at an explicit
limit vector); hypotheses explicit (nonnegativity, row sums,
primitivity, the stationary trio); citation precise at section level
with the physical-copy caveat (H&J §8.5 primary, LPW Theorem 4.9 the
stochastic-form cross-reference); statement differences recorded in
both the module documentation and the source index; small blast
radius (one statement, no rate, no `∃!`); indices updated
(`index/sources/horn_johnson_matrix_analysis.md` §8.5 row + notes,
`index/map/linear_algebra.md` and `index/map/spectral_graph.md`
sections and declaration rows); QA delivered at all three mandated
levels.

**QA (all three mandated sections + the coherence join):**
(A) the positive witness on the reducible fixture — primitivity by
theorem route with a raw floor spot-check at a zero-support pair; the
power iteration at `e₀` with the limit coefficient pinned raw to the
uniform value `u4 ⬝ᵥ e₀ = 1/4`; the second iterate computed
completely raw from the sixteen pinned entries, `(A4G ^ 2) 0 3 =
3/16 < 1/4` — the sequence visibly in motion toward its limit; the
entrywise form at a zero-support pair; the walk form at the
non-uniform start `![1/2, 1/2, 0, 0]` genuinely mixing toward
uniform. (B) the periodicity refutation — `P2 = !![0,1;1,0]`:
nonnegative, row-stochastic, *and irreducible* (all proved), the
uniform distribution verified stationary raw, `P2_not_primitive`
(every power is `1` or `P₂`, both with zero entries —
`Nat.even_or_odd` + the two power laws), and `P2_no_limit` (the
even/odd subsequences are constantly `e₀`/`e₁` via `Tendsto.comp`
with `tendsto_atTop_atTop` witnesses, so no limit exists for any
candidate — `tendsto_nhds_unique` forcing `e₀ = e₁`, contradiction at
coordinate `0`); `P2_fence_isolation` collects every other axiom
hypothesis as *verified* alongside both refutations — exactly `hprim`
isolated. (C) the coherence join — `dmQA_onesVec_fix` (the powers fix
`onesVec` unconditionally) against the axiom's limit at `x =
onesVec`, forcing the limit vector to *be* `onesVec` — the mass fact
`π ⬝ᵥ 1 = 1` derived from the axiom — cross-checked against the raw
`∑ u4 = 1`. One QA declaration deliberately removed after drafting:
an equality lemma joining the two irreducibility routes (rfl by proof
irrelevance — inert surface, the strategy's load-bearing principle's
exact warning case; a note in the file documents why no such lemma
can carry content).

**Verification:** spike first (`wip/ppc_spike.lean`, several rounds
to green — the fixes recorded in the pin-technique list below);
`lake env lean` on both public modules and the QA file — zero errors,
zero warnings each; explicit `lake build` targets all ✔ (1736/1736,
2195/2195, 2201/2201); `#print axioms` via `wip/ppc_axcheck.lean` on
all 13 public module + 22 QA declarations — the unconditional ones
the standard three only, the six convergence theorems
`primitive_power_tendsto` + the standard three, and **no
`perron_frobenius` anywhere** (the trust-cost independence claim is
machine-verified); **full `lake build` ✔ (2263 targets, +2, "Build
completed successfully")**; `lint_axioms` (**10**, the new axiom
mapped in the indices), `check_citations`, `check_markdown_links`
pass; scoreboard regenerated (**2051/10/0**, idempotent). Records
updated: README (2051; the status paragraph's convergence-layer
clause; two module-table rows), the coverage map (the PF row's
primitive-limit sentence), the radar (QA axis synced 2021/51 →
2051/52, held 4.0), the scoreboard (four verification rows + the
interpretation bullet), `index/sources/horn_johnson_matrix_analysis.md`
(§8.5 row + notes), `index/map/linear_algebra.md` (status + 8
declaration rows + consumers de-staled), `index/map/spectral_graph.md`
(the DirectedMixing section), backlog item 8 (the sixth update), the
umbrella `Scaffold.lean`, this plan, and the activity log. Nothing
committed; the prior runs' uncommitted deliveries preserved
untouched.

**Pin-technique list (the spike's recurring fixes):**
`tendsto_nhds_unique` takes the tendstos in (a-tendsto, b-tendsto)
order for conclusion `a = b` — match the goal's LHS to the *first*
argument; `tendsto_const` is `tendsto_const_nhds` at this pin;
`Finset.sum_pos'` has the wrong shape here (it is the `1 ≤ f → 1 <
∑`-family) — the positive-term extraction is `by_contra` + `push_neg`
+ `Finset.sum_nonneg` at the negated sum; `mul_nonpos_of_nonpos_of_nonneg`
and `mul_nonpos_of_nonneg_of_nonpos` both needed (the two factor
splittings); `Matrix.mulVec_mulVec` is right-associative
(`M *ᵥ N *ᵥ v = (M * N) *ᵥ v`), so the induction rewrites with `←`;
`Finset.induction_on`'s `insert` alternative takes
`| @insert m s hm ih` (all four binders named with `@` — the plain
`| insert m s hm ih` arity fails); `Finset.sum_insert` after `rw`
strand-rewrites only some occurrences when the bound variable shadows
the inserted element — state the two sides as explicit `have`
function equalities (`funext` + `rw`) and rewrite with those;
`Matrix.one_apply` lives in `Data/Matrix/Diagonal.lean` (not Basic);
matrix/vector literals over ℝ are `noncomputable def`s at this pin
(`Real.instLinearOrderedField`); `𝓝` needs `open scoped Topology`;
QA fixtures from another QA module need full qualification inside
`open ... in` blocks (`A4`/`u4` live in `Scaffold.QA.SpectralGraph`);
`Finset.sum_univ_four` is `Fin.sum_univ_four` at this pin; and the
`Nat.even_or_odd` destructuring yields `m + m` (not `2 * m`) for the
even case — bridge with an explicit `show m + m = 2 * m from by ring`.

**Open follow-ons (priced, gated):** the *rate* layer (geometric
decay `|λ₂|ᵗ`-shaped, total-variation/χ² — needs the complex spectral
theory of non-symmetric matrices, a separate admission gated on a
named consumer); the column-stochastic/transposed axiom variant (no
consumer named); `IsPrimitive` characterization theorems
(aperiodicity ⇔ primitive — no consumer); the magnetic-Laplacian
slice (backlog item 8's own scope note).
