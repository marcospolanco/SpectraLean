# Linear Algebra

This index maps Lean modules and declarations for classical
finite-dimensional matrix theory that is not specific to the symmetric
eigenvalue toolkit (that lives in the [Spectral Graph Theory
map](spectral_graph.md)).

## Status

**Implemented**: Perron–Frobenius theory for irreducible nonnegative
matrices in `Scaffold.Mathlib.LinearAlgebra.PerronFrobenius` — the
second spectral toolkit, opened for the directed-graph axis
(`docs/1_STRATEGY.md`'s 2026-08-19 scope decision) after the
directed-operators program's calibration witness showed the undirected
positivity layer does not transfer to directed input. **Since
2026-08-24**: primitive power convergence in
`Scaffold.Mathlib.LinearAlgebra.PrimitiveConvergence` — the
primitivity-shaped admission the standing handoff named as the
directed-mixing gate (`proposals/primitive-power-convergence.md`,
explicit axioms 9 → 10), with the unconditional transfer layer
(primitivity from positivity, primitivity → irreducibility by the
entry-of-power walk decomposition, row-stochastic powers fixing the
constant-one vector) and the two generic corollaries (entrywise
column convergence, the row-action walk form).

## Declarations

| Declaration | Kind | Statement | Source |
| --- | --- | --- | --- |
| `Matrix.IsIrreducible` | def | every index reaches every other through positive-weight directed arcs (`Relation.ReflTransGen`) | combinatorial form of H&J irreducibility |
| `perron_frobenius` | **axiom** | for nonnegative irreducible `A` with a positive entry: a Perron root `r > 0` with a strictly positive eigenvector, `rootMultiplicity r A.charpoly = 1`, every nonzero nonnegative eigenvector is a positive multiple of the Perron vector (and its eigenvalue is `r`), and every complex charpoly root has modulus `≤ r`. **No strict-dominance clause** — that needs primitivity | [Horn & Johnson](../sources/horn_johnson_matrix_analysis.md), Theorem 8.4.4 |
| `Matrix.IsPrimitive` | def | some strictly positive power is strictly positive, entrywise (H&J's definition of primitivity verbatim) | [Horn & Johnson](../sources/horn_johnson_matrix_analysis.md), §8.5 |
| `primitive_power_tendsto` | **theorem (retired from axiom 2026-09-02)** | powers of a primitive row-stochastic matrix converge entrywise to the rank-one stationary projector: `(P ^ t) *ᵥ x → (π ⬝ᵥ x) • 1` at any nonnegative mass-one stationary `π ᵥ* P = π` (given-π form) — the row-stochastic specialization of the primitive Perron–Frobenius limit at root `1`, **proved by the Doeblin/Dobrushin contraction route** (the entrywise-range engine below); no rate clause, the proof's `ρ^(t/m)` byproduct explicit but typically loose | [Horn & Johnson](../sources/horn_johnson_matrix_analysis.md), §8.5 (stochastic form cf. Levin–Peres–Wilmer Thm 4.9) |
| `isPrimitive_of_pos` | theorem | a strictly positive matrix is primitive at `k = 1` | — |
| `reachable_of_pow_pos` | theorem | an entry of a positive power is a sum over walks: positivity yields a positive-weight directed path (`ReflTransGen`) | — |
| `isIrreducible_of_isPrimitive` | theorem | primitivity implies strong connectivity — the connective tissue to the `perron_frobenius` hypothesis form | — |
| `pow_mulVec_one` | theorem | powers of a row-stochastic matrix fix the constant-one vector | — |
| `primitive_entrywise_tendsto` | theorem | hard crust since the retirement: every column of `Pᵗ` converges to `π` (at the basis vector, through `Matrix.mulVec_single`) | — |
| `primitive_vecMul_tendsto` | theorem | hard crust since the retirement: `ν ᵥ* Pᵗ → π` for every start summing to one (finite-sum interchange; the pin has no tendsto-sum lemma) | — |
| `entrySup` / `entryInf` / `entryRange` | def | the entrywise supremum/infimum/range of a vector on a nonempty finite type — the quantity Doeblin's coefficient controls (2026-09-02) | — |
**Adversarial-fence coverage (2026-09-05,
`proposals/adversarial-fences-primitive-convergence-family.md`):**
nineteen hypothesis-form fences in the new
`Scaffold/QA/LinearAlgebra/PrimitiveConvergence_QA.lean` cover the
family's bookkeeping layer, the entrywise-range engine (both breakers
per theorem), all three convergence theorems' `hprim` clauses (killed
by the docstring's own directed 2-cycle's oscillation), and the
primitivity suppliers; the convergence trio's stochasticity/π clauses
and the signed-cancellation walk classes carry priced deferrals. The π-clause cluster was closed the same
day (the deferral-closure record): the stationarity and mass
clauses fenced at the strictly-positive spectral-decomposition
fixture, `hπnn` classified entangled through the stationary-space
pin; the trio's `hnn`/`hrow` clauses and the walk quartet remain
priced. The remainder was closed 2026-09-06 (the
remainder-closure record): the signed-cancellation walk quartet and
the positive-clause tail fenced, the trio's `hnn`/`hrow` clauses
classified (truth-removable through Perron; no admissible fixture) —
the family's priceable clause surface closed in full.

| `entryRange_mulVec_le_of_pos_entries` | theorem | **the Doeblin/Dobrushin contraction**: if every entry of the row-stochastic `Q` is `≥ δ`, then `range (Q *ᵥ y) ≤ (1 - |V|δ) · range y` — the row split `δ` + remainder-of-mass `1-|V|δ` route; the retirement's engine, reusable for any stochastic action | — |
| `entryRange_pow_mul_le` | theorem | the iterated block contraction: `range (P^(m·q) *ᵥ y) ≤ (1-|V|δ)^q · range y` when `P^m` is entrywise `≥ δ` | — |

## Usage Patterns

- The irreducibility hypothesis is discharged by exhibiting one-step
  arcs: `Relation.ReflTransGen.single` on positive entries (see
  `Scaffold/QA/LinearAlgebra/PerronFrobenius_QA.lean`).
- The spectral-radius content is consumed through the domination clause
  at the roots of the complexified characteristic polynomial
  `Matrix.charpoly (A.map (algebraMap ℝ ℂ))`; there is no matrix
  spectral-radius definition in the pinned Mathlib.
- The calibration boundary: on imprimitive input (directed cycles,
  period ≥ 2) other eigenvalues share the maximal modulus — do not
  strengthen the statement with strict dominance. The QA witness
  `strict_dominance_refuted_QA` (`!![0,4;1,0]`, spectrum `{2, −2}`)
  keeps this falsifiable.
- The convergence boundary is the same fence in limit form: the
  directed 2-cycle is nonnegative, row-stochastic, *and* irreducible,
  yet its powers provably have no limit (`P2_no_limit_QA` in
  `SpectralGraph/DirectedMixing_QA.lean`, with every other
  `primitive_power_tendsto` hypothesis verified on the same fixture —
  exactly `hprim` isolated). Convergence statements need primitivity,
  never mere irreducibility.
- The degenerate-cardinality corners are audited and safe (2026-08-28,
  `proposals/audit-perron-frobenius-family-degenerate-corner.md`): at
  `Fintype.card V = 0` neither axiom is instantiable — `hex`
  (`perron_frobenius_hex_unsat_card_zero_QA`) and `hπsum`
  (`mass_one_unsat_card_zero_QA`, DirectedMixing_QA Section D) are
  each unsatisfiable there, proved unconditionally — so no `Nonempty
  V` guard is needed; at `Fin 1` both instantiate with conclusions
  pinned to hand data (`perron_frobenius_S1_QA`,
  `P1_singleton_axiom_QA`).
- **Every hypothesis clause of `perron_frobenius` is load-bearing**
  (2026-09-05, the adversarial fence audit
  `proposals/adversarial-fences-perron-frobenius-family.md`):
  tagged axiom-independent fences in `PerronFrobenius_QA.lean`'s
  `AdversarialFences` section refute the axiom-minus-one-clause shape
  at fixtures where the kept clauses are proven genuine — `hnn` at the
  negative-diagonal irreducible `!![-1,2;2,-1]]` (the eigen conjuncts
  stay satisfiable in isolation at `r = 1`, so the kill route is
  genuinely the domination clause: the pinned complex root `−3` forces
  `3 ≤ 1`), `hirr` at the reducible nilpotent edge `!![0,1;0,0]]`
  (the stranded vertex's zero row forces `r x₁ = 0` against `r > 0`,
  `x₁ > 0`), and `hex` at the one-vertex zero matrix `!![0]]`
  (nonnegativity and irreducibility genuine, the module's own named
  corner now proved rather than warned); plus the `IsIrreducible`
  positive-arcs definitional witness `!![0,-2;-2,0]]` (negativity
  creates no arcs).

## Named Consumers

- Irreducible-directed-graph stationary distributions — **delivered
  2026-08-24** (`GraphTheory.IrreducibleStationary`).
- PageRank-style centrality with an existence proof — **delivered
  2026-08-24** (`GraphTheory.PageRank`).
- The PageRank power iteration / directed mixing — **delivered
  2026-08-24** (`GraphTheory.DirectedMixing`, the first
  `primitive_power_tendsto` consumer; **hard crust since the
  2026-09-02 retirement** of that admission by the Doeblin/Dobrushin
  contraction route; geometric *rates* remain a
  future admission gated on a named consumer).

## See Also

- [Spectral Graph Theory map](spectral_graph.md) for the directed
  operators this serves (`GraphTheory.Directed`)
- [Sources Index](../sources/) for detailed bibliographic information
