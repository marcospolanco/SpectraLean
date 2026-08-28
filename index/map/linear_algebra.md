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
| `primitive_power_tendsto` | **axiom** | powers of a primitive row-stochastic matrix converge entrywise to the rank-one stationary projector: `(P ^ t) *ᵥ x → (π ⬝ᵥ x) • 1` at any nonnegative mass-one stationary `π ᵥ* P = π` (given-π form). **The first convergence axiom** — the row-stochastic specialization of the primitive Perron–Frobenius limit at root `1`; no rate clause (see the module documentation) | [Horn & Johnson](../sources/horn_johnson_matrix_analysis.md), §8.5 (stochastic form cf. Levin–Peres–Wilmer Thm 4.9) |
| `isPrimitive_of_pos` | theorem | a strictly positive matrix is primitive at `k = 1` | — |
| `reachable_of_pow_pos` | theorem | an entry of a positive power is a sum over walks: positivity yields a positive-weight directed path (`ReflTransGen`) | — |
| `isIrreducible_of_isPrimitive` | theorem | primitivity implies strong connectivity — the connective tissue to the `perron_frobenius` hypothesis form | — |
| `pow_mulVec_one` | theorem | powers of a row-stochastic matrix fix the constant-one vector | — |
| `primitive_entrywise_tendsto` | theorem | conditional on `primitive_power_tendsto`: every column of `Pᵗ` converges to `π` (at the basis vector, through `Matrix.mulVec_single`) | — |
| `primitive_vecMul_tendsto` | theorem | conditional: `ν ᵥ* Pᵗ → π` for every start summing to one (finite-sum interchange; the pin has no tendsto-sum lemma) | — |

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

## Named Consumers

- Irreducible-directed-graph stationary distributions — **delivered
  2026-08-24** (`GraphTheory.IrreducibleStationary`).
- PageRank-style centrality with an existence proof — **delivered
  2026-08-24** (`GraphTheory.PageRank`).
- The PageRank power iteration / directed mixing — **delivered
  2026-08-24** (`GraphTheory.DirectedMixing`, the first
  `primitive_power_tendsto` consumer; geometric *rates* remain a
  future admission gated on a named consumer).

## See Also

- [Spectral Graph Theory map](spectral_graph.md) for the directed
  operators this serves (`GraphTheory.Directed`)
- [Sources Index](../sources/) for detailed bibliographic information
