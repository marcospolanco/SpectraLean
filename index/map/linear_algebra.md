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
positivity layer does not transfer to directed input.

## Declarations

| Declaration | Kind | Statement | Source |
| --- | --- | --- | --- |
| `Matrix.IsIrreducible` | def | every index reaches every other through positive-weight directed arcs (`Relation.ReflTransGen`) | combinatorial form of H&J irreducibility |
| `perron_frobenius` | **axiom** | for nonnegative irreducible `A` with a positive entry: a Perron root `r > 0` with a strictly positive eigenvector, `rootMultiplicity r A.charpoly = 1`, every nonzero nonnegative eigenvector is a positive multiple of the Perron vector (and its eigenvalue is `r`), and every complex charpoly root has modulus `≤ r`. **No strict-dominance clause** — that needs primitivity | [Horn & Johnson](../sources/horn_johnson_matrix_analysis.md), Theorem 8.4.4 |

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

## Named Consumers (follow-ons, not delivered)

- Irreducible-directed-graph stationary distributions (existence and
  uniqueness of a positive stationary distribution for the row-normalized
  walk).
- PageRank-style centrality with an existence proof.

## See Also

- [Spectral Graph Theory map](spectral_graph.md) for the directed
  operators this serves (`GraphTheory.Directed`)
- [Sources Index](../sources/) for detailed bibliographic information
