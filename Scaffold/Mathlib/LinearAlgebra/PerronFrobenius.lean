import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Complex.Basic

/-!
# Perron–Frobenius for irreducible nonnegative matrices

The second spectral toolkit. Everything the shelf has built for graph
walks — `RandomWalk`, `Normalized`, `Stationary`, `Mixing` — reaches
directed input only through the directed axis' one symmetric operator
(`directedNormalizedLaplacian`, `GraphTheory.Directed`), whose QA
calibration witness shows the undirected positivity layer does not
transfer: on genuinely directed input there is no symmetric operator to
restrict to, and the symmetric `evals`/`eigvecOf` toolkit does not
apply. Perron–Frobenius is the nonnegative-matrix theory that replaces
it, and it is absent from the pinned Mathlib (the only `Perron` hits in
the pin are unrelated `BoxIntegral` files; see
`docs/8_MATHLIB_COVERAGE_MAP.md`). This module admits it at the
irreducible-case qualification level, exactly as scoped by
`proposals/admit-perron-frobenius.md`.

## The statement and its calibration

The admitted statement deliberately claims **no strict eigenvalue
dominance**. For an irreducible but imprimitive matrix — the simplest
example is a directed cycle's adjacency matrix — the eigenvalues of
maximum modulus form the full set of `h`-th roots of `r` (times `r`),
where `h` is the period; strict dominance of `r` over all other
eigenvalues holds only under the additional hypothesis of primitivity
(irreducible plus aperiodic). Folding that stronger clause in would make
the axiom false on the directed 2-cycle, whose spectrum is `{r, −r}`;
this is exactly the class of understated qualification this repository
has been burned by twice (`old_cheeger_lower_bound_refuted_QA`, the
pre-repair `lambda2_variational`). The QA centerpiece
`Scaffold.LinearAlgebra.QA.strict_dominance_refuted_QA` exhibits the
asymmetric directed 2-cycle `!![0,4;1,0]` — Perron root `2`, second
eigenvalue `−2` of *equal* modulus — precisely so a future reader cannot
mistake the admitted statement for the stronger primitive case.

What *is* claimed, per bullet of the proposal (mirroring the source
theorem's enumerated conclusions):

1. the spectral radius `r` is a **positive real eigenvalue** — encoded
   as `0 < r` together with a strictly positive eigenvector
   `A *ᵥ x = r • x` and the complex-spectrum domination clause below
   (these three conjuncts say exactly `r = ρ(A) ∈ spectrum(A)`);
2. `r` is **simple** — algebraic multiplicity one, stated as
   `rootMultiplicity r A.charpoly = 1` over `ℝ` (multiplicity of a real
   root is invariant under the `ℝ → ℂ` coefficient extension);
3. the eigenvector is **strictly positive and unique up to positive
   scalars** among nonnegative eigenvectors — every nonzero nonnegative
   eigenvector (for *any* eigenvalue) is a positive multiple of `x`;
4. `r` is the **only eigenvalue with a nonnegative eigenvector** —
   stated explicitly even though it is one derivation away from bullet 3,
   so each bullet of the source maps to a visible conjunct;
5. the **domination** clause: every root `z` of the complexified
   characteristic polynomial satisfies `|z| ≤ r`. There is no
   `Matrix.spectralRadius` in the pinned Mathlib (the `spectralRadius`
   hits there are operator-theory/C*-algebra files, the thread the
   resolvent program already found structurally inapplicable to real
   matrices), so the spectral-radius content is encoded directly through
   the complex roots.

## Statement differences from the source

- The source theorem is stated at matrix size `n ≥ 2`, where
  irreducibility already forces a positive entry in every row. This
  statement is over an arbitrary `Fintype V`, so the degenerate cases
  H&J's convention excludes are guarded by the explicit hypothesis
  `hex : ∃ i j, 0 < A i j` (implied by `hirr` whenever `2 ≤ card V`;
  exactly the missing strength at `card V ≤ 1`, where the vacuously
  irreducible 1×1 zero matrix and the empty type would otherwise falsify
  `0 < r`).
- Irreducibility is stated combinatorially (strong connectivity through
  positive-weight directed arcs) rather than through permutation
  similarity to a block-triangular form; the two are classically
  equivalent for nonnegative matrices.

## Consumers (named, not delivered here)

Irreducible-directed-graph stationary distributions (existence and
uniqueness of a positive stationary distribution for the row-normalized
walk) and PageRank-style centrality. Per the proposal's one-step
discipline these are separate follow-on proof obligations, not
corollaries of this admission.

Source:
- Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., Cambridge
  University Press, 2013, Theorem 8.4.4 (Perron–Frobenius theorem for
  irreducible nonnegative matrices). Section-level locator is recorded;
  the page-level locator is pending the same physical-copy review as
  the other Horn–Johnson rows.
- Original results: O. Perron, *Zur Theorie der Matrices*, Math. Ann.
  64 (1907); G. Frobenius, *Über Matrizen aus nicht negativen
  Elementen*, Sitzungsber. Königl. Preuss. Akad. Wiss. (1912).

QA: exercised by `Scaffold.LinearAlgebra.QA.perron_frobenius_P_QA` and
`Scaffold.LinearAlgebra.QA.perron_frobenius_D_QA` (the axiom instantiated
on two asymmetric irreducible fixtures, the Perron root derived to be
exactly the hand-computed value in both), by
`Scaffold.LinearAlgebra.QA.strict_dominance_refuted_QA` (the mandated
imprimitive-cycle negative witness: the strengthening is refuted while
the axiom's own conclusion stays satisfiable on the same fixture), and
by the charpoly/rootMultiplicity/complex-roots pins
(`P_charpoly_QA`, `P_rootMultiplicity_QA`,
`P_charpoly_complex_roots_QA`, `D_charpoly_complex_roots_QA`) in
`Scaffold/QA/LinearAlgebra/PerronFrobenius_QA.lean`.
-/

open scoped Matrix

namespace Matrix

variable {V : Type}

/-- Combinatorial irreducibility of a real square matrix: every index
reaches every other through positive-weight directed arcs, i.e. the
support digraph is strongly connected. This is the directed analogue of
the `supportGraph`/`SimpleGraph.Connected` pattern used for the
undirected kernel characterization, and the hypothesis under which
Perron–Frobenius is admitted. It carries no `Fintype` assumption; on a
type with at most one element it holds vacuously or by reflexivity, which
is why `perron_frobenius` carries the explicit `hex` guard. -/
def IsIrreducible (A : Matrix V V ℝ) : Prop :=
  ∀ i j, Relation.ReflTransGen (fun a b => 0 < A a b) i j

end Matrix

namespace Scaffold.LinearAlgebra

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Perron–Frobenius for irreducible nonnegative matrices** (admitted
axiom). For a nonnegative irreducible matrix with at least one positive
entry, there are a Perron root `r` and a Perron vector `x` such that:

- `0 < r` and `x i > 0` for every `i`, with `A *ᵥ x = r • x` — `r` is a
  positive real eigenvalue with a strictly positive eigenvector;
- `rootMultiplicity r A.charpoly = 1` — the eigenvalue is simple;
- every nonzero nonnegative eigenvector of `A`, whatever its eigenvalue,
  is a positive scalar multiple of `x`, and its eigenvalue is `r` — no
  other eigenvalue admits a nonnegative eigenvector;
- every root `z` of the complexified characteristic polynomial has
  `|z| ≤ r` — together with the first bullet this says `r` is the
  spectral radius and it is an eigenvalue.

No strict-dominance clause: for imprimitive matrices (directed cycles)
there are other eigenvalues of modulus exactly `r`; see the module
documentation and the calibration witness
`Scaffold.LinearAlgebra.QA.strict_dominance_refuted_QA`.

Source:
- Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., Cambridge
  University Press, 2013, Theorem 8.4.4.

Statement differences: see the module documentation (`hex` guard over
arbitrary `Fintype V`; combinatorial irreducibility; the spectral radius
encoded through complex charpoly roots since the pinned Mathlib has no
matrix spectral radius).

QA: exercised by
`Scaffold.LinearAlgebra.QA.perron_frobenius_P_QA`,
`Scaffold.LinearAlgebra.QA.perron_frobenius_D_QA`,
`Scaffold.LinearAlgebra.QA.strict_dominance_refuted_QA`, and the
charpoly pins in `Scaffold/QA/LinearAlgebra/PerronFrobenius_QA.lean`. -/
axiom perron_frobenius (A : Matrix V V ℝ)
    (hnn : ∀ i j, 0 ≤ A i j) (hirr : A.IsIrreducible)
    (hex : ∃ i j, 0 < A i j) :
    ∃ r : ℝ, ∃ x : V → ℝ,
      0 < r ∧
      (∀ i, 0 < x i) ∧
      A *ᵥ x = r • x ∧
      Polynomial.rootMultiplicity r A.charpoly = 1 ∧
      (∀ μ : ℝ, ∀ y : V → ℝ, (∀ i, 0 ≤ y i) → y ≠ 0 → A *ᵥ y = μ • y → μ = r) ∧
      (∀ μ : ℝ, ∀ y : V → ℝ, (∀ i, 0 ≤ y i) → y ≠ 0 → A *ᵥ y = μ • y →
          ∃ c : ℝ, 0 < c ∧ y = c • x) ∧
      (∀ z : ℂ, z ∈ (Matrix.charpoly (A.map (algebraMap ℝ ℂ))).roots →
          Complex.abs z ≤ r)
