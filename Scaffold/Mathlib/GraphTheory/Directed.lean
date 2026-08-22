/-
Copyright 2024 Scaffold Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Scaffold.Mathlib.GraphTheory.Normalized

/-!
# Directed and asymmetric graph operators

The foundational slice of the directed-graph axis (backlog item 8,
`proposals/directed-graph-operators.md`): the two directed degree
functions, their relation to the undirected shelf (Step 1, delivered
2026-08-22), and the **directed normalized Laplacian** at the
out-degree-symmetrized convention (Step 2 + the Step-3 agreement brick,
delivered 2026-08-22, completing the proposal's Lean content). Everything
here is proved; no axiom is admitted, and the only hypothesis anywhere
is the one each theorem names (`A.IsSymm` on the symmetric cone,
positive out-degrees where normalization consumes them).

## The Step 0 discovery this module is shaped by

The undirected shelf already carries the *out*-degree half of the
directed story, hypothesis-free:

- `deg A i = ∑ j, A i j` is the row sum — the out-degree of `i` for a
  directed weight matrix;
- `walkTransitionMatrix A = D⁻¹ A` and `walkLaplacian A = I − D⁻¹ A`
  (`Scaffold.Mathlib.GraphTheory.Normalized`) are defined with **no
  symmetry hypothesis**, and their load-bearing interface lemmas
  (`walkTransitionMatrix_row_sum`, `walkTransitionMatrix_apply`,
  `walkLaplacian_mulVec_one_eq_zero`) hold for any matrix with positive
  row sums — so they apply verbatim to asymmetric, genuinely directed
  input. The QA file certifies exactly this on a nonsymmetric fixture.

What is genuinely new in the degree layer is the **in-degree** (the
column sum), the agreement theorems on the symmetric cone, and the
directed handshaking identity.

## The directed normalized Laplacian (Step 2, the convention decision (b))

`directedNormalizedLaplacian A = I − ½(SAS + SAᵀS)` with
`S = D_out^{-1/2}` (the shelf's `degreeInvSqrt` — the out-degree square
root, since `deg` *is* the out-degree). Properties delivered:

- **symmetric by construction, for every `A`, no hypothesis** — the two
  halves are transposes of each other, so the sum is symmetric even
  when `A` is not. This is the directed axis' one symmetric operator;
- **total** (defined for any matrix; the normalization is honest
  exactly where out-degrees are positive, as in the undirected shelf);
- **agreement on the symmetric cone**: `= normalizedLaplacian A` when
  `A.IsSymm` — the proposal's Step-3 acceptance bar (both halves
  coincide there);
- **the square-root-free conjugate**
  `√D · L_dir · √D = degreeMatrix A − ½(A + Aᵀ)`: the underlying
  symmetric-combinatorial object is the *symmetrized adjacency*
  `½(A + Aᵀ)` with the out-degree matrix — the exact analogue of
  `degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt`.

**Calibration (the honest boundary):** symmetric does *not* mean PSD
here. On directed input `L_dir` can have a negative eigenvalue — QA
exhibits `A = !![0,4;1,0]` where the quadratic form at `(1,1)` is
`−1/2 < 0` (the symmetrized adjacency can overweight against the
out-degrees when in- and out-degrees differ). The positivity layer of
the symmetric toolkit (PSD-ness, variational eigenvalue bounds) therefore
does **not** transfer; a directed spectral theory needs Perron–Frobenius
(`proposals/admit-perron-frobenius.md`), exactly as the proposal's
Calibration section records. The convention is deliberately *not*
Chung's Perron-vector form — see the Step-0 record in the proposal.

## Carrier convention (Step 0 decision (a))

No new type: statements are on `Matrix V V ℝ` directly (the same
carrier as the `WAdj` abbreviation), with nonnegativity and
degree-positivity hypotheses attached at call sites exactly where
consumed, mirroring the shelf's convention. There is no type-level
symmetry to lose: on the undirected shelf every symmetry use is an
explicit `A.IsSymm` hypothesis.

## Main definitions

- `outDeg A i`: the out-degree `∑ j, A i j` (definitionally `deg A i`);
- `inDeg A i`: the in-degree `∑ j, A j i` (the column sum; equal by
  `rfl` to `deg Aᵀ i`);
- `directedNormalizedLaplacian A`:
  `I − ½(SAS + SAᵀS)`, `S = degreeInvSqrt A` (out-degree normalization).

## Main statements

- `outDeg_eq_deg`, `inDeg_eq_deg_transpose`: the two `rfl` identifications
  with the shelf's degree (the out-degree *is* `deg`; the in-degree is
  `deg` of the transpose);
- `inDeg_eq_outDeg_of_isSymm`, `inDeg_eq_deg_of_isSymm`: agreement on
  the symmetric cone — on an undirected graph the two directed degrees
  coincide with the shelf's degree;
- `sum_outDeg_eq_sum_inDeg`: directed handshaking — the total
  out-weight equals the total in-weight (by `Finset.sum_comm`; no
  nonnegativity or symmetry needed);
- `directedNormalizedLaplacian_apply`: the entry form
  `δ_ij − ½·(√d_i)⁻¹(A_ij + A_ji)(√d_j)⁻¹`;
- `directedNormalizedLaplacian_isSymm`: symmetry, hypothesis-free;
- `directedNormalizedLaplacian_eq_normalizedLaplacian`: the Step-3
  acceptance bar — on the symmetric cone the directed operator *is*
  the shelf's `normalizedLaplacian`;
- `degreeSqrt_mul_directedNormalizedLaplacian_mul_degreeSqrt`: the
  square-root-free conjugate `√D L_dir √D = D − ½(A + Aᵀ)`.

Junk-value discipline: both degree functions are total; on matrices
with negative entries they are simply signed sums, and no theorem here
consumes a sign hypothesis. The directed normalized Laplacian is
likewise total (noncomputable through `Real.sqrt`/`ℝ` inversion, as the
shelf's normalizations are); on zero out-degrees its entries carry the
same junk reciprocals the shelf's do, ruled out by the positivity
hypothesis wherever consumed.
-/

namespace SpectralGraphTheory

open Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Directed degrees
-/

/-- The out-degree of vertex `i` in a directed weight matrix: the `i`-th
row sum `∑ j, A i j`. Definitionally the shelf's `deg` (see
`outDeg_eq_deg`); named separately so directed statements read at their
intended generality. -/
def outDeg (A : Matrix V V ℝ) (i : V) : ℝ :=
  ∑ j, A i j

/-- The in-degree of vertex `i` in a directed weight matrix: the `i`-th
column sum `∑ j, A j i` — the genuinely new directed quantity (the row
sum was already `deg`). Definitionally `deg` of the transpose (see
`inDeg_eq_deg_transpose`). -/
def inDeg (A : Matrix V V ℝ) (i : V) : ℝ :=
  ∑ j, A j i

omit [DecidableEq V] in
/-- The out-degree *is* the shelf's degree: `deg` was the row sum all
along, so every existing `deg`-indexed theorem (degree matrices,
positive-degree interfaces) applies to the directed out-degree verbatim.
Definitional (`rfl`). -/
theorem outDeg_eq_deg (A : Matrix V V ℝ) (i : V) :
    outDeg A i = deg A i :=
  rfl

omit [DecidableEq V] in
/-- The in-degree is the degree of the transpose: reading the same
matrix with every arc reversed exchanges the two degree functions.
Definitional (`rfl`). -/
theorem inDeg_eq_deg_transpose (A : Matrix V V ℝ) (i : V) :
    inDeg A i = deg Aᵀ i :=
  rfl

omit [DecidableEq V] in
/-- Agreement on the symmetric cone: an undirected weight matrix has
`inDeg = outDeg` at every vertex. This is the degree brick of the
proposal's Step 3 acceptance bar (each directed construction reduces to
its undirected counterpart under `A.IsSymm`). -/
theorem inDeg_eq_outDeg_of_isSymm (A : Matrix V V ℝ)
    (hA : A.IsSymm) (i : V) :
    inDeg A i = outDeg A i := by
  simp only [inDeg, outDeg]
  exact Finset.sum_congr rfl fun j _ => hA.apply i j

omit [DecidableEq V] in
/-- Agreement with the shelf: on a symmetric matrix the in-degree is
the shelf's `deg` (composed from `inDeg_eq_outDeg_of_isSymm` and the
definitional `outDeg_eq_deg`). -/
theorem inDeg_eq_deg_of_isSymm (A : Matrix V V ℝ)
    (hA : A.IsSymm) (i : V) :
    inDeg A i = deg A i :=
  (inDeg_eq_outDeg_of_isSymm A hA i).trans (outDeg_eq_deg A i)

omit [DecidableEq V] in
/-- Directed handshaking: the total out-weight equals the total
in-weight, `∑ i, outDeg A i = ∑ i, inDeg A i`, with no nonnegativity or
symmetry hypothesis — each directed edge contributes its weight once to
each side. By `Finset.sum_comm` on the double sum. -/
theorem sum_outDeg_eq_sum_inDeg (A : Matrix V V ℝ) :
    ∑ i, outDeg A i = ∑ i, inDeg A i := by
  simp only [outDeg, inDeg]
  exact Finset.sum_comm

/-!
## The directed normalized Laplacian (Step 2)

The convention is the Step-0 decision (b): out-degree-symmetrized,
`L_dir := I − ½(SAS + SAᵀS)` with `S = D_out^{-1/2}` — symmetric by
construction, *not* Chung's Perron-vector form (which would make an
admitted axiom a prerequisite of a definition; see the proposal's
Step 0 record for the recorded decoupling from
`admit-perron-frobenius.md`).
-/

/-- The directed normalized Laplacian at the out-degree-symmetrized
convention (Step-0 decision (b)):
`L_dir := I − ½(SAS + SAᵀS)` where `S = degreeInvSqrt A` is the
out-degree reciprocal-square-root matrix (`deg` is the out-degree, per
`outDeg_eq_deg`). Symmetric by construction for *every* `A`
(`directedNormalizedLaplacian_isSymm`, no hypothesis); on the symmetric
cone it is exactly the shelf's `normalizedLaplacian`
(`directedNormalizedLaplacian_eq_normalizedLaplacian`). Total by
definition; the normalization is honest wherever out-degrees are
positive, exactly as in the undirected shelf. Noncomputable because
`Real.sqrt` and `ℝ` inversion are.

Not PSD in general on directed input — see the module docstring's
calibration note; QA exhibits the 2×2 refutation. -/
noncomputable def directedNormalizedLaplacian (A : Matrix V V ℝ) :
    Matrix V V ℝ :=
  1 - (1 / 2 : ℝ) • (degreeInvSqrt A * A * degreeInvSqrt A
    + degreeInvSqrt A * Aᵀ * degreeInvSqrt A)

/-- Entry form: the `i j` entry is
`δ_ij − ½·(√d_i)⁻¹(A_ij + A_ji)(√d_j)⁻¹` with `d` the out-degree — the
second term is the same in both directions of the arc, which is exactly
the symmetrization. The entry-level interface QA computes through. -/
theorem directedNormalizedLaplacian_apply (A : Matrix V V ℝ) (i j : V) :
    directedNormalizedLaplacian A i j =
      (if i = j then (1 : ℝ) else 0)
        - (1 / 2 : ℝ) * (Real.sqrt (deg A i))⁻¹ * (A i j + A j i)
          * (Real.sqrt (deg A j))⁻¹ := by
  simp only [directedNormalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, degreeInvSqrt,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply]
  split_ifs <;> ring

/-- **Symmetric by construction, for every `A`, no hypothesis.** The two
halves of the defining sum are transposes of each other
(`(SAS)ᵀ = SAᵀS`, `S` diagonal), so the sum is symmetric even when `A`
is not — this is the directed axis' one symmetric operator, the object
that makes quadratic-form statements available to directed input at
all. Contrast `walkTransitionMatrix`/`walkLaplacian`, which are
provably *not* symmetric on directed input (the QA negative witnesses
of Step 1). -/
theorem directedNormalizedLaplacian_isSymm (A : Matrix V V ℝ) :
    (directedNormalizedLaplacian A).IsSymm := by
  have hS : (degreeInvSqrt A)ᵀ = degreeInvSqrt A :=
    Matrix.diagonal_transpose _
  show (directedNormalizedLaplacian A)ᵀ = directedNormalizedLaplacian A
  rw [directedNormalizedLaplacian, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    hS, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [add_comm (degreeInvSqrt A * (A * degreeInvSqrt A))]

/-- **The Step-3 acceptance bar:** on the symmetric cone the directed
normalized Laplacian *is* the shelf's `normalizedLaplacian` — the
transpose half of the defining sum coincides with the first half
(`Aᵀ = A`), and `½ • (M + M) = M`. Together with the Step-1 degree
agreements (`inDeg_eq_outDeg_of_isSymm`, `inDeg_eq_deg_of_isSymm`) and
the Step-0 record that the directed axis uses the *same* walk-operator
definitions, this completes the proposal's agreement obligation: every
directed construction reduces to its undirected counterpart when
`A.IsSymm`. -/
theorem directedNormalizedLaplacian_eq_normalizedLaplacian
    (A : Matrix V V ℝ) (hA : A.IsSymm) :
    directedNormalizedLaplacian A = normalizedLaplacian A := by
  have key : ∀ M : Matrix V V ℝ, (1 / 2 : ℝ) • (M + M) = M := by
    intro M
    rw [smul_add, ← add_smul]
    norm_num
  rw [directedNormalizedLaplacian, normalizedLaplacian, hA, key]

/-- The square-root-free conjugate: `√D · L_dir · √D = D − ½(A + Aᵀ)`,
the out-degree matrix minus the *symmetrized adjacency*. The exact
analogue of `degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt`
(the square roots cancel, `√D (1/√D) = 1`): every quadratic-form
statement about `L_dir` transfers to this square-root-free-shaped
symmetric pair, whose combinatorial object is the undirected multigraph
`½(A + Aᵀ)` with out-degree normalization. -/
theorem degreeSqrt_mul_directedNormalizedLaplacian_mul_degreeSqrt
    (A : Matrix V V ℝ) (hd : ∀ i, 0 < deg A i) :
    degreeSqrt A * directedNormalizedLaplacian A * degreeSqrt A
      = degreeMatrix A - (1 / 2 : ℝ) • (A + Aᵀ) := by
  have hST : degreeSqrt A * degreeInvSqrt A = 1 :=
    degreeSqrt_mul_degreeInvSqrt A hd
  have hTS : degreeInvSqrt A * degreeSqrt A = 1 :=
    degreeInvSqrt_mul_degreeSqrt A hd
  have hkey : ∀ M : Matrix V V ℝ,
      degreeSqrt A * (degreeInvSqrt A * M * degreeInvSqrt A)
        * degreeSqrt A = M := by
    intro M
    simp only [← Matrix.mul_assoc]
    rw [hST, Matrix.one_mul, Matrix.mul_assoc, hTS, Matrix.mul_one]
  rw [smul_add, directedNormalizedLaplacian, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, smul_add, hkey, hkey,
    ← degreeSqrt_mul_degreeSqrt A (fun i => le_of_lt (hd i))]

end SpectralGraphTheory
