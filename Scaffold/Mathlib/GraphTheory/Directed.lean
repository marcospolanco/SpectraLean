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
# Directed and asymmetric graph operators: the degree layer

The foundational slice of the directed-graph axis (backlog item 8,
`proposals/directed-graph-operators.md` Step 1, delivered 2026-08-22
after that proposal's Step 0 record): the two directed degree functions
and their relation to the undirected shelf. Everything here is proved;
no axiom is admitted, no symmetry is assumed anywhere.

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

What is genuinely new here is the **in-degree** (the column sum), the
agreement theorems on the symmetric cone, and the directed handshaking
identity.

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
  `rfl` to `deg Aᵀ i`).

## Main statements

- `outDeg_eq_deg`, `inDeg_eq_deg_transpose`: the two `rfl` identifications
  with the shelf's degree (the out-degree *is* `deg`; the in-degree is
  `deg` of the transpose);
- `inDeg_eq_outDeg_of_isSymm`, `inDeg_eq_deg_of_isSymm`: agreement on
  the symmetric cone — on an undirected graph the two directed degrees
  coincide with the shelf's degree (the first brick of the proposal's
  Step 3 acceptance bar);
- `sum_outDeg_eq_sum_inDeg`: directed handshaking — the total
  out-weight equals the total in-weight (by `Finset.sum_comm`; no
  nonnegativity or symmetry needed).

Junk-value discipline: both degree functions are total; on matrices
with negative entries they are simply signed sums, and no theorem here
consumes a sign hypothesis.
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

end SpectralGraphTheory
