/-
  Spectral.lean

  Purpose
  -------
  The spectral graph theory center of Scaffold: real definitions for
  weighted adjacency matrices, degrees, the combinatorial Laplacian,
  quadratic/Rayleigh forms, a canonically sorted real spectrum,
  cut/volume/conductance quantities, and event-driven adjacency updates,
  together with proved structural theorems. No statement is admitted in
  this module: the variational characterization of the algebraic
  connectivity λ₂ was admitted until 2026-08-18 and is proved here
  (`lambda2_variational`), and Cauchy interlacing was admitted until
  2026-08-18 and is proved here
  (`eigen_interlacing_principal_submatrix`). It also provides the
  `supportGraph` adapter from weighted adjacency matrices to Mathlib's
  `SimpleGraph`, through which the Laplacian kernel is characterized on
  connected graphs: the kernel is exactly the constants.

  Everything definable and provable here is defined and proved; this
  module carries no `axiom` declarations.

  Related modules: Cheeger-type inequalities live in
  `Scaffold.Mathlib.GraphTheory.Cheeger`, event-driven dynamics in
  `Scaffold.Mathlib.GraphTheory.Dynamics`, and Weyl / Davis–Kahan
  perturbation bounds in
  `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl` and
  `.../DavisKahan`.

  Representation convention: a weighted graph on `V` is an arbitrary
  `A : Matrix V V ℝ`; symmetry and nonnegativity are explicit hypotheses
  of every statement that needs them, never assumptions of the type. This
  mirrors Mathlib's `Matrix.IsSymm` style and keeps adapters to
  `SimpleGraph.adjMatrix` local to consumers.

  Historical note: earlier revisions of this file also sketched random
  walks, expanders, spanning-tree and heat-kernel sections with
  `sorry`-proved statements referencing undefined identifiers; they were
  never elaborable and were removed rather than repaired. Git history
  preserves them as backlog.

  Source (classical background):
  - Chung, F. R. K., "Spectral Graph Theory", CBMS 92, AMS, 1997.
  - Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., CUP, 2013.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Algebra.Module.Submodule.Range

open scoped BigOperators Matrix
open InnerProductSpace

namespace SpectralGraphTheory

/-!
## 0. Core objects

Finite vertex type, real-weighted adjacency matrix.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Weighted adjacency matrix type abbreviation. -/
abbrev WAdj := Matrix V V ℝ

/-- Degree of vertex `i` in adjacency matrix `A`: the `i`-th row sum. -/
def deg (A : WAdj (V := V)) (i : V) : ℝ :=
  ∑ j, A i j

/-- Diagonal degree matrix `D` for adjacency matrix `A`. -/
def degreeMatrix (A : WAdj (V := V)) : Matrix V V ℝ :=
  fun i j => if h : i = j then deg A i else 0

/-- (Combinatorial) Laplacian: `L = D - A`. -/
def laplacian (A : WAdj (V := V)) : Matrix V V ℝ :=
  degreeMatrix A - A

/-- Quadratic form of a matrix `M` at vector `x`: `xᵀ M x`. -/
def quadForm (M : Matrix V V ℝ) (x : V → ℝ) : ℝ :=
  Matrix.dotProduct x (M.mulVec x)

/-- Rayleigh quotient `R_L(x) = (xᵀ L x) / (xᵀ x)` for `x ≠ 0`, with the
junk value `0` at `x = 0` so the function is total. -/
noncomputable def rayleigh (L : Matrix V V ℝ) (x : V → ℝ) : ℝ :=
  if x = 0 then 0 else quadForm L x / Matrix.dotProduct x x

/-- The all-ones vector. -/
def onesVec : V → ℝ :=
  fun _ => 1

/-!
## 1. Basic structural facts (proved)
-/

/-- The degree matrix is diagonal away from the diagonal. -/
theorem degreeMatrix_off_diagonal (A : WAdj (V := V)) {i j : V} (h : i ≠ j) :
    degreeMatrix A i j = 0 := by
  simp [degreeMatrix, h]

/-- The degree matrix carries the degree on the diagonal. -/
theorem degreeMatrix_diagonal (A : WAdj (V := V)) (i : V) :
    degreeMatrix A i i = deg A i := by
  simp [degreeMatrix]

/-- Diagonal entries of the degree matrix are row sums, hence nonnegative
for nonnegative weights. -/
theorem degreeMatrix_diagonal_nonneg (A : WAdj (V := V))
    (hnonneg : ∀ i j, 0 ≤ A i j) (i : V) :
    0 ≤ degreeMatrix A i i := by
  rw [degreeMatrix_diagonal]
  exact Finset.sum_nonneg fun j _ => hnonneg i j

/-- The degree matrix is symmetric. -/
theorem degreeMatrix_symmetric (A : WAdj (V := V)) :
    Matrix.IsSymm (degreeMatrix A) := by
  refine Matrix.IsSymm.ext fun i j => ?_
  by_cases h : i = j
  · subst h
    rfl
  · rw [degreeMatrix_off_diagonal A (Ne.symm h), degreeMatrix_off_diagonal A h]

/-- The Laplacian of a symmetric weighted adjacency matrix is symmetric. -/
theorem laplacian_symmetric (A : WAdj (V := V)) (hA : Matrix.IsSymm A) :
    Matrix.IsSymm (laplacian A) :=
  (degreeMatrix_symmetric A).sub hA

/-- The degree of `i` is the row sum, so every Laplacian row sums to zero;
the all-ones vector is in the kernel of every Laplacian. No symmetry is
required: this is the row-sum identity. -/
theorem laplacian_ones_in_kernel (A : WAdj (V := V)) :
    (laplacian A).mulVec onesVec = 0 := by
  funext i
  have hrow : ∑ j, degreeMatrix A i j = deg A i := by
    simp only [degreeMatrix, eq_comm]
    simp
  simp only [laplacian, Matrix.sub_apply, Matrix.mulVec, Matrix.dotProduct,
    onesVec, mul_one, Finset.sum_sub_distrib]
  rw [hrow, deg]
  simp

/-!
## 2. Sorted spectrum of a symmetric matrix

Mathlib's spectral theorem provides eigenvalues
`Matrix.IsHermitian.eigenvalues : V → ℝ` in the order of an orthonormal
eigenbasis. We sort that multiset into canonical nondecreasing order so
that all downstream statements (λ₂, spectral gaps, interlacing, Weyl
bounds) share one spectrum API.
-/

section Spectrum

variable {M : Matrix V V ℝ}

/-- A real symmetric matrix is hermitian, bridging `Matrix.IsSymm` to the
spectral theorem API. -/
theorem isHermitian_of_isSymm (hM : M.IsSymm) :
    Matrix.IsHermitian M := by
  show Mᴴ = M
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hM.eq

private theorem length_sortedEvals (hM : M.IsSymm) :
    (Multiset.sort (fun a b => a ≤ b)
        ((Finset.univ : Finset V).val.map
          ((isHermitian_of_isSymm hM).eigenvalues))).length =
      Fintype.card V := by
  rw [Multiset.length_sort, Multiset.card_map]
  simp

/-- The eigenvalues of a real symmetric matrix in nondecreasing order,
with multiplicity, indexed by `Fin (Fintype.card V)`.

This is a real definition: the sort (over `ℝ`) of the eigenvalue multiset
produced by Mathlib's spectral theorem. Monotonicity in the index is
`evals_sorted`, proved from the sorting construction. -/
noncomputable def evals (hM : M.IsSymm) : Fin (Fintype.card V) → ℝ := fun i =>
  (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map
        ((isHermitian_of_isSymm hM).eigenvalues))).get
    ⟨i.1, by rw [length_sortedEvals hM]; exact i.isLt⟩

/-- The sorted spectrum is nondecreasing in the index, by construction. -/
theorem evals_sorted (hM : M.IsSymm) :
    Monotone (evals hM) := by
  intro i j hij
  have hsort : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map
        ((isHermitian_of_isSymm hM).eigenvalues))).Sorted (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  rcases lt_or_eq_of_le hij with h | h
  · exact hsort.rel_get_of_lt (by simpa [length_sortedEvals hM] using h)
  · subst h
    exact le_refl _

/-- Algebraic connectivity (Fiedler value): the second-smallest eigenvalue
of the Laplacian, `evals (laplacian A) 1`. The cardinality hypothesis is
explicit because the spectrum is indexed by `Fin (Fintype.card V)`. -/
noncomputable def lambda2 (A : WAdj (V := V)) (hA : A.IsSymm)
    (hcard : 2 ≤ Fintype.card V) : ℝ :=
  evals (laplacian_symmetric A hA) ⟨1, by omega⟩

/-- The second entry of the sorted spectrum of a symmetric matrix: the
"second-smallest eigenvalue" of the matrix *itself*, without wrapping it
in the combinatorial Laplacian. `lambda2` is this quantity for
`laplacian A` (`lambda2_eq_secondEval`); spectral statements about other
symmetric operators — normalized Laplacians in particular — must use
`secondEval` on the operator directly. -/
noncomputable def secondEval (M : Matrix V V ℝ) (hM : M.IsSymm)
    (hcard : 2 ≤ Fintype.card V) : ℝ :=
  evals hM ⟨1, by omega⟩

/-- `lambda2` is the second sorted eigenvalue of the combinatorial
Laplacian: the adjacency-facing `lambda2` API interoperates with the
matrix-facing `secondEval` API. -/
theorem lambda2_eq_secondEval (A : WAdj (V := V)) (hA : A.IsSymm)
    (hcard : 2 ≤ Fintype.card V) :
    lambda2 A hA hcard =
      secondEval (laplacian A) (laplacian_symmetric A hA) hcard := rfl

/-- The spectral gap at index `k`: the difference `λ_{k+1} - λ_k` of the
sorted spectrum. The index hypothesis makes `k+1` admissible. -/
noncomputable def spectralGap (M : Matrix V V ℝ) (hM : M.IsSymm)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V) : ℝ :=
  evals hM ⟨(k : ℕ) + 1, hk⟩ - evals hM ⟨k, by omega⟩

/-- The `i`-th eigenvector of a symmetric matrix, from the orthonormal
eigenbasis of the spectral theorem, as a plain function. -/
noncomputable def eigvecOf (M : Matrix V V ℝ) (hM : M.IsSymm) (i : V) : V → ℝ :=
  ((isHermitian_of_isSymm hM).eigenvectorBasis i : V → ℝ)

/-- The eigenvalue attached to the `i`-th eigenbasis vector (basis order,
not sorted). -/
noncomputable def eigvalOf (M : Matrix V V ℝ) (hM : M.IsSymm) (i : V) : ℝ :=
  (isHermitian_of_isSymm hM).eigenvalues i

/-- Every entry of the sorted spectrum is an eigenvalue of the
underlying eigenbasis listing: sorting a multiset permutes it, and each
`get` lands in it. This connects the sorted-spectrum API (`evals`) to
the eigenbasis API (`eigvalOf`). -/
theorem evals_mem_eigvalOf (hM : M.IsSymm) (k : Fin (Fintype.card V)) :
    ∃ i : V, evals hM k = eigvalOf M hM i := by
  have hlen : (k : ℕ) < (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map
        ((isHermitian_of_isSymm hM).eigenvalues))).length := by
    rw [Multiset.length_sort, Multiset.card_map]
    simpa using k.isLt
  have hmem : evals hM k ∈ Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map
        ((isHermitian_of_isSymm hM).eigenvalues)) :=
    List.get_mem _ (k : ℕ) hlen
  rw [Multiset.mem_sort] at hmem
  rcases Multiset.mem_map.1 hmem with ⟨i, _, hi⟩
  exact ⟨i, hi.symm⟩

/-- The last entry of the sorted spectrum dominates every eigenvalue of
the eigenbasis listing: sorting is nondecreasing and every listed
eigenvalue survives the sort, so each is bounded by the final entry.
This is the half of "the sorted spectrum and the eigenbasis listing
carry the same multiset" that top-eigenvalue bounds consume. The
cardinality hypothesis keeps the last index inhabited (the empty type
has no last index). -/
theorem eigvalOf_le_evals_last {M : Matrix V V ℝ} (hM : M.IsSymm)
    (hcard : 1 ≤ Fintype.card V) (i : V) :
    eigvalOf M hM i ≤ evals hM ⟨Fintype.card V - 1, by omega⟩ := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map
        ((isHermitian_of_isSymm hM).eigenvalues))).length =
      Fintype.card V := length_sortedEvals hM
  have hmem : eigvalOf M hM i ∈ Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map
        ((isHermitian_of_isSymm hM).eigenvalues)) := by
    rw [Multiset.mem_sort]
    exact Multiset.mem_map.2 ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨p, hp⟩ := List.mem_iff_get.1 hmem
  have hsort : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map
        ((isHermitian_of_isSymm hM).eigenvalues))).Sorted (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hlast : evals hM ⟨Fintype.card V - 1, by omega⟩ =
      (Multiset.sort (fun a b => a ≤ b)
        ((Finset.univ : Finset V).val.map
          ((isHermitian_of_isSymm hM).eigenvalues))).get
      ⟨Fintype.card V - 1, by rw [hlen]; omega⟩ := rfl
  rw [hlast, ← hp]
  have hpn : p.1 < Fintype.card V := by simpa [hlen] using p.isLt
  rcases Nat.lt_or_ge p.1 (Fintype.card V - 1) with hlt | heq
  · exact hsort.rel_get_of_lt (by simpa using hlt)
  · have hpe : p = ⟨Fintype.card V - 1, by rw [hlen]; omega⟩ :=
      Fin.ext (show p.1 = Fintype.card V - 1 by omega)
    rw [hpe]

/-- The first entry of the sorted spectrum is dominated by every
eigenvalue of the eigenbasis listing: sorting is nondecreasing and
every listed eigenvalue survives the sort, so the first entry bounds
each from below. The mirror of `eigvalOf_le_evals_last`; together they
say the sorted spectrum and the eigenbasis listing carry the same
extremes. Consumed by the operator-norm bridge
(`Analysis.OperatorTheory.Resolvent.l2OpNorm_le_of_abs_evals_le`).
The cardinality hypothesis keeps the first index inhabited. -/
theorem evals_first_le_eigvalOf {M : Matrix V V ℝ} (hM : M.IsSymm)
    (hcard : 1 ≤ Fintype.card V) (i : V) :
    evals hM ⟨0, by omega⟩ ≤ eigvalOf M hM i := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map
        ((isHermitian_of_isSymm hM).eigenvalues))).length =
      Fintype.card V := length_sortedEvals hM
  have hmem : eigvalOf M hM i ∈ Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map
        ((isHermitian_of_isSymm hM).eigenvalues)) := by
    rw [Multiset.mem_sort]
    exact Multiset.mem_map.2 ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨p, hp⟩ := List.mem_iff_get.1 hmem
  have hsort : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map
        ((isHermitian_of_isSymm hM).eigenvalues))).Sorted (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hfirst : evals hM ⟨0, by omega⟩ =
      (Multiset.sort (fun a b => a ≤ b)
        ((Finset.univ : Finset V).val.map
          ((isHermitian_of_isSymm hM).eigenvalues))).get
        ⟨0, by rw [hlen]; omega⟩ := rfl
  rw [hfirst, ← hp]
  have hpn : p.1 < Fintype.card V := by simpa [hlen] using p.isLt
  rcases Nat.eq_zero_or_pos p.1 with h0 | h0
  · have hpe : p = ⟨0, by rw [hlen]; omega⟩ :=
      Fin.ext (show p.1 = 0 by omega)
    rw [hpe]
  · exact hsort.rel_get_of_lt (by simpa [hlen] using h0)

/-- The orthogonal spectral projector onto the span of the eigenvectors
whose eigenvalues are at most `c`:
`P_c = ∑_{λᵢ ≤ c} vᵢ vᵢᵀ` over the orthonormal eigenbasis.

This is a real definition, replacing an unconditional `0` placeholder in
earlier revisions. It is symmetric by construction
(`spectralProjector_symmetric`); idempotence follows from orthonormality
of the eigenbasis and is consumed through the admitted perturbation
interfaces. -/
noncomputable def spectralProjector (M : Matrix V V ℝ) (hM : M.IsSymm) (c : ℝ) :
    Matrix V V ℝ :=
  Matrix.of fun a b =>
    ∑ i ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c),
      eigvecOf M hM i a * eigvecOf M hM i b

/-- Spectral projectors are symmetric by construction (each outer product
`vᵢvᵢᵀ` is symmetric). -/
theorem spectralProjector_symmetric (M : Matrix V V ℝ) (hM : M.IsSymm) (c : ℝ) :
    (spectralProjector M hM c).IsSymm := by
  refine Matrix.IsSymm.ext fun a b => ?_
  simp only [spectralProjector, Matrix.transpose_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The invariant-subspace projector onto the span of the eigenvectors of
the `k+1` smallest eigenvalues: the spectral projector at the threshold
`evals hM k`. When the gap `λ_{k+1} - λ_k` is positive this span is
exactly `(k+1)`-dimensional; with eigenvalue ties at the threshold the
projector includes the whole tied eigenspace. -/
noncomputable def initialProjector (M : Matrix V V ℝ) (hM : M.IsSymm)
    (k : Fin (Fintype.card V)) : Matrix V V ℝ :=
  spectralProjector M hM (evals hM k)

/-- `initialProjector` is symmetric. -/
theorem initialProjector_symmetric (M : Matrix V V ℝ) (hM : M.IsSymm)
    (k : Fin (Fintype.card V)) :
    (initialProjector M hM k).IsSymm :=
  spectralProjector_symmetric M hM _

/-- `initialProjector` transports along matrix equalities: the symmetry
proof enters only through propositions, so projectors of equal matrices
are equal by proof irrelevance. This is the interface needed to restate
perturbation conclusions (stated at `A + E`) at a rewritten matrix. -/
theorem initialProjector_congr {M N : Matrix V V ℝ} (hMN : M = N)
    (hM : M.IsSymm) (hN : N.IsSymm) (k : Fin (Fintype.card V)) :
    initialProjector M hM k = initialProjector N hN k := by
  subst hMN
  rfl

/-!
### Eigenbasis orthonormality and completeness (proved)

The structural facts behind `spectralProjector`, from the orthonormal
eigenbasis of Mathlib's spectral theorem. Together they say the
eigenvector coordinate matrix is orthogonal; `spectralProjector` algebra
below consumes exactly these two relations.
-/

/-- Pairwise orthonormality of the eigenbasis behind `spectralProjector`:
the coordinate inner product of the `i`-th and `j`-th eigenvectors is
`δᵢⱼ`. Proved from `OrthonormalBasis.orthonormal`; the Euclidean inner
product reduces to the coordinate sum by `PiLp.inner_apply`. -/
theorem eigvecOf_inner (M : Matrix V V ℝ) (hM : M.IsSymm) (i j : V) :
    ∑ k, eigvecOf M hM i k * eigvecOf M hM j k = if i = j then 1 else 0 := by
  have h := (isHermitian_of_isSymm hM).eigenvectorBasis.orthonormal
  rw [orthonormal_iff_ite] at h
  have hij := h i j
  rw [PiLp.inner_apply] at hij
  simpa [RCLike.inner_apply] using hij

/-- Completeness of the eigenbasis: the synthesis
`∑ i, v i a * v i b` recovers the identity matrix. Proved from
`OrthonormalBasis.sum_repr'` at `EuclideanSpace.single a 1`: the basis
resolves every unit vector. -/
theorem eigvecOf_complete (M : Matrix V V ℝ) (hM : M.IsSymm) (a b : V) :
    ∑ i, eigvecOf M hM i a * eigvecOf M hM i b = if a = b then 1 else 0 := by
  have h := (isHermitian_of_isSymm hM).eigenvectorBasis.sum_repr'
    (EuclideanSpace.single a (1 : ℝ))
  have hcoeff : ∀ i : V,
      ⟪(isHermitian_of_isSymm hM).eigenvectorBasis i,
        EuclideanSpace.single a (1 : ℝ)⟫_ℝ = eigvecOf M hM i a := by
    intro i
    rw [EuclideanSpace.inner_single_right]
    simp only [smul_eq_mul, one_mul, starRingEnd_apply]
    rfl
  have hb := congrFun h b
  simp only [hcoeff] at hb
  have hsum : ((∑ i : V, eigvecOf M hM i a •
      (isHermitian_of_isSymm hM).eigenvectorBasis i : V → ℝ)) b
      = ∑ i : V, eigvecOf M hM i a * eigvecOf M hM i b := by
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  rw [← hsum]
  refine hb.trans ?_
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg hab, EuclideanSpace.single_apply,
      if_neg (fun h => hab h.symm)]

/-- All eigenvalues of a symmetric matrix with everywhere-nonpositive
quadratic form are nonpositive: at each eigenbasis vector `v`, the
eigenvector equation gives `λ (v ⬝ v) = vᵀ M v ≤ 0` with `v ⬝ v = 1` by
orthonormality. A one-sided Rayleigh-quotient bound; the same pattern
bounds eigenvalues of PSD-type operators and is consumed by the
computational eigenvalue QA in `Scaffold/QA/SpectralGraph/Cheeger_QA.lean`. -/
theorem eigvalOf_le_of_quadForm_nonpos (M : Matrix V V ℝ) (hM : M.IsSymm)
    (hq : ∀ x : V → ℝ, Matrix.dotProduct x (M.mulVec x) ≤ 0) (i : V) :
    eigvalOf M hM i ≤ 0 := by
  have hev : M *ᵥ eigvecOf M hM i
      = eigvalOf M hM i • eigvecOf M hM i :=
    (isHermitian_of_isSymm hM).mulVec_eigenvectorBasis i
  have hvv : Matrix.dotProduct (eigvecOf M hM i) (eigvecOf M hM i) = 1 := by
    have h := (isHermitian_of_isSymm hM).eigenvectorBasis.orthonormal
    rw [orthonormal_iff_ite] at h
    have hii := h i i
    rw [PiLp.inner_apply] at hii
    simpa [eigvecOf, RCLike.inner_apply, Matrix.dotProduct] using hii
  have hq' := hq (eigvecOf M hM i)
  rw [hev, Matrix.dotProduct_smul, smul_eq_mul, hvv] at hq'
  simpa using hq'

/-- The trace of a real symmetric matrix is the sum of its eigenvalues.
Proved from Mathlib's unitary diagonalization (`spectral_theorem`):
conjugation `U D U*` preserves the trace. Together with Mathlib's
`Matrix.IsHermitian.det_eq_prod_eigenvalues` this pins small spectra from
trace, determinant, and per-eigenvalue bounds — the technique used by the
computational eigenvalue QA in `Scaffold/QA/SpectralGraph/Cheeger_QA.lean`. -/
theorem eigvalOf_sum_eq_trace (M : Matrix V V ℝ) (hM : M.IsSymm) :
    ∑ i, eigvalOf M hM i = M.trace := by
  have hst := (isHermitian_of_isSymm hM).spectral_theorem (A := M) (n := V)
  have hd : ∑ i, eigvalOf M hM i
      = (Matrix.diagonal (RCLike.ofReal ∘
          (isHermitian_of_isSymm hM).eigenvalues)).trace := by
    simp [Matrix.trace_diagonal, eigvalOf, Function.comp_apply,
      RCLike.ofReal_real_eq_id]
  calc ∑ i, eigvalOf M hM i
      = (Matrix.diagonal (RCLike.ofReal ∘
          (isHermitian_of_isSymm hM).eigenvalues)).trace := hd
    _ = (((isHermitian_of_isSymm hM).eigenvectorUnitary : Matrix V V ℝ) *
          Matrix.diagonal (RCLike.ofReal ∘
            (isHermitian_of_isSymm hM).eigenvalues) *
          star ((isHermitian_of_isSymm hM).eigenvectorUnitary :
            Matrix V V ℝ)).trace := by
        rw [Matrix.trace_mul_cycle, unitary.coe_star_mul_self,
          Matrix.one_mul]
    _ = M.trace := by congr 1; exact hst.symm

/-- Spectral projectors compose by nested thresholds: the product of the
projectors at `c₁` and `c₂` is the projector at the smaller threshold,
whenever `c₁ ≤ c₂`. Entrywise, the product expands into outer products
of eigenvectors whose cross terms vanish by pairwise orthonormality,
and the two threshold filters intersect in the filter of the smaller
threshold. The consumption half of the projector algebra's master law
(`spectralProjector_mul_spectralProjector`); the two-sided band
projectors of `GraphTheory.Band` are built on it. -/
theorem spectralProjector_mul_spectralProjector_of_le
    (M : Matrix V V ℝ) (hM : M.IsSymm) {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) :
    spectralProjector M hM c₁ * spectralProjector M hM c₂
      = spectralProjector M hM c₁ := by
  ext a b
  simp only [Matrix.mul_apply, spectralProjector, Matrix.of_apply]
  have hexp : ∀ k : V,
      (∑ i ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c₁),
          eigvecOf M hM i a * eigvecOf M hM i k) *
        (∑ j ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c₂),
            eigvecOf M hM j k * eigvecOf M hM j b) =
      ∑ i ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c₁),
        ∑ j ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c₂),
          (eigvecOf M hM i a * eigvecOf M hM i k) *
            (eigvecOf M hM j k * eigvecOf M hM j b) :=
    fun k => Finset.sum_mul_sum _ _ _ _
  simp only [hexp]
  have hreorder : ∑ k : V,
      ∑ i ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c₁),
        ∑ j ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c₂),
          (eigvecOf M hM i a * eigvecOf M hM i k) *
            (eigvecOf M hM j k * eigvecOf M hM j b) =
    ∑ i ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c₁),
      ∑ j ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c₂),
        ∑ k : V,
          (eigvecOf M hM i a * eigvecOf M hM i k) *
            (eigvecOf M hM j k * eigvecOf M hM j b) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [hreorder]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hinner : ∀ j : V,
      (∑ k : V, (eigvecOf M hM i a * eigvecOf M hM i k) *
          (eigvecOf M hM j k * eigvecOf M hM j b)) =
      eigvecOf M hM i a * eigvecOf M hM j b *
        (if i = j then 1 else 0) := by
    intro j
    have hterm : ∀ k : V,
        (eigvecOf M hM i a * eigvecOf M hM i k) *
            (eigvecOf M hM j k * eigvecOf M hM j b) =
        eigvecOf M hM i a * eigvecOf M hM j b *
          (eigvecOf M hM i k * eigvecOf M hM j k) := fun k => by ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum,
      eigvecOf_inner]
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  have hite : ∀ j : V,
      eigvecOf M hM i a * eigvecOf M hM j b * (if i = j then 1 else 0) =
      if i = j then eigvecOf M hM i a * eigvecOf M hM j b else 0 := by
    intro j
    by_cases hd : i = j <;> simp [hd]
  rw [Finset.sum_congr rfl (fun j _ => hite j), Finset.sum_ite_eq]
  have hmem : i ∈ Finset.univ.filter (fun x => eigvalOf M hM x ≤ c₂) := by
    obtain ⟨_, hi1⟩ := Finset.mem_filter.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hi1.trans h⟩
  rw [if_pos hmem]

/-- The flipped nestedness law: for `c₁ ≤ c₂`, `P_{c₂} * P_{c₁} = P_{c₁}`
as well — nested projectors commute, and both orders land on the smaller
threshold. By transposing `spectralProjector_mul_spectralProjector_of_le`
(spectral projectors are symmetric). -/
theorem spectralProjector_mul_spectralProjector_of_le'
    (M : Matrix V V ℝ) (hM : M.IsSymm) {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) :
    spectralProjector M hM c₂ * spectralProjector M hM c₁
      = spectralProjector M hM c₁ := by
  calc spectralProjector M hM c₂ * spectralProjector M hM c₁
      = (spectralProjector M hM c₁ * spectralProjector M hM c₂)ᵀ := by
        rw [Matrix.transpose_mul]
        rw [show (spectralProjector M hM c₁)ᵀ = spectralProjector M hM c₁ from
          spectralProjector_symmetric M hM c₁,
          show (spectralProjector M hM c₂)ᵀ = spectralProjector M hM c₂ from
          spectralProjector_symmetric M hM c₂]
    _ = (spectralProjector M hM c₁)ᵀ := by
        rw [spectralProjector_mul_spectralProjector_of_le M hM h]
    _ = spectralProjector M hM c₁ := spectralProjector_symmetric M hM c₁

/-- The master product law of the spectral-projector family: projectors
at two thresholds compose to the projector at the *minimum* threshold,
with no order constraint. Idempotence is the diagonal case (`min c c = c`;
`spectralProjector_idempotent` is derived from this law), and the
two-sided band projectors of `GraphTheory.Band` consume the ordered
forms to expand products of differences. -/
theorem spectralProjector_mul_spectralProjector
    (M : Matrix V V ℝ) (hM : M.IsSymm) (c₁ c₂ : ℝ) :
    spectralProjector M hM c₁ * spectralProjector M hM c₂
      = spectralProjector M hM (min c₁ c₂) := by
  rcases le_total c₁ c₂ with h | h
  · rw [min_eq_left h]
    exact spectralProjector_mul_spectralProjector_of_le M hM h
  · rw [min_eq_right h]
    exact spectralProjector_mul_spectralProjector_of_le' M hM h

/-- The complete action of a spectral projector on the eigenbasis: the
projector at threshold `c` fixes the eigenvector when its eigenvalue is
at most `c` and annihilates it when the eigenvalue is strictly above.
This is the bandpass-filtering interface: it describes exactly which
modes survive a threshold, and the two-sided version is
`GraphTheory.Band.bandProjector_mulVec_eigvecOf_self` and its
annihilation counterparts. -/
theorem spectralProjector_mulVec_eigvecOf (M : Matrix V V ℝ)
    (hM : M.IsSymm) (c : ℝ) (i : V) :
    spectralProjector M hM c *ᵥ eigvecOf M hM i
      = if eigvalOf M hM i ≤ c then eigvecOf M hM i else 0 := by
  ext b
  simp only [Matrix.mulVec, Matrix.dotProduct, spectralProjector,
    Matrix.of_apply]
  have hexp : ∀ k : V,
      (∑ i' ∈ Finset.univ.filter (fun x => eigvalOf M hM x ≤ c),
          eigvecOf M hM i' b * eigvecOf M hM i' k) * eigvecOf M hM i k =
      ∑ i' ∈ Finset.univ.filter (fun x => eigvalOf M hM x ≤ c),
        (eigvecOf M hM i' b * eigvecOf M hM i' k * eigvecOf M hM i k) :=
    fun k => Finset.sum_mul _ _ _
  simp only [hexp]
  rw [Finset.sum_comm]
  have hterm : ∀ i' : V,
      (∑ k : V, eigvecOf M hM i' b * eigvecOf M hM i' k
          * eigvecOf M hM i k) =
      eigvecOf M hM i' b * (if i' = i then 1 else 0) := by
    intro i'
    have hring : ∀ k : V,
        eigvecOf M hM i' b * eigvecOf M hM i' k * eigvecOf M hM i k =
        eigvecOf M hM i' b * (eigvecOf M hM i' k * eigvecOf M hM i k) :=
      fun k => by ring
    rw [Finset.sum_congr rfl (fun k _ => hring k), ← Finset.mul_sum,
      eigvecOf_inner]
  rw [Finset.sum_congr rfl (fun i' _ => hterm i')]
  have hite : ∀ i' : V,
      eigvecOf M hM i' b * (if i' = i then 1 else 0) =
      if i' = i then eigvecOf M hM i' b else 0 := by
    intro i'
    by_cases hd : i' = i <;> simp [hd]
  rw [Finset.sum_congr rfl (fun i' _ => hite i'), Finset.sum_ite_eq']
  have hmem : i ∈ Finset.univ.filter (fun x : V => eigvalOf M hM x ≤ c) ↔
      eigvalOf M hM i ≤ c := by simp [Finset.mem_filter]
  by_cases h : eigvalOf M hM i ≤ c
  · rw [if_pos (hmem.2 h), ite_apply, if_pos h]
  · rw [if_neg (fun hc => h (hmem.1 hc)), ite_apply, if_neg h]
    rfl

/-- Below-threshold eigenvectors are fixed by the projector at that
threshold: the specialization of `spectralProjector_mulVec_eigvecOf`. -/
theorem spectralProjector_mulVec_eigvecOf_self (M : Matrix V V ℝ)
    (hM : M.IsSymm) (c : ℝ) (i : V) (h : eigvalOf M hM i ≤ c) :
    spectralProjector M hM c *ᵥ eigvecOf M hM i = eigvecOf M hM i := by
  rw [spectralProjector_mulVec_eigvecOf M hM c i, if_pos h]

/-- Above-threshold eigenvectors are annihilated by the projector at
that threshold: the other specialization of
`spectralProjector_mulVec_eigvecOf`. -/
theorem spectralProjector_mulVec_eigvecOf_of_lt (M : Matrix V V ℝ)
    (hM : M.IsSymm) (c : ℝ) (i : V) (h : c < eigvalOf M hM i) :
    spectralProjector M hM c *ᵥ eigvecOf M hM i = 0 := by
  rw [spectralProjector_mulVec_eigvecOf M hM c i, if_neg h.not_le]

/-- Spectral projectors are idempotent: `P_c * P_c = P_c`. Entrywise, the
product expands into outer products of eigenvectors whose cross terms
vanish by pairwise orthonormality, leaving the original sum. This is the
structural fact consumed (previously implicitly) by every projector-based
statement in the Cheeger, dynamics, and drift interfaces. Since the
master product law `spectralProjector_mul_spectralProjector` was proved,
this is its diagonal case, re-derived rather than re-proved. -/
theorem spectralProjector_idempotent (M : Matrix V V ℝ) (hM : M.IsSymm)
    (c : ℝ) :
    spectralProjector M hM c * spectralProjector M hM c
      = spectralProjector M hM c := by
  rw [spectralProjector_mul_spectralProjector, min_self]

/-- Below the whole spectrum the spectral projector vanishes: the
threshold filter is empty. -/
theorem spectralProjector_eq_zero (M : Matrix V V ℝ) (hM : M.IsSymm)
    (c : ℝ) (h : ∀ i, c < eigvalOf M hM i) :
    spectralProjector M hM c = 0 := by
  have hS : (Finset.univ : Finset V).filter (fun i => eigvalOf M hM i ≤ c)
      = ∅ :=
    Finset.filter_eq_empty_iff.2 (fun x _ => (h x).not_le)
  ext a b
  simp [spectralProjector, hS]

/-- Above the whole spectrum the spectral projector is the identity: the
threshold filter is everything and the eigenbasis resolves the identity
(`eigvecOf_complete`). -/
theorem spectralProjector_eq_one (M : Matrix V V ℝ) (hM : M.IsSymm)
    (c : ℝ) (h : ∀ i, eigvalOf M hM i ≤ c) :
    spectralProjector M hM c = 1 := by
  have hS : (Finset.univ : Finset V).filter (fun i => eigvalOf M hM i ≤ c)
      = Finset.univ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_of_true (h x) trivial
  ext a b
  simp only [spectralProjector, Matrix.of_apply, hS]
  rw [eigvecOf_complete, Matrix.one_apply]

/-- The invariant-subspace projectors of the SGT center are idempotent. -/
theorem initialProjector_idempotent (M : Matrix V V ℝ) (hM : M.IsSymm)
    (k : Fin (Fintype.card V)) :
    initialProjector M hM k * initialProjector M hM k
      = initialProjector M hM k :=
  spectralProjector_idempotent M hM _

end Spectrum

/-!
## 3. Cuts, volume, conductance
-/

/-- Volume of a vertex set `S`: the sum of degrees in `S`. -/
def vol (A : WAdj (V := V)) (S : Finset V) : ℝ :=
  ∑ i in S, deg A i

/-- Edge boundary weight between `S` and its complement. -/
def boundary (A : WAdj (V := V)) (S : Finset V) : ℝ :=
  ∑ i in S, ∑ j in Sᶜ, A i j

/-- Conductance `φ(S) = boundary(S) / min(vol(S), vol(Sᶜ))`, the standard
bottleneck ratio. Meaningful for nonempty proper subsets of positive
volume; elsewhere it evaluates to the junk value inherited from division. -/
noncomputable def conductance (A : WAdj (V := V)) (S : Finset V) : ℝ :=
  boundary A S / min (vol A S) (vol A Sᶜ)

/-- The Cheeger constant: the infimum of the conductance over all
nonempty proper vertex subsets; when no such subset exists (fewer than
two vertices) the set is empty and the value is `Real.sInf ∅ = 0`. -/
noncomputable def cheegerConstant (A : WAdj (V := V)) : ℝ :=
  sInf {c : ℝ | ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧ conductance A S = c}

theorem vol_nonneg (A : WAdj (V := V)) (hnonneg : ∀ i j, 0 ≤ A i j)
    (S : Finset V) : 0 ≤ vol A S :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnonneg i j

omit [DecidableEq V] in
/-- A nonempty vertex set has positive volume when every degree is
positive — the regularity-free positivity replacement for
`vol_pos_of_regular`, consumed by the irregular Cheeger upper bound
(`GraphTheory.VariationalTransfer`) among others. -/
theorem vol_pos_of_pos_deg (A : WAdj (V := V)) (hd : ∀ i, 0 < deg A i)
    {S : Finset V} (hS : S.Nonempty) : 0 < vol A S := by
  obtain ⟨i, hi⟩ := hS
  exact Finset.sum_pos' (fun j _ => le_of_lt (hd j))
    ⟨i, hi, hd i⟩

theorem boundary_nonneg (A : WAdj (V := V)) (hnonneg : ∀ i j, 0 ≤ A i j)
    (S : Finset V) : 0 ≤ boundary A S :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnonneg i j

/-- Conductance of any subset is nonnegative for nonnegative weights. -/
theorem conductance_nonneg (A : WAdj (V := V)) (hnonneg : ∀ i j, 0 ≤ A i j)
    (S : Finset V) : 0 ≤ conductance A S :=
  div_nonneg (boundary_nonneg A hnonneg S)
    (le_min_iff.mpr ⟨vol_nonneg A hnonneg S, vol_nonneg A hnonneg Sᶜ⟩)

/-- The Cheeger constant is nonnegative whenever weights are: it is an
infimum of nonnegative conductances. -/
theorem cheegerConstant_nonneg (A : WAdj (V := V)) (hnonneg : ∀ i j, 0 ≤ A i j) :
    0 ≤ cheegerConstant A :=
  Real.sInf_nonneg fun c hc => by
    obtain ⟨S, _, _, rfl⟩ := hc
    exact conductance_nonneg A hnonneg S

/-- The Cheeger constant is attained as a lower bound by the conductance
of every nonempty proper subset. -/
theorem conductance_ge_cheegerConstant (A : WAdj (V := V))
    (hnonneg : ∀ i j, 0 ≤ A i j) (S : Finset V)
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    cheegerConstant A ≤ conductance A S := by
  have hmem : conductance A S ∈
      {c : ℝ | ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧ conductance A S = c} :=
    ⟨S, hS, hSc, rfl⟩
  have hbd : BddBelow
      {c : ℝ | ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧ conductance A S = c} :=
    ⟨0, fun c hc => by
      obtain ⟨T, _, _, rfl⟩ := hc
      exact conductance_nonneg A hnonneg T⟩
  have hglb := Real.isGLB_sInf ⟨conductance A S, hmem⟩ hbd
  exact hglb.1 hmem

/-!
### Cut duality (proved)

A cut is a property of the *partition* `{S, Sᶜ}`, not of the chosen
side. These duality facts are what cut-consuming algorithms (sweep
cuts in spectral partitioning, sparsest-cut statement shapes) assume;
they also let the Cheeger minimizer be canonicalized up to
complementation.
-/

/-- Volume complementarity: the volumes of a set and its complement sum
to the total volume `vol A univ`. -/
theorem vol_compl (A : WAdj (V := V)) (S : Finset V) :
    vol A S + vol A Sᶜ = vol A (Finset.univ : Finset V) :=
  Finset.sum_add_sum_compl S (fun i => deg A i)

/-- The edge boundary is a property of the partition, not the chosen
side: `boundary A S = boundary A Sᶜ` for symmetric weights. Proof: the
complement's boundary sums `A i j` over `(Sᶜ) × S`, which is the
original's index set `(S × Sᶜ)` after `Finset.sum_comm`, with the
summand equal by symmetry. -/
theorem boundary_compl (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (S : Finset V) :
    boundary A S = boundary A Sᶜ := by
  simp only [boundary, compl_compl]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => (hA.apply j i).symm

/-- Conductance is invariant under complementation: both the boundary
(duality) and the two volumes entering the denominator (complementarity
and symmetry of `min`) agree. Consequence for the Cheeger minimizer:
the minimizing cut may be canonicalized to either side, as sweep-cut
consumers require. -/
theorem conductance_compl (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (S : Finset V) :
    conductance A S = conductance A Sᶜ := by
  rw [conductance, conductance, boundary_compl A hA, compl_compl, min_comm]

/-- Degenerate-cut guard: the boundary of the empty set vanishes. -/
theorem boundary_empty (A : WAdj (V := V)) : boundary A ∅ = 0 := by
  simp [boundary]

/-- Degenerate-cut guard: the boundary of the full vertex set vanishes
(its complement is empty). -/
theorem boundary_univ (A : WAdj (V := V)) :
    boundary A (Finset.univ : Finset V) = 0 := by
  simp [boundary]

/-!
## 4. Laplacian quadratic form (proved)

The Dirichlet-sum identity: the Laplacian quadratic form is the weighted
sum of squared vertex differences. This makes positive semidefiniteness
manifest.
-/

/-- The Dirichlet form identity: for symmetric `A`,
`xᵀ L x = ½ ∑_{i,j} A i j (x i - x j)²`. -/
theorem laplacian_quadForm (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (x : V → ℝ) :
    quadForm (laplacian A) x = (∑ i, ∑ j, A i j * (x i - x j) ^ 2) / 2 := by
  -- The diagonal (degree) part of the quadratic form.
  have hdegpart : ∀ i : V,
      ∑ j, degreeMatrix A i j * x i * x j = deg A i * x i * x i := by
    intro i
    refine (Finset.sum_eq_single i ?_ ?_).trans (by rw [degreeMatrix_diagonal])
    · intro j _ hj
      rw [degreeMatrix_off_diagonal A (Ne.symm hj)]
      ring
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  -- Row sums convert between degree-weighted and adjacency-weighted sums.
  have hrow : ∀ i : V, deg A i * x i * x i = ∑ j, A i j * x i * x i := by
    intro i
    rw [deg, mul_assoc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_assoc]
  -- The symmetric counterpart, using that `A` is symmetric.
  have hswap : ∑ i, ∑ j, A i j * x j * x j = ∑ i, ∑ j, A i j * x i * x i := by
    have key : ∀ j : V, ∑ i, A i j * x j * x j = deg A j * x j * x j := by
      intro j
      rw [deg, mul_assoc, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [hA.apply i j, mul_assoc]
    have L : ∑ i, ∑ j, A i j * x j * x j = ∑ j, deg A j * x j * x j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => key j
    have R : ∑ i, ∑ j, A i j * x i * x i = ∑ j, deg A j * x j * x j :=
      Finset.sum_congr rfl fun i _ => (hrow i).symm
    rw [L, R]
  -- Unfold the quadratic form into entrywise sums.
  have h1 : quadForm (laplacian A) x
      = ∑ i, ∑ j, (degreeMatrix A i j - A i j) * x i * x j := by
    simp only [quadForm, laplacian, Matrix.dotProduct, Matrix.mulVec,
      Matrix.sub_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- Split the Dirichlet sum into its three components.
  have hexp : ∀ i j : V, A i j * (x i - x j) ^ 2
      = A i j * x i * x i - 2 * (A i j * x i * x j) + A i j * x j * x j := by
    intro i j
    rw [sub_sq]
    ring
  have hsplit : ∑ i, ∑ j, A i j * (x i - x j) ^ 2
      = (∑ i, ∑ j, A i j * x i * x i) - 2 * (∑ i, ∑ j, A i j * x i * x j)
        + ∑ i, ∑ j, A i j * x j * x j := by
    simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum]
  -- Assemble: the quadratic form is the degree part minus the adjacency part.
  have hqf : quadForm (laplacian A) x
      = (∑ i, ∑ j, A i j * x i * x i) - ∑ i, ∑ j, A i j * x i * x j := by
    rw [h1]
    have e1 : ∀ i : V,
        ∑ j, (degreeMatrix A i j - A i j) * x i * x j
          = ∑ j, A i j * x i * x i - ∑ j, A i j * x i * x j := by
      intro i
      simp only [sub_mul, mul_sub]
      rw [Finset.sum_sub_distrib, hdegpart i, hrow i]
    calc ∑ i, ∑ j, (degreeMatrix A i j - A i j) * x i * x j
        = ∑ i, (∑ j, A i j * x i * x i - ∑ j, A i j * x i * x j) :=
          Finset.sum_congr rfl fun i _ => e1 i
      _ = (∑ i, ∑ j, A i j * x i * x i) - ∑ i, ∑ j, A i j * x i * x j := by
          rw [← Finset.sum_sub_distrib]
  rw [hqf, hsplit, hswap]
  linarith

/-- Positive semidefiniteness of the Laplacian for symmetric nonnegative
weights: every term of the Dirichlet sum is nonnegative. -/
theorem laplacian_psd (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) :
    ∀ x : V → ℝ, 0 ≤ quadForm (laplacian A) x := by
  intro x
  rw [laplacian_quadForm A hA x]
  refine div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_) zero_le_two
  exact mul_nonneg (hnonneg i j) (sq_nonneg (x i - x j))

/-!
## 5. Connectivity and the Laplacian kernel (proved)

The support-graph adapter to Mathlib's `SimpleGraph`, and the kernel
characterization: on a connected graph (symmetric, nonnegative weights),
the constants are the *only* Laplacian-kernel vectors. This is the
converse of `laplacian_ones_in_kernel` and the hinge on which
effective-resistance well-definedness, positivity of `λ₂`, Fiedler
interfaces, and mixing statements hang (backlog item 7; proposal
`proposals/electrical-structure-crust.md`, step 1). The proof path is
the classical one: a kernel vector has zero Dirichlet energy, hence is
constant across every positive-weight edge, and connectivity propagates
the value along walks.
-/

/-- The loopless support graph of a symmetric weighted adjacency matrix:
`i` and `j` are adjacent exactly when `i ≠ j` and the weight `A i j` is
positive. The `i ≠ j` conjunct is forced by `SimpleGraph`
looplessness — positive diagonal weights (self-loops) cancel in `D - A`
and so must not create adjacency. This is the `WAdj → SimpleGraph`
direction of the Mathlib adapter surface: it makes Mathlib's `Walk`,
`Reachable`, and `Connected` API applicable to the matrix-first
representation, with symmetry discharged once, here. -/
def supportGraph (A : WAdj (V := V)) (hA : A.IsSymm) : SimpleGraph V where
  Adj i j := i ≠ j ∧ 0 < A i j
  symm := fun i j h => ⟨Ne.symm h.1, by rw [hA.apply i j]; exact h.2⟩
  loopless := fun _ h => h.1 rfl

omit [Fintype V] [DecidableEq V] in
/-- Adjacency in the support graph is exactly a positive off-diagonal
weight: the interface lemma for consumers that should not unfold the
adapter. -/
theorem supportGraph_adj {A : WAdj (V := V)} {hA : A.IsSymm} {i j : V} :
    (supportGraph A hA).Adj i j ↔ i ≠ j ∧ 0 < A i j :=
  Iff.rfl

/-- A Laplacian-kernel vector is constant across every edge of positive
weight: the quadratic form vanishes on the kernel, and by the Dirichlet
identity it is a sum of nonnegative terms `A i j (f i - f j)²` that must
vanish termwise. -/
theorem eq_of_laplacian_mulVec_eq_zero_of_pos_weight (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j) {f : V → ℝ}
    (hf : (laplacian A).mulVec f = 0) {i j : V} (hpos : 0 < A i j) :
    f i = f j := by
  have hqf : quadForm (laplacian A) f = 0 := by
    rw [quadForm, hf]
    simp
  rw [laplacian_quadForm A hA f] at hqf
  rcases (div_eq_zero_iff (b := (2 : ℝ))).1 hqf with hsum | h2
  · have hinner := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i' _ => Finset.sum_nonneg fun j' _ =>
        mul_nonneg (hnonneg i' j') (sq_nonneg _))).1 hsum i
      (Finset.mem_univ i)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j' _ => mul_nonneg (hnonneg i j') (sq_nonneg _))).1 hinner j
      (Finset.mem_univ j)
    rcases mul_eq_zero.1 hterm with hA0 | hsq
    · exact absurd hA0 hpos.ne'
    · exact sub_eq_zero.1 (sq_eq_zero_iff.1 hsq)
  · exact absurd h2 (by norm_num)

/-- A Laplacian-kernel vector is constant along support-graph walks:
each walk step crosses a positive-weight edge, and the previous theorem
forces equality across it. Induction over `SimpleGraph.Walk`. -/
theorem eq_of_supportGraph_walk (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) {f : V → ℝ}
    (hf : (laplacian A).mulVec f = 0) {i j : V}
    (w : (supportGraph A hA).Walk i j) : f i = f j := by
  induction w with
  | nil => rfl
  | cons hadj _ ih =>
    exact (eq_of_laplacian_mulVec_eq_zero_of_pos_weight A hA hnonneg hf
      ((supportGraph_adj.1 hadj).2)).trans ih

/-- **Connectivity ⇒ the Laplacian kernel is the constants** (the
converse of `laplacian_ones_in_kernel`): for symmetric nonnegative
weights whose support graph is connected, every kernel vector is
constant. The anchor vertex comes from the `Nonempty` field bundled in
`SimpleGraph.Connected`; the value then propagates along walks to every
vertex. -/
theorem exists_const_of_laplacian_mulVec_eq_zero (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hconn : (supportGraph A hA).Connected) {f : V → ℝ}
    (hf : (laplacian A).mulVec f = 0) : ∃ c : ℝ, f = fun _ => c := by
  obtain ⟨i₀⟩ := hconn.nonempty
  refine ⟨f i₀, funext fun i => ?_⟩
  obtain ⟨w⟩ := hconn i₀ i
  exact (eq_of_supportGraph_walk A hA hnonneg hf w).symm

/-- Every constant vector is killed by the Laplacian: the scalar
multiple of `laplacian_ones_in_kernel`, routed through the linear map
`Matrix.mulVecLin`. -/
theorem laplacian_mulVec_const (A : WAdj (V := V)) (c : ℝ) :
    (laplacian A).mulVec (fun _ => c) = 0 := by
  have hvec : (fun _ => c : V → ℝ) = c • onesVec := by
    funext i; simp [onesVec]
  rw [hvec, ← Matrix.mulVecLin_apply, map_smul,
    show Matrix.mulVecLin (laplacian A) onesVec = 0 by
      rw [Matrix.mulVecLin_apply]; exact laplacian_ones_in_kernel A,
    smul_zero]

/-- **The kernel characterization, iff form:** for a connected graph
with symmetric nonnegative weights, `L *ᵥ f = 0` if and only if `f` is
constant. -/
theorem laplacian_mulVec_eq_zero_iff_exists_const (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hconn : (supportGraph A hA).Connected) (f : V → ℝ) :
    (laplacian A).mulVec f = 0 ↔ ∃ c : ℝ, f = fun _ => c :=
  ⟨fun hf => exists_const_of_laplacian_mulVec_eq_zero A hA hnonneg hconn hf,
    by rintro ⟨c, rfl⟩; exact laplacian_mulVec_const A c⟩

/-- **The kernel characterization, span form:** for a connected graph
with symmetric nonnegative weights, the kernel of the Laplacian as a
linear map is exactly the line spanned by the all-ones vector. This is
the statement shape consumed by uniqueness arguments — e.g. the
well-definedness of effective resistance via "two solutions differ by a
kernel element, which is constant" (proposal step 2). -/
theorem laplacian_kernel_eq_span_onesVec (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hconn : (supportGraph A hA).Connected) :
    LinearMap.ker (Matrix.mulVecLin (laplacian A))
      = Submodule.span ℝ ({onesVec} : Set (V → ℝ)) := by
  refine le_antisymm ?_ ?_
  · intro f hf
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hf
    obtain ⟨c, hc⟩ := exists_const_of_laplacian_mulVec_eq_zero A hA hnonneg
      hconn hf
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [hc]
    funext i
    simp [onesVec]
  · rw [Submodule.span_le]
    rintro f (rfl : f = onesVec)
    show Matrix.mulVecLin (laplacian A) onesVec = 0
    rw [Matrix.mulVecLin_apply]
    exact laplacian_ones_in_kernel A

/-!
### The kernel on a disconnected graph (component form)

The connected statement above identifies the kernel with the constants.
The component form below drops the connectivity hypothesis entirely:
`L *ᵥ f = 0` exactly when `f` is constant on each connected component
of the support graph. This is the weighted counterpart of Mathlib's
`SimpleGraph.lapMatrix_toLin'_apply_eq_zero_iff_forall_reachable` and
the load-bearing statement behind the kernel-equality bridge to
Mathlib's `lapMatrix` kernel in
`Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter` (proposal
`proposals/electrical-structure-crust.md`, step 3).
-/

/-- Entrywise action of the Laplacian in diffusion form:
`(L *ᵥ f) i = ∑ j, A i j * (f i - f j)`. The degree part of the matrix
cancels the `j = i` term, so self-loop weights do not appear — the
same cancellation that keeps `supportGraph` loopless honest. -/
theorem laplacian_mulVec_apply (A : WAdj (V := V)) (f : V → ℝ) (i : V) :
    (laplacian A).mulVec f i = ∑ j, A i j * (f i - f j) := by
  have hdeg : ∑ j, degreeMatrix A i j * f j = deg A i * f i := by
    refine (Finset.sum_eq_single i ?_ ?_).trans ?_
    · intro j _ hj
      rw [degreeMatrix_off_diagonal A (Ne.symm hj), zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
    rw [degreeMatrix_diagonal]
  have hrow : deg A i * f i = ∑ j, A i j * f i := by
    rw [deg, Finset.sum_mul]
  simp only [laplacian, Matrix.sub_apply, Matrix.mulVec, Matrix.dotProduct,
    sub_mul]
  rw [Finset.sum_sub_distrib, hdeg, hrow, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_sub]

/-- A vector that is constant on each connected component of the
support graph is killed by the Laplacian — the kernel-characterization
direction that needs **no** connectivity hypothesis. Entrywise, every
term `A i j * (f i - f j)` of the diffusion form vanishes: a positive
off-diagonal weight is a support-graph edge, along which `f` is
constant by hypothesis. -/
theorem laplacian_mulVec_eq_zero_of_forall_reachable (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j) {f : V → ℝ}
    (hf : ∀ i j : V, (supportGraph A hA).Reachable i j → f i = f j) :
    (laplacian A).mulVec f = 0 := by
  funext i
  rw [laplacian_mulVec_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases eq_or_lt_of_le (hnonneg i j) with h0 | hpos
  · rw [← h0, zero_mul]
  · by_cases hij : i = j
    · subst hij
      rw [sub_self, mul_zero]
    · rw [hf i j ((supportGraph_adj.2 ⟨hij, hpos⟩).reachable),
        sub_self, mul_zero]

/-- **The kernel characterization, component form** (no connectivity
hypothesis): for symmetric nonnegative weights, `L *ᵥ f = 0` if and
only if `f` is constant along reachability in the support graph, i.e.
constant on each connected component. One direction is the walk
propagation behind `laplacian_kernel_eq_span_onesVec`; the converse is
`laplacian_mulVec_eq_zero_of_forall_reachable`. -/
theorem laplacian_mulVec_eq_zero_iff_forall_reachable (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j) (f : V → ℝ) :
    (laplacian A).mulVec f = 0 ↔
      ∀ i j : V, (supportGraph A hA).Reachable i j → f i = f j :=
  ⟨fun hf i j h =>
      Nonempty.elim h fun w => eq_of_supportGraph_walk A hA hnonneg hf w,
    fun hf => laplacian_mulVec_eq_zero_of_forall_reachable A hA hnonneg hf⟩

/-!
### Potential solvability (the electrical hinge)

The solvability half of the potential equation: on a connected graph
(symmetric, nonnegative weights), every zero-sum demand `b` admits a
potential `f` with `laplacian A *ᵥ f = b`. Existence is *not* implied by
the kernel characterization — it is the hinge on which the electrical
program turns, and `proposals/electrical-structure-crust.md` gates any
definition of effective resistance behind it (step 4 there).

Route decision, recorded before stating: the **constructive eigenbasis**
route (witness `f = ∑_{λᵢ ≠ 0} (vᵢ ⬝ᵥ b / λᵢ) • vᵢ`), not the
orthogonality route (`range L = (ker L)ᗮ`, for which the pin has no
ready-made lemma over these function types). The constructive route
consumes the center's own proved spectral tools — orthonormality
(`eigvecOf_inner`), completeness (`eigvecOf_complete`), the eigenvector
equation (`mulVec_eigenvectorBasis`) — and the step-2 kernel theorem
`laplacian_kernel_eq_span_onesVec`, so an error in any of them would
break this proof rather than pass beside it.
-/

/-- Reciprocity: the Laplacian is self-adjoint in coordinates,
`w ⬝ᵥ (L *ᵥ f) = (L *ᵥ w) ⬝ᵥ f` (a discrete Green identity). This is
`Matrix.dotProduct_mulVec` plus symmetry of `L`. Consumers: the kernel
certificate below, the negative solvability witnesses in
`Scaffold/QA/SpectralGraph/PotentialSolvability_QA.lean`, and the energy
identities of the electrical program (proposal step 5). -/
theorem laplacian_dotProduct_mulVec (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (w f : V → ℝ) :
    Matrix.dotProduct w (laplacian A *ᵥ f)
      = Matrix.dotProduct (laplacian A *ᵥ w) f := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    (laplacian_symmetric A hA).eq]

/-- Kernel vectors certify unsolvability: if `L *ᵥ w = 0`, then every
image `L *ᵥ f` is `⬝ᵥ`-orthogonal to `w`. Contrapositive: a demand `b`
with `w ⬝ᵥ b ≠ 0` for some kernel vector `w` admits no potential — the
shape of every unsolvability witness. -/
theorem dotProduct_eq_zero_of_laplacian_mulVec_eq_zero
    (A : WAdj (V := V)) (hA : Matrix.IsSymm A) {w f : V → ℝ}
    (hw : (laplacian A).mulVec w = 0) :
    Matrix.dotProduct w (laplacian A *ᵥ f) = 0 := by
  rw [laplacian_dotProduct_mulVec A hA w f, hw, Matrix.zero_dotProduct]

/-- Entrywise action of a symmetric matrix on a finite combination of
its eigenbasis vectors: multiplying distributes over the combination and
each eigenvector returns its eigenvalue. A general coefficient `c` keeps
the statement instantiation-friendly; the coefficient never needs to be
unfolded at use sites. -/
theorem mulVec_eigvecOf_sum_apply {M : Matrix V V ℝ} (hM : M.IsSymm)
    (c : V → ℝ) (a : V) :
    (M *ᵥ (fun a => ∑ i, c i * eigvecOf M hM i a)) a
      = ∑ i, c i * (eigvalOf M hM i * eigvecOf M hM i a) := by
  have hev : ∀ i : V, M *ᵥ eigvecOf M hM i
      = eigvalOf M hM i • eigvecOf M hM i :=
    fun i => (isHermitian_of_isSymm hM).mulVec_eigenvectorBasis i
  have h1 : (M *ᵥ (fun a => ∑ i, c i * eigvecOf M hM i a)) a
      = ∑ k, M a k * ∑ i, c i * eigvecOf M hM i k := by
    simp only [Matrix.mulVec, Matrix.dotProduct]
  have h2 : ∀ i : V, ∑ k, M a k * eigvecOf M hM i k
      = eigvalOf M hM i * eigvecOf M hM i a := by
    intro i
    exact congrFun (hev i) a
  have hfold : ∀ i : V, c i * ∑ k, M a k * eigvecOf M hM i k
      = ∑ k, c i * (M a k * eigvecOf M hM i k) := by
    intro i
    simp only [Finset.mul_sum]
  rw [h1]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr : ∀ k : V, M a k * (c i * eigvecOf M hM i k)
      = c i * (M a k * eigvecOf M hM i k) := fun k => by ring
  calc ∑ k, M a k * (c i * eigvecOf M hM i k)
      = ∑ k, c i * (M a k * eigvecOf M hM i k) :=
        Finset.sum_congr rfl fun k _ => hr k
    _ = c i * ∑ k, M a k * eigvecOf M hM i k := (hfold i).symm
    _ = c i * (eigvalOf M hM i * eigvecOf M hM i a) := by rw [h2 i]

/-!
### Eigenbasis expansion, Parseval, and the quadratic-form resolution

Entrywise completeness, the Parseval identity for the dot product, and
the spectral resolution of the quadratic form through the orthonormal
eigenbasis. These are the matrix-world counterparts of basis expansion
in an inner product space; the λ₂ variational characterization below
is built entirely from them.
-/

/-- Eigenbasis expansion, entrywise: every vector is reconstructed
from its eigencomponents, `x a = ∑ i, (v i ⬝ᵥ x) * v i a` over the
orthonormal eigenbasis. This is the entrywise form of completeness
(`eigvecOf_complete`), factored out for reuse: Parseval, the quadratic
form resolution, and the constructive spectral inversion all consume
it. -/
theorem eigvecOf_expansion_apply {M : Matrix V V ℝ} (hM : M.IsSymm)
    (x : V → ℝ) (a : V) :
    ∑ i, Matrix.dotProduct (eigvecOf M hM i) x * eigvecOf M hM i a
      = x a := by
  calc ∑ i, Matrix.dotProduct (eigvecOf M hM i) x * eigvecOf M hM i a
      = ∑ i, ∑ k, (eigvecOf M hM i k * x k) * eigvecOf M hM i a := by
        exact Finset.sum_congr rfl fun i _ => by
          simp only [Matrix.dotProduct, Finset.sum_mul]
    _ = ∑ k, ∑ i, (eigvecOf M hM i k * x k) * eigvecOf M hM i a :=
        Finset.sum_comm
    _ = ∑ k, x k * ∑ i, eigvecOf M hM i k * eigvecOf M hM i a := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ k, x k * (if k = a then 1 else 0) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [eigvecOf_complete M hM k a]
    _ = x a := by simp

/-- Parseval identity: the dot product resolves through the orthonormal
eigenbasis, `x ⬝ᵥ y = ∑ i, (v i ⬝ᵥ x) * (v i ⬝ᵥ y)`. -/
theorem dotProduct_eigvecOf {M : Matrix V V ℝ} (hM : M.IsSymm)
    (x y : V → ℝ) :
    Matrix.dotProduct x y =
      ∑ i, Matrix.dotProduct (eigvecOf M hM i) x
        * Matrix.dotProduct (eigvecOf M hM i) y := by
  calc Matrix.dotProduct x y = ∑ a, x a * y a := rfl
    _ = ∑ a, x a * ∑ i, Matrix.dotProduct (eigvecOf M hM i) y
          * eigvecOf M hM i a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [eigvecOf_expansion_apply hM y a]
    _ = ∑ a, ∑ i, x a * (Matrix.dotProduct (eigvecOf M hM i) y
          * eigvecOf M hM i a) := by simp only [Finset.mul_sum]
    _ = ∑ i, ∑ a, x a * (Matrix.dotProduct (eigvecOf M hM i) y
          * eigvecOf M hM i a) := Finset.sum_comm
    _ = ∑ i, Matrix.dotProduct (eigvecOf M hM i) y
          * ∑ a, x a * eigvecOf M hM i a := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hre : ∀ a : V, x a * (Matrix.dotProduct (eigvecOf M hM i) y
            * eigvecOf M hM i a)
            = Matrix.dotProduct (eigvecOf M hM i) y * (x a
              * eigvecOf M hM i a) := fun a => by ring
        rw [Finset.sum_congr rfl fun a _ => hre a, ← Finset.mul_sum]
    _ = ∑ i, Matrix.dotProduct (eigvecOf M hM i) y
          * Matrix.dotProduct x (eigvecOf M hM i) := rfl
    _ = ∑ i, Matrix.dotProduct (eigvecOf M hM i) x
          * Matrix.dotProduct (eigvecOf M hM i) y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.dotProduct_comm x (eigvecOf M hM i)]
        ring

/-- The eigenaction in the first slot of the dot product: for symmetric
`M`, `v i ⬝ᵥ (M *ᵥ x) = μ i * (v i ⬝ᵥ x)` — the self-adjointness of `M`
in coordinates, through the eigenvector equation. -/
theorem dotProduct_eigvecOf_mulVec {M : Matrix V V ℝ} (hM : M.IsSymm)
    (i : V) (x : V → ℝ) :
    Matrix.dotProduct (eigvecOf M hM i) (M *ᵥ x)
      = eigvalOf M hM i * Matrix.dotProduct (eigvecOf M hM i) x := by
  have hev : M *ᵥ eigvecOf M hM i
      = eigvalOf M hM i • eigvecOf M hM i :=
    (isHermitian_of_isSymm hM).mulVec_eigenvectorBasis i
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq, hev,
    Matrix.smul_dotProduct, smul_eq_mul]

/-- The eigenaction at `1 - M`: for symmetric `M`, reading a component of
`(1 - M) *ᵥ x` in the eigenbasis multiplies the component of `x` by
`1 - μ i`. Composed from `dotProduct_eigvecOf_mulVec` (self-adjointness in
coordinates). The reflection-shaped operators of the mixing program — the
walk transition matrix, seen through the degree-square-root similarity as
`1 − L_sym` — consume this to evolve eigencoordinates stepwise. -/
theorem eigvecOf_dotProduct_one_sub_mulVec {M : Matrix V V ℝ} (hM : M.IsSymm)
    (i : V) (x : V → ℝ) :
    Matrix.dotProduct (eigvecOf M hM i) ((1 - M) *ᵥ x)
      = (1 - eigvalOf M hM i) * Matrix.dotProduct (eigvecOf M hM i) x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.dotProduct_sub,
    dotProduct_eigvecOf_mulVec hM i x, sub_mul, one_mul]

/-- Spectral resolution of the quadratic form: for symmetric `M`,
`xᵀ M x = ∑ i, μ i * (v i ⬝ᵥ x)²` — the energy is the eigenvalue-weighted
sum of squared eigencomponents. -/
theorem quadForm_eigvalOf {M : Matrix V V ℝ} (hM : M.IsSymm)
    (x : V → ℝ) :
    quadForm M x =
      ∑ i, eigvalOf M hM i
        * (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2 := by
  rw [quadForm, dotProduct_eigvecOf hM x (M *ᵥ x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_eigvecOf_mulVec hM i x]
  ring

/-- A unit eigenvector's quadratic form is its eigenvalue. -/
theorem quadForm_eigvecOf_self {M : Matrix V V ℝ} (hM : M.IsSymm)
    (i : V) :
    quadForm M (eigvecOf M hM i) = eigvalOf M hM i := by
  have h1 : Matrix.dotProduct (eigvecOf M hM i) (eigvecOf M hM i) = 1 := by
    simpa [Matrix.dotProduct] using eigvecOf_inner M hM i i
  have hev : M *ᵥ eigvecOf M hM i
      = eigvalOf M hM i • eigvecOf M hM i :=
    (isHermitian_of_isSymm hM).mulVec_eigenvectorBasis i
  calc quadForm M (eigvecOf M hM i)
      = eigvalOf M hM i := by
        show Matrix.dotProduct (eigvecOf M hM i) (M *ᵥ eigvecOf M hM i) = _
        rw [hev, Matrix.dotProduct_smul, smul_eq_mul, h1, mul_one]

/-- **Top-eigenvalue Rayleigh domination, multiplication form.** For any
symmetric matrix, `xᵀ M x ≤ λ_max • (x ⬝ᵥ x)` where `λ_max` is the last
entry of the sorted spectrum: the quadratic form is the eigenvalue-weighted
sum of squared eigencomponents (`quadForm_eigvalOf`), Parseval identifies
the weight sum with `x ⬝ᵥ x` (`dotProduct_eigvecOf`), and every
eigenvalue is dominated by the last sorted entry
(`eigvalOf_le_evals_last`). Stated unconditionally in `x` (both sides
vanish at `x = 0`) and without any positivity hypothesis — this is the
upper half of the Rayleigh sandwich that perturbation and mixing
arguments consume. -/
theorem quadForm_le_evals_last {M : Matrix V V ℝ} (hM : M.IsSymm)
    (hcard : 1 ≤ Fintype.card V) (x : V → ℝ) :
    quadForm M x ≤
      evals hM ⟨Fintype.card V - 1, by omega⟩ * Matrix.dotProduct x x := by
  have hq : quadForm M x
      = ∑ i, eigvalOf M hM i
        * (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2 :=
    quadForm_eigvalOf hM x
  have hD : Matrix.dotProduct x x
      = ∑ i, (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2 := by
    rw [dotProduct_eigvecOf hM x x]
    exact Finset.sum_congr rfl fun i _ => (pow_two _).symm
  rw [hq, hD, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (eigvalOf_le_evals_last hM hcard i) (sq_nonneg _)

/-- **Bottom-eigenvalue Rayleigh domination, multiplication form.** For any
symmetric matrix, `λ_min * (x ⬝ᵥ x) ≤ xᵀ M x` where `λ_min` is the first
entry of the sorted spectrum — the mirror of `quadForm_le_evals_last`:
the quadratic form is the eigenvalue-weighted sum of squared eigencomponents
(`quadForm_eigvalOf`), Parseval identifies the weight sum with `x ⬝ᵥ x`
(`dotProduct_eigvecOf`), and every eigenvalue dominates the first sorted
entry (`evals_first_le_eigvalOf`). Stated unconditionally in `x` (both
sides vanish at `x = 0`) and without any positivity hypothesis — this is
the lower half of the Rayleigh sandwich that perturbation arguments
consume (the additive Weyl bound in
`Analysis.OperatorTheory.Perturbation.Weyl` is its first consumer). -/
theorem evals_first_mul_dotProduct_le_quadForm {M : Matrix V V ℝ} (hM : M.IsSymm)
    (hcard : 1 ≤ Fintype.card V) (x : V → ℝ) :
    evals hM ⟨0, by omega⟩ * Matrix.dotProduct x x ≤ quadForm M x := by
  have hq : quadForm M x
      = ∑ i, eigvalOf M hM i
        * (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2 :=
    quadForm_eigvalOf hM x
  have hD : Matrix.dotProduct x x
      = ∑ i, (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2 := by
    rw [dotProduct_eigvecOf hM x x]
    exact Finset.sum_congr rfl fun i _ => (pow_two _).symm
  rw [hq, hD, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (evals_first_le_eigvalOf hM hcard i) (sq_nonneg _)

/-- **General-kernel orthogonality.** For any symmetric matrix and any
kernel vector `w` (`M *ᵥ w = 0`), eigenvectors at nonzero eigenvalues are
orthogonal to `w`. Proof: Parseval on the pair `(v i, M *ᵥ w)`, with the
eigenaction resolved and the kernel equation killing the left side. The
`onesVec` instance below adds only the specialization `w = onesVec`; the
general form is what operators with a non-constant kernel vector — the
normalized Laplacian `L_sym` of an irregular graph, whose kernel is
spanned by `√D · onesVec` — consume for variational statements
(`secondEval_le_rayleigh_of_ker`). -/
theorem eigvecOf_ortho_of_mulVec_eq_zero {M : Matrix V V ℝ}
    (hM : M.IsSymm) {w : V → ℝ} (hker : M *ᵥ w = 0) {i : V}
    (hne : eigvalOf M hM i ≠ 0) :
    Matrix.dotProduct (eigvecOf M hM i) w = 0 := by
  -- Parseval on the pair (v i, M *ᵥ w), with the eigenaction resolved
  have hparseval : Matrix.dotProduct (eigvecOf M hM i) (M *ᵥ w)
      = ∑ j : V, Matrix.dotProduct (eigvecOf M hM j) (eigvecOf M hM i)
        * (eigvalOf M hM j
          * Matrix.dotProduct (eigvecOf M hM j) w) := by
    rw [dotProduct_eigvecOf hM (eigvecOf M hM i) (M *ᵥ w)]
    simp only [dotProduct_eigvecOf_mulVec hM]
  rw [hker, Matrix.dotProduct_zero] at hparseval
  -- the sum collapses to the i-term by orthonormality
  have hvanish : ∀ j ∈ (Finset.univ : Finset V), j ≠ i →
      (Matrix.dotProduct (eigvecOf M hM j) (eigvecOf M hM i)
        * (eigvalOf M hM j
          * Matrix.dotProduct (eigvecOf M hM j) w)) = 0 := by
    intro j _ hj
    have hij : eigvecOf M hM j ⬝ᵥ eigvecOf M hM i = 0 := by
      simpa [Matrix.dotProduct, if_neg hj] using eigvecOf_inner M hM j i
    rw [hij, zero_mul]
  rw [Finset.sum_eq_single i hvanish (fun hni =>
    absurd (Finset.mem_univ i) hni)] at hparseval
  -- the i-term is (v i ⬝ᵥ v i) * (μ i * (v i ⬝ᵥ w)) = μ i * (v i ⬝ᵥ w)
  have hii : Matrix.dotProduct (eigvecOf M hM i)
      (eigvecOf M hM i) = 1 := by
    simpa [Matrix.dotProduct] using eigvecOf_inner M hM i i
  rw [hii, one_mul] at hparseval
  exact (mul_eq_zero.1 hparseval.symm).resolve_left hne

/-- Generic form: for any symmetric matrix whose kernel contains
`onesVec` (`M *ᵥ onesVec = 0`), eigenvectors at nonzero eigenvalues are
orthogonal to `onesVec`. Proof: Parseval on the pair `(v i, M *ᵥ
onesVec)`, with the eigenaction resolved and the kernel equation killing
the left side. Used by `secondEval_variational` for general operators
(normalized Laplacians in particular); the Laplacian instance below is
the special case `M = laplacian A`. Instance of the generic
`eigvecOf_ortho_of_mulVec_eq_zero` at `w = onesVec`. -/
theorem eigvecOf_ortho_onesVec_of_mulVec_eq_zero {M : Matrix V V ℝ}
    (hM : M.IsSymm) (hker : M *ᵥ onesVec = 0) {i : V}
    (hne : eigvalOf M hM i ≠ 0) :
    Matrix.dotProduct (eigvecOf M hM i) onesVec = 0 := by
  -- Parseval on the pair (v i, M *ᵥ onesVec), with the eigenaction resolved
  have hparseval : Matrix.dotProduct (eigvecOf M hM i) (M *ᵥ onesVec)
      = ∑ j : V, Matrix.dotProduct (eigvecOf M hM j) (eigvecOf M hM i)
        * (eigvalOf M hM j
          * Matrix.dotProduct (eigvecOf M hM j) onesVec) := by
    rw [dotProduct_eigvecOf hM (eigvecOf M hM i) (M *ᵥ onesVec)]
    simp only [dotProduct_eigvecOf_mulVec hM]
  rw [hker, Matrix.dotProduct_zero] at hparseval
  -- the sum collapses to the i-term by orthonormality
  have hvanish : ∀ j ∈ (Finset.univ : Finset V), j ≠ i →
      (Matrix.dotProduct (eigvecOf M hM j) (eigvecOf M hM i)
        * (eigvalOf M hM j
          * Matrix.dotProduct (eigvecOf M hM j) onesVec)) = 0 := by
    intro j _ hj
    have hij : eigvecOf M hM j ⬝ᵥ eigvecOf M hM i = 0 := by
      simpa [Matrix.dotProduct, if_neg hj] using eigvecOf_inner M hM j i
    rw [hij, zero_mul]
  rw [Finset.sum_eq_single i hvanish (fun hni =>
    absurd (Finset.mem_univ i) hni)] at hparseval
  -- the i-term is (v i ⬝ᵥ v i) * (μ i * (v i ⬝ᵥ onesVec)) = μ i * (v i ⬝ᵥ onesVec)
  have hii : Matrix.dotProduct (eigvecOf M hM i)
      (eigvecOf M hM i) = 1 := by
    simpa [Matrix.dotProduct] using eigvecOf_inner M hM i i
  rw [hii, one_mul] at hparseval
  exact (mul_eq_zero.1 hparseval.symm).resolve_left hne

/-- Eigenvectors of nonzero Laplacian eigenvalues are orthogonal to
`onesVec`: `onesVec` is always in the kernel (row sums vanish, no
symmetry needed), and the eigenbasis expansion of the kernel equation
kills its components along nonzero eigenspaces. No hypothesis beyond
symmetry. Instance of the generic
`eigvecOf_ortho_onesVec_of_mulVec_eq_zero` at `M = laplacian A`. -/
theorem eigvecOf_ortho_onesVec (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    {i : V}
    (hne : eigvalOf (laplacian A) (laplacian_symmetric A hA) i ≠ 0) :
    Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i)
      onesVec = 0 :=
  eigvecOf_ortho_onesVec_of_mulVec_eq_zero (laplacian_symmetric A hA)
    (laplacian_ones_in_kernel A) hne

/-- **Constructive spectral inversion.** For a symmetric matrix `M`, a
demand `b` whose components along the zero-eigenvalue eigenvectors all
vanish is in the range of `mulVec`: the witness is the pseudo-inverse
combination `f = ∑_{λᵢ ≠ 0} (vᵢ ⬝ᵥ b / λᵢ) • vᵢ` over the orthonormal
eigenbasis, and `M *ᵥ f = b` follows from the eigenvector equation plus
completeness of the basis. This is the load-bearing consumer of the
eigenbasis algebra (`eigvecOf_inner`, `eigvecOf_complete`,
`mulVec_eigenvectorBasis`): a defect in any of them breaks this proof. -/
theorem exists_mulVec_eq_of_zero_comp {M : Matrix V V ℝ} (hM : M.IsSymm)
    {b : V → ℝ}
    (hz : ∀ i : V, eigvalOf M hM i = 0 →
      Matrix.dotProduct (eigvecOf M hM i) b = 0) :
    ∃ f : V → ℝ, M *ᵥ f = b := by
  -- The eigenbasis resolves every demand: `b = ∑ i, (v i ⬝ᵥ b) • v i`.
  have hexp : ∀ a : V, ∑ i, Matrix.dotProduct (eigvecOf M hM i) b
      * eigvecOf M hM i a = b a :=
    fun a => eigvecOf_expansion_apply hM b a
  -- Per eigenvector, the divided coefficient remultiplies to the demand
  -- component; the zero-eigenvalue terms vanish by `hz`.
  have hterm : ∀ i a : V, (if eigvalOf M hM i = 0 then (0 : ℝ)
      else Matrix.dotProduct (eigvecOf M hM i) b / eigvalOf M hM i)
      * (eigvalOf M hM i * eigvecOf M hM i a)
      = Matrix.dotProduct (eigvecOf M hM i) b * eigvecOf M hM i a := by
    intro i a
    by_cases h0 : eigvalOf M hM i = 0
    · rw [if_pos h0, zero_mul, hz i h0, zero_mul]
    · rw [if_neg h0, ← mul_assoc, div_mul_cancel₀ _ h0]
  -- The witness: divide each eigencomponent by its eigenvalue, dropping
  -- the (vanishing) kernel components.
  refine ⟨fun a => ∑ i, (if eigvalOf M hM i = 0 then (0 : ℝ)
      else Matrix.dotProduct (eigvecOf M hM i) b / eigvalOf M hM i)
      * eigvecOf M hM i a, ?_⟩
  funext a
  calc (M *ᵥ (fun a => ∑ i, (if eigvalOf M hM i = 0 then (0 : ℝ)
          else Matrix.dotProduct (eigvecOf M hM i) b / eigvalOf M hM i)
          * eigvecOf M hM i a)) a
      = ∑ i, (if eigvalOf M hM i = 0 then (0 : ℝ)
          else Matrix.dotProduct (eigvecOf M hM i) b / eigvalOf M hM i)
          * (eigvalOf M hM i * eigvecOf M hM i a) :=
        mulVec_eigvecOf_sum_apply hM
          (fun i => if eigvalOf M hM i = 0 then (0 : ℝ)
            else Matrix.dotProduct (eigvecOf M hM i) b / eigvalOf M hM i) a
    _ = ∑ i, Matrix.dotProduct (eigvecOf M hM i) b
          * eigvecOf M hM i a :=
          Finset.sum_congr rfl fun i _ => hterm i a
    _ = b a := hexp a

/-- **Potential solvability (the electrical hinge).** For a connected
graph with symmetric nonnegative weights, every zero-sum demand `b`
(`∑ i, b i = 0`) admits a potential `f` with `laplacian A *ᵥ f = b`.

The zero-sum hypothesis discharges exactly the kernel components of the
demand: by `laplacian_kernel_eq_span_onesVec` the kernel is the line
spanned by `onesVec` (proposal step 2), and `onesVec ⬝ᵥ b = ∑ i, b i`.
Existence and this uniqueness-with-constants together are what justify a
total `effectiveResistance` in proposal step 5; defining it before this
theorem would admit vacuous proofs. -/
theorem exists_laplacian_mulVec_eq_of_sum_eq_zero (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hconn : (supportGraph A hA).Connected) {b : V → ℝ}
    (hb : ∑ i, b i = 0) :
    ∃ f : V → ℝ, (laplacian A).mulVec f = b := by
  have hL : (laplacian A).IsSymm := laplacian_symmetric A hA
  have hevL : ∀ i : V, laplacian A *ᵥ eigvecOf (laplacian A) hL i
      = eigvalOf (laplacian A) hL i • eigvecOf (laplacian A) hL i :=
    fun i => (isHermitian_of_isSymm hL).mulVec_eigenvectorBasis i
  refine exists_mulVec_eq_of_zero_comp hL fun i hi => ?_
  have hmem : eigvecOf (laplacian A) hL i
      ∈ LinearMap.ker (Matrix.mulVecLin (laplacian A)) := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hevL i, hi, zero_smul]
  have hspan : eigvecOf (laplacian A) hL i
      ∈ Submodule.span ℝ ({onesVec} : Set (V → ℝ)) := by
    rw [← laplacian_kernel_eq_span_onesVec A hA hnonneg hconn]
    exact hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hspan
  calc Matrix.dotProduct (eigvecOf (laplacian A) hL i) b
      = Matrix.dotProduct (c • onesVec) b := by rw [hc]
    _ = c * (∑ k, b k) := by
        simp only [Matrix.dotProduct, onesVec, Pi.smul_apply, smul_eq_mul,
          mul_one, Finset.mul_sum]
    _ = 0 := by rw [hb, mul_zero]

/-- **The unit demand is solvable:** on a connected graph with symmetric
nonnegative weights, the demand `e u − e v` (unit injection at `u`, unit
extraction at `v`; `e u = Pi.single u 1`) admits a potential. This is the
equation that defines effective resistance in proposal step 5: `r` is
`f u − f v` for a solution `f`, whose uniqueness modulo constants comes
from `laplacian_mulVec_eq_zero_iff_exists_const`. -/
theorem exists_laplacian_mulVec_eq_single_sub_single (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hconn : (supportGraph A hA).Connected) (u v : V) :
    ∃ f : V → ℝ, (laplacian A).mulVec f
      = Pi.single u (1 : ℝ) - Pi.single v (1 : ℝ) := by
  refine exists_laplacian_mulVec_eq_of_sum_eq_zero A hA hnonneg hconn ?_
  simp only [Pi.sub_apply, Finset.sum_sub_distrib]
  have h1 : ∀ w : V, ∑ i, Pi.single w (1 : ℝ) i = 1 := by
    intro w
    simp
  rw [h1 u, h1 v, sub_self]

/-!
### λ₂: multiplicity pins and the variational characterization (proved)

Two counting facts about the sorted spectrum are the multiplicity pins
that make the second-eigenvalue variational principle provable in the
matrix world — the counterpart, in operator proofs, of restricting to
the orthogonal complement of the kernel:

- `evals_one_le_max_of_ne`: no two distinct eigenbasis indices both
  carry eigenvalues below the second sorted entry — at most one
  eigenvalue sits strictly below `evals 1`;
- `exists_ne_eigvalOf_of_evals_head_eq`: if the first two sorted
  entries coincide, that value is carried by two distinct eigenbasis
  indices — a repeated bottom entry has multiplicity at least two.

From these plus the expansion tools above, `lambda2_variational`
(Courant–Fischer for the second-smallest eigenvalue, over vectors
orthogonal to `onesVec`) is *proved*: for symmetric nonnegative weights
it was an axiom before 2026-08-18. The nonnegativity hypothesis is
load-bearing: with negative weights `onesVec` need not be a bottom
eigenvector, and the statement fails (refuted in QA on a negative
two-vertex fixture).
-/

section Lambda2Variational

/-- Length-of-filter bridge (private): filtering the sorted list of a
multiset selects exactly the multiset's filtered members. -/
private theorem filter_length_eq_card_filter {m : Multiset ℝ}
    {p : ℝ → Prop} [DecidablePred p] :
    (List.filter (fun x => decide (p x))
        (Multiset.sort (fun a b => a ≤ b) m)).length
      = Multiset.card (Multiset.filter p m) := by
  calc (List.filter (fun x => decide (p x))
        (Multiset.sort (fun a b => a ≤ b) m)).length
      = Multiset.card (Multiset.filter p
          (Multiset.sort (fun a b => a ≤ b) m)) := by
        rw [← Multiset.coe_card]
        rfl
    _ = Multiset.card (Multiset.filter p m) := by rw [Multiset.sort_eq]

/-- Filter-size workhorse (private): in a nondecreasing list whose
`k`-th entry exceeds `t`, at most `k` entries are at most `t`. -/
private theorem sorted_filter_le_length {l : List ℝ}
    (hs : l.Sorted (fun a b => a ≤ b)) {t : ℝ} {k : ℕ}
    (hk : k < l.length) (hgt : t < l.get ⟨k, hk⟩) :
    (l.filter (fun x => decide (x ≤ t))).length ≤ k := by
  have hfilter_nil : ∀ l' : List ℝ, (∀ x ∈ l', ¬ x ≤ t) →
      (l'.filter (fun x => decide (x ≤ t))) = [] := by
    intro l' h
    induction l' with
    | nil => rfl
    | cons a l'' ih =>
      have hn : ¬ (fun x => decide (x ≤ t)) a = true := by
        simpa using h a (by simp)
      rw [List.filter_cons_of_neg (p := fun x => decide (x ≤ t)) hn,
        ih (fun x hx => h x (by simp [hx]))]
  induction l generalizing k with
  | nil => simp at hk
  | cons a l' ih =>
    obtain ⟨hle, hs'⟩ := List.sorted_cons.1 hs
    match k with
    | 0 =>
      have ha : t < a := hgt
      have hn : ¬ (fun x => decide (x ≤ t)) a = true := by
        simp [not_le.2 ha]
      rw [List.filter_cons_of_neg (p := fun x => decide (x ≤ t)) hn,
        hfilter_nil l' (fun x hx => by
          have hax : a ≤ x := hle x hx
          intro hxt
          exact absurd hxt (by linarith))]
      simp
    | k'+1 =>
      have hk' : k' < l'.length := by
        simp only [List.length_cons] at hk
        omega
      have hgetsucc : (a :: l').get ⟨k' + 1, hk⟩
          = l'.get ⟨k', hk'⟩ := rfl
      by_cases hdec : (fun x => decide (x ≤ t)) a = true
      · rw [List.filter_cons_of_pos (p := fun x => decide (x ≤ t)) hdec,
          List.length_cons]
        have hrec := ih hs' hk' (by rw [← hgetsucc]; exact hgt)
        simp only [List.length_cons] at hrec ⊢
        omega
      · rw [List.filter_cons_of_neg (p := fun x => decide (x ≤ t)) hdec]
        have hrec := ih hs' hk' (by rw [← hgetsucc]; exact hgt)
        omega

/-- Head-repetition workhorse (private): if the first two entries of a
list equal `t`, at least two entries equal `t`. No sortedness needed. -/
private theorem filter_eq_two_of_head {l : List ℝ} {t : ℝ}
    (h1 : 1 < l.length)
    (h0 : l.get ⟨0, by omega⟩ = t) (h0' : l.get ⟨1, h1⟩ = t) :
    2 ≤ (l.filter (fun x => decide (x = t))).length := by
  match l with
  | [] => simp at h1
  | a :: l' =>
    have hlen' : 0 < l'.length := by
      simp only [List.length_cons] at h1; omega
    have ea : a = t := h0
    have eb : l'.get ⟨0, hlen'⟩ = t := h0'
    have hmem : t ∈ l' := by
      rw [← eb]
      exact List.get_mem l' 0 hlen'
    have hmemf : t ∈ List.filter (fun x => decide (x = t)) l' :=
      List.mem_filter.2 ⟨hmem, by simp⟩
    have hpos : 0 < (List.filter (fun x => decide (x = t)) l').length :=
      List.length_pos_of_mem hmemf
    have hp : (fun x => decide (x = t)) a = true := by simp [ea]
    rw [List.filter_cons_of_pos (p := fun x => decide (x = t)) hp]
    simp only [List.length_cons]
    omega

/-- **Multiplicity pin, upper form.** No two distinct eigenbasis
indices carry eigenvalues strictly below the second sorted spectrum
entry: `evals 1` is at most the larger of any two distinct indices'
eigenvalues. This is the matrix-world counterpart of "the eigenspace
below the second eigenvalue is at most one-dimensional"; it is what
forces Rayleigh quotients of vectors orthogonal to the kernel to
dominate `λ₂`. -/
theorem evals_one_le_max_of_ne {M : Matrix V V ℝ} (hM : M.IsSymm)
    (hcard : 2 ≤ Fintype.card V) (i₁ i₂ : V) (hne : i₁ ≠ i₂) :
    evals hM ⟨1, by omega⟩ ≤
      max (eigvalOf M hM i₁) (eigvalOf M hM i₂) := by
  set T : ℝ := max (eigvalOf M hM i₁) (eigvalOf M hM i₂) with hT
  -- the index-side filter has two members
  have hS : 1 < (Finset.univ.filter (fun i => eigvalOf M hM i ≤ T)).card := by
    rw [Finset.one_lt_card_iff]
    exact ⟨i₁, i₂,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, le_max_left _ _⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, le_max_right _ _⟩, hne⟩
  -- so the eigenvalue multiset has at least two entries ≤ T
  have hmcard : 2 ≤ Multiset.card
      (Multiset.filter (fun t => t ≤ T)
        ((Finset.univ : Finset V).val.map (eigvalOf M hM))) := by
    rw [Multiset.filter_map, Multiset.card_map, ← Finset.filter_val]
    simp only [Function.comp_def]
    have h1 : ((Finset.univ : Finset V).filter
        (fun i => eigvalOf M hM i ≤ T)).card
        = Multiset.card ((Finset.univ.filter
            (fun i => eigvalOf M hM i ≤ T) : Finset V)).val := rfl
    rw [← h1]
    omega
  -- transfer to the sorted list
  have hlen : 1 < (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map (eigvalOf M hM))).length := by
    rw [Multiset.length_sort, Multiset.card_map]
    have hu : ((Finset.univ : Finset V).val : Multiset V).card
        = Fintype.card V := by simp
    rw [hu]
    omega
  have hlfilt : 2 ≤ (List.filter (fun x => decide (x ≤ T))
      (Multiset.sort (fun a b => a ≤ b)
        ((Finset.univ : Finset V).val.map (eigvalOf M hM)))).length := by
    rw [filter_length_eq_card_filter]
    exact hmcard
  -- conclude
  by_contra hnot
  push_neg at hnot
  have hgt : T < (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map (eigvalOf M hM))).get
      ⟨1, by rw [Multiset.length_sort, Multiset.card_map]; simp; omega⟩ :=
    hnot
  have hle := sorted_filter_le_length
    (Multiset.sort_sorted (fun a b => a ≤ b) _) hlen hgt
  omega

/-- **Multiplicity pin, lower form.** If the first two sorted spectrum
entries coincide, that common value is carried by (at least) two
distinct eigenbasis indices. This is what produces a kernel vector
orthogonal to `onesVec` on graphs whose `λ₂` vanishes. -/
theorem exists_ne_eigvalOf_of_evals_head_eq {M : Matrix V V ℝ}
    (hM : M.IsSymm) (hcard : 2 ≤ Fintype.card V)
    (heq : evals hM ⟨0, by omega⟩ = evals hM ⟨1, by omega⟩) :
    ∃ i₁ i₂ : V, i₁ ≠ i₂ ∧
      eigvalOf M hM i₁ = evals hM ⟨1, by omega⟩ ∧
      eigvalOf M hM i₂ = evals hM ⟨1, by omega⟩ := by
  set t0 := evals hM ⟨1, by omega⟩ with ht0
  have hlen : 1 < (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map (eigvalOf M hM))).length := by
    rw [Multiset.length_sort, Multiset.card_map]
    have hu : ((Finset.univ : Finset V).val : Multiset V).card
        = Fintype.card V := by simp
    rw [hu]
    omega
  have hg0 : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map (eigvalOf M hM))).get
      ⟨0, by omega⟩ = t0 := heq
  have hg1 : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map (eigvalOf M hM))).get
      ⟨1, hlen⟩ = t0 := rfl
  have hfilt : 2 ≤ (List.filter
      (fun x => decide (x = t0))
      (Multiset.sort (fun a b => a ≤ b)
        ((Finset.univ : Finset V).val.map (eigvalOf M hM)))).length :=
    filter_eq_two_of_head hlen hg0 hg1
  -- transfer to the multiset and then to indices
  have hmcard : 2 ≤ Multiset.card (Multiset.filter
      (fun t => t = t0)
      ((Finset.univ : Finset V).val.map (eigvalOf M hM))) := by
    rw [← filter_length_eq_card_filter]
    exact hfilt
  have hS : 1 < (Finset.univ.filter
      (fun i => eigvalOf M hM i = t0)).card := by
    have h2 : (Finset.univ.filter (fun i => eigvalOf M hM i = t0)).card
        = Multiset.card (Multiset.filter (fun t => t = t0)
            ((Finset.univ : Finset V).val.map (eigvalOf M hM))) := by
      show Multiset.card (Finset.univ.filter
          (fun i => eigvalOf M hM i = t0) : Finset V).val = _
      rw [Finset.filter_val, Multiset.filter_map, Multiset.card_map]
      rfl
    rw [h2]
    exact hmcard
  obtain ⟨i₁, i₂, hm1, hm2, hne⟩ := Finset.one_lt_card_iff.1 hS
  exact ⟨i₁, i₂, hne, (Finset.mem_filter.1 hm1).2,
    (Finset.mem_filter.1 hm2).2⟩

/-- **Courant–Fischer for the second sorted eigenvalue — general
operator form, proved, no axioms.** For a symmetric matrix `M` that is
positive semidefinite and has `onesVec` in its kernel, `secondEval M` is
the infimum of the Rayleigh quotient of `M` over the nonzero vectors
orthogonal to `onesVec`.

This is the generalization of `lambda2_variational` from the
combinatorial Laplacian to any operator satisfying its two load-bearing
facts (`hpsd`, `hker`); the Laplacian instance follows by
`lambda2_eq_secondEval`, and the regular normalized Laplacian
`I - d⁻¹ • A` satisfies both under `d`-regularity (proved in
`GraphTheory.Cheeger`). `hpsd` is load-bearing here exactly as `hnonneg`
is there: without it the statement is false
(`old_lambda2_variational_refuted_QA`).

Route (matrix world, through the proved eigenbasis tools): the lower
bound `secondEval ≤ R(x)` comes from the spectral resolution of
`quadForm` plus the upper multiplicity pin (`evals_one_le_max_of_ne`: at
most one eigenvalue is below the second sorted entry, and its
eigenvector is parallel to `onesVec` by
`eigvecOf_ortho_onesVec_of_mulVec_eq_zero`, so it is invisible to
vectors orthogonal to `onesVec`); the upper bound exhibits witnesses —
the eigenvector at `evals 1` when the second entry is positive, and a
kernel vector orthogonal to `onesVec` produced by the lower multiplicity
pin (`exists_ne_eigvalOf_of_evals_head_eq`) when it is zero.

QA: exercised through `lambda2_variational` by the `Variational_QA`
lemmas in `Scaffold/QA/SpectralGraph/Variational_QA.lean`, and through
the Cheeger instance by `Scaffold/QA/SpectralGraph/Cheeger_QA.lean`. -/
theorem secondEval_variational {M : Matrix V V ℝ} (hM : M.IsSymm)
    (hpsd : ∀ x : V → ℝ, 0 ≤ quadForm M x) (hker : M *ᵥ onesVec = 0)
    (hcard : 2 ≤ Fintype.card V) :
    secondEval M hM hcard =
      sInf {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ Matrix.dotProduct x onesVec = 0 ∧
        rayleigh M x = r} := by
  classical
  have hL2evals : secondEval M hM hcard = evals hM ⟨1, by omega⟩ := rfl
  have hmunn : ∀ i : V, 0 ≤ eigvalOf M hM i := by
    intro i
    have h := hpsd (eigvecOf M hM i)
    rw [quadForm_eigvecOf_self hM i] at h
    exact h
  have hvv : ∀ i : V, Matrix.dotProduct (eigvecOf M hM i)
      (eigvecOf M hM i) = 1 := by
    intro i
    simpa [Matrix.dotProduct] using eigvecOf_inner M hM i i
  have hvne : ∀ i : V, eigvecOf M hM i ≠ 0 := by
    intro i h
    have h1 := hvv i
    rw [h, Matrix.dotProduct_zero] at h1
    exact zero_ne_one h1
  -- two distinct vertices exist
  obtain ⟨u, v, huv⟩ : ∃ u v : V, u ≠ v := by
    have h1 : 1 < (Finset.univ : Finset V).card := by
      rw [Finset.card_univ]
      omega
    obtain ⟨a, b, -, -, hab⟩ := Finset.one_lt_card_iff.1 h1
    exact ⟨a, b, hab⟩
  -- the constraint set is nonempty
  have hSne : {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧ rayleigh M x = r}.Nonempty := by
    have hpu : ∀ w : V, ∑ i, Pi.single w (1 : ℝ) i = 1 := by
      intro w
      simp
    refine ⟨rayleigh M (Pi.single u 1 - Pi.single v 1 : V → ℝ), ?_⟩
    show ∃ x : V → ℝ, x ≠ 0 ∧ Matrix.dotProduct x onesVec = 0 ∧
      rayleigh M x = rayleigh M (Pi.single u 1 - Pi.single v 1 : V → ℝ)
    refine ⟨Pi.single u 1 - Pi.single v 1, ?_, ?_, rfl⟩
    · intro h
      have h1 : (Pi.single u 1 - Pi.single v 1 : V → ℝ) u = 0 :=
        congrFun h u
      simp [Pi.sub_apply, Pi.single_apply, huv] at h1
    · simp only [Matrix.dotProduct, onesVec, Pi.sub_apply, mul_one,
        Finset.sum_sub_distrib]
      rw [hpu u, hpu v, sub_self]
  -- Step 1: every element of the set dominates the second sorted entry
  have hstep1 : ∀ x : V → ℝ, x ≠ 0 →
      Matrix.dotProduct x onesVec = 0 →
      secondEval M hM hcard ≤ rayleigh M x := by
    intro x hx0 hxorth
    have hDpos : 0 < Matrix.dotProduct x x := by
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hx0 (funext hcon)
      exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
        ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩
    -- the key nonnegativity: ∑ i, (μ i − λ₂) (v i ⬝ᵥ x)² ≥ 0
    have hkey : 0 ≤ ∑ i, (eigvalOf M hM i - secondEval M hM hcard)
        * (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2 := by
      by_cases hex : ∃ i₀ : V,
          eigvalOf M hM i₀ < secondEval M hM hcard
      · obtain ⟨i₀, hi₀⟩ := hex
        have hL2pos : 0 < secondEval M hM hcard :=
          lt_of_le_of_lt (hmunn i₀) hi₀
        -- onesVec has a nonzero eigencomponent; its eigenvalue is 0
        have honesne : (onesVec : V → ℝ) ≠ 0 := by
          intro h
          have h1 : (1 : ℝ) = 0 := congrFun h u
          simp at h1
        obtain ⟨j₀, hj₀c⟩ : ∃ j : V,
            Matrix.dotProduct (eigvecOf M hM j) onesVec ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          apply honesne
          funext a
          have hsum := eigvecOf_expansion_apply hM onesVec a
          simp [hcon] at hsum
          exact hsum.symm
        have hj0mu : eigvalOf M hM j₀ = 0 := by
          by_contra hmu
          exact hj₀c (eigvecOf_ortho_onesVec_of_mulVec_eq_zero hM hker hmu)
        -- j₀ = i₀, since two distinct indices cannot both be below λ₂
        have hj₀ : j₀ = i₀ := by
          by_contra hne
          have hmax := evals_one_le_max_of_ne hM hcard i₀ j₀
            (fun h' => hne h'.symm)
          rw [← hL2evals] at hmax
          have hbelow : max (eigvalOf M hM i₀)
              (eigvalOf M hM j₀) < secondEval M hM hcard := by
            rw [hj0mu]
            exact max_lt hi₀ hL2pos
          exact absurd hmax (not_le.2 hbelow)
        -- every other index dominates λ₂
        have hge : ∀ k : V, k ≠ i₀ →
            secondEval M hM hcard ≤ eigvalOf M hM k := by
          intro k hk
          by_contra hlt
          push_neg at hlt
          have hmax := evals_one_le_max_of_ne hM hcard i₀ k hk.symm
          rw [← hL2evals] at hmax
          exact absurd hmax (not_le.2 (max_lt hi₀ hlt))
        -- the coefficient of x along v i₀ vanishes
        have hc₀ : Matrix.dotProduct (eigvecOf M hM i₀) x = 0 := by
          -- every other index has positive eigenvalue, hence ⊥ onesVec
          have hmupos : ∀ j : V, j ≠ i₀ →
              eigvalOf M hM j ≠ 0 := by
            intro j hj hzero
            have hle := hge j hj
            rw [hzero] at hle
            exact absurd hle (not_le.2 hL2pos)
          -- so the expansion of onesVec is supported only at i₀
          have hexp : ∀ a : V, onesVec a
              = Matrix.dotProduct (eigvecOf M hM i₀) onesVec
                * eigvecOf M hM i₀ a := by
            intro a
            have hsum : ∑ j, Matrix.dotProduct
                (eigvecOf M hM j) onesVec
                * eigvecOf M hM j a = onesVec a :=
              eigvecOf_expansion_apply hM onesVec a
            rw [Finset.sum_eq_single i₀ (fun j _ hj => by
              have hzero := eigvecOf_ortho_onesVec_of_mulVec_eq_zero hM hker
                (hmupos j hj)
              rw [hzero, zero_mul])
              (fun hni => absurd (Finset.mem_univ i₀) hni)] at hsum
            exact hsum.symm
          have hdne : Matrix.dotProduct (eigvecOf M hM i₀)
              onesVec ≠ 0 := by
            rw [← hj₀]
            exact hj₀c
          -- 0 = x ⬝ᵥ onesVec = d * (x ⬝ᵥ v i₀) with d ≠ 0
          have hprod : Matrix.dotProduct (eigvecOf M hM i₀)
              onesVec * Matrix.dotProduct x
              (eigvecOf M hM i₀) = 0 := by
            have hx1 : Matrix.dotProduct x
                (fun a => Matrix.dotProduct
                    (eigvecOf M hM i₀) onesVec
                  * eigvecOf M hM i₀ a) = 0 :=
              (congrArg (Matrix.dotProduct x) (funext hexp)).symm.trans
                hxorth
            have hcalc : Matrix.dotProduct x
                (fun a => Matrix.dotProduct
                    (eigvecOf M hM i₀) onesVec
                  * eigvecOf M hM i₀ a)
                = Matrix.dotProduct (eigvecOf M hM i₀) onesVec
                  * Matrix.dotProduct x
                    (eigvecOf M hM i₀) := by
              simp only [Matrix.dotProduct]
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun a _ => by ring
            rw [← hcalc]
            exact hx1
          rw [Matrix.dotProduct_comm]
          exact (mul_eq_zero.1 hprod).resolve_left hdne
        -- assemble: the i₀-term vanishes, every other term is nonnegative
        rw [← Finset.add_sum_erase (Finset.univ : Finset V)
          (fun i => (eigvalOf M hM i - secondEval M hM hcard)
            * (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2)
          (Finset.mem_univ i₀), hc₀, zero_pow two_ne_zero, mul_zero,
          zero_add]
        exact Finset.sum_nonneg fun k hk =>
          mul_nonneg (sub_nonneg.2 (hge k (Finset.mem_erase.1 hk).1))
            (sq_nonneg _)
      · -- no eigenvalue below λ₂: every term is nonnegative
        refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ (sq_nonneg _)
        by_contra hlt
        push_neg at hlt
        exact hex ⟨k, by linarith⟩
    -- conclude λ₂ ≤ R(x) from the spectral resolution and Parseval
    have hQge : secondEval M hM hcard * Matrix.dotProduct x x
        ≤ quadForm M x := by
      rw [quadForm_eigvalOf hM x, dotProduct_eigvecOf hM x x,
        ← sub_nonneg, Finset.mul_sum, ← Finset.sum_sub_distrib]
      rw [Finset.sum_congr rfl fun i _ => show
        (eigvalOf M hM i
            * (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2
          - secondEval M hM hcard
            * (Matrix.dotProduct (eigvecOf M hM i) x
              * Matrix.dotProduct (eigvecOf M hM i) x))
        = (eigvalOf M hM i - secondEval M hM hcard)
          * (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2 from
        by ring]
      exact hkey
    rw [rayleigh, if_neg hx0]
    exact (le_div_iff₀ hDpos).2 hQge
  -- Step 2: some element of the set is at most λ₂
  have hSbdd : BddBelow {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧ rayleigh M x = r} :=
    ⟨secondEval M hM hcard, fun r hr => by
      obtain ⟨x, hx0, hxorth, hrx⟩ := hr
      rw [← hrx]
      exact hstep1 x hx0 hxorth⟩
  have hortho_pair : ∀ i j : V, i ≠ j →
      Matrix.dotProduct (eigvecOf M hM i)
        (eigvecOf M hM j) = 0 := by
    intro i j hij
    simpa [Matrix.dotProduct, hij] using eigvecOf_inner M hM i j
  have hmemupper : ∃ r ∈ {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧ rayleigh M x = r},
      r ≤ secondEval M hM hcard := by
    have hL2nn : 0 ≤ secondEval M hM hcard := by
      obtain ⟨i, hi⟩ := evals_mem_eigvalOf hM ⟨1, by omega⟩
      rw [hL2evals, hi]
      exact hmunn i
    rcases eq_or_lt_of_le hL2nn with h0 | hpos
    · -- λ₂ = 0: a kernel vector ⊥ onesVec exists, from the double bottom
      have he01 : evals hM ⟨1, by omega⟩ = 0 := by
        rw [← hL2evals]
        exact h0.symm
      have hev01 : evals hM ⟨0, by omega⟩ = evals hM ⟨1, by omega⟩ := by
        have h1 : evals hM ⟨0, by omega⟩ ≤ evals hM ⟨1, by omega⟩ :=
          evals_sorted hM (Fin.le_def.2 (Nat.le_succ 0))
        have h2 : 0 ≤ evals hM ⟨0, by omega⟩ := by
          obtain ⟨i, hi⟩ := evals_mem_eigvalOf hM ⟨0, by omega⟩
          rw [hi]
          exact hmunn i
        rw [he01] at h1 ⊢
        exact le_antisymm h1 h2
      obtain ⟨i₁, i₂, hne, hmu1, hmu2⟩ :=
        exists_ne_eigvalOf_of_evals_head_eq hM hcard hev01
      rw [he01] at hmu1 hmu2
      have hev₁ : M *ᵥ eigvecOf M hM i₁ = 0 := by
        have h : M *ᵥ eigvecOf M hM i₁
            = eigvalOf M hM i₁ • eigvecOf M hM i₁ :=
          (isHermitian_of_isSymm hM).mulVec_eigenvectorBasis i₁
        rw [hmu1, zero_smul] at h
        exact h
      have hev₂ : M *ᵥ eigvecOf M hM i₂ = 0 := by
        have h : M *ᵥ eigvecOf M hM i₂
            = eigvalOf M hM i₂ • eigvecOf M hM i₂ :=
          (isHermitian_of_isSymm hM).mulVec_eigenvectorBasis i₂
        rw [hmu2, zero_smul] at h
        exact h
      by_cases hortho1 : Matrix.dotProduct (eigvecOf M hM i₁)
          onesVec = 0
      · refine ⟨rayleigh M (eigvecOf M hM i₁),
          ⟨eigvecOf M hM i₁, hvne i₁, hortho1, rfl⟩, ?_⟩
        rw [rayleigh, if_neg (hvne i₁), quadForm, hev₁,
          Matrix.dotProduct_zero, zero_div]
        exact h0.le
      · -- cross combination: orthogonal to onesVec and in the kernel
        refine ⟨rayleigh M
            (Matrix.dotProduct (eigvecOf M hM i₂) onesVec
              • eigvecOf M hM i₁
              - Matrix.dotProduct (eigvecOf M hM i₁) onesVec
                • eigvecOf M hM i₂),
          ⟨_, ?_, ?_, rfl⟩, ?_⟩
        · intro h
          have h2 : Matrix.dotProduct (eigvecOf M hM i₂)
              (Matrix.dotProduct (eigvecOf M hM i₂) onesVec
                • eigvecOf M hM i₁
                - Matrix.dotProduct (eigvecOf M hM i₁) onesVec
                  • eigvecOf M hM i₂) = 0 := by
            rw [h, Matrix.dotProduct_zero]
          rw [Matrix.dotProduct_sub, Matrix.dotProduct_smul,
            Matrix.dotProduct_smul, smul_eq_mul, smul_eq_mul,
            hortho_pair i₂ i₁ (Ne.symm hne), hvv i₂, mul_zero] at h2
          simp at h2
          exact absurd (by linarith) hortho1
        · rw [Matrix.sub_dotProduct, Matrix.smul_dotProduct,
            Matrix.smul_dotProduct, smul_eq_mul, smul_eq_mul]
          ring
        · have hLw : M *ᵥ
              (Matrix.dotProduct (eigvecOf M hM i₂) onesVec
                • eigvecOf M hM i₁
                - Matrix.dotProduct (eigvecOf M hM i₁) onesVec
                  • eigvecOf M hM i₂) = 0 := by
            rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
              hev₁, hev₂, smul_zero, smul_zero, sub_zero]
          rw [rayleigh]
          split
          · exact h0.le
          · rw [quadForm, hLw, Matrix.dotProduct_zero, zero_div]
            exact h0.le
    · -- 0 < λ₂: the eigenvector at the second sorted entry is ⊥ onesVec
      obtain ⟨i₂, hi₂⟩ := evals_mem_eigvalOf hM ⟨1, by omega⟩
      have hmui2 : eigvalOf M hM i₂
          = secondEval M hM hcard := by
        rw [hL2evals]
        exact hi₂.symm
      refine ⟨secondEval M hM hcard,
        ⟨eigvecOf M hM i₂, hvne i₂,
          eigvecOf_ortho_onesVec_of_mulVec_eq_zero hM hker
            (by rw [hmui2]; exact ne_of_gt hpos),
          ?_⟩, le_refl _⟩
      rw [rayleigh, if_neg (hvne i₂), quadForm_eigvecOf_self, hvv i₂,
        div_one]
      exact hmui2
  -- assemble both sides
  refine le_antisymm ?_ ?_
  · refine le_csInf hSne ?_
    rintro r ⟨x, hx0, hxorth, hrx⟩
    rw [← hrx]
    exact hstep1 x hx0 hxorth
  · obtain ⟨r, hrmem, hrle⟩ := hmemupper
    exact le_trans (csInf_le hSbdd hrmem) hrle

/-- Consumer form of `secondEval_variational`: every admissible test
vector bounds the second sorted eigenvalue from above,
`secondEval ≤ R(x)` for `x ≠ 0` with `x ⊥ onesVec`. This one-sided form
is what test-vector arguments consume (the Cheeger easy direction in
`GraphTheory.Cheeger`); it needs no infimum manipulation at the use
site. -/
theorem secondEval_le_rayleigh {M : Matrix V V ℝ} (hM : M.IsSymm)
    (hpsd : ∀ x : V → ℝ, 0 ≤ quadForm M x) (hker : M *ᵥ onesVec = 0)
    (hcard : 2 ≤ Fintype.card V) {x : V → ℝ} (hx0 : x ≠ 0)
    (hxorth : Matrix.dotProduct x onesVec = 0) :
    secondEval M hM hcard ≤ rayleigh M x := by
  rw [secondEval_variational hM hpsd hker hcard]
  refine csInf_le ?_ ⟨x, hx0, hxorth, rfl⟩
  -- PSD makes the constraint set bounded below by 0
  refine ⟨0, fun r hr => ?_⟩
  obtain ⟨y, hy0, -, hyr⟩ := hr
  rw [← hyr, rayleigh, if_neg hy0]
  have hypos : 0 < Matrix.dotProduct y y := by
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hy0 (funext hcon)
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
      ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩
  exact div_nonneg (hpsd y) hypos.le

/-- **General-kernel Rayleigh domination** (the consumer form of the
Courant–Fischer principle at an arbitrary kernel vector): every nonzero
test vector orthogonal to a *nonzero kernel vector* `w` of a PSD
symmetric matrix bounds the second sorted eigenvalue from above,
`secondEval ≤ R(x)`.

The delivered `secondEval_le_rayleigh` is the `w = onesVec` instance,
sufficient for every operator whose kernel contains the constants (the
combinatorial and regular-normalized Laplacians). Operators with a
non-constant kernel vector need this general form: the symmetric
normalized Laplacian `L_sym = 1 − D^{-1/2} A D^{-1/2}` of an *irregular*
graph is killed by `√D · onesVec`, not by `onesVec`, and the irregular
Cheeger upper bound (`GraphTheory.VariationalTransfer`, 2026-08-25) is
its first consumer.

Proof (the `secondEval_variational` Step-1 argument re-run at `w`): the
eigenbasis expansion of the PSD kernel equation confines `w`'s
eigencomponents to the zero eigenspace (`eigvecOf_ortho_of_mulVec_eq_zero`);
when some eigenvalue is below `λ₂` it is the unique zero-eigenvalue index,
`w`'s expansion is supported there, and `x ⊥ w` kills exactly that
eigencomponent of `x`; otherwise every eigenvalue dominates `λ₂`. Either
way the spectral resolution of the quadratic form (`quadForm_eigvalOf`)
plus Parseval gives `λ₂ · (x ⬝ᵥ x) ≤ xᵀ M x`.

QA: exercised on genuinely irregular input by
`Scaffold/QA/SpectralGraph/IrregularCheeger_QA.lean` (the P₃ eigenpair
witness pins `secondEval (L_sym) ≤ 1` through this lemma at a vector
*not* orthogonal to `onesVec`), and fenced by the PSD-drop refutation
there (`icvQ_psd_fence`: `diag(−1, 0)` with `w = e₁`, `x = e₀` makes the
hypothesis-free conclusion `0 ≤ −1` false). -/
theorem secondEval_le_rayleigh_of_ker {M : Matrix V V ℝ} (hM : M.IsSymm)
    (hpsd : ∀ x : V → ℝ, 0 ≤ quadForm M x) {w : V → ℝ} (hwne : w ≠ 0)
    (hker : M *ᵥ w = 0) (hcard : 2 ≤ Fintype.card V) {x : V → ℝ}
    (hx0 : x ≠ 0) (hxorth : Matrix.dotProduct x w = 0) :
    secondEval M hM hcard ≤ rayleigh M x := by
  have hstep1 : ∀ x : V → ℝ, x ≠ 0 →
      Matrix.dotProduct x w = 0 →
      secondEval M hM hcard ≤ rayleigh M x := by
    intro x hx0 hxorth
    have hDpos : 0 < Matrix.dotProduct x x := by
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hx0 (funext hcon)
      exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
        ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩
    -- the key nonnegativity: ∑ i, (μ i − λ₂) (v i ⬝ᵥ x)² ≥ 0
    have hkey : 0 ≤ ∑ i, (eigvalOf M hM i - secondEval M hM hcard)
        * (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2 := by
      by_cases hex : ∃ i₀ : V,
          eigvalOf M hM i₀ < secondEval M hM hcard
      · obtain ⟨i₀, hi₀⟩ := hex
        have hmunn_i₀ : 0 ≤ eigvalOf M hM i₀ := by
          have h := hpsd (eigvecOf M hM i₀)
          rw [quadForm_eigvecOf_self hM i₀] at h
          exact h
        have hL2pos : 0 < secondEval M hM hcard :=
          lt_of_le_of_lt hmunn_i₀ hi₀
        -- w has a nonzero eigencomponent; its eigenvalue is 0
        obtain ⟨j₀, hj₀c⟩ : ∃ j : V,
            Matrix.dotProduct (eigvecOf M hM j) w ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          apply hwne
          funext a
          have hsum := eigvecOf_expansion_apply hM w a
          simp [hcon] at hsum
          exact hsum.symm
        have hj0mu : eigvalOf M hM j₀ = 0 := by
          by_contra hmu
          exact hj₀c (eigvecOf_ortho_of_mulVec_eq_zero hM hker hmu)
        have hL2evals : secondEval M hM hcard
            = evals hM ⟨1, by omega⟩ := rfl
        -- j₀ = i₀, since two distinct indices cannot both be below λ₂
        have hj₀ : j₀ = i₀ := by
          by_contra hne
          have hmax := evals_one_le_max_of_ne hM hcard i₀ j₀
            (fun h' => hne h'.symm)
          rw [← hL2evals] at hmax
          have hbelow : max (eigvalOf M hM i₀)
              (eigvalOf M hM j₀) < secondEval M hM hcard := by
            rw [hj0mu]
            exact max_lt hi₀ hL2pos
          exact absurd hmax (not_le.2 hbelow)
        -- every other index dominates λ₂
        have hge : ∀ k : V, k ≠ i₀ →
            secondEval M hM hcard ≤ eigvalOf M hM k := by
          intro k hk
          by_contra hlt
          push_neg at hlt
          have hmax := evals_one_le_max_of_ne hM hcard i₀ k hk.symm
          rw [← hL2evals] at hmax
          exact absurd hmax (not_le.2 (max_lt hi₀ hlt))
        -- the coefficient of x along v i₀ vanishes
        have hc₀ : Matrix.dotProduct (eigvecOf M hM i₀) x = 0 := by
          -- every other index has positive eigenvalue, hence ⊥ w
          have hmupos : ∀ j : V, j ≠ i₀ →
              eigvalOf M hM j ≠ 0 := by
            intro j hj hzero
            have hle := hge j hj
            rw [hzero] at hle
            exact absurd hle (not_le.2 hL2pos)
          -- so the expansion of w is supported only at i₀
          have hexp : ∀ a : V, w a
              = Matrix.dotProduct (eigvecOf M hM i₀) w
                * eigvecOf M hM i₀ a := by
            intro a
            have hsum : ∑ j, Matrix.dotProduct
                (eigvecOf M hM j) w
                * eigvecOf M hM j a = w a :=
              eigvecOf_expansion_apply hM w a
            rw [Finset.sum_eq_single i₀ (fun j _ hj => by
              have hzero := eigvecOf_ortho_of_mulVec_eq_zero hM hker
                (hmupos j hj)
              rw [hzero, zero_mul])
              (fun hni => absurd (Finset.mem_univ i₀) hni)] at hsum
            exact hsum.symm
          have hdne : Matrix.dotProduct (eigvecOf M hM i₀)
              w ≠ 0 := by
            rw [← hj₀]
            exact hj₀c
          -- 0 = x ⬝ᵥ w = d * (x ⬝ᵥ v i₀) with d ≠ 0
          have hprod : Matrix.dotProduct (eigvecOf M hM i₀)
              w * Matrix.dotProduct x
              (eigvecOf M hM i₀) = 0 := by
            have hx1 : Matrix.dotProduct x
                (fun a => Matrix.dotProduct
                    (eigvecOf M hM i₀) w
                  * eigvecOf M hM i₀ a) = 0 :=
              (congrArg (Matrix.dotProduct x) (funext hexp)).symm.trans
                hxorth
            have hcalc : Matrix.dotProduct x
                (fun a => Matrix.dotProduct
                    (eigvecOf M hM i₀) w
                  * eigvecOf M hM i₀ a)
                = Matrix.dotProduct (eigvecOf M hM i₀) w
                  * Matrix.dotProduct x
                    (eigvecOf M hM i₀) := by
              simp only [Matrix.dotProduct]
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun a _ => by ring
            rw [← hcalc]
            exact hx1
          rw [Matrix.dotProduct_comm]
          exact (mul_eq_zero.1 hprod).resolve_left hdne
        -- assemble: the i₀-term vanishes, every other term is nonnegative
        rw [← Finset.add_sum_erase (Finset.univ : Finset V)
          (fun i => (eigvalOf M hM i - secondEval M hM hcard)
            * (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2)
          (Finset.mem_univ i₀), hc₀, zero_pow two_ne_zero, mul_zero,
          zero_add]
        exact Finset.sum_nonneg fun k hk =>
          mul_nonneg (sub_nonneg.2 (hge k (Finset.mem_erase.1 hk).1))
            (sq_nonneg _)
      · -- no eigenvalue below λ₂: every term is nonnegative
        refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ (sq_nonneg _)
        by_contra hlt
        push_neg at hlt
        exact hex ⟨k, by linarith⟩
    -- conclude λ₂ ≤ R(x) from the spectral resolution and Parseval
    have hQge : secondEval M hM hcard * Matrix.dotProduct x x
        ≤ quadForm M x := by
      rw [quadForm_eigvalOf hM x, dotProduct_eigvecOf hM x x,
        ← sub_nonneg, Finset.mul_sum, ← Finset.sum_sub_distrib]
      rw [Finset.sum_congr rfl fun i _ => show
        (eigvalOf M hM i
            * (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2
          - secondEval M hM hcard
            * (Matrix.dotProduct (eigvecOf M hM i) x
              * Matrix.dotProduct (eigvecOf M hM i) x))
        = (eigvalOf M hM i - secondEval M hM hcard)
          * (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2 from
        by ring]
      exact hkey
    rw [rayleigh, if_neg hx0]
    exact (le_div_iff₀ hDpos).2 hQge
  exact hstep1 x hx0 hxorth

/-- **Variational (Courant–Fischer) characterization of the algebraic
connectivity — proved, no axioms.** For symmetric nonnegative weights,
`λ₂` is the infimum of the Laplacian Rayleigh quotient over nonzero
vectors orthogonal to `onesVec`.

Source (classical background; this is a proof, not an admission):
- Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., Cambridge
  University Press, 2013, Section 4.2 (Courant–Fischer).
- Chung, F. R. K., "Spectral Graph Theory", CBMS 92, AMS, 1997,
  Section 1.3 (Laplacian form).

Statement differences: Rayleigh quotients use Scaffold's `rayleigh`
(total function, junk value `0` at the zero vector, excluded by the
`x ≠ 0` side condition), and orthogonality is the dot product with
`onesVec`. The hypothesis `hnonneg` is load-bearing and was missing in
the pre-2026-08-18 axiom shape, which is false for negative weights
(see `old_lambda2_variational_refuted_QA` in
`Scaffold/QA/SpectralGraph/Variational_QA.lean`).

Proof: the instance at `M = laplacian A` of the general operator form
`secondEval_variational` (same file), whose two hypotheses — PSD and
`onesVec` in the kernel — are `laplacian_psd` and
`laplacian_ones_in_kernel` here. The general form's proof is the
matrix-world eigenbasis argument recorded there.

QA: exercised by the `Variational_QA` refutation and instantiation
lemmas in `Scaffold/QA/SpectralGraph/Variational_QA.lean`. -/
theorem lambda2_variational (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hcard : 2 ≤ Fintype.card V) :
    lambda2 A hA hcard =
      sInf {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ Matrix.dotProduct x onesVec = 0 ∧
        rayleigh (laplacian A) x = r} := by
  rw [lambda2_eq_secondEval]
  exact secondEval_variational (laplacian_symmetric A hA)
    (laplacian_psd A hA hnonneg) (laplacian_ones_in_kernel A) hcard

end Lambda2Variational

section CourantFischer

/-!
### General Courant–Fischer min–max

The `k`-th sorted eigenvalue of *any* real symmetric matrix, at every
index `k`, as a subspace-constrained optimization. This generalizes the
fixed-index-1 engine of `secondEval_variational` (which additionally
assumes PSD and a known kernel vector): no positivity, kernel, or
graph-side hypothesis is needed here, only symmetry.

The min–max theorem is delivered in three forms:
`exists_submodule_forall_rayleigh_le` (an optimal `(k+1)`-dimensional
subspace exists), `exists_ne_mem_rayleigh_ge_of_finrank_eq` (every
`(k+1)`-dimensional competitor contains a test vector whose Rayleigh
quotient is at least `evals k`), and the packaged infimum equation
`evals_min_max`.
-/

/-- Empty-filter helper (private): a list containing no entry strictly
below the threshold filters to the empty list. -/
private theorem filter_nil_of_forall_lt {t : ℝ} {l : List ℝ}
    (h : ∀ x ∈ l, ¬ x < t) :
    l.filter (fun x => decide (x < t)) = [] := by
  induction l with
  | nil => rfl
  | cons b l' ih =>
    rw [List.filter_cons_of_neg (p := fun x => decide (x < t))
      (by simpa using h b (by simp))]
    exact ih (fun x hx => h x (by simp [hx]))

/-- Head-threshold workhorse (private): in a nondecreasing list, the
first `k+1` entries are all at most the `k`-th entry, so at least `k+1`
entries pass the filter `· ≤ l.get k`. -/
private theorem sorted_filter_ge_length_of_le_get {l : List ℝ}
    (hs : l.Sorted (fun a b => a ≤ b)) {k : ℕ} (hk : k < l.length) :
    k + 1 ≤ (l.filter (fun x => decide (x ≤ l.get ⟨k, hk⟩))).length := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l' ih =>
    obtain ⟨hle, hs'⟩ := List.sorted_cons.1 hs
    match k with
    | 0 =>
      have hth : (a :: l').get ⟨0, hk⟩ = a := rfl
      simp only [hth]
      rw [List.filter_cons_of_pos (p := fun x => decide (x ≤ a)) (by simp)]
      simp only [List.length_cons]
      omega
    | k'+1 =>
      have hk' : k' < l'.length := by
        simp only [List.length_cons] at hk
        omega
      have hgetsucc : (a :: l').get ⟨k' + 1, hk⟩
          = l'.get ⟨k', hk'⟩ := rfl
      have hale : a ≤ l'.get ⟨k', hk'⟩ := hle _ (List.get_mem l' k' hk')
      simp only [hgetsucc]
      rw [List.filter_cons_of_pos (p := fun x => decide (x ≤ l'.get ⟨k', hk'⟩))
        (by simp only [hgetsucc]; exact decide_eq_true hale)]
      have hrec := ih hs' hk'
      simp only [List.length_cons] at hrec ⊢
      omega

/-- Strict-threshold workhorse (private): in a nondecreasing list, at
most `k` entries are strictly below the `k`-th entry. -/
private theorem sorted_filter_lt_length_of_eq_get {l : List ℝ}
    (hs : l.Sorted (fun a b => a ≤ b)) {k : ℕ} (hk : k < l.length) :
    (l.filter (fun x => decide (x < l.get ⟨k, hk⟩))).length ≤ k := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l' ih =>
    obtain ⟨hle, hs'⟩ := List.sorted_cons.1 hs
    match k with
    | 0 =>
      have hth : (a :: l').get ⟨0, hk⟩ = a := rfl
      simp only [hth]
      rw [List.filter_cons_of_neg (p := fun x => decide (x < a)) (by simp),
        filter_nil_of_forall_lt (t := a) (fun x hx => by
          have hax : a ≤ x := hle x hx
          intro hxt
          exact absurd hxt (by linarith))]
      simp
    | k'+1 =>
      have hk' : k' < l'.length := by
        simp only [List.length_cons] at hk
        omega
      have hgetsucc : (a :: l').get ⟨k' + 1, hk⟩
          = l'.get ⟨k', hk'⟩ := rfl
      simp only [hgetsucc]
      have hrec := ih hs' hk'
      by_cases hdec : (fun x => decide (x < l'.get ⟨k', hk'⟩)) a = true
      · rw [List.filter_cons_of_pos
          (p := fun x => decide (x < l'.get ⟨k', hk'⟩)) hdec]
        simp only [List.length_cons]
        omega
      · rw [List.filter_cons_of_neg
          (p := fun x => decide (x < l'.get ⟨k', hk'⟩)) hdec]
        omega

/-- Multiset-transfer bridge (private): filtering the eigenvalue
multiset and counting equals filtering the eigenbasis index set. -/
private theorem card_filter_eigvalOf_eq {M : Matrix V V ℝ} {hM : M.IsSymm}
    {p : ℝ → Prop} [DecidablePred p] :
    (Finset.univ.filter fun i => p (eigvalOf M hM i)).card =
      Multiset.card (Multiset.filter p
        ((Finset.univ : Finset V).val.map (eigvalOf M hM))) := by
  show Multiset.card
      ((Finset.univ.filter fun i => p (eigvalOf M hM i) : Finset V)).val = _
  rw [Finset.filter_val, Multiset.filter_map, Multiset.card_map]
  rfl

/-- **Multiplicity pin at a general index, upper form.** Fewer than `k+1`
eigenbasis indices carry eigenvalues strictly below the `k`-th sorted
entry: the strict sub-level set of the index map has at most `k`
elements. Generalizes `evals_one_le_max_of_ne` (the `k = 1` two-index
form) to every index. -/
theorem card_filter_eigvalOf_lt_evals_le {M : Matrix V V ℝ} (hM : M.IsSymm)
    (k : Fin (Fintype.card V)) :
    (Finset.univ.filter fun i => eigvalOf M hM i < evals hM k).card ≤ (k : ℕ) := by
  rw [card_filter_eigvalOf_eq (p := fun t => t < evals hM k),
    ← filter_length_eq_card_filter (p := fun t => t < evals hM k)]
  exact sorted_filter_lt_length_of_eq_get
    (Multiset.sort_sorted (fun a b => a ≤ b) _)
    (by rw [length_sortedEvals hM]; exact k.isLt)

/-- **Multiplicity pin at a general index, lower form.** At least `k+1`
eigenbasis indices carry eigenvalues at most the `k`-th sorted entry. -/
theorem succ_le_card_filter_eigvalOf_le {M : Matrix V V ℝ} (hM : M.IsSymm)
    (k : Fin (Fintype.card V)) :
    (k : ℕ) + 1 ≤
      (Finset.univ.filter fun i => eigvalOf M hM i ≤ evals hM k).card := by
  rw [card_filter_eigvalOf_eq (p := fun t => t ≤ evals hM k),
    ← filter_length_eq_card_filter (p := fun t => t ≤ evals hM k)]
  exact sorted_filter_ge_length_of_le_get
    (Multiset.sort_sorted (fun a b => a ≤ b) _)
    (by rw [length_sortedEvals hM]; exact k.isLt)

/-- Pairwise orthonormality in dot-product form: the coordinate dot
product of the `i`-th and `j`-th eigenvectors is `δᵢⱼ`. This is
`eigvecOf_inner` read through `Matrix.dotProduct`. -/
theorem eigvecOf_dotProduct {M : Matrix V V ℝ} (hM : M.IsSymm) (i j : V) :
    Matrix.dotProduct (eigvecOf M hM i) (eigvecOf M hM j)
      = if i = j then 1 else 0 := by
  simpa [Matrix.dotProduct] using eigvecOf_inner M hM i j

/-- Any subfamily of the orthonormal eigenbasis, indexed by the coercions
of a finset, is linearly independent. -/
theorem linearIndependent_eigvecOf_finset {M : Matrix V V ℝ} (hM : M.IsSymm)
    (t : Finset V) :
    LinearIndependent ℝ (fun i : {x // x ∈ t} => eigvecOf M hM i.1) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hdot : Matrix.dotProduct (eigvecOf M hM j.1)
      (∑ i, g i • eigvecOf M hM i.1) = 0 := by
    rw [hg, Matrix.dotProduct_zero]
  have hexpand : Matrix.dotProduct (eigvecOf M hM j.1)
      (∑ i, g i • eigvecOf M hM i.1)
      = ∑ i, g i * Matrix.dotProduct (eigvecOf M hM j.1)
          (eigvecOf M hM i.1) := by
    calc Matrix.dotProduct (eigvecOf M hM j.1) (∑ i, g i • eigvecOf M hM i.1)
        = ∑ a, eigvecOf M hM j.1 a * ∑ i, g i * eigvecOf M hM i.1 a := by
          simp only [Matrix.dotProduct, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul]
      _ = ∑ a, ∑ i, eigvecOf M hM j.1 a * (g i * eigvecOf M hM i.1 a) := by
          simp only [Finset.mul_sum]
      _ = ∑ i, ∑ a, eigvecOf M hM j.1 a * (g i * eigvecOf M hM i.1 a) :=
          Finset.sum_comm
      _ = ∑ i, g i * ∑ a, eigvecOf M hM j.1 a * eigvecOf M hM i.1 a := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
      _ = ∑ i, g i * Matrix.dotProduct (eigvecOf M hM j.1)
            (eigvecOf M hM i.1) := rfl
  rw [hexpand] at hdot
  simp only [eigvecOf_dotProduct hM] at hdot
  rw [Finset.sum_eq_single j (fun i _ hij => by
      have hne : j.1 ≠ i.1 := fun h => hij (Subtype.ext h.symm)
      simp only [mul_ite, mul_one, mul_zero, if_neg hne])
    (fun hni => absurd (Finset.mem_univ j) hni)] at hdot
  simpa using hdot

/-- The span of any subfamily of the orthonormal eigenbasis has dimension
exactly the size of the index finset. -/
theorem finrank_span_eigvecOf_finset {M : Matrix V V ℝ} (hM : M.IsSymm)
    (t : Finset V) :
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range fun i : {x // x ∈ t} => eigvecOf M hM i.1)) = t.card := by
  rw [finrank_span_eq_card (linearIndependent_eigvecOf_finset hM t)]
  simp

omit [DecidableEq V] in
/-- Positivity idiom: the dot product of a nonzero real vector with
itself is positive. Public since the Rayleigh-sandwich consumers in
`GraphTheory.Expander` (and any division-form variational bound) need
the same denominator fact. -/
theorem dotProduct_self_pos {x : V → ℝ} (hx : x ≠ 0) :
    0 < Matrix.dotProduct x x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hx (funext hcon)
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
    ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩

/-- **Component-form Rayleigh upper bound.** If every eigencomponent of
`x` attached to an eigenvalue strictly above `evals hM k` vanishes, then
`R(x) ≤ evals hM k`: the Rayleigh quotient is an eigenvalue-weighted
average of the squared eigencomponents
(`quadForm_eigvalOf`, `dotProduct_eigvecOf`), and every surviving term
is weighted by an eigenvalue at most `evals hM k`. -/
theorem rayleigh_le_evals_of_forall_dotProduct_eq_zero {M : Matrix V V ℝ}
    (hM : M.IsSymm) (k : Fin (Fintype.card V)) {x : V → ℝ} (hx0 : x ≠ 0)
    (hx : ∀ i : V, evals hM k < eigvalOf M hM i →
      Matrix.dotProduct (eigvecOf M hM i) x = 0) :
    rayleigh M x ≤ evals hM k := by
  have hDpos : 0 < Matrix.dotProduct x x := dotProduct_self_pos hx0
  rw [rayleigh, if_neg hx0, div_le_iff₀ hDpos]
  have hq : quadForm M x
      = ∑ i, eigvalOf M hM i
        * (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2 :=
    quadForm_eigvalOf hM x
  have hD : Matrix.dotProduct x x
      = ∑ i, (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2 := by
    rw [dotProduct_eigvecOf hM x x]
    exact Finset.sum_congr rfl fun i _ => (pow_two _).symm
  rw [hq, hD, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hμ : eigvalOf M hM i ≤ evals hM k
  · exact mul_le_mul_of_nonneg_right hμ (sq_nonneg _)
  · push_neg at hμ
    rw [hx i hμ]
    simp

/-- **Component-form Rayleigh lower bound.** If every eigencomponent of
`x` attached to an eigenvalue strictly below `evals hM k` vanishes, then
`evals hM k ≤ R(x)`: the weighted average only mixes eigenvalues at
least `evals hM k`. -/
theorem evals_le_rayleigh_of_forall_dotProduct_eq_zero {M : Matrix V V ℝ}
    (hM : M.IsSymm) (k : Fin (Fintype.card V)) {x : V → ℝ} (hx0 : x ≠ 0)
    (hx : ∀ i : V, eigvalOf M hM i < evals hM k →
      Matrix.dotProduct (eigvecOf M hM i) x = 0) :
    evals hM k ≤ rayleigh M x := by
  have hDpos : 0 < Matrix.dotProduct x x := dotProduct_self_pos hx0
  rw [rayleigh, if_neg hx0, le_div_iff₀ hDpos]
  have hq : quadForm M x
      = ∑ i, eigvalOf M hM i
        * (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2 :=
    quadForm_eigvalOf hM x
  have hD : Matrix.dotProduct x x
      = ∑ i, (Matrix.dotProduct (eigvecOf M hM i) x) ^ 2 := by
    rw [dotProduct_eigvecOf hM x x]
    exact Finset.sum_congr rfl fun i _ => (pow_two _).symm
  rw [hq, hD, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hμ : evals hM k ≤ eigvalOf M hM i
  · exact mul_le_mul_of_nonneg_right hμ (sq_nonneg _)
  · push_neg at hμ
    rw [hx i hμ]
    simp

/-- Orthogonality to a span of eigenbasis vectors: a vector in the span
of the eigenbasis vectors indexed by `t` has vanishing eigencomponents
outside `t`. The dot product with a fixed eigenvector is a linear
functional, so its kernel contains the span whenever it contains the
generators. -/
theorem dotProduct_eigvecOf_eq_zero_of_mem_span {M : Matrix V V ℝ}
    (hM : M.IsSymm) (t : Finset V) {j : V} (hj : j ∉ t) {x : V → ℝ}
    (hx : x ∈ Submodule.span ℝ
      (Set.range fun i : {y // y ∈ t} => eigvecOf M hM i.1)) :
    Matrix.dotProduct (eigvecOf M hM j) x = 0 := by
  classical
  have hspan_le : Submodule.span ℝ
      (Set.range fun i : {y // y ∈ t} => eigvecOf M hM i.1)
      ≤ LinearMap.ker
        ({ toFun := fun y => Matrix.dotProduct (eigvecOf M hM j) y
           map_add' := fun y z => Matrix.dotProduct_add _ _ _
           map_smul' := fun c y => Matrix.dotProduct_smul _ _ _ } :
          (V → ℝ) →ₗ[ℝ] ℝ) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine LinearMap.mem_ker.2 ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [eigvecOf_dotProduct hM j i.1, if_neg (fun h => hj (by rw [h]; exact i.2))]
  have hxker := hspan_le hx
  rwa [LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk] at hxker

/-- **Courant–Fischer, existence direction.** There exists a subspace of
dimension exactly `k + 1` on which every Rayleigh quotient is at most
`evals hM k`: the span of any `k + 1` eigenbasis vectors drawn from the
at-most-threshold set `succ_le_card_filter_eigvalOf_le` (extracted with
`Finset.exists_smaller_set`), whose dimension is the index count by
orthonormality (`finrank_span_eigvecOf_finset`) and whose members have
no eigencomponents strictly above the threshold
(`dotProduct_eigvecOf_eq_zero_of_mem_span`), forcing the eigenvalue
weighted average `R(x)` down to `evals hM k`. -/
theorem exists_submodule_forall_rayleigh_le {M : Matrix V V ℝ} (hM : M.IsSymm)
    (k : Fin (Fintype.card V)) :
    ∃ W : Submodule ℝ (V → ℝ), Module.finrank ℝ W = (k : ℕ) + 1 ∧
      ∀ x ∈ W, x ≠ 0 → rayleigh M x ≤ evals hM k := by
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq
    (n := (k : ℕ) + 1) (succ_le_card_filter_eigvalOf_le hM k)
  refine ⟨Submodule.span ℝ
      (Set.range fun i : {y // y ∈ t} => eigvecOf M hM i.1),
    ?_, ?_⟩
  · rw [finrank_span_eigvecOf_finset hM t]
    exact htc
  · intro x hx hx0
    refine rayleigh_le_evals_of_forall_dotProduct_eq_zero hM k hx0 ?_
    intro i hi
    exact dotProduct_eigvecOf_eq_zero_of_mem_span hM t
      (fun hmem => absurd hi
        (not_lt.2 (Finset.mem_filter.1 (hts hmem)).2)) hx

/-- **Courant–Fischer, competitor direction.** Every subspace `W` of
dimension `k + 1` contains a nonzero test vector whose Rayleigh quotient
is at least `evals hM k`. The tail eigenspace — the span of the
eigenbasis vectors with eigenvalue at least `evals hM k` — has dimension
`n - (at most k)` by the strict multiplicity pin, so
`dim W + dim T ≥ (k + 1) + (n - k) > n`, and the dimension formula
forces `W ∩ T` to contain a nonzero vector: a member of `W` with no
eigencomponents strictly below the threshold, whose Rayleigh quotient is
therefore an average of eigenvalues at least `evals hM k`. -/
theorem exists_ne_mem_rayleigh_ge_of_finrank_eq {M : Matrix V V ℝ}
    (hM : M.IsSymm) (k : Fin (Fintype.card V))
    (W : Submodule ℝ (V → ℝ)) (hW : Module.finrank ℝ W = (k : ℕ) + 1) :
    ∃ x ∈ W, x ≠ 0 ∧ evals hM k ≤ rayleigh M x := by
  classical
  have hkltn : (k : ℕ) < Fintype.card V := k.isLt
  have hltcard : (Finset.univ.filter
      fun i => eigvalOf M hM i < evals hM k).card ≤ (k : ℕ) :=
    card_filter_eigvalOf_lt_evals_le hM k
  -- the tail filter (eigenvalues at or above evals k) carries all but
  -- at most k of the eigenbasis indices
  have htailcard : Fintype.card V - (k : ℕ) ≤
      (Finset.univ.filter fun i => evals hM k ≤ eigvalOf M hM i).card := by
    have hunion : (Finset.univ : Finset V) ⊆
        (Finset.univ.filter fun i => eigvalOf M hM i < evals hM k) ∪
        (Finset.univ.filter fun i => evals hM k ≤ eigvalOf M hM i) := by
      intro i _
      by_cases h : eigvalOf M hM i < evals hM k
      · exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
      · exact Finset.mem_union.2
          (Or.inr (Finset.mem_filter.2 ⟨Finset.mem_univ _, le_of_not_gt h⟩))
    have hcard := Finset.card_le_card hunion
    rw [Finset.card_univ] at hcard
    have hunioncard := Finset.card_union_le
      (Finset.univ.filter fun i => eigvalOf M hM i < evals hM k)
      (Finset.univ.filter fun i => evals hM k ≤ eigvalOf M hM i)
    omega
  set Ttail : Finset V :=
    Finset.univ.filter fun i => evals hM k ≤ eigvalOf M hM i with hTtail
  -- dimension counting: W ⊓ T is nonzero
  have hTdim : Module.finrank ℝ (Submodule.span ℝ
      (Set.range fun i : {y // y ∈ Ttail} => eigvecOf M hM i.1)) = Ttail.card :=
    finrank_span_eigvecOf_finset hM Ttail
  have hdfin := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span ℝ
      (Set.range fun i : {y // y ∈ Ttail} => eigvecOf M hM i.1))
  have htop : Module.finrank ℝ ↥(W ⊔ Submodule.span ℝ
      (Set.range fun i : {y // y ∈ Ttail} => eigvecOf M hM i.1))
      ≤ Module.finrank ℝ (V → ℝ) := Submodule.finrank_le _
  have hpi : Module.finrank ℝ (V → ℝ) = Fintype.card V :=
    Module.finrank_pi ℝ
  have hpos : 0 < Module.finrank ℝ ↥(W ⊓ Submodule.span ℝ
      (Set.range fun i : {y // y ∈ Ttail} => eigvecOf M hM i.1)) := by
    omega
  have hne : W ⊓ Submodule.span ℝ
      (Set.range fun i : {y // y ∈ Ttail} => eigvecOf M hM i.1) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hpos
    simp at hpos
  obtain ⟨x, hxmem, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  refine ⟨x, hxmem.1, hx0, ?_⟩
  refine evals_le_rayleigh_of_forall_dotProduct_eq_zero hM k hx0 ?_
  intro i hi
  refine dotProduct_eigvecOf_eq_zero_of_mem_span hM Ttail ?_ hxmem.2
  intro hmem
  rw [hTtail] at hmem
  exact absurd hi (not_lt.2 (Finset.mem_filter.1 hmem).2)

/-- **General Courant–Fischer min–max (proved, no axioms).** The `k`-th
sorted eigenvalue of a real symmetric matrix is the infimum, over
`(k+1)`-dimensional subspaces `W`, of the values dominating the Rayleigh
quotients on `W` — the subspace-form min–max. Both inequalities come from
the two witness forms: the competitor direction bounds every dominated
value below by `evals hM k`, and the existence direction exhibits a `W`
on which `evals hM k` itself is a dominating value.

Source (classical background; this is a proof, not an admission):
- Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., Cambridge
  University Press, 2013, Section 4.2 (Courant–Fischer), Theorem 4.2.6.

Statement differences: Rayleigh quotients use Scaffold's total `rayleigh`
(junk value `0` at the zero vector, excluded by `x ≠ 0`), the spectrum is
`Fin`-indexed from `0` so the `k`-th entry pairs with subspaces of
dimension `k + 1`, and the within-subspace maximum is expressed as the
set of dominating values rather than a `sup` on a sphere. Only symmetry
is assumed — no positivity, kernel, or graph structure (compare
`secondEval_variational`, the index-1 PSD-plus-kernel instance).

QA: `Scaffold/QA/SpectralGraph/CourantFischer_QA.lean` pins both
directions on a two-vertex fixture with spectrum `[1, 3]`, refutes wrong
and under-dimensional competitor subspaces, and instantiates the
competitor direction on the three-vertex path Laplacian. -/
theorem evals_min_max {M : Matrix V V ℝ} (hM : M.IsSymm)
    (k : Fin (Fintype.card V)) :
    evals hM k = sInf {r : ℝ | ∃ W : Submodule ℝ (V → ℝ),
      Module.finrank ℝ W = (k : ℕ) + 1 ∧
      ∀ x ∈ W, x ≠ 0 → rayleigh M x ≤ r} := by
  have hdom : ∀ r ∈ {r : ℝ | ∃ W : Submodule ℝ (V → ℝ),
      Module.finrank ℝ W = (k : ℕ) + 1 ∧
      ∀ x ∈ W, x ≠ 0 → rayleigh M x ≤ r}, evals hM k ≤ r := by
    rintro r ⟨W, hWr, hWb⟩
    obtain ⟨x, hxW, hx0, hge⟩ :=
      exists_ne_mem_rayleigh_ge_of_finrank_eq hM k W hWr
    exact hge.trans (hWb x hxW hx0)
  obtain ⟨W₁, hW₁r, hW₁b⟩ := exists_submodule_forall_rayleigh_le hM k
  have hbdd : BddBelow {r : ℝ | ∃ W : Submodule ℝ (V → ℝ),
      Module.finrank ℝ W = (k : ℕ) + 1 ∧
      ∀ x ∈ W, x ≠ 0 → rayleigh M x ≤ r} :=
    ⟨evals hM k, fun r hr => hdom r hr⟩
  have hmem : (evals hM k) ∈ {r : ℝ | ∃ W : Submodule ℝ (V → ℝ),
      Module.finrank ℝ W = (k : ℕ) + 1 ∧
      ∀ x ∈ W, x ≠ 0 → rayleigh M x ≤ r} :=
    ⟨W₁, hW₁r, hW₁b⟩
  refine le_antisymm (le_csInf ⟨evals hM k, hmem⟩ fun r hr => hdom r hr)
    (csInf_le hbdd hmem)

end CourantFischer

/-!
## 6. Event-driven adjacency updates
-/

/-- A single event update: replace the weight of the undirected edge
`{u, v}` by `w` (writing both symmetric entries; `u = v` addresses the
diagonal entry). -/
def eventUpdate (A : WAdj (V := V)) (u v : V) (w : ℝ) : WAdj (V := V) :=
  fun i j => if (i = u ∧ j = v) ∨ (i = v ∧ j = u) then w else A i j

/-- Event updates preserve symmetry, so the event-driven dynamics of
`Scaffold.Mathlib.GraphTheory.Dynamics` stays inside symmetric matrices. -/
theorem eventUpdate_preserves_symmetry (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (u v : V) (w : ℝ) : Matrix.IsSymm (eventUpdate A u v w) := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [eventUpdate, Matrix.transpose_apply]
  by_cases h : (j = u ∧ i = v) ∨ (j = v ∧ i = u)
  · rw [if_pos h, if_pos (by tauto : (i = u ∧ j = v) ∨ (i = v ∧ j = u))]
  · rw [if_neg h, if_neg (by tauto : ¬((i = u ∧ j = v) ∨ (i = v ∧ j = u)))]
    exact (hA.apply j i).symm

/-!
## 7. Principal submatrices and Cauchy interlacing (proved)

No statement is admitted in this module anymore. The one classical
result that remained an `axiom` here — Cauchy interlacing for principal
submatrices — was retired on 2026-08-18 and is proved below from the
Courant–Fischer min–max engine
(`exists_submodule_forall_rayleigh_le`,
`exists_ne_mem_rayleigh_ge_of_finrank_eq`): its first named consumer.
-/

/-- The principal submatrix of `M` on the vertices in `S`, symmetric when
`M` is. -/
theorem principalSubmatrix_symmetric (M : Matrix V V ℝ) (hM : M.IsSymm)
    (S : Finset V) :
    Matrix.IsSymm (M.submatrix (fun i : ↥S => (i : V)) (fun i : ↥S => (i : V))) := by
  show (M.submatrix (fun i : ↥S => (i : V)) (fun i : ↥S => (i : V)))ᵀ
      = M.submatrix (fun i : ↥S => (i : V)) (fun i : ↥S => (i : V))
  rw [Matrix.transpose_submatrix, hM.eq]

/-!
### The extend-by-zero padding bridge

Vectors on the vertex set `S` embed into vectors on `V` by extension
with zero. The embedding preserves dot products and quadratic forms
against `M` (entries with an index outside `S` never contribute), so it
preserves Rayleigh quotients. Through this bridge, test subspaces for
the principal submatrix and for the ambient matrix share one
Courant–Fischer engine.
-/

/-- Extend a vector defined on `S` by zero to all of `V`. -/
def padVec (S : Finset V) (y : ↥S → ℝ) : V → ℝ :=
  fun v => if h : v ∈ S then y ⟨v, h⟩ else 0

omit [Fintype V] in
theorem padVec_apply {S : Finset V} {y : ↥S → ℝ} {v : V} (hv : v ∈ S) :
    padVec S y v = y ⟨v, hv⟩ := dif_pos hv

omit [Fintype V] in
theorem padVec_apply_of_not_mem {S : Finset V} {y : ↥S → ℝ} {v : V}
    (hv : v ∉ S) : padVec S y v = 0 := dif_neg hv

omit [Fintype V] in
theorem padVec_zero (S : Finset V) : padVec S 0 = 0 := by
  funext v
  simp only [Pi.zero_apply]
  by_cases hv : v ∈ S
  · simp [padVec, hv, Pi.zero_apply]
  · simp [padVec, hv]

omit [Fintype V] in
theorem padVec_injective (S : Finset V) : Function.Injective (padVec S) := by
  intro y₁ y₂ h
  funext a
  have h₁ : padVec S y₁ (a : V) = padVec S y₂ (a : V) := by rw [h]
  rw [padVec_apply a.2, padVec_apply a.2] at h₁
  exact h₁

omit [Fintype V] in
theorem padVec_ne_zero {S : Finset V} {y : ↥S → ℝ} (hy : y ≠ 0) :
    padVec S y ≠ 0 := fun h =>
  hy (padVec_injective S (by rw [h, padVec_zero]))

/-- The padding as a linear map. -/
def padVecLinear (S : Finset V) : (↥S → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun := padVec S
  map_add' y z := by
    funext v
    by_cases hv : v ∈ S
    · simp only [padVec_apply hv, Pi.add_apply]
    · simp only [padVec_apply_of_not_mem hv, Pi.add_apply, add_zero]
  map_smul' c y := by
    funext v
    by_cases hv : v ∈ S
    · simp only [padVec_apply hv, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    · simp only [padVec_apply_of_not_mem hv, Pi.smul_apply, smul_eq_mul,
        mul_zero]

omit [Fintype V] in
theorem padVecLinear_apply (S : Finset V) (y : ↥S → ℝ) :
    padVecLinear S y = padVec S y := rfl

omit [Fintype V] in
theorem padVecLinear_injective (S : Finset V) :
    Function.Injective (padVecLinear S) := by
  intro y₁ y₂ h
  refine padVec_injective S ?_
  rw [← padVecLinear_apply S y₁, ← padVecLinear_apply S y₂]
  exact h

/-- Padding preserves the ambient dot product: the norm term of the
Rayleigh quotient is computed entirely on `S`. -/
theorem dotProduct_padVec_self (S : Finset V) (y : ↥S → ℝ) :
    Matrix.dotProduct (padVec S y) (padVec S y) = Matrix.dotProduct y y := by
  classical
  simp only [Matrix.dotProduct]
  have hzero : ∀ v ∈ (Finset.univ : Finset V), v ∉ S →
      padVec S y v * padVec S y v = 0 := by
    intro v _ hv
    rw [padVec_apply_of_not_mem hv]; ring
  rw [← Finset.sum_subset (Finset.subset_univ S) hzero,
    ← Finset.sum_attach (f := fun v : V => padVec S y v * padVec S y v),
    Finset.sum_coe_sort_eq_attach]
  exact Finset.sum_congr rfl fun x _ => by
    simp only [padVec_apply x.2, Subtype.eta]

omit [DecidableEq V] in
/-- The quadratic form as an explicit double sum. -/
theorem quadForm_eq_sum (M : Matrix V V ℝ) (x : V → ℝ) :
    quadForm M x = ∑ i ∈ (Finset.univ : Finset V), ∑ j ∈ (Finset.univ : Finset V),
      M i j * x i * x j := by
  simp only [quadForm, Matrix.dotProduct, Matrix.mulVec, Matrix.dotProduct,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by ring

/-- Padding preserves the quadratic form against `M`: the padded vector
sees exactly the principal submatrix. No symmetry is needed. -/
theorem quadForm_padVec (M : Matrix V V ℝ) (S : Finset V) (y : ↥S → ℝ) :
    quadForm M (padVec S y) =
      quadForm (M.submatrix (fun a : ↥S => (a : V)) (fun b : ↥S => (b : V))) y := by
  classical
  rw [quadForm_eq_sum, quadForm_eq_sum]
  have hinner : ∀ v ∈ (Finset.univ : Finset V),
      (∑ j ∈ (Finset.univ : Finset V), M v j * padVec S y v * padVec S y j)
        = ∑ j ∈ S, M v j * padVec S y v * padVec S y j := by
    intro v _
    have hz : ∀ j ∈ (Finset.univ : Finset V), j ∉ S →
        M v j * padVec S y v * padVec S y j = 0 := by
      intro j _ hj
      rw [padVec_apply_of_not_mem hj]; ring
    rw [← Finset.sum_subset (Finset.subset_univ S) hz]
  have hzero : ∀ v ∈ (Finset.univ : Finset V), v ∉ S →
      (∑ j ∈ S, M v j * padVec S y v * padVec S y j) = 0 := by
    intro v _ hv
    rw [padVec_apply_of_not_mem hv, Finset.sum_eq_zero]
    intro j _; ring
  rw [Finset.sum_congr rfl hinner,
    ← Finset.sum_subset (Finset.subset_univ S) hzero,
    ← Finset.sum_attach (f := fun v : V => ∑ j ∈ S, M v j * padVec S y v * padVec S y j)]
  simp only [Finset.sum_coe_sort_eq_attach]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_attach (f := fun j : V => M ↑x j * padVec S y ↑x * padVec S y j)]
  exact Finset.sum_congr rfl fun j _ => by
    rw [padVec_apply x.2, padVec_apply j.2]
    rfl

/-- Padding preserves Rayleigh quotients of nonzero vectors — the
interface fact through which both interlacing directions transport
spectral information between `M` and its principal submatrix. -/
theorem rayleigh_padVec (M : Matrix V V ℝ) (S : Finset V) {y : ↥S → ℝ}
    (hy : y ≠ 0) :
    rayleigh M (padVec S y) =
      rayleigh (M.submatrix (fun a : ↥S => (a : V)) (fun b : ↥S => (b : V))) y := by
  have h0 : padVec S y ≠ 0 := padVec_ne_zero hy
  simp only [rayleigh, if_neg h0, if_neg hy, quadForm_padVec,
    dotProduct_padVec_self]

/-!
### Subspace bookkeeping for the interlacing proof

Two finite-dimensional facts shared by the interlacing argument:
padding preserves submodule dimensions, and every subspace of dimension
at least `k` contains one of dimension exactly `k` (the competitor
direction of Courant–Fischer demands an exact dimension).
-/

/-- An injective linear map preserves submodule dimensions. -/
theorem finrank_map_eq_of_injective {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module ℝ X] [Module ℝ Y] (f : X →ₗ[ℝ] Y) (hf : Function.Injective f)
    (P : Submodule ℝ X) :
    Module.finrank ℝ (Submodule.map f P) = Module.finrank ℝ P :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf P)).symm

/-- Under an injective linear map, the dimension of a preimage submodule
is the dimension of the submodule itself, when it lies in the range. -/
theorem finrank_comap_eq_of_le_range {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module ℝ X] [Module ℝ Y] (f : X →ₗ[ℝ] Y) (hf : Function.Injective f)
    (P : Submodule ℝ Y) (hP : P ≤ LinearMap.range f) :
    Module.finrank ℝ (Submodule.comap f P) = Module.finrank ℝ P := by
  classical
  have gm : ∀ a : Submodule.comap f P, (f.comp (Submodule.subtype _)) a ∈ P :=
    fun a => a.2
  let g := (f.comp (Submodule.subtype (Submodule.comap f P))).codRestrict P gm
  have hbij : Function.Bijective g := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      have hv : f a = f b := congrArg Subtype.val h
      exact Subtype.ext (hf hv)
    · rintro ⟨c, hc⟩
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (hP hc)
      refine ⟨⟨x, Submodule.mem_comap.2 (by rw [hx]; exact hc)⟩, ?_⟩
      exact Subtype.ext hx
  exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective g hbij)

/-- In finite dimension, every subspace of dimension at least `k`
contains a subspace of dimension exactly `k`: the span of `k` basis
vectors. -/
theorem exists_submodule_finrank_eq_of_le {X : Type*} [AddCommGroup X] [Module ℝ X]
    [FiniteDimensional ℝ X] (P : Submodule ℝ X) {k : ℕ}
    (hk : k ≤ Module.finrank ℝ P) :
    ∃ W : Submodule ℝ X, W ≤ P ∧ Module.finrank ℝ W = k := by
  classical
  have hb : LinearIndependent ℝ
      (fun k' : Fin k => ((Module.finBasis ℝ P) (Fin.castLE hk k') : X)) :=
    ((Module.finBasis ℝ P).linearIndependent.comp
      (Fin.castLE hk) (Fin.castLE_injective hk)).map'
        (Submodule.subtype P) (Submodule.ker_subtype P)
  refine ⟨Submodule.span ℝ
    (Set.range fun k' : Fin k => ((Module.finBasis ℝ P) (Fin.castLE hk k') : X)), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.coe_mem _
  · rw [finrank_span_eq_card hb]; simp

/-- **Cauchy interlacing for eigenvalues of a principal submatrix
(proved, no axioms).** With the spectra of `M` (size `n`) and its
principal submatrix on `S` (size `m`) both in nondecreasing order, for
every admissible index `i`, `λᵢ ≤ μᵢ ≤ λᵢ₊ₙ₋ₘ`.

Formerly an explicit axiom; retired 2026-08-18. The proof is the
textbook min–max argument through the padding bridge: the lower bound
pads the submatrix's attaining subspace into the ambient space and
applies the Courant–Fischer competitor direction; the upper bound
intersects the ambient's attaining subspace with the range of padding
(the dimension count `dim (U ⊓ range pad) ≥ i + 1` is the extra
subspace-intersection step the proposal warned about), extracts an
exact-dimensional competitor subspace, and transports back through
`rayleigh_padVec`. The proof is load-bearing on both Courant–Fischer
witness directions: a defect in either would surface here.

Source (classical background; this is a proof, not an admission):
- Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., Cambridge
  University Press, 2013, Section 4.3 (Cauchy interlacing; section-level
  locator, page number to be confirmed during citation review).

Statement differences: indexed against Scaffold's `evals` (sorted
nondecreasing, `Fin (Fintype.card _)`-indexed) rather than a notation of
the textbook; the index bookkeeping is stated as explicit numeric
hypotheses `hi`/`hn`.

QA: pinned to its values on the two-vertex Laplacian with a singleton
submatrix (strict window `0 < 1 < 2`, both naive one-sided bounds
refuted) in `Scaffold/QA/SpectralGraph/Interlacing_QA.lean`, using the
computational eigenvalue machinery (`eigvalOf_sum_eq_trace`,
`det_eq_prod_eigenvalues`, sortedness).
-/
theorem eigen_interlacing_principal_submatrix
    (M : Matrix V V ℝ) (hM : M.IsSymm) (S : Finset V)
    (i : Fin (Fintype.card ↥S))
    (hn : (i : ℕ) + (Fintype.card V - Fintype.card ↥S) < Fintype.card V) :
    evals hM ⟨i, lt_of_lt_of_le i.isLt (by
        rw [Fintype.card_coe]
        exact mod_cast Finset.card_le_univ S)⟩ ≤
        evals (principalSubmatrix_symmetric M hM S) i ∧
      evals (principalSubmatrix_symmetric M hM S) i ≤
        evals hM ⟨(i : ℕ) + (Fintype.card V - Fintype.card ↥S), hn⟩ := by
  classical
  have hB : Matrix.IsSymm
      (M.submatrix (fun a : ↥S => (a : V)) (fun b : ↥S => (b : V))) :=
    principalSubmatrix_symmetric M hM S
  have hray : ∀ y : ↥S → ℝ, y ≠ 0 →
      rayleigh M (padVec S y) =
        rayleigh (M.submatrix (fun a : ↥S => (a : V)) (fun b : ↥S => (b : V))) y :=
    fun y hy => rayleigh_padVec M S hy
  have hmn : Fintype.card ↥S ≤ Fintype.card V := by
    rw [Fintype.card_coe, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ S)
  constructor
  · -- Lower bound: pad the submatrix's attaining subspace into `V`.
    obtain ⟨W_B, hWdim, hWb⟩ := exists_submodule_forall_rayleigh_le hB i
    have hW'im : Module.finrank ℝ (Submodule.map (padVecLinear S) W_B)
        = (i : ℕ) + 1 := by
      rw [finrank_map_eq_of_injective _ (padVecLinear_injective S)]; exact hWdim
    obtain ⟨x', hx'mem, hx'0, hx'ge⟩ :=
      exists_ne_mem_rayleigh_ge_of_finrank_eq hM ⟨(i : ℕ),
        lt_of_lt_of_le i.isLt hmn⟩ (Submodule.map (padVecLinear S) W_B) hW'im
    obtain ⟨y, hyW, hyx⟩ := Submodule.mem_map.1 hx'mem
    have hy0 : y ≠ 0 := fun h => hx'0 (by
      rw [← hyx, h, padVecLinear_apply, padVec_zero])
    rw [← hyx, padVecLinear_apply] at hx'ge
    refine le_trans hx'ge ?_
    rw [hray y hy0]
    exact hWb y hyW hy0
  · -- Upper bound: intersect the ambient's attaining subspace with the
    -- range of padding, then transport back.
    obtain ⟨U, hUdim, hUb⟩ := exists_submodule_forall_rayleigh_le hM
      ⟨(i : ℕ) + (Fintype.card V - Fintype.card ↥S), hn⟩
    have hRdim : Module.finrank ℝ (LinearMap.range (padVecLinear S))
        = Fintype.card ↥S := by
      rw [LinearMap.finrank_range_of_inj (padVecLinear_injective S),
        Module.finrank_pi]
    have hVdim : Module.finrank ℝ (V → ℝ) = Fintype.card V :=
      Module.finrank_pi ℝ
    have hform := Submodule.finrank_sup_add_finrank_inf_eq U
      (LinearMap.range (padVecLinear S))
    have hsup : Module.finrank ℝ ↥(U ⊔ LinearMap.range (padVecLinear S))
        ≤ Fintype.card V := by
      have hle := Submodule.finrank_le (U ⊔ LinearMap.range (padVecLinear S))
      rwa [hVdim] at hle
    have hUdim' : Module.finrank ℝ U
        = (i : ℕ) + (Fintype.card V - Fintype.card ↥S) + 1 := hUdim
    have hint : (i : ℕ) + 1 ≤ Module.finrank ℝ
        ↥(U ⊓ LinearMap.range (padVecLinear S)) := by omega
    obtain ⟨P, hPU, hPdim⟩ := exists_submodule_finrank_eq_of_le
      (U ⊓ LinearMap.range (padVecLinear S)) hint
    have hPR : P ≤ LinearMap.range (padVecLinear S) :=
      hPU.trans inf_le_right
    have hWdimB : Module.finrank ℝ
        (Submodule.comap (padVecLinear S) P) = (i : ℕ) + 1 := by
      rw [finrank_comap_eq_of_le_range _ (padVecLinear_injective S) P hPR]
      exact hPdim
    obtain ⟨y, hyW, hy0, hyge⟩ :=
      exists_ne_mem_rayleigh_ge_of_finrank_eq hB i
        (Submodule.comap (padVecLinear S) P) hWdimB
    have hypadU : padVecLinear S y ∈ U := by
      have h1 : padVecLinear S y ∈ P := Submodule.mem_comap.mp hyW
      exact (hPU h1).1
    refine le_trans hyge ?_
    rw [← hray y hy0]
    exact hUb (padVec S y) hypadU (padVec_ne_zero hy0)

/- The `lambda2_variational` Courant–Fischer characterization formerly
admitted here (symmetry hypotheses only, no weight nonnegativity) was
retired on 2026-08-18: it is now a proved theorem in the
`Lambda2Variational` section above, restated with the load-bearing
hypothesis `hnonneg : ∀ i j, 0 ≤ A i j` (the pre-repair shape is false
for negative weights and is refuted in
`Scaffold/QA/SpectralGraph/Variational_QA.lean`).
See `lambda2_variational` for the proved statement and its citation
provenance. -/

end SpectralGraphTheory
