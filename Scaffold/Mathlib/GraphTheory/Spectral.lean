/-
  Spectral.lean

  Purpose
  -------
  The spectral graph theory center of Scaffold: real definitions for
  weighted adjacency matrices, degrees, the combinatorial Laplacian,
  quadratic/Rayleigh forms, a canonically sorted real spectrum,
  cut/volume/conductance quantities, and event-driven adjacency updates,
  together with proved structural theorems and a minimal set of explicit,
  cited axioms (Cauchy interlacing; the variational characterization of
  the algebraic connectivity λ₂ was admitted until 2026-08-18 and is now
  proved here, `lambda2_variational`). It also provides the
  `supportGraph` adapter from weighted adjacency matrices to Mathlib's
  `SimpleGraph`, through which the Laplacian kernel is characterized on
  connected graphs: the kernel is exactly the constants.

  Everything definable and provable here is defined and proved; the only
  admitted statement is the `axiom` declaration, carrying a
  `Source:` citation.

  Related modules: Cheeger-type inequalities live in
  `Scaffold.Mathlib.GraphTheory.Cheeger`, event-driven persistence in
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

/-- Spectral projectors are idempotent: `P_c * P_c = P_c`. Entrywise, the
product expands into outer products of eigenvectors whose cross terms
vanish by pairwise orthonormality, leaving the original sum. This is the
structural fact consumed (previously implicitly) by every projector-based
statement in the Cheeger, persistence, and drift interfaces. -/
theorem spectralProjector_idempotent (M : Matrix V V ℝ) (hM : M.IsSymm)
    (c : ℝ) :
    spectralProjector M hM c * spectralProjector M hM c
      = spectralProjector M hM c := by
  ext a b
  simp only [Matrix.mul_apply, spectralProjector, Matrix.of_apply]
  have hexp : ∀ k : V,
      (∑ i ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c),
          eigvecOf M hM i a * eigvecOf M hM i k) *
        (∑ j ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c),
            eigvecOf M hM j k * eigvecOf M hM j b) =
      ∑ i ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c),
        ∑ j ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c),
          (eigvecOf M hM i a * eigvecOf M hM i k) *
            (eigvecOf M hM j k * eigvecOf M hM j b) :=
    fun k => Finset.sum_mul_sum _ _ _ _
  simp only [hexp]
  have hreorder : ∑ k : V,
      ∑ i ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c),
        ∑ j ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c),
          (eigvecOf M hM i a * eigvecOf M hM i k) *
            (eigvecOf M hM j k * eigvecOf M hM j b) =
    ∑ i ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c),
      ∑ j ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c),
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
  have hsingle : ∑ x ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c),
      eigvecOf M hM i a * eigvecOf M hM x b * (if i = x then 1 else 0)
      = eigvecOf M hM i a * eigvecOf M hM i b := by
    rw [Finset.sum_eq_single i
      (fun x _ hx => by
        rw [if_neg (fun h => hx h.symm), mul_zero])
      (fun hcon => absurd hi hcon)]
    simp
  rw [hsingle]

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

/-- Eigenvectors of nonzero Laplacian eigenvalues are orthogonal to
`onesVec`: `onesVec` is always in the kernel (row sums vanish, no
symmetry needed), and the eigenbasis expansion of the kernel equation
kills its components along nonzero eigenspaces. No hypothesis beyond
symmetry. -/
theorem eigvecOf_ortho_onesVec (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    {i : V}
    (hne : eigvalOf (laplacian A) (laplacian_symmetric A hA) i ≠ 0) :
    Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i)
      onesVec = 0 := by
  have hL := laplacian_symmetric A hA
  -- Parseval on the pair (v i, L *ᵥ onesVec), with the eigenaction resolved
  have hparseval : Matrix.dotProduct (eigvecOf (laplacian A) hL i)
      ((laplacian A) *ᵥ onesVec)
      = ∑ j : V, Matrix.dotProduct (eigvecOf (laplacian A) hL j)
          (eigvecOf (laplacian A) hL i)
        * (eigvalOf (laplacian A) hL j
          * Matrix.dotProduct (eigvecOf (laplacian A) hL j) onesVec) := by
    rw [dotProduct_eigvecOf hL (eigvecOf (laplacian A) hL i)
      ((laplacian A) *ᵥ onesVec)]
    simp only [dotProduct_eigvecOf_mulVec hL]
  rw [laplacian_ones_in_kernel A, Matrix.dotProduct_zero] at hparseval
  -- the sum collapses to the i-term by orthonormality
  have hvanish : ∀ j ∈ (Finset.univ : Finset V), j ≠ i →
      (Matrix.dotProduct (eigvecOf (laplacian A) hL j)
          (eigvecOf (laplacian A) hL i)
        * (eigvalOf (laplacian A) hL j
          * Matrix.dotProduct (eigvecOf (laplacian A) hL j) onesVec)) = 0 := by
    intro j _ hj
    have hij : eigvecOf (laplacian A) hL j ⬝ᵥ eigvecOf (laplacian A) hL i
          = 0 := by
      simpa [Matrix.dotProduct, if_neg hj]
        using eigvecOf_inner (laplacian A) hL j i
    rw [hij, zero_mul]
  rw [Finset.sum_eq_single i hvanish (fun hni =>
    absurd (Finset.mem_univ i) hni)] at hparseval
  -- the i-term is (v i ⬝ᵥ v i) * (μ i * (v i ⬝ᵥ onesVec)) = μ i * (v i ⬝ᵥ onesVec)
  have hii : Matrix.dotProduct (eigvecOf (laplacian A) hL i)
      (eigvecOf (laplacian A) hL i) = 1 := by
    simpa [Matrix.dotProduct] using eigvecOf_inner (laplacian A) hL i i
  rw [hii, one_mul] at hparseval
  exact (mul_eq_zero.1 hparseval.symm).resolve_left hne

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

Route (matrix world, through the proved eigenbasis tools): the lower
bound `λ₂ ≤ R(x)` comes from the spectral resolution of `quadForm`
plus the upper multiplicity pin (`evals_one_le_max_of_ne`: at most one
eigenvalue is below `λ₂`, and its eigenvector is parallel to `onesVec`
by `eigvecOf_ortho_onesVec`, so it is invisible to vectors orthogonal
to `onesVec`); the upper bound exhibits witnesses — the eigenvector at
`evals 1` when `λ₂ > 0`, and a kernel vector orthogonal to `onesVec`
produced by the lower multiplicity pin
(`exists_ne_eigvalOf_of_evals_head_eq`) when `λ₂ = 0`.

QA: exercised by the `Variational_QA` refutation and instantiation
lemmas in `Scaffold/QA/SpectralGraph/Variational_QA.lean`. -/
theorem lambda2_variational (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hcard : 2 ≤ Fintype.card V) :
    lambda2 A hA hcard =
      sInf {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ Matrix.dotProduct x onesVec = 0 ∧
        rayleigh (laplacian A) x = r} := by
  classical
  have hL := laplacian_symmetric A hA
  have hL2evals : lambda2 A hA hcard = evals hL ⟨1, by omega⟩ := rfl
  have hpsd := laplacian_psd A hA hnonneg
  have hmunn : ∀ i : V, 0 ≤ eigvalOf (laplacian A) hL i := by
    intro i
    have h := hpsd (eigvecOf (laplacian A) hL i)
    rw [quadForm_eigvecOf_self hL i] at h
    exact h
  have hvv : ∀ i : V, Matrix.dotProduct (eigvecOf (laplacian A) hL i)
      (eigvecOf (laplacian A) hL i) = 1 := by
    intro i
    simpa [Matrix.dotProduct] using eigvecOf_inner (laplacian A) hL i i
  have hvne : ∀ i : V, eigvecOf (laplacian A) hL i ≠ 0 := by
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
      Matrix.dotProduct x onesVec = 0 ∧ rayleigh (laplacian A) x = r}.Nonempty :=
    by
    have hpu : ∀ w : V, ∑ i, Pi.single w (1 : ℝ) i = 1 := by
      intro w
      simp
    refine ⟨rayleigh (laplacian A)
      (Pi.single u 1 - Pi.single v 1 : V → ℝ), ?_⟩
    show ∃ x : V → ℝ, x ≠ 0 ∧ Matrix.dotProduct x onesVec = 0 ∧
      rayleigh (laplacian A) x = rayleigh (laplacian A)
        (Pi.single u 1 - Pi.single v 1 : V → ℝ)
    refine ⟨Pi.single u 1 - Pi.single v 1, ?_, ?_, rfl⟩
    · intro h
      have h1 : (Pi.single u 1 - Pi.single v 1 : V → ℝ) u = 0 :=
        congrFun h u
      simp [Pi.sub_apply, Pi.single_apply, huv] at h1
    · simp only [Matrix.dotProduct, onesVec, Pi.sub_apply, mul_one,
        Finset.sum_sub_distrib]
      rw [hpu u, hpu v, sub_self]
  -- Step 1: every element of the set dominates λ₂
  have hstep1 : ∀ x : V → ℝ, x ≠ 0 →
      Matrix.dotProduct x onesVec = 0 →
      lambda2 A hA hcard ≤ rayleigh (laplacian A) x := by
    intro x hx0 hxorth
    have hDpos : 0 < Matrix.dotProduct x x := by
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hx0 (funext hcon)
      exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
        ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩
    -- the key nonnegativity: ∑ i, (μ i − λ₂) (v i ⬝ᵥ x)² ≥ 0
    have hkey : 0 ≤ ∑ i, (eigvalOf (laplacian A) hL i
        - lambda2 A hA hcard)
        * (Matrix.dotProduct (eigvecOf (laplacian A) hL i) x) ^ 2 := by
      by_cases hex : ∃ i₀ : V,
          eigvalOf (laplacian A) hL i₀ < lambda2 A hA hcard
      · obtain ⟨i₀, hi₀⟩ := hex
        have hL2pos : 0 < lambda2 A hA hcard :=
          lt_of_le_of_lt (hmunn i₀) hi₀
        -- onesVec has a nonzero eigencomponent; its eigenvalue is 0
        have honesne : (onesVec : V → ℝ) ≠ 0 := by
          intro h
          have h1 : (1 : ℝ) = 0 := congrFun h u
          simp at h1
        obtain ⟨j₀, hj₀c⟩ : ∃ j : V,
            Matrix.dotProduct (eigvecOf (laplacian A) hL j) onesVec ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          apply honesne
          funext a
          have hsum := eigvecOf_expansion_apply hL onesVec a
          simp [hcon] at hsum
          exact hsum.symm
        have hj0mu : eigvalOf (laplacian A) hL j₀ = 0 := by
          by_contra hmu
          exact hj₀c (eigvecOf_ortho_onesVec A hA hmu)
        -- j₀ = i₀, since two distinct indices cannot both be below λ₂
        have hj₀ : j₀ = i₀ := by
          by_contra hne
          have hmax := evals_one_le_max_of_ne hL hcard i₀ j₀
            (fun h' => hne h'.symm)
          rw [← hL2evals] at hmax
          have hbelow : max (eigvalOf (laplacian A) hL i₀)
              (eigvalOf (laplacian A) hL j₀) < lambda2 A hA hcard := by
            rw [hj0mu]
            exact max_lt hi₀ hL2pos
          exact absurd hmax (not_le.2 hbelow)
        -- every other index dominates λ₂
        have hge : ∀ k : V, k ≠ i₀ →
            lambda2 A hA hcard ≤ eigvalOf (laplacian A) hL k := by
          intro k hk
          by_contra hlt
          push_neg at hlt
          have hmax := evals_one_le_max_of_ne hL hcard i₀ k hk.symm
          rw [← hL2evals] at hmax
          exact absurd hmax (not_le.2 (max_lt hi₀ hlt))
        -- the coefficient of x along v i₀ vanishes
        have hc₀ : Matrix.dotProduct (eigvecOf (laplacian A) hL i₀) x = 0 := by
          -- every other index has positive eigenvalue, hence ⊥ onesVec
          have hmupos : ∀ j : V, j ≠ i₀ →
              eigvalOf (laplacian A) hL j ≠ 0 := by
            intro j hj hzero
            have hle := hge j hj
            rw [hzero] at hle
            exact absurd hle (not_le.2 hL2pos)
          -- so the expansion of onesVec is supported only at i₀
          have hexp : ∀ a : V, onesVec a
              = Matrix.dotProduct (eigvecOf (laplacian A) hL i₀) onesVec
                * eigvecOf (laplacian A) hL i₀ a := by
            intro a
            have hsum : ∑ j, Matrix.dotProduct
                (eigvecOf (laplacian A) hL j) onesVec
                * eigvecOf (laplacian A) hL j a = onesVec a :=
              eigvecOf_expansion_apply hL onesVec a
            rw [Finset.sum_eq_single i₀ (fun j _ hj => by
              have hzero := eigvecOf_ortho_onesVec A hA (hmupos j hj)
              rw [hzero, zero_mul])
              (fun hni => absurd (Finset.mem_univ i₀) hni)] at hsum
            exact hsum.symm
          have hdne : Matrix.dotProduct (eigvecOf (laplacian A) hL i₀)
              onesVec ≠ 0 := by
            rw [← hj₀]
            exact hj₀c
          -- 0 = x ⬝ᵥ onesVec = d * (x ⬝ᵥ v i₀) with d ≠ 0
          have hprod : Matrix.dotProduct (eigvecOf (laplacian A) hL i₀)
              onesVec * Matrix.dotProduct x
              (eigvecOf (laplacian A) hL i₀) = 0 := by
            have hx1 : Matrix.dotProduct x
                (fun a => Matrix.dotProduct
                    (eigvecOf (laplacian A) hL i₀) onesVec
                  * eigvecOf (laplacian A) hL i₀ a) = 0 :=
              (congrArg (Matrix.dotProduct x) (funext hexp)).symm.trans
                hxorth
            have hcalc : Matrix.dotProduct x
                (fun a => Matrix.dotProduct
                    (eigvecOf (laplacian A) hL i₀) onesVec
                  * eigvecOf (laplacian A) hL i₀ a)
                = Matrix.dotProduct (eigvecOf (laplacian A) hL i₀) onesVec
                  * Matrix.dotProduct x
                    (eigvecOf (laplacian A) hL i₀) := by
              simp only [Matrix.dotProduct]
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun a _ => by ring
            rw [← hcalc]
            exact hx1
          rw [Matrix.dotProduct_comm]
          exact (mul_eq_zero.1 hprod).resolve_left hdne
        -- assemble: the i₀-term vanishes, every other term is nonnegative
        rw [← Finset.add_sum_erase (Finset.univ : Finset V)
          (fun i => (eigvalOf (laplacian A) hL i - lambda2 A hA hcard)
            * (Matrix.dotProduct (eigvecOf (laplacian A) hL i) x) ^ 2)
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
    have hQge : lambda2 A hA hcard * Matrix.dotProduct x x
        ≤ quadForm (laplacian A) x := by
      rw [quadForm_eigvalOf hL x, dotProduct_eigvecOf hL x x,
        ← sub_nonneg, Finset.mul_sum, ← Finset.sum_sub_distrib]
      rw [Finset.sum_congr rfl fun i _ => show
        (eigvalOf (laplacian A) hL i
            * (Matrix.dotProduct (eigvecOf (laplacian A) hL i) x) ^ 2
          - lambda2 A hA hcard
            * (Matrix.dotProduct (eigvecOf (laplacian A) hL i) x
              * Matrix.dotProduct (eigvecOf (laplacian A) hL i) x))
        = (eigvalOf (laplacian A) hL i - lambda2 A hA hcard)
          * (Matrix.dotProduct (eigvecOf (laplacian A) hL i) x) ^ 2 from
        by ring]
      exact hkey
    rw [rayleigh, if_neg hx0]
    exact (le_div_iff₀ hDpos).2 hQge
  -- Step 2: some element of the set is at most λ₂
  have hSbdd : BddBelow {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧ rayleigh (laplacian A) x = r} :=
    ⟨lambda2 A hA hcard, fun r hr => by
      obtain ⟨x, hx0, hxorth, hrx⟩ := hr
      rw [← hrx]
      exact hstep1 x hx0 hxorth⟩
  have hortho_pair : ∀ i j : V, i ≠ j →
      Matrix.dotProduct (eigvecOf (laplacian A) hL i)
        (eigvecOf (laplacian A) hL j) = 0 := by
    intro i j hij
    simpa [Matrix.dotProduct, hij] using eigvecOf_inner (laplacian A) hL i j
  have hmemupper : ∃ r ∈ {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧ rayleigh (laplacian A) x = r},
      r ≤ lambda2 A hA hcard := by
    have hL2nn : 0 ≤ lambda2 A hA hcard := by
      obtain ⟨i, hi⟩ := evals_mem_eigvalOf hL ⟨1, by omega⟩
      rw [hL2evals, hi]
      exact hmunn i
    rcases eq_or_lt_of_le hL2nn with h0 | hpos
    · -- λ₂ = 0: a kernel vector ⊥ onesVec exists, from the double bottom
      have he01 : evals hL ⟨1, by omega⟩ = 0 := by
        rw [← hL2evals]
        exact h0.symm
      have hev01 : evals hL ⟨0, by omega⟩ = evals hL ⟨1, by omega⟩ := by
        have h1 : evals hL ⟨0, by omega⟩ ≤ evals hL ⟨1, by omega⟩ :=
          evals_sorted hL (Fin.le_def.2 (Nat.le_succ 0))
        have h2 : 0 ≤ evals hL ⟨0, by omega⟩ := by
          obtain ⟨i, hi⟩ := evals_mem_eigvalOf hL ⟨0, by omega⟩
          rw [hi]
          exact hmunn i
        rw [he01] at h1 ⊢
        exact le_antisymm h1 h2
      obtain ⟨i₁, i₂, hne, hmu1, hmu2⟩ :=
        exists_ne_eigvalOf_of_evals_head_eq hL hcard hev01
      rw [he01] at hmu1 hmu2
      have hev₁ : (laplacian A) *ᵥ eigvecOf (laplacian A) hL i₁ = 0 := by
        have h : (laplacian A) *ᵥ eigvecOf (laplacian A) hL i₁
            = eigvalOf (laplacian A) hL i₁ • eigvecOf (laplacian A) hL i₁ :=
          (isHermitian_of_isSymm hL).mulVec_eigenvectorBasis i₁
        rw [hmu1, zero_smul] at h
        exact h
      have hev₂ : (laplacian A) *ᵥ eigvecOf (laplacian A) hL i₂ = 0 := by
        have h : (laplacian A) *ᵥ eigvecOf (laplacian A) hL i₂
            = eigvalOf (laplacian A) hL i₂ • eigvecOf (laplacian A) hL i₂ :=
          (isHermitian_of_isSymm hL).mulVec_eigenvectorBasis i₂
        rw [hmu2, zero_smul] at h
        exact h
      by_cases hortho1 : Matrix.dotProduct (eigvecOf (laplacian A) hL i₁)
          onesVec = 0
      · refine ⟨rayleigh (laplacian A) (eigvecOf (laplacian A) hL i₁),
          ⟨eigvecOf (laplacian A) hL i₁, hvne i₁, hortho1, rfl⟩, ?_⟩
        rw [rayleigh, if_neg (hvne i₁), quadForm, hev₁,
          Matrix.dotProduct_zero, zero_div]
        exact h0.le
      · -- cross combination: orthogonal to onesVec and in the kernel
        refine ⟨rayleigh (laplacian A)
            (Matrix.dotProduct (eigvecOf (laplacian A) hL i₂) onesVec
              • eigvecOf (laplacian A) hL i₁
              - Matrix.dotProduct (eigvecOf (laplacian A) hL i₁) onesVec
                • eigvecOf (laplacian A) hL i₂),
          ⟨_, ?_, ?_, rfl⟩, ?_⟩
        · intro h
          have h2 : Matrix.dotProduct (eigvecOf (laplacian A) hL i₂)
              (Matrix.dotProduct (eigvecOf (laplacian A) hL i₂) onesVec
                • eigvecOf (laplacian A) hL i₁
                - Matrix.dotProduct (eigvecOf (laplacian A) hL i₁) onesVec
                  • eigvecOf (laplacian A) hL i₂) = 0 := by
            rw [h, Matrix.dotProduct_zero]
          rw [Matrix.dotProduct_sub, Matrix.dotProduct_smul,
            Matrix.dotProduct_smul, smul_eq_mul, smul_eq_mul,
            hortho_pair i₂ i₁ (Ne.symm hne), hvv i₂, mul_zero] at h2
          simp at h2
          exact absurd (by linarith) hortho1
        · rw [Matrix.sub_dotProduct, Matrix.smul_dotProduct,
            Matrix.smul_dotProduct, smul_eq_mul, smul_eq_mul]
          ring
        · have hLw : (laplacian A) *ᵥ
              (Matrix.dotProduct (eigvecOf (laplacian A) hL i₂) onesVec
                • eigvecOf (laplacian A) hL i₁
                - Matrix.dotProduct (eigvecOf (laplacian A) hL i₁) onesVec
                  • eigvecOf (laplacian A) hL i₂) = 0 := by
            rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
              hev₁, hev₂, smul_zero, smul_zero, sub_zero]
          rw [rayleigh]
          split
          · exact h0.le
          · rw [quadForm, hLw, Matrix.dotProduct_zero, zero_div]
            exact h0.le
    · -- 0 < λ₂: the eigenvector at the second sorted entry is ⊥ onesVec
      obtain ⟨i₂, hi₂⟩ := evals_mem_eigvalOf hL ⟨1, by omega⟩
      have hmui2 : eigvalOf (laplacian A) hL i₂
          = lambda2 A hA hcard := by
        rw [hL2evals]
        exact hi₂.symm
      refine ⟨lambda2 A hA hcard,
        ⟨eigvecOf (laplacian A) hL i₂, hvne i₂,
          eigvecOf_ortho_onesVec A hA (by rw [hmui2]; exact ne_of_gt hpos),
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

end Lambda2Variational

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
## 7. Admitted classical results (explicit axiom boundary)

Exactly one statement is admitted here; it is a classical finite
dimensional result stated against the `evals` API defined above. (The
variational characterization of `λ₂` formerly admitted here is proved
above, `lambda2_variational`.)
-/

/-- The principal submatrix of `M` on the vertices in `S`, symmetric when
`M` is. -/
theorem principalSubmatrix_symmetric (M : Matrix V V ℝ) (hM : M.IsSymm)
    (S : Finset V) :
    Matrix.IsSymm (M.submatrix (fun i : ↥S => (i : V)) (fun i : ↥S => (i : V))) := by
  show (M.submatrix (fun i : ↥S => (i : V)) (fun i : ↥S => (i : V)))ᵀ
      = M.submatrix (fun i : ↥S => (i : V)) (fun i : ↥S => (i : V))
  rw [Matrix.transpose_submatrix, hM.eq]

/-- Cauchy interlacing for eigenvalues of a principal submatrix: with the
spectra of `M` (size `n`) and its principal submatrix on `S` (size `m`)
both in nondecreasing order, for every admissible index `i`,
`λᵢ ≤ μᵢ ≤ λᵢ₊ₙ₋ₘ`.

Source:
- Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., Cambridge
  University Press, 2013, Section 4.3 (Cauchy interlacing; section-level
  locator, page number to be confirmed during citation review).

Statement differences: indexed against Scaffold's `evals` (sorted
nondecreasing, `Fin (Fintype.card _)`-indexed) rather than a notation of
the textbook; the index bookkeeping is stated as explicit numeric
hypotheses `hi`/`hn`.

QA: exercised structurally by
`SpectralGraphTheory.QA.principal_submatrix_preserves_symmetry_QA` in
`Scaffold/QA/SpectralGraph/Interlacing_QA.lean`; no thin QA of the
inequality itself exists because any instance requires an independent
eigenvalue computation.
-/
axiom eigen_interlacing_principal_submatrix
    (M : Matrix V V ℝ) (hM : M.IsSymm) (S : Finset V)
    (i : Fin (Fintype.card ↥S))
    (hn : (i : ℕ) + (Fintype.card V - Fintype.card ↥S) < Fintype.card V) :
    evals hM ⟨i, lt_of_lt_of_le i.isLt (by
        rw [Fintype.card_coe]
        exact mod_cast Finset.card_le_univ S)⟩ ≤
        evals (principalSubmatrix_symmetric M hM S) i ∧
      evals (principalSubmatrix_symmetric M hM S) i ≤
        evals hM ⟨(i : ℕ) + (Fintype.card V - Fintype.card ↥S), hn⟩

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
