/-
  Spectral.lean

  Purpose
  -------
  The spectral graph theory center of Scaffold: real definitions for
  weighted adjacency matrices, degrees, the combinatorial Laplacian,
  quadratic/Rayleigh forms, a canonically sorted real spectrum,
  cut/volume/conductance quantities, and event-driven adjacency updates,
  together with proved structural theorems and a minimal set of explicit,
  cited axioms (Cauchy interlacing and the variational characterization
  of the algebraic connectivity λ₂). It also provides the
  `supportGraph` adapter from weighted adjacency matrices to Mathlib's
  `SimpleGraph`, through which the Laplacian kernel is characterized on
  connected graphs: the kernel is exactly the constants.

  Everything definable and provable here is defined and proved; the only
  admitted statements are the two `axiom` declarations, each carrying a
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

Exactly two statements are admitted here; both are classical finite
dimensional results stated against the `evals` API defined above.
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

/-- Variational (Rayleigh–Ritz) characterization of the algebraic
connectivity: λ₂ is the infimum of the Laplacian Rayleigh quotient over
vectors orthogonal to the all-ones vector.

Source:
- Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., Cambridge
  University Press, 2013, Section 4.2 (Courant–Fischer; section-level
  locator, page number to be confirmed during citation review).
- Chung, F. R. K., "Spectral Graph Theory", CBMS 92, AMS, 1997,
  Section 1.3 for the Laplacian form of the statement.

Statement differences: Rayleigh quotients use Scaffold's `rayleigh`
(total function, junk value `0` at the zero vector, which is excluded by
the `x ≠ 0` side condition), and orthogonality is the dot product with
`onesVec`.

QA: exercised by
`SpectralGraphTheory.QA.rayleigh_quotient_*` lemmas in
`Scaffold/QA/SpectralGraph/Variational_QA.lean`, which check the
interface pieces (nonnegativity for PSD operators, kernel vectors,
homogeneity) that this axiom composes with.
-/
axiom lambda2_variational (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hcard : 2 ≤ Fintype.card V) :
    lambda2 A hA hcard =
      sInf {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ Matrix.dotProduct x onesVec = 0 ∧
        rayleigh (laplacian A) x = r}

end SpectralGraphTheory
