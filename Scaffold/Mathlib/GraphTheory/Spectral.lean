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
  of the algebraic connectivity λ₂).

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

open scoped BigOperators Matrix

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
  have h := (isHermitian_of_isSymm hM).eigenvectorBasis.orthonormal i j
  rw [PiLp.inner_apply] at h
  simpa using h

/-- Completeness of the eigenbasis: the synthesis
`∑ i, v i a * v i b` recovers the identity matrix. Proved from
`OrthonormalBasis.sum_repr'` at `EuclideanSpace.single a 1`: the basis
resolves every unit vector. -/
theorem eigvecOf_complete (M : Matrix V V ℝ) (hM : M.IsSymm) (a b : V) :
    ∑ i, eigvecOf M hM i a * eigvecOf M hM i b = if a = b then 1 else 0 := by
  have h := (isHermitian_of_isSymm hM).eigenvectorBasis.sum_repr'
    (EuclideanSpace.single a (1 : ℝ))
  funext b
  have hcoeff : ∀ i : V, ⟪(isHermitian_of_isSymm hM).eigenvectorBasis i,
      EuclideanSpace.single a (1 : ℝ)⟫_ℝ = eigvecOf M hM i a := by
    intro i
    rw [PiLp.inner_apply]
    simp [EuclideanSpace.single_apply]
  simp only [hcoeff, smul_eq_mul]
  simpa using congrFun h b

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
  refine Finset.sum_congr rfl fun i _ => ?_
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
    rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_mul,
      eigvecOf_inner]
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  by_cases hij : i = j
  · subst hij
    simp
  · have hzero : ∀ j ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c),
      eigvecOf M hM i a * eigvecOf M hM j b * (if i = j then 1 else 0) = 0 := by
    intro j _
    rw [if_neg hij, mul_zero]
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]

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
      = Finset.univ :=
    Finset.filter_eq_univ_iff.2 (fun x _ => h x)
  ext a b
  simp only [spectralProjector, hS, Finset.sum_univ]
  simp [eigvecOf_complete]
  rw [Matrix.one_apply]

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
## 5. Event-driven adjacency updates
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
## 6. Admitted classical results (explicit axiom boundary)

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
