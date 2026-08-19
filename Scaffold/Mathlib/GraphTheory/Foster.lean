/-
  Foster.lean

  Purpose
  -------
  Foster's Theorem for weighted graphs, proved as hard crust with zero
  new axioms, per `proposals/spectral-graph-sparsification.md` Phase A
  (the only phase authorized: Phase B — the sparsification guarantee —
  is blocked in that proposal on an unresolved matrix-Chernoff scope
  decision and is not developed here).

  The theorem: on a connected graph with symmetric nonnegative
  conductances, the conductance-weighted resistances sum to the vertex
  count minus one,

    (∑ i, ∑ j, A i j * effectiveResistance A i j) / 2 = card V - 1,

  the unordered-pair form of `∑_{u<v} w_e R_e = n - 1` (ordered pairs
  double every edge; the `/ 2` is that double-counting factor). The
  statement is proved at full strength: no cardinality hypothesis is
  needed (for `card V = 1` both sides are `0`).

  Route (the proposal's pseudoinverse-free eigenbasis route, recorded
  2026-08-18 in that document's "Correction"; the classical
  `Tr(L^{1/2} L⁺ L^{1/2})` trace identity is background motivation only
  and nothing pseudoinverse-shaped is defined or consumed here):

  1. Per pair `(u, v)`, the resistance equals a spectral sum over the
     orthonormal eigenbasis of the Laplacian: the squared voltage
     difference along each unit eigenvector, divided by its eigenvalue,
     with the zero-eigenvalue terms omitted
     (`effectiveResistance_eq_sum_eigbasis`). This is the energy
     identity (resistance = the solution potential's energy) composed
     with the spectral resolution of the quadratic form
     (`quadForm_eigvalOf`), each eigencomponent of the potential being
     the voltage difference over the eigenvalue by self-adjointness
     (`dotProduct_eigvecOf_mulVec`).

  2. Swap the summation order in the double sum. Per eigenvector, the
     inner conductance-weighted Dirichlet sum is exactly twice the
     eigenvector's quadratic form (`laplacian_quadForm`), which is its
     eigenvalue (`quadForm_eigvecOf_self`) — every nonzero-eigenvalue
     index contributes exactly `2`, and zero-eigenvalue indices
     contribute exactly `0`.

  3. Count the nonzero-eigenvalue indices: exactly `card V - 1`, because
     the kernel of a connected Laplacian is the line spanned by `onesVec`
     (`laplacian_kernel_eq_span_onesVec`) while the eigenbasis is
     orthonormal — at most one basis vector lies in a line, and at least
     one does because `onesVec` itself is a nonzero kernel vector
     (`card_filter_eigvalOf_laplacian_eq_zero`).

  Load-bearing chain: an error in the unit-demand solvability theorem,
  the kernel characterization, the spectral resolution, the eigenbasis
  orthonormality/completeness, or the Dirichlet form identity would
  break these proofs rather than pass beside them.

  Everything here is proved; this module adds no axioms. Foster's
  original source (Foster 1949) is recorded in the proposal; the
  theorem is not admitted from it but proved from the center.
-/

import Scaffold.Mathlib.GraphTheory.Electrical

open scoped BigOperators Matrix

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Foster's Theorem (proposal `spectral-graph-sparsification.md`, Phase A)
-/

/-- **The kernel of a connected Laplacian occupies exactly one
eigenbasis index.** The Laplacian's kernel is the line spanned by
`onesVec` (`laplacian_kernel_eq_span_onesVec`); the eigenbasis is
orthonormal, so at most one basis vector can lie in that line; and at
least one must, because `onesVec` is a nonzero kernel vector
(`laplacian_ones_in_kernel`) and hence has all its eigencomponents
along nonzero-eigenvalue directions killed by self-adjointness. This is
the counting fact that turns "each nonzero eigenvalue contributes
exactly `1` to Foster's sum" into `card V - 1`. -/
theorem card_filter_eigvalOf_laplacian_eq_zero (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hconn : (supportGraph A hA).Connected) :
    (Finset.univ.filter fun k =>
      eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0).card = 1 := by
  have hL : (laplacian A).IsSymm := laplacian_symmetric A hA
  have hne : Nonempty V := hconn.nonempty
  -- At most one index: two zero-eigenvalue eigenvectors are two nonzero
  -- vectors on one line, but the basis is orthonormal.
  have hpair : ∀ k₁ k₂ : V,
      eigvalOf (laplacian A) hL k₁ = 0 → eigvalOf (laplacian A) hL k₂ = 0 →
      k₁ = k₂ := by
    intro k₁ k₂ h₁ h₂
    by_contra hne12
    have hmem : ∀ k : V, eigvalOf (laplacian A) hL k = 0 →
        ∃ c : ℝ, eigvecOf (laplacian A) hL k = c • onesVec := by
      intro k hk
      have hker : eigvecOf (laplacian A) hL k
          ∈ LinearMap.ker (Matrix.mulVecLin (laplacian A)) := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        have hev : (laplacian A) *ᵥ eigvecOf (laplacian A) hL k
            = eigvalOf (laplacian A) hL k • eigvecOf (laplacian A) hL k :=
          (isHermitian_of_isSymm hL).mulVec_eigenvectorBasis k
        rw [hev, hk, zero_smul]
      rw [laplacian_kernel_eq_span_onesVec A hA hnonneg hconn] at hker
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hker
      exact ⟨c, hc.symm⟩
    obtain ⟨c₁, hc₁⟩ := hmem k₁ h₁
    obtain ⟨c₂, hc₂⟩ := hmem k₂ h₂
    have hunit1 : Matrix.dotProduct (eigvecOf (laplacian A) hL k₁)
        (eigvecOf (laplacian A) hL k₁) = 1 := by
      simpa using eigvecOf_dotProduct hL k₁ k₁
    have hunit2 : Matrix.dotProduct (eigvecOf (laplacian A) hL k₂)
        (eigvecOf (laplacian A) hL k₂) = 1 := by
      simpa using eigvecOf_dotProduct hL k₂ k₂
    have hc1ne : c₁ ≠ 0 := fun h0 => by
      rw [h0, zero_smul] at hc₁
      rw [hc₁] at hunit1
      simp at hunit1
    have hc2ne : c₂ ≠ 0 := fun h0 => by
      rw [h0, zero_smul] at hc₂
      rw [hc₂] at hunit2
      simp at hunit2
    have hortho : Matrix.dotProduct (eigvecOf (laplacian A) hL k₁)
        (eigvecOf (laplacian A) hL k₂) = 0 := by
      rw [eigvecOf_dotProduct hL k₁ k₂, if_neg hne12]
    rw [hc₁, hc₂, Matrix.smul_dotProduct, Matrix.dotProduct_smul,
      smul_eq_mul, smul_eq_mul] at hortho
    have hones : Matrix.dotProduct (onesVec (V := V)) (onesVec (V := V))
        = (Fintype.card V : ℝ) := by
      show (∑ x : V, onesVec x * onesVec x) = (Fintype.card V : ℝ)
      simp [onesVec]
    rw [hones] at hortho
    have hcardne : (Fintype.card V : ℝ) ≠ 0 := by
      haveI : Nonempty V := hne
      exact_mod_cast Fintype.card_ne_zero
    rcases mul_eq_zero.1 hortho with h | h
    · exact hc1ne h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact hc2ne h'
      · exact absurd h' hcardne
  -- At least one index: `onesVec` is a nonzero kernel vector, so its
  -- expansion along the eigenbasis cannot have all components on
  -- nonzero-eigenvalue directions (each such component is killed by
  -- self-adjointness applied to the kernel equation).
  have hex : ∃ k₀ : V, eigvalOf (laplacian A) hL k₀ = 0 := by
    by_contra hno
    push_neg at hno
    have hcomp : ∀ k : V,
        Matrix.dotProduct (eigvecOf (laplacian A) hL k) onesVec = 0 := by
      intro k
      have h := dotProduct_eigvecOf_mulVec hL k onesVec
      rw [laplacian_ones_in_kernel, Matrix.dotProduct_zero] at h
      exact (mul_eq_zero.1 h.symm).resolve_left (hno k)
    have hzero : (onesVec (V := V)) = 0 := by
      funext a
      have he := eigvecOf_expansion_apply hL onesVec a
      simp only [hcomp, zero_mul, Finset.sum_const_zero] at he
      exact he.symm
    exact absurd (congrFun hzero hne.some) (by simp [onesVec])
  obtain ⟨k₀, hk₀⟩ := hex
  have hsub : (Finset.univ.filter fun k =>
      eigvalOf (laplacian A) hL k = 0) ⊆ {k₀} := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ] at hk
    exact Finset.mem_singleton.mpr (hpair k k₀ hk.2 hk₀)
  rcases Finset.subset_singleton_iff.1 hsub with h | h
  · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ k₀, hk₀⟩)
      (by rw [h]; simp)
  · rw [h]
    rfl

/-- **Resistance as a spectral sum (the per-pair Foster kernel).** On a
connected graph with symmetric nonnegative conductances, the effective
resistance between `u` and `v` is the sum over the Laplacian's
orthonormal eigenbasis of the squared voltage difference along each unit
eigenvector divided by its eigenvalue, omitting zero-eigenvalue terms
(their voltage differences vanish: a kernel eigenvector is orthogonal to
every demand the Laplacian can produce). This is Foster's
pseudoinverse-free replacement: no `L⁺` is ever formed; the potential
solving `L *ᵥ f = e u − e v` is only ever used through its energy, which
`quadForm_eigvalOf` resolves spectrally. -/
theorem effectiveResistance_eq_sum_eigbasis (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hconn : (supportGraph A hA).Connected) (u v : V) :
    effectiveResistance A u v
      = ∑ k, (if eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0
            then (0 : ℝ)
            else (eigvecOf (laplacian A) (laplacian_symmetric A hA) k u
                  - eigvecOf (laplacian A) (laplacian_symmetric A hA) k v) ^ 2
              / eigvalOf (laplacian A) (laplacian_symmetric A hA) k) := by
  have hL : (laplacian A).IsSymm := laplacian_symmetric A hA
  obtain ⟨f, hf⟩ :=
    exists_laplacian_mulVec_eq_single_sub_single A hA hnonneg hconn u v
  rw [effectiveResistance_eq A hA hnonneg hconn ⟨f, hf, rfl⟩,
    ← quadForm_laplacian_eq_sub_of_mulVec_eq_single_sub_single A hf,
    quadForm_eigvalOf hL f]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h0 : eigvalOf (laplacian A) hL k = 0
  · have hd0 : (if eigvalOf (laplacian A) hL k = 0
          then (0 : ℝ)
          else (eigvecOf (laplacian A) hL k u
                - eigvecOf (laplacian A) hL k v) ^ 2
            / eigvalOf (laplacian A) hL k) = 0 := if_pos h0
    rw [hd0, h0, zero_mul]
  · simp only [if_neg h0]
    -- The eigencomponent of the potential is the voltage difference
    -- over the eigenvalue (self-adjointness through the demand equation).
    have hc : eigvalOf (laplacian A) hL k
        * Matrix.dotProduct (eigvecOf (laplacian A) hL k) f
        = eigvecOf (laplacian A) hL k u - eigvecOf (laplacian A) hL k v := by
      rw [← dotProduct_eigvecOf_mulVec hL k f, hf,
        Matrix.dotProduct_sub, Matrix.dotProduct_single,
        Matrix.dotProduct_single, mul_one, mul_one]
    have hd : (eigvecOf (laplacian A) hL k u
          - eigvecOf (laplacian A) hL k v) ^ 2
        / eigvalOf (laplacian A) hL k
        = eigvalOf (laplacian A) hL k
          * (Matrix.dotProduct (eigvecOf (laplacian A) hL k) f) ^ 2 := by
      rw [← hc]
      field_simp
      ring
    rw [hd]

/-- **Foster's Theorem** (proposal `spectral-graph-sparsification.md`,
Phase A; Foster 1949). On a connected graph with symmetric nonnegative
conductances, the conductance-weighted effective resistances sum to the
number of edges of a spanning tree:

  (∑ i, ∑ j, A i j * effectiveResistance A i j) / 2 = card V - 1,

i.e. in unordered-pair notation `∑_{u < v} w_{uv} R_eff(u, v) = n - 1`
(the `/ 2` removes the ordered-pair double count). Every nonzero
Laplacian eigenvalue contributes exactly `1` to the unordered sum —
term by term, through the spectral resolution of each pair's energy and
the Dirichlet-form identity — and connectivity makes the zero-eigenvalue
eigenspace exactly one-dimensional, so precisely `n - 1` eigenvalues
contribute. Proof route and citation discussion live in the module
header; no pseudoinverse, matrix square root, or new axiom is involved. -/
theorem foster_theorem (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hconn : (supportGraph A hA).Connected) :
    (∑ i, ∑ j, A i j * effectiveResistance A i j) / 2
      = (Fintype.card V : ℝ) - 1 := by
  have hL : (laplacian A).IsSymm := laplacian_symmetric A hA
  -- Swap the double sum: eigenvector index outermost.
  have hswap : ∑ i, ∑ j, A i j * effectiveResistance A i j
      = ∑ k, ∑ i, ∑ j, A i j * (if eigvalOf (laplacian A) hL k = 0
            then (0 : ℝ)
            else (eigvecOf (laplacian A) hL k i
                  - eigvecOf (laplacian A) hL k j) ^ 2
              / eigvalOf (laplacian A) hL k) := by
    calc ∑ i, ∑ j, A i j * effectiveResistance A i j
        = ∑ i, ∑ j, ∑ k, A i j * (if eigvalOf (laplacian A) hL k = 0
              then (0 : ℝ)
              else (eigvecOf (laplacian A) hL k i
                    - eigvecOf (laplacian A) hL k j) ^ 2
                / eigvalOf (laplacian A) hL k) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [effectiveResistance_eq_sum_eigbasis A hA hnonneg hconn i j,
            Finset.mul_sum]
      _ = ∑ i, ∑ k, ∑ j, A i j * (if eigvalOf (laplacian A) hL k = 0
              then (0 : ℝ)
              else (eigvecOf (laplacian A) hL k i
                    - eigvecOf (laplacian A) hL k j) ^ 2
                / eigvalOf (laplacian A) hL k) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, A i j * (if eigvalOf (laplacian A) hL k = 0
              then (0 : ℝ)
              else (eigvecOf (laplacian A) hL k i
                    - eigvecOf (laplacian A) hL k j) ^ 2
                / eigvalOf (laplacian A) hL k) :=
          Finset.sum_comm
  -- Per eigenvector, the inner Dirichlet sum is twice the eigenvalue.
  have hterm : ∀ k : V,
      (∑ i, ∑ j, A i j * (if eigvalOf (laplacian A) hL k = 0
            then (0 : ℝ)
            else (eigvecOf (laplacian A) hL k i
                  - eigvecOf (laplacian A) hL k j) ^ 2
              / eigvalOf (laplacian A) hL k))
      = if eigvalOf (laplacian A) hL k = 0 then (0 : ℝ) else 2 := by
    intro k
    by_cases h0 : eigvalOf (laplacian A) hL k = 0
    · have hz : ∀ i j : V, A i j * (if eigvalOf (laplacian A) hL k = 0
            then (0 : ℝ)
            else (eigvecOf (laplacian A) hL k i
                  - eigvecOf (laplacian A) hL k j) ^ 2
              / eigvalOf (laplacian A) hL k) = 0 := by
        intro i j
        rw [if_pos h0, mul_zero]
      rw [Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => hz i j,
        Finset.sum_const_zero, Finset.sum_const_zero, if_pos h0]
    · have hz : ∀ i j : V, A i j * (if eigvalOf (laplacian A) hL k = 0
            then (0 : ℝ)
            else (eigvecOf (laplacian A) hL k i
                  - eigvecOf (laplacian A) hL k j) ^ 2
              / eigvalOf (laplacian A) hL k)
          = A i j * (eigvecOf (laplacian A) hL k i
              - eigvecOf (laplacian A) hL k j) ^ 2
            / eigvalOf (laplacian A) hL k := by
        intro i j
        rw [if_neg h0, mul_div_assoc]
      rw [Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => hz i j,
        if_neg h0]
      simp only [← Finset.sum_div, ← Finset.sum_div]
      have hq : ∑ i, ∑ j, A i j * (eigvecOf (laplacian A) hL k i
            - eigvecOf (laplacian A) hL k j) ^ 2
          = 2 * quadForm (laplacian A) (eigvecOf (laplacian A) hL k) := by
        rw [laplacian_quadForm A hA (eigvecOf (laplacian A) hL k)]
        field_simp
      rw [hq, quadForm_eigvecOf_self hL k]
      field_simp
  -- Assemble: the ordered sum is 2 per nonzero-eigenvalue index.
  rw [hswap, Finset.sum_congr rfl fun k _ => hterm k]
  have hfilter : ∑ k, (if eigvalOf (laplacian A) hL k = 0 then (0 : ℝ) else 2)
      = ((Finset.univ.filter fun k =>
          eigvalOf (laplacian A) hL k ≠ 0).card : ℝ) * 2 := by
    have h2 : ∀ k : V, (if eigvalOf (laplacian A) hL k = 0 then (0 : ℝ) else 2)
        = 2 * (if eigvalOf (laplacian A) hL k ≠ 0 then (1 : ℝ) else 0) := by
      intro k
      by_cases h : eigvalOf (laplacian A) hL k = 0
      · simp [h]
      · simp [h]
    simp only [h2, ← Finset.mul_sum, Finset.sum_boole]
    ring
  rw [hfilter]
  -- The nonzero-eigenvalue count is card V - 1.
  have hcount : (Finset.univ.filter fun k =>
      eigvalOf (laplacian A) hL k ≠ 0).card = Fintype.card V - 1 := by
    have hdis : Disjoint
        (Finset.univ.filter fun k => eigvalOf (laplacian A) hL k ≠ 0)
        (Finset.univ.filter fun k => ¬ eigvalOf (laplacian A) hL k ≠ 0) :=
      Finset.disjoint_filter_filter_neg Finset.univ Finset.univ
        (fun k => eigvalOf (laplacian A) hL k ≠ 0)
    have h0' : (Finset.univ.filter fun k =>
          ¬ eigvalOf (laplacian A) hL k ≠ 0).card = 1 := by
      have hset : (Finset.univ.filter fun k =>
            ¬ eigvalOf (laplacian A) hL k ≠ 0)
          = (Finset.univ.filter fun k =>
            eigvalOf (laplacian A) hL k = 0) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, not_not]
      rw [hset, card_filter_eigvalOf_laplacian_eq_zero A hA hnonneg hconn]
    have hpart : (Finset.univ.filter fun k => eigvalOf (laplacian A) hL k ≠ 0).card
        + (Finset.univ.filter fun k => ¬ eigvalOf (laplacian A) hL k ≠ 0).card
        = Fintype.card V := by
      rw [← Finset.card_union_of_disjoint hdis,
        Finset.filter_union_filter_neg_eq
          (p := fun k => eigvalOf (laplacian A) hL k ≠ 0) Finset.univ,
        Finset.card_univ]
    omega
  rw [hcount]
  have hcardpos : 0 < Fintype.card V :=
    Fintype.card_pos_iff.mpr hconn.nonempty
  rw [Nat.cast_sub (by omega)]
  field_simp

/-- **The leverage score of a pair** (the sparsification-facing
corollary object; the sampling machinery itself is Phase B and blocked).
`A u v * R u v / (card V - 1)`: the share of the total Foster budget
`n - 1` carried by the pair's conductance-weighted resistance. The
division is guarded by the cardinality hypothesis of the consumers
(`sum_leverageScore_eq_two`); on `card V ≤ 1` or across components the
value is junk inherited from `effectiveResistance` and must not be read
as a probability. -/
noncomputable def leverageScore (A : WAdj (V := V)) (u v : V) : ℝ :=
  (A u v * effectiveResistance A u v) / ((Fintype.card V : ℝ) - 1)

/-- **Foster's theorem in leverage form:** on a connected graph with at
least two vertices, the ordered-pair leverage scores sum to exactly `2`
— equivalently, the unordered-pair scores sum to `1`, which is what
makes them an importance-sampling distribution over the edges (the
Spielman–Srivastava observation; the sparsification guarantee itself is
Phase B and blocked). The cardinality hypothesis is the division guard. -/
theorem sum_leverageScore_eq_two (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hconn : (supportGraph A hA).Connected)
    (hcard : 2 ≤ Fintype.card V) :
    ∑ i, ∑ j, leverageScore A i j = 2 := by
  have h1 : (1 : ℝ) < (Fintype.card V : ℝ) :=
    by exact_mod_cast (by omega : 1 < Fintype.card V)
  have hne : ((Fintype.card V : ℝ) - 1) ≠ 0 := by linarith
  have hsplit : ∑ i, ∑ j, leverageScore A i j
      = (∑ i, ∑ j, A i j * effectiveResistance A i j)
        / ((Fintype.card V : ℝ) - 1) := by
    simp only [leverageScore, Finset.sum_div, Finset.sum_div]
  have hS : (∑ i, ∑ j, A i j * effectiveResistance A i j)
      = 2 * ((Fintype.card V : ℝ) - 1) := by
    rw [← foster_theorem A hA hnonneg hconn]
    field_simp
  rw [hsplit, hS]
  field_simp

end SpectralGraphTheory
