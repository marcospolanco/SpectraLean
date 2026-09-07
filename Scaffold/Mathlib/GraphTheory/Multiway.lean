/-
  Multiway.lean

  Purpose
  -------
  The higher-order Cheeger easy direction, every-family form: on every
  symmetric nonnegative positive-degree graph, for every `k` with
  `1 ≤ k ≤ card V` and every family of nonempty pairwise-disjoint vertex
  sets `S₁, …, S_k` (deliberately *not* a partition — it need not cover
  `V`),

  - `evals (L_sym) ⟨k−1⟩ ≤ 2 · max_i (boundary A (S i) / vol A (S i))`
    (`cheeger_upper_bound_multiway`), and
  - on families of at least two parts, where every complement is
    nonempty, the conductance form
    `evals (L_sym) ⟨k−1⟩ ≤ 2 · max_i (conductance A (S i))`
    (`cheeger_upper_bound_multiway_conductance`).

  The delivered irregular Cheeger pair (2026-08-25/26) is this family's
  `k = 2` instance; the classical statement and subspace route are
  Lee–Gharan–Trevisan, "Higher-Order Cheeger Inequalities" (STOC 2012 /
  JAMS 2014) — provenance only: every statement here is proved from the
  center, zero axioms admitted.

  The proof is the subspace (Rayleigh–Ritz) route through the new
  engine `evals_le_of_linearIndependent` (`Spectral.lean`, delivered
  with this module): the *plain, uncentered* part indicators form the
  test family (pulled back by `√D` through the irregular family's
  congruence bridge), and the cross-part energy a linear combination
  re-introduces is *absorbed* — not eliminated — pointwise by
  `(a − b)² ≤ 2a² + 2b²`, giving the theorem's constant exactly 2
  (`laplacian_quadForm_multiwayCombination_le`). No centering, no
  kernel-orthogonality hypothesis: the `k = 2` engines' constraint is
  replaced by the subspace engine's dimension count, which is what makes
  the every-family form (no partition-space attainment, no ρ_k minimum)
  reachable.

  Non-goals (priced follow-ons in `proposals/multiway-expansion.md`): the
  multiway *hard* direction (λ_k from below, higher-order Cheeger from
  above) — genuinely multi-run, unchanged. The ρ_k partition-minimum
  packaging was delivered as the follow-on below (2026-08-26).

  QA
  --
  `Scaffold/QA/SpectralGraph/MultiwayCheeger_QA.lean`: tight instances
  at `k = n` on both fixtures (K₂ `k = 2` singletons and the
  all-rational C₄ `k = 4` singletons, both equalities), the P₃
  non-covering family at `k = 2` (the every-family, not-partition
  scope), P₃ `k = 3` with `λ₃ = 2` pinned independently by trace
  arithmetic plus an eigenvector witness, the `k = 1` zero-constraint
  edge instance, the C₄ cyclic-pair overlap fence — every other
  hypothesis verified, disjointness refuted, conclusion refuted — and
  the ρ_k instances below (ρ₂(C₄) = 1/2 exact with the minimum
  provably beating the diagonal partition, ρ₂(K₂) = ρ₃(P₃) = 1 at
  independently pinned top eigenvalues, and the empty-partition-space
  junk fence at `k = 3` on `K₂`).
-/
import Scaffold.Mathlib.GraphTheory.VariationalTransfer
import Scaffold.Mathlib.GraphTheory.Heat

open scoped BigOperators Matrix
namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The part-indicator test family -/

/-- The `{0,1}`-valued indicator of a vertex set, as a plain function
(classical decidability; noncomputable by design). -/
noncomputable def partIndicator (S : Finset V) : V → ℝ :=
  fun u => @ite _ (u ∈ S) (Classical.propDecidable _) (1 : ℝ) 0

omit [Fintype V] [DecidableEq V] in
/-- Indicator entries: `1` on members. -/
theorem partIndicator_of_mem {S : Finset V} {u : V} (h : u ∈ S) :
    partIndicator S u = 1 := by
  unfold partIndicator
  rw [if_pos h]

omit [Fintype V] [DecidableEq V] in
/-- Indicator entries: `0` off members. -/
theorem partIndicator_of_not_mem {S : Finset V} {u : V} (h : u ∉ S) :
    partIndicator S u = 0 := by
  unfold partIndicator
  rw [if_neg h]

/-- **The indicator's Dirichlet energy is the boundary.** The quadratic
form of the combinatorial Laplacian at the plain indicator of `S` is
exactly `boundary A S`: within-part differences vanish, and each
crossing pair contributes its weight once from each side, matching the
boundary's double count. This is the multiway family's per-part energy
identity — the `k = 2` family's `cutTestVector` energy identity at the
indicator level, for arbitrary part counts. -/
theorem quadForm_laplacian_partIndicator (A : WAdj (V := V)) (hA : A.IsSymm)
    (S : Finset V) :
    quadForm (laplacian A) (partIndicator S) = boundary A S := by
  rw [laplacian_quadForm A hA]
  have hrowS : ∀ u ∈ S, ∑ v, A u v * (partIndicator S u - partIndicator S v) ^ 2
      = ∑ v in Sᶜ, A u v := by
    intro u hu
    rw [← Finset.sum_add_sum_compl S
        (fun v => A u v * (partIndicator S u - partIndicator S v) ^ 2)]
    have h1 : ∑ v in S, A u v * (partIndicator S u - partIndicator S v) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun v hv => ?_
      rw [partIndicator_of_mem hu, partIndicator_of_mem hv, sub_self, zero_pow two_ne_zero,
        mul_zero]
    rw [h1, zero_add]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [partIndicator_of_mem hu, partIndicator_of_not_mem (Finset.mem_compl.1 hv)]
    simp
  have hrowSc : ∀ u ∈ Sᶜ, ∑ v, A u v * (partIndicator S u - partIndicator S v) ^ 2
      = ∑ v in S, A u v := by
    intro u hu
    rw [← Finset.sum_add_sum_compl S
        (fun v => A u v * (partIndicator S u - partIndicator S v) ^ 2)]
    have h1 : ∑ v in Sᶜ, A u v * (partIndicator S u - partIndicator S v) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun v hv => ?_
      rw [partIndicator_of_not_mem (Finset.mem_compl.1 hu),
        partIndicator_of_not_mem (Finset.mem_compl.1 hv), sub_self,
        zero_pow two_ne_zero, mul_zero]
    rw [h1, add_zero]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [partIndicator_of_not_mem (Finset.mem_compl.1 hu), partIndicator_of_mem hv]
    simp
  have hbd1 : ∑ u ∈ S, ∑ v in Sᶜ, A u v = boundary A S := rfl
  have hbd2 : ∑ u ∈ Sᶜ, ∑ v in S, A u v = boundary A Sᶜ := by
    simp only [boundary, compl_compl]
  rw [← Finset.sum_add_sum_compl S
      (fun u => ∑ v, A u v * (partIndicator S u - partIndicator S v) ^ 2),
    Finset.sum_congr rfl (fun u hu => hrowS u hu),
    Finset.sum_congr rfl (fun u hu => hrowSc u hu), hbd1, hbd2,
    boundary_compl A hA S]
  ring

/-!
## The boundary outflow lemma (Step 1)

`proposals/boundary-outflow-lemma.md` (2026-09-07, the Active table's
Medium row): the vector-level statement underneath the part-indicator
energy identity above — `L · 1_S` is the *outflow vector*: on a region
member, the crossing outflow `∑_{j ∈ Sᶜ} A i j`; off the region, the
negative inflow `-(∑_{j ∈ S} A i j)`. Hypothesis-free (any weights,
asymmetric included): the whole content is
`laplacian_mulVec_apply` at the indicator plus the same
`Finset.sum_add_sum_compl` split the energy identity's own proof
performs one level up.
-/

/-- **The boundary outflow lemma, membership case** (hypothesis-free):
on a region member, the Laplacian's action on the indicator is the
outflow into the complement — every crossing edge contributes its
weight once. -/
theorem laplacian_mulVec_partIndicator_of_mem (A : WAdj (V := V))
    {S : Finset V} {i : V} (hi : i ∈ S) :
    (laplacian A).mulVec (partIndicator S) i = ∑ j in Sᶜ, A i j := by
  rw [laplacian_mulVec_apply A (partIndicator S) i,
    ← Finset.sum_add_sum_compl S
      (fun j => A i j * (partIndicator S i - partIndicator S j))]
  have h1 : ∑ j in S, A i j * (partIndicator S i - partIndicator S j) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [partIndicator_of_mem hi, partIndicator_of_mem hj, sub_self, mul_zero]
  rw [h1, zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [partIndicator_of_mem hi, partIndicator_of_not_mem (Finset.mem_compl.1 hj)]
  simp

/-- **The boundary outflow lemma, complement case** (hypothesis-free):
off the region, the action is the negative inflow from the region. -/
theorem laplacian_mulVec_partIndicator_of_not_mem (A : WAdj (V := V))
    {S : Finset V} {i : V} (hi : i ∉ S) :
    (laplacian A).mulVec (partIndicator S) i = -(∑ j in S, A i j) := by
  rw [laplacian_mulVec_apply A (partIndicator S) i,
    ← Finset.sum_add_sum_compl S
      (fun j => A i j * (partIndicator S i - partIndicator S j))]
  have h1 : ∑ j in Sᶜ, A i j * (partIndicator S i - partIndicator S j) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [partIndicator_of_not_mem hi,
      partIndicator_of_not_mem (Finset.mem_compl.1 hj), sub_self, mul_zero]
  rw [h1, add_zero]
  have hcongr : ∑ j in S, A i j * (partIndicator S i - partIndicator S j)
      = ∑ j in S, (-(A i j)) := Finset.sum_congr rfl fun j hj => by
    show A i j * (partIndicator S i - partIndicator S j) = -(A i j)
    rw [show partIndicator S i = 0 from partIndicator_of_not_mem hi,
      show partIndicator S j = 1 from partIndicator_of_mem hj]
    ring
  rw [hcongr, Finset.sum_neg_distrib]

/-- **The boundary outflow lemma, case-split form**: `L · 1_S` is the
outflow vector — on `S` the crossing outflow `∑_{j ∈ Sᶜ} A i j`, off
`S` its negative inflow `-(∑_{j ∈ S} A i j)`. -/
theorem laplacian_mulVec_partIndicator_apply (A : WAdj (V := V))
    (S : Finset V) (i : V) :
    (laplacian A).mulVec (partIndicator S) i
      = if i ∈ S then ∑ j in Sᶜ, A i j else -(∑ j in S, A i j) := by
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    exact laplacian_mulVec_partIndicator_of_mem A hi
  · rw [if_neg hi]
    exact laplacian_mulVec_partIndicator_of_not_mem A hi

/-- **The region row-sum total is the boundary** (hypothesis-free):
summing the membership case over the region gives `boundary A S`
definitionally. -/
theorem sum_laplacian_mulVec_partIndicator (A : WAdj (V := V))
    (S : Finset V) :
    ∑ i in S, (laplacian A).mulVec (partIndicator S) i = boundary A S := by
  refine Finset.sum_congr rfl fun i hi => ?_
  exact laplacian_mulVec_partIndicator_of_mem A hi

/-- **The indicator's Dirichlet energy is the boundary — WITHOUT
symmetry.** The delivered `quadForm_laplacian_partIndicator` carries
`hA : A.IsSymm` because its route runs through the squared-difference
quadratic form and `boundary_compl`; the vector-level outflow route
never flips the region, so the same identity holds for ANY weights
(asymmetric included). The hypothesis is thereby removable. -/
theorem quadForm_laplacian_partIndicator_unsymm (A : WAdj (V := V))
    (S : Finset V) :
    quadForm (laplacian A) (partIndicator S) = boundary A S := by
  have hsplit :
      ∑ i, partIndicator S i * (laplacian A).mulVec (partIndicator S) i
        = ∑ i in S, (laplacian A).mulVec (partIndicator S) i := by
    rw [← Finset.sum_add_sum_compl S
        (fun i => partIndicator S i * (laplacian A).mulVec (partIndicator S) i)]
    have h1 : ∑ i in Sᶜ, partIndicator S i
        * (laplacian A).mulVec (partIndicator S) i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [partIndicator_of_not_mem (Finset.mem_compl.1 hi), zero_mul]
    rw [h1, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [partIndicator_of_mem hi, one_mul]
  show Matrix.dotProduct (partIndicator S)
      ((laplacian A).mulVec (partIndicator S)) = _
  rw [Matrix.dotProduct, hsplit, sum_laplacian_mulVec_partIndicator]

open Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation in
/-- **The regional dissipation bound at the region indicator** (the
Boundary Outflow Lemma's Part 2, the Medium row's own ask, verbatim):
the heat flow's displacement of any input `x₀`, measured by region
membership `1_S`, is bounded by `t` times the norm of the Laplacian's
OUTFLOW VECTOR `L · 1_S` (Step 1's own object — the membership case
`laplacian_mulVec_partIndicator_of_mem` is its per-entry content) times
the input's norm. The cut↔heat bridge: combinatorial region structure
on the left, heat semigroup on the right, connected through the
outflow vector. -/
theorem abs_partIndicator_dotProduct_heatFlow_le (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j) {t : ℝ} (ht : 0 ≤ t)
    (S : Finset V) (x₀ : V → ℝ) :
    |Matrix.dotProduct (partIndicator S) (x₀ - heatKernel A t *ᵥ x₀)|
      ≤ t * ‖(WithLp.equiv 2 (V → ℝ)).symm
          (laplacian A *ᵥ partIndicator S)‖
        * ‖(WithLp.equiv 2 (V → ℝ)).symm x₀‖ := by
  have h := abs_dotProduct_heatFlow_le A hA hnonneg ht (partIndicator S) x₀
  rwa [norm_euclidean_eq_sqrt, norm_euclidean_eq_sqrt]

/-- The part-indicator combination `∑ᵢ cᵢ · 1_{Sᵢ}`: the multiway test
family's general member (classical decidability; noncomputable by
design). -/
noncomputable def multiwayCombination {k : ℕ} (S : Fin k → Finset V)
    (c : Fin k → ℝ) : V → ℝ :=
  fun u => ∑ i, @ite _ (u ∈ S i) (Classical.propDecidable _) (c i) 0

omit [Fintype V] [DecidableEq V] in
/-- On a disjoint family, a member of the `i₀`-th part reads exactly
`c i₀` — the parts do not overlap, so no other part contributes. -/
theorem multiwayCombination_of_mem {k : ℕ} {S : Fin k → Finset V}
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) {u : V} {i₀ : Fin k}
    {c : Fin k → ℝ} (h : u ∈ S i₀) :
    multiwayCombination S c u = c i₀ := by
  rw [multiwayCombination, Finset.sum_eq_single i₀]
  · simp [h]
  · intro j _ hj
    have hujs : u ∉ S j := fun hu =>
      Finset.disjoint_left.1 (hdisj i₀ j (Ne.symm hj)) h hu
    simp [hujs]
  · intro hi₀
    exact absurd (Finset.mem_univ i₀) hi₀

omit [Fintype V] [DecidableEq V] in
/-- Off all parts, the combination reads `0`. -/
theorem multiwayCombination_eq_zero {k : ℕ} {S : Fin k → Finset V}
    {u : V} {c : Fin k → ℝ} (h : ∀ i, u ∉ S i) :
    multiwayCombination S c u = 0 := by
  rw [multiwayCombination]
  exact Finset.sum_eq_zero fun i _ => by simp [h i]

/-- **The degree-weighted norm of the combination is the volume-weighted
coefficient mass.** Pulling the combination back by `√D` (the irregular
family's congruence route), the squared norm is `∑ i, c i² · vol (S i)`:
disjointness makes the weighted sum of squares read each part's volume
exactly once. -/
theorem dotProduct_degreeSqrt_mulVec_multiwayCombination (A : WAdj (V := V))
    (hdeg : ∀ i, 0 ≤ deg A i) {k : ℕ} {S : Fin k → Finset V}
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (c : Fin k → ℝ) :
    Matrix.dotProduct (degreeSqrt A *ᵥ multiwayCombination S c)
        (degreeSqrt A *ᵥ multiwayCombination S c)
      = ∑ i, c i ^ 2 * vol A (S i) := by
  rw [dotProduct_degreeSqrt_mulVec A hdeg]
  have hper : ∀ u : V,
      deg A u * multiwayCombination S c u * multiwayCombination S c u
        = ∑ i, (if u ∈ S i then deg A u * c i ^ 2 else 0) := by
    intro u
    by_cases hu : ∃ i₀ : Fin k, u ∈ S i₀
    · obtain ⟨i₀, hi₀⟩ := hu
      rw [multiwayCombination_of_mem hdisj hi₀, Finset.sum_eq_single i₀]
      · simp [hi₀]; ring
      · intro j _ hj
        have hujs : u ∉ S j := fun hu =>
          Finset.disjoint_left.1 (hdisj i₀ j (Ne.symm hj)) hi₀ hu
        simp [hujs]
      · intro hi₀
        exact absurd (Finset.mem_univ i₀) hi₀
    · push_neg at hu
      rw [multiwayCombination_eq_zero hu, Finset.sum_eq_zero]
      · ring
      · intro i _
        simp [hu i]
  have hconv : ∀ (t : Finset V) (g : V → ℝ),
      ∑ u ∈ (Finset.univ : Finset V), (if u ∈ t then g u else 0) = ∑ u ∈ t, g u := by
    intro t g
    rw [← Finset.sum_filter]
    congr 1
    ext u
    simp [Finset.mem_filter]
  rw [Finset.sum_congr rfl (fun u _ => hper u), Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hconv, vol, Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => by ring

omit [Fintype V] [DecidableEq V] in
/-- Triple-sum rotation helper (private). -/
private theorem triple_sum_comm {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (F : α → β → γ → ℝ) :
    (∑ a : α, ∑ b : β, ∑ c : γ, F a b c) = (∑ c : γ, ∑ a : α, ∑ b : β, F a b c) := by
  have hinner : ∀ a : α, (∑ b : β, ∑ c : γ, F a b c) = (∑ c : γ, ∑ b : β, F a b c) :=
    fun a => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun a _ => hinner a),
    Finset.sum_comm (f := fun (a : α) (c : γ) => ∑ b : β, F a b c)]

/-! ## Cross-part energy absorption -/

/-- **Cross-part energy absorption at the theorem's constant.** The
Dirichlet energy of the part combination is bounded by twice the
boundary-weighted coefficient mass:
`xᵀ L x ≤ 2 · ∑ i, c i² · boundary (S i)` for every combination — the
pointwise `(a − b)² ≤ 2a² + 2b²` at the crossing parts only (same-part
and off-part pairs contribute nothing). This is where a linear
combination's re-introduced cross-part energy is *absorbed* rather than
eliminated: the constant 2 in the headline theorem is exactly this
absorption constant. Load-bearing on `quadForm_laplacian_partIndicator`
(the per-part energy identity) through `laplacian_quadForm`. -/
theorem laplacian_quadForm_multiwayCombination_le (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) {k : ℕ} {S : Fin k → Finset V}
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (c : Fin k → ℝ) :
    quadForm (laplacian A) (multiwayCombination S c)
      ≤ 2 * ∑ i, c i ^ 2 * boundary A (S i) := by
  classical
  -- the pointwise absorption at the crossing-part weights
  have hpt : ∀ u v : V,
      (multiwayCombination S c u - multiwayCombination S c v) ^ 2
        ≤ 2 * ∑ i, (partIndicator (S i) u - partIndicator (S i) v) ^ 2 * c i ^ 2 := by
    intro u v
    have hterm : ∀ i : Fin k,
        (partIndicator (S i) u - partIndicator (S i) v) ^ 2 * c i ^ 2 ≥ 0 :=
      fun i => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hsumnn : 0 ≤ ∑ i, (partIndicator (S i) u - partIndicator (S i) v) ^ 2 * c i ^ 2 :=
      Finset.sum_nonneg fun i _ => hterm i
    by_cases hu : ∃ i₁ : Fin k, u ∈ S i₁
    · obtain ⟨i₁, hi₁⟩ := hu
      have hu1 : partIndicator (S i₁) u = 1 := partIndicator_of_mem hi₁
      by_cases hv : ∃ i₂ : Fin k, v ∈ S i₂
      · obtain ⟨i₂, hi₂⟩ := hv
        have hv2 : partIndicator (S i₂) v = 1 := partIndicator_of_mem hi₂
        rw [multiwayCombination_of_mem hdisj hi₁,
          multiwayCombination_of_mem hdisj hi₂]
        by_cases hij : i₁ = i₂
        · subst hij
          have hu12 : ∀ i : Fin k, u ∈ S i → v ∈ S i := by
            intro i hui
            by_contra hvnot
            have hie : i = i₁ := by
              by_contra hne
              exact Finset.disjoint_left.1 (hdisj i i₁ hne) hui hi₁
            subst hie
            exact hvnot hi₂
          have hcut : ∀ i : Fin k,
              (partIndicator (S i) u - partIndicator (S i) v) ^ 2 * c i ^ 2 = 0 := by
            intro i
            by_cases hui : u ∈ S i
            · rw [partIndicator_of_mem hui, partIndicator_of_mem (hu12 i hui)]
              simp
            · have hvnot : v ∉ S i := by
                intro hvi
                have hie : i = i₁ := by
                  by_contra hne
                  exact Finset.disjoint_left.1 (hdisj i i₁ hne) hvi hi₂
                subst hie
                exact hui hi₁
              rw [partIndicator_of_not_mem hui, partIndicator_of_not_mem hvnot]
              simp
          rw [Finset.sum_eq_zero fun i _ => hcut i]
          simp
        · have hu2 : partIndicator (S i₂) u = 0 :=
            partIndicator_of_not_mem fun h =>
              Finset.disjoint_left.1 (hdisj i₁ i₂ hij) hi₁ h
          have hv1 : partIndicator (S i₁) v = 0 :=
            partIndicator_of_not_mem fun h =>
              Finset.disjoint_left.1 (hdisj i₂ i₁ (fun h' => hij h'.symm)) hi₂ h
          have hterm1 : (partIndicator (S i₁) u - partIndicator (S i₁) v) ^ 2
              * c i₁ ^ 2 = c i₁ ^ 2 := by rw [hu1, hv1]; simp
          have hterm2 : (partIndicator (S i₂) u - partIndicator (S i₂) v) ^ 2
              * c i₂ ^ 2 = c i₂ ^ 2 := by rw [hu2, hv2]; simp
          have h2 := Finset.sum_le_sum_of_subset_of_nonneg
              (f := fun i => (partIndicator (S i) u - partIndicator (S i) v) ^ 2 * c i ^ 2)
              (Finset.subset_univ (insert i₂ (∅ : Finset (Fin k))))
              (fun i _ _ => hterm i)
          have hne2 : i₂ ∉ (∅ : Finset (Fin k)) := by simp
          rw [Finset.sum_insert hne2, Finset.sum_empty] at h2
          rw [hterm2] at h2
          have h3 := Finset.sum_le_sum_of_subset_of_nonneg
              (f := fun i => (partIndicator (S i) u - partIndicator (S i) v) ^ 2 * c i ^ 2)
              (Finset.subset_univ (insert i₁ (insert i₂ (∅ : Finset (Fin k)))))
              (fun i _ _ => hterm i)
          have hne1 : i₁ ∉ (insert i₂ (∅ : Finset (Fin k))) := by simp [hij]
          rw [Finset.sum_insert hne1, Finset.sum_insert hne2, Finset.sum_empty, hterm1,
            hterm2] at h3
          nlinarith [sq_nonneg (c i₁ + c i₂), h2, h3]
      · push_neg at hv
        rw [multiwayCombination_of_mem hdisj hi₁, multiwayCombination_eq_zero hv]
        have hterm1 : (partIndicator (S i₁) u - partIndicator (S i₁) v) ^ 2
            * c i₁ ^ 2 = c i₁ ^ 2 := by
          rw [hu1, partIndicator_of_not_mem (hv i₁)]
          simp
        have h2 := Finset.sum_le_sum_of_subset_of_nonneg
            (f := fun i => (partIndicator (S i) u - partIndicator (S i) v) ^ 2 * c i ^ 2)
            (Finset.subset_univ (insert i₁ (∅ : Finset (Fin k))))
            (fun i _ _ => hterm i)
        have hne1 : i₁ ∉ (∅ : Finset (Fin k)) := by simp
        rw [Finset.sum_insert hne1, Finset.sum_empty, hterm1] at h2
        nlinarith [sq_nonneg (c i₁), h2]
    · push_neg at hu
      by_cases hv : ∃ i₂ : Fin k, v ∈ S i₂
      · obtain ⟨i₂, hi₂⟩ := hv
        rw [multiwayCombination_eq_zero hu, multiwayCombination_of_mem hdisj hi₂]
        have hterm2 : (partIndicator (S i₂) u - partIndicator (S i₂) v) ^ 2
            * c i₂ ^ 2 = c i₂ ^ 2 := by
          rw [partIndicator_of_not_mem (hu i₂), partIndicator_of_mem hi₂]
          simp
        have h2 := Finset.sum_le_sum_of_subset_of_nonneg
            (f := fun i => (partIndicator (S i) u - partIndicator (S i) v) ^ 2 * c i ^ 2)
            (Finset.subset_univ (insert i₂ (∅ : Finset (Fin k))))
            (fun i _ _ => hterm i)
        have hne2 : i₂ ∉ (∅ : Finset (Fin k)) := by simp
        rw [Finset.sum_insert hne2, Finset.sum_empty, hterm2] at h2
        nlinarith [sq_nonneg (c i₂), h2]
      · push_neg at hv
        rw [multiwayCombination_eq_zero hu, multiwayCombination_eq_zero hv]
        nlinarith [hsumnn]
  -- sum the pointwise bound
  have hrow : ∀ u : V,
      ∑ v, A u v * (multiwayCombination S c u - multiwayCombination S c v) ^ 2
        ≤ ∑ v, A u v * (2 * ∑ i,
            (partIndicator (S i) u - partIndicator (S i) v) ^ 2 * c i ^ 2) :=
    fun u => Finset.sum_le_sum fun v _ =>
      mul_le_mul_of_nonneg_left (hpt u v) (hnn u v)
  have hcutsum : ∀ i : Fin k,
      ∑ u, ∑ v, A u v * (partIndicator (S i) u - partIndicator (S i) v) ^ 2
        = 2 * boundary A (S i) := by
    intro i
    have h := laplacian_quadForm A hA (partIndicator (S i))
    rw [quadForm_laplacian_partIndicator A hA (S i)] at h
    linarith
  have h1 : ∀ u v : V,
      A u v * (2 * ∑ i, (partIndicator (S i) u - partIndicator (S i) v) ^ 2 * c i ^ 2)
        = ∑ i, A u v * (2 * ((partIndicator (S i) u - partIndicator (S i) v) ^ 2
            * c i ^ 2)) := by
    intro u v
    have e1 : (2 * ∑ i : Fin k, (partIndicator (S i) u - partIndicator (S i) v) ^ 2
        * c i ^ 2) = ∑ i : Fin k, 2 * ((partIndicator (S i) u
          - partIndicator (S i) v) ^ 2 * c i ^ 2) :=
      Finset.mul_sum Finset.univ (fun i =>
        (partIndicator (S i) u - partIndicator (S i) v) ^ 2 * c i ^ 2) (2 : ℝ)
    rw [e1, Finset.mul_sum]
  have hmid : (∑ u, ∑ v, A u v * (2 * ∑ i,
          (partIndicator (S i) u - partIndicator (S i) v) ^ 2 * c i ^ 2))
      = 4 * ∑ i, c i ^ 2 * boundary A (S i) := by
    rw [Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => h1 u v)),
      triple_sum_comm (fun (u : V) (v : V) (i : Fin k) =>
        A u v * (2 * ((partIndicator (S i) u - partIndicator (S i) v) ^ 2 * c i ^ 2))),
      Finset.mul_sum Finset.univ (fun i => c i ^ 2 * boundary A (S i)) (4 : ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hre : ∑ u, ∑ v, A u v * (2 * ((partIndicator (S i) u
            - partIndicator (S i) v) ^ 2 * c i ^ 2))
        = ∑ u, ∑ v, c i ^ 2 * 2 * (A u v
            * (partIndicator (S i) u - partIndicator (S i) v) ^ 2) :=
      Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    have efact : c i ^ 2 * 2 * (∑ u, ∑ v, A u v
          * (partIndicator (S i) u - partIndicator (S i) v) ^ 2)
        = ∑ u, ∑ v, c i ^ 2 * 2 * (A u v
            * (partIndicator (S i) u - partIndicator (S i) v) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by rw [Finset.mul_sum]
    rw [hre, ← efact, hcutsum i]
    ring
  calc quadForm (laplacian A) (multiwayCombination S c)
      = (∑ u, ∑ v, A u v * (multiwayCombination S c u
          - multiwayCombination S c v) ^ 2) / 2 :=
        laplacian_quadForm A hA (multiwayCombination S c)
    _ ≤ (∑ u, ∑ v, A u v * (2 * ∑ i,
          (partIndicator (S i) u - partIndicator (S i) v) ^ 2 * c i ^ 2)) / 2 := by
        exact (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)).2
          (Finset.sum_le_sum fun u _ => hrow u)
    _ = 2 * ∑ i, c i ^ 2 * boundary A (S i) := by
        rw [hmid]
        ring

/-! ## The multiway easy direction -/

/-- **The multiway Cheeger easy direction (boundary/volume form).** On
every symmetric nonnegative positive-degree graph, every disjoint family
of `k` nonempty vertex sets certifies
`evals (L_sym) ⟨k−1⟩ ≤ 2 · max_i (boundary (S i) / vol (S i))` — the
higher-order generalization of the delivered
`cheeger_upper_bound_normalized` (its `k = 2` instance at the pair
`S, Sᶜ`), at the every-family form: any concrete disjoint family
certifies, no partition-space minimum is taken. The test family is the
plain part indicators pulled back by `√D` (linearly independent since
`√D` is invertible and the parts are nonempty), the combination bound is
the absorption lemma at constant 2, and the conclusion is the subspace
engine `evals_le_of_linearIndependent` at `L_sym`.

Source (classical background; this is a proof, not an admission):
- Lee, J. R., Gharan, S. O., & Trevisan, L., "Higher-Order Cheeger
  Inequalities", STOC 2012 / J. AMS 27 (2014), §2 (the λ_k ≤ 2ρ_k half,
  subspace form of its test-function argument).

QA: `Scaffold/QA/SpectralGraph/MultiwayCheeger_QA.lean` — the tight
equality instances at `k = n` (K₂ `k = 2`, C₄ `k = 4`), the P₃
non-covering family (`k = 2`), the singleton partition (`k = 3`, joined
to the independently pinned `λ₃ = 2`), the `k = 1` edge instance, and
the overlap fence. -/
theorem cheeger_upper_bound_multiway (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    {k : ℕ} (hk1 : 1 ≤ k) (hkc : k ≤ Fintype.card V)
    (S : Fin k → Finset V) (hne : ∀ i, (S i).Nonempty)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    evals (normalizedLaplacian_symmetric A hA) ⟨k - 1, by omega⟩
      ≤ 2 * Finset.univ.sup' (⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
          (fun i => boundary A (S i) / vol A (S i)) := by
  -- the pulled-back family
  have hbridge : ∀ c : Fin k → ℝ,
      ∑ i, c i • (degreeSqrt A *ᵥ partIndicator (S i))
        = degreeSqrt A *ᵥ multiwayCombination S c := by
    intro c
    funext u
    have hsumapp : (∑ i, c i • (degreeSqrt A *ᵥ partIndicator (S i))) u
        = ∑ i, c i * (degreeSqrt A *ᵥ partIndicator (S i)) u := by
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun i _ => rfl
    rw [hsumapp, degreeSqrt_mulVec, multiwayCombination, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : u ∈ S i
    · simp only [partIndicator, if_pos h, degreeSqrt_mulVec]
      ring
    · simp only [partIndicator, if_neg h, degreeSqrt_mulVec]
      ring
  -- linear independence of the pulled-back family
  have hLI : LinearIndependent ℝ
      (fun i : Fin k => degreeSqrt A *ᵥ partIndicator (S i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum i₀
    have hz : multiwayCombination S c = 0 := by
      funext u
      have h := congrFun hsum u
      rw [hbridge c, degreeSqrt_mulVec] at h
      simp only [Pi.zero_apply] at h
      rcases mul_eq_zero.1 h with h1 | h2
      · exact absurd h1 (Real.sqrt_ne_zero'.2 (hd u))
      · exact h2
    obtain ⟨u₀, hu₀⟩ := hne i₀
    have h := congrFun hz u₀
    rw [multiwayCombination_of_mem hdisj hu₀] at h
    simpa using h
  -- the combination-level Rayleigh bound
  have hbnd : ∀ c : Fin k → ℝ,
      quadForm (normalizedLaplacian A) (∑ i, c i • (degreeSqrt A *ᵥ partIndicator (S i)))
        ≤ (2 * Finset.univ.sup' (⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
              (fun i => boundary A (S i) / vol A (S i)))
          * Matrix.dotProduct (∑ i, c i • (degreeSqrt A *ᵥ partIndicator (S i)))
              (∑ i, c i • (degreeSqrt A *ᵥ partIndicator (S i))) := by
    intro c
    have hQ : quadForm (normalizedLaplacian A)
        (∑ i, c i • (degreeSqrt A *ᵥ partIndicator (S i)))
        = quadForm (laplacian A) (multiwayCombination S c) := by
      rw [hbridge c,
        ← quadForm_laplacian_eq_quadForm_normalizedLaplacian A hd]
    have hN : Matrix.dotProduct (∑ i, c i • (degreeSqrt A *ᵥ partIndicator (S i)))
          (∑ i, c i • (degreeSqrt A *ᵥ partIndicator (S i)))
        = ∑ i, c i ^ 2 * vol A (S i) := by
      rw [hbridge c,
        dotProduct_degreeSqrt_mulVec_multiwayCombination A
          (fun i => le_of_lt (hd i)) hdisj]
    have hvpos : ∀ i : Fin k, 0 < vol A (S i) := fun i =>
      vol_pos_of_pos_deg A hd (hne i)
    have hterm : ∀ i : Fin k, c i ^ 2 * boundary A (S i)
        ≤ (Finset.univ.sup' (⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
              (fun i => boundary A (S i) / vol A (S i)))
          * (c i ^ 2 * vol A (S i)) := by
      intro i
      have hle : boundary A (S i) / vol A (S i)
          ≤ Finset.univ.sup' (⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
              (fun i => boundary A (S i) / vol A (S i)) :=
        ((Finset.le_sup'_iff
            (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
              (Finset.univ : Finset (Fin k)).Nonempty)).2)
          ⟨i, Finset.mem_univ _, le_refl _⟩
      have hbdd : c i ^ 2 * boundary A (S i)
          = (boundary A (S i) / vol A (S i)) * (c i ^ 2 * vol A (S i)) := by
        rw [mul_comm (c i ^ 2) (vol A (S i)), ← mul_assoc,
          div_mul_cancel₀ (boundary A (S i)) (ne_of_gt (hvpos i))]
        ring
      rw [hbdd]
      exact mul_le_mul_of_nonneg_right hle (mul_nonneg (sq_nonneg _) (le_of_lt (hvpos i)))
    have hE := laplacian_quadForm_multiwayCombination_le A hA hnn hdisj c
    have h1 : ∑ i, c i ^ 2 * boundary A (S i)
        ≤ (Finset.univ.sup' (⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
              (fun i => boundary A (S i) / vol A (S i)))
          * ∑ i, c i ^ 2 * vol A (S i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hterm i
    rw [hQ, hN]
    linarith
  exact evals_le_of_linearIndependent (normalizedLaplacian_symmetric A hA)
    hk1 hkc hLI hbnd

/-- **The multiway easy direction at the conductance form.** On families
of at least two parts, every part's complement is nonempty (it contains
the other parts), so `boundary / vol ≤ boundary / min vol volᶜ =
conductance` termwise, and the boundary/volume form transfers. This is
the `k`-way generalization of the delivered
`cheeger_upper_bound_normalized`'s conductance shape. -/
theorem cheeger_upper_bound_multiway_conductance (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    {k : ℕ} (hk2 : 2 ≤ k) (hkc : k ≤ Fintype.card V)
    (S : Fin k → Finset V) (hne : ∀ i, (S i).Nonempty)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    evals (normalizedLaplacian_symmetric A hA) ⟨k - 1, by omega⟩
      ≤ 2 * Finset.univ.sup' (⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
          (fun i => conductance A (S i)) := by
  have hvpos : ∀ i : Fin k, 0 < vol A (S i) := fun i =>
    vol_pos_of_pos_deg A hd (hne i)
  have hvcpos : ∀ i : Fin k, 0 < vol A (S i)ᶜ := by
    intro i
    obtain ⟨j, hj⟩ : ∃ j : Fin k, j ≠ i := by
      have hk : 0 < k := by omega
      by_cases hi0 : (i : ℕ) = 0
      · exact ⟨Fin.mk 1 (by omega), by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.mk_one, Fin.val_one] at this
          omega⟩
      · exact ⟨Fin.mk 0 (by omega), by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_zero] at this
          omega⟩
    have hsub : S j ⊆ (S i)ᶜ := by
      intro x hx
      simp only [Finset.mem_compl]
      exact Finset.disjoint_left.1 (hdisj j i (fun h => hj h)) hx
    have hvj : 0 < vol A (S j) := vol_pos_of_pos_deg A hd (hne j)
    exact lt_of_lt_of_le hvj (vol_le_vol_of_subset A hnn hsub)
  have hmono : Finset.univ.sup' (⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
        (fun i => boundary A (S i) / vol A (S i))
      ≤ Finset.univ.sup' (⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
          (fun i => conductance A (S i)) := by
    refine (Finset.sup'_le_iff
      (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin k)).Nonempty)
      (fun i => boundary A (S i) / vol A (S i))).2 (fun i _ => ?_)
    have hbc : boundary A (S i) / vol A (S i) ≤ conductance A (S i) := by
      show boundary A (S i) / vol A (S i)
        ≤ boundary A (S i) / min (vol A (S i)) (vol A (S i)ᶜ)
      have hminpos : 0 < min (vol A (S i)) (vol A (S i)ᶜ) :=
        lt_min (hvpos i) (hvcpos i)
      rw [div_le_div_iff₀ (hvpos i) hminpos]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _)
        (boundary_nonneg A hnn (S i))
    exact hbc.trans ((Finset.le_sup'_iff (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
      (Finset.univ : Finset (Fin k)).Nonempty)).2 ⟨i, Finset.mem_univ _, le_refl _⟩)
  exact le_trans (cheeger_upper_bound_multiway A hA hnn hd (by omega) hkc S hne
    hdisj) (by linarith)

/-! ## The ρ_k packaging: the partition minimum

The every-family theorems above certify at any concrete disjoint
family; the classical statement form (Lee–Gharan–Trevisan's λ_k ≤ 2ρ_k)
minimizes over k-way *partitions*. The partition space of a finite
vertex type is finite, so the minimum is attained — the every-family
form makes this a pure attainment task, with no new engine content. -/

/-- A k-way partition of the vertex set: `k` nonempty pairwise-disjoint
parts covering `V`. Deliberately a *covering* family (the every-family
theorems above do not require covering; the ρ_k minimum is taken over
the partitions). -/
structure IsMultiwayPartition {k : ℕ} (S : Fin k → Finset V) : Prop where
  /-- every part is nonempty -/
  nonempty : ∀ i, (S i).Nonempty
  /-- distinct parts are disjoint -/
  disjoint : ∀ i j, i ≠ j → Disjoint (S i) (S j)
  /-- the parts cover the vertex set -/
  covers : ∀ v : V, ∃ i, v ∈ S i

/-- The maximum part conductance of a `k`-part family. At `k = 0` the
range is empty and the `sSup ∅ = 0` junk value is returned; every use
is at `k ≥ 1` (any k-way partition has `k ≥ 1` parts). -/
noncomputable def maxPartConductance (A : WAdj (V := V)) {k : ℕ}
    (S : Fin k → Finset V) : ℝ :=
  sSup (Set.range fun i : Fin k => conductance A (S i))

/-- The delivered theorems' `Finset.sup'` maximum is the `sSup` of the
range at every nonempty index type — the join between the family's
statement shapes and the packaged minimum's `sSup` definition. -/
theorem finset_univ_sup'_eq_sSup_range {k : ℕ} (hk : 0 < k) (f : Fin k → ℝ) :
    Finset.univ.sup' (⟨⟨0, hk⟩, Finset.mem_univ _⟩) f = sSup (Set.range f) := by
  have hbdd : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
  refine le_antisymm ?_ ?_
  · refine (Finset.sup'_le_iff (⟨⟨0, hk⟩, Finset.mem_univ _⟩ :
      (Finset.univ : Finset (Fin k)).Nonempty) f).2 fun i _ =>
        le_csSup hbdd (Set.mem_range_self i)
  · refine csSup_le ⟨f ⟨0, hk⟩, Set.mem_range_self _⟩ ?_
    rintro b ⟨i, rfl⟩
    exact (Finset.le_sup'_iff (⟨⟨0, hk⟩, Finset.mem_univ _⟩ :
      (Finset.univ : Finset (Fin k)).Nonempty)).2
      ⟨i, Finset.mem_univ _, le_refl _⟩

/-- A constant family's maximum part conductance is the constant. -/
theorem maxPartConductance_const {k : ℕ} (hk : 0 < k) {A : WAdj (V := V)}
    {S : Fin k → Finset V} {c : ℝ} (h : ∀ i, conductance A (S i) = c) :
    maxPartConductance A S = c := by
  have hne : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  rw [maxPartConductance, show (fun i : Fin k => conductance A (S i))
      = fun _ => c from funext h, Set.range_const, csSup_singleton]

/-- **ρ_k, the multiway expansion constant**: the minimum, over k-way
partitions, of the maximum part conductance — the classical object of
the higher-order Cheeger easy direction. If no k-way partition exists
(`k > card V`), the value set is empty and the `sInf ∅ = 0` junk value
is returned; every consumer carries partition existence (or
`k ≤ card V`, which supplies it) as a hypothesis. -/
noncomputable def multiwayExpansion (A : WAdj (V := V)) (k : ℕ) : ℝ :=
  sInf {m : ℝ | ∃ S : Fin k → Finset V, IsMultiwayPartition S ∧
    maxPartConductance A S = m}

/-- The ρ_k value set is finite: it is a subset of the range of
`maxPartConductance` over the (finite) type of k-part families. -/
private theorem partitionValueSet_finite (A : WAdj (V := V)) (k : ℕ) :
    {m : ℝ | ∃ S : Fin k → Finset V, IsMultiwayPartition S ∧
      maxPartConductance A S = m}.Finite :=
  Set.Finite.subset (Set.finite_range
      (fun S : Fin k → Finset V => maxPartConductance A S))
    (by rintro m ⟨S, hp, hm⟩; exact ⟨S, hm⟩)

/-- ρ_k is at most every partition's maximum part conductance (the
`csInf` bound; the value set's finiteness supplies `BddBelow`). -/
theorem multiwayExpansion_le (A : WAdj (V := V)) {k : ℕ} {S : Fin k → Finset V}
    (hp : IsMultiwayPartition S) :
    multiwayExpansion A k ≤ maxPartConductance A S :=
  csInf_le (partitionValueSet_finite A k).bddBelow ⟨S, hp, rfl⟩

/-- **Attainment over the finite partition space.** The ρ_k infimum is
realized by an actual k-way partition: the value set is finite (a
subset of the range over the finite family type), so its `sInf` is a
member. This is the only new content of the packaging — the every-family
form already certifies at the attained minimizer. -/
theorem exists_isMultiwayPartition_eq_multiwayExpansion (A : WAdj (V := V))
    (k : ℕ) (hex : ∃ S : Fin k → Finset V, IsMultiwayPartition S) :
    ∃ T : Fin k → Finset V, IsMultiwayPartition T ∧
      maxPartConductance A T = multiwayExpansion A k := by
  have hsne : {m : ℝ | ∃ S : Fin k → Finset V, IsMultiwayPartition S ∧
      maxPartConductance A S = m}.Nonempty := by
    obtain ⟨S, hp⟩ := hex
    exact ⟨_, S, hp, rfl⟩
  obtain ⟨S, hp, hm⟩ := hsne.csInf_mem (partitionValueSet_finite A k)
  exact ⟨S, hp, hm⟩

/-- **The ρ_k form of the multiway Cheeger easy direction.** On every
symmetric nonnegative positive-degree graph, for every `k` with
`2 ≤ k ≤ card V` and at least one k-way partition:
`evals (L_sym) ⟨k−1⟩ ≤ 2 · ρ_k` — the classical minimum-over-partitions
statement, obtained by attaining the minimum
(`exists_isMultiwayPartition_eq_multiwayExpansion`) and consuming the
every-family conductance theorem at the minimizer. No new engine
content: attainment is the whole proof.

Source (classical background; this is a proof, not an admission):
- Lee, J. R., Gharan, S. O., & Trevisan, L., "Higher-Order Cheeger
  Inequalities", STOC 2012 / J. AMS 27 (2014), §1 (the λ_k ≤ 2ρ_k
  statement form).

QA: `Scaffold/QA/SpectralGraph/MultiwayCheeger_QA.lean` — ρ₂(C₄) = 1/2
exact (the theorem joined to the independently pinned λ₂ = 1 forces the
minimum strictly below the diagonal partition's value), ρ₂(K₂) = 1 and
ρ₃(P₃) = 1 at the pinned top eigenvalues, and the empty-set junk fence
at k = 3 on K₂ (no 3-partition exists in two vertices; ρ₃ = sInf ∅ = 0
— the partition-existence hypothesis is load-bearing). -/
theorem cheeger_upper_bound_multiway_rhoK (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i) {k : ℕ} (hk : 2 ≤ k)
    (hkc : k ≤ Fintype.card V)
    (hex : ∃ S : Fin k → Finset V, IsMultiwayPartition S) :
    evals (normalizedLaplacian_symmetric A hA) ⟨k - 1, by omega⟩
      ≤ 2 * multiwayExpansion A k := by
  obtain ⟨T, hp, hTeq⟩ :=
    exists_isMultiwayPartition_eq_multiwayExpansion A k hex
  have h1 := cheeger_upper_bound_multiway_conductance A hA hnn hd hk hkc T
    hp.nonempty hp.disjoint
  rw [finset_univ_sup'_eq_sSup_range (by omega : 0 < k)
    (fun i => conductance A (T i))] at h1
  calc evals (normalizedLaplacian_symmetric A hA) ⟨k - 1, by omega⟩
      ≤ 2 * maxPartConductance A T := h1
    _ = 2 * multiwayExpansion A k := by rw [hTeq]

/-- **k-way partitions exist whenever `1 ≤ k ≤ card V`.** Constructed
from an injection `Fin k ↪ V`: singleton parts, with the designated
last part absorbing the complement of the injection's range. This
discharges the `hex` hypothesis of the ρ_k statements in the common
case. -/
theorem exists_isMultiwayPartition_of_le_card {k : ℕ} (hk1 : 1 ≤ k)
    (hkc : k ≤ Fintype.card V) :
    ∃ S : Fin k → Finset V, IsMultiwayPartition S := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin k ↪ V) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hkc)
  set last : Fin k := ⟨k - 1, by omega⟩ with hlast
  refine ⟨fun i => if i = last
      then insert (e i) (Finset.univ \ Finset.image e Finset.univ)
      else {e i}, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = last
    · simp only [h, if_pos]
      exact Finset.insert_nonempty _ _
    · simp only [if_neg h]
      exact Finset.singleton_nonempty _
  · intro i j hij
    by_cases hi : i = last <;> by_cases hj : j = last
    · exact absurd (hi.trans hj.symm) hij
    · rw [if_pos hi, if_neg hj, Finset.disjoint_insert_left]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_singleton]
        exact fun h => hij (e.injective h)
      · rw [Finset.disjoint_singleton_right]
        intro hmem
        exact (Finset.mem_sdiff.1 hmem).2
          (Finset.mem_image_of_mem e (Finset.mem_univ j))
    · rw [if_neg hi, if_pos hj, Finset.disjoint_insert_right]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_singleton]
        exact fun h => hij (e.injective h.symm)
      · rw [Finset.disjoint_singleton_left]
        intro hmem
        exact (Finset.mem_sdiff.1 hmem).2
          (Finset.mem_image_of_mem e (Finset.mem_univ i))
    · rw [if_neg hi, if_neg hj]
      exact Finset.disjoint_singleton.2 (fun h => hij (e.injective h))
  · intro v
    by_cases hv : v ∈ Finset.image e Finset.univ
    · obtain ⟨i, _, hvi⟩ := Finset.mem_image.1 hv
      by_cases h : i = last
      · subst h
        refine ⟨last, ?_⟩
        rw [if_pos rfl]
        exact Finset.mem_insert.2 (Or.inl hvi.symm)
      · refine ⟨i, ?_⟩
        rw [if_neg h]
        exact Finset.mem_singleton.2 hvi.symm
    · refine ⟨last, ?_⟩
      rw [if_pos rfl]
      exact Finset.mem_insert.2 (Or.inr (Finset.mem_sdiff.2 ⟨Finset.mem_univ v, hv⟩))

end SpectralGraphTheory
