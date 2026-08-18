/-
  Fiedler_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.Fiedler` (Phase A of
  `proposals/fiedler-partitioning.md`): the Fiedler vector and its
  sign-pattern partition.

  - Positive witness 1 (`K₂`, reusing the `Variational_QA` fixture):
    the partition is pinned, through the eigenvector equation and
    orthogonality, to one of the two singleton halves — a genuine
    bipartition of `K₂`, with its boundary computed to be the single
    edge.
  - Positive witness 2 (the `P₄` barbell — two near-cliques `K₂ + K₂`
    joined by one bridge edge — the proposal's named example shape):
    `lambda2 ≤ 1` through the proved Rayleigh engine at the known-good
    cut indicator, `lambda2 ≠ 1` through the eigen equations, and the
    sign pattern derived from the eigen equations forces the Fiedler
    partition to be exactly the known good cut `{0, 1}` or its
    complement `{2, 3}` — boundary `1`, volume `3`, conductance `1/3`.
  - Negative witness (two disjoint edges on `Fin 4`, reusing the
    `Variational_QA` fixture): the connectivity/`lambda2 > 0`
    hypothesis is load-bearing — the support graph is not connected,
    `lambda2 = 0`, and `onesVec` is a nonzero eigenvector at that same
    eigenvalue whose positive set is all of `univ`, so no
    nonempty/proper conclusion can follow from the eigen-property
    alone.

  All proofs are real Lean proofs (no `sorry`/`admit`). The Fiedler
  vector itself is noncomputable (spectral theorem plus classical
  choice), so the witnesses pin it through its proved defining
  properties — the eigenvector equation, unit norm, and orthogonality
  — rather than by deciding entries.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Fiedler
import Scaffold.QA.SpectralGraph.Variational_QA

open scoped BigOperators Classical Matrix

namespace SpectralGraphTheory.QA

/-!
## Positive witness 1: `K₂`
-/

section FiedlerK2

/-- `λ₂(K₂) = 2` is positive, so the interface-form partition facts
apply on the edge. -/
theorem k2_lambda2_pos_QA :
    0 < lambda2 k2Adj k2Adj_symmetric (le_refl 2) := by
  rw [k2_lambda2_eq_two]
  norm_num

/-- The Fiedler entries of `K₂` sum to zero (orthogonality to the
constants, instantiated). -/
theorem k2_fiedler_sum_QA :
    ∑ i, fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) i = 0 :=
  fiedlerVector_sum_eq_zero k2Adj k2Adj_symmetric (le_refl 2)
    k2_lambda2_pos_QA

/-- The Fiedler vector of `K₂` is antisymmetric: `f 1 = -f 0`, computed
from the zero sum. -/
theorem k2_fiedler_antisymm_QA :
    fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 1
      = -fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0 := by
  have h := k2_fiedler_sum_QA
  simp only [Fin.sum_univ_two] at h
  linarith

/-- The leading Fiedler entry of `K₂` is nonzero — by unit norm, since
antisymmetry would otherwise force the whole vector to vanish. -/
theorem k2_fiedler_zero_ne_QA :
    fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0 ≠ 0 := by
  intro h
  have h1 := k2_fiedler_antisymm_QA
  rw [h] at h1
  have hn := fiedlerVector_norm k2Adj k2Adj_symmetric (le_refl 2)
  simp only [Matrix.dotProduct, Fin.sum_univ_two, h, h1] at hn
  norm_num at hn

/-- **The partition of `K₂` is pinned**: one of the two singleton
halves — the sign pattern of an antisymmetric nonzero vector. -/
theorem k2_fiedlerPartition_eq_QA :
    fiedlerPartition k2Adj k2Adj_symmetric (le_refl 2) = ({0} : Finset (Fin 2))
    ∨ fiedlerPartition k2Adj k2Adj_symmetric (le_refl 2) = ({1} : Finset (Fin 2)) := by
  by_cases h0 : 0 ≤ fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0
  · have h0pos : 0 < fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0 := by
      rcases lt_or_eq_of_le h0 with h | h
      · exact h
      · exact absurd h.symm k2_fiedler_zero_ne_QA
    have h1neg : fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 1 < 0 := by
      rw [k2_fiedler_antisymm_QA]
      linarith
    left
    refine Finset.ext fun i => ?_
    simp only [fiedlerPartition_mem, Finset.mem_singleton]
    fin_cases i
    · exact ⟨fun _ => rfl, fun _ => h0pos.le⟩
    · exact ⟨fun h => absurd h (not_le.2 h1neg), fun h => by simp at h⟩
  · have h0neg : fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0 < 0 := by
      by_contra hc
      push_neg at hc
      exact h0 hc
    have h1pos : 0 < fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 1 := by
      rw [k2_fiedler_antisymm_QA]
      linarith
    right
    refine Finset.ext fun i => ?_
    simp only [fiedlerPartition_mem, Finset.mem_singleton]
    fin_cases i
    · exact ⟨fun h => absurd h (not_le.2 h0neg), fun h => by simp at h⟩
    · exact ⟨fun _ => rfl, fun _ => h1pos.le⟩

/-- The `K₂` Fiedler partition has exactly one vertex — a genuine
bipartition. -/
theorem k2_fiedlerPartition_card_QA :
    (fiedlerPartition k2Adj k2Adj_symmetric (le_refl 2)).card = 1 := by
  rcases k2_fiedlerPartition_eq_QA with h | h <;> rw [h] <;> simp

/-- Interface instantiation: nonempty on the edge. -/
theorem k2_fiedlerPartition_nonempty_QA :
    (fiedlerPartition k2Adj k2Adj_symmetric (le_refl 2)).Nonempty :=
  fiedlerPartition_nonempty_of_pos k2Adj k2Adj_symmetric (le_refl 2)
    k2_lambda2_pos_QA

/-- Interface instantiation: proper on the edge. -/
theorem k2_fiedlerPartition_ne_univ_QA :
    fiedlerPartition k2Adj k2Adj_symmetric (le_refl 2) ≠ Finset.univ :=
  fiedlerPartition_ne_univ_of_pos k2Adj k2Adj_symmetric (le_refl 2)
    k2_lambda2_pos_QA

theorem k2_compl_singleton_QA :
    ({0} : Finset (Fin 2))ᶜ = {1} := by decide

theorem k2_compl_singleton'_QA :
    ({1} : Finset (Fin 2))ᶜ = {0} := by decide

/-- The boundary of either half is the single crossing edge — computed
from the definitions, independently of any boundary theorem. -/
theorem k2_fiedlerPartition_boundary_QA :
    boundary k2Adj (fiedlerPartition k2Adj k2Adj_symmetric (le_refl 2)) = 1 := by
  rcases k2_fiedlerPartition_eq_QA with h | h
  · rw [h]
    simp only [boundary, Finset.sum_singleton, k2_compl_singleton_QA]
    simp [k2Adj]
  · rw [h]
    simp only [boundary, Finset.sum_singleton, k2_compl_singleton'_QA]
    simp [k2Adj]
end FiedlerK2

/-!
## Positive witness 2: the `P₄` barbell — two `K₂` near-cliques joined
by one bridge edge `0 — 1 — 2 — 3`

The known good cut is the middle bisection `{0, 1} | {2, 3}` (boundary
`1`, volume `3`, conductance `1/3`). The Fiedler partition is *derived*
— from the eigenvector equation, unit norm, and orthogonality — to be
exactly this cut or its complement.
-/

section FiedlerPath4

/-- Adjacency of the four-vertex path `0 — 1 — 2 — 3`, as a matrix
literal (`connPathAdj` pattern). -/
def path4Adj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of !![0, 1, 0, 0; 1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0]

theorem path4Adj_symmetric : path4Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [path4Adj] <;> try rfl

theorem path4Adj_nonneg : ∀ i j, 0 ≤ path4Adj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [path4Adj]
  all_goals try exact le_refl _

/-- The three edges of the path, as support-graph adjacencies. -/
theorem path4_adj01_QA :
    (supportGraph path4Adj path4Adj_symmetric).Adj (0 : Fin 4) 1 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [path4Adj]⟩

theorem path4_adj12_QA :
    (supportGraph path4Adj path4Adj_symmetric).Adj (1 : Fin 4) 2 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [path4Adj]⟩

theorem path4_adj23_QA :
    (supportGraph path4Adj path4Adj_symmetric).Adj (2 : Fin 4) 3 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [path4Adj]⟩

/-- The support graph of the path is connected: every vertex is
reachable from `0` along the path. -/
theorem path4_supportGraph_connected :
    (supportGraph path4Adj path4Adj_symmetric).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons path4_adj01_QA SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons path4_adj01_QA
      (SimpleGraph.Walk.cons path4_adj12_QA SimpleGraph.Walk.nil)⟩
  · exact ⟨SimpleGraph.Walk.cons path4_adj01_QA
      (SimpleGraph.Walk.cons path4_adj12_QA
        (SimpleGraph.Walk.cons path4_adj23_QA SimpleGraph.Walk.nil))⟩

/-- Interface instantiation: the algebraic-connectivity certificate
applies, `0 < λ₂(P₄)`. -/
theorem path4_lambda2_pos_QA :
    0 < lambda2 path4Adj path4Adj_symmetric (by norm_num) :=
  lambda2_pos_of_connected path4Adj path4Adj_symmetric path4Adj_nonneg
    (by norm_num) path4_supportGraph_connected

/-- The cut indicator of the known good cut. -/
def bar4w : Fin 4 → ℝ := ![1, 1, -1, -1]

theorem bar4w_ne_zero : bar4w ≠ 0 := by
  intro h
  have h0 : bar4w 0 = 0 := congrFun h 0
  simp [bar4w] at h0

theorem bar4w_orth :
    Matrix.dotProduct bar4w onesVec = 0 := by
  simp [Matrix.dotProduct, onesVec, bar4w, Fin.sum_univ_four]

/-- The Laplacian action on the cut indicator, computed entrywise from
the diffusion form and the row profiles. -/
theorem bar4w_mulVec_QA :
    (laplacian path4Adj).mulVec bar4w = ![0, 2, -2, 0] := by
  funext i
  rw [laplacian_mulVec_apply]
  fin_cases i <;>
    simp only [Fin.sum_univ_four, path4Adj, bar4w, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons,
      Matrix.of_apply] <;>
    norm_num

theorem bar4w_quadForm :
    quadForm (laplacian path4Adj) bar4w = 4 := by
  show Matrix.dotProduct bar4w ((laplacian path4Adj).mulVec bar4w) = 4
  rw [bar4w_mulVec_QA]
  simp only [Matrix.dotProduct, bar4w, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.head_cons]
  norm_num

theorem bar4w_dotProduct :
    Matrix.dotProduct bar4w bar4w = 4 := by
  simp only [Matrix.dotProduct, bar4w, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.head_cons]
  norm_num

/-- **`λ₂(P₄) ≤ 1`** through the proved Rayleigh engine at the known
good cut indicator: the only crossing edge contributes `(1 - (-1))² =
4` energy for norm-squared `4`. -/
theorem path4_lambda2_le_one_QA :
    lambda2 path4Adj path4Adj_symmetric (by norm_num) ≤ 1 := by
  rw [lambda2_eq_secondEval]
  have h := secondEval_le_rayleigh (laplacian_symmetric path4Adj
      path4Adj_symmetric)
    (laplacian_psd path4Adj path4Adj_symmetric path4Adj_nonneg)
    (laplacian_ones_in_kernel path4Adj) (by norm_num)
    (x := bar4w) bar4w_ne_zero bar4w_orth
  have hr : rayleigh (laplacian path4Adj) bar4w = 1 := by
    rw [rayleigh, if_neg bar4w_ne_zero, bar4w_quadForm, bar4w_dotProduct]
    norm_num
  rw [hr] at h
  linarith

/-- The entrywise eigen equations for the Fiedler vector of `P₄`, in
diffusion form. -/
theorem path4_eigen_entries_QA (i : Fin 4) :
    ∑ j, path4Adj i j * (fiedlerVector path4Adj path4Adj_symmetric (by norm_num) i
        - fiedlerVector path4Adj path4Adj_symmetric (by norm_num) j)
      = lambda2 path4Adj path4Adj_symmetric (by norm_num)
        * fiedlerVector path4Adj path4Adj_symmetric (by norm_num) i := by
  have he := fiedlerVector_eigen path4Adj path4Adj_symmetric (by norm_num)
  have hi := congrFun he i
  rw [laplacian_mulVec_apply] at hi
  exact hi

/-- The endpoint eigen relations, evaluated from the sparsity of the
path. -/
theorem path4_eigen_e0_QA :
    fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 0
        - fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 1
      = lambda2 path4Adj path4Adj_symmetric (by norm_num)
        * fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 0 := by
  simpa [Fin.sum_univ_four, path4Adj] using path4_eigen_entries_QA 0

theorem path4_eigen_e1_QA :
    (fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 1
        - fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 0)
      + (fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 1
        - fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 2)
      = lambda2 path4Adj path4Adj_symmetric (by norm_num)
        * fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 1 := by
  simpa [Fin.sum_univ_four, path4Adj] using path4_eigen_entries_QA 1

theorem path4_eigen_e3_QA :
    fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 3
        - fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 2
      = lambda2 path4Adj path4Adj_symmetric (by norm_num)
        * fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 3 := by
  simpa [Fin.sum_univ_four, path4Adj] using path4_eigen_entries_QA 3

/-- **`λ₂(P₄) ≠ 1`**: at eigenvalue `1` the endpoint equations force
`f 1 = 0` and `f 2 = 0`, the middle equation then forces `f 0 = 0`,
and the zero sum forces `f 3 = 0` — contradicting unit norm. -/
theorem path4_lambda2_ne_one_QA :
    lambda2 path4Adj path4Adj_symmetric (by norm_num) ≠ 1 := by
  intro heq
  have e0 := path4_eigen_e0_QA
  have e1 := path4_eigen_e1_QA
  have e3 := path4_eigen_e3_QA
  rw [heq] at e0 e1 e3
  simp only [one_mul] at e0 e1 e3
  have hf1 : fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 1 = 0 := by
    linarith [e0]
  have hf2 : fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 2 = 0 := by
    linarith [e3]
  have hf0 : fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 0 = 0 := by
    linarith [e1, hf1, hf2]
  have hsum := fiedlerVector_sum_eq_zero path4Adj path4Adj_symmetric
    (by norm_num) path4_lambda2_pos_QA
  simp only [Fin.sum_univ_four] at hsum
  have hf3 : fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 3 = 0 := by
    linarith
  apply fiedlerVector_ne_zero path4Adj path4Adj_symmetric (by norm_num)
  funext i
  fin_cases i
  · simp only [Pi.zero_apply]; exact hf0
  · simp only [Pi.zero_apply]; exact hf1
  · simp only [Pi.zero_apply]; exact hf2
  · simp only [Pi.zero_apply]; exact hf3

theorem path4_lambda2_lt_one_QA :
    lambda2 path4Adj path4Adj_symmetric (by norm_num) < 1 :=
  lt_of_le_of_ne path4_lambda2_le_one_QA path4_lambda2_ne_one_QA

/-- The Fiedler sign relations on `P₄`: the middle entries are damped
copies of the endpoints (`f 1 = (1 - λ) f 0`, `f 2 = (1 - λ) f 3`),
the endpoints are opposite (`f 3 = -f 0`), and the leading entry is
nonzero. Everything is derived from the eigen equations plus the zero
sum — the sign pattern of the classic Fiedler picture. -/
theorem path4_fiedler_relations_QA :
    fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 1
        = (1 - lambda2 path4Adj path4Adj_symmetric (by norm_num))
          * fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 0
      ∧ fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 2
        = (1 - lambda2 path4Adj path4Adj_symmetric (by norm_num))
          * fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 3
      ∧ fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 3
        = -fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 0
      ∧ fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 0 ≠ 0 := by
  have hl := path4_lambda2_lt_one_QA
  have h1 : fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 1
      = fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 0
        - lambda2 path4Adj path4Adj_symmetric (by norm_num)
          * fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 0 := by
    linarith [path4_eigen_e0_QA]
  have h2 : fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 2
      = fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 3
        - lambda2 path4Adj path4Adj_symmetric (by norm_num)
          * fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 3 := by
    linarith [path4_eigen_e3_QA]
  have hsum := fiedlerVector_sum_eq_zero path4Adj path4Adj_symmetric
    (by norm_num) path4_lambda2_pos_QA
  simp only [Fin.sum_univ_four] at hsum
  have key : (2 - lambda2 path4Adj path4Adj_symmetric (by norm_num))
      * (fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 0
        + fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 3) = 0 := by
    linear_combination hsum - h1 - h2
  have h03 : fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 0
      + fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 3 = 0 := by
    exact (mul_eq_zero.1 key).resolve_left (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination h1
  · linear_combination h2
  · linarith
  · intro h
    have z1 : fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 1 = 0 := by
      rw [h1, h, mul_zero, sub_zero]
    have z3 : fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 3 = 0 := by
      linarith
    have z2 : fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 2 = 0 := by
      rw [h2, z3, mul_zero, sub_zero]
    apply fiedlerVector_ne_zero path4Adj path4Adj_symmetric (by norm_num)
    funext i
    fin_cases i
    · simp only [Pi.zero_apply]; exact h
    · simp only [Pi.zero_apply]; exact z1
    · simp only [Pi.zero_apply]; exact z2
    · simp only [Pi.zero_apply]; exact z3

/-- **The Fiedler partition of `P₄` is exactly the known good cut**
`{0, 1}` (or its complement `{2, 3}`, the same cut up to
complementation): the middle entries share their endpoint's sign, and
the endpoints have opposite signs. -/
theorem path4_fiedlerPartition_eq_QA :
    fiedlerPartition path4Adj path4Adj_symmetric (by norm_num)
      = ({0, 1} : Finset (Fin 4))
    ∨ fiedlerPartition path4Adj path4Adj_symmetric (by norm_num)
      = ({2, 3} : Finset (Fin 4)) := by
  obtain ⟨h1, h2, h3, h0ne⟩ := path4_fiedler_relations_QA
  rcases lt_or_gt_of_ne (Ne.symm h0ne) with h0pos | h0neg
  · have p1 : 0 < fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 1 := by
      rw [h1]
      exact mul_pos (by linarith [path4_lambda2_lt_one_QA]) h0pos
    have n3 : fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 3 < 0 := by
      rw [h3]
      linarith
    have n2 : fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 2 < 0 := by
      rw [h2]
      exact mul_neg_of_pos_of_neg (by linarith [path4_lambda2_lt_one_QA])
        (by rw [h3]; linarith)
    left
    refine Finset.ext fun i => ?_
    simp only [fiedlerPartition_mem, Finset.mem_insert, Finset.mem_singleton]
    fin_cases i
    · exact ⟨fun _ => Or.inl rfl, fun _ => h0pos.le⟩
    · exact ⟨fun _ => Or.inr rfl, fun _ => p1.le⟩
    · exact ⟨fun h => absurd h (not_le.2 n2), fun h => by simp at h⟩
    · exact ⟨fun h => absurd h (not_le.2 n3), fun h => by simp at h⟩
  · have n1 : fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 1 < 0 := by
      rw [h1]
      exact mul_neg_of_pos_of_neg (by linarith [path4_lambda2_lt_one_QA]) h0neg
    have p3 : 0 < fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 3 := by
      rw [h3]
      linarith
    have p2 : 0 < fiedlerVector path4Adj path4Adj_symmetric (by norm_num) 2 := by
      rw [h2]
      exact mul_pos (by linarith [path4_lambda2_lt_one_QA]) p3
    right
    refine Finset.ext fun i => ?_
    simp only [fiedlerPartition_mem, Finset.mem_insert, Finset.mem_singleton]
    fin_cases i
    · exact ⟨fun h => absurd h (not_le.2 h0neg), fun h => by simp at h⟩
    · exact ⟨fun h => absurd h (not_le.2 n1), fun h => by simp at h⟩
    · exact ⟨fun _ => Or.inl rfl, fun _ => p2.le⟩
    · exact ⟨fun _ => Or.inr rfl, fun _ => p3.le⟩

/-- The partition has exactly two vertices of the four. -/
theorem path4_fiedlerPartition_card_QA :
    (fiedlerPartition path4Adj path4Adj_symmetric (by norm_num)).card = 2 := by
  rcases path4_fiedlerPartition_eq_QA with h | h <;> rw [h] <;> simp

/-- Interface instantiation: nonempty on the barbell. -/
theorem path4_fiedlerPartition_nonempty_QA :
    (fiedlerPartition path4Adj path4Adj_symmetric (by norm_num)).Nonempty :=
  fiedlerPartition_nonempty path4Adj path4Adj_symmetric path4Adj_nonneg
    (by norm_num) path4_supportGraph_connected

/-- Interface instantiation: proper on the barbell. -/
theorem path4_fiedlerPartition_ne_univ_QA :
    fiedlerPartition path4Adj path4Adj_symmetric (by norm_num) ≠ Finset.univ :=
  fiedlerPartition_ne_univ path4Adj path4Adj_symmetric path4Adj_nonneg
    (by norm_num) path4_supportGraph_connected

theorem path4_compl01_QA :
    ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide

theorem path4_compl23_QA :
    ({2, 3} : Finset (Fin 4))ᶜ = {0, 1} := by decide

/-- Degrees of the path: end vertices have degree `1`, inner vertices
degree `2` — computed from the row profiles. -/
theorem path4_deg_0 : deg path4Adj 0 = 1 := by
  simp only [deg, Fin.sum_univ_four, path4Adj]
  norm_num

theorem path4_deg_1 : deg path4Adj 1 = 2 := by
  simp only [deg, Fin.sum_univ_four, path4Adj]
  norm_num

theorem path4_deg_2 : deg path4Adj 2 = 2 := by
  simp only [deg, Fin.sum_univ_four, path4Adj]
  norm_num

theorem path4_deg_3 : deg path4Adj 3 = 1 := by
  norm_num [deg, Fin.sum_univ_four, path4Adj, Matrix.vecHead, Matrix.vecTail]

/-- Row sums of the adjacency against the known good cut, via the
complement split of the full row (`Cuts_QA` pattern). -/
theorem path4_row0_compl_sum :
    ∑ j in ({0, 1} : Finset (Fin 4))ᶜ, path4Adj 0 j = 0 := by
  have hsplit := Finset.sum_add_sum_compl
    ({0, 1} : Finset (Fin 4)) (fun j => path4Adj 0 j)
  have hin : ∑ j in ({0, 1} : Finset (Fin 4)), path4Adj 0 j = 1 := by
    rw [Finset.sum_pair (by decide)]
    simp [path4Adj]
  have htot : ∑ j in (Finset.univ : Finset (Fin 4)), path4Adj 0 j = 1 :=
    path4_deg_0
  linarith

theorem path4_row1_compl_sum :
    ∑ j in ({0, 1} : Finset (Fin 4))ᶜ, path4Adj 1 j = 1 := by
  have hsplit := Finset.sum_add_sum_compl
    ({0, 1} : Finset (Fin 4)) (fun j => path4Adj 1 j)
  have hin : ∑ j in ({0, 1} : Finset (Fin 4)), path4Adj 1 j = 1 := by
    rw [Finset.sum_pair (by decide)]
    simp [path4Adj]
  have htot : ∑ j in (Finset.univ : Finset (Fin 4)), path4Adj 1 j = 2 :=
    path4_deg_1
  linarith

/-- The boundary of the known good cut is the single bridge edge. -/
theorem path4_boundary_cut01_QA :
    boundary path4Adj ({0, 1} : Finset (Fin 4)) = 1 := by
  simp only [boundary]
  rw [Finset.sum_pair (by decide), path4_row0_compl_sum, path4_row1_compl_sum]
  norm_num

/-- By cut duality the complement cut has the same boundary. -/
theorem path4_boundary_cut23_QA :
    boundary path4Adj ({2, 3} : Finset (Fin 4)) = 1 := by
  rw [← path4_compl01_QA, ← boundary_compl path4Adj path4Adj_symmetric]
  exact path4_boundary_cut01_QA

/-- **The Fiedler partition of the barbell crosses exactly the bridge
edge** — the known good cut, checked against the computed boundary. -/
theorem path4_fiedlerPartition_boundary_QA :
    boundary path4Adj (fiedlerPartition path4Adj path4Adj_symmetric (by norm_num))
      = 1 := by
  rcases path4_fiedlerPartition_eq_QA with h | h
  · rw [h]; exact path4_boundary_cut01_QA
  · rw [h]; exact path4_boundary_cut23_QA

/-- The volume of the known good cut: the two halves carry degrees `1`
and `2`. -/
theorem path4_vol_cut01_QA :
    vol path4Adj ({0, 1} : Finset (Fin 4)) = 3 := by
  simp only [vol]
  rw [Finset.sum_pair (by decide), path4_deg_0, path4_deg_1]
  norm_num

theorem path4_vol_cut23_QA :
    vol path4Adj ({2, 3} : Finset (Fin 4)) = 3 := by
  simp only [vol]
  rw [Finset.sum_pair (by decide), path4_deg_2, path4_deg_3]
  norm_num

/-- The conductance of the Fiedler partition is the bridge fraction
`1/3` — the quality of the known good cut. -/
theorem path4_fiedlerPartition_conductance_QA :
    conductance path4Adj (fiedlerPartition path4Adj path4Adj_symmetric (by norm_num))
      = 1 / 3 := by
  rcases path4_fiedlerPartition_eq_QA with h | h
  · rw [h, conductance, path4_boundary_cut01_QA, path4_vol_cut01_QA,
      path4_compl01_QA, path4_vol_cut23_QA]
    norm_num
  · rw [h, conductance, path4_boundary_cut23_QA, path4_vol_cut23_QA,
      path4_compl23_QA, path4_vol_cut01_QA]
    norm_num

end FiedlerPath4


/-!
## Negative witness: the connectivity/`lambda2 > 0` hypothesis is
load-bearing

On two disjoint edges (the `Variational_QA` fixture), the support graph
is not connected, `lambda2 = 0` (so the sanity theorems' hypothesis
fails), and the all-ones vector is a genuine nonzero eigenvector at
that same eigenvalue — satisfying exactly the eigen-equation
`fiedlerVector_eigen` states — yet its positive set is all of `univ`.
So neither nonempty-with-complement-possible nor properness can follow
from the eigen-property alone; `0 < lambda2` (equivalently, via
`lambda2_pos_of_connected`'s contrapositive, connectivity) is what
rules out the degenerate sign pattern.
-/

section FiedlerTwoEdge

/-- Every positive weight of the disconnected fixture stays inside one
block `{0, 1}` or `{2, 3}`. -/
theorem twoEdgeAdj_blocks : ∀ u v : Fin 4, 0 < twoEdgeAdj u v →
    ((u : ℕ) ≤ 1 ↔ (v : ℕ) ≤ 1) := by
  intro u v h
  simp only [twoEdgeAdj, Matrix.of_apply] at h
  split at h
  · rename_i hcond
    obtain ⟨-, heq⟩ := hcond
    constructor
    · intro hu
      rw [← heq]
      exact hu
    · intro hv
      rw [heq]
      exact hv
  · exact absurd h (by norm_num)

/-- Support-graph walks of the fixture never change block. -/
theorem twoEdge_walk_blocks {u v : Fin 4}
    (w : (supportGraph twoEdgeAdj twoEdgeAdj_symmetric).Walk u v) :
    ((u : ℕ) ≤ 1 ↔ (v : ℕ) ≤ 1) := by
  induction w with
  | nil => rfl
  | cons hadj _ ih =>
    exact (twoEdgeAdj_blocks _ _ ((supportGraph_adj.1 hadj).2)).trans ih

/-- The support graph of the fixture is not connected: a walk from `0`
to `2` would have to change block. -/
theorem twoEdgeAdj_not_connected :
    ¬(supportGraph twoEdgeAdj twoEdgeAdj_symmetric).Connected := by
  intro hconn
  obtain ⟨w⟩ := hconn 0 2
  have hb := twoEdge_walk_blocks w
  rw [show (0 : Fin 4).val = 0 from rfl, show (2 : Fin 4).val = 2 from rfl] at hb
  omega

/-- The sanity theorems' hypothesis fails here: `λ₂ = 0`. -/
theorem twoEdge_lambda2_not_pos_QA :
    ¬ 0 < lambda2 twoEdgeAdj twoEdgeAdj_symmetric (by norm_num) := by
  rw [twoEdge_lambda2_eq_zero_QA]
  norm_num

/-- `onesVec` satisfies the same eigen-equation `fiedlerVector_eigen`
states, at the same eigenvalue `λ₂ = 0`. -/
theorem twoEdge_ones_eigen_QA :
    (laplacian twoEdgeAdj).mulVec (onesVec : Fin 4 → ℝ)
      = lambda2 twoEdgeAdj twoEdgeAdj_symmetric (by norm_num) • onesVec := by
  rw [twoEdge_lambda2_eq_zero_QA, zero_smul]
  exact laplacian_ones_in_kernel twoEdgeAdj

theorem twoEdge_ones_ne_zero_QA : (onesVec : Fin 4 → ℝ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [onesVec] at h0

/-- The positive set of the ones vector is everything — the degenerate
sign pattern. -/
theorem twoEdge_ones_filter_eq_univ_QA :
    (Finset.univ.filter fun i => 0 ≤ (onesVec : Fin 4 → ℝ) i) = Finset.univ := by
  ext i
  simp [onesVec]

/-- **Load-bearing summary:** on this fixture the connectivity
hypothesis fails, and a nonzero eigenvector at `λ₂` exists whose sign
filter is all of `univ` — an unguarded analogue of
`fiedlerPartition_ne_univ` would be false for this eigenvector. -/
theorem twoEdge_load_bearing_QA :
    ¬(supportGraph twoEdgeAdj twoEdgeAdj_symmetric).Connected ∧
    ∃ v : Fin 4 → ℝ, v ≠ 0 ∧
      (laplacian twoEdgeAdj).mulVec v
        = lambda2 twoEdgeAdj twoEdgeAdj_symmetric (by norm_num) • v ∧
      (Finset.univ.filter fun i => 0 ≤ v i) = Finset.univ :=
  ⟨twoEdgeAdj_not_connected, ⟨onesVec, twoEdge_ones_ne_zero_QA,
    twoEdge_ones_eigen_QA, twoEdge_ones_filter_eq_univ_QA⟩⟩

end FiedlerTwoEdge
