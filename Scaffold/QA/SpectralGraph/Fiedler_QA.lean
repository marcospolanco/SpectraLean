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
  - Phase B witnesses (delivered 2026-08-23, all on `K₂`): the
    Rayleigh transfer cross-checked against the independently pinned
    `lambda2 (K₂) = 2` (a defective `/ d` normalization or
    quadratic-form transfer breaks the agreement), the conductance
    minimum attained at the pinned value `cheegerConstant (K₂) = 1`,
    the certified cut *identified* (every nonempty proper cut on
    `Fin 2` is a singleton of conductance `1`) with its bound
    theorem-sourced, and the regularity refutation: at the wrong
    `d = 100` (every other hypothesis holding) the `hd`-dropped form
    would demand a cut of conductance squared `≤ 1/25`, refuted at
    `1 ≤ 1/25`.

  All proofs are real Lean proofs (no `sorry`/`admit`). The Fiedler
  vector itself is noncomputable (spectral theorem plus classical
  choice), so the witnesses pin it through its proved defining
  properties — the eigenvector equation, unit norm, and orthogonality
  — rather than by deciding entries.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Fiedler
import Scaffold.Mathlib.GraphTheory.Sparsification
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

/-!
## Phase B witnesses: the certified conductance cut on `K₂`

`cheeger_cut_existence` (delivered 2026-08-23, pure hard crust) is
exercised end-to-end on the `K₂` fixture: the extracted cut is
*identified* (a singleton, conductance `1`), its bound is sourced from
the theorem, and every quantity is cross-checked against independent
computations. The regularity hypothesis `hd` is shown load-bearing by
refuting the hypothesis-free form at the wrong degree `d = 100`.
-/

section FiedlerPhaseB

/-- `K₂` is `1`-regular. -/
private theorem k2Adj_deg (i : Fin 2) : deg k2Adj i = 1 := by
  fin_cases i <;> simp [deg, k2Adj, Fin.sum_univ_two]

/-- Total volume of `K₂`: two vertices of degree `1`. -/
private theorem k2Adj_vol_univ :
    vol k2Adj (Finset.univ : Finset (Fin 2)) = 2 := by
  simp [vol, Fin.sum_univ_two, k2Adj_deg]

/-- Every nonempty proper subset of `Fin 2` is a singleton — the
identification the cut witnesses consume. -/
private theorem k2Adj_cuts_singleton {S : Finset (Fin 2)}
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) : ∃ i : Fin 2, S = {i} := by
  have hcard : S.card = 1 := by
    have h1 : S.card + Sᶜ.card = 2 := by
      rw [Finset.card_add_card_compl]; simp
    have h2 : 1 ≤ Sᶜ.card := Finset.card_pos.2 hSc
    have h3 : 1 ≤ S.card := Finset.card_pos.2 hS
    omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.1 hcard
  exact ⟨i, hi⟩

/-- The complement-row sum of a singleton: the full row has degree `1`
and the in-set part is the zero diagonal entry. -/
private theorem k2Adj_compl_row_sum (i : Fin 2) :
    ∑ j ∈ ({i} : Finset (Fin 2))ᶜ, k2Adj i j = 1 := by
  have hsplit := Finset.sum_add_sum_compl ({i} : Finset (Fin 2))
    (fun j => k2Adj i j)
  have hin : ∑ j ∈ ({i} : Finset (Fin 2)), k2Adj i j = 0 := by
    rw [Finset.sum_singleton]; simp [k2Adj]
  have hrow : ∑ j : Fin 2, k2Adj i j = 1 := k2Adj_deg i
  linarith

/-- The boundary of a singleton cut is the single crossing edge. -/
private theorem k2Adj_boundary_singleton (i : Fin 2) :
    boundary k2Adj {i} = 1 := by
  simp only [boundary, Finset.sum_singleton]
  exact k2Adj_compl_row_sum i

/-- The volume of any singleton is its degree, `1`. -/
private theorem k2Adj_vol_singleton (i : Fin 2) :
    vol k2Adj {i} = 1 := by
  rw [vol, Finset.sum_singleton, k2Adj_deg]

/-- The complement volume of a singleton is the other degree, `1`. -/
private theorem k2Adj_vol_singleton_compl (i : Fin 2) :
    vol k2Adj ({i} : Finset (Fin 2))ᶜ = 1 := by
  have h := vol_compl k2Adj ({i} : Finset (Fin 2))
  rw [k2Adj_vol_singleton i, k2Adj_vol_univ] at h
  linarith

/-- The conductance of either singleton cut is `1` — both sides
computed from the definitions. -/
theorem k2Adj_conductance_singleton_QA (i : Fin 2) :
    conductance k2Adj {i} = 1 := by
  rw [conductance, k2Adj_boundary_singleton i, k2Adj_vol_singleton i,
    k2Adj_vol_singleton_compl i]
  norm_num

/-- The `K₂` support graph is connected — the connectivity hypothesis
of the certified-cut theorem holds on the fixture. -/
theorem k2Adj_supportGraph_connected_QA :
    (supportGraph k2Adj k2Adj_symmetric).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (by
      rw [supportGraph_adj]
      exact ⟨by decide, by simp [k2Adj]⟩) SimpleGraph.Walk.nil⟩

/-- **The Cheeger constant of `K₂` is `1`**, pinned both directions:
`≤` by the exhibited singleton cut, `≥` because every nonempty proper
cut on `Fin 2` is a singleton of conductance `1`. -/
theorem k2_cheegerConstant_eq_one_QA : cheegerConstant k2Adj = 1 := by
  have hsetne : {c : ℝ | ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance k2Adj S = c}.Nonempty :=
    ⟨1, {0}, Finset.singleton_nonempty 0, ⟨1, by decide⟩,
      k2Adj_conductance_singleton_QA 0⟩
  have hbdd : BddBelow
      {c : ℝ | ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
        conductance k2Adj S = c} :=
    ⟨0, fun c hc => by
      obtain ⟨S, hS, hSc, rfl⟩ := hc
      exact conductance_nonneg k2Adj k2Adj_nonneg S⟩
  rw [cheegerConstant]
  refine le_antisymm ?_ ?_
  · exact csInf_le hbdd
      ⟨{0}, Finset.singleton_nonempty 0, ⟨1, by decide⟩,
        k2Adj_conductance_singleton_QA 0⟩
  · refine le_csInf hsetne ?_
    rintro c ⟨S, hS, hSc, rfl⟩
    obtain ⟨i, hi⟩ := k2Adj_cuts_singleton hS hSc
    rw [hi, k2Adj_conductance_singleton_QA i]

/-- **Attainment instantiated:** the conductance minimum is achieved
by an actual nonempty proper cut, and on `K₂` its value is the pinned
`cheegerConstant = 1`. -/
theorem k2_attainment_QA :
    ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance k2Adj S = 1 := by
  obtain ⟨S, hS, hSc, h⟩ :=
    cheegerConstant_attained k2Adj k2Adj_nonneg (le_refl 2)
  exact ⟨S, hS, hSc, by rw [h, k2_cheegerConstant_eq_one_QA]⟩

/-- **The Rayleigh transfer cross-checked.** The Fiedler vector's
Rayleigh quotient at `L_sym` evaluates to exactly the independently
pinned `lambda2 (K₂) = 2` (here at `d = 1`, where `2 / 1 = 2`): the
unit norm, the quadratic-form transfer `quadForm (L_sym) = d⁻¹ •
quadForm (L)`, and the energy identity all had to be exactly right —
a defective normalization surfaces as a mismatch against this pin. -/
theorem k2_fiedler_rayleigh_QA :
    rayleigh (regularNormalizedLaplacian k2Adj 1)
        (fiedlerVector k2Adj k2Adj_symmetric (le_refl 2)) = 2 := by
  rw [fiedlerVector_rayleigh_regularNormalizedLaplacian k2Adj
    k2Adj_symmetric (le_refl 2) 1 k2Adj_deg (by norm_num),
    k2_lambda2_eq_two]
  norm_num

/-- **The certified cut, identified and theorem-sourced.** On `K₂` the
cut whose existence `cheeger_cut_existence` guarantees is a singleton
(every nonempty proper cut on `Fin 2` is), its conductance is the
computed `1`, and its bound is exactly the theorem's conclusion. -/
theorem k2_cut_certified_QA :
    ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance k2Adj S = 1 ∧
      conductance k2Adj S ^ 2
        ≤ 2 * lambda2 k2Adj k2Adj_symmetric (le_refl 2) / 1 := by
  obtain ⟨S, hS, hSc, hle⟩ := cheeger_cut_existence k2Adj k2Adj_symmetric
    k2Adj_nonneg 1 k2Adj_deg (by norm_num) (le_refl 2)
    k2Adj_supportGraph_connected_QA
  obtain ⟨i, hi⟩ := k2Adj_cuts_singleton hS hSc
  subst hi
  exact ⟨{i}, Finset.singleton_nonempty i, hSc,
    k2Adj_conductance_singleton_QA i, hle⟩

/-- **The certificate in numbers:** the identified cut has conductance
`1` and the certified bound reads `1 ≤ 4` against the pinned
`lambda2 (K₂) = 2` — both sides independently computed. -/
theorem k2_cut_certified_numeric_QA :
    ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance k2Adj S = 1 ∧ (1 : ℝ) ≤ 2 * 2 / 1 := by
  obtain ⟨S, hS, hSc, h1, h2⟩ := k2_cut_certified_QA
  rw [k2_lambda2_eq_two] at h2
  have h3 : (1 : ℝ) = conductance k2Adj S ^ 2 := by
    rw [h1]; norm_num
  refine ⟨S, hS, hSc, h1, ?_⟩
  calc (1 : ℝ) = conductance k2Adj S ^ 2 := h3
    _ ≤ 2 * 2 / 1 := h2

/-- **The regularity hypothesis is load-bearing.** With `hd` dropped,
the bound would have to hold at *every* positive degree; at `d = 100`
on `K₂` (which is `1`-regular, so `hd` fails exactly there while
every other hypothesis holds) the conclusion demands a nonempty
proper cut of conductance squared `≤ 2 · 2 / 100 = 1/25`. Every
nonempty proper cut on `Fin 2` is a singleton of conductance `1`, so
the conclusion reads `1 ≤ 1/25` — false. -/
theorem cut_existence_regular_dropped_refuted_QA :
    ¬ (∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
        conductance k2Adj S ^ 2
          ≤ 2 * lambda2 k2Adj k2Adj_symmetric (le_refl 2) / 100) := by
  rintro ⟨S, hS, hSc, hle⟩
  obtain ⟨i, hi⟩ := k2Adj_cuts_singleton hS hSc
  subst hi
  rw [k2Adj_conductance_singleton_QA i, k2_lambda2_eq_two] at hle
  norm_num at hle

end FiedlerPhaseB

/-!
## Phase C witnesses: the swept Fiedler cut on `K₂`

`fiedler_sweep_cut` (delivered 2026-08-24,
`proposals/sweep-cut-extraction.md`) exercised on the `K₂` fixture: the
returned cut identified through the Fiedler value pins (every nonempty
proper cut on `Fin 2` is a singleton; the *sweep family* itself is
characterized to be exactly the two singletons through the antisymmetry
pins), its conductance computed to `1` raw, the theorem bound cross-
checked against the pinned `lambda2 (K₂) = 2`, and the optimality tie
`conductance S = cheegerConstant (K₂) = 1` — the sweep is exact on
`K₂`.
-/

section FiedlerPhaseC

/-- **The swept cut, identified and theorem-sourced.** On `K₂` the cut
whose existence `fiedler_sweep_cut` guarantees is a singleton (every
nonempty proper cut on `Fin 2` is), its conductance is the computed
`1`, and its bound is exactly the theorem's conclusion
(`1 ≤ 2 · 2 / 1 = 4`). -/
theorem k2_sweep_cut_QA :
    ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      ((∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ fiedlerVector k2Adj k2Adj_symmetric
            (le_refl 2) i) ∨
        (∃ t : ℝ, ∀ i, i ∈ S ↔ fiedlerVector k2Adj k2Adj_symmetric
            (le_refl 2) i ≤ t)) ∧
      conductance k2Adj S = 1 ∧
      conductance k2Adj S ^ 2
        ≤ 2 * lambda2 k2Adj k2Adj_symmetric (le_refl 2) / 1 := by
  obtain ⟨S, hS, hSc, hfam, hle⟩ :=
    fiedler_sweep_cut k2Adj k2Adj_symmetric k2Adj_nonneg 1 k2Adj_deg
      (by norm_num) (le_refl 2) k2Adj_supportGraph_connected_QA
  obtain ⟨i, hi⟩ := k2Adj_cuts_singleton hS hSc
  subst hi
  refine ⟨{i}, Finset.singleton_nonempty i, hSc, hfam,
    k2Adj_conductance_singleton_QA i, hle⟩

/-- **The sweep family of the `K₂` Fiedler vector:** any nonempty
proper closed superlevel or sublevel set of the Fiedler vector is one
of the two singletons — the sign of the Fiedler entry decides which.
This pins the family constraint itself (on an eigenvector with equal
entries the family would be *empty*, and no theorem of this shape
could hold), through the antisymmetry and nonvanishing pins. -/
theorem k2_sweep_family_QA (S : Finset (Fin 2)) (hS : S.Nonempty)
    (hSc : Sᶜ.Nonempty)
    (hfam : (∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ fiedlerVector k2Adj k2Adj_symmetric
            (le_refl 2) i) ∨
      (∃ t : ℝ, ∀ i, i ∈ S ↔ fiedlerVector k2Adj k2Adj_symmetric
            (le_refl 2) i ≤ t)) :
    S = ({0} : Finset (Fin 2)) ∨ S = ({1} : Finset (Fin 2)) := by
  classical
  have hanti : fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 1
      = -fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0 :=
    k2_fiedler_antisymm_QA
  have hv0 : fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0 ≠ 0 :=
    k2_fiedler_zero_ne_QA
  rcases hfam with ⟨t, ht⟩ | ⟨t, ht⟩
  · by_cases hpos : fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0 < 0
    · -- values (-b, b), b > 0
      have h1pos : 0 < fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 1 := by
        rw [hanti]
        linarith
      by_cases hA : t ≤ fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0
      · exfalso
        have h0 : (0 : Fin 2) ∈ S := (ht 0).2 hA
        have h1 : (1 : Fin 2) ∈ S := (ht 1).2 (by
          rw [hanti]; linarith)
        have hEq : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
          intro i
          fin_cases i
          · exact h0
          · exact h1)
        rw [hEq] at hSc
        simp at hSc
      · by_cases hB : t ≤ fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 1
        · refine Or.inr ?_
          have h1 : (1 : Fin 2) ∈ S := (ht 1).2 hB
          have h0 : (0 : Fin 2) ∉ S := fun hc => hA ((ht 0).1 hc)
          apply Finset.ext
          intro i
          fin_cases i
          · simp [h0]
          · simp [h1]
        · exfalso
          have h0 : (0 : Fin 2) ∉ S := fun hc => hA ((ht 0).1 hc)
          have h1 : (1 : Fin 2) ∉ S := fun hc => hB ((ht 1).1 hc)
          have hEq : S = ∅ := Finset.eq_empty_iff_forall_not_mem.2 (by
            intro i hi
            fin_cases i
            · exact h0 hi
            · exact h1 hi)
          rw [hEq] at hS
          simp at hS
    · -- values (a, -a), a > 0
      have hpos' : 0 < fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0 := by
        by_contra hc
        push_neg at hc
        exact hv0 (le_antisymm hc (le_of_not_gt hpos))
      have h1neg : fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 1 < 0 := by
        rw [hanti]
        linarith
      by_cases hA : t ≤ fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 1
      · exfalso
        have h0 : (0 : Fin 2) ∈ S := (ht 0).2 (by
          rw [show fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0
              = -fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 1 from
            by rw [hanti]; ring]
          linarith)
        have h1 : (1 : Fin 2) ∈ S := (ht 1).2 hA
        have hEq : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
          intro i
          fin_cases i
          · exact h0
          · exact h1)
        rw [hEq] at hSc
        simp at hSc
      · by_cases hB : t ≤ fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0
        · refine Or.inl ?_
          have h0 : (0 : Fin 2) ∈ S := (ht 0).2 hB
          have h1 : (1 : Fin 2) ∉ S := fun hc => hA ((ht 1).1 hc)
          apply Finset.ext
          intro i
          fin_cases i
          · simp [h0]
          · simp [h1]
        · exfalso
          have h0 : (0 : Fin 2) ∉ S := fun hc => hB ((ht 0).1 hc)
          have h1 : (1 : Fin 2) ∉ S := fun hc => hA ((ht 1).1 hc)
          have hEq : S = ∅ := Finset.eq_empty_iff_forall_not_mem.2 (by
            intro i hi
            fin_cases i
            · exact h0 hi
            · exact h1 hi)
          rw [hEq] at hS
          simp at hS
  · by_cases hpos : fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0 < 0
    · -- values (-b, b), b > 0
      have h1pos : 0 < fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 1 := by
        rw [hanti]
        linarith
      by_cases hA : fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 1 ≤ t
      · exfalso
        have h0 : (0 : Fin 2) ∈ S := (ht 0).2 (by
          rw [show fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0
              = -fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 1 from
            by rw [hanti]; ring]
          linarith)
        have h1 : (1 : Fin 2) ∈ S := (ht 1).2 hA
        have hEq : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
          intro i
          fin_cases i
          · exact h0
          · exact h1)
        rw [hEq] at hSc
        simp at hSc
      · by_cases hB : fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0 ≤ t
        · refine Or.inl ?_
          have h0 : (0 : Fin 2) ∈ S := (ht 0).2 hB
          have h1 : (1 : Fin 2) ∉ S := fun hc => hA ((ht 1).1 hc)
          apply Finset.ext
          intro i
          fin_cases i
          · simp [h0]
          · simp [h1]
        · exfalso
          have h0 : (0 : Fin 2) ∉ S := fun hc => hB ((ht 0).1 hc)
          have h1 : (1 : Fin 2) ∉ S := fun hc => hA ((ht 1).1 hc)
          have hEq : S = ∅ := Finset.eq_empty_iff_forall_not_mem.2 (by
            intro i hi
            fin_cases i
            · exact h0 hi
            · exact h1 hi)
          rw [hEq] at hS
          simp at hS
    · -- values (a, -a), a > 0
      have hpos' : 0 < fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0 := by
        by_contra hc
        push_neg at hc
        exact hv0 (le_antisymm hc (le_of_not_gt hpos))
      by_cases hA : fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 0 ≤ t
      · exfalso
        have h0 : (0 : Fin 2) ∈ S := (ht 0).2 hA
        have h1 : (1 : Fin 2) ∈ S := (ht 1).2 (by
          rw [hanti]; linarith)
        have hEq : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
          intro i
          fin_cases i
          · exact h0
          · exact h1)
        rw [hEq] at hSc
        simp at hSc
      · by_cases hB : fiedlerVector k2Adj k2Adj_symmetric (le_refl 2) 1 ≤ t
        · refine Or.inr ?_
          have h1 : (1 : Fin 2) ∈ S := (ht 1).2 hB
          have h0 : (0 : Fin 2) ∉ S := fun hc => hA ((ht 0).1 hc)
          apply Finset.ext
          intro i
          fin_cases i
          · simp [h0]
          · simp [h1]
        · exfalso
          have h0 : (0 : Fin 2) ∉ S := fun hc => hA ((ht 0).1 hc)
          have h1 : (1 : Fin 2) ∉ S := fun hc => hB ((ht 1).1 hc)
          have hEq : S = ∅ := Finset.eq_empty_iff_forall_not_mem.2 (by
            intro i hi
            fin_cases i
            · exact h0 hi
            · exact h1 hi)
          rw [hEq] at hS
          simp at hS

/-- **The sweep is exact on `K₂`:** the identified cut's conductance
equals the pinned Cheeger constant — the swept cut is an optimal cut
here, while the theorem only certifies the `2 λ₂ / d = 4` bound. -/
theorem k2_sweep_optimal_QA :
    ∃ S : Finset (Fin 2), conductance k2Adj S = 1
      ∧ conductance k2Adj S = cheegerConstant k2Adj := by
  obtain ⟨S, -, -, -, h1, -⟩ := k2_sweep_cut_QA
  exact ⟨S, h1, by rw [h1, k2_cheegerConstant_eq_one_QA]⟩

end FiedlerPhaseC

/-!
## Fiedler-subspace stability (`fiedlerSubspace_stability`)

Step 1 QA of `proposals/fiedler-subspace-stability-davis-kahan.md`:
the Davis–Kahan Fiedler-subspace wrapper, exercised at exact graph
spectra.

- **Obligation 1 (the cross-check):** the exact combinatorial P₃
  spectrum pins `λ₂ = 1` (the `≥` side new, by the sum-of-squares
  identity `E(x) = ‖x‖² + 3 (x₀ + x₂)²` on the zero-sum constraint)
  and `λ₃ = 3` (by `laplacian_evals_zero` + the λ₂ pin + the trace
  identity `0 + 1 + λ₃ = 4`), then the wrapper's zero-perturbation
  instance at `δ = 2` cross-checked against the raw matrix identity
  `P₃ + 0 = P₃` — two routes meeting at distance exactly `0`, with the
  separation discharge as the load-bearing step (a wrong index or
  wrong operator in `hsep` fails exactly there).
- **Obligation 2 (the boundary witness):** the complete graph `K₃`,
  where the Fiedler eigenvalue is not simple (`λ₂ = λ₃ = 3`, both sides
  exact: the `≤` by the Rayleigh engine at `![1, -1, 0]`, the `≥` by
  the identity `E(x) = 3‖x‖² − (x₀+x₁+x₂)²` on the constraint), pins
  the wrapper's hypothesis set as *provably empty* for every positive
  `δ` — the eigenvalue tie at the threshold makes the statement
  vacuous rather than silently bounded: tie-awareness inherited from
  Davis–Kahan's own case split.

All proofs are real Lean proofs (no `sorry`/`admit`); everything here
is unconditional (the wrapper and all engine lemmas it consumes are
proved).

Step 2 (`FiedlerLineStability`, 2026-08-28): the residual-projector
statement on the same fixtures — the P₃ → K₃ edge-addition instance
with the bound exactly `≤ 1` (the perturbed side sits on Davis–Kahan's
own tie branch), the perturbation norm pinned exactly `2` from both
sides, the common-kernel identification at the genuine two-spectrum
pair P₃/K₃, the fix-iff pins at vectors, and the disconnected fence
proving the identification's connectivity hypothesis load-bearing.
All unconditional.

Scoreboard: ../QA_SCOREBOARD.md
-/

section FiedlerSubspaceStability

open scoped Matrix.L2OpNorm

open Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation

/-- Private helper: a nonzero real vector has strictly positive squared
norm (as a dot product). -/
private theorem dotProduct_self_pos {n : Type} [Fintype n]
    (hn : 0 < Fintype.card n) {x : n → ℝ} (hx : x ≠ 0) :
    0 < Matrix.dotProduct x x := by
  obtain ⟨v⟩ : Nonempty n := Fintype.card_pos_iff.1 hn
  have hle : (0 : ℝ) ≤ Matrix.dotProduct x x := by
    simp only [Matrix.dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    apply hx
    funext i
    have hsum0 : ∑ k, x k * x k = 0 := by
      rw [← show Matrix.dotProduct x x = ∑ k, x k * x k from rfl]
      exact h.symm
    have hmem : ∀ j : n, x j * x j = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun k (_ : k ∈ Finset.univ) => mul_self_nonneg _)).1 hsum0 j
        (Finset.mem_univ j)
    exact mul_self_eq_zero.1 (hmem i)

/-- The Dirichlet form of `P₃` at any vector: the two edge terms. -/
theorem path3_quadForm (x : Fin 3 → ℝ) :
    quadForm (laplacian path3Adj) x
      = (x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 := by
  rw [laplacian_quadForm path3Adj path3Adj_symmetric x]
  simp [path3Adj, Fin.sum_univ_three]
  ring

/-- **λ₂ of the combinatorial three-path is exactly `1` — the `≥`
side**, by the sum-of-squares identity `E(x) = ‖x‖² + 3 (x₀ + x₂)²` on
the zero-sum constraint (the constraint is what the variational engine
supplies; the identity is pure algebra, `linear_combination` on
`∑ x = 0`). Load-bearing: a wrong Dirichlet form or a wrong constraint
direction breaks exactly this pin. -/
theorem path3_lambda2_ge_one_QA :
    1 ≤ lambda2 path3Adj path3Adj_symmetric (by norm_num) := by
  rw [lambda2_variational path3Adj path3Adj_symmetric path3Adj_nonneg
    (by norm_num)]
  have hwne : (![1, 0, -1] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have h1 : (![1, 0, -1] : Fin 3 → ℝ) 0 = 0 := congrFun h 0
    simp at h1
  have hworth : Matrix.dotProduct (![1, 0, -1] : Fin 3 → ℝ) onesVec = 0 := by
    simp [Matrix.dotProduct, onesVec, Fin.sum_univ_three]
  have hqf : quadForm (laplacian path3Adj) (![1, 0, -1] : Fin 3 → ℝ) = 2 := by
    rw [path3_quadForm]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.head_cons]
  have hdot : Matrix.dotProduct (![1, 0, -1] : Fin 3 → ℝ)
      (![1, 0, -1] : Fin 3 → ℝ) = 2 := by
    norm_num [Matrix.dotProduct, Fin.sum_univ_three]
  have hray : rayleigh (laplacian path3Adj) (![1, 0, -1] : Fin 3 → ℝ) = 1 := by
    rw [rayleigh, if_neg hwne, hqf, hdot]
    norm_num
  refine le_csInf ⟨1, (![1, 0, -1] : Fin 3 → ℝ), hwne, hworth, hray⟩ ?_
  rintro r ⟨y, hy0, horth, rfl⟩
  have hsum3 : y 0 + y 1 + y 2 = 0 := by
    simpa [Matrix.dotProduct, onesVec, Fin.sum_univ_three] using horth
  have hident : (y 0 - y 1) ^ 2 + (y 1 - y 2) ^ 2
      = (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + 3 * (y 0 + y 2) ^ 2 := by
    linear_combination hsum3 * (-3 * y 0 + y 1 - 3 * y 2)
  have hnn : 0 < Matrix.dotProduct y y :=
    dotProduct_self_pos (by norm_num) hy0
  have hdd : Matrix.dotProduct y y
      = (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 := by
    rw [show Matrix.dotProduct y y = ∑ k, y k * y k from rfl,
      Fin.sum_univ_three]
    ring
  rw [rayleigh, if_neg hy0, path3_quadForm, hident]
  refine (one_le_div hnn).2 ?_
  rw [hdd]
  nlinarith [sq_nonneg (y 0 + y 2)]

/-- λ₂ of the combinatorial three-path, exact: the two one-sided pins
(the `≤` side is `Variational_QA.path3_lambda2_le_one_QA`). -/
theorem path3_lambda2_eq_one_QA :
    lambda2 path3Adj path3Adj_symmetric (by norm_num) = 1 :=
  le_antisymm path3_lambda2_le_one_QA path3_lambda2_ge_one_QA

theorem path3_evals_zero_QA :
    evals (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨0, by norm_num⟩
      = 0 :=
  laplacian_evals_zero path3Adj path3Adj_symmetric path3Adj_nonneg
    (by norm_num)

theorem path3_evals_one_eq_one_QA :
    evals (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨1, by norm_num⟩
      = 1 :=
  (lambda2_eq_secondEval path3Adj path3Adj_symmetric (by norm_num)).symm
    |>.trans path3_lambda2_eq_one_QA

/-- Trace of the three-path Laplacian: degrees `1 + 2 + 1`. -/
theorem path3_trace : (laplacian path3Adj).trace = 4 := by
  have hdeg : ∀ i : Fin 3,
      deg path3Adj i = if (i : ℕ) = 1 then 2 else 1 := by
    intro i
    fin_cases i <;> rw [deg, Fin.sum_univ_three] <;> norm_num [path3Adj]
  have hLdiag : ∀ i : Fin 3,
      (laplacian path3Adj) i i = if (i : ℕ) = 1 then 2 else 1 := by
    intro i
    rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal,
      show path3Adj i i = 0 from by
        have : ∀ i : Fin 3, path3Adj i i = 0 := by
          intro i
          fin_cases i <;> simp [path3Adj]
        exact this i, sub_zero]
    exact hdeg i
  rw [show (laplacian path3Adj).trace
      = ∑ i : Fin 3, (laplacian path3Adj) i i from rfl,
    Finset.sum_congr rfl fun i _ => hLdiag i]
  simp only [Fin.sum_univ_three]
  norm_num

/-- **λ₃ of the three-path Laplacian is exactly `3`**, by the trace
identity `0 + 1 + λ₃ = 4` at the two exact pins. The separation
hypothesis of the Davis–Kahan wrapper consumes precisely this value. -/
theorem path3_evals_two_eq_three_QA :
    evals (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨2, by norm_num⟩
      = 3 := by
  have hsum := evals_sum_eq_trace
    (laplacian_symmetric path3Adj path3Adj_symmetric)
  have h1 : ∑ i : Fin 3,
      evals (laplacian_symmetric path3Adj path3Adj_symmetric) i = 4 := by
    rw [show (laplacian path3Adj).trace = 4 from path3_trace] at hsum
    exact hsum
  have hsum3 : evals (laplacian_symmetric path3Adj path3Adj_symmetric)
        ⟨0, by norm_num⟩
      + evals (laplacian_symmetric path3Adj path3Adj_symmetric)
        ⟨1, by norm_num⟩
      + evals (laplacian_symmetric path3Adj path3Adj_symmetric)
        ⟨2, by norm_num⟩ = 4 := by
    simp only [Fin.sum_univ_three] at h1
    exact h1
  rw [path3_evals_zero_QA, path3_evals_one_eq_one_QA] at hsum3
  linarith

/-- **Obligation 1, route 2 (raw):** at `E = 0` the projector distance
is exactly `0` by the matrix identity `P₃ + 0 = P₃` alone — no
Davis–Kahan, no wrapper. -/
theorem fiedlerSubspace_zero_raw_QA :
    ‖initialProjector (laplacian (path3Adj + 0))
        (laplacian_symmetric (path3Adj + 0)
          (path3Adj_symmetric.add (by simp))) ⟨1, by norm_num⟩
      - initialProjector (laplacian path3Adj)
        (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨1, by norm_num⟩‖
      = 0 := by
  have hident : initialProjector (laplacian (path3Adj + 0))
      (laplacian_symmetric (path3Adj + 0)
        (path3Adj_symmetric.add (by simp))) ⟨1, by norm_num⟩
      = initialProjector (laplacian path3Adj)
        (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨1, by norm_num⟩ :=
    initialProjector_congr (by rw [add_zero])
      (laplacian_symmetric (path3Adj + 0)
        (path3Adj_symmetric.add (by simp)))
      (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨1, by norm_num⟩
  rw [hident, sub_self, norm_zero]

/-- **Obligation 1, route 1 (the wrapper):** the instance itself, with
the separation hypothesis discharged by the exact spectrum pins — the
load-bearing step (a wrong index convention or wrong operator in the
wrapper's `hsep` fails exactly here: the pins are `0, 1, 3`, and only
`λ₃ − λ₂ = 3 − 1` admits `δ = 2`). -/
theorem fiedlerSubspace_zero_bound_QA :
    ‖initialProjector (laplacian (path3Adj + 0))
        (laplacian_symmetric (path3Adj + 0)
          (path3Adj_symmetric.add (by simp))) ⟨1, by norm_num⟩
      - initialProjector (laplacian path3Adj)
        (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨1, by norm_num⟩‖
      ≤ ‖laplacian (0 : WAdj (V := Fin 3))‖ / 2 := by
  refine fiedlerSubspace_stability path3Adj 0 path3Adj_symmetric
    (by simp) (by norm_num) 2 (by norm_num) ?_
  rw [evals_congr (laplacian_symmetric (path3Adj + 0)
      (path3Adj_symmetric.add (by simp)))
    (laplacian_symmetric path3Adj path3Adj_symmetric)
    (by rw [add_zero]) ⟨2, by norm_num⟩,
    path3_evals_two_eq_three_QA, path3_evals_one_eq_one_QA]
  norm_num

/-- **The two routes meet:** the wrapper's bound `≤ 0` (route 1) and
the raw identity `= 0` (route 2) sandwich the distance at exactly `0`. -/
theorem fiedlerSubspace_zero_join_QA :
    ‖initialProjector (laplacian (path3Adj + 0))
        (laplacian_symmetric (path3Adj + 0)
          (path3Adj_symmetric.add (by simp))) ⟨1, by norm_num⟩
      - initialProjector (laplacian path3Adj)
        (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨1, by norm_num⟩‖
      = 0 := by
  refine le_antisymm ?_ (norm_nonneg _)
  have h := fiedlerSubspace_zero_bound_QA
  rwa [show laplacian (0 : WAdj (V := Fin 3)) = 0 from
    laplacian_zero (V := Fin 3), norm_zero, zero_div] at h

/-- Adjacency of the complete graph on three vertices. -/
def k3Adj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then 0 else 1

theorem k3Adj_symmetric : k3Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [k3Adj]

theorem k3Adj_nonneg : ∀ i j, 0 ≤ k3Adj i j := by
  intro i j
  simp only [k3Adj, Matrix.of_apply]
  split <;> norm_num

theorem k3_quadForm (x : Fin 3 → ℝ) :
    quadForm (laplacian k3Adj) x
      = (x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 + (x 0 - x 2) ^ 2 := by
  rw [laplacian_quadForm k3Adj k3Adj_symmetric x]
  simp [k3Adj, Fin.sum_univ_three]
  ring

/-- **λ₂ of `K₃` is exactly `3`** — the Fiedler eigenvalue is NOT
simple: the bottom cluster is the whole nonzero spectrum, the substance
of the vacuity witness below. The `≤` side is the Rayleigh engine at
the explicit mode `![1, -1, 0]`; the `≥` side is the identity
`E(x) = 3‖x‖² − (x₀+x₁+x₂)²` on the zero-sum constraint (equality
throughout — the whole orthogonal complement of `onesVec` is an
eigenspace). -/
theorem k3_lambda2_eq_three_QA :
    lambda2 k3Adj k3Adj_symmetric (by norm_num) = 3 := by
  refine le_antisymm ?_ ?_
  · rw [lambda2_variational k3Adj k3Adj_symmetric k3Adj_nonneg (by norm_num)]
    have hvne : (![1, -1, 0] : Fin 3 → ℝ) ≠ 0 := by
      intro h
      have h1 : (![1, -1, 0] : Fin 3 → ℝ) 0 = 0 := congrFun h 0
      simp at h1
    have hworth : Matrix.dotProduct (![1, -1, 0] : Fin 3 → ℝ) onesVec = 0 := by
      simp [Matrix.dotProduct, onesVec, Fin.sum_univ_three]
    have hray : rayleigh (laplacian k3Adj) (![1, -1, 0] : Fin 3 → ℝ) = 3 := by
      rw [rayleigh, if_neg hvne, k3_quadForm]
      norm_num [Matrix.dotProduct, Fin.sum_univ_three]
    exact csInf_le ⟨0, by
      rintro r ⟨y, hy0, -, rfl⟩
      rw [rayleigh, if_neg hy0]
      exact div_nonneg (laplacian_psd k3Adj k3Adj_symmetric k3Adj_nonneg y)
        (by
          simp only [Matrix.dotProduct]
          exact Finset.sum_nonneg fun j _ => mul_self_nonneg _)⟩
      ⟨(![1, -1, 0] : Fin 3 → ℝ), hvne, hworth, hray⟩
  · rw [lambda2_variational k3Adj k3Adj_symmetric k3Adj_nonneg (by norm_num)]
    have hvne : (![1, -1, 0] : Fin 3 → ℝ) ≠ 0 := by
      intro h
      have h1 : (![1, -1, 0] : Fin 3 → ℝ) 0 = 0 := congrFun h 0
      simp at h1
    have hworth : Matrix.dotProduct (![1, -1, 0] : Fin 3 → ℝ) onesVec = 0 := by
      simp [Matrix.dotProduct, onesVec, Fin.sum_univ_three]
    have hray : rayleigh (laplacian k3Adj) (![1, -1, 0] : Fin 3 → ℝ) = 3 := by
      rw [rayleigh, if_neg hvne, k3_quadForm]
      norm_num [Matrix.dotProduct, Fin.sum_univ_three]
    refine le_csInf ⟨3, (![1, -1, 0] : Fin 3 → ℝ), hvne, hworth, hray⟩ ?_
    rintro r ⟨y, hy0, horth, rfl⟩
    have hsum3 : y 0 + y 1 + y 2 = 0 := by
      simpa [Matrix.dotProduct, onesVec, Fin.sum_univ_three] using horth
    have hident : (y 0 - y 1) ^ 2 + (y 1 - y 2) ^ 2 + (y 0 - y 2) ^ 2
        = 3 * ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2)
          - (y 0 + y 1 + y 2) ^ 2 := by
      ring
    have hnn : 0 < Matrix.dotProduct y y :=
      dotProduct_self_pos (by norm_num) hy0
    have hdd : Matrix.dotProduct y y
        = (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 := by
      rw [show Matrix.dotProduct y y = ∑ k, y k * y k from rfl,
        Fin.sum_univ_three]
      ring
    have hquad : quadForm (laplacian k3Adj) y
        = 3 * Matrix.dotProduct y y := by
      rw [k3_quadForm, hident, hsum3, hdd]
      ring
    rw [rayleigh, if_neg hy0, hquad]
    exact (le_div_iff₀ hnn).2 (le_refl _)

theorem k3_evals_zero_QA :
    evals (laplacian_symmetric k3Adj k3Adj_symmetric) ⟨0, by norm_num⟩
      = 0 :=
  laplacian_evals_zero k3Adj k3Adj_symmetric k3Adj_nonneg (by norm_num)

theorem k3_evals_one_eq_three_QA :
    evals (laplacian_symmetric k3Adj k3Adj_symmetric) ⟨1, by norm_num⟩
      = 3 :=
  (lambda2_eq_secondEval k3Adj k3Adj_symmetric (by norm_num)).symm
    |>.trans k3_lambda2_eq_three_QA

theorem k3_trace : (laplacian k3Adj).trace = 6 := by
  have hdeg : ∀ i : Fin 3, deg k3Adj i = 2 := by
    intro i
    fin_cases i <;> rw [deg, Fin.sum_univ_three] <;> norm_num [k3Adj]
  have hLdiag : ∀ i : Fin 3, (laplacian k3Adj) i i = 2 := by
    intro i
    rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal,
      show k3Adj i i = 0 from by
        have : ∀ i : Fin 3, k3Adj i i = 0 := by
          intro i
          simp [k3Adj]
        exact this i, sub_zero]
    exact hdeg i
  rw [show (laplacian k3Adj).trace
      = ∑ i : Fin 3, (laplacian k3Adj) i i from rfl,
    Finset.sum_congr rfl fun i _ => hLdiag i]
  simp only [Fin.sum_univ_three]
  norm_num

/-- λ₃ of `K₃` equals λ₂: the trace identity `0 + 3 + λ₃ = 6` pins the
eigenvalue tie at the exact threshold the wrapper's separation
hypothesis lives on. -/
theorem k3_evals_two_eq_three_QA :
    evals (laplacian_symmetric k3Adj k3Adj_symmetric) ⟨2, by norm_num⟩
      = 3 := by
  have hsum := evals_sum_eq_trace
    (laplacian_symmetric k3Adj k3Adj_symmetric)
  have h1 : ∑ i : Fin 3,
      evals (laplacian_symmetric k3Adj k3Adj_symmetric) i = 6 := by
    rw [show (laplacian k3Adj).trace = 6 from k3_trace] at hsum
    exact hsum
  have hsum3 : evals (laplacian_symmetric k3Adj k3Adj_symmetric)
        ⟨0, by norm_num⟩
      + evals (laplacian_symmetric k3Adj k3Adj_symmetric)
        ⟨1, by norm_num⟩
      + evals (laplacian_symmetric k3Adj k3Adj_symmetric)
        ⟨2, by norm_num⟩ = 6 := by
    simp only [Fin.sum_univ_three] at h1
    exact h1
  rw [k3_evals_zero_QA, k3_evals_one_eq_three_QA] at hsum3
  linarith

/-- **Obligation 2, the boundary witness: at the eigenvalue tie the
hypothesis set is provably empty.** At the complete graph `K₃` the
Fiedler eigenvalue is not simple (`λ₂ = λ₃ = 3`), so for every positive
`δ` the wrapper's separation hypothesis fails — the statement is
vacuous at the tie (the honest boundary Davis–Kahan's own proof
case-splits on), not silently useful. -/
theorem fiedlerSubspace_tie_vacuous_QA (δ : ℝ) (hδ : 0 < δ) :
    ¬ (δ ≤ evals (laplacian_symmetric (k3Adj + 0)
          (k3Adj_symmetric.add (by simp))) ⟨2, by norm_num⟩
        - evals (laplacian_symmetric k3Adj k3Adj_symmetric)
          ⟨1, by norm_num⟩) := by
  intro h
  rw [evals_congr (laplacian_symmetric (k3Adj + 0)
      (k3Adj_symmetric.add (by simp)))
    (laplacian_symmetric k3Adj k3Adj_symmetric)
    (by rw [add_zero]) ⟨2, by norm_num⟩,
    k3_evals_two_eq_three_QA, k3_evals_one_eq_three_QA] at h
  linarith

end FiedlerSubspaceStability

/-!
### Step 2: the Fiedler line

The residual-projector statement (`fiedlerLine_stability`) exercised on
fixtures: the P₃ → K₃ edge addition (the perturbed side sits exactly on
Davis–Kahan's tie branch, the derived bound exactly `≤ 1`), the
common-kernel identification at a genuine two-spectrum pair, the fix-iff
pins at concrete vectors, and the disconnected fence proving the
identification's connectivity hypothesis load-bearing.
-/

section FiedlerLineStability

open scoped Matrix.L2OpNorm

/-- The single edge `(0,2)`: the perturbation turning `P₃` into `K₃`. -/
def edge02 : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    if ((i : ℕ) = 0 ∧ (j : ℕ) = 2) ∨ ((i : ℕ) = 2 ∧ (j : ℕ) = 0) then 1 else 0

theorem edge02_isSymm : edge02.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [edge02]

theorem edge02_nonneg : ∀ i j, 0 ≤ edge02 i j := by
  intro i j
  simp only [edge02, Matrix.of_apply]
  split <;> norm_num

theorem edge02_deg (i : Fin 3) :
    deg edge02 i = if (i : ℕ) = 1 then 0 else 1 := by
  fin_cases i <;> rw [deg, Fin.sum_univ_three] <;> norm_num [edge02]

theorem edge02_laplacian_eq_rankOne :
    laplacian edge02 = rankOne (![1, 0, -1] : Fin 3 → ℝ) := by
  ext i j
  rw [laplacian, Matrix.sub_apply]
  by_cases hij : i = j
  · subst hij
    rw [degreeMatrix_diagonal, edge02_deg i, rankOne_apply]
    fin_cases i <;>
      simp [edge02, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_succ, Matrix.head_cons]
  · rw [degreeMatrix_off_diagonal edge02 hij, rankOne_apply]
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | (simp [edge02, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_succ, Matrix.head_cons]; try norm_num)

/-- **The perturbation norm is exactly `2`, pinned from both sides** —
`≤ 2` by the rank-one bound (`l2OpNorm_rankOne_le`, the Sparsification
delivery's algebra), `≥ 2` by the quadForm witness `![1, 0, -1]` through
the norm→form transfer (`abs_quadForm_le_of_l2OpNorm_le`, `4 ≤ 2 · 2`).
A wrong constant anywhere in that chain breaks exactly one side. -/
theorem edge02_laplacian_norm : ‖laplacian edge02‖ = 2 := by
  refine le_antisymm ?_ ?_
  · rw [edge02_laplacian_eq_rankOne]
    have hle := l2OpNorm_rankOne_le (![1, 0, -1] : Fin 3 → ℝ)
    rw [show Matrix.dotProduct (![1, 0, -1] : Fin 3 → ℝ)
        (![1, 0, -1] : Fin 3 → ℝ) = 2 from
      by norm_num [Matrix.dotProduct, Fin.sum_univ_three]] at hle
    exact hle
  · have hq : quadForm (laplacian edge02) (![1, 0, -1] : Fin 3 → ℝ) = 4 := by
      rw [edge02_laplacian_eq_rankOne, rankOne_quadForm]
      norm_num [Matrix.dotProduct, Fin.sum_univ_three]
    have hle := abs_quadForm_le_of_l2OpNorm_le
      (t := ‖laplacian edge02‖) (le_refl _) (![1, 0, -1] : Fin 3 → ℝ)
    rw [hq, abs_of_nonneg (by norm_num),
      show Matrix.dotProduct (![1, 0, -1] : Fin 3 → ℝ)
        (![1, 0, -1] : Fin 3 → ℝ) = 2 from
        by norm_num [Matrix.dotProduct, Fin.sum_univ_three]] at hle
    linarith

theorem path3_deg_QA (i : Fin 3) :
    deg path3Adj i = if (i : ℕ) = 1 then 2 else 1 := by
  fin_cases i <;> rw [deg, Fin.sum_univ_three] <;> norm_num [path3Adj]

theorem path3_add_edge02 : path3Adj + edge02 = k3Adj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [path3Adj, edge02, k3Adj, Matrix.of_apply]

theorem path3_supportGraph_connected :
    (supportGraph path3Adj path3Adj_symmetric).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨1, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.cons (u := 1) (v := 0) (w := 0)
      ⟨by decide, by simp [path3Adj]⟩ SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 1) (v := 2) (w := 2)
      ⟨by decide, by simp [path3Adj]⟩ SimpleGraph.Walk.nil⟩

theorem k3_supportGraph_connected :
    (supportGraph k3Adj k3Adj_symmetric).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨1, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.cons (u := 1) (v := 0) (w := 0)
      ⟨by decide, by simp [k3Adj]⟩ SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 1) (v := 2) (w := 2)
      ⟨by decide, by simp [k3Adj]⟩ SimpleGraph.Walk.nil⟩

theorem sum_nonneg : ∀ i j, 0 ≤ (path3Adj + edge02) i j := by
  intro i j
  simp only [Matrix.add_apply]
  have h1 : 0 ≤ path3Adj i j := path3Adj_nonneg i j
  have h2 : 0 ≤ edge02 i j := edge02_nonneg i j
  linarith

theorem sum_supportGraph_connected :
    (supportGraph (path3Adj + edge02) (path3Adj_symmetric.add edge02_isSymm)).Connected := by
  have heq : supportGraph (path3Adj + edge02) (path3Adj_symmetric.add edge02_isSymm)
      = supportGraph k3Adj k3Adj_symmetric := by
    ext i j
    simp only [supportGraph_adj]
    constructor <;> intro ⟨hij, hpos⟩
    · exact ⟨hij, by rw [path3_add_edge02] at hpos; exact hpos⟩
    · exact ⟨hij, by rw [path3_add_edge02]; exact hpos⟩
  rw [heq]
  exact k3_supportGraph_connected

theorem line_sep_QA : (2 : ℝ) ≤ evals (laplacian_symmetric (path3Adj + edge02)
      (path3Adj_symmetric.add edge02_isSymm)) ⟨2, by norm_num⟩
    - evals (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨1, by norm_num⟩ := by
  rw [evals_congr (laplacian_symmetric (path3Adj + edge02)
      (path3Adj_symmetric.add edge02_isSymm))
    (laplacian_symmetric k3Adj k3Adj_symmetric)
    (by rw [path3_add_edge02]) ⟨2, by norm_num⟩,
    k3_evals_two_eq_three_QA, path3_evals_one_eq_one_QA]
  norm_num

/-- **The headline instance: the P₃ → K₃ edge addition.** The
separation `δ = 2` is discharged against the two pinned spectra
(`λ₃(L K₃) = 3`, `λ₂(L P₃) = 1`) — the load-bearing step, since only
that difference admits `δ = 2` — and the bound evaluates to
`‖laplacian edge02‖ / 2 = 2 / 2 = 1`. The perturbed side `K₃` sits
exactly on Davis–Kahan's own tie branch (`λ₂ = λ₃ = 3`), the branch
whose proof route yields `≤ 1 ≤ ‖E‖/δ` with **no slack here**: the
derived bound is exactly `1`, not a vacuous margin. -/
theorem fiedlerLine_K3_le_one_QA :
    ‖(initialProjector (laplacian (path3Adj + edge02))
          (laplacian_symmetric (path3Adj + edge02)
            (path3Adj_symmetric.add edge02_isSymm)) ⟨1, by norm_num⟩
        - initialProjector (laplacian (path3Adj + edge02))
          (laplacian_symmetric (path3Adj + edge02)
            (path3Adj_symmetric.add edge02_isSymm)) ⟨0, by norm_num⟩)
      - (initialProjector (laplacian path3Adj)
          (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨1, by norm_num⟩
        - initialProjector (laplacian path3Adj)
          (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨0, by norm_num⟩)‖
      ≤ 1 := by
  have h := fiedlerLine_stability path3Adj edge02 path3Adj_symmetric edge02_isSymm
    path3Adj_nonneg sum_nonneg path3_supportGraph_connected
    sum_supportGraph_connected (by norm_num : (3 : ℕ) ≤ Fintype.card (Fin 3))
    2 (by norm_num) line_sep_QA
  rwa [edge02_laplacian_norm, div_self two_ne_zero] at h

/-- **The identification instance at a genuine two-spectrum pair:** `P₃`
(spectrum `{0, 1, 3}`) and `K₃` (spectrum `{0, 3, 3}`) share the kernel
line, so their index-0 projectors coincide — the equality the headline
uses internally, exercised at operators that differ everywhere except
on the constants. -/
theorem initialProjector_zero_path3_eq_k3_QA :
    initialProjector (laplacian path3Adj)
        (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨0, by norm_num⟩
      = initialProjector (laplacian k3Adj)
        (laplacian_symmetric k3Adj k3Adj_symmetric) ⟨0, by norm_num⟩ :=
  initialProjector_laplacian_zero_eq_of_connected path3Adj k3Adj
    path3Adj_symmetric k3Adj_symmetric path3Adj_nonneg k3Adj_nonneg
    path3_supportGraph_connected k3_supportGraph_connected (by norm_num)

/-- The fix-iff, positive side: the constant vector is fixed by the
index-0 projector of `P₃` (kernel to fixed space). -/
theorem initialProjector_zero_fix_ones_QA :
    initialProjector (laplacian path3Adj)
        (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨0, by norm_num⟩ *ᵥ
      (onesVec : Fin 3 → ℝ) = onesVec :=
  (initialProjector_laplacian_zero_fix_iff path3Adj path3Adj_symmetric
    path3Adj_nonneg (by norm_num) onesVec).2
    (laplacian_ones_in_kernel path3Adj)

/-- The fix-iff, negative side: `![1, 2, 3]` is not constant, is not in
the kernel of `P₃`'s Laplacian (`L *ᵥ ![1, 2, 3] = ![-1, 0, 1] ≠ 0` by
the diffusion form), and is therefore not fixed by the index-0
projector. -/
theorem initialProjector_zero_nofix_123_QA :
    initialProjector (laplacian path3Adj)
        (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨0, by norm_num⟩ *ᵥ
      (![1, 2, 3] : Fin 3 → ℝ) ≠ (![1, 2, 3] : Fin 3 → ℝ) := by
  intro hfix
  have hker := (initialProjector_laplacian_zero_fix_iff path3Adj path3Adj_symmetric
    path3Adj_nonneg (by norm_num) _).1 hfix
  have hL : (laplacian path3Adj) *ᵥ (![1, 2, 3] : Fin 3 → ℝ)
      = ![(-1 : ℝ), 0, 1] := by
    funext i
    fin_cases i <;> rw [laplacian_mulVec_apply, Fin.sum_univ_three] <;>
      norm_num [path3Adj, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_succ, Matrix.head_cons]
  rw [hL] at hker
  have h0 := congrFun hker 0
  have hne : (![(-1 : ℝ), 0, 1] : Fin 3 → ℝ) 0 ≠ (0 : Fin 3 → ℝ) 0 := by
    norm_num
  exact absurd h0 hne

/-- **The disconnected fence: the identification fails without
connectivity.** The empty graph's Laplacian is the zero matrix, so its
index-0 projector fixes every kernel vector — including `e₀` (the
kernel is everything); `P₃`'s projector does not fix `e₀` (it is not in
the kernel: `L *ᵥ e₀ = ![1, -1, 0] ≠ 0`). Both directions of the
fix-iff are exercised, and the identification's connectivity hypothesis
is proved load-bearing rather than decorative. -/
theorem initialProjector_zero_disconnected_fence_QA :
    initialProjector (laplacian (0 : WAdj (V := Fin 3)))
        (laplacian_symmetric 0 (by simp)) ⟨0, by norm_num⟩
      ≠ initialProjector (laplacian path3Adj)
        (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨0, by norm_num⟩ := by
  intro heq
  have h1 : initialProjector (laplacian (0 : WAdj (V := Fin 3)))
      (laplacian_symmetric 0 (by simp)) ⟨0, by norm_num⟩ *ᵥ
      (![1, 0, 0] : Fin 3 → ℝ) = (![1, 0, 0] : Fin 3 → ℝ) := by
    refine (initialProjector_laplacian_zero_fix_iff (0 : WAdj (V := Fin 3))
      (by simp) (fun i j => by simp) (by norm_num) _).2 ?_
    rw [laplacian_zero (V := Fin 3), Matrix.zero_mulVec]
  have h2 : initialProjector (laplacian path3Adj)
      (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨0, by norm_num⟩ *ᵥ
      (![1, 0, 0] : Fin 3 → ℝ) ≠ (![1, 0, 0] : Fin 3 → ℝ) := by
    intro hfix
    have hker := (initialProjector_laplacian_zero_fix_iff path3Adj
      path3Adj_symmetric path3Adj_nonneg (by norm_num) _).1 hfix
    have hL : (laplacian path3Adj) *ᵥ (![1, 0, 0] : Fin 3 → ℝ)
        = ![1, -1, 0] := by
      funext i
      fin_cases i <;> rw [laplacian_mulVec_apply, Fin.sum_univ_three] <;>
        norm_num [path3Adj, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_succ, Matrix.head_cons]
    rw [hL] at hker
    have h0 := congrFun hker 0
    have hne : (![1, -1, 0] : Fin 3 → ℝ) 0 ≠ (0 : Fin 3 → ℝ) 0 := by
      norm_num
    exact absurd h0 hne
  exact h2 (heq ▸ h1)

end FiedlerLineStability
