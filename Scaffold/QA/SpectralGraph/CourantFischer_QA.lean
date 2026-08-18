/-
  CourantFischer_QA.lean

  Purpose
  -------
  QA lemmas for the general Courant–Fischer min–max interface of
  `Scaffold.Mathlib.GraphTheory.Spectral`
  (`exists_submodule_forall_rayleigh_le`,
  `exists_ne_mem_rayleigh_ge_of_finrank_eq`, `evals_min_max`), proved
  2026-08-18:

  - a two-vertex symmetric-matrix fixture `!![2, 1; 1, 2]` whose sorted
    spectrum `[1, 3]` is pinned from trace, determinant, and sortedness
    (independently of the theorem);
  - both directions instantiated: the competitor direction on a concrete
    line, and — through the existence direction plus
    `Submodule.eq_top_of_finrank_eq` — the derived universal that every
    Rayleigh quotient is at most the top eigenvalue, with the witness of
    the competitor direction then pinned to attain it exactly;
  - negative witnesses: the existence-direction property is shown to
    *discriminate* subspaces (it fails on the wrong line, `3 ≤ 1`
    refuted), and the competitor direction's dimension hypothesis is
    witnessed load-bearing (its conclusion fails on a one-dimensional
    subspace at index `1`);
  - an interior-index (`k = 1 < n - 1`) instantiation on the three-vertex
    path Laplacian: the competitor direction bounds `evals 1 ≤ 1` on a
    hand-checked two-dimensional subspace whose members all have
    Rayleigh quotient at most `1`, the bound agrees with the older
    `secondEval_le_rayleigh` engine, and a wrong two-dimensional
    subspace is refuted (`4/3 ≤ evals 1` contradicts `evals 1 ≤ 1`).

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not
  prove the theorem; it checks its interface against independently
  computed values and falsifies nearby wrong statements.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral

/-!
# QA for the general Courant–Fischer min–max
-/

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## Fixture 1: the symmetric matrix `!![2, 1; 1, 2]` on `Fin 2`

Sorted spectrum `[1, 3]`, pinned by trace (`4`), determinant (`3`), and
sortedness. All entries are rational, so every Rayleigh value below is
computed entrywise, without the spectral theorem.
-/

section Mat2

/-- The fixture: a symmetric, positive-definite integer matrix with
spectrum `{1, 3}` — not a Laplacian, exercising that the theorem needs
only symmetry. -/
def mat2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, 1; 1, 2]

theorem mat2_symmetric : mat2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, mat2]

theorem mat2_apply (i j : Fin 2) : mat2 i j = if i = j then 2 else 1 := by
  fin_cases i <;> fin_cases j <;> simp [mat2]

theorem mat2_trace : mat2.trace = 4 := by
  simp [Matrix.trace, mat2_apply]
  norm_num

theorem mat2_det : mat2.det = 3 := by
  have h00 : mat2 0 0 = 2 := by simp [mat2_apply]
  have h11 : mat2 1 1 = 2 := by simp [mat2_apply]
  have h01 : mat2 0 1 = 1 := by simp [mat2_apply]
  have h10 : mat2 1 0 = 1 := by simp [mat2_apply]
  rw [Matrix.det_fin_two, h00, h11, h01, h10]
  norm_num

private theorem list_two_eq {l : List ℝ} (h : l.length = 2) :
    l = [l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩] :=
  List.ext_get h (by
    intro n h₁ h₂
    have hn2 : n < 2 := by omega
    interval_cases n <;> simp)

/-- Two-point spectrum pinning for the fixture: a sorted length-two
list with sum `4` and product `3` is `[1, 3]`. -/
private theorem two_point_pin13 {l : List ℝ} (h2 : l.length = 2)
    (hs : l.Sorted (fun a b => a ≤ b)) (hsum : l.sum = 4)
    (hprod : l.prod = 3) :
    l.get ⟨0, by omega⟩ = 1 ∧ l.get ⟨1, by omega⟩ = 3 := by
  obtain ⟨g₀, g₁, hg⟩ : ∃ a b : ℝ, l = [a, b] :=
    ⟨l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩, list_two_eq h2⟩
  subst hg
  have hmono : g₀ ≤ g₁ := by
    have h := hs.rel_get_of_lt (show (0 : Fin 2) < 1 by decide)
    simpa using h
  simp only [List.sum_cons, List.sum_nil, add_zero, List.prod_cons,
    List.prod_nil, mul_one] at hsum hprod
  have hsq : (g₁ - g₀) ^ 2 = 4 := by
    have hring : (g₁ - g₀) ^ 2 = (g₀ + g₁) ^ 2 - 4 * (g₀ * g₁) := by ring
    rw [hsum, hprod] at hring
    norm_num at hring
    exact hring
  have hd : g₁ - g₀ = 2 := by
    have hfactor : (g₁ - g₀ - 2) * (g₁ - g₀ + 2) = 0 := by
      have hexp : (g₁ - g₀ - 2) * (g₁ - g₀ + 2)
          = (g₁ - g₀) ^ 2 - 4 := by ring
      rw [hexp, hsq]
      ring
    rcases mul_eq_zero.1 hfactor with h | h
    · linarith
    · have hn : g₁ - g₀ = -2 := by linarith
      linarith
  refine ⟨?_, ?_⟩
  · show g₀ = 1
    linarith
  · show g₁ = 3
    linarith

/-- The sorted spectrum of the fixture is exactly `[1, 3]`: the first
entry is `1` and the second is `3`, from trace, determinant, and
sortedness — independent of the min–max theorem. A mis-sorted or
off-by-one `evals` fails this pin. -/
theorem mat2_evals_pin :
    evals mat2_symmetric ⟨0, by simp⟩ = 1 ∧
      evals mat2_symmetric ⟨1, by simp⟩ = 3 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm mat2_symmetric).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm mat2_symmetric).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm mat2_symmetric).eigenvalues))).sum = 4 := by
    have htr : ∑ i : Fin 2, eigvalOf mat2 mat2_symmetric i = 4 := by
      rw [eigvalOf_sum_eq_trace, mat2_trace]
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm mat2_symmetric).eigenvalues))).prod = 3 := by
    have hd : ∏ i : Fin 2,
        ((isHermitian_of_isSymm mat2_symmetric).eigenvalues i) = 3 := by
      have hd0 := (isHermitian_of_isSymm mat2_symmetric).det_eq_prod_eigenvalues
      rw [mat2_det] at hd0
      simpa using hd0.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    exact hd
  exact two_point_pin13 hlen hsorted hsum hprod

/-- The Rayleigh quotient at the low eigenvector `![1, -1]` is exactly
`evals 0 = 1` — computed entrywise. -/
theorem mat2_rayleigh_low : rayleigh mat2 ![1, -1] = 1 := by
  have hne : (![1, -1] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  rw [rayleigh, if_neg hne]
  norm_num [quadForm, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, mat2_apply]

/-- The Rayleigh quotient at the high eigenvector `![1, 1]` is exactly
`evals 1 = 3` — computed entrywise. -/
theorem mat2_rayleigh_high : rayleigh mat2 ![1, 1] = 3 := by
  have hne : (![1, 1] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  rw [rayleigh, if_neg hne]
  norm_num [quadForm, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, mat2_apply]

/-!
### Line subspaces of `Fin 2 → ℝ`
-/

/-- A single nonzero vector is a linearly independent family. -/
private theorem linearIndependent_single {v : Fin 2 → ℝ} (hv : v ≠ 0) :
    LinearIndependent ℝ (fun _ : Fin 1 => v) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  have h0 : g 0 • v = 0 := by simpa [Fin.sum_univ_one] using hg
  rcases smul_eq_zero.1 h0 with h | h
  · exact h
  · exact absurd h hv

/-- Every nonzero member of the high line `span {![1, 1]}` has Rayleigh
quotient exactly `3`. -/
theorem mat2_rayleigh_of_mem_high_line {y : Fin 2 → ℝ}
    (hy : y ∈ Submodule.span ℝ
      (Set.range fun _ : Fin 1 => (![1, 1] : Fin 2 → ℝ)))
    (hy0 : y ≠ 0) :
    rayleigh mat2 y = 3 := by
  rw [mem_span_range_iff_exists_fun] at hy
  obtain ⟨c, hc⟩ := hy
  have hye : y = ![c 0, c 0] := by
    rw [← hc]
    funext i
    fin_cases i <;> simp [Fin.sum_univ_one]
  have hc0 : c 0 ≠ 0 := by
    intro h
    apply hy0
    rw [hye, h]
    simp
  rw [hye, rayleigh, if_neg (by
    intro h
    have h0 := congrFun h 0
    simp [hc0] at h0)]
  have hq : quadForm mat2 ![c 0, c 0] = 6 * c 0 * c 0 := by
    rw [quadForm]
    norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, mat2_apply]
    ring
  have hd : Matrix.dotProduct ![c 0, c 0] ![c 0, c 0] = 2 * c 0 * c 0 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero]
    rw [show (![c 0, c 0] : Fin 2 → ℝ) 1 = c 0 from rfl]
    ring
  rw [hq, hd]
  field_simp
  ring

/-- Every nonzero member of the low line `span {![1, -1]}` has Rayleigh
quotient exactly `1`. -/
theorem mat2_rayleigh_of_mem_low_line {y : Fin 2 → ℝ}
    (hy : y ∈ Submodule.span ℝ
      (Set.range fun _ : Fin 1 => (![1, -1] : Fin 2 → ℝ)))
    (hy0 : y ≠ 0) :
    rayleigh mat2 y = 1 := by
  rw [mem_span_range_iff_exists_fun] at hy
  obtain ⟨c, hc⟩ := hy
  have hye : y = ![c 0, -c 0] := by
    rw [← hc]
    funext i
    fin_cases i <;> simp [Fin.sum_univ_one]
  have hc0 : c 0 ≠ 0 := by
    intro h
    apply hy0
    rw [hye, h]
    simp
  rw [hye, rayleigh, if_neg (by
    intro h
    have h0 := congrFun h 0
    simp [hc0] at h0)]
  have hq : quadForm mat2 ![c 0, -c 0] = 2 * c 0 * c 0 := by
    rw [quadForm]
    norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, mat2_apply]
    ring
  have hd : Matrix.dotProduct ![c 0, -c 0] ![c 0, -c 0] = 2 * c 0 * c 0 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero]
    rw [show (![c 0, -c 0] : Fin 2 → ℝ) 1 = -c 0 from rfl]
    ring
  rw [hq, hd]
  field_simp

/-- **Competitor direction, `k = 0`, instance.** On the concrete line
`span {![1, 1]}` (dimension `1 = k + 1` by hand), the theorem produces a
test vector with Rayleigh quotient at least `evals 0 = 1`; the line
computation above shows that quotient is exactly `3`. -/
theorem mat2_dir2_k0_line_instance_QA :
    ∃ x ∈ Submodule.span ℝ
        (Set.range fun _ : Fin 1 => (![1, 1] : Fin 2 → ℝ)),
      x ≠ 0 ∧ evals mat2_symmetric ⟨0, by simp⟩ ≤ rayleigh mat2 x := by
  refine exists_ne_mem_rayleigh_ge_of_finrank_eq mat2_symmetric ⟨0, by simp⟩ _ ?_
  rw [finrank_span_eq_card (linearIndependent_single (by
    intro h
    have h0 := congrFun h 0
    simp at h0))]
  simp

/-- **Existence direction, `k = 0`, discrimination.** The
all-Rayleigh-quotients-at-most-`evals 0` property *fails* on the wrong
line `span {![1, 1]}` (whose members have quotient `3`): with
`evals 0 = 1` pinned, this refutes `3 ≤ 1`. The property is therefore
not vacuous, and an inverted (descending) `evals` would fail this
witness. -/
theorem mat2_dir1_k0_wrong_line_QA :
    ¬ ∀ x ∈ Submodule.span ℝ
        (Set.range fun _ : Fin 1 => (![1, 1] : Fin 2 → ℝ)),
      x ≠ 0 → rayleigh mat2 x ≤ evals mat2_symmetric ⟨0, by simp⟩ := by
  intro h
  have hmem : (![1, 1] : Fin 2 → ℝ) ∈ Submodule.span ℝ
      (Set.range fun _ : Fin 1 => (![1, 1] : Fin 2 → ℝ)) := by
    rw [mem_span_range_iff_exists_fun]
    refine ⟨fun _ => 1, ?_⟩
    simp [Fin.sum_univ_one]
  have hne : (![1, 1] : Fin 2 → ℝ) ≠ 0 := by
    intro h0
    have h1 := congrFun h0 0
    simp at h1
  have hval := h _ hmem hne
  rw [mat2_rayleigh_of_mem_high_line hmem hne, mat2_evals_pin.1] at hval
  exact absurd hval (by norm_num)

/-- **Existence direction, `k = 0`, positive line check.** The
eigendirection line `span {![1, -1]}` does satisfy the property: every
nonzero member has quotient exactly `evals 0 = 1`. Together with
`mat2_dir1_k0_wrong_line_QA`, the property separates the two lines. -/
theorem mat2_dir1_k0_line_holds_QA :
    ∀ x ∈ Submodule.span ℝ
        (Set.range fun _ : Fin 1 => (![1, -1] : Fin 2 → ℝ)),
      x ≠ 0 → rayleigh mat2 x ≤ evals mat2_symmetric ⟨0, by simp⟩ := by
  intro x hx hx0
  rw [mat2_rayleigh_of_mem_low_line hx hx0, mat2_evals_pin.1]

/-- **Existence direction, `k = 1`, derived universal.** The theorem's
`k = 1` subspace is two-dimensional, hence the whole space, so the
existence direction yields: *every* vector's Rayleigh quotient is at
most `evals 1 = 3` — the top eigenvalue dominates, derived through the
theorem rather than assumed. -/
theorem mat2_rayleigh_le_max_of_dir1_QA :
    ∀ x : Fin 2 → ℝ, rayleigh mat2 x ≤ evals mat2_symmetric ⟨1, by simp⟩ := by
  obtain ⟨W', hdim, hbound⟩ :=
    exists_submodule_forall_rayleigh_le mat2_symmetric ⟨1, by simp⟩
  have htop : W' = ⊤ := Submodule.eq_top_of_finrank_eq (by
    rw [hdim]
    simp [finrank_top, Module.finrank_pi])
  intro x
  by_cases hx : x = 0
  · subst hx
    have hzero : rayleigh mat2 0 = 0 := by simp [rayleigh]
    rw [hzero, mat2_evals_pin.2]
    norm_num
  · exact hbound x (by rw [htop]; trivial) hx

theorem mat2_finrank_top : Module.finrank ℝ (⊤ : Submodule ℝ (Fin 2 → ℝ)) = 2 := by
  rw [finrank_top, Module.finrank_pi]; simp

/-- **Competitor direction, `k = 1`, attainment.** On the whole space
(dimension `2 = k + 1`), the theorem's witness has quotient at least
`evals 1`, and the derived universal bounds every quotient by
`evals 1` — so the witness attains `evals 1 = 3` exactly, through both
directions of the theorem. -/
theorem mat2_dir2_k1_attained_QA :
    ∃ x : Fin 2 → ℝ, x ≠ 0 ∧
      rayleigh mat2 x = evals mat2_symmetric ⟨1, by simp⟩ := by
  obtain ⟨x, -, hx0, hge⟩ := exists_ne_mem_rayleigh_ge_of_finrank_eq
    mat2_symmetric ⟨1, by simp⟩ ⊤ mat2_finrank_top
  exact ⟨x, hx0, le_antisymm (mat2_rayleigh_le_max_of_dir1_QA x) hge⟩

/-- **Competitor direction, dimension hypothesis load-bearing.** At
index `1`, a one-dimensional subspace is too small: on the line
`span {![1, -1]}` every nonzero member has quotient exactly `1 < 3`,
so the theorem's conclusion is *false* there. The hypothesis
`finrank W = k + 1` cannot be weakened to `finrank W ≥ 1`. -/
theorem mat2_dir2_k1_dim_load_bearing_QA :
    ¬ (∃ x ∈ Submodule.span ℝ
        (Set.range fun _ : Fin 1 => (![1, -1] : Fin 2 → ℝ)),
        x ≠ 0 ∧ evals mat2_symmetric ⟨1, by simp⟩ ≤ rayleigh mat2 x) := by
  rintro ⟨x, hxmem, hx0, hge⟩
  rw [mat2_rayleigh_of_mem_low_line hxmem hx0, mat2_evals_pin.2] at hge
  exact absurd hge (by norm_num)

end Mat2

/-!
## Fixture 2: the three-vertex path Laplacian (interior index `k = 1`)

`Fin 3` is the smallest size where `k = 1` is an interior index
(`k + 1 = 2 < 3 = n`), so the dimension-counting step of the competitor
direction is genuinely load-bearing rather than degenerating to the
whole space.
-/

section Path3

/-- Adjacency of the three-vertex path `0 - 1 - 2` (weight `1` per
edge): neighbors are exactly the index pairs at distance one. -/
def path3Adj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if i.val + j.val = 1 ∨ i.val + j.val = 3 then 1 else 0

theorem path3Adj_symmetric : path3Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [Matrix.transpose_apply, Matrix.of_apply, path3Adj]
  by_cases h : j.val + i.val = 1 ∨ j.val + i.val = 3
  · rw [if_pos h]
    exact (if_pos (h.imp
      (fun hc => by rw [add_comm j.val i.val] at hc; exact hc)
      (fun hc => by rw [add_comm j.val i.val] at hc; exact hc))).symm
  · rw [if_neg h]
    exact (if_neg (fun hcon : i.val + j.val = 1 ∨ i.val + j.val = 3 =>
      h (hcon.imp
        (fun hc => by rw [add_comm i.val j.val] at hc; exact hc)
        (fun hc => by rw [add_comm i.val j.val] at hc; exact hc)))).symm

theorem path3Adj_nonneg : ∀ i j, 0 ≤ path3Adj i j := by
  intro i j
  by_cases h : i.val + j.val = 1 ∨ i.val + j.val = 3 <;> simp [path3Adj, h]

theorem path3_deg (i : Fin 3) :
    deg path3Adj i = if i = 1 then 2 else 1 := by
  fin_cases i <;>
    simp only [deg, Fin.sum_univ_three, Matrix.of_apply, path3Adj] <;>
    norm_num; simp

theorem path3_diag_zero (i : Fin 3) : path3Adj i i = 0 := by
  fin_cases i <;>
    simp only [Matrix.of_apply, path3Adj] <;> norm_num

theorem path3_lap_entry (i j : Fin 3) :
    laplacian path3Adj i j =
      if i = j then (if i = 1 then 2 else 1) else -(path3Adj i j) := by
  by_cases hij : i = j
  · subst hij
    have hd0 : path3Adj i i = 0 := path3_diag_zero i
    rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal, path3_deg,
      hd0]
    simp
  · rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal _ hij,
      zero_sub, if_neg hij]

/-- Fully numeric Laplacian entries of the path: diagonal `1, 2, 1`,
off-diagonal `-1` on the two edges, `0` elsewhere. -/
theorem path3_lap_val (i j : Fin 3) :
    laplacian path3Adj i j =
      if i.val = j.val then (if i.val = 1 then 2 else 1)
      else if i.val + j.val = 1 ∨ i.val + j.val = 3 then -1 else 0 := by
  rw [path3_lap_entry]
  by_cases hij : i = j
  · subst hij
    by_cases h1 : i.val = 1
    · have h2 : i = 1 := Fin.ext h1
      simp [h1, h2]
    · have h2 : ¬ i = 1 := fun h => h1 (congrArg Fin.val h)
      simp [h1, h2]
  · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    by_cases h : i.val + j.val = 1 ∨ i.val + j.val = 3
    · simp [hij, hval, h, path3Adj]
    · simp [hij, hval, h, path3Adj]

theorem path3_laplacian_symmetric :
    (laplacian path3Adj).IsSymm :=
  laplacian_symmetric path3Adj path3Adj_symmetric

/-- The two-dimensional test subspace for the interior index: the span
of the constant vector and the alternating-cut vector. -/
def path3W2 : Submodule ℝ (Fin 3 → ℝ) :=
  Submodule.span ℝ (Set.range ![![1, 1, 1], ![1, 0, -1]])

theorem path3W2_mem_iff {y : Fin 3 → ℝ} :
    y ∈ path3W2 ↔ ∃ a b : ℝ, y = ![a + b, a, a - b] := by
  constructor
  · intro hy
    have hy' : y ∈ Submodule.span ℝ
        (Set.range (![![1, 1, 1], ![1, 0, -1]] : Fin 2 → (Fin 3 → ℝ))) := hy
    rw [mem_span_range_iff_exists_fun] at hy'
    obtain ⟨c, hc⟩ := hy'
    refine ⟨c 0, c 1, ?_⟩
    rw [← hc]
    funext k
    fin_cases k <;> simp [Fin.sum_univ_two]; all_goals ring
  · rintro ⟨a, b, rfl⟩
    have hgoal : (![a + b, a, a - b] : Fin 3 → ℝ) ∈ Submodule.span ℝ
        (Set.range (![![1, 1, 1], ![1, 0, -1]] : Fin 2 → (Fin 3 → ℝ))) := by
      rw [mem_span_range_iff_exists_fun]
      refine ⟨![a, b], ?_⟩
      funext k
      fin_cases k <;> simp [Fin.sum_univ_two]; all_goals ring
    exact hgoal

theorem path3W2_finrank : Module.finrank ℝ path3W2 = 2 := by
  have hli : LinearIndependent ℝ
      (![![1, 1, 1], ![1, 0, -1]] : Fin 2 → (Fin 3 → ℝ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hexp : (∑ j : Fin 2, g j •
        (![![1, 1, 1], ![1, 0, -1]] : Fin 2 → (Fin 3 → ℝ)) j)
        = ![g 0 + g 1, g 0, g 0 - g 1] := by
      funext k
      fin_cases k <;> simp [Fin.sum_univ_two]; all_goals ring
    rw [hexp] at hg
    have hmid : g 0 = 0 := by
      have h1 := congrFun hg 1
      simp at h1
      exact h1
    have hfirst : g 0 + g 1 = 0 := by
      have h0 := congrFun hg 0
      simp at h0
      exact h0
    fin_cases i <;> simp [hmid]; all_goals linarith
  show Module.finrank ℝ (Submodule.span ℝ
      (Set.range (![![1, 1, 1], ![1, 0, -1]] : Fin 2 → (Fin 3 → ℝ)))) = 2
  rw [finrank_span_eq_card hli]
  simp

/-- Parametric quadratic form on the test subspace: the energy of
`a • ![1,1,1] + b • ![1,0,-1]` is `2 b²`. -/
theorem path3_span_quadForm (a b : ℝ) :
    quadForm (laplacian path3Adj) ![a + b, a, a - b] = 2 * b * b := by
  have hmul : (laplacian path3Adj) *ᵥ ![a + b, a, a - b] = ![b, 0, -b] := by
    funext k
    fin_cases k <;>
      simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
        path3_lap_val]; all_goals ring
  rw [quadForm, hmul]
  simp only [Matrix.dotProduct, Fin.sum_univ_three]
  rw [show (![a + b, a, a - b] : Fin 3 → ℝ) 0 = a + b from rfl,
    show (![a + b, a, a - b] : Fin 3 → ℝ) 1 = a from rfl,
    show (![a + b, a, a - b] : Fin 3 → ℝ) 2 = a - b from rfl,
    show (![b, 0, -b] : Fin 3 → ℝ) 0 = b from rfl,
    show (![b, 0, -b] : Fin 3 → ℝ) 1 = 0 from rfl,
    show (![b, 0, -b] : Fin 3 → ℝ) 2 = -b from rfl]
  ring

/-- Parametric squared norm on the test subspace: `3 a² + 2 b²`. -/
theorem path3_span_norm (a b : ℝ) :
    Matrix.dotProduct ![a + b, a, a - b] ![a + b, a, a - b]
      = 3 * a * a + 2 * b * b := by
  simp only [Matrix.dotProduct, Fin.sum_univ_three]
  rw [show (![a + b, a, a - b] : Fin 3 → ℝ) 0 = a + b from rfl,
    show (![a + b, a, a - b] : Fin 3 → ℝ) 1 = a from rfl,
    show (![a + b, a, a - b] : Fin 3 → ℝ) 2 = a - b from rfl]
  ring

/-- Every member of the test subspace has Rayleigh quotient at most
`1` (the zero vector by the junk convention, every nonzero member by
the parametric computation `2 b² ≤ 3 a² + 2 b²`). -/
theorem path3W2_rayleigh_le {y : Fin 3 → ℝ} (hy : y ∈ path3W2) :
    rayleigh (laplacian path3Adj) y ≤ 1 := by
  obtain ⟨a, b, rfl⟩ := path3W2_mem_iff.1 hy
  by_cases hy0 : (![a + b, a, a - b] : Fin 3 → ℝ) = 0
  · rw [rayleigh, if_pos hy0]
    norm_num
  · rw [rayleigh, if_neg hy0, path3_span_quadForm, path3_span_norm]
    have hpos : (0 : ℝ) < 3 * a * a + 2 * b * b := by
      have hentry : a ≠ 0 ∨ b ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        apply hy0
        funext k
        fin_cases k <;> simp [hcon.1, hcon.2]
      rcases hentry with ha | hb
      · have haa : 0 < a * a := mul_self_pos.2 ha
        have hbb : 0 ≤ b * b := mul_self_nonneg b
        nlinarith
      · have hbb : 0 < b * b := mul_self_pos.2 hb
        have haa : 0 ≤ a * a := mul_self_nonneg a
        nlinarith
    rw [div_le_iff₀ hpos]
    have hnn : 0 ≤ a * a := mul_self_nonneg a
    nlinarith

/-- **Competitor direction, interior index.** Through the theorem: the
second sorted eigenvalue of the path Laplacian is at most `1`. The
hand-checked subspace computation carries the whole content; the
theorem supplies the witness inside the subspace. -/
theorem path3_secondEval_le_one_QA :
    evals path3_laplacian_symmetric ⟨1, by simp⟩ ≤ 1 := by
  obtain ⟨x, hxmem, -, hge⟩ := exists_ne_mem_rayleigh_ge_of_finrank_eq
    path3_laplacian_symmetric ⟨1, by simp⟩ path3W2 path3W2_finrank
  exact hge.trans (path3W2_rayleigh_le hxmem)

/-- Cross-engine agreement: the same bound through the older, proved
`secondEval_le_rayleigh` engine at the alternating cut vector
`![1, 0, -1]` (orthogonal to `onesVec`, quotient exactly `1`). The two
variational engines bound the same eigenvalue by the same value. -/
theorem path3_secondEval_le_one_old_route_QA :
    secondEval (laplacian path3Adj) path3_laplacian_symmetric (by simp) ≤ 1 := by
  have hx0 : (![1, 0, -1] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have h2 := congrFun h 2
    simp at h2
  have horth : Matrix.dotProduct ![1, 0, -1] (onesVec : Fin 3 → ℝ) = 0 := by
    simp only [Matrix.dotProduct, onesVec, Fin.sum_univ_three]
    norm_num
  have hconv : (![0 + 1, 0, 0 - 1] : Fin 3 → ℝ) = ![1, 0, -1] := by
    funext k
    fin_cases k <;> norm_num
  have hq : quadForm (laplacian path3Adj) (![1, 0, -1] : Fin 3 → ℝ)
      = 2 * 1 * 1 := by
    have h := path3_span_quadForm 0 1
    rwa [hconv] at h
  have hn : Matrix.dotProduct (![1, 0, -1] : Fin 3 → ℝ) (![1, 0, -1] : Fin 3 → ℝ)
      = 3 * 0 * 0 + 2 * 1 * 1 := by
    have h := path3_span_norm 0 1
    rwa [hconv] at h
  have hrw : rayleigh (laplacian path3Adj) ![1, 0, -1] = 1 := by
    rw [rayleigh, if_neg hx0, hq, hn]
    norm_num
  calc secondEval (laplacian path3Adj) path3_laplacian_symmetric (by simp)
      ≤ rayleigh (laplacian path3Adj) ![1, 0, -1] :=
        secondEval_le_rayleigh path3_laplacian_symmetric
          (laplacian_psd path3Adj path3Adj_symmetric path3Adj_nonneg)
          (laplacian_ones_in_kernel path3Adj) (by simp) hx0 horth
    _ = 1 := hrw

/-- The wrong two-dimensional subspace: span of the constant vector and
`![1, 1, -1]`, whose Rayleigh quotient is `4/3`. -/
def path3Wbad : Submodule ℝ (Fin 3 → ℝ) :=
  Submodule.span ℝ (Set.range ![![1, 1, 1], ![1, 1, -1]])

theorem path3Wbad_rayleigh_bad :
    rayleigh (laplacian path3Adj) ![1, 1, -1] = 4 / 3 := by
  have hne : (![1, 1, -1] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have h2 := congrFun h 2
    simp at h2
  have hmul : (laplacian path3Adj) *ᵥ ![1, 1, -1] = ![0, 2, -2] := by
    funext k
    fin_cases k <;>
      simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
        path3_lap_val]; all_goals ring
  rw [rayleigh, if_neg hne, quadForm, hmul]
  norm_num [Matrix.dotProduct, Fin.sum_univ_three]

theorem path3Wbad_mem_bad : (![1, 1, -1] : Fin 3 → ℝ) ∈ path3Wbad := by
  have hgoal : (![1, 1, -1] : Fin 3 → ℝ) ∈ Submodule.span ℝ
      (Set.range (![![1, 1, 1], ![1, 1, -1]] : Fin 2 → (Fin 3 → ℝ))) := by
    rw [mem_span_range_iff_exists_fun]
    refine ⟨![0, 1], ?_⟩
    funext k
    fin_cases k <;> simp [Fin.sum_univ_two]
  exact hgoal

/-- **Existence direction, interior index, discrimination.** The
all-quotients-at-most-`evals 1` property fails on the wrong
two-dimensional subspace: it contains `![1, 1, -1]` with quotient
`4/3`, while `evals 1 ≤ 1` through the competitor direction. A
two-dimensional `k = 1` subspace is therefore genuinely constrained,
not merely dimensional. -/
theorem path3_dir1_discriminates_QA :
    ¬ ∀ x ∈ path3Wbad, x ≠ 0 →
      rayleigh (laplacian path3Adj) x ≤
        evals path3_laplacian_symmetric ⟨1, by simp⟩ := by
  intro h
  have hne : (![1, 1, -1] : Fin 3 → ℝ) ≠ 0 := by
    intro h0
    have h2 := congrFun h0 2
    simp at h2
  have hval := h _ path3Wbad_mem_bad hne
  have hbad := hval.trans (path3_secondEval_le_one_QA)
  rw [path3Wbad_rayleigh_bad] at hbad
  exact absurd hbad (by norm_num)

end Path3

end SpectralGraphTheory.QA
