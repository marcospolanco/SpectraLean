/-
  MultiwayCheeger_QA.lean

  Purpose
  -------
  QA for the multiway Cheeger easy direction delivered in
  `Scaffold.Mathlib.GraphTheory.Multiway` together with its engine
  layer in `Scaffold.Mathlib.GraphTheory.Spectral`
  (`proposals/multiway-expansion.md`, 2026-08-26): the every-family
  statements

  - `cheeger_upper_bound_multiway`:
    `evals (L_sym) ⟨k−1⟩ ≤ 2 · max_i (boundary (S i) / vol (S i))`,
  - `cheeger_upper_bound_multiway_conductance`: the conductance form,

  and the engines `evals_le_of_card_eigvalOf_le` (order statistics ↔
  counting), `evals_le_of_linearIndependent` (subspace Rayleigh–Ritz),
  `evals_sum_eq_trace` (trace at the sorted API), and
  `exists_eigvalOf_eq_of_mulVec_eq_smul` (the eigenvalue-witness
  bridge).

  Sections:

  - **Fixture `K₂`** (`mwEdgeAdj`, degrees `1, 1`): degree/volume/
    boundary pins, the anti-aligned mode `![1, -1]` at eigenvalue `2`
    verified raw, and the independent lower pin
    `2 ≤ evals ⟨1⟩` through the eigenvalue-witness bridge composed
    with `eigvalOf_le_evals_last`.

  - **Fixture `P₃`** (`mwPathAdj`, degrees `1, 2, 1`): three raw
    eigenvector witnesses (the kernel `![1, √2, 1]` at `0`, the mode
    `![1, 0, -1]` at `1`, the mode `![1, -√2, 1]` at `2`), the exact
    head pin `evals ⟨0⟩ = 0` (kernel witness + PSD nonnegativity), the
    independent `evals ⟨1⟩ ≤ 1` through the NEW counting bridge at two
    raw witnesses, the independent `2 ≤ evals ⟨2⟩` through the witness
    bridge, and the trace identity exercised raw
    (`λ₁ + λ₂ + λ₃ = trace = 3`).

  - **Fixture `C₄`** (`mwCycleAdj`, degrees `2, 2, 2, 2` — the
    all-rational fixture where `L_sym = I − A/2`): boundary/volume of
    the singletons (`2` over `2`), the alternating mode
    `![1, 0, -1, 0]` at eigenvalue `2` verified raw, the independent
    `2 ≤ evals ⟨3⟩`, and the trace identity exercised raw
    (`trace = 4`).

  - **The instances** (proposal obligations 1–4, 6): K₂ `k = 2`
    singletons — tight equality `2 = 2 · 1` at BOTH statement forms;
    P₃ `k = 2` at the *non-covering* family `{0}, {2}` (the
    every-family, not-partition scope, joined to the independent
    `≤ 1` pin); P₃ `k = 3` singletons — the equality
    `evals ⟨2⟩ = 2 = 2 · 1` (independent `≥` side, theorem `≤` side),
    with the trace cross-check deriving `λ₂ = 1` and agreeing with the
    counting pin; C₄ `k = 4` singletons — tight equality at `k = n`;
    P₃ `k = 1` — the engine's zero-constraint edge instance at the
    exact pin `evals ⟨0⟩ = 0 ≤ 2 = 2 · 1`.

  - **The overlap fence** (obligation 5): the cyclic-pair family
    `{0,1}, {1,2}, {2,3}, {3,0}` on `C₄` — every hypothesis verified
    (nonempty parts, `boundary / vol = 2/4 = 1/2` each, computed raw),
    disjointness provably refuted (`1 ∈ S 0 ∩ S 1`), and the dropped
    conclusion refuted (`2 ≤ evals ⟨3⟩ > 1 = 2 · max`). Disjointness
    is exercised, not decorated.

  - **Absorption tightness**: the cross-part absorption lemma
    `laplacian_quadForm_multiwayCombination_le` holds with EQUALITY at
    the alternating combinations on both fixtures (K₂: `4 = 2 · 2`;
    C₄: `16 = 2 · 8`) — the constant `2` is sharp, and the per-part
    energy identity `quadForm_laplacian_partIndicator` is pinned raw
    on a C₄ singleton (both sides `2` by hand). These are the
    falsifiability anchors for the theorem's constant: a wrong
    constant, a wrong boundary, or a wrong indicator makes an equality
    pin fail.

  - **The ρ_k packaging** (the follow-on delivery, 2026-08-26): the
    pinned `λ₂ (L_sym C₄) = 1` (both sides independent: the counting
    bridge at two raw eigenvectors for `≤ 1`; the `(x₀+x₂)²`
    sum-of-squares through `secondEval_variational_of_ker` for `≥ 1`),
    then the star instance **`ρ₂(C₄) = 1/2` exact** — the adjacent-pair
    witness bounds above, the theorem joined to the pinned `λ₂ = 1`
    bounds below, so the minimum provably beats the diagonal
    partition's `1` (attainment exercised, not decorated);
    `ρ₂(K₂) = ρ₃(P₃) = 1` at the pinned top eigenvalues; the supplier
    instance at `3 ≤ 4`; and the **empty-set junk fence** — no
    3-partition of two vertices exists, so `ρ₃(K₂) = sInf ∅ = 0`: the
    partition-existence hypothesis is load-bearing.

  Non-circularity: every spectral pin consumed by an instance is
  produced by an independent route — raw eigenvector checks through
  the eigenvalue-witness bridge, the counting bridge at raw
  witnesses, or trace arithmetic — never by the theorem being
  instantiated. Where an equality pin joins an independent `≥` side to
  the theorem's `≤` side (K₂ `k = 2`, P₃ `k = 3`, C₄ `k = 4`), the
  comment says so explicitly.
-/
import Scaffold.Mathlib.GraphTheory.Multiway

open scoped BigOperators Matrix
namespace SpectralGraphTheory.MultiwayQA

/-!
## Shared helpers
-/

/-- A constant family's `sup'` is the constant (the sup of a singleton
value): used to evaluate every instance's `max_i` at the fixtures,
where all parts have the same `boundary / vol` ratio. -/
private theorem sup'_const {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) (c : ℝ)
    (h : ∀ i, f i = c) :
    Finset.univ.sup'
      (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin n)).Nonempty) f = c := by
  refine le_antisymm ?_ ?_
  · exact (Finset.sup'_le_iff
      (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin n)).Nonempty) f).2
      (fun i _ => (h i) ▸ le_refl c)
  · exact (Finset.le_sup'_iff
      (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin n)).Nonempty)).2
      ⟨⟨0, by omega⟩, Finset.mem_univ _, (h ⟨0, by omega⟩).symm.le⟩

/-- The eigenvalue-witness bridge composed with last-entry domination:
a raw eigenvector at `μ` gives the lower spectral pin
`μ ≤ evals ⟨n − 1⟩`. The bridge consumes completeness through
`dotProduct_eigvecOf`; no spectrum is computed. -/
private theorem evals_last_ge_of_mulVec_eq_smul {V : Type} [Fintype V]
    [DecidableEq V] {M : Matrix V V ℝ} (hM : M.IsSymm) (hcard : 1 ≤ Fintype.card V)
    {x : V → ℝ} {μ : ℝ} (hx : x ≠ 0) (hxμ : M *ᵥ x = μ • x) :
    μ ≤ evals hM ⟨Fintype.card V - 1, by omega⟩ := by
  obtain ⟨i, hi⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul hM hx hxμ
  exact hi ▸ eigvalOf_le_evals_last hM hcard i

/-- Boundary of a singleton via complement summation:
`boundary A {i} = ∑ j, A i j − A i i`. The uniform route for all
singleton boundary pins below. -/
private theorem boundary_singleton_eq {V : Type} [Fintype V] [DecidableEq V]
    (A : WAdj (V := V)) (i : V) :
    boundary A {i} = ∑ j, A i j - A i i := by
  rw [boundary, Finset.sum_singleton]
  have h := Finset.sum_add_sum_compl {i} (fun j => A i j)
  rw [Finset.sum_singleton] at h
  linarith

/-- Boundary of a general set as degree volume minus the internal
weight. The uniform route for the cyclic-pair boundaries. -/
private theorem boundary_eq {V : Type} [Fintype V] [DecidableEq V]
    (A : WAdj (V := V)) (S : Finset V) :
    boundary A S = ∑ u ∈ S, deg A u - ∑ u ∈ S, ∑ v ∈ S, A u v := by
  rw [boundary]
  have h : ∀ u ∈ S, ∑ v ∈ Sᶜ, A u v = ∑ v, A u v - ∑ v ∈ S, A u v := by
    intro u _
    have h2 := Finset.sum_add_sum_compl S (fun v => A u v)
    linarith
  rw [Finset.sum_congr rfl (fun u hu => h u hu), Finset.sum_sub_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun u _ => rfl)

/-!
## Fixture: the two-vertex edge `K₂`
-/

/-- Adjacency matrix of the two-vertex edge: `1`-regular, symmetric,
nonnegative. -/
def mwEdgeAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

theorem mwEdgeAdj_symmetric : mwEdgeAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [mwEdgeAdj]

theorem mwEdgeAdj_nonneg : ∀ i j, 0 ≤ mwEdgeAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [mwEdgeAdj]

theorem mwEdgeAdj_deg : ∀ i, deg mwEdgeAdj i = 1 := by
  intro i
  fin_cases i <;> simp [deg, mwEdgeAdj, Fin.sum_univ_two]

theorem mwEdgeAdj_pos_deg : ∀ i, 0 < deg mwEdgeAdj i := by
  intro i
  rw [mwEdgeAdj_deg]
  norm_num

theorem mwEdgeAdj_vol_single : ∀ i : Fin 2, vol mwEdgeAdj {i} = 1 := by
  intro i
  fin_cases i <;> simp [vol, mwEdgeAdj_deg]

theorem mwEdgeAdj_boundary_single : ∀ i : Fin 2, boundary mwEdgeAdj {i} = 1 := by
  intro i
  rw [boundary_singleton_eq]
  fin_cases i <;> simp [deg, mwEdgeAdj, Fin.sum_univ_two]

/-- The anti-aligned mode of the edge. -/
def mwEdgeVec : Fin 2 → ℝ := ![1, -1]

theorem mwEdgeVec_ne : mwEdgeVec ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [mwEdgeVec] at h0

/-- The anti-aligned mode is an eigenvector of `L_sym` at eigenvalue
`2`, verified entrywise from the definition of `normalizedLaplacian`
(degrees `1`, so the entry formula is `I − A`). -/
theorem mwEdgeAdj_normLap_antialigned :
    normalizedLaplacian mwEdgeAdj *ᵥ mwEdgeVec = (2 : ℝ) • mwEdgeVec := by
  have hentry : ∀ i j : Fin 2,
      normalizedLaplacian mwEdgeAdj i j
        = (if i = j then (1 : ℝ) else 0)
          - (Real.sqrt (deg mwEdgeAdj i))⁻¹ * mwEdgeAdj i j
            * (Real.sqrt (deg mwEdgeAdj j))⁻¹ := by
    intro i j
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal, degreeInvSqrt,
      Matrix.diagonal_apply]
  have hdeglit : ∀ i : Fin 2,
      deg !![0, 1; 1, 0] i = (1 : ℝ) := by
    intro i
    fin_cases i <;> simp [deg, Fin.sum_univ_two]
  funext i
  fin_cases i <;>
    simp only [hentry, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      mwEdgeVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul]
  all_goals
    simp [hdeglit, mwEdgeAdj, Real.sqrt_one]
  all_goals norm_num

/-- **The independent lower pin `2 ≤ λ₂` on `K₂`.** Raw eigenvector
check through the witness bridge; no spectrum is computed. -/
theorem mwEdgeAdj_secondEval_ge_two :
    (2 : ℝ) ≤ evals (normalizedLaplacian_symmetric mwEdgeAdj mwEdgeAdj_symmetric)
        ⟨1, by decide⟩ :=
  evals_last_ge_of_mulVec_eq_smul
    (normalizedLaplacian_symmetric mwEdgeAdj mwEdgeAdj_symmetric)
    (by decide) mwEdgeVec_ne mwEdgeAdj_normLap_antialigned

/-!
## Fixture: the three-vertex path `P₃`
-/

/-- Adjacency of the three-vertex path `0 — 1 — 2`: genuinely
irregular (degrees `1, 2, 1`), symmetric, nonnegative. -/
def mwPathAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; 1, 0, 1; 0, 1, 0]

theorem mwPathAdj_symmetric : mwPathAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [mwPathAdj]

theorem mwPathAdj_nonneg : ∀ i j, 0 ≤ mwPathAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [mwPathAdj]

theorem mwPathAdj_deg : ∀ i, deg mwPathAdj i = if i = 1 then 2 else 1 := by
  intro i
  fin_cases i <;> simp [deg, mwPathAdj, Fin.sum_univ_three]; all_goals norm_num

theorem mwPathAdj_pos_deg : ∀ i, 0 < deg mwPathAdj i := by
  intro i
  fin_cases i <;> simp [mwPathAdj_deg]

/-- The degree pin at the *literal* adjacency (survives simp's
unfolding of `mwPathAdj`). -/
private theorem mwPath_deglit : ∀ i : Fin 3,
    deg !![0, 1, 0; 1, 0, 1; 0, 1, 0] i = if i = 1 then 2 else 1 := by
  intro i
  fin_cases i <;> simp [deg, Fin.sum_univ_three]; all_goals norm_num

theorem mwPathAdj_vol_single : ∀ i : Fin 3, vol mwPathAdj {i}
    = if i = 1 then 2 else 1 := by
  intro i
  rw [vol, Finset.sum_singleton, mwPathAdj_deg]

theorem mwPathAdj_boundary_eq_vol_single (i : Fin 3) :
    boundary mwPathAdj {i} = vol mwPathAdj {i} := by
  rw [boundary_singleton_eq, vol, Finset.sum_singleton]
  have hdiag : mwPathAdj i i = 0 := by fin_cases i <;> rfl
  rw [hdiag, sub_zero]
  rfl

/-- The stretched-constant kernel witness `√D · 1 = ![1, √2, 1]`. -/
noncomputable def mwPathKerVec : Fin 3 → ℝ := ![1, Real.sqrt 2, 1]

theorem mwPathKerVec_ne : mwPathKerVec ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [mwPathKerVec] at h0

/-- The first mode of the path. -/
def mwPathModeOne : Fin 3 → ℝ := ![1, 0, -1]

theorem mwPathModeOne_ne : mwPathModeOne ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [mwPathModeOne] at h0

/-- The second mode of the path. -/
noncomputable def mwPathModeTwo : Fin 3 → ℝ := ![1, -Real.sqrt 2, 1]

theorem mwPathModeTwo_ne : mwPathModeTwo ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [mwPathModeTwo] at h0

/-- The shared entry formula for `L_sym` on `P₃`. -/
private theorem mwPathAdj_entry (i j : Fin 3) :
    normalizedLaplacian mwPathAdj i j
      = (if i = j then (1 : ℝ) else 0)
        - (Real.sqrt (deg mwPathAdj i))⁻¹ * mwPathAdj i j
          * (Real.sqrt (deg mwPathAdj j))⁻¹ := by
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, degreeInvSqrt,
    Matrix.diagonal_apply]


/-- The nine entries of `L_sym` on `P₃` at literal indices: `1` on the
diagonal, `-(√2)⁻¹` at the two edges, `0` off the path. -/
private theorem mwPathE00 : normalizedLaplacian mwPathAdj 0 0 = 1 := by
  rw [mwPathAdj_entry]; simp [mwPathAdj_deg, mwPathAdj]
private theorem mwPathE01 : normalizedLaplacian mwPathAdj 0 1 = -(Real.sqrt 2)⁻¹ := by
  rw [mwPathAdj_entry]; simp [mwPath_deglit, mwPathAdj, Real.sqrt_one]
private theorem mwPathE02 : normalizedLaplacian mwPathAdj 0 2 = 0 := by
  rw [mwPathAdj_entry]; simp [mwPathAdj_deg, mwPathAdj]
private theorem mwPathE10 : normalizedLaplacian mwPathAdj 1 0 = -(Real.sqrt 2)⁻¹ := by
  rw [mwPathAdj_entry]; simp [mwPath_deglit, mwPathAdj, Real.sqrt_one]
private theorem mwPathE11 : normalizedLaplacian mwPathAdj 1 1 = 1 := by
  rw [mwPathAdj_entry]; simp [mwPathAdj_deg, mwPathAdj]
private theorem mwPathE12 : normalizedLaplacian mwPathAdj 1 2 = -(Real.sqrt 2)⁻¹ := by
  rw [mwPathAdj_entry]; simp [mwPath_deglit, mwPathAdj, Real.sqrt_one]
private theorem mwPathE20 : normalizedLaplacian mwPathAdj 2 0 = 0 := by
  rw [mwPathAdj_entry]; simp [mwPathAdj_deg, mwPathAdj]
private theorem mwPathE21 : normalizedLaplacian mwPathAdj 2 1 = -(Real.sqrt 2)⁻¹ := by
  rw [mwPathAdj_entry]; simp [mwPath_deglit, mwPathAdj, Real.sqrt_one]
private theorem mwPathE22 : normalizedLaplacian mwPathAdj 2 2 = 1 := by
  rw [mwPathAdj_entry]; simp [mwPathAdj_deg, mwPathAdj]

/-- The kernel: `√D · 1` is in the kernel of `L_sym`, verified
entrywise — the middle entry is the `√2` cancellation
`(√2)⁻¹ + √2 = (√2)⁻¹ + (√2)⁻¹ + ... = 0` through `hkey`. -/
theorem mwPathAdj_normLap_kernel :
    normalizedLaplacian mwPathAdj *ᵥ mwPathKerVec = 0 := by
  have hs2 : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hinv : (Real.sqrt (2 : ℝ))⁻¹ * Real.sqrt 2 = 1 :=
    inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (by norm_num))
  have hkey : (Real.sqrt (2 : ℝ))⁻¹ + (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by
    calc (Real.sqrt 2)⁻¹ + (Real.sqrt 2)⁻¹
        = 2 * (Real.sqrt 2)⁻¹ := by ring
      _ = Real.sqrt 2 * Real.sqrt 2 * (Real.sqrt 2)⁻¹ := by rw [hs2]
      _ = Real.sqrt 2 * ((Real.sqrt 2)⁻¹ * Real.sqrt 2) := by ring
      _ = Real.sqrt 2 * 1 := by rw [hinv]
      _ = Real.sqrt 2 := by ring
  have h0 : (normalizedLaplacian mwPathAdj *ᵥ mwPathKerVec) 0
      = (0 : Fin 3 → ℝ) 0 := by
    rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
      mwPathE00, mwPathE01, mwPathE02]
    simp only [mwPathKerVec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Pi.zero_apply, mul_one, one_mul, zero_mul]
    linarith [hinv]
  have h1 : (normalizedLaplacian mwPathAdj *ᵥ mwPathKerVec) 1
      = (0 : Fin 3 → ℝ) 1 := by
    rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
      mwPathE10, mwPathE11, mwPathE12]
    have hv2 : mwPathKerVec 2 = 1 := rfl
    rw [hv2]
    simp only [mwPathKerVec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Pi.zero_apply, mul_one, one_mul]
    linarith [hkey]
  have h2 : (normalizedLaplacian mwPathAdj *ᵥ mwPathKerVec) 2
      = (0 : Fin 3 → ℝ) 2 := by
    have hv2 : mwPathKerVec 2 = 1 := rfl
    rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
      mwPathE20, mwPathE21, mwPathE22, hv2]
    simp only [mwPathKerVec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Pi.zero_apply, mul_one, one_mul, zero_mul]
    linarith [hinv]
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The first mode `![1, 0, -1]` is an eigenvector at eigenvalue `1`,
verified entrywise (the `√2` cross terms multiply the vanishing middle
entry). -/
theorem mwPathAdj_normLap_modeOne :
    normalizedLaplacian mwPathAdj *ᵥ mwPathModeOne = (1 : ℝ) • mwPathModeOne := by
  have h0 : (normalizedLaplacian mwPathAdj *ᵥ mwPathModeOne) 0
      = ((1 : ℝ) • mwPathModeOne) 0 := by
    rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
      mwPathE00, mwPathE01, mwPathE02]
    have hv1 : mwPathModeOne 1 = 0 := rfl
    have hv2 : mwPathModeOne 2 = -1 := rfl
    rw [hv1, hv2]
    simp only [mwPathModeOne, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Pi.smul_apply, smul_eq_mul]
    norm_num
  have h1 : (normalizedLaplacian mwPathAdj *ᵥ mwPathModeOne) 1
      = ((1 : ℝ) • mwPathModeOne) 1 := by
    rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
      mwPathE10, mwPathE11, mwPathE12]
    have hv2 : mwPathModeOne 2 = -1 := rfl
    rw [hv2]
    simp only [mwPathModeOne, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Pi.smul_apply, smul_eq_mul, mul_one, one_mul]
    ring
  have h2 : (normalizedLaplacian mwPathAdj *ᵥ mwPathModeOne) 2
      = ((1 : ℝ) • mwPathModeOne) 2 := by
    rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
      mwPathE20, mwPathE21, mwPathE22]
    have hv1 : mwPathModeOne 1 = 0 := rfl
    have hv2 : mwPathModeOne 2 = -1 := rfl
    rw [hv1, hv2]
    simp only [mwPathModeOne, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Pi.smul_apply, smul_eq_mul]
    norm_num
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The second mode `![1, -√2, 1]` is an eigenvector at eigenvalue
`2`, verified entrywise — the middle entry at `2 * -√2 = -(2 * √2)`
through `hkey`. -/
theorem mwPathAdj_normLap_modeTwo :
    normalizedLaplacian mwPathAdj *ᵥ mwPathModeTwo = (2 : ℝ) • mwPathModeTwo := by
  have hs2 : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hinv : (Real.sqrt (2 : ℝ))⁻¹ * Real.sqrt 2 = 1 :=
    inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (by norm_num))
  have hkey : (Real.sqrt (2 : ℝ))⁻¹ + (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by
    calc (Real.sqrt 2)⁻¹ + (Real.sqrt 2)⁻¹
        = 2 * (Real.sqrt 2)⁻¹ := by ring
      _ = Real.sqrt 2 * Real.sqrt 2 * (Real.sqrt 2)⁻¹ := by rw [hs2]
      _ = Real.sqrt 2 * ((Real.sqrt 2)⁻¹ * Real.sqrt 2) := by ring
      _ = Real.sqrt 2 * 1 := by rw [hinv]
      _ = Real.sqrt 2 := by ring
  have h0 : (normalizedLaplacian mwPathAdj *ᵥ mwPathModeTwo) 0
      = ((2 : ℝ) • mwPathModeTwo) 0 := by
    rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
      mwPathE00, mwPathE01, mwPathE02]
    simp only [mwPathModeTwo, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Pi.smul_apply, smul_eq_mul, mul_one, one_mul,
      zero_mul]
    linarith [hinv]
  have h1 : (normalizedLaplacian mwPathAdj *ᵥ mwPathModeTwo) 1
      = ((2 : ℝ) • mwPathModeTwo) 1 := by
    rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
      mwPathE10, mwPathE11, mwPathE12]
    have hv2 : mwPathModeTwo 2 = 1 := rfl
    rw [hv2]
    simp only [mwPathModeTwo, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Pi.smul_apply, smul_eq_mul, mul_one, one_mul]
    linarith [hkey]
  have h2 : (normalizedLaplacian mwPathAdj *ᵥ mwPathModeTwo) 2
      = ((2 : ℝ) • mwPathModeTwo) 2 := by
    have hv2 : mwPathModeTwo 2 = 1 := rfl
    rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
      mwPathE20, mwPathE21, mwPathE22, hv2]
    simp only [mwPathModeTwo, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Pi.smul_apply, smul_eq_mul, mul_one, one_mul,
      zero_mul]
    have hv2lit : (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ) 2 = 1 := rfl
    rw [hv2lit]
    linarith [hinv]
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- PSD nonnegativity read at the eigenbasis: every eigenbasis
eigenvalue of `L_sym` is nonnegative (from `normalizedLaplacian_psd`
at the basis vectors). -/
theorem mwPathAdj_eigvalOf_nonneg (i : Fin 3) :
    0 ≤ eigvalOf (normalizedLaplacian mwPathAdj)
        (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric) i := by
  have h := normalizedLaplacian_psd mwPathAdj mwPathAdj_symmetric
    mwPathAdj_nonneg mwPathAdj_pos_deg
    (eigvecOf (normalizedLaplacian mwPathAdj)
      (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric) i)
  rw [quadForm_eigvecOf_self
    (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric) i] at h
  exact h

/-- **The exact head pin `λ₁ = 0`**: the kernel witness lands an
eigenvalue at `0` (witness bridge), the first sorted entry is at most
every eigenbasis eigenvalue (`evals_first_le_eigvalOf`), and PSD
nonnegativity bounds it below through `evals_mem_eigvalOf`. -/
theorem mwPathAdj_evals_head_eq_zero :
    evals (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric)
        ⟨0, by decide⟩ = 0 := by
  have hM := normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric
  have hker : normalizedLaplacian mwPathAdj *ᵥ mwPathKerVec
      = (0 : ℝ) • mwPathKerVec := by
    rw [mwPathAdj_normLap_kernel, zero_smul]
  obtain ⟨i₀, h₀⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul hM
    mwPathKerVec_ne hker
  refine le_antisymm ?_ ?_
  · exact (evals_first_le_eigvalOf hM
        (by norm_num : 1 ≤ Fintype.card (Fin 3)) i₀).trans h₀.le
  · obtain ⟨j, hj⟩ := evals_mem_eigvalOf hM ⟨0, by decide⟩
    rw [hj]
    exact mwPathAdj_eigvalOf_nonneg j

/-- **The independent counting pin `λ₂ ≤ 1`**: the kernel witness and
the first mode land eigenvalues `0` and `1` at *distinct* eigenbasis
indices (their values differ), so at least two eigenvalues are `≤ 1`,
and the NEW order-statistics bridge `evals_le_of_card_eigvalOf_le`
gives `evals ⟨1⟩ ≤ 1`. All inputs are raw eigenvector checks; the
multiway theorem is nowhere in sight. -/
theorem mwPathAdj_secondEval_le_one :
    evals (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric)
        ⟨1, by decide⟩ ≤ 1 := by
  have hM := normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric
  have hker : normalizedLaplacian mwPathAdj *ᵥ mwPathKerVec
      = (0 : ℝ) • mwPathKerVec := by
    rw [mwPathAdj_normLap_kernel, zero_smul]
  obtain ⟨i₀, h₀⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul hM
    mwPathKerVec_ne hker
  obtain ⟨i₁, h₁⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul hM
    mwPathModeOne_ne mwPathAdj_normLap_modeOne
  have hcard : 2 ≤ (Finset.univ.filter
      (fun i => eigvalOf (normalizedLaplacian mwPathAdj) hM i ≤ 1)).card := by
    have hlt : 1 < (Finset.univ.filter
        (fun i => eigvalOf (normalizedLaplacian mwPathAdj) hM i ≤ 1)).card := by
      rw [Finset.one_lt_card_iff]
      exact ⟨i₀, i₁,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [h₀]⟩,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [h₁]⟩,
        fun h => by rw [h] at h₀; exact absurd (h₁.symm.trans h₀) (by norm_num)⟩
    omega
  exact evals_le_of_card_eigvalOf_le hM (by decide) hcard

/-- **The independent lower pin `2 ≤ λ₃`**: the second mode at
eigenvalue `2`, through the witness bridge and last-entry
domination. -/
theorem mwPathAdj_thirdEval_ge_two :
    (2 : ℝ) ≤ evals (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric)
        ⟨2, by decide⟩ :=
  evals_last_ge_of_mulVec_eq_smul
    (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric)
    (by decide) mwPathModeTwo_ne mwPathAdj_normLap_modeTwo

/-- The diagonal of `L_sym` on `P₃` is constantly `1` (degrees are
positive and the adjacency is loop-free). -/
theorem mwPathAdj_normLap_diag (i : Fin 3) :
    normalizedLaplacian mwPathAdj i i = 1 := by
  rw [mwPathAdj_entry]
  have hdiag : mwPathAdj i i = 0 := by fin_cases i <;> rfl
  rw [hdiag, mul_zero, zero_mul, sub_zero]
  simp

/-- **The trace identity exercised raw**: the sorted entries sum to the
trace `3` (`evals_sum_eq_trace`, the new sorted-API lemma), evaluated
entrywise. Load-bearing: a wrong sort, a wrong eigenbasis, or a wrong
trace def breaks it. -/
theorem mwPathAdj_evals_sum_eq_three :
    ∑ i : Fin (Fintype.card (Fin 3)),
      evals (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric) i = 3 := by
  rw [evals_sum_eq_trace
    (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric)]
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.card_fin]
  rw [Finset.sum_congr rfl fun x _ => mwPathAdj_normLap_diag x]
  norm_num

/-!
## Fixture: the four-vertex cycle `C₄`
-/

/-- Adjacency of the four-vertex cycle `0 — 1 — 2 — 3 — 0`: regular
(degree `2`), so `L_sym = I − A/2` is all-rational. -/
def mwCycleAdj : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0]

theorem mwCycleAdj_symmetric : mwCycleAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [mwCycleAdj]

theorem mwCycleAdj_nonneg : ∀ i j, 0 ≤ mwCycleAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [mwCycleAdj]

theorem mwCycleAdj_deg : ∀ i, deg mwCycleAdj i = 2 := by
  intro i
  fin_cases i <;> simp [deg, mwCycleAdj, Fin.sum_univ_four] <;> norm_num

theorem mwCycleAdj_pos_deg : ∀ i, 0 < deg mwCycleAdj i := by
  intro i
  rw [mwCycleAdj_deg]
  norm_num

theorem mwCycleAdj_vol_single : ∀ i : Fin 4, vol mwCycleAdj {i} = 2 := by
  intro i
  fin_cases i <;> simp [vol, mwCycleAdj_deg]

theorem mwCycleAdj_boundary_single : ∀ i : Fin 4, boundary mwCycleAdj {i} = 2 := by
  intro i
  rw [boundary_singleton_eq]
  fin_cases i <;> simp [deg, mwCycleAdj, Fin.sum_univ_four] <;> norm_num

/-- The alternating mode of the cycle. -/
def mwCycleVec : Fin 4 → ℝ := ![1, -1, 1, -1]

theorem mwCycleVec_ne : mwCycleVec ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [mwCycleVec] at h0

/-- The alternating mode is an eigenvector at eigenvalue `2` — the top
of the spectrum, where `A` acts at `-2` — verified entrywise from the
all-rational form `L_sym = I − A/2`. -/
theorem mwCycleAdj_normLap_alternating :
    normalizedLaplacian mwCycleAdj *ᵥ mwCycleVec = (2 : ℝ) • mwCycleVec := by
  have hs2 : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hkey : ∀ c : ℝ, (Real.sqrt (2 : ℝ))⁻¹ * c * (Real.sqrt 2)⁻¹ = c / 2 := by
    intro c
    calc (Real.sqrt (2 : ℝ))⁻¹ * c * (Real.sqrt 2)⁻¹
        = c * ((Real.sqrt (2 : ℝ))⁻¹ * (Real.sqrt 2)⁻¹) := by ring
      _ = c * ((Real.sqrt (2 : ℝ) * Real.sqrt 2)⁻¹) := by rw [mul_inv]
      _ = c * (2 : ℝ)⁻¹ := by rw [hs2]
      _ = c / 2 := by rw [div_eq_mul_inv]
  have hentry : ∀ i j : Fin 4,
      normalizedLaplacian mwCycleAdj i j
        = (if i = j then (1 : ℝ) else 0) - mwCycleAdj i j / 2 := by
    intro i j
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal, degreeInvSqrt,
      Matrix.diagonal_apply]
    rw [mwCycleAdj_deg i, mwCycleAdj_deg j, hkey]
  funext i
  fin_cases i <;>
    simp only [hentry, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_four,
      mwCycleVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul]
  all_goals
    simp [mwCycleAdj]
  all_goals norm_num

/-- **The independent lower pin `2 ≤ λ₄`**: the alternating mode
through the witness bridge. -/
theorem mwCycleAdj_fourthEval_ge_two :
    (2 : ℝ) ≤ evals (normalizedLaplacian_symmetric mwCycleAdj mwCycleAdj_symmetric)
        ⟨3, by decide⟩ :=
  evals_last_ge_of_mulVec_eq_smul
    (normalizedLaplacian_symmetric mwCycleAdj mwCycleAdj_symmetric)
    (by decide) mwCycleVec_ne mwCycleAdj_normLap_alternating

/-- The diagonal of `L_sym` on `C₄` is constantly `1`. -/
theorem mwCycleAdj_normLap_diag (i : Fin 4) :
    normalizedLaplacian mwCycleAdj i i = 1 := by
  have hdiag : mwCycleAdj i i = 0 := by fin_cases i <;> rfl
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, degreeInvSqrt,
    Matrix.diagonal_apply, mwCycleAdj_deg]
  rw [hdiag]
  simp

/-- **The trace identity exercised raw on `C₄`**: the sorted entries
sum to the trace `4`. -/
theorem mwCycleAdj_evals_sum_eq_four :
    ∑ i : Fin (Fintype.card (Fin 4)),
      evals (normalizedLaplacian_symmetric mwCycleAdj mwCycleAdj_symmetric) i = 4 := by
  rw [evals_sum_eq_trace
    (normalizedLaplacian_symmetric mwCycleAdj mwCycleAdj_symmetric)]
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.card_fin]
  rw [Finset.sum_congr rfl fun x _ => mwCycleAdj_normLap_diag x]
  norm_num

/-!
## The singleton families' ratios
-/

/-- Every singleton on `K₂` has `boundary / vol = 1 / 1`. -/
theorem mwEdgeAdj_ratio_single (i : Fin 2) :
    boundary mwEdgeAdj {i} / vol mwEdgeAdj {i} = 1 := by
  rw [mwEdgeAdj_boundary_single i, mwEdgeAdj_vol_single i]
  norm_num

/-- Every singleton on `P₃` has `boundary / vol = 1` — the middle
vertex reads `2 / 2`, the ends `1 / 1`. -/
theorem mwPathAdj_ratio_single (i : Fin 3) :
    boundary mwPathAdj {i} / vol mwPathAdj {i} = 1 := by
  rw [mwPathAdj_boundary_eq_vol_single i]
  refine div_self ?_
  intro h
  rw [mwPathAdj_vol_single i] at h
  fin_cases i <;> simp at h

/-- Every singleton on `C₄` has `boundary / vol = 2 / 2 = 1`. -/
theorem mwCycleAdj_ratio_single (i : Fin 4) :
    boundary mwCycleAdj {i} / vol mwCycleAdj {i} = 1 := by
  rw [mwCycleAdj_boundary_single i, mwCycleAdj_vol_single i]
  norm_num

/-!
## Obligation 1: `K₂`, `k = 2`, singletons — tight equality, both forms
-/

/-- The two-singleton family on `K₂`. -/
def mwEdgeSingletons : Fin 2 → Finset (Fin 2) :=
  ![{0}, {1}]

theorem mwEdgeSingletons_nonempty : ∀ i, (mwEdgeSingletons i).Nonempty := by
  intro i
  fin_cases i <;> simp [mwEdgeSingletons]

theorem mwEdgeSingletons_disjoint : ∀ i j, i ≠ j →
    Disjoint (mwEdgeSingletons i) (mwEdgeSingletons j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | simp [mwEdgeSingletons]

/-- **Obligation 1, boundary/volume form: tight equality `2 = 2·1`.**
The `≥` side is the independent raw-eigenvector pin; the `≤` side is
the theorem instance; the max is computed raw (`1/1` per part). -/
theorem mw_edge_k2_QA :
    evals (normalizedLaplacian_symmetric mwEdgeAdj mwEdgeAdj_symmetric) ⟨1, by decide⟩
      = 2 * Finset.univ.sup'
          (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
            (Finset.univ : Finset (Fin 2)).Nonempty)
          (fun i => boundary mwEdgeAdj (mwEdgeSingletons i)
            / vol mwEdgeAdj (mwEdgeSingletons i)) := by
  have hsup : Finset.univ.sup'
      (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin 2)).Nonempty)
      (fun i => boundary mwEdgeAdj (mwEdgeSingletons i)
        / vol mwEdgeAdj (mwEdgeSingletons i)) = 1 := by
    refine sup'_const (by norm_num : 0 < 2) _ 1 ?_
    intro i
    have hi : mwEdgeSingletons i = ({i} : Finset (Fin 2)) := by
      fin_cases i <;> rfl
    rw [hi]
    exact mwEdgeAdj_ratio_single i
  refine le_antisymm ?_ ?_
  · exact cheeger_upper_bound_multiway mwEdgeAdj mwEdgeAdj_symmetric
      mwEdgeAdj_nonneg mwEdgeAdj_pos_deg (by norm_num) (by decide)
      mwEdgeSingletons mwEdgeSingletons_nonempty mwEdgeSingletons_disjoint
  · rw [hsup]
    norm_num
    exact mwEdgeAdj_secondEval_ge_two

/-- The conductance of a singleton on `K₂` is `1 / min(1, 1) = 1`
(complement volume through `vol_compl` and the total volume `2`). -/
theorem mwEdgeAdj_conductance_single (i : Fin 2) :
    conductance mwEdgeAdj {i} = 1 := by
  have huniv : vol mwEdgeAdj (Finset.univ : Finset (Fin 2)) = 2 := by
    simp [vol, mwEdgeAdj_deg]
  have hcompl : vol mwEdgeAdj ({i} : Finset (Fin 2))ᶜ = 1 := by
    have h := vol_compl mwEdgeAdj ({i} : Finset (Fin 2))
    rw [mwEdgeAdj_vol_single i, huniv] at h
    linarith
  rw [conductance, mwEdgeAdj_boundary_single i, mwEdgeAdj_vol_single i,
    hcompl]
  norm_num

/-- **Obligation 1, conductance form: the same tight equality.** -/
theorem mw_edge_k2_conductance_QA :
    evals (normalizedLaplacian_symmetric mwEdgeAdj mwEdgeAdj_symmetric) ⟨1, by decide⟩
      = 2 * Finset.univ.sup'
          (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
            (Finset.univ : Finset (Fin 2)).Nonempty)
          (fun i => conductance mwEdgeAdj (mwEdgeSingletons i)) := by
  have hsup : Finset.univ.sup'
      (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin 2)).Nonempty)
      (fun i => conductance mwEdgeAdj (mwEdgeSingletons i)) = 1 := by
    refine sup'_const (by norm_num : 0 < 2) _ 1 ?_
    intro i
    have hi : mwEdgeSingletons i = ({i} : Finset (Fin 2)) := by
      fin_cases i <;> rfl
    rw [hi]
    exact mwEdgeAdj_conductance_single i
  refine le_antisymm ?_ ?_
  · exact cheeger_upper_bound_multiway_conductance mwEdgeAdj
      mwEdgeAdj_symmetric mwEdgeAdj_nonneg mwEdgeAdj_pos_deg
      (by norm_num) (by decide)
      mwEdgeSingletons mwEdgeSingletons_nonempty mwEdgeSingletons_disjoint
  · rw [hsup]
    norm_num
    exact mwEdgeAdj_secondEval_ge_two

/-!
## Obligation 2: `P₃`, `k = 2`, the non-covering family `{0}, {2}`
-/

/-- The non-covering family on `P₃`: two nonempty disjoint parts whose
union is *not* the whole vertex set (vertex `1` is in neither). -/
def mwPathEnds : Fin 2 → Finset (Fin 3) :=
  ![{0}, {2}]

theorem mwPathEnds_nonempty : ∀ i, (mwPathEnds i).Nonempty := by
  intro i
  fin_cases i <;> simp [mwPathEnds]

theorem mwPathEnds_disjoint : ∀ i j, i ≠ j →
    Disjoint (mwPathEnds i) (mwPathEnds j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | simp [mwPathEnds]

/-- **The family genuinely does not cover `V`.** Vertex `1` lies in
neither part — the every-family scope is not the partition scope. -/
theorem mwPathEnds_not_cover :
    (1 : Fin 3) ∉ mwPathEnds 0 ∪ mwPathEnds 1 := by
  simp [mwPathEnds]

/-- **Obligation 2: a non-covering family still certifies.** The
theorem instance at `{0}, {2}` reads `λ₂ ≤ 2 · max(1, 1) = 2`; the
independent counting pin (`≤ 1`, raw witnesses only) shows the
certificate is honest — a bound on the true value, obtained from a
family that is not a partition. -/
theorem mw_path_k2_noncovering_QA :
    evals (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric) ⟨1, by decide⟩
      ≤ 2 * Finset.univ.sup'
          (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
            (Finset.univ : Finset (Fin 2)).Nonempty)
          (fun i => boundary mwPathAdj (mwPathEnds i)
            / vol mwPathAdj (mwPathEnds i))
      ∧ evals (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric)
          ⟨1, by decide⟩ ≤ 1 := by
  have hsup : Finset.univ.sup'
      (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin 2)).Nonempty)
      (fun i => boundary mwPathAdj (mwPathEnds i)
        / vol mwPathAdj (mwPathEnds i)) = 1 := by
    refine sup'_const (by norm_num : 0 < 2) _ 1 ?_
    intro i
    fin_cases i <;>
      simp only [mwPathEnds, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
    · exact mwPathAdj_ratio_single 0
    · exact mwPathAdj_ratio_single 2
  refine ⟨?_, mwPathAdj_secondEval_le_one⟩
  refine le_trans (cheeger_upper_bound_multiway mwPathAdj
    mwPathAdj_symmetric mwPathAdj_nonneg mwPathAdj_pos_deg
    (by norm_num) (by decide) mwPathEnds mwPathEnds_nonempty
    mwPathEnds_disjoint) ?_
  rw [hsup]

/-!
## Obligation 3: `P₃`, `k = 3`, the singleton partition — `λ₃ = 2`
-/

/-- The singleton partition of `P₃`. -/
def mwPathSingletons : Fin 3 → Finset (Fin 3) :=
  ![{0}, {1}, {2}]

theorem mwPathSingletons_eq (i : Fin 3) :
    mwPathSingletons i = ({i} : Finset (Fin 3)) := by
  fin_cases i <;> rfl

theorem mwPathSingletons_nonempty : ∀ i, (mwPathSingletons i).Nonempty := by
  intro i
  rw [mwPathSingletons_eq]
  simp

theorem mwPathSingletons_disjoint : ∀ i j, i ≠ j →
    Disjoint (mwPathSingletons i) (mwPathSingletons j) := by
  intro i j hij
  rw [mwPathSingletons_eq, mwPathSingletons_eq]
  exact Finset.disjoint_singleton.2 hij

/-- The singleton partition's max ratio is `1`. -/
theorem mwPathSingletons_sup :
    Finset.univ.sup'
      (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin 3)).Nonempty)
      (fun i => boundary mwPathAdj (mwPathSingletons i)
        / vol mwPathAdj (mwPathSingletons i)) = 1 := by
  refine sup'_const (by norm_num : 0 < 3) _ 1 ?_
  intro i
  rw [mwPathSingletons_eq i]
  exact mwPathAdj_ratio_single i

/-- **Obligation 3: the equality `λ₃ = 2 = 2 · 1`.** The `≥` side is
the independent raw-eigenvector pin (`![1, -√2, 1]` at `2`); the `≤`
side is the theorem instance at the singleton partition. -/
theorem mw_path_k3_QA :
    evals (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric) ⟨2, by decide⟩
      = 2 * Finset.univ.sup'
          (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
            (Finset.univ : Finset (Fin 3)).Nonempty)
          (fun i => boundary mwPathAdj (mwPathSingletons i)
            / vol mwPathAdj (mwPathSingletons i)) := by
  refine le_antisymm ?_ ?_
  · exact cheeger_upper_bound_multiway mwPathAdj mwPathAdj_symmetric
      mwPathAdj_nonneg mwPathAdj_pos_deg (by norm_num) (by decide)
      mwPathSingletons mwPathSingletons_nonempty mwPathSingletons_disjoint
  · rw [mwPathSingletons_sup]
    norm_num
    exact mwPathAdj_thirdEval_ge_two

/-- **The trace cross-check.** Combining the exact pins
`λ₁ = 0` (independent) and `λ₃ = 2` (independent `≥` joined to the
theorem's `≤` at obligation 3) with the trace identity `λ₁ + λ₂ + λ₃ =
3` derives `λ₂ = 1` — in exact agreement with the independent counting
pin `λ₂ ≤ 1` (and with the pinned value in
`IrregularCheeger_QA.lean`, produced there by a sum-of-squares
argument). Three routes, one number. -/
theorem mw_path_trace_consistency :
    evals (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric) ⟨1, by decide⟩
      = 1 := by
  have hsum3 : evals (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric)
        ⟨0, by decide⟩
      + evals (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric)
        ⟨1, by decide⟩
      + evals (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric)
        ⟨2, by decide⟩ = 3 := by
    have h1 : ∑ i : Fin 3, evals
        (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric) i = 3 :=
      mwPathAdj_evals_sum_eq_three
    simp only [Fin.sum_univ_three] at h1
    exact h1
  have h3 : evals (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric)
      ⟨2, by decide⟩ = 2 := by
    rw [mw_path_k3_QA, mwPathSingletons_sup]
    norm_num
  rw [mwPathAdj_evals_head_eq_zero, h3] at hsum3
  linarith

/-!
## Obligation 4: `C₄`, `k = 4`, singletons — tight equality at `k = n`
-/

/-- The singleton partition of `C₄`. -/
def mwCycleSingletons : Fin 4 → Finset (Fin 4) :=
  ![{0}, {1}, {2}, {3}]

theorem mwCycleSingletons_eq (i : Fin 4) :
    mwCycleSingletons i = ({i} : Finset (Fin 4)) := by
  fin_cases i <;> rfl

theorem mwCycleSingletons_nonempty : ∀ i, (mwCycleSingletons i).Nonempty := by
  intro i
  rw [mwCycleSingletons_eq]
  simp

theorem mwCycleSingletons_disjoint : ∀ i j, i ≠ j →
    Disjoint (mwCycleSingletons i) (mwCycleSingletons j) := by
  intro i j hij
  rw [mwCycleSingletons_eq, mwCycleSingletons_eq]
  exact Finset.disjoint_singleton.2 hij

/-- **Obligation 4: tight equality at `k = n`.** `λ₄ = 2 = 2 · 1`:
the `≥` side is the independent raw-eigenvector pin (alternating mode),
the `≤` side is the theorem instance at the full singleton partition. -/
theorem mw_cycle_k4_QA :
    evals (normalizedLaplacian_symmetric mwCycleAdj mwCycleAdj_symmetric) ⟨3, by decide⟩
      = 2 * Finset.univ.sup'
          (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
            (Finset.univ : Finset (Fin 4)).Nonempty)
          (fun i => boundary mwCycleAdj (mwCycleSingletons i)
            / vol mwCycleAdj (mwCycleSingletons i)) := by
  have hsup : Finset.univ.sup'
      (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin 4)).Nonempty)
      (fun i => boundary mwCycleAdj (mwCycleSingletons i)
        / vol mwCycleAdj (mwCycleSingletons i)) = 1 := by
    refine sup'_const (by norm_num : 0 < 4) _ 1 ?_
    intro i
    rw [mwCycleSingletons_eq i]
    exact mwCycleAdj_ratio_single i
  refine le_antisymm ?_ ?_
  · exact cheeger_upper_bound_multiway mwCycleAdj mwCycleAdj_symmetric
      mwCycleAdj_nonneg mwCycleAdj_pos_deg (by norm_num) (by decide)
      mwCycleSingletons mwCycleSingletons_nonempty mwCycleSingletons_disjoint
  · rw [hsup]
    norm_num
    exact mwCycleAdj_fourthEval_ge_two

/-!
## Obligation 5: the `C₄` overlap fence — disjointness exercised
-/

/-- The cyclic-pair family on `C₄`: four nonempty pairs, each of
`boundary / vol = 2/4 = 1/2`, pairwise *overlapping* (each shares a
vertex with the next). -/
def mwCyclePairs : Fin 4 → Finset (Fin 4) :=
  ![{0, 1}, {1, 2}, {2, 3}, {3, 0}]

theorem mwCyclePairs_nonempty : ∀ i, (mwCyclePairs i).Nonempty := by
  intro i
  fin_cases i <;> simp [mwCyclePairs]

/-- **Disjointness provably fails**: vertex `1` lies in the first two
parts. -/
theorem mwCyclePairs_not_disjoint :
    ¬ ∀ i j, i ≠ j → Disjoint (mwCyclePairs i) (mwCyclePairs j) := by
  intro hdisj
  have h := hdisj 0 1 (by decide)
  have h1 : (1 : Fin 4) ∈ mwCyclePairs 0 ∩ mwCyclePairs 1 := by
    simp [mwCyclePairs]
  rw [Finset.disjoint_iff_inter_eq_empty.1 h] at h1
  simp at h1

/-- The volume of every cyclic pair is `2 + 2 = 4`. -/
theorem mwCyclePairs_vol (i : Fin 4) : vol mwCycleAdj (mwCyclePairs i) = 4 := by
  fin_cases i <;> simp [mwCyclePairs, vol, mwCycleAdj_deg] <;> norm_num

/-- The boundary of every cyclic pair is `2` (volume `4` minus the
pair's internal weight `2`). -/
theorem mwCyclePairs_boundary (i : Fin 4) :
    boundary mwCycleAdj (mwCyclePairs i) = 2 := by
  have hdeglit : ∀ i : Fin 4,
      deg !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0] i = 2 := by
    intro i
    fin_cases i <;> simp [deg, Fin.sum_univ_four] <;> norm_num
  rw [boundary_eq]
  fin_cases i <;>
    simp only [mwCyclePairs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    <;> simp [vol, mwCycleAdj_deg, hdeglit, mwCycleAdj]
    <;> norm_num

/-- **Obligation 5: the fence.** Every hypothesis of the headline
holds for the cyclic-pair family *except disjointness* — the parts are
nonempty, the ratios are all `1/2` (raw), the graph side holds — and
the dropped conclusion is refuted: it would read
`λ₄ ≤ 2 · (1/2) = 1`, but the independent pin gives `2 ≤ λ₄`.
Disjointness is load-bearing. -/
theorem mw_cycle_overlap_fence_QA :
    (∀ i, (mwCyclePairs i).Nonempty)
      ∧ (∀ i, boundary mwCycleAdj (mwCyclePairs i)
          / vol mwCycleAdj (mwCyclePairs i) = 1 / 2)
      ∧ 2 * Finset.univ.sup'
          (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
            (Finset.univ : Finset (Fin 4)).Nonempty)
          (fun i => boundary mwCycleAdj (mwCyclePairs i)
            / vol mwCycleAdj (mwCyclePairs i)) = 1
      ∧ ¬ (evals (normalizedLaplacian_symmetric mwCycleAdj mwCycleAdj_symmetric)
            ⟨3, by decide⟩
          ≤ 2 * Finset.univ.sup'
              (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
                (Finset.univ : Finset (Fin 4)).Nonempty)
              (fun i => boundary mwCycleAdj (mwCyclePairs i)
                / vol mwCycleAdj (mwCyclePairs i))) := by
  have hsup : Finset.univ.sup'
      (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin 4)).Nonempty)
      (fun i => boundary mwCycleAdj (mwCyclePairs i)
        / vol mwCycleAdj (mwCyclePairs i)) = 1 / 2 := by
    refine sup'_const (by norm_num : 0 < 4) _ (1 / 2) ?_
    intro i
    rw [mwCyclePairs_boundary i, mwCyclePairs_vol i]
    norm_num
  refine ⟨mwCyclePairs_nonempty, ?_, ?_, ?_⟩
  · intro i
    rw [mwCyclePairs_boundary i, mwCyclePairs_vol i]
    norm_num
  · rw [hsup]
    norm_num
  · intro hle
    rw [hsup] at hle
    have h := le_trans mwCycleAdj_fourthEval_ge_two hle
    norm_num at h

/-!
## Obligation 6: the `k = 1` edge instance
-/

/-- The one-part family on `P₃`. -/
def mwPathOne : Fin 1 → Finset (Fin 3) :=
  ![{0}]

theorem mwPathOne_nonempty : ∀ i, (mwPathOne i).Nonempty := by
  intro i
  have : i = 0 := Subsingleton.elim i 0
  subst this
  simp [mwPathOne]

theorem mwPathOne_disjoint : ∀ i j, i ≠ j →
    Disjoint (mwPathOne i) (mwPathOne j) := by
  intro i j hij
  exact absurd (Subsingleton.elim i j) hij

/-- **Obligation 6: the engine's zero-constraint edge.** At `k = 1`
the family is a single part, the subspace engine's constraint set is
empty, and the instance reads `λ₁ ≤ 2 · (boundary {0} / vol {0}) =
2 · 1`. Joined to the exact independent pin `λ₁ = 0`: both ends
pinned, `0 ≤ 2` at `k = 1`. -/
theorem mw_path_k1_QA :
    evals (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric) ⟨0, by decide⟩
      ≤ 2 * Finset.univ.sup'
          (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
            (Finset.univ : Finset (Fin 1)).Nonempty)
          (fun i => boundary mwPathAdj (mwPathOne i)
            / vol mwPathAdj (mwPathOne i))
      ∧ evals (normalizedLaplacian_symmetric mwPathAdj mwPathAdj_symmetric)
          ⟨0, by decide⟩ = 0 := by
  have hsup : Finset.univ.sup'
      (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin 1)).Nonempty)
      (fun i => boundary mwPathAdj (mwPathOne i)
        / vol mwPathAdj (mwPathOne i)) = 1 := by
    refine sup'_const (by norm_num : 0 < 1) _ 1 ?_
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [show mwPathOne 0 = ({0} : Finset (Fin 3)) from rfl]
    exact mwPathAdj_ratio_single 0
  refine ⟨?_, mwPathAdj_evals_head_eq_zero⟩
  refine le_trans (cheeger_upper_bound_multiway mwPathAdj
    mwPathAdj_symmetric mwPathAdj_nonneg mwPathAdj_pos_deg
    (by norm_num) (by decide) mwPathOne mwPathOne_nonempty
    mwPathOne_disjoint) ?_
  rw [hsup]

/-!
## Absorption tightness: the constant `2` is sharp
-/

/-- The alternating combination on `K₂`'s singleton family reads
`![1, -1]`, by the disjoint-family entry rule. -/
theorem mwEdgeCombination :
    multiwayCombination mwEdgeSingletons mwEdgeVec = mwEdgeVec := by
  funext u
  have hmemu : u ∈ mwEdgeSingletons u := by
    have hu : mwEdgeSingletons u = ({u} : Finset (Fin 2)) := by
      fin_cases u <;> rfl
    rw [hu]; simp
  have hzero : ∀ b ∈ (Finset.univ : Finset (Fin 2)), b ≠ u →
      (@ite _ (u ∈ mwEdgeSingletons b) (Classical.propDecidable _)
        (mwEdgeVec b) 0) = 0 := by
    intro b _ hbu
    rw [if_neg]
    intro hmem
    have hub : mwEdgeSingletons b = ({b} : Finset (Fin 2)) := by
      fin_cases b <;> rfl
    rw [hub] at hmem
    simp only [Finset.mem_singleton] at hmem
    exact hbu hmem.symm
  rw [multiwayCombination, Finset.sum_eq_single u]
  · rw [if_pos hmemu]
  · exact hzero
  · intro hnu
    exact absurd (Finset.mem_univ u) hnu

/-- **Absorption equality on `K₂`.** The cross-part absorption lemma
holds with *equality* at the alternating combination: the raw Dirichlet
energy is `4` (each ordered crossing pair contributes `2² = 4`), and
the bound's right side is `2 · (1 + 1) = 4`. The theorem's constant
`2` is attained — a falsifiability anchor for the absorption lemma's
tightness: a wrong constant, a wrong boundary, or a wrong combination
rule breaks the pin. -/
theorem mw_edge_absorption_eq :
    quadForm (laplacian mwEdgeAdj) (multiwayCombination mwEdgeSingletons mwEdgeVec)
      = 2 * ∑ i : Fin 2, mwEdgeVec i ^ 2 * boundary mwEdgeAdj (mwEdgeSingletons i) := by
  have hb : ∀ i : Fin 2, boundary mwEdgeAdj (mwEdgeSingletons i) = 1 := by
    intro i
    have hi : mwEdgeSingletons i = ({i} : Finset (Fin 2)) := by
      fin_cases i <;> rfl
    rw [hi]
    exact mwEdgeAdj_boundary_single i
  rw [mwEdgeCombination, laplacian_quadForm mwEdgeAdj mwEdgeAdj_symmetric mwEdgeVec]
  have hsum : (∑ u : Fin 2, ∑ v : Fin 2, mwEdgeAdj u v
      * (mwEdgeVec u - mwEdgeVec v) ^ 2) = 8 := by
    simp only [Fin.sum_univ_two, mwEdgeAdj, mwEdgeVec,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    norm_num
  rw [hsum]
  simp only [Fin.sum_univ_two, mwEdgeVec, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, hb]
  norm_num

/-- The alternating combination on `C₄`'s singleton family reads
`![1, -1, 1, -1]`. -/
def mwCycleAlt : Fin 4 → ℝ := ![1, -1, 1, -1]

theorem mwCycleCombination :
    multiwayCombination mwCycleSingletons mwCycleAlt = mwCycleAlt := by
  funext u
  have hmemu : u ∈ mwCycleSingletons u := by
    rw [mwCycleSingletons_eq]; simp
  have hzero : ∀ b ∈ (Finset.univ : Finset (Fin 4)), b ≠ u →
      (@ite _ (u ∈ mwCycleSingletons b) (Classical.propDecidable _)
        (mwCycleAlt b) 0) = 0 := by
    intro b _ hbu
    rw [if_neg]
    intro hmem
    have hub : mwCycleSingletons b = ({b} : Finset (Fin 4)) :=
      mwCycleSingletons_eq b
    rw [hub] at hmem
    simp only [Finset.mem_singleton] at hmem
    exact hbu hmem.symm
  rw [multiwayCombination, Finset.sum_eq_single u]
  · rw [if_pos hmemu]
  · exact hzero
  · intro hnu
    exact absurd (Finset.mem_univ u) hnu

/-- **Absorption equality on `C₄`.** At the alternating combination
the raw Dirichlet energy is `16` (eight ordered crossing pairs at
`2² = 4` each) and the bound's right side is `2 · 4 · 2 = 16`:
equality. This is the mechanism behind the `k = 4` headline equality —
the absorption is tight exactly at the top mode. -/
theorem mw_cycle_absorption_eq :
    quadForm (laplacian mwCycleAdj) (multiwayCombination mwCycleSingletons mwCycleAlt)
      = 2 * ∑ i : Fin 4, mwCycleAlt i ^ 2 * boundary mwCycleAdj (mwCycleSingletons i) := by
  have hb : ∀ i : Fin 4, boundary mwCycleAdj (mwCycleSingletons i) = 2 := by
    intro i
    rw [mwCycleSingletons_eq i]
    exact mwCycleAdj_boundary_single i
  rw [mwCycleCombination,
    laplacian_quadForm mwCycleAdj mwCycleAdj_symmetric mwCycleAlt]
  have hsum : (∑ u : Fin 4, ∑ v : Fin 4, mwCycleAdj u v
      * (mwCycleAlt u - mwCycleAlt v) ^ 2) = 32 := by
    simp only [Fin.sum_univ_four, mwCycleAdj, mwCycleAlt,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    norm_num
  rw [hsum]
  simp only [Fin.sum_univ_four, mwCycleAlt, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, hb]
  norm_num

/-- **The per-part energy identity pinned raw on `C₄`.** The Dirichlet
energy of the plain indicator of `{0}` computes to `2` by hand, and
`boundary {0} = 2` independently — the identity
`quadForm_laplacian_partIndicator` therefore holds at an object where
both sides are hand-checkable; a wrong indicator definition or a wrong
boundary definition breaks the join. -/
theorem mw_cycle_partIndicator_QA :
    quadForm (laplacian mwCycleAdj) (partIndicator ({0} : Finset (Fin 4))) = 2
      ∧ boundary mwCycleAdj ({0} : Finset (Fin 4)) = 2 := by
  refine ⟨?_, mwCycleAdj_boundary_single 0⟩
  have hentry : ∀ u : Fin 4, partIndicator ({0} : Finset (Fin 4)) u
      = if u = 0 then (1 : ℝ) else 0 := by
    intro u
    by_cases h : u ∈ ({0} : Finset (Fin 4))
    · rw [partIndicator_of_mem h, if_pos (Finset.mem_singleton.1 h)]
    · have hne : u ≠ 0 := by
        intro heq
        apply h
        rw [heq]
        exact Finset.mem_singleton_self 0
      rw [partIndicator_of_not_mem h, if_neg hne]
  rw [laplacian_quadForm mwCycleAdj mwCycleAdj_symmetric]
  simp only [hentry, Fin.sum_univ_four, mwCycleAdj, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  simp
  norm_num

/-!
## The ρ_k packaging: partition instances, exact minima, and the junk fence
-/

/-- The shared entry formula for `L_sym` on `C₄`: degrees are `2`, so
the off-diagonal scaling is `/ 2`. -/
private theorem mwCycle_entry (i j : Fin 4) :
    normalizedLaplacian mwCycleAdj i j
      = (if i = j then (1 : ℝ) else 0) - mwCycleAdj i j / 2 := by
  have hs2 : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hkey : ∀ c : ℝ, (Real.sqrt (2 : ℝ))⁻¹ * c * (Real.sqrt 2)⁻¹ = c / 2 := by
    intro c
    calc (Real.sqrt (2 : ℝ))⁻¹ * c * (Real.sqrt 2)⁻¹
        = c * ((Real.sqrt (2 : ℝ))⁻¹ * (Real.sqrt 2)⁻¹) := by ring
      _ = c * ((Real.sqrt (2 : ℝ) * Real.sqrt 2)⁻¹) := by rw [mul_inv]
      _ = c * (2 : ℝ)⁻¹ := by rw [hs2]
      _ = c / 2 := by rw [div_eq_mul_inv]
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, degreeInvSqrt,
    Matrix.diagonal_apply]
  rw [mwCycleAdj_deg i, mwCycleAdj_deg j, hkey]

/-- The mode `![1, 0, -1, 0]` of the cycle, an eigenvector at
eigenvalue `1` (the adjacency acts at `0` on it). -/
def mwCycleModeOne : Fin 4 → ℝ := ![1, 0, -1, 0]

theorem mwCycleModeOne_ne : mwCycleModeOne ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [mwCycleModeOne] at h0

/-- The mode `![1, 0, -1, 0]` is an eigenvector of `L_sym` at
eigenvalue `1`, verified entrywise from the all-rational form
`L_sym = I − A/2`. -/
theorem mwCycleAdj_normLap_modeOne :
    normalizedLaplacian mwCycleAdj *ᵥ mwCycleModeOne = (1 : ℝ) • mwCycleModeOne := by
  funext i
  fin_cases i <;>
    simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_four,
      mwCycle_entry, mwCycleModeOne, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Pi.smul_apply, smul_eq_mul]
  all_goals simp [mwCycleAdj]

/-- **The independent pin `λ₂ (L_sym C₄) ≤ 1`.** The kernel witness
`√D · 1` (eigenvalue `0`, through the shelf supplier) and the mode at
`1` land at *distinct* eigenbasis indices (their values differ), so at
least two eigenvalues are `≤ 1`, and the counting bridge gives the
second sorted entry `≤ 1`. Raw eigenvector checks only; the multiway
family is nowhere in sight. -/
theorem mwCycleAdj_secondEval_le_one :
    evals (normalizedLaplacian_symmetric mwCycleAdj mwCycleAdj_symmetric)
        ⟨1, by decide⟩ ≤ 1 := by
  have hM := normalizedLaplacian_symmetric mwCycleAdj mwCycleAdj_symmetric
  have hkne : degreeSqrt mwCycleAdj *ᵥ (onesVec : Fin 4 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp only [degreeSqrt_mulVec_apply, mwCycleAdj_deg, onesVec,
      Pi.zero_apply] at h0
    norm_num at h0
  have hker : normalizedLaplacian mwCycleAdj *ᵥ
      (degreeSqrt mwCycleAdj *ᵥ (onesVec : Fin 4 → ℝ)) = (0 : ℝ) •
      (degreeSqrt mwCycleAdj *ᵥ (onesVec : Fin 4 → ℝ)) := by
    rw [normalizedLaplacian_mulVec_degreeSqrt_onesVec mwCycleAdj
      mwCycleAdj_pos_deg, zero_smul]
  obtain ⟨i₀, h₀⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul hM hkne hker
  obtain ⟨i₁, h₁⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul hM
    mwCycleModeOne_ne mwCycleAdj_normLap_modeOne
  have hcard : 2 ≤ (Finset.univ.filter
      (fun i => eigvalOf (normalizedLaplacian mwCycleAdj) hM i ≤ 1)).card := by
    have hlt : 1 < (Finset.univ.filter
        (fun i => eigvalOf (normalizedLaplacian mwCycleAdj) hM i ≤ 1)).card := by
      rw [Finset.one_lt_card_iff]
      exact ⟨i₀, i₁,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [h₀]⟩,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [h₁]⟩,
        fun h => by rw [h] at h₀; exact absurd (h₁.symm.trans h₀) (by norm_num)⟩
    omega
  exact evals_le_of_card_eigvalOf_le hM (by decide) hcard

/-- **The quadratic-form identity on `C₄`.** `xᵀ L_sym x = ∑ xᵢ² −
(x₀+x₂)(x₁+x₃)` — the entrywise expansion of `I − A/2` against the
cycle's adjacency; at degree-weighted zero sum the cross term becomes
`−(x₀+x₂)²`, the sum-of-squares supplier for the lower pin. -/
private theorem mwCycle_quadForm (x : Fin 4 → ℝ) :
    quadForm (normalizedLaplacian mwCycleAdj) x
      = x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3
          - (x 0 + x 2) * (x 1 + x 3) := by
  simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_four,
    mwCycle_entry]
  simp [mwCycleAdj]
  ring

/-- **The independent pin `1 ≤ λ₂ (L_sym C₄)`.** The sInf engine at the
kernel vector `√D · 1`: every degree-weighted-zero-sum vector has
`quadForm = ‖x‖² + (x₀+x₂)² ≥ ‖x‖²` (the sum-of-squares above), so
every constraint-set Rayleigh quotient is `≥ 1`; nonemptiness witnessed
by the mode at Rayleigh exactly `1`. -/
theorem mwCycleAdj_secondEval_ge_one :
    1 ≤ secondEval (normalizedLaplacian mwCycleAdj)
        (normalizedLaplacian_symmetric mwCycleAdj mwCycleAdj_symmetric)
        (by decide : 2 ≤ Fintype.card (Fin 4)) := by
  have hkne : degreeSqrt mwCycleAdj *ᵥ (onesVec : Fin 4 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp only [degreeSqrt_mulVec_apply, mwCycleAdj_deg, onesVec,
      Pi.zero_apply] at h0
    norm_num at h0
  rw [secondEval_variational_of_ker
    (normalizedLaplacian_symmetric mwCycleAdj mwCycleAdj_symmetric)
    (normalizedLaplacian_psd mwCycleAdj mwCycleAdj_symmetric
      mwCycleAdj_nonneg mwCycleAdj_pos_deg)
    hkne
    (normalizedLaplacian_mulVec_degreeSqrt_onesVec mwCycleAdj
      mwCycleAdj_pos_deg)
    (by decide)]
  refine le_csInf ?_ ?_
  · refine ⟨1, mwCycleModeOne, mwCycleModeOne_ne, ?_, ?_⟩
    · simp only [Matrix.dotProduct, degreeSqrt_mulVec_apply, mwCycleAdj_deg,
        onesVec, mul_one, Fin.sum_univ_four, mwCycleModeOne,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      norm_num
    · have hq : quadForm (normalizedLaplacian mwCycleAdj) mwCycleModeOne
          = Matrix.dotProduct mwCycleModeOne mwCycleModeOne := by
        rw [quadForm, mwCycleAdj_normLap_modeOne, Matrix.dotProduct_smul,
          smul_eq_mul, one_mul]
      have hd : Matrix.dotProduct mwCycleModeOne mwCycleModeOne = 2 := by
        simp [Matrix.dotProduct, Fin.sum_univ_four, mwCycleModeOne]
        norm_num
      rw [rayleigh, if_neg mwCycleModeOne_ne, hq, hd]
      norm_num
  · rintro r ⟨x, hx0, hxorth, hxr⟩
    have hc : x 0 + x 1 + x 2 + x 3 = 0 := by
      simp only [Matrix.dotProduct, degreeSqrt_mulVec_apply, mwCycleAdj_deg,
        onesVec, mul_one, Fin.sum_univ_four] at hxorth
      rcases mul_eq_zero.1 (show (x 0 + x 1 + x 2 + x 3) * Real.sqrt (2 : ℝ)
          = 0 by linear_combination hxorth) with h | h
      · exact h
      · exact absurd h (Real.sqrt_ne_zero'.mpr (by norm_num))
    have hdp : 0 < Matrix.dotProduct x x := by
      obtain ⟨i, hi⟩ : ∃ i : Fin 4, x i ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hx0 (funext hcon)
      have h1 : ∀ j ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ x j * x j :=
        fun j _ => mul_self_nonneg (x j)
      have h2 : 0 < x i * x i := mul_self_pos.2 hi
      simpa [Matrix.dotProduct] using
        Finset.sum_pos' h1 ⟨i, Finset.mem_univ i, h2⟩
    have hdpe : Matrix.dotProduct x x
        = x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 := by
      simp [Matrix.dotProduct, Fin.sum_univ_four]
    have hcross : (x 0 + x 2) * (x 1 + x 3) = -(x 0 + x 2) * (x 0 + x 2) := by
      have h13 : x 1 + x 3 = -(x 0 + x 2) := by linarith
      rw [h13]
      ring
    rw [← hxr, rayleigh, if_neg hx0, mwCycle_quadForm, hcross,
      le_div_iff₀ hdp]
    nlinarith [sq_nonneg (x 0 + x 2)]

/-- **The exact pin: `λ₂ (L_sym C₄) = 1`.** Both sides independent of
the multiway family — the counting bridge at two raw eigenvectors for
`≤ 1`, the `(x₀+x₂)²` sum-of-squares for `≥ 1`. This pin is the join
partner that makes the ρ₂(C₄) instance below a forced equality. -/
theorem mwCycleAdj_secondEval_eq_one :
    secondEval (normalizedLaplacian mwCycleAdj)
        (normalizedLaplacian_symmetric mwCycleAdj mwCycleAdj_symmetric)
        (by decide : 2 ≤ Fintype.card (Fin 4)) = 1 :=
  le_antisymm mwCycleAdj_secondEval_le_one mwCycleAdj_secondEval_ge_one

/-- The adjacent-pair partition of `C₄`: `{0,1}, {2,3}`. -/
def mwCycleAdjPairs : Fin 2 → Finset (Fin 4) :=
  ![{0, 1}, {2, 3}]

theorem mwCycleAdjPairs_isPartition :
    IsMultiwayPartition mwCycleAdjPairs := by
  refine ⟨fun i => ?_, ?_, ?_⟩
  · fin_cases i <;> simp [mwCycleAdjPairs]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | simp [mwCycleAdjPairs]
  · intro v
    fin_cases v
    · exact ⟨0, by simp [mwCycleAdjPairs]⟩
    · exact ⟨0, by simp [mwCycleAdjPairs]⟩
    · exact ⟨1, by simp [mwCycleAdjPairs]⟩
    · exact ⟨1, by simp [mwCycleAdjPairs]⟩

theorem mwCycleAdj_vol_univ :
    vol mwCycleAdj (Finset.univ : Finset (Fin 4)) = 8 := by
  simp [vol, mwCycleAdj_deg]
  norm_num

/-- Both adjacent pairs have conductance `2 / min(4, 4) = 1/2` — the
boundary/volume pins are the cyclic-pair family's (both families share
the sets `{0,1}` and `{2,3}`). -/
theorem mwCycleAdj_conductance_adjPair (i : Fin 2) :
    conductance mwCycleAdj (mwCycleAdjPairs i) = 1 / 2 := by
  have hb : ∀ i : Fin 2, boundary mwCycleAdj (mwCycleAdjPairs i) = 2 := by
    intro i
    have hp0 : boundary mwCycleAdj ({0, 1} : Finset (Fin 4)) = 2 :=
      mwCyclePairs_boundary 0
    have hp2 : boundary mwCycleAdj ({2, 3} : Finset (Fin 4)) = 2 :=
      mwCyclePairs_boundary 2
    fin_cases i
    · exact hp0
    · exact hp2
  have hv : ∀ i : Fin 2, vol mwCycleAdj (mwCycleAdjPairs i) = 4 := by
    intro i
    have hp0 : vol mwCycleAdj ({0, 1} : Finset (Fin 4)) = 4 :=
      mwCyclePairs_vol 0
    have hp2 : vol mwCycleAdj ({2, 3} : Finset (Fin 4)) = 4 :=
      mwCyclePairs_vol 2
    fin_cases i
    · exact hp0
    · exact hp2
  have hvc : ∀ i : Fin 2, vol mwCycleAdj (mwCycleAdjPairs i)ᶜ = 4 := by
    intro i
    have h := vol_compl mwCycleAdj (mwCycleAdjPairs i)
    rw [hv i, mwCycleAdj_vol_univ] at h
    linarith
  rw [conductance, hb i, hv i, hvc i]
  norm_num

theorem mwCycleAdjPairs_maxConductance :
    maxPartConductance mwCycleAdj mwCycleAdjPairs = 1 / 2 :=
  maxPartConductance_const (by norm_num) mwCycleAdj_conductance_adjPair

/-- **The star instance: `ρ₂(C₄) = 1/2` exactly.** The `≤` side is the
adjacent-pair witness; the `≥` side is *forced by the theorem* joined
to the independently pinned `λ₂ = 1` — a broken attainment (a junk
`sInf`), a wrong constant, or a wrong minimum would break the
equality. Attainment is exercised, not decorated. -/
theorem mw_cycle_rho_two_eq_half :
    multiwayExpansion mwCycleAdj 2 = 1 / 2 := by
  refine le_antisymm ?_ ?_
  · exact (multiwayExpansion_le mwCycleAdj mwCycleAdjPairs_isPartition).trans
      (le_of_eq mwCycleAdjPairs_maxConductance)
  · have h := cheeger_upper_bound_multiway_rhoK mwCycleAdj
      mwCycleAdj_symmetric mwCycleAdj_nonneg mwCycleAdj_pos_deg
      (by norm_num) (by decide) ⟨mwCycleAdjPairs, mwCycleAdjPairs_isPartition⟩
    have hev : evals (normalizedLaplacian_symmetric mwCycleAdj
        mwCycleAdj_symmetric) ⟨1, by decide⟩ = 1 :=
      mwCycleAdj_secondEval_eq_one
    rw [hev] at h
    linarith

/-- The diagonal partition of `C₄`, whose maximum part conductance is
`1`: the packaged minimum provably optimizes below it. -/
def mwCycleDiagPairs : Fin 2 → Finset (Fin 4) :=
  ![{0, 2}, {1, 3}]

theorem mwCycleDiagPairs_isPartition :
    IsMultiwayPartition mwCycleDiagPairs := by
  refine ⟨fun i => ?_, ?_, ?_⟩
  · fin_cases i <;> simp [mwCycleDiagPairs]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | simp [mwCycleDiagPairs]
  · intro v
    fin_cases v
    · exact ⟨0, by simp [mwCycleDiagPairs]⟩
    · exact ⟨1, by simp [mwCycleDiagPairs]⟩
    · exact ⟨0, by simp [mwCycleDiagPairs]⟩
    · exact ⟨1, by simp [mwCycleDiagPairs]⟩

/-- Both diagonal pairs have conductance `4 / min(4, 4) = 1`. -/
theorem mwCycleDiagPairs_conductance (i : Fin 2) :
    conductance mwCycleAdj (mwCycleDiagPairs i) = 1 := by
  have hset : ∀ i : Fin 2, mwCycleDiagPairs i = ({0, 2} : Finset (Fin 4)) ∨
      mwCycleDiagPairs i = ({1, 3} : Finset (Fin 4)) := by
    intro i
    fin_cases i <;> simp [mwCycleDiagPairs]
  have hbd : ∀ i : Fin 2, boundary mwCycleAdj (mwCycleDiagPairs i) = 4 := by
    intro i
    rw [boundary_eq]
    have hdeglit : ∀ i : Fin 4,
        deg !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0] i = 2 := by
      intro i
      fin_cases i <;> simp [deg, Fin.sum_univ_four] <;> norm_num
    rcases hset i with h | h <;> rw [h] <;>
      simp [vol, mwCycleAdj_deg, hdeglit, mwCycleAdj] <;> norm_num
  have hv : ∀ i : Fin 2, vol mwCycleAdj (mwCycleDiagPairs i) = 4 := by
    intro i
    rcases hset i with h | h <;> rw [h] <;>
      simp [vol, mwCycleAdj_deg] <;> norm_num
  have hvc : ∀ i : Fin 2, vol mwCycleAdj (mwCycleDiagPairs i)ᶜ = 4 := by
    intro i
    have h := vol_compl mwCycleAdj (mwCycleDiagPairs i)
    rw [hv i, mwCycleAdj_vol_univ] at h
    linarith
  rw [conductance, hbd i, hv i, hvc i]
  norm_num

/-- **The minimum is not vacuous: ρ₂ beats this partition.**
`ρ₂(C₄) = 1/2 < 1 = maxPartConductance` at the diagonal partition —
the packaged minimum genuinely optimizes over the partition space
(the diagonal cut's own certificate is strictly worse). -/
theorem mw_cycle_rho_beats_diagonal :
    multiwayExpansion mwCycleAdj 2 = 1 / 2 ∧
      maxPartConductance mwCycleAdj mwCycleDiagPairs = 1 ∧ 1 / 2 < 1 :=
  ⟨mw_cycle_rho_two_eq_half,
    maxPartConductance_const (by norm_num) mwCycleDiagPairs_conductance,
    by norm_num⟩

/-- The singleton partition of `K₂` *is* a partition (it covers). -/
theorem mwEdgeSingletons_isPartition :
    IsMultiwayPartition mwEdgeSingletons := by
  refine ⟨fun i => ?_, ?_, ?_⟩
  · exact mwEdgeSingletons_nonempty i
  · intro i j hij
    exact mwEdgeSingletons_disjoint i j hij
  · intro v
    have hv : mwEdgeSingletons v = ({v} : Finset (Fin 2)) := by
      fin_cases v <;> rfl
    refine ⟨v, ?_⟩
    rw [hv]; simp

/-- **The K₂ instance: `ρ₂ = 1` exactly.** The `≤` side is the
singleton witness; the `≥` side is forced by the theorem joined to the
independent raw-eigenvector pin `2 ≤ λ₂`. -/
theorem mw_edge_rho_two_eq_one :
    multiwayExpansion mwEdgeAdj 2 = 1 := by
  refine le_antisymm ?_ ?_
  · exact (multiwayExpansion_le mwEdgeAdj mwEdgeSingletons_isPartition).trans
      (le_of_eq (maxPartConductance_const (by norm_num)
        (fun i => by
          have hi : mwEdgeSingletons i = ({i} : Finset (Fin 2)) := by
            fin_cases i <;> rfl
          rw [hi]
          exact mwEdgeAdj_conductance_single i)))
  · have h := cheeger_upper_bound_multiway_rhoK mwEdgeAdj
      mwEdgeAdj_symmetric mwEdgeAdj_nonneg mwEdgeAdj_pos_deg
      (by norm_num) (by decide) ⟨mwEdgeSingletons, mwEdgeSingletons_isPartition⟩
    have hev : (2 : ℝ) ≤ evals (normalizedLaplacian_symmetric mwEdgeAdj
        mwEdgeAdj_symmetric) ⟨1, by decide⟩ := mwEdgeAdj_secondEval_ge_two
    linarith

theorem mwPathAdj_vol_univ :
    vol mwPathAdj (Finset.univ : Finset (Fin 3)) = 4 := by
  have h0 : deg mwPathAdj (0 : Fin 3) = 1 := by simp [mwPathAdj_deg]
  have h1 : deg mwPathAdj (1 : Fin 3) = 2 := by simp [mwPathAdj_deg]
  have h2 : deg mwPathAdj (2 : Fin 3) = 1 := by simp [mwPathAdj_deg]
  simp only [vol, Fin.sum_univ_three, h0, h1, h2]
  norm_num

/-- Every singleton on `P₃` has conductance `1` — the middle vertex
`2/min(2,2)`, the ends `1/min(1,3)`. -/
theorem mwPathAdj_conductance_single (i : Fin 3) :
    conductance mwPathAdj {i} = 1 := by
  have hv : vol mwPathAdj {i} = if i = 1 then 2 else 1 := mwPathAdj_vol_single i
  have hb : boundary mwPathAdj {i} = vol mwPathAdj {i} :=
    mwPathAdj_boundary_eq_vol_single i
  have hv4 : vol mwPathAdj {i} + vol mwPathAdj ({i} : Finset (Fin 3))ᶜ = 4 := by
    have h := vol_compl mwPathAdj ({i} : Finset (Fin 3))
    rw [mwPathAdj_vol_univ] at h
    linarith
  rw [conductance, hb]
  by_cases hi : i = 1
  · subst hi
    have hv1 : vol mwPathAdj ({1} : Finset (Fin 3)) = 2 := by
      have h1 := mwPathAdj_vol_single 1; simpa using h1
    rw [hv1]
    have hc1 : vol mwPathAdj ({1} : Finset (Fin 3))ᶜ = 2 := by linarith
    rw [hc1]
    norm_num
  · have hv2 : vol mwPathAdj {i} = 1 := by rw [hv, if_neg hi]
    rw [hv2]
    have hc3 : vol mwPathAdj ({i} : Finset (Fin 3))ᶜ = 3 := by linarith
    rw [hc3]
    norm_num

/-- The singleton partition of `P₃` is a partition (it covers). -/
theorem mwPathSingletons_isPartition :
    IsMultiwayPartition mwPathSingletons := by
  refine ⟨fun i => ?_, ?_, ?_⟩
  · exact mwPathSingletons_nonempty i
  · intro i j hij
    exact mwPathSingletons_disjoint i j hij
  · intro v
    have hv : mwPathSingletons v = ({v} : Finset (Fin 3)) := by
      rw [mwPathSingletons_eq]
    refine ⟨v, ?_⟩
    rw [hv]; simp

/-- **The P₃ instance: `ρ₃ = 1` exactly.** The `≤` side is the
singleton witness; the `≥` side is forced by the theorem joined to the
independently pinned `λ₃ = 2` (obligation 3's raw eigenvector pin). -/
theorem mw_path_rho_three_eq_one :
    multiwayExpansion mwPathAdj 3 = 1 := by
  refine le_antisymm ?_ ?_
  · exact (multiwayExpansion_le mwPathAdj mwPathSingletons_isPartition).trans
      (le_of_eq (maxPartConductance_const (by norm_num)
        (fun i => by
          rw [mwPathSingletons_eq i]
          exact mwPathAdj_conductance_single i)))
  · have h := cheeger_upper_bound_multiway_rhoK mwPathAdj
      mwPathAdj_symmetric mwPathAdj_nonneg mwPathAdj_pos_deg
      (by norm_num) (by decide) ⟨mwPathSingletons, mwPathSingletons_isPartition⟩
    have hev : evals (normalizedLaplacian_symmetric mwPathAdj
        mwPathAdj_symmetric) ⟨2, by decide⟩ = 2 := by
      rw [mw_path_k3_QA, mwPathSingletons_sup]
      norm_num
    rw [hev] at h
    linarith

/-- **No three nonempty pairwise-disjoint parts fit in two vertices.**
Choosing a point from each part gives an injection `Fin 3 ↪ Fin 2`,
contradicting the cardinalities — the partition space at `k = 3` on
`K₂` is provably empty. -/
theorem mw_no_three_partition_on_edge (S : Fin 3 → Finset (Fin 2))
    (hne : ∀ i, (S i).Nonempty) (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    False := by
  classical
  choose u hu using fun i => hne i
  have hinj : Function.Injective u := by
    intro i j huij
    by_contra hne'
    have h1 : u j ∈ S i := by rw [← huij]; exact hu i
    have hint : u j ∈ S i ∩ S j := Finset.mem_inter.2 ⟨h1, hu j⟩
    rw [Finset.disjoint_iff_inter_eq_empty.1 (hdisj i j hne')] at hint
    simp at hint
  have hcard : Fintype.card (Fin 3) ≤ Fintype.card (Fin 2) :=
    Fintype.card_le_of_injective u hinj
  norm_num at hcard

/-- **The empty-set junk fence.** With `k = 3 > 2 = card V` the
partition space is empty and `ρ₃` is the `sInf ∅ = 0` junk value (the
same convention the `subgaussian` repair documents): the
partition-existence hypothesis of the ρ_k statements is load-bearing,
not decorative. -/
theorem mw_edge_rho_three_eq_zero :
    multiwayExpansion mwEdgeAdj 3 = 0 := by
  have hempty : {m : ℝ | ∃ S : Fin 3 → Finset (Fin 2), IsMultiwayPartition S ∧
      maxPartConductance mwEdgeAdj S = m} = ∅ := by
    refine Set.eq_empty_iff_forall_not_mem.2 ?_
    rintro m ⟨S, hp, -⟩
    exact mw_no_three_partition_on_edge S hp.nonempty hp.disjoint
  rw [multiwayExpansion, hempty, Real.sInf_empty]

/-- The existence supplier instantiates on concrete input with no side
conditions (`3 ≤ 4` on `C₄`) — the `hex` hypothesis of the ρ_k
statements is dischargeable at `k ≤ card V`. -/
theorem mw_supplier_instance_QA :
    ∃ S : Fin 3 → Finset (Fin 4), IsMultiwayPartition S :=
  exists_isMultiwayPartition_of_le_card (by norm_num) (by decide)

end SpectralGraphTheory.MultiwayQA
