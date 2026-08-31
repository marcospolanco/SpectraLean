/-
  Poincare.lean

  The Poincaré inequality for graph Laplacians, in both the
  combinatorial and the normalized (degree-weighted, π-measure) forms,
  plus its cut-level consumer: the spectral edge-expansion bound
  `λ₂ · |S| · (|V| − |S|)/|V| ≤ boundary A S`.

  Delivered 2026-08-31 by `proposals/poincare-inequality.md`
  (same-run proposal + delivery), closing the SGT radar's axis-3 named
  absent category "Poincaré" (log-Sobolev remains the axis's named
  gap). Zero axioms: every statement here is a corollary of proved
  shelf engines — `secondEval_le_rayleigh` (the onesVec-kernel Rayleigh
  lower bound), `secondEval_le_rayleigh_of_ker` (the general-kernel
  form), the congruence `√D L_sym √D = laplacian A`, the kernel
  membership `√D · 1 ∈ ker L_sym`, and `Multiway.lean`'s indicator
  energy identity `quadForm_laplacian_partIndicator`.

  Named consumers (the proposal's leverage case):

  - the mixing program (`GraphTheory.Mixing`): the delivered ℓ²(π)
    contraction under a hypothesis-shaped rate is Poincaré in walk
    form; the normalized statement here is stated in the mixing
    program's own degree-weighted idiom so it composes with
    `stationaryVec`-style interfaces without measure theory;
  - the heat-semigroup family (`GraphTheory.Heat`): eigenmode decay is
    delivered; variance decay under `e^{-tL}` is the priced follow-on
    this inequality feeds (named in the proposal, not delivered);
  - `spectral_gap_edge_expansion` below: the linear-in-λ₂,
    set-by-set edge expansion bound — a shape the Cheeger family does
    not carry (Cheeger's lower bound is quadratic in the conductance;
    this is linear in the gap, needs no sweep, no median, no
    regularity) — and `Multiway.lean`'s indicator identity's first
    consumer outside its own module.

  Statement-shape provenance (no statement is *admitted* on these —
  everything is proved, so these citations locate the classical
  shapes, they are not trust boundaries): Chung, *Spectral Graph
  Theory* (1997) §1.3 (the normalized form for connected graphs) and
  Levin–Peres–Wilmer, *Markov Chains and Mixing Times* (2009), Ch. 12
  (the π-form for reversible chains). Page-level locators stay
  unconfirmed per the standing locator rule.
-/

import Scaffold.Mathlib.GraphTheory.Spectral
import Scaffold.Mathlib.GraphTheory.Electrical
import Scaffold.Mathlib.GraphTheory.Normalized
import Scaffold.Mathlib.GraphTheory.VariationalTransfer
import Scaffold.Mathlib.GraphTheory.Multiway
import Scaffold.Mathlib.GraphTheory.Fiedler

open scoped BigOperators Matrix

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Centering invariance of the Dirichlet energy.** The all-ones
vector is in every Laplacian's kernel, so subtracting a constant from a
function does not change its energy: the mixed term vanishes against
the row-sum identity and the constant's own energy is zero. -/
theorem quadForm_laplacian_sub_const (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (f : V → ℝ) (c : ℝ) :
    quadForm (laplacian A) (f - c • onesVec) = quadForm (laplacian A) f := by
  have hq : quadForm (laplacian A) onesVec = 0 := by
    simp only [quadForm, laplacian_ones_in_kernel A, Matrix.dotProduct_zero]
  rw [quadForm_laplacian_sub_smul A hA f onesVec c,
    laplacian_ones_in_kernel A, Matrix.dotProduct_zero, hq]
  ring

/-- **The Poincaré inequality, engine (division-free) form.** For every
symmetric nonnegative adjacency matrix and every function `f`, the
variance of `f` around its mean is controlled by its Dirichlet energy at
the second sorted Laplacian eigenvalue:

`λ₂ (laplacian A) · ∑ i, (f i − mean f)² ≤ fᵀ (laplacian A) f`.

No positivity hypothesis on `λ₂` is needed: on a disconnected graph
`λ₂ = 0` and the statement is vacuously true — the QA fences prove that
the *division* form's `0 < λ₂` guard is exactly the boundary of the
true region (no finite constant works on a disconnected fixture).
The proof is the proved Rayleigh lower bound `secondEval_le_rayleigh`
at the centered vector, which is orthogonal to `onesVec` by the choice
of the mean, plus centering invariance of the energy. -/
theorem poincare_variance_mul_le (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnn : ∀ i j, 0 ≤ A i j) (hcard : 2 ≤ Fintype.card V) (f : V → ℝ) :
    secondEval (laplacian A) (laplacian_symmetric A hA) hcard
      * ∑ i, (f i - (∑ j, f j) / (Fintype.card V : ℝ)) ^ 2
      ≤ quadForm (laplacian A) f := by
  have hn0 : (0:ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.2 (by omega)
  obtain ⟨x, hxdef⟩ : ∃ x : V → ℝ,
      ∀ i, x i = f i - (∑ j, f j) / (Fintype.card V : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have hcenter : x = f - ((∑ j, f j) / (Fintype.card V : ℝ)) • onesVec := by
    funext i
    rw [hxdef i]
    simp [onesVec]
  have hsumx : ∑ i, x i = 0 := by
    simp only [hxdef, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, Finset.card_univ, mul_div_assoc,
      mul_div_cancel₀ _ (ne_of_gt hn0)]
    ring
  have horth : Matrix.dotProduct x onesVec = 0 := by
    simp only [Matrix.dotProduct, onesVec, mul_one]
    exact hsumx
  have hvar : ∑ i, (f i - (∑ j, f j) / (Fintype.card V : ℝ)) ^ 2
      = Matrix.dotProduct x x := by
    simp only [Matrix.dotProduct, ← hxdef, pow_two]
  by_cases hx : x = 0
  · rw [hvar, hx, Matrix.dotProduct_zero, mul_zero]
    exact laplacian_psd A hA hnn f
  · have hR := secondEval_le_rayleigh (laplacian_symmetric A hA)
      (laplacian_psd A hA hnn) (laplacian_ones_in_kernel A) hcard hx horth
    rw [rayleigh, if_neg hx] at hR
    have hmul : secondEval (laplacian A) (laplacian_symmetric A hA) hcard
        * Matrix.dotProduct x x ≤ quadForm (laplacian A) x :=
      (le_div_iff₀ (dotProduct_self_pos hx)).1 hR
    rw [hvar]
    rw [hcenter] at hmul ⊢
    rw [← quadForm_laplacian_sub_const A hA f
      ((∑ j, f j) / (Fintype.card V : ℝ))]
    exact hmul

/-- **The Poincaré inequality for the combinatorial Laplacian.** On a
network whose spectral gap is positive — connected symmetric nonnegative
graphs being the canonical case, via `poincare_inequality_of_connected`
— every function's variance around its mean is at most its Dirichlet
energy over the gap:

`∑ i, (f i − mean f)² ≤ fᵀ (laplacian A) f / λ₂ (laplacian A)`.

This is the division form of `poincare_variance_mul_le`; the QA pins
attain it exactly at Fiedler vectors (K₂ and P₃), so the constant is
sharp. -/
theorem poincare_inequality (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnn : ∀ i j, 0 ≤ A i j) (hcard : 2 ≤ Fintype.card V)
    (hpos : 0 < secondEval (laplacian A) (laplacian_symmetric A hA) hcard)
    (f : V → ℝ) :
    ∑ i, (f i - (∑ j, f j) / (Fintype.card V : ℝ)) ^ 2
      ≤ quadForm (laplacian A) f
        / secondEval (laplacian A) (laplacian_symmetric A hA) hcard := by
  refine (le_div_iff₀ hpos).2 ?_
  rw [mul_comm]
  exact poincare_variance_mul_le A hA hnn hcard f

/-- The connected convenience twin of `poincare_inequality`: on a
connected symmetric nonnegative network the spectral gap is positive
(the Fiedler certificate), so the Poincaré inequality holds with the
gap derived from connectivity. -/
theorem poincare_inequality_of_connected (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j)
    (hcard : 2 ≤ Fintype.card V) (hconn : (supportGraph A hA).Connected)
    (f : V → ℝ) :
    ∑ i, (f i - (∑ j, f j) / (Fintype.card V : ℝ)) ^ 2
      ≤ quadForm (laplacian A) f
        / secondEval (laplacian A) (laplacian_symmetric A hA) hcard := by
  refine poincare_inequality A hA hnn hcard ?_ f
  have h := lambda2_pos_of_connected A hA hnn hcard hconn
  rwa [lambda2_eq_secondEval] at h

/-- **The Poincaré inequality for the normalized Laplacian, in the
degree-weighted (π-measure) form.** On a positive-degree network with a
positive normalized spectral gap,

`∑ i, deg i · (f i − E_π f)² ≤ fᵀ (laplacian A) f / λ₂ (L_sym)`,

where `E_π f = (∑ j, deg j · f j)/(∑ j, deg j)` is the stationary-mean
functional of the walk (the mixing program's `stationaryVec` idiom, no
measure theory). Note the eigenvalue in the denominator is `L_sym`'s
own second eigenvalue — not a combinatorial one; the two are not
scalar-related on irregular graphs, which is why this is a separate
theorem rather than a corollary of the combinatorial form. Proof: the
general-kernel Rayleigh lower bound at the stretched centered vector
`√D (f − E_π f · 1)` (orthogonal to the kernel vector `√D · 1` by mass
conservation), with the energy transported through the congruence
`√D L_sym √D = laplacian A`. -/
theorem poincare_inequality_normalized (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) (hcard : 2 ≤ Fintype.card V)
    (hpos : 0 < secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard)
    (f : V → ℝ) :
    ∑ i, deg A i * (f i - (∑ j, deg A j * f j) / (∑ j, deg A j)) ^ 2
      ≤ quadForm (laplacian A) f
        / secondEval (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) hcard := by
  obtain ⟨i₀⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have hvolpos : 0 < ∑ j, deg A j :=
    Finset.sum_pos' (fun j _ => le_of_lt (hd j))
      ⟨i₀, Finset.mem_univ _, hd i₀⟩
  obtain ⟨y, hydef⟩ : ∃ y : V → ℝ,
      ∀ i, y i = f i - (∑ j, deg A j * f j) / (∑ j, deg A j) :=
    ⟨_, fun _ => rfl⟩
  have hcenter : y = f
      - ((∑ j, deg A j * f j) / (∑ j, deg A j)) • onesVec := by
    funext i
    rw [hydef i]
    simp [onesVec]
  have hmass : ∑ i, deg A i * y i = 0 := by
    have hcombine : ∑ i, deg A i * y i
        = ∑ i, (deg A i * f i
            - deg A i * ((∑ j, deg A j * f j) / (∑ j, deg A j))) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hydef i]
      ring
    rw [hcombine, Finset.sum_sub_distrib]
    have hconst : ∑ i, deg A i
        * ((∑ j, deg A j * f j) / (∑ j, deg A j))
        = (∑ j, deg A j * f j) := by
      rw [← Finset.sum_mul, mul_div_cancel₀ _ (ne_of_gt hvolpos)]
    rw [hconst, sub_self]
  have horth : Matrix.dotProduct (degreeSqrt A *ᵥ y)
      (degreeSqrt A *ᵥ onesVec) = 0 := by
    have hterm : ∀ i : V,
        (degreeSqrt A *ᵥ y) i * (degreeSqrt A *ᵥ onesVec) i
          = deg A i * y i := by
      intro i
      rw [degreeSqrt_mulVec_apply, degreeSqrt_mulVec_apply, onesVec,
        mul_one, mul_right_comm, Real.mul_self_sqrt (le_of_lt (hd i))]
    have hdotrwl : Matrix.dotProduct (degreeSqrt A *ᵥ y)
        (degreeSqrt A *ᵥ onesVec) = ∑ i, deg A i * y i := by
      simp only [Matrix.dotProduct]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    rw [hdotrwl, hmass]
  by_cases hx : degreeSqrt A *ᵥ y = 0
  · have hfconst : ∀ i : V,
        f i - (∑ j, deg A j * f j) / (∑ j, deg A j) = 0 := by
      intro i
      have h0 := congrFun hx i
      rw [degreeSqrt_mulVec_apply, hydef i] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h (Real.sqrt_ne_zero'.mpr (hd i))
      · exact h
    have hvar0 : ∑ i, deg A i
        * (f i - (∑ j, deg A j * f j) / (∑ j, deg A j)) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hfconst i]
      simp
    rw [hvar0]
    exact div_nonneg (laplacian_psd A hA hnn f) hpos.le
  · have hwne : degreeSqrt A *ᵥ onesVec ≠ 0 := by
      intro h
      have h0 := congrFun h i₀
      rw [degreeSqrt_mulVec_apply, onesVec, mul_one] at h0
      exact (Real.sqrt_ne_zero'.mpr (hd i₀)) h0
    have hR := secondEval_le_rayleigh_of_ker
      (normalizedLaplacian_symmetric A hA)
      (normalizedLaplacian_psd A hA hnn hd) hwne
      (normalizedLaplacian_mulVec_degreeSqrt_onesVec A hd) hcard hx horth
    rw [rayleigh, if_neg hx] at hR
    have hxx := dotProduct_degreeSqrt_mulVec A (fun i => le_of_lt (hd i)) y
    have henergy : quadForm (normalizedLaplacian A) (degreeSqrt A *ᵥ y)
        = quadForm (laplacian A) f := by
      rw [← quadForm_laplacian_eq_quadForm_normalizedLaplacian A hd y,
        hcenter, quadForm_laplacian_sub_const A hA f _]
    have hmul : secondEval (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) hcard
        * ∑ i, deg A i
            * (f i - (∑ j, deg A j * f j) / (∑ j, deg A j)) ^ 2
        ≤ quadForm (laplacian A) f := by
      have hsumconv : ∑ i, deg A i * y i * y i
          = ∑ i, deg A i
              * (f i - (∑ j, deg A j * f j) / (∑ j, deg A j)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hydef i]
        ring
      have hpos' : 0 < ∑ i, deg A i
          * (f i - (∑ j, deg A j * f j) / (∑ j, deg A j)) ^ 2 := by
        rw [← hsumconv, ← hxx]
        exact dotProduct_self_pos hx
      rw [henergy, hxx, hsumconv] at hR
      exact (le_div_iff₀ hpos').1 hR
    exact (le_div_iff₀ hpos).2 (by rw [mul_comm]; exact hmul)

/-- **The normalized Poincaré inequality's connected twin.** On a
connected positive-degree network the normalized spectral gap is
positive (the delivered connectivity transfer), so the degree-weighted
Poincaré inequality holds with the gap derived from connectivity. -/
theorem poincare_inequality_normalized_of_connected (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected) (f : V → ℝ) :
    ∑ i, deg A i * (f i - (∑ j, deg A j * f j) / (∑ j, deg A j)) ^ 2
      ≤ quadForm (laplacian A) f
        / secondEval (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) hcard :=
  poincare_inequality_normalized A hA hnn hd hcard
    (secondEval_normalizedLaplacian_pos_of_connected A hA hnn hd hcard hconn) f

/-- **Spectral edge expansion.** Instantiating the Poincaré engine form
at the plain indicator of a vertex set — whose variance is
`|S| · |V∖S| / |V|` and whose Dirichlet energy is exactly the boundary
weight (Multiway's indicator energy identity) — gives the linear-in-λ₂
edge expansion bound

`λ₂ (laplacian A) · |S| · (|V| − |S|) / |V| ≤ boundary A S`

for *every* vertex set, with no hypothesis beyond the engine's. Unlike
the Cheeger family's conductance statements this is set-by-set, linear
in the spectral gap, and needs no sweep or median; the QA pins attain
it with equality on `K₂` and `K₃` singletons. -/
theorem spectral_gap_edge_expansion (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j)
    (hcard : 2 ≤ Fintype.card V) (S : Finset V) :
    secondEval (laplacian A) (laplacian_symmetric A hA) hcard * (S.card : ℝ)
      * ((Fintype.card V : ℝ) - (S.card : ℝ)) / (Fintype.card V : ℝ)
      ≤ boundary A S := by
  have hn0 : ((Fintype.card V : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.2 (by omega))
  have hsumind : ∑ j, partIndicator S j = (S.card : ℝ) := by
    rw [← Finset.sum_add_sum_compl S (partIndicator S),
      Finset.sum_congr rfl (fun i hi => partIndicator_of_mem hi),
      Finset.sum_congr rfl
        (fun i hi => partIndicator_of_not_mem (Finset.mem_compl.1 hi)),
      Finset.sum_const, Finset.sum_const]
    simp
  have hvar : ∑ i, (partIndicator S i
        - (∑ j, partIndicator S j) / (Fintype.card V : ℝ)) ^ 2
      = (S.card : ℝ) * ((Fintype.card V : ℝ) - (S.card : ℝ))
        / (Fintype.card V : ℝ) := by
    have hmem : ∀ i ∈ S,
        (partIndicator S i - (S.card : ℝ)/(Fintype.card V : ℝ))^2
          = (1 - (S.card : ℝ)/(Fintype.card V : ℝ))^2 := by
      intro i hi
      rw [partIndicator_of_mem hi]
    have hnot : ∀ i ∈ Sᶜ,
        (partIndicator S i - (S.card : ℝ)/(Fintype.card V : ℝ))^2
          = ((S.card : ℝ)/(Fintype.card V : ℝ))^2 := by
      intro i hi
      rw [partIndicator_of_not_mem (Finset.mem_compl.1 hi)]
      ring
    have hcomplcard : ((Sᶜ).card : ℝ)
        = (Fintype.card V : ℝ) - (S.card : ℝ) := by
      rw [Finset.card_compl]
      exact Nat.cast_sub (Finset.card_le_univ S)
    have hSrwl : ∑ i in S, (partIndicator S i
        - (S.card : ℝ)/(Fintype.card V : ℝ))^2
        = ∑ i in S, (1 - (S.card : ℝ)/(Fintype.card V : ℝ))^2 := by
      refine Finset.sum_congr rfl fun i hi => hmem i hi
    have hScrwl : ∑ i in Sᶜ, (partIndicator S i
        - (S.card : ℝ)/(Fintype.card V : ℝ))^2
        = ∑ i in Sᶜ, ((S.card : ℝ)/(Fintype.card V : ℝ))^2 := by
      refine Finset.sum_congr rfl fun i hi => hnot i hi
    rw [hsumind,
      ← Finset.sum_add_sum_compl S
        (fun i => (partIndicator S i
          - (S.card : ℝ)/(Fintype.card V : ℝ))^2),
      hSrwl, hScrwl, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, hcomplcard]
    field_simp
    ring
  have hmul := poincare_variance_mul_le A hA hnn hcard (partIndicator S)
  rw [hvar, quadForm_laplacian_partIndicator A hA S] at hmul
  linear_combination hmul


end SpectralGraphTheory
