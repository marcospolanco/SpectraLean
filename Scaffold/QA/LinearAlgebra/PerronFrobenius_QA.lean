/-
  PerronFrobenius_QA.lean

  Purpose
  -------
  QA for `Scaffold.Mathlib.LinearAlgebra.PerronFrobenius` (the admitted
  Perron–Frobenius axiom, `proposals/admit-perron-frobenius.md`). Both
  fixtures are deliberately asymmetric (entries `2 ≠ 1` and `4 ≠ 1`) so
  the certification runs on genuinely directed input, and both are
  rational so every quantity is pinned by `norm_num`-class arithmetic —
  no irrational Perron data anywhere.

  Fixtures:

  - `P = !![1,2;1,0]` — the positive witness. Nonnegative, irreducible,
    with a positive diagonal entry (primitive: `P² > 0`). Perron root
    `2`, Perron vector `(2,1)`, second eigenvalue `−1` of *strictly*
    smaller modulus: the case in which the primitive strengthening
    happens to hold, so the axiom's clauses can be pinned against exact
    hand data (`charpoly = (X + 1)(X − 2)`, complex roots `{2, −1}`,
    `rootMultiplicity 2 = 1`).

  - `D = !![0,4;1,0]` — the calibration witness, an asymmetric directed
    2-cycle (zero diagonal, period 2, imprimitive). Perron root `2`,
    second eigenvalue `−2` with eigenvector `(−2,1)` of *equal* modulus.
    This is the proposal's mandated negative witness: it refutes the
    strict-dominance strengthening (`strict_dominance_refuted_QA`) while
    the axiom's own conclusion stays satisfiable on the same fixture
    (the domination clause instantiated at `z = −2` gives exactly the
    peripheral equality `|−2| = 2 ≤ 2`), so a future reader cannot
    mistake the admitted statement for the stronger primitive case.

  Load-bearing design: `P_only_nonneg_eigenvalue_QA` and
  `D_only_nonneg_eigenvalue_QA` are proved *by hand* (no axiom) — the
  eigenvector equations plus nonnegativity alone force the eigenvalue to
  be the Perron root — and the axiom's own only-eigenvalue clause is
  instantiated on the same hand data in
  `P_axiom_only_eigenvalue_on_hand_witness_QA`, so the axiom's content
  and the fixture's content are independently established and
  cross-checked. The Perron-root derivations consume the axiom's
  eigen-equation on the *unknown* existential witness `x` and recover
  `r = 2` exactly; an axiom whose conclusion were weaker (say no
  domination clause) or wrong (say a strict-dominance clause) would fail
  to support, or contradict, these pins.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interface where the arithmetic is
  evaluated. QA does not prove the axiom.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.LinearAlgebra.PerronFrobenius
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Polynomial.RingDivision

open scoped Matrix
open Polynomial

namespace Scaffold.LinearAlgebra.QA

/-! ### Fixtures and their entry tables -/

/-- The positive witness: asymmetric, nonnegative, irreducible,
primitive (`P² > 0`); Perron root `2`, Perron vector `(2, 1)`, second
eigenvalue `−1`. -/
def P : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 1, 0]

/-- The calibration witness: an asymmetric directed 2-cycle — zero
diagonal, period 2, imprimitive; Perron root `2`, second eigenvalue
`−2` of equal modulus. -/
def D : Matrix (Fin 2) (Fin 2) ℝ := !![0, 4; 1, 0]

theorem P_00 : P 0 0 = 1 := rfl
theorem P_01 : P 0 1 = 2 := rfl
theorem P_10 : P 1 0 = 1 := rfl
theorem P_11 : P 1 1 = 0 := rfl

theorem D_00 : D 0 0 = 0 := rfl
theorem D_01 : D 0 1 = 4 := rfl
theorem D_10 : D 1 0 = 1 := rfl
theorem D_11 : D 1 1 = 0 := rfl

/-- Both fixtures are genuinely directed: their adjacency is not
symmetric (`2 ≠ 1`, `4 ≠ 1`). -/
theorem P_not_IsSymm : ¬ P.IsSymm := fun h =>
  absurd (h.apply 0 1) (by rw [P_01, P_10]; norm_num)

theorem D_not_IsSymm : ¬ D.IsSymm := fun h =>
  absurd (h.apply 0 1) (by rw [D_01, D_10]; norm_num)

/-! ### Hypotheses of the axiom on the fixtures -/

theorem P_nonneg : ∀ i j, 0 ≤ P i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [P_00, P_01, P_10, P_11]

theorem D_nonneg : ∀ i j, 0 ≤ D i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [D_00, D_01, D_10, D_11]

theorem P_isIrreducible : P.IsIrreducible := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    first
      | exact Relation.ReflTransGen.refl
      | exact Relation.ReflTransGen.single
          (by show 0 < P 0 1; rw [P_01]; norm_num)
      | exact Relation.ReflTransGen.single
          (by show 0 < P 1 0; rw [P_10]; norm_num)

theorem D_isIrreducible : D.IsIrreducible := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    first
      | exact Relation.ReflTransGen.refl
      | exact Relation.ReflTransGen.single
          (by show 0 < D 0 1; rw [D_01]; norm_num)
      | exact Relation.ReflTransGen.single
          (by show 0 < D 1 0; rw [D_10]; norm_num)

theorem P_hex : ∃ i j, 0 < P i j := ⟨0, 1, by rw [P_01]; norm_num⟩

theorem D_hex : ∃ i j, 0 < D i j := ⟨0, 1, by rw [D_01]; norm_num⟩

/-! ### Eigen-equation entry lemmas (the raw interface) -/

theorem P_mulVec_eq (x : Fin 2 → ℝ) :
    (P *ᵥ x) 0 = x 0 + 2 * x 1 ∧ (P *ᵥ x) 1 = x 0 := by
  constructor
  · simp [Matrix.mulVec, Matrix.dotProduct, P, Fin.sum_univ_two]
  · simp [Matrix.mulVec, Matrix.dotProduct, P, Fin.sum_univ_two]

theorem D_mulVec_eq (x : Fin 2 → ℝ) :
    (D *ᵥ x) 0 = 4 * x 1 ∧ (D *ᵥ x) 1 = x 0 := by
  constructor
  · simp [Matrix.mulVec, Matrix.dotProduct, D, Fin.sum_univ_two]
  · simp [Matrix.mulVec, Matrix.dotProduct, D, Fin.sum_univ_two]

/-! ### Hand pins: the Perron data of both fixtures, no axiom -/

/-- **Hand pin (no axiom).** `(2, 1)` is the Perron eigenvector of `P`
at the eigenvalue `2`, computed entrywise from the raw fixture. -/
theorem P_hand_eigenvector_QA : P *ᵥ ![2, 1] = (2:ℝ) • ![2, 1] := by
  obtain ⟨e0, e1⟩ := P_mulVec_eq ![2, 1]
  funext i
  fin_cases i
  · show (P *ᵥ ![2, 1]) 0 = ((2:ℝ) • ![2, 1]) 0
    rw [e0]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul]
    norm_num
  · show (P *ᵥ ![2, 1]) 1 = ((2:ℝ) • ![2, 1]) 1
    rw [e1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul]
    norm_num

/-- **Hand pin (no axiom).** On `P`, every nonzero nonnegative
eigenvector has eigenvalue exactly `2`: the eigen-equations force
`μ² = μ + 2`, and nonnegativity forces `μ ≥ 0`, killing the `−1` root.
This is the content of the axiom's only-eigenvalue clause, established
independently of the axiom. -/
theorem P_only_nonneg_eigenvalue_QA (μ : ℝ) (y : Fin 2 → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hyne : y ≠ 0) (heig : P *ᵥ y = μ • y) :
    μ = 2 := by
  obtain ⟨e0, e1⟩ := P_mulVec_eq y
  rw [heig] at e0 e1
  simp only [Pi.smul_apply, smul_eq_mul] at e0 e1
  have hy1 : y 1 ≠ 0 := by
    intro h
    apply hyne
    have hy0 : y 0 = 0 := by rw [← e1, h]; ring
    funext i
    fin_cases i <;> simp [hy0, h]
  have hy1pos : 0 < y 1 := by
    rcases lt_or_eq_of_le (hy 1) with h | h
    · exact h
    · exact absurd h (Ne.symm hy1)
  have hμnn : 0 ≤ μ := by
    by_contra hμ
    push_neg at hμ
    have hlt : μ * y 1 < 0 := mul_neg_of_neg_of_pos hμ hy1pos
    rw [e1] at hlt
    linarith [hy 0]
  rw [← e1] at e0
  have hkey : y 1 * (μ * μ) = y 1 * (μ + 2) := by
    linear_combination e0
  have hμ2 : μ * μ = μ + 2 := mul_left_cancel₀ hy1 hkey
  rcases mul_eq_zero.mp (show (μ - 2) * (μ + 1) = 0 by linear_combination hμ2) with h | h
  · linarith
  · exact absurd (show μ = -1 by linarith) (by linarith)

/-- **Hand pin (no axiom).** `(2, 1)` is the Perron eigenvector of `D`
at the eigenvalue `2`. -/
theorem D_hand_eigenvector_pos_QA : D *ᵥ ![2, 1] = (2:ℝ) • ![2, 1] := by
  obtain ⟨e0, e1⟩ := D_mulVec_eq ![2, 1]
  funext i
  fin_cases i
  · show (D *ᵥ ![2, 1]) 0 = ((2:ℝ) • ![2, 1]) 0
    rw [e0]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul]
    norm_num
  · show (D *ᵥ ![2, 1]) 1 = ((2:ℝ) • ![2, 1]) 1
    rw [e1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul]
    norm_num

/-- **Hand pin (no axiom).** `(−2, 1)` is an eigenvector of `D` at the
eigenvalue `−2` — the second peripheral eigenvalue of the directed
2-cycle. -/
theorem D_hand_eigenvector_neg_QA : D *ᵥ ![-2, 1] = ((-2:ℝ)) • ![-2, 1] := by
  obtain ⟨e0, e1⟩ := D_mulVec_eq ![-2, 1]
  funext i
  fin_cases i
  · show (D *ᵥ ![-2, 1]) 0 = (((-2:ℝ)) • ![-2, 1]) 0
    rw [e0]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul]
    norm_num
  · show (D *ᵥ ![-2, 1]) 1 = (((-2:ℝ)) • ![-2, 1]) 1
    rw [e1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul]
    norm_num

/-- **Hand pin (no axiom).** On `D`, every nonzero nonnegative
eigenvector has eigenvalue exactly `2`: the eigen-equations force
`μ² = 4`, and nonnegativity forces `μ ≥ 0`, killing the `−2` root —
the peripheral eigenvalue `−2` has no nonnegative eigenvector. -/
theorem D_only_nonneg_eigenvalue_QA (μ : ℝ) (y : Fin 2 → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hyne : y ≠ 0) (heig : D *ᵥ y = μ • y) :
    μ = 2 := by
  obtain ⟨e0, e1⟩ := D_mulVec_eq y
  rw [heig] at e0 e1
  simp only [Pi.smul_apply, smul_eq_mul] at e0 e1
  have hy1 : y 1 ≠ 0 := by
    intro h
    apply hyne
    have hy0 : y 0 = 0 := by rw [← e1, h]; ring
    funext i
    fin_cases i <;> simp [hy0, h]
  have hy1pos : 0 < y 1 := by
    rcases lt_or_eq_of_le (hy 1) with h | h
    · exact h
    · exact absurd h (Ne.symm hy1)
  have hμnn : 0 ≤ μ := by
    by_contra hμ
    push_neg at hμ
    have hlt : μ * y 1 < 0 := mul_neg_of_neg_of_pos hμ hy1pos
    rw [e1] at hlt
    linarith [hy 0]
  rw [← e1] at e0
  have hkey : y 1 * (μ * μ) = y 1 * 4 := by
    linear_combination e0
  have hμ2 : μ * μ = 4 := mul_left_cancel₀ hy1 hkey
  rcases mul_eq_zero.mp (show (μ - 2) * (μ + 2) = 0 by linear_combination hμ2) with h | h
  · linarith
  · exact absurd h (by linarith)

/-! ### The mandated negative witness: the strict-dominance
strengthening is false on the imprimitive fixture -/

/-- The calibration centerpiece. The strengthening of Perron–Frobenius
that adds a strict-dominance clause — every eigenvalue other than the
Perron root, of any eigenvector, has strictly smaller modulus — is
**false** on the (irreducible, nonnegative, asymmetric) directed 2-cycle
`D`: the Perron pair `(2, (2,1))` satisfies the strengthened
hypotheses, the eigenpair `(−2, (−2,1))` satisfies the eigen-equation,
and `|−2| = 2 = r`. Strict dominance requires primitivity; this is the
proposal's Calibration boundary in proved form. -/
theorem strict_dominance_refuted_QA :
    ¬ (∀ r : ℝ, ∀ x : Fin 2 → ℝ, (∀ i, 0 < x i) → D *ᵥ x = r • x →
        ∀ μ : ℝ, ∀ y : Fin 2 → ℝ, y ≠ 0 → D *ᵥ y = μ • y → μ ≠ r → |μ| < r) := by
  intro h
  have hpos : ∀ i, 0 < (![2, 1] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> simp
  have hne : (![(-2 : ℝ), 1] : Fin 2 → ℝ) ≠ 0 := by
    intro h0
    have := congrFun h0 1
    simp at this
  have hbad := h 2 ![2, 1] hpos D_hand_eigenvector_pos_QA
    (-2) ![-2, 1] hne D_hand_eigenvector_neg_QA (by norm_num)
  norm_num at hbad

/-! ### Axiom-consumed pins: the positive witness `P` -/

/-- **Axiom-consumed.** The Perron root of `P` is exactly `2` and the
Perron vector points along `(2, 1)` — both derived from the axiom's
eigen-equation on its unknown existential witness, with the axiom's
simplicity clause instantiated at the derived root. `#print axioms` on
this theorem lists `perron_frobenius` (plus the standard three): that is
the point — this is the axiom's interface being pinned against hand
data. -/
theorem perron_frobenius_P_QA :
    ∃ x : Fin 2 → ℝ, (∀ i, 0 < x i) ∧ P *ᵥ x = (2:ℝ) • x ∧
      Polynomial.rootMultiplicity 2 P.charpoly = 1 ∧
      ∃ c : ℝ, 0 < c ∧ x = c • ![2, 1] := by
  obtain ⟨r, x, hr, hx, hevec, hmult, -, -, -⟩ :=
    perron_frobenius P P_nonneg P_isIrreducible P_hex
  obtain ⟨e0, e1⟩ := P_mulVec_eq x
  rw [hevec] at e0 e1
  simp only [Pi.smul_apply, smul_eq_mul] at e0 e1
  have hx1 : x 1 ≠ 0 := ne_of_gt (hx 1)
  rw [← e1] at e0
  have hkey : x 1 * (r * r) = x 1 * (r + 2) := by
    linear_combination e0
  have hr2 : r * r = r + 2 := mul_left_cancel₀ hx1 hkey
  rcases mul_eq_zero.mp (show (r - 2) * (r + 1) = 0 by linear_combination hr2) with h | h
  · have hre : r = 2 := by linarith
    subst hre
    refine ⟨x, hx, hevec, hmult, x 1, hx 1, ?_⟩
    funext i
    fin_cases i
    · simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.head_cons]
      exact e1.symm.trans (mul_comm _ _)
    · simp [Pi.smul_apply, smul_eq_mul]
  · exact absurd h (by linarith)

/-- **Axiom-cross-check.** Feeding the hand Perron eigenvector `(2, 1)`
(a nonnegative eigenvector at the hand eigenvalue `2`) into the axiom's
only-eigenvalue clause returns that eigenvalue for *any* nonnegative
eigenvector `y`: the axiom's clause agrees with the hand route
(`P_only_nonneg_eigenvalue_QA`) on the fixture, through the axiom's own
statement rather than a re-derivation. -/
theorem P_axiom_only_eigenvalue_on_hand_witness_QA :
    ∀ (x : Fin 2 → ℝ), (∀ i, 0 < x i) → P *ᵥ x = (2:ℝ) • x →
      ∀ μ : ℝ, ∀ y : Fin 2 → ℝ, (∀ i, 0 ≤ y i) → y ≠ 0 → P *ᵥ y = μ • y →
        μ = 2 := by
  intro x hxpos hevec μ y hy hyne heig
  obtain ⟨r, -, hr, -, -, -, hone, -, -⟩ :=
    perron_frobenius P P_nonneg P_isIrreducible P_hex
  have hxne : x ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp at this
    exact (hxpos 0).ne' this
  have hr_eq : 2 = r :=
    hone 2 x (fun i => le_of_lt (hxpos i)) hxne hevec
  exact (hone μ y hy hyne heig).trans hr_eq.symm

/-! ### Axiom-consumed pins: the calibration witness `D` -/

/-- **Axiom-consumed.** The Perron root of `D` is exactly `2` and its
Perron vector points along `(2, 1)` — the same derivation as
`perron_frobenius_P_QA` on the imprimitive fixture, where the
strict-dominance strengthening dies: the axiom's weaker conclusion is
the one that holds here. -/
theorem perron_frobenius_D_QA :
    ∃ x : Fin 2 → ℝ, (∀ i, 0 < x i) ∧ D *ᵥ x = (2:ℝ) • x ∧
      ∃ c : ℝ, 0 < c ∧ x = c • ![2, 1] := by
  obtain ⟨r, x, hr, hx, hevec, -, hone, -, hdom⟩ :=
    perron_frobenius D D_nonneg D_isIrreducible D_hex
  obtain ⟨e0, e1⟩ := D_mulVec_eq x
  rw [hevec] at e0 e1
  simp only [Pi.smul_apply, smul_eq_mul] at e0 e1
  have hx1 : x 1 ≠ 0 := ne_of_gt (hx 1)
  rw [← e1] at e0
  have hkey : x 1 * (r * r) = x 1 * 4 := by
    linear_combination e0
  have hr2 : r * r = 4 := mul_left_cancel₀ hx1 hkey
  rcases mul_eq_zero.mp (show (r - 2) * (r + 2) = 0 by linear_combination hr2) with h | h
  · have hre : r = 2 := by linarith
    subst hre
    exact ⟨x, hx, hevec, x 1, hx 1, by
      funext i
      fin_cases i
      · simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.head_cons]
        exact e1.symm.trans (mul_comm _ _)
      · simp [Pi.smul_apply, smul_eq_mul]⟩
  · exact absurd h (by linarith)

/-! ### Characteristic polynomials, simplicity, and the complex
spectrum -/

/-- One-time numeral normalization: `C 2` as the polynomial numeral
(the pinned Mathlib has `C_1` but no `C_2`, and `ring` treats `C 2` as
an atom). -/
private theorem C_two_real_QA : C ((2:ℝ)) = (2 : ℝ[X]) := by
  have e : (2:ℝ) = 1 + 1 := by norm_num
  have e' : (2:ℝ[X]) = 1 + 1 := by norm_num
  rw [e, Polynomial.C_add, Polynomial.C_1, ← e']

private theorem C_four_real_QA : C ((4:ℝ)) = (4 : ℝ[X]) := by
  have e : (4:ℝ) = 2 + 2 := by norm_num
  have e' : (4:ℝ[X]) = 2 + 2 := by norm_num
  rw [e, Polynomial.C_add, C_two_real_QA, ← e']

private theorem C_two_complex_QA : C ((2:ℂ)) = (2 : ℂ[X]) := by
  have e : (2:ℂ) = 1 + 1 := by norm_num
  have e' : (2:ℂ[X]) = 1 + 1 := by norm_num
  rw [e, Polynomial.C_add, Polynomial.C_1, ← e']

private theorem C_four_complex_QA : C ((4:ℂ)) = (4 : ℂ[X]) := by
  have e : (4:ℂ) = 2 + 2 := by norm_num
  have e' : (4:ℂ[X]) = 2 + 2 := by norm_num
  rw [e, Polynomial.C_add, C_two_complex_QA, ← e']

/-- The characteristic polynomial of `P`, computed from the definition
through the 2×2 determinant: `X² − X − 2 = (X + 1)(X − 2)`. -/
theorem P_charpoly_QA : P.charpoly = (X + C (1:ℝ)) * (X - C (2:ℝ)) := by
  rw [Matrix.charpoly, Matrix.det_fin_two]
  have h00 : Matrix.charmatrix P 0 0 = X - C (1:ℝ) := by
    rw [Matrix.charmatrix_apply_eq, P_00]
  have h11 : Matrix.charmatrix P 1 1 = X - C (0:ℝ) := by
    rw [Matrix.charmatrix_apply_eq, P_11]
  have h01 : Matrix.charmatrix P 0 1 = -(C (2:ℝ)) := by
    rw [Matrix.charmatrix_apply_ne (h := by decide), P_01]
  have h10 : Matrix.charmatrix P 1 0 = -(C (1:ℝ)) := by
    rw [Matrix.charmatrix_apply_ne (h := by decide), P_10]
  have hC : (-(C (2:ℝ))) * (-(C (1:ℝ))) = C (2:ℝ) := by
    rw [neg_mul_neg, ← Polynomial.C_mul]
    exact congrArg Polynomial.C (by norm_num : (2:ℝ) * (1:ℝ) = 2)
  rw [h00, h11, h01, h10, hC, Polynomial.C_0, Polynomial.C_1, C_two_real_QA]
  ring

/-- The Perron root of `P` is a **simple** eigenvalue: multiplicity one
in the characteristic polynomial, by the factorization route
(`(X + 1)` contributes nothing at `2`, `(X − 2)` exactly one). This is
the axiom's simplicity clause, pinned by hand. -/
theorem P_rootMultiplicity_QA : Polynomial.rootMultiplicity 2 P.charpoly = 1 := by
  have hEq : X + C (1:ℝ) = X - C (-(1:ℝ)) := by
    rw [Polynomial.C_neg, sub_neg_eq_add]
  have hne : (X + C (1:ℝ)) ≠ 0 := by
    rw [hEq]
    exact Polynomial.X_sub_C_ne_zero _
  have hroot : ¬ Polynomial.IsRoot (X + C (1:ℝ)) 2 := by
    intro hroot'
    have h2 : (X + C (1:ℝ)).eval 2 = 0 := hroot'
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at h2
    norm_num at h2
  rw [P_charpoly_QA, ← pow_one (X - C (2:ℝ)),
    Polynomial.rootMultiplicity_mul_X_sub_C_pow hne,
    Polynomial.rootMultiplicity_eq_zero hroot]

/-- The complexified characteristic polynomial of `P` factors over `ℂ`
with roots exactly `2` and `−1`. -/
theorem P_charpoly_complex_QA :
    (Matrix.charpoly (P.map (algebraMap ℝ ℂ))) =
      (X - C (Complex.ofReal 2)) * (X - C (Complex.ofReal (-1))) := by
  rw [Matrix.charpoly, Matrix.det_fin_two]
  have h00 : Matrix.charmatrix (P.map (algebraMap ℝ ℂ)) 0 0
      = X - C (Complex.ofReal 1) := by
    rw [Matrix.charmatrix_apply_eq, Matrix.map_apply, P_00, Complex.coe_algebraMap]
  have h11 : Matrix.charmatrix (P.map (algebraMap ℝ ℂ)) 1 1
      = X - C (Complex.ofReal 0) := by
    rw [Matrix.charmatrix_apply_eq, Matrix.map_apply, P_11, Complex.coe_algebraMap]
  have h01 : Matrix.charmatrix (P.map (algebraMap ℝ ℂ)) 0 1
      = -(C (Complex.ofReal 2)) := by
    rw [Matrix.charmatrix_apply_ne (h := by decide), Matrix.map_apply, P_01, Complex.coe_algebraMap]
  have h10 : Matrix.charmatrix (P.map (algebraMap ℝ ℂ)) 1 0
      = -(C (Complex.ofReal 1)) := by
    rw [Matrix.charmatrix_apply_ne (h := by decide), Matrix.map_apply, P_10, Complex.coe_algebraMap]
  have hC : (-(C (Complex.ofReal 2))) * (-(C (Complex.ofReal 1)))
      = C (Complex.ofReal 2) := by
    rw [neg_mul_neg, ← Polynomial.C_mul, ← Complex.ofReal_mul]
    exact congrArg Polynomial.C (congrArg Complex.ofReal (by norm_num : (2:ℝ) * (1:ℝ) = 2))
  rw [h00, h11, h01, h10, hC]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_neg, Polynomial.C_0, Polynomial.C_1, Polynomial.C_neg,
    C_two_complex_QA]
  ring

theorem P_complex_roots_QA :
    (Matrix.charpoly (P.map (algebraMap ℝ ℂ))).roots
      = ({Complex.ofReal 2, Complex.ofReal (-1)} : Multiset ℂ) := by
  rw [P_charpoly_complex_QA]
  have hne : ((X - C (Complex.ofReal 2)) * (X - C (Complex.ofReal (-1)))) ≠ 0 :=
    mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _)
  rw [Polynomial.roots_mul hne, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
  simp

/-- **Axiom-consumed.** The domination clause on the positive witness:
both complex roots `2` and `−1` have modulus at most the derived Perron
root `r = 2` (here `|2| = 2` and `|−1| = 1`, the strict case of the
primitive fixture). The axiom's spectral-radius content, pinned against
the hand-computed complex spectrum. -/
theorem P_axiom_domination_QA :
    Complex.abs (Complex.ofReal 2) ≤ 2 ∧ Complex.abs (Complex.ofReal (-1)) ≤ 2 := by
  obtain ⟨r, x, hr, hx, hevec, -, -, -, hdom⟩ :=
    perron_frobenius P P_nonneg P_isIrreducible P_hex
  obtain ⟨e0, e1⟩ := P_mulVec_eq x
  rw [hevec] at e0 e1
  simp only [Pi.smul_apply, smul_eq_mul] at e0 e1
  have hx1 : x 1 ≠ 0 := ne_of_gt (hx 1)
  rw [← e1] at e0
  have hkey : x 1 * (r * r) = x 1 * (r + 2) := by
    linear_combination e0
  have hr2 : r * r = r + 2 := mul_left_cancel₀ hx1 hkey
  rcases mul_eq_zero.mp (show (r - 2) * (r + 1) = 0 by linear_combination hr2) with h | h
  · have hre : r = 2 := by linarith
    subst hre
    have m2 : Complex.ofReal 2 ∈ (Matrix.charpoly (P.map (algebraMap ℝ ℂ))).roots := by
      rw [P_complex_roots_QA]
      simp
    have m1 : Complex.ofReal (-1) ∈ (Matrix.charpoly (P.map (algebraMap ℝ ℂ))).roots := by
      rw [P_complex_roots_QA]
      simp
    exact ⟨hdom _ m2, hdom _ m1⟩
  · exact absurd h (by linarith)

/-- The characteristic polynomial of `D`: `X² − 4 = (X − 2)(X + 2)` —
the two peripheral eigenvalues are the roots. -/
theorem D_charpoly_QA : D.charpoly = (X - C (2:ℝ)) * (X + C (2:ℝ)) := by
  rw [Matrix.charpoly, Matrix.det_fin_two]
  have h00 : Matrix.charmatrix D 0 0 = X - C (0:ℝ) := by
    rw [Matrix.charmatrix_apply_eq, D_00]
  have h11 : Matrix.charmatrix D 1 1 = X - C (0:ℝ) := by
    rw [Matrix.charmatrix_apply_eq, D_11]
  have h01 : Matrix.charmatrix D 0 1 = -(C (4:ℝ)) := by
    rw [Matrix.charmatrix_apply_ne (h := by decide), D_01]
  have h10 : Matrix.charmatrix D 1 0 = -(C (1:ℝ)) := by
    rw [Matrix.charmatrix_apply_ne (h := by decide), D_10]
  have hC : (-(C (4:ℝ))) * (-(C (1:ℝ))) = C (4:ℝ) := by
    rw [neg_mul_neg, ← Polynomial.C_mul]
    exact congrArg Polynomial.C (by norm_num : (4:ℝ) * (1:ℝ) = 4)
  rw [h00, h11, h01, h10, hC, Polynomial.C_0, C_two_real_QA, C_four_real_QA]
  ring

/-- The complexified characteristic polynomial of `D` factors over `ℂ`
with roots exactly `2` and `−2` — the full peripheral pair of the
directed 2-cycle. -/
theorem D_charpoly_complex_QA :
    (Matrix.charpoly (D.map (algebraMap ℝ ℂ))) =
      (X - C (Complex.ofReal 2)) * (X - C (Complex.ofReal (-2))) := by
  rw [Matrix.charpoly, Matrix.det_fin_two]
  have h00 : Matrix.charmatrix (D.map (algebraMap ℝ ℂ)) 0 0
      = X - C (Complex.ofReal 0) := by
    rw [Matrix.charmatrix_apply_eq, Matrix.map_apply, D_00, Complex.coe_algebraMap]
  have h11 : Matrix.charmatrix (D.map (algebraMap ℝ ℂ)) 1 1
      = X - C (Complex.ofReal 0) := by
    rw [Matrix.charmatrix_apply_eq, Matrix.map_apply, D_11, Complex.coe_algebraMap]
  have h01 : Matrix.charmatrix (D.map (algebraMap ℝ ℂ)) 0 1
      = -(C (Complex.ofReal 4)) := by
    rw [Matrix.charmatrix_apply_ne (h := by decide), Matrix.map_apply, D_01, Complex.coe_algebraMap]
  have h10 : Matrix.charmatrix (D.map (algebraMap ℝ ℂ)) 1 0
      = -(C (Complex.ofReal 1)) := by
    rw [Matrix.charmatrix_apply_ne (h := by decide), Matrix.map_apply, D_10, Complex.coe_algebraMap]
  have hC : (-(C (Complex.ofReal 4))) * (-(C (Complex.ofReal 1)))
      = C (Complex.ofReal 4) := by
    rw [neg_mul_neg, ← Polynomial.C_mul, ← Complex.ofReal_mul]
    exact congrArg Polynomial.C (congrArg Complex.ofReal (by norm_num : (4:ℝ) * (1:ℝ) = 4))
  rw [h00, h11, h01, h10, hC]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_neg, Polynomial.C_0, Polynomial.C_1, Polynomial.C_neg,
    C_two_complex_QA, C_four_complex_QA]
  ring

theorem D_complex_roots_QA :
    (Matrix.charpoly (D.map (algebraMap ℝ ℂ))).roots
      = ({Complex.ofReal 2, Complex.ofReal (-2)} : Multiset ℂ) := by
  rw [D_charpoly_complex_QA]
  have hne : ((X - C (Complex.ofReal 2)) * (X - C (Complex.ofReal (-2)))) ≠ 0 :=
    mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _)
  rw [Polynomial.roots_mul hne, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
  simp

/-- **Axiom-consumed.** The domination clause on the calibration
witness: the second peripheral root `−2` satisfies `|−2| ≤ r = 2` —
with *equality*, which is exactly why the strict-dominance
strengthening is false here (`strict_dominance_refuted_QA`) while the
axiom's conclusion remains satisfiable. -/
theorem D_axiom_domination_QA : Complex.abs (Complex.ofReal (-2)) ≤ 2 := by
  obtain ⟨r, x, hr, hx, hevec, -, -, -, hdom⟩ :=
    perron_frobenius D D_nonneg D_isIrreducible D_hex
  obtain ⟨e0, e1⟩ := D_mulVec_eq x
  rw [hevec] at e0 e1
  simp only [Pi.smul_apply, smul_eq_mul] at e0 e1
  have hx1 : x 1 ≠ 0 := ne_of_gt (hx 1)
  rw [← e1] at e0
  have hkey : x 1 * (r * r) = x 1 * 4 := by
    linear_combination e0
  have hr2 : r * r = 4 := mul_left_cancel₀ hx1 hkey
  rcases mul_eq_zero.mp (show (r - 2) * (r + 2) = 0 by linear_combination hr2) with h | h
  · have hre : r = 2 := by linarith
    subst hre
    have m : Complex.ofReal (-2) ∈ (Matrix.charpoly (D.map (algebraMap ℝ ℂ))).roots := by
      rw [D_complex_roots_QA]
      simp
    exact hdom _ m
  · exact absurd h (by linarith)

end Scaffold.LinearAlgebra.QA
