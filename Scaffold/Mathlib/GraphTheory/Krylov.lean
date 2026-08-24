/-
Copyright 2024 Scaffold Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Scaffold.Mathlib.GraphTheory.Heat
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Krylov spaces, polynomial images, and the Chebyshev layer

Step 1a (the interface layer) of
`proposals/approximate-spectral-projection.md`: the reusable pieces the
cleared Lanczos/Kaniel–Paige shape is assembled from — the scalar
Chebyshev facts, the polynomial-eigenaction transfer, and the Krylov
span with its membership interface — plus the hypothesis-form
Kaniel–Paige skeleton that Step 1b will discharge against the shelf's
spectral layer. Everything here is proved hard crust; this module adds
no axioms.

Survey note (Step 0, recorded before this layer was written): the
pinned Mathlib carries `Polynomial.Chebyshev.T` with `T_real_cos`
(`T_n(cos θ) = cos (n θ)` — the entire band bound follows from it) and
the `aeval`/monomial-sum layer, but **no `natDegree (T ℝ n) = n` and no
growth lemma for `T` beyond `1`** — both priced as shallow gaps in the
Step-0 survey and both delivered here. The shelf's SGT interface is at
`V : Type` (Type 0), not `Type*`; this module matches it (the Step-0
run's sharpest elaboration finding — working at `Type*` strands
`rayleigh` and `Heat.pow_mulVec_smul` on postponed instances).

Contents:

- `abs_T_eval_le_one` — `|T_n(x)| ≤ 1` on `[-1, 1]` (the Chebyshev band
  bound; the polynomial-image half of the Kaniel–Paige argument);
- `natDegree_T` — `(T ℝ n).natDegree = n` (the first priced gap; with
  `Polynomial.natDegree_comp` it gives the `natDegree < k` side
  condition the affine-composed band polynomial needs);
- `one_le_eval_T_of_one_le` — `1 ≤ T_m(x)` at `x ≥ 1` (the second
  priced gap; the non-vacuity half of the Kaniel–Paige denominator
  `T_{k−1}(1 + 2γ) ≥ 1`);
- `sum_mulVec` — the `*ᵥ`-action distributes over Finset sums in the
  matrix argument (the pin-gap helper this repository has inlined since
  the band-projector Step 3);
- `krylovSpan M b k` — the `k`-th Krylov space, the span of
  `b, Mb, …, Mᵏ⁻¹ b`: the variational object Rayleigh–Ritz optimizes
  over;
- `aeval_mulVec_eq_eval_smul` — `p(M) v = p(μ) • v` at an eigenvector
  (`M v = μ • v`), through the heat module's `pow_mulVec_smul`;
- `aeval_mulVec_mem_krylovSpan` — degree-`< k` polynomial images of
  `b` lie in `krylovSpan M b k`;
- `kanielPaigeSkeleton` — the full bound in hypothesis form: every
  spectral-layer input the real proof must supply from
  `quadForm_eigvalOf` / `dotProduct_eigvecOf` / the Rayleigh sandwich
  enters as a *named* hypothesis (`hp₁`, `horth`, `horthM`, `hbottom`,
  `hband`), and the skeleton proves the exact bound composes from
  exactly those plus the pieces above.

Step 1b (the spectral discharge) adds the layer that discharges those
five sites on the shelf's eigenbasis machinery:

- `eigvec_dotProduct_mulVec` / `eigvec_dotProduct_pow_mulVec` /
  `eigvec_dotProduct_aeval_mulVec` — the general-eigenvector transfer:
  for symmetric `M` and `M *ᵥ u = μ • u`, `u ⬝ᵥ (M *ᵥ y) = μ (u ⬝ᵥ y)`
  and its power/polynomial propagations. Not tied to `eigvecOf`, so any
  eigenvector qualifies; at `u ⊥ g` this is the `horth` discharge;
- `eigvecOf_dotProduct_aeval_mulVec` — the component form: the `i`-th
  eigencomponent of `p(M) y` is `p(μ i)` times the `i`-th component of
  `y`; with Parseval (`dotProduct_eigvecOf`) and the quadratic-form
  resolution (`quadForm_eigvalOf`) this drives `hband`/`hbottom` through
  `dotProduct_aeval_mulVec_self` and `quadForm_aeval_mulVec`;
- `bandMap Ltwo Lbot` — the affine band map `w(λ) = (2λ − Ltwo −
  Lbot)/(Ltwo − Lbot)` sending the spectral band `[Lbot, Ltwo]` onto
  `[-1, 1]`, with its eval pins, degree, band range, and growth lemmas
  (`hp₁`/`hdeg`/`hTv` at the composed polynomial
  `T_{k−1} ∘ w`);
- `exists_unit_decomposition` — `b = c • u + s • g` with `g ⊥ u`,
  `‖g‖² ≤ 1`, `c² + s² = 1` for unit `b` along a unit `u`;
- `kanielPaigeChebyshev` — the composite: the full skeleton conclusion
  at the Chebyshev-composed band polynomial, every spectral site
  discharged from the eigenbasis-level band hypothesis (`hpar`: every
  eigenvector at an eigenvalue outside `[Lbot, Ltwo]` is a multiple of
  `u` — with `Ltwo ≤ Ltop` this says the only eigenvalue above `Ltwo`
  is the simple top one).

Step 1c (the final statement) adds the public form of the bound:

- `kanielPaige` — the classical Kaniel–Paige statement at the Step-0
  recorded shape: unit `b` with `u ⬝ᵥ b ≠ 0` (the `c`/`s`/`g`
  decomposition supplied internally by `exists_unit_decomposition`,
  through the identifications `c = u ⬝ᵥ b`, `s² = 1 − c²`, and
  `w(Ltop) = 1 + 2γ` at `γ = (Ltop − Ltwo)/(Ltwo − Lbot)`), so the
  bound reads `(Ltop − Lbot) · tan²φ / T_{k−1}(1 + 2γ)²`.

The Kaniel–Paige citation (Saad, *Numerical Methods for Large
Eigenvalue Problems*, §6) is recorded in the proposal, which owns this
program's statement; the interface pieces and the hypothesis-form
skeleton carry no citation, and the final statement's docstring carries
the §6 locator with the proposal's own verify-against-the-physical-copy
caveat — nothing axiom-backed is involved anywhere in this module.
-/

open Polynomial Matrix

namespace SpectralGraphTheory

/-! ### The Chebyshev layer (scalar; no vertex type) -/

/-- `|T_n(x)| ≤ 1` on `[-1, 1]`: `T_n(cos θ) = cos (n θ)` at
`θ = arccos x`, and `|cos| ≤ 1`. -/
theorem abs_T_eval_le_one (n : ℕ) {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x| ≤ 1 := by
  have hcos : (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x
      = Real.cos ((n : ℤ) * Real.arccos x) := by
    rw [← Polynomial.Chebyshev.T_real_cos]
    congr 1
    exact (Real.cos_arccos hx1 hx2).symm
  rw [hcos]
  exact abs_le.2 ⟨(Real.cos_mem_Icc _).1, (Real.cos_mem_Icc _).2⟩

/-- The natural-degree identification for the Chebyshev polynomials
over `ℝ` — the first priced shallow gap of the Step-0 survey (the pin
carries no such lemma; `Polynomial.natDegree_sub_eq_left_of_natDegree_lt`
does the degree arithmetic at the two-step recurrence). -/
theorem natDegree_T (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).natDegree = n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
      push_cast at ih1 ih2 ⊢
      -- ih1 : natDegree (T ↑n) = n, ih2 : natDegree (T (↑n + 1)) = n + 1
      have hT1ne : Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1) ≠ 0 := by
        intro h0
        rw [h0, Polynomial.natDegree_zero] at ih2
        exact Nat.succ_ne_zero n ih2.symm
      have hlc1 : (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)).leadingCoeff ≠ 0 := by
        rw [Ne, Polynomial.leadingCoeff_eq_zero]
        exact hT1ne
      have hC2 : (2 : ℝ[X]) = Polynomial.C (2 : ℝ) := (map_ofNat _ 2).symm
      have hlc2X : ((2 : ℝ[X]) * X).leadingCoeff ≠ 0 := by
        have hlc : ((2 : ℝ[X]) * X).leadingCoeff = 2 := by
          rw [hC2, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
            Polynomial.leadingCoeff_X]
          norm_num
        rw [hlc]
        norm_num
      have hdeg2X : ((2 : ℝ[X]) * X).natDegree = 1 := by
        rw [hC2, Polynomial.natDegree_C_mul two_ne_zero]
        simp
      have hdeg : (((2 : ℝ[X]) * X
            * Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1))).natDegree
          = n + 2 := by
        rw [Polynomial.natDegree_mul' (mul_ne_zero hlc2X hlc1),
          hdeg2X, ih2]
        omega
      rw [Polynomial.Chebyshev.T_add_two,
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by
          rw [ih1, hdeg]
          omega),
        hdeg]

/-- The growth engine: on `1 ≤ x` the Chebyshev values stay `≥ 1` and
increase with the index — proved as one conjunction by ordinary
induction, the recurrence's linear combination never needing more than
the two previous instances. -/
private theorem eval_T_pair_mono {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    1 ≤ (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x ∧
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x ≤
      (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)).eval x := by
  induction n with
  | zero =>
      push_cast
      exact ⟨by simp, by simpa using hx⟩
  | succ n ih =>
      push_cast
      refine ⟨le_trans ih.1 ih.2, ?_⟩
      have h2X : ((2 : ℝ[X]) * X).eval x = 2 * x := by
        have hC2 : (2 : ℝ[X]) = Polynomial.C (2 : ℝ) := (map_ofNat _ 2).symm
        rw [hC2, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      have hE : (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1 + 1)).eval x
          = 2 * x * (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)).eval x
            - (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x := by
        rw [Polynomial.Chebyshev.T_add_one, Int.add_sub_cancel,
          Polynomial.eval_sub, Polynomial.eval_mul, h2X]
      rw [hE]
      nlinarith [hx, ih.1, ih.2]

/-- `T_m(x) ≥ 1` whenever `x ≥ 1` — the second priced shallow gap of
the Step-0 survey: the non-vacuity half of the Kaniel–Paige denominator
(`T_{k−1}(1 + 2γ) ≥ 1` at a nonnegative gap), two-step content proved
by the conjunction engine above. -/
theorem one_le_eval_T_of_one_le {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    1 ≤ (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x :=
  (eval_T_pair_mono hx n).1

/-! ### The Krylov layer -/

section Krylov

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The `*ᵥ`-action distributes over Finset sums in the matrix
argument — the "inlined mulVec analog of `Matrix.sum_mul`" pattern this
repository has used since the band-projector Step 3. -/
theorem sum_mulVec {ι : Type} (F : ι → Matrix V V ℝ) (s : Finset ι)
    (b : V → ℝ) :
    (∑ i ∈ s, F i) *ᵥ b = ∑ i ∈ s, (F i *ᵥ b) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec,
        ih]

/-- The `k`-th Krylov space of `M` seeded at `b`: the span of
`b, M b, …, Mᵏ⁻¹ b`. The variational object the Rayleigh–Ritz value
optimizes over, and the container the Kaniel–Paige polynomial images
land in. -/
def krylovSpan (M : Matrix V V ℝ) (b : V → ℝ) (k : ℕ) :
    Submodule ℝ (V → ℝ) :=
  Submodule.span ℝ (Set.range fun i : Fin k => (M ^ (i : ℕ)) *ᵥ b)

theorem scalar_mul_eq_smul (a : ℝ) (M : Matrix V V ℝ) :
    (algebraMap ℝ (Matrix V V ℝ) a) * M = a • M := by
  rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]

/-- `p(M) v = p(μ) • v` whenever `M v = μ • v`: the eigen-equation
propagates through `aeval` by the monomial-sum decomposition, each
monomial term through the heat module's power lemma. -/
theorem aeval_mulVec_eq_eval_smul (M : Matrix V V ℝ) {v : V → ℝ} {μ : ℝ}
    (hMv : M *ᵥ v = μ • v) (p : ℝ[X]) :
    (aeval M p) *ᵥ v = (p.eval μ) • v := by
  have key : ∀ (j : ℕ) (a : ℝ),
      (aeval M (monomial j a)) *ᵥ v = (a * μ ^ j) • v := by
    intro j a
    rw [Polynomial.aeval_monomial, scalar_mul_eq_smul,
      Matrix.smul_mulVec_assoc, pow_mulVec_smul M hMv j, smul_smul]
  calc (aeval M p) *ᵥ v
      = ((aeval M) (∑ j ∈ Finset.range (p.natDegree + 1),
          monomial j (p.coeff j))) *ᵥ v := by
        conv_lhs => rw [Polynomial.as_sum_range p]
    _ = (∑ j ∈ Finset.range (p.natDegree + 1),
           (aeval M) (monomial j (p.coeff j))) *ᵥ v := by
        rw [map_sum (aeval M) (fun j => monomial j (p.coeff j))
          (Finset.range (p.natDegree + 1))]
    _ = ∑ j ∈ Finset.range (p.natDegree + 1),
          ((aeval M) (monomial j (p.coeff j)) *ᵥ v) :=
        sum_mulVec _ _ v
    _ = ∑ j ∈ Finset.range (p.natDegree + 1), (p.coeff j * μ ^ j) • v :=
        Finset.sum_congr rfl fun j _ => key j _
    _ = (p.eval μ) • v := by
        rw [← Finset.sum_smul, ← Polynomial.eval_eq_sum_range]

/-- The degree-`< k` polynomial images of `b` lie in the `k`-th Krylov
span — the membership half of "the Rayleigh–Ritz value over the Krylov
space dominates `R(p(M)b)`". -/
theorem aeval_mulVec_mem_krylovSpan (M : Matrix V V ℝ) (b : V → ℝ) (k : ℕ)
    (p : ℝ[X]) (hdeg : p.natDegree < k) :
    (aeval M p) *ᵥ b ∈ krylovSpan M b k := by
  have h1 : (aeval M p) *ᵥ b
      = ∑ j ∈ Finset.range k,
          ((aeval M) (monomial j (p.coeff j)) *ᵥ b) := by
    conv_lhs => rw [Polynomial.as_sum_range' p k hdeg]
    rw [map_sum (aeval M) (fun j => monomial j (p.coeff j))
      (Finset.range k), sum_mulVec _ _ b]
  rw [h1]
  refine Submodule.sum_mem _ fun j hj => ?_
  have hj' : j < k := Finset.mem_range.mp hj
  rw [Polynomial.aeval_monomial, scalar_mul_eq_smul,
    Matrix.smul_mulVec_assoc]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨⟨j, hj'⟩, rfl⟩)

set_option maxHeartbeats 800000 in
/-- **The Kaniel–Paige skeleton** (hypothesis form). From the
decomposition `b = c • u + s • g` of a starting vector along a unit top
eigenvector `u` (`M u = Ltop • u`) and its orthogonal complement, plus
exactly the facts the shelf's spectral layer supplies (each a named
hypothesis here, each dischargeable from `quadForm_eigvalOf` /
`dotProduct_eigvecOf` / the Rayleigh sandwich and the Chebyshev band
bound in the full proof), the Krylov space contains a nonzero vector
whose Rayleigh quotient is within
`(Ltop - Lbot) · s² / (c² T²)` of the top eigenvalue. No Lanczos
tridiagonalization, no recursion — the bound is a variational
statement about polynomial images of `b`. -/
theorem kanielPaigeSkeleton (M : Matrix V V ℝ) (b u g : V → ℝ)
    (c s Ltop Lbot Tv : ℝ) (k : ℕ) (p : ℝ[X])
    (hb : b = c • u + s • g)
    (hu : M *ᵥ u = Ltop • u)
    (huu : Matrix.dotProduct u u = 1)
    (hc : c ≠ 0)
    (hTv : 1 ≤ Tv)
    (hbotle : Lbot ≤ Ltop)
    (hdeg : p.natDegree < k)
    -- spectral-layer hypotheses: discharge sites named for Step 1
    (hp₁ : p.eval Ltop = Tv)
    (horth : Matrix.dotProduct u ((aeval M p) *ᵥ g) = 0)
    (horthM : Matrix.dotProduct u (M *ᵥ ((aeval M p) *ᵥ g)) = 0)
    (hbottom : Lbot * Matrix.dotProduct ((aeval M p) *ᵥ g)
        ((aeval M p) *ᵥ g)
      ≤ Matrix.dotProduct ((aeval M p) *ᵥ g)
          (M *ᵥ ((aeval M p) *ᵥ g)))
    (hband : Matrix.dotProduct ((aeval M p) *ᵥ g) ((aeval M p) *ᵥ g) ≤ 1) :
    ∃ x ∈ krylovSpan M b k, x ≠ 0 ∧
      Ltop - rayleigh M x
        ≤ (Ltop - Lbot) * s ^ 2 / c ^ 2 / Tv ^ 2 := by
  set q : V → ℝ := (aeval M p) *ᵥ g with hq
  set x : V → ℝ := (aeval M p) *ᵥ b with hxbdef
  -- the polynomial image of b along the decomposition
  have hxb : x = (c * Tv) • u + s • q := by
    have hpu : (aeval M p) *ᵥ u = Tv • u := by
      rw [aeval_mulVec_eq_eval_smul M hu, hp₁]
    conv_lhs => rw [hxbdef, hb]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [hpu, smul_smul, mul_comm c Tv, ← hq]
  have hqᵤ : Matrix.dotProduct q u = 0 := by
    rw [Matrix.dotProduct_comm, horth]
  -- squared norm
  have hD : Matrix.dotProduct x x
      = (c * Tv) ^ 2 + s ^ 2 * Matrix.dotProduct q q := by
    simp only [hxb, Matrix.add_dotProduct, Matrix.dotProduct_add,
      Matrix.dotProduct_smul, Matrix.smul_dotProduct, smul_eq_mul,
      huu, horth, hqᵤ, horthM, zero_mul, mul_zero, add_zero, zero_add]
    ring
  -- quadratic form
  have hMx : M *ᵥ x = (c * Tv * Ltop) • u + s • (M *ᵥ q) := by
    rw [hxb, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hu, smul_smul]
  have hP : Matrix.dotProduct x (M *ᵥ x)
      = (c * Tv) ^ 2 * Ltop
        + s ^ 2 * Matrix.dotProduct q (M *ᵥ q) := by
    simp only [hxb, hMx, Matrix.mulVec_add, Matrix.mulVec_smul, hu,
      Matrix.add_dotProduct, Matrix.dotProduct_add,
      Matrix.dotProduct_smul, Matrix.smul_dotProduct, smul_eq_mul,
      huu, horth, hqᵤ, horthM, zero_mul, mul_zero, add_zero, zero_add]
    ring
  have hQ0 : (0:ℝ) ≤ Matrix.dotProduct q q := by
    unfold Matrix.dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hA : (0:ℝ) < c ^ 2 * Tv ^ 2 := by positivity
  have hx0 : x ≠ 0 := by
    intro h0
    have h0' : Matrix.dotProduct x x = 0 := by rw [h0]; simp
    rw [hD, mul_pow] at h0'
    have hA' : (0:ℝ) < (c * Tv) ^ 2 := by positivity
    nlinarith [hQ0]
  refine ⟨x, aeval_mulVec_mem_krylovSpan M b k p hdeg, hx0, ?_⟩
  -- the bound
  have hnum : Ltop * Matrix.dotProduct x x
      - Matrix.dotProduct x (M *ᵥ x)
      = s ^ 2 * (Ltop * Matrix.dotProduct q q
          - Matrix.dotProduct q (M *ᵥ q)) := by
    rw [hD, hP]; ring
  have hstep1 : s ^ 2 * (Ltop * Matrix.dotProduct q q
        - Matrix.dotProduct q (M *ᵥ q))
      ≤ s ^ 2 * ((Ltop - Lbot) * Matrix.dotProduct q q) := by
    nlinarith [hbottom, sq_nonneg s]
  have hstep2 : s ^ 2 * ((Ltop - Lbot) * Matrix.dotProduct q q)
      ≤ s ^ 2 * (Ltop - Lbot) * 1 := by
    have hprod : (0:ℝ) ≤ s ^ 2 * (Ltop - Lbot) := by nlinarith
    have key := mul_le_mul_of_nonneg_left hband hprod
    linarith
  -- clear denominators on both sides
  set Q := Matrix.dotProduct q q with hQdef
  set R := Matrix.dotProduct q (M *ᵥ q) with hRdef
  set A := (c * Tv) ^ 2 with hAdef
  have hA0 : (0:ℝ) < A := by positivity
  have hDpos : (0:ℝ) < A + s ^ 2 * Q := by nlinarith [hQ0, hA0]
  -- the Rayleigh quotient, denominator-cleared
  have hsub : Ltop - ((A * Ltop + s ^ 2 * R) / (A + s ^ 2 * Q))
      = (Ltop * (A + s ^ 2 * Q) - (A * Ltop + s ^ 2 * R))
        / (A + s ^ 2 * Q) := by
    field_simp
  have hE : (Ltop - Lbot) * s ^ 2 / c ^ 2 / Tv ^ 2
      = ((Ltop - Lbot) * s ^ 2) / (c ^ 2 * Tv ^ 2) := by field_simp
  have hray : rayleigh M x
      = Matrix.dotProduct x (M *ᵥ x) / Matrix.dotProduct x x := by
    unfold rayleigh
    rw [if_neg hx0, quadForm]
  have hAc2 : c ^ 2 * Tv ^ 2 = A := by ring
  rw [hray, hD, hP, hE, hsub, hAc2,
    div_le_div_iff₀ hDpos hA0]
  -- cleared goal: (Ltop * (A + s²Q) − (A·Ltop + s²R)) * A ≤ (Ltop−Lbot)*s²*(A + s²Q)
  have hclear : Ltop * (A + s ^ 2 * Q) - (A * Ltop + s ^ 2 * R)
      = s ^ 2 * (Ltop * Q - R) := by ring
  have hLB : (0:ℝ) ≤ s ^ 2 * (Ltop - Lbot) := by nlinarith [sq_nonneg s, hbotle]
  have hq1 : s ^ 2 * (Ltop * Q - R) * A ≤ s ^ 2 * ((Ltop - Lbot) * Q) * A := by
    have hnn2 : (0:ℝ) ≤ A := le_of_lt hA0
    exact mul_le_mul_of_nonneg_right hstep1 hnn2
  have hq2 : s ^ 2 * ((Ltop - Lbot) * Q) * A
      ≤ s ^ 2 * (Ltop - Lbot) * (A + s ^ 2 * Q) := by
    have hprod : (0:ℝ) ≤ s ^ 2 * (Ltop - Lbot) * Q := by
      nlinarith [hband, hQ0, sq_nonneg s, hbotle]
    nlinarith [hprod, sq_nonneg s, hQ0]
  nlinarith [hclear, hq1, hq2, hQ0, hband, hLB, sq_nonneg s, hbotle,
    hA0]

end Krylov

/-! ### Step 1b: the spectral discharge -/

section KrylovDischarge

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
private theorem dotProduct_sum_right {ι : Type} (F : ι → V → ℝ) (s : Finset ι)
    (v : V → ℝ) :
    v ⬝ᵥ (∑ i ∈ s, F i) = ∑ i ∈ s, (v ⬝ᵥ F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.dotProduct_add, ih]

omit [DecidableEq V] in
private theorem dotProduct_self_eq_zero {v : V → ℝ}
    (h : Matrix.dotProduct v v = 0) : v = 0 := by
  funext i
  have hnn : ∀ j ∈ (Finset.univ : Finset V), 0 ≤ v j * v j :=
    fun j _ => mul_self_nonneg _
  have hsum := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h i (Finset.mem_univ i)
  simpa using mul_self_eq_zero.1 hsum

omit [DecidableEq V] in
/-- Self-adjointness in coordinates at an eigenvector: for symmetric
`M` and `M *ᵥ u = μ • u`, the eigen-equation moves across the dot
product, `u ⬝ᵥ (M *ᵥ y) = μ * (u ⬝ᵥ y)`. Not tied to `eigvecOf` — any
eigenvector qualifies. -/
theorem eigvec_dotProduct_mulVec {M : Matrix V V ℝ} (hM : M.IsSymm)
    {u : V → ℝ} {μ : ℝ} (hu : M *ᵥ u = μ • u) (y : V → ℝ) :
    Matrix.dotProduct u (M *ᵥ y) = μ * Matrix.dotProduct u y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq, hu,
    Matrix.smul_dotProduct, smul_eq_mul]

/-- The power transfer: `u ⬝ᵥ (M ^ j *ᵥ g) = μ ^ j * (u ⬝ᵥ g)` — the
eigenvector equation propagates through matrix powers, the transpose
commuting with powers at symmetric `M`. -/
theorem eigvec_dotProduct_pow_mulVec {M : Matrix V V ℝ} (hM : M.IsSymm)
    {u : V → ℝ} {μ : ℝ} (hu : M *ᵥ u = μ • u) (j : ℕ) (g : V → ℝ) :
    Matrix.dotProduct u ((M ^ j) *ᵥ g) = μ ^ j * Matrix.dotProduct u g := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_pow,
    hM.eq, pow_mulVec_smul M hu, Matrix.smul_dotProduct, smul_eq_mul]

/-- **The polynomial transfer at an eigenvector.** For symmetric `M`,
`u ⬝ᵥ (p(M) *ᵥ g) = (u ⬝ᵥ g) * p.eval μ` — polynomial images of `g`
pair with an eigenvector `u` exactly as scalar multiples by `p(μ)`. In
particular `u ⊥ g` makes every polynomial image of `g` orthogonal to
`u`: the `horth` discharge site. -/
theorem eigvec_dotProduct_aeval_mulVec {M : Matrix V V ℝ} (hM : M.IsSymm)
    {u : V → ℝ} {μ : ℝ} (hu : M *ᵥ u = μ • u) (p : ℝ[X]) (g : V → ℝ) :
    Matrix.dotProduct u ((aeval M p) *ᵥ g)
      = Matrix.dotProduct u g * p.eval μ := by
  have key : ∀ (j : ℕ) (a : ℝ),
      Matrix.dotProduct u ((aeval M (monomial j a)) *ᵥ g)
        = (a * μ ^ j) * Matrix.dotProduct u g := by
    intro j a
    rw [Polynomial.aeval_monomial, scalar_mul_eq_smul,
      Matrix.smul_mulVec_assoc, Matrix.dotProduct_smul, smul_eq_mul,
      eigvec_dotProduct_pow_mulVec hM hu j g]
    ring
  calc Matrix.dotProduct u ((aeval M p) *ᵥ g)
      = Matrix.dotProduct u ((aeval M) (∑ j ∈ Finset.range (p.natDegree + 1),
          monomial j (p.coeff j)) *ᵥ g) := by
        conv_lhs => rw [Polynomial.as_sum_range p]
    _ = Matrix.dotProduct u (∑ j ∈ Finset.range (p.natDegree + 1),
          (aeval M) (monomial j (p.coeff j)) *ᵥ g) := by
        rw [map_sum (aeval M) (fun j => monomial j (p.coeff j))
          (Finset.range (p.natDegree + 1)), sum_mulVec _ _ g]
    _ = ∑ j ∈ Finset.range (p.natDegree + 1),
          Matrix.dotProduct u ((aeval M) (monomial j (p.coeff j)) *ᵥ g) :=
        dotProduct_sum_right _ _ u
    _ = ∑ j ∈ Finset.range (p.natDegree + 1),
          ((p.coeff j * μ ^ j) * Matrix.dotProduct u g) :=
        Finset.sum_congr rfl fun j _ => key j _
    _ = Matrix.dotProduct u g * p.eval μ := by
        rw [← Finset.sum_mul, ← Polynomial.eval_eq_sum_range, mul_comm]

/-- The component form: the `i`-th eigencomponent of a polynomial image
`p(M) y` is `p(μ i)` times the `i`-th component of `y`. -/
theorem eigvecOf_dotProduct_aeval_mulVec {M : Matrix V V ℝ} (hM : M.IsSymm)
    (i : V) (p : ℝ[X]) (y : V → ℝ) :
    Matrix.dotProduct (eigvecOf M hM i) ((aeval M p) *ᵥ y)
      = p.eval (eigvalOf M hM i)
        * Matrix.dotProduct (eigvecOf M hM i) y := by
  have hu : M *ᵥ eigvecOf M hM i
      = eigvalOf M hM i • eigvecOf M hM i :=
    (isHermitian_of_isSymm hM).mulVec_eigenvectorBasis i
  rw [eigvec_dotProduct_aeval_mulVec hM hu p y, mul_comm]

/-- Parseval for polynomial images: the squared norm of `p(M) y`
resolves through the eigenbasis as `∑ (p(μ i))² (v i ⬝ᵥ y)²`. -/
theorem dotProduct_aeval_mulVec_self {M : Matrix V V ℝ} (hM : M.IsSymm)
    (p : ℝ[X]) (y : V → ℝ) :
    Matrix.dotProduct ((aeval M p) *ᵥ y) ((aeval M p) *ᵥ y)
      = ∑ i, (p.eval (eigvalOf M hM i)) ^ 2
        * (Matrix.dotProduct (eigvecOf M hM i) y) ^ 2 := by
  rw [dotProduct_eigvecOf hM _ _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eigvecOf_dotProduct_aeval_mulVec hM i p y]
  ring

/-- The quadratic form of a polynomial image: `quadForm M (p(M) y)`
resolves as `∑ μ i (p(μ i))² (v i ⬝ᵥ y)²`. -/
theorem quadForm_aeval_mulVec {M : Matrix V V ℝ} (hM : M.IsSymm)
    (p : ℝ[X]) (y : V → ℝ) :
    quadForm M ((aeval M p) *ᵥ y)
      = ∑ i, eigvalOf M hM i * (p.eval (eigvalOf M hM i)) ^ 2
        * (Matrix.dotProduct (eigvecOf M hM i) y) ^ 2 := by
  rw [quadForm_eigvalOf hM _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eigvecOf_dotProduct_aeval_mulVec hM i p y]
  ring

/-- The affine band map `w(λ) = (2λ − Ltwo − Lbot)/(Ltwo − Lbot)`: sends
the spectral band `[Lbot, Ltwo]` onto `[-1, 1]` and any `Ltop ≥ Ltwo`
above `1`. The polynomial the Kaniel–Paige argument composes with
`T_{k−1}`. -/
noncomputable def bandMap (Ltwo Lbot : ℝ) : ℝ[X] :=
  Polynomial.C (2 / (Ltwo - Lbot)) * (X - Polynomial.C ((Ltwo + Lbot) / 2))

theorem bandMap_eval (Ltwo Lbot μ : ℝ) :
    (bandMap Ltwo Lbot).eval μ = (2 * μ - Ltwo - Lbot) / (Ltwo - Lbot) := by
  simp only [bandMap, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_sub]
  rw [div_mul_eq_mul_div]
  congr 1
  ring

theorem bandMap_eval_bot (hpos : 0 < Ltwo - Lbot) :
    (bandMap Ltwo Lbot).eval Lbot = -1 := by
  rw [bandMap_eval, div_eq_iff (ne_of_gt hpos)]
  ring

theorem bandMap_eval_two (hpos : 0 < Ltwo - Lbot) :
    (bandMap Ltwo Lbot).eval Ltwo = 1 := by
  rw [bandMap_eval, div_eq_iff (ne_of_gt hpos)]
  ring

theorem abs_bandMap_eval_le_one (hpos : 0 < Ltwo - Lbot)
    (h1 : Lbot ≤ μ) (h2 : μ ≤ Ltwo) :
    |(bandMap Ltwo Lbot).eval μ| ≤ 1 := by
  rw [bandMap_eval, abs_le]
  constructor
  · rw [le_div_iff₀ hpos]
    linarith
  · rw [div_le_iff₀ hpos]
    linarith

theorem one_le_bandMap_eval (hpos : 0 < Ltwo - Lbot) (hL : Ltwo ≤ Ltop) :
    1 ≤ (bandMap Ltwo Lbot).eval Ltop := by
  rw [bandMap_eval, le_div_iff₀ hpos]
  linarith

theorem natDegree_bandMap (h : Ltwo - Lbot ≠ 0) :
    (bandMap Ltwo Lbot).natDegree = 1 := by
  have hC : (Polynomial.C (2 / (Ltwo - Lbot))) ≠ 0 :=
    Polynomial.C_ne_zero.2 (div_ne_zero two_ne_zero h)
  have hX : (X - Polynomial.C ((Ltwo + Lbot) / 2)) ≠ 0 := by
    intro h0
    have hd : (X - Polynomial.C ((Ltwo + Lbot) / 2)).natDegree = 0 := by
      rw [h0]; simp
    rw [Polynomial.natDegree_X_sub_C] at hd
    simp at hd
  rw [bandMap, Polynomial.natDegree_mul hC hX, Polynomial.natDegree_C,
    Polynomial.natDegree_X_sub_C]

omit [DecidableEq V] in
/-- Every unit vector decomposes along a unit vector as
`b = c • u + s • g` with `g ⊥ u`, `‖g‖² ≤ 1`, and `c² + s² = 1` —
`c = u ⬝ᵥ b` is forced by orthogonality, `s² = 1 − c²` by the norm. -/
theorem exists_unit_decomposition (u b : V → ℝ)
    (huu : Matrix.dotProduct u u = 1) (hbb : Matrix.dotProduct b b = 1) :
    ∃ (c s : ℝ) (g : V → ℝ),
      b = c • u + s • g ∧ Matrix.dotProduct u g = 0 ∧
        Matrix.dotProduct g g ≤ 1 ∧ c ^ 2 + s ^ 2 = 1 := by
  classical
  set c : ℝ := Matrix.dotProduct u b with hc
  set g0 : V → ℝ := b - c • u with hg0
  have hbu : Matrix.dotProduct b u = c := by rw [Matrix.dotProduct_comm, hc]
  have hug0 : Matrix.dotProduct u g0 = 0 := by
    rw [hg0, Matrix.dotProduct_sub, Matrix.dotProduct_smul, smul_eq_mul, hc, huu,
      mul_one, sub_self]
  have hng0 : Matrix.dotProduct g0 g0 = 1 - c ^ 2 := by
    have hexp : Matrix.dotProduct g0 g0
        = Matrix.dotProduct b b - c * Matrix.dotProduct b u
          - c * Matrix.dotProduct u b + c * (c * Matrix.dotProduct u u) := by
      rw [hg0]
      simp only [Matrix.dotProduct_sub, Matrix.sub_dotProduct,
        Matrix.dotProduct_smul, Matrix.smul_dotProduct, smul_eq_mul]
      ring
    rw [hexp, hbb, huu, hbu, ← hc]
    ring
  have hnnc : 0 ≤ 1 - c ^ 2 := by
    rw [← hng0]
    unfold Matrix.dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  by_cases hz : 1 - c ^ 2 = 0
  · have hg0z : g0 = 0 := dotProduct_self_eq_zero (by rw [← hz]; exact hng0)
    refine ⟨c, 0, 0, ?_, by simp, by simp, ?_⟩
    · simp only [smul_zero, add_zero]
      rw [hg0z] at hg0
      exact sub_eq_zero.1 hg0.symm
    · have hcc : c ^ 2 = 1 := by linarith
      simp [hcc]
  · have hpos : 0 < 1 - c ^ 2 := lt_of_le_of_ne hnnc (Ne.symm hz)
    set s : ℝ := Real.sqrt (1 - c ^ 2) with hs
    have hspos : 0 < s := Real.sqrt_pos.2 hpos
    have hssq : s ^ 2 = 1 - c ^ 2 := Real.sq_sqrt hnnc
    refine ⟨c, s, s⁻¹ • g0, ?_, ?_, ?_, ?_⟩
    · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hspos), one_smul, hg0]
      ring
    · rw [Matrix.dotProduct_smul, hug0, smul_zero]
    · have hkey : s⁻¹ * (s⁻¹ * s ^ 2) = 1 := by
        field_simp
        ring
      rw [Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_eq_mul, smul_eq_mul,
        hng0, ← hssq, hkey]
    · rw [hssq]
      ring

set_option maxHeartbeats 800000 in
/-- **The Kaniel–Paige bound at the Chebyshev band polynomial — the
spectral discharge complete.** For symmetric `M` with unit top
eigenvector `u` at `Ltop`, a starting vector decomposed as
`b = c • u + s • g` with `g ⊥ u` of norm ≤ 1, and the eigenbasis-level
band hypothesis (`hpar`: every eigenvector at an eigenvalue outside
`[Lbot, Ltwo]` is a multiple of `u` — with `Ltwo ≤ Ltop` this says the
only eigenvalue above `Ltwo` is the simple top one), the `k`-th Krylov
space contains a nonzero vector whose Rayleigh quotient is within
`(Ltop − Lbot) s²/c² / T_{k−1}(w(Ltop))²` of the top eigenvalue, at the
affine band map `w(λ) = (2λ − Ltwo − Lbot)/(Ltwo − Lbot)`.

Every spectral-layer hypothesis of `kanielPaigeSkeleton` is discharged
here from the shelf's eigenbasis machinery: `horth`/`horthM` by the
general-eigenvector transfer, `hband`/`hbottom` by Parseval and the
quadratic-form resolution through `eigvecOf` components with the
Chebyshev band bound `|T ∘ w| ≤ 1`, `hp₁`/`hdeg`/`hTv` by
`natDegree_T`, `natDegree_comp`, and the growth lemma. -/
theorem kanielPaigeChebyshev (M : Matrix V V ℝ) (hM : M.IsSymm)
    (b u g : V → ℝ) (c s Ltop Ltwo Lbot : ℝ) (k : ℕ)
    (hb : b = c • u + s • g)
    (hu : M *ᵥ u = Ltop • u)
    (huu : Matrix.dotProduct u u = 1)
    (hgu : Matrix.dotProduct u g = 0)
    (hgg : Matrix.dotProduct g g ≤ 1)
    (hc : c ≠ 0)
    (hLbot : Lbot < Ltwo) (hLtwo : Ltwo ≤ Ltop)
    (hpar : ∀ i : V, ¬(Lbot ≤ eigvalOf M hM i ∧ eigvalOf M hM i ≤ Ltwo) →
      ∃ t : ℝ, eigvecOf M hM i = t • u)
    (hk : 1 ≤ k) :
    ∃ x ∈ krylovSpan M b k, x ≠ 0 ∧
      Ltop - rayleigh M x ≤ (Ltop - Lbot) * s ^ 2 / c ^ 2 /
        ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
          (bandMap Ltwo Lbot)).eval Ltop ^ 2 := by
  have hpos : 0 < Ltwo - Lbot := sub_pos.2 hLbot
  -- Tv and its growth
  have hTv : 1 ≤ ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
      (bandMap Ltwo Lbot)).eval Ltop := by
    rw [Polynomial.eval_comp]
    exact one_le_eval_T_of_one_le (one_le_bandMap_eval hpos hLtwo) _
  -- the degree side condition
  have hdeg : ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
      (bandMap Ltwo Lbot)).natDegree < k := by
    rw [Polynomial.natDegree_comp, natDegree_T, natDegree_bandMap (ne_of_gt hpos)]
    omega
  -- the band/parallel dichotomy
  have hdich : ∀ i : V, Matrix.dotProduct (eigvecOf M hM i) g ≠ 0 →
      Lbot ≤ eigvalOf M hM i ∧ eigvalOf M hM i ≤ Ltwo := by
    intro i hi
    by_contra hnb
    obtain ⟨t, ht⟩ := hpar i hnb
    rw [ht, Matrix.smul_dotProduct, hgu, smul_zero] at hi
    exact hi rfl
  -- the Chebyshev band bound at in-band eigenvalues
  have hpband : ∀ i : V, Lbot ≤ eigvalOf M hM i → eigvalOf M hM i ≤ Ltwo →
      ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
          (bandMap Ltwo Lbot)).eval (eigvalOf M hM i) ^ 2 ≤ 1 := by
    intro i h1 h2
    have habs : |((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
        (bandMap Ltwo Lbot)).eval (eigvalOf M hM i)| ≤ 1 := by
      rw [Polynomial.eval_comp]
      have hw := abs_le.1 (abs_bandMap_eval_le_one hpos h1 h2)
      exact abs_T_eval_le_one _ hw.1 hw.2
    have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rwa [sq_abs, one_pow] at hsq
  -- horth: the polynomial transfer at the orthogonal complement
  have horth : Matrix.dotProduct u
      ((aeval M ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
        (bandMap Ltwo Lbot))) *ᵥ g) = 0 := by
    rw [eigvec_dotProduct_aeval_mulVec hM hu _ g, hgu, zero_mul]
  have horthM : Matrix.dotProduct u (M *ᵥ
      ((aeval M ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
        (bandMap Ltwo Lbot))) *ᵥ g)) = 0 := by
    rw [eigvec_dotProduct_mulVec hM hu _, horth, mul_zero]
  -- the norm resolution
  have hqq : Matrix.dotProduct
      ((aeval M ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
        (bandMap Ltwo Lbot))) *ᵥ g)
      ((aeval M ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
        (bandMap Ltwo Lbot))) *ᵥ g)
      = ∑ i, (((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
          (bandMap Ltwo Lbot)).eval (eigvalOf M hM i)) ^ 2
        * (Matrix.dotProduct (eigvecOf M hM i) g) ^ 2 :=
    dotProduct_aeval_mulVec_self hM _ g
  -- hband
  have hband : Matrix.dotProduct
      ((aeval M ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
        (bandMap Ltwo Lbot))) *ᵥ g)
      ((aeval M ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
        (bandMap Ltwo Lbot))) *ᵥ g) ≤ 1 := by
    have h1 : ∑ i, (((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
          (bandMap Ltwo Lbot)).eval (eigvalOf M hM i)) ^ 2
        * (Matrix.dotProduct (eigvecOf M hM i) g) ^ 2
        ≤ ∑ i, (Matrix.dotProduct (eigvecOf M hM i) g) ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases h0 : Matrix.dotProduct (eigvecOf M hM i) g = 0
      · simp [h0]
      · have hle := hpband i (hdich i h0).1 (hdich i h0).2
        have hnn : (0:ℝ) ≤ (Matrix.dotProduct (eigvecOf M hM i) g) ^ 2 :=
          sq_nonneg _
        have := mul_le_mul_of_nonneg_right hle hnn
        linarith
    have h2 : Matrix.dotProduct g g
        = ∑ i, (Matrix.dotProduct (eigvecOf M hM i) g) ^ 2 := by
      rw [dotProduct_eigvecOf hM g g]
      exact Finset.sum_congr rfl fun i _ => (sq _).symm
    rw [hqq]
    linarith
  -- hbottom
  have hbottom : Lbot * Matrix.dotProduct
      ((aeval M ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
        (bandMap Ltwo Lbot))) *ᵥ g)
      ((aeval M ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
        (bandMap Ltwo Lbot))) *ᵥ g)
      ≤ Matrix.dotProduct
          ((aeval M ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
            (bandMap Ltwo Lbot))) *ᵥ g)
          (M *ᵥ ((aeval M ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
            (bandMap Ltwo Lbot))) *ᵥ g)) := by
    have hQM : Matrix.dotProduct
        ((aeval M ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
          (bandMap Ltwo Lbot))) *ᵥ g)
        (M *ᵥ ((aeval M ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
          (bandMap Ltwo Lbot))) *ᵥ g))
        = ∑ i, eigvalOf M hM i
          * (((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
              (bandMap Ltwo Lbot)).eval (eigvalOf M hM i)) ^ 2
          * (Matrix.dotProduct (eigvecOf M hM i) g) ^ 2 :=
      quadForm_aeval_mulVec hM _ g
    rw [hqq, hQM, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h0 : Matrix.dotProduct (eigvecOf M hM i) g = 0
    · simp [h0]
    · have hnn : (0:ℝ) ≤ (((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
          (bandMap Ltwo Lbot)).eval (eigvalOf M hM i)) ^ 2
          * (Matrix.dotProduct (eigvecOf M hM i) g) ^ 2 :=
        by positivity
      have hb := (hdich i h0).1
      calc Lbot * ((((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
            (bandMap Ltwo Lbot)).eval (eigvalOf M hM i)) ^ 2
          * (Matrix.dotProduct (eigvecOf M hM i) g) ^ 2)
          ≤ eigvalOf M hM i * ((((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
              (bandMap Ltwo Lbot)).eval (eigvalOf M hM i)) ^ 2
            * (Matrix.dotProduct (eigvecOf M hM i) g) ^ 2) :=
            mul_le_mul_of_nonneg_right hb hnn
        _ = eigvalOf M hM i
            * (((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
                (bandMap Ltwo Lbot)).eval (eigvalOf M hM i)) ^ 2
            * (Matrix.dotProduct (eigvecOf M hM i) g) ^ 2 := by ring
  -- assemble
  exact kanielPaigeSkeleton M b u g c s Ltop Lbot
    (((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
      (bandMap Ltwo Lbot)).eval Ltop) k
    ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp (bandMap Ltwo Lbot))
    hb hu huu hc hTv
    (le_trans (le_of_lt hLbot) hLtwo) hdeg rfl horth horthM hbottom hband

/-! ### Step 1c: the final statement -/

/-- **The Kaniel–Paige bound for the Lanczos starting vector (final
form).** For symmetric `M` with a unit eigenvector `u` at the top
eigenvalue `Ltop`, a unit starting vector `b` with a component on `u`
(`u ⬝ᵥ b ≠ 0`), the eigenbasis-level band hypothesis (`hpar`: every
eigenvector at an eigenvalue outside `[Lbot, Ltwo]` is a multiple of
`u` — with `Lbot < Ltwo ≤ Ltop` this says the bulk spectrum lies in the
band and the only eigenvalue above it is the simple top one), and
`k ≥ 1`, the `k`-th Krylov space `K_k(M, b) = span{b, Mb, …, Mᵏ⁻¹ b}`
contains a nonzero vector whose Rayleigh quotient is within

`(Ltop − Lbot) · tan²φ / T_{k−1}(1 + 2γ)²`,  `γ = (Ltop − Ltwo)/(Ltwo − Lbot)`,

of the top eigenvalue, where `tan φ` is the angle between `b` and `u`,
`tan²φ = (1 − (u ⬝ᵥ b)²)/(u ⬝ᵥ b)²` — the unit decomposition
`b = cos φ • u + sin φ • g` is supplied internally by
`exists_unit_decomposition` (via `c = u ⬝ᵥ b` and `s² = 1 − c²`), and
the affine band map's value `w(Ltop) = 1 + 2γ` restates
`kanielPaigeChebyshev`'s composed Chebyshev value in the classical
gap form. This is the classical Kaniel–Paige bound: Saad, *Numerical
Methods for Large Eigenvalue Problems*, 2nd ed., §6 — the locator is
recorded at chapter/section level by
`proposals/approximate-spectral-projection.md` (which owns this
program's statement) and, per that proposal's clean-room note, is to be
confirmed against the physical copy before any committed external use;
the statement itself is proved here, not admitted. No Lanczos
tridiagonalization and no finite-precision claims — the exact-arithmetic
variational content only. -/
theorem kanielPaige (M : Matrix V V ℝ) (hM : M.IsSymm)
    (u b : V → ℝ) (Ltop Ltwo Lbot : ℝ) (k : ℕ)
    (hu : M *ᵥ u = Ltop • u)
    (huu : Matrix.dotProduct u u = 1)
    (hbb : Matrix.dotProduct b b = 1)
    (hub : Matrix.dotProduct u b ≠ 0)
    (hLbot : Lbot < Ltwo) (hLtwo : Ltwo ≤ Ltop)
    (hpar : ∀ i : V, ¬(Lbot ≤ eigvalOf M hM i ∧ eigvalOf M hM i ≤ Ltwo) →
      ∃ t : ℝ, eigvecOf M hM i = t • u)
    (hk : 1 ≤ k) :
    ∃ x ∈ krylovSpan M b k, x ≠ 0 ∧
      Ltop - rayleigh M x
        ≤ (Ltop - Lbot) * (1 - (Matrix.dotProduct u b) ^ 2)
            / (Matrix.dotProduct u b) ^ 2
          / (Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).eval
              (1 + 2 * (Ltop - Ltwo) / (Ltwo - Lbot)) ^ 2 := by
  obtain ⟨c, s, g, hb, hgu, hgg, hcs⟩ :=
    exists_unit_decomposition u b huu hbb
  have huc : Matrix.dotProduct u b = c := by
    rw [hb, Matrix.dotProduct_add]
    simp [huu, hgu]
  have hc0 : c ≠ 0 := by rw [← huc]; exact hub
  have hs2 : s ^ 2 = 1 - (Matrix.dotProduct u b) ^ 2 := by
    rw [← huc] at hcs
    linear_combination hcs
  have hne : (Ltwo - Lbot : ℝ) ≠ 0 := ne_of_gt (sub_pos.2 hLbot)
  have hTv : ((Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).comp
      (bandMap Ltwo Lbot)).eval Ltop
      = (Polynomial.Chebyshev.T ℝ ((k - 1 : ℕ) : ℤ)).eval
          (1 + 2 * (Ltop - Ltwo) / (Ltwo - Lbot)) := by
    rw [Polynomial.eval_comp, bandMap_eval]
    congr 1
    field_simp
    ring
  obtain ⟨x, hxmem, hx0, hxbound⟩ :=
    kanielPaigeChebyshev M hM b u g c s Ltop Ltwo Lbot k
      hb hu huu hgu hgg hc0 hLbot hLtwo hpar hk
  refine ⟨x, hxmem, hx0, ?_⟩
  rw [hTv, hs2, ← huc] at hxbound
  exact hxbound

end KrylovDischarge

end SpectralGraphTheory
