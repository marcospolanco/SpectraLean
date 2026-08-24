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
import Scaffold.Mathlib.GraphTheory.PolyFilter
import Scaffold.Mathlib.GraphTheory.ClusterProjector
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Duhamel
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.ProjectionGap

/-!
# Band Davis–Kahan — perturbation stability for band projectors

`proposals/band-davis-kahan.md` (backlog item 9 of
`docs/6_SGT_BACKLOG.md`, opened by the Davis–Kahan Step-0/1 survey of
`proposals/discharge-perturbation-axioms.md`): the **bounded-window**
Davis–Kahan theorem. If `P` and `Q` are the band projectors of two
symmetric matrices `A` and `B` on δ-separated spectral windows, then

```
‖Q * P‖ ≤ ‖A - B‖ / δ
```

— the product of the two band projectors is small inversely to the
window separation and the perturbation size. This is the bounded-window
sibling of the proved half-line theorem `davis_kahan_sin_theta`
(`Perturbation/DavisKahan.lean`, the Duhamel route): the two are
genuinely different statements, and neither substitutes for the other
(the recorded catch: the shift technique needs a finite containment
radius, which the half-line window does not provide).

`proposals/band-davis-kahan-difference.md` (the product theorem's own
recorded follow-on): the **difference form** of the same theorem —

```
‖P_A - P_B‖ ≤ ‖A - B‖ / δ
```

for band projectors of *equal rank*, under one-sided eigenvalue
separation (B's out-of-window eigenvalues δ-away from A's window
closure `[a₁, b₁]`), at constant 1 — the classical Davis–Kahan sin-Θ
(subspace-distance) shape, delivered through the equal-rank gap
identity `l2OpNorm_sub_eq_of_rank_eq` (its first consumer) plus the
same commutator/shift engine re-run at the complement projector
`Q' = 1 - Q` (see the `DifferenceForm` sections below).

`proposals/band-davis-kahan-cluster.md` then generalized the
separation to the literal Yu–Wang–Samworth pairwise δ, and
`proposals/band-davis-kahan-symmetric.md` (the cluster form's own
recorded follow-on) delivers the **two-sided (both-separations)
form** — separation on both out-of-window flanks at constant 2, with
**no rank hypothesis at all** (the both-gaps dimension-freeness; see
the `SymmetricForm` sections) — plus the public interface lemma
`l2OpNorm_transpose` (absent from the pinned Mathlib and the shelf).

## The route (pure algebra, no calculus)

The survey's commutator/shift technique. Center `A`'s window at
`c = (a₁ + b₁)/2` with radius `r = (b₁ - a₁)/2`; every `B`-eigenvalue
in its window is then at distance `≥ r + δ` from `c` (interval
arithmetic). Two per-vector facts, each by the eigenbasis component
action (`eigvecOf_dotProduct_bandProjector_mulVec`, PolyFilter) plus
Parseval (`dotProduct_eigvecOf`, Spectral):

- **compression** — `‖(A - cI) *ᵥ (P *ᵥ y)‖ ≤ r * ‖y‖`: the shifted
  action's eigencomponents are `(λ i - c) χ i (v i ⬝ᵥ y)`, each factor
  bounded by `r` in-band and annihilated out-of-band;
- **expansion** — `(r + δ) * ‖z‖ ≤ ‖(B - cI) *ᵥ z‖` for `z` fixed by
  `Q`: `z`'s eigencomponents are supported in `B`'s window, where
  `|μ j - c| ≥ r + δ`.

**The crux** (worked through in the proposal before any Lean): the
naive single-shift assembly strands `+ r` — the containment-spread term
that kills this technique at the half-line window. The rescue is
*range invariance*: `(A - cI) *ᵥ (P *ᵥ y)` stays in `P`'s range (its
out-of-band components vanish), so `Q *ᵥ w = (Q * P) *ᵥ w` and the
A-compressed term is bounded by `r * ‖Q * P‖ * ‖y‖` rather than
`r * ‖y‖` — the `r` then cancels algebraically:

`(r + δ) ‖(Q*P) *ᵥ y‖ ≤ (r ‖Q*P‖ + ‖A - B‖) ‖y‖` for every `y`,
transported to norms by the Duhamel pairing engine
(`l2OpNorm_le_of_abs_dotProduct_le`), gives
`δ ‖Q * P‖ ≤ ‖A - B‖`. Constant 1, no integral, no sorting, no rank
counting — the bounded window is load-bearing twice (finite `r`, and
the invariance step).

## Statement provenance

The statement is *proved*, not admitted — this module adds no axioms.
Route provenance: Vershynin, *High-Dimensional Probability*, 2018,
Thm 4.1.15–4.1.16 (the textbook packaging of this commutator/shift
technique; `index/sources/vershynin_hdp.md`, Chapter 4 note — locator
carried with the repo's standing verify-against-physical-copy caveat).
The classical statement: Davis & Kahan 1970 / Yu–Wang–Samworth 2015
Theorem 1, specialized from eigenvalue-cluster separation to interval
separation. Statement differences from the textbook packaging
(recorded in the proposal before stating): windows are
`bandProjector`'s own `(a, b]` convention; the conclusion is the
operator norm of the *product* `Q * P` (no rank hypothesis needed or
stated); separation is interval separation (`b₁ + δ ≤ a₂` or
`b₂ + δ ≤ a₁`), from which eigenvalue separation follows inside the
proof.

QA: `Scaffold/QA/Perturbation/BandDavisKahan_QA.lean` — the rotated
2×2 witness with `‖Q * P‖` pinned from below through the eigenbasis,
the ε = 0 commuting attainment, the overlapping-window fence refuted
in proved form, and the mirror-theorem instance; and
`Scaffold/QA/Perturbation/BandDavisKahanDiff_QA.lean` — the difference
form's positive two-route witness, its ε = 0 attainment, the
margin-corollary instance, and the rank-hypothesis fence refuted in
proved form.
-/

open scoped BigOperators Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation

open SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Interface lemmas

Two shelf gaps priced by the proposal's Step-0 survey and landed here:
the vector action bound, and the operator↔projector commutation at the
vector level (the 2026-08-21 survey's spike-verified fact, previously
unlanded because the Duhamel route did not need it). -/

section Interface

/-- The packaging of a plain vector as a `EuclideanSpace` element (the
norm spine's carrier). -/
private noncomputable abbrev pack (x : V → ℝ) : EuclideanSpace ℝ V :=
  (WithLp.equiv 2 (V → ℝ)).symm x

omit [DecidableEq V] in
private theorem nonneg_dotProduct_self (x : V → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

omit [Fintype V] [DecidableEq V] in
private theorem pack_add (x y : V → ℝ) :
    pack (x + y) = pack x + pack y := by
  apply (WithLp.equiv 2 (V → ℝ)).injective
  rw [WithLp.equiv_add]
  simp only [Equiv.apply_symm_apply]

omit [DecidableEq V] in
private theorem norm_pack_sq (x : V → ℝ) : ‖pack x‖ ^ 2 = x ⬝ᵥ x := by
  rw [pow_two, norm_euclidean_eq_sqrt,
    Real.mul_self_sqrt (nonneg_dotProduct_self x)]

/-- **The vector action bound.** The ℓ² operator norm bounds the
action on every vector, in the plain sqrt-of-dot-product packaging —
the reverse direction of `ContinuousLinearMap.opNorm_le_bound`,
transported through the C*-norm spine (`Matrix.cstar_norm_def` +
`toEuclideanCLM`). Reusable by every perturbation consumer that needs
to *lower*-bound a matrix norm by a single action (QA's raw witnesses
consume it at a unit vector). -/
theorem l2OpNorm_mulVec_le (M : Matrix V V ℝ) (v : V → ℝ) :
    ‖pack (M *ᵥ v)‖ ≤ ‖M‖ * ‖pack v‖ := by
  have h := ContinuousLinearMap.le_opNorm
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) M :
      EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V))
    (pack v)
  rw [Matrix.toEuclideanCLM_piLp_equiv_symm, ← Matrix.cstar_norm_def] at h
  exact h

/-- Two vectors with identical eigenbasis components are equal (basis
injectivity, through the entrywise expansion). -/
private theorem eq_of_forall_dotProduct_eigvecOf_eq {M : Matrix V V ℝ}
    (hM : M.IsSymm) (x y : V → ℝ)
    (h : ∀ i, Matrix.dotProduct (eigvecOf M hM i) x
      = Matrix.dotProduct (eigvecOf M hM i) y) : x = y := by
  funext a
  have hx := eigvecOf_expansion_apply hM x a
  have hy := eigvecOf_expansion_apply hM y a
  rw [← hx, ← hy]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

/-- A self-adjoint matrix commutes with its own threshold projector, at
the vector level. Componentwise: both sides' eigencomponents are
`χ(μ i ≤ c) * μ i * (v i ⬝ᵥ u)` — the eigenaction
(`dotProduct_eigvecOf_mulVec`) against the component action
(`eigvecOf_dotProduct_spectralProjector_mulVec`). -/
theorem mulVec_spectralProjector_comm {M : Matrix V V ℝ} (hM : M.IsSymm)
    (c : ℝ) (u : V → ℝ) :
    M *ᵥ ((spectralProjector M hM c) *ᵥ u)
      = (spectralProjector M hM c) *ᵥ (M *ᵥ u) := by
  refine eq_of_forall_dotProduct_eigvecOf_eq hM _ _ fun i => ?_
  rw [dotProduct_eigvecOf_mulVec hM i,
    eigvecOf_dotProduct_spectralProjector_mulVec hM c i,
    eigvecOf_dotProduct_spectralProjector_mulVec hM c i,
    dotProduct_eigvecOf_mulVec hM i]
  ring_nf

/-- The band form: a self-adjoint matrix commutes with its own band
projector (the difference of two threshold commutations; no `a ≤ b`
guard — the identity is linear in the projector). -/
theorem mulVec_bandProjector_comm {M : Matrix V V ℝ} (hM : M.IsSymm)
    (a b : ℝ) (u : V → ℝ) :
    M *ᵥ ((bandProjector M hM a b) *ᵥ u)
      = (bandProjector M hM a b) *ᵥ (M *ᵥ u) := by
  have hL : M *ᵥ (bandProjector M hM a b *ᵥ u)
      = M *ᵥ (spectralProjector M hM b *ᵥ u)
        - M *ᵥ (spectralProjector M hM a *ᵥ u) := by
    rw [bandProjector, Matrix.sub_mulVec, Matrix.mulVec_sub]
  have hR : bandProjector M hM a b *ᵥ (M *ᵥ u)
      = spectralProjector M hM b *ᵥ (M *ᵥ u)
        - spectralProjector M hM a *ᵥ (M *ᵥ u) := by
    rw [bandProjector, Matrix.sub_mulVec]
  rw [hL, hR, mulVec_spectralProjector_comm hM b u,
    mulVec_spectralProjector_comm hM a u]

end Interface

/-! ## The engine

Private per-vector layers: the two Parseval facts (compression,
expansion), range invariance, and the band contractivity of the action;
then the core assembly at eigenvalue-window form. -/

section Engine

variable {A B : Matrix V V ℝ}

/-- **(F1) compression:** the shifted action on `A`'s band-filtered
vector has norm at most `r * ‖y‖`, whenever every in-band eigenvalue of
`A` lies within `r` of `c`. -/
private theorem norm_pack_shift_bandProjector_mulVec_le (hA : A.IsSymm)
    (a₁ b₁ c r : ℝ) (hab : a₁ ≤ b₁) (hr : 0 ≤ r)
    (hnear : ∀ i, a₁ < eigvalOf A hA i → eigvalOf A hA i ≤ b₁ →
      |eigvalOf A hA i - c| ≤ r)
    (y : V → ℝ) :
    ‖pack ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y))‖
      ≤ r * ‖pack y‖ := by
  have hcomp : ∀ i : V, Matrix.dotProduct (eigvecOf A hA i)
      ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y))
      = (eigvalOf A hA i - c)
        * (if a₁ < eigvalOf A hA i ∧ eigvalOf A hA i ≤ b₁ then (1 : ℝ) else 0)
        * Matrix.dotProduct (eigvecOf A hA i) y := by
    intro i
    simp only [Matrix.sub_mulVec, Matrix.dotProduct_sub,
      dotProduct_eigvecOf_mulVec hA,
      eigvecOf_dotProduct_bandProjector_mulVec hA a₁ b₁ hab,
      Matrix.smul_mulVec_assoc, Matrix.one_mulVec, Matrix.mulVec_smul,
      Matrix.dotProduct_smul, smul_eq_mul, sub_mul]
    ring
  have hsq : ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y)) ⬝ᵥ
      ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y))
      ≤ r * r * (y ⬝ᵥ y) := by
    have hterm : ∀ i : V,
        (Matrix.dotProduct (eigvecOf A hA i)
          ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y)))
          * (Matrix.dotProduct (eigvecOf A hA i)
          ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y)))
        ≤ (r * r)
          * (Matrix.dotProduct (eigvecOf A hA i) y
            * Matrix.dotProduct (eigvecOf A hA i) y) := by
      intro i
      rw [hcomp i]
      by_cases hband : a₁ < eigvalOf A hA i ∧ eigvalOf A hA i ≤ b₁
      · rw [if_pos hband, mul_one]
        have habs := hnear i hband.1 hband.2
        obtain ⟨hl, hu⟩ := abs_le.mp habs
        have hkey : (eigvalOf A hA i - c) * (eigvalOf A hA i - c) ≤ r * r := by
          have := sq_le_sq' hl hu
          simpa [sq] using this
        nlinarith [hkey, mul_self_nonneg
          (Matrix.dotProduct (eigvecOf A hA i) y)]
      · rw [if_neg hband]
        have hzero : ((eigvalOf A hA i - c) * (0 : ℝ)
            * Matrix.dotProduct (eigvecOf A hA i) y)
            * ((eigvalOf A hA i - c) * (0 : ℝ)
            * Matrix.dotProduct (eigvecOf A hA i) y) = 0 := by ring
        rw [hzero]
        exact mul_nonneg (mul_nonneg hr hr) (mul_self_nonneg _)
    rw [dotProduct_eigvecOf hA ((A - c • 1) *ᵥ
      (bandProjector A hA a₁ b₁ *ᵥ y)) ((A - c • 1) *ᵥ
      (bandProjector A hA a₁ b₁ *ᵥ y))]
    calc ∑ i : V, (Matrix.dotProduct (eigvecOf A hA i)
          ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y)))
          * (Matrix.dotProduct (eigvecOf A hA i)
          ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y)))
        ≤ ∑ i : V, (r * r)
            * (Matrix.dotProduct (eigvecOf A hA i) y
              * Matrix.dotProduct (eigvecOf A hA i) y) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = r * r * (y ⬝ᵥ y) := by
          rw [show y ⬝ᵥ y = ∑ i, Matrix.dotProduct (eigvecOf A hA i) y
              * Matrix.dotProduct (eigvecOf A hA i) y from
            dotProduct_eigvecOf hA y y, ← Finset.mul_sum]
  have hnn : 0 ≤ ‖pack ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y))‖ :=
    norm_nonneg _
  have hnn' : 0 ≤ ‖pack y‖ := norm_nonneg _
  have hsqrt : ‖pack ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y))‖ ^ 2
      ≤ (r * ‖pack y‖) ^ 2 := by
    rw [mul_pow, norm_pack_sq, norm_pack_sq, pow_two]
    exact hsq
  have habs := abs_le_of_sq_le_sq hsqrt (mul_nonneg hr hnn')
  rwa [abs_of_nonneg hnn] at habs

/-- **Range invariance:** the shifted band-filtered vector stays in the
band's range — its out-of-band eigencomponents vanish, so the band
projector fixes it. This is the step that makes the window radius
cancel in the main assembly (the proposal's crux). -/
private theorem bandProjector_mulVec_shift_self (hA : A.IsSymm)
    (a₁ b₁ c : ℝ) (hab : a₁ ≤ b₁) (y : V → ℝ) :
    bandProjector A hA a₁ b₁ *ᵥ ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y))
      = (A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y) := by
  refine eq_of_forall_dotProduct_eigvecOf_eq hA _ _ fun i => ?_
  rw [eigvecOf_dotProduct_bandProjector_mulVec hA a₁ b₁ hab i]
  have hcomp : Matrix.dotProduct (eigvecOf A hA i)
      ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y))
      = (eigvalOf A hA i - c)
        * (if a₁ < eigvalOf A hA i ∧ eigvalOf A hA i ≤ b₁ then (1 : ℝ) else 0)
        * Matrix.dotProduct (eigvecOf A hA i) y := by
    simp only [Matrix.sub_mulVec, Matrix.dotProduct_sub,
      dotProduct_eigvecOf_mulVec hA,
      eigvecOf_dotProduct_bandProjector_mulVec hA a₁ b₁ hab,
      Matrix.smul_mulVec_assoc, Matrix.one_mulVec, Matrix.mulVec_smul,
      Matrix.dotProduct_smul, smul_eq_mul, sub_mul]
    ring
  rw [hcomp]
  by_cases hband : a₁ < eigvalOf A hA i ∧ eigvalOf A hA i ≤ b₁
  · rw [if_pos hband, one_mul]
  · rw [if_neg hband]
    ring

/-- **(F2) expansion:** for a vector fixed by `B`'s band projector, the
shifted action expands by at least `r + δ` whenever every in-band
eigenvalue of `B` lies at distance `≥ r + δ` from `c`. -/
private theorem norm_pack_shift_apply_ge (hB : B.IsSymm)
    (a₂ b₂ c r δ : ℝ) (hab₂ : a₂ ≤ b₂) (hrδ : 0 ≤ r + δ)
    (hfar : ∀ j, a₂ < eigvalOf B hB j → eigvalOf B hB j ≤ b₂ →
      r + δ ≤ |eigvalOf B hB j - c|)
    (z : V → ℝ) (hz : bandProjector B hB a₂ b₂ *ᵥ z = z) :
    (r + δ) * ‖pack z‖ ≤ ‖pack ((B - c • 1) *ᵥ z)‖ := by
  have hzcomp : ∀ j, Matrix.dotProduct (eigvecOf B hB j) z
      = (if a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂ then (1 : ℝ) else 0)
        * Matrix.dotProduct (eigvecOf B hB j) z := by
    intro j
    calc Matrix.dotProduct (eigvecOf B hB j) z
        = Matrix.dotProduct (eigvecOf B hB j)
            (bandProjector B hB a₂ b₂ *ᵥ z) := by rw [hz]
      _ = (if a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂ then (1 : ℝ) else 0)
          * Matrix.dotProduct (eigvecOf B hB j) z :=
          eigvecOf_dotProduct_bandProjector_mulVec hB a₂ b₂ hab₂ j z
  have hcomp : ∀ j, Matrix.dotProduct (eigvecOf B hB j) ((B - c • 1) *ᵥ z)
      = (eigvalOf B hB j - c) * Matrix.dotProduct (eigvecOf B hB j) z := by
    intro j
    simp only [Matrix.sub_mulVec, Matrix.dotProduct_sub,
      dotProduct_eigvecOf_mulVec hB,
      Matrix.smul_mulVec_assoc, Matrix.one_mulVec, Matrix.mulVec_smul,
      Matrix.dotProduct_smul, smul_eq_mul, sub_mul]
  have hsum : (r + δ) * (r + δ) * (z ⬝ᵥ z)
      ≤ ((B - c • 1) *ᵥ z) ⬝ᵥ ((B - c • 1) *ᵥ z) := by
    have hsplit : (r + δ) * (r + δ) * (z ⬝ᵥ z)
        = ∑ j, (r + δ) * (r + δ)
          * (Matrix.dotProduct (eigvecOf B hB j) z
            * Matrix.dotProduct (eigvecOf B hB j) z) := by
      rw [dotProduct_eigvecOf hB z z, ← Finset.mul_sum]
    rw [hsplit, dotProduct_eigvecOf hB ((B - c • 1) *ᵥ z)
      ((B - c • 1) *ᵥ z)]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hcomp j, hzcomp j]
    by_cases hband : a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂
    · rw [if_pos hband, one_mul]
      have habs := hfar j hband.1 hband.2
      have hkey : (r + δ) * (r + δ)
          ≤ (eigvalOf B hB j - c) * (eigvalOf B hB j - c) :=
        le_trans (mul_self_le_mul_self hrδ habs) (le_of_eq (abs_mul_abs_self _))
      nlinarith [hkey, mul_self_nonneg (Matrix.dotProduct (eigvecOf B hB j) z)]
    · simp [hband]
  have hnn : 0 ≤ ‖pack z‖ := norm_nonneg _
  have hnn' : 0 ≤ ‖pack ((B - c • 1) *ᵥ z)‖ := norm_nonneg _
  have hsqrt : ((r + δ) * ‖pack z‖) ^ 2
      ≤ ‖pack ((B - c • 1) *ᵥ z)‖ ^ 2 := by
    rw [mul_pow, norm_pack_sq, norm_pack_sq, pow_two]
    exact hsum
  have habs := abs_le_of_sq_le_sq hsqrt hnn'
  rwa [abs_of_nonneg (mul_nonneg hrδ hnn)] at habs

/-- The band projector's action is contractive (Parseval + component
action: the filtered signal's squared norm is a sub-sum of the input's
eigencomponent energy). -/
private theorem norm_pack_bandProjector_mulVec_le {M : Matrix V V ℝ}
    (hM : M.IsSymm) (a b : ℝ) (hab : a ≤ b) (y : V → ℝ) :
    ‖pack (bandProjector M hM a b *ᵥ y)‖ ≤ ‖pack y‖ := by
  have hsq : (bandProjector M hM a b *ᵥ y) ⬝ᵥ (bandProjector M hM a b *ᵥ y)
      ≤ y ⬝ᵥ y := by
    rw [dotProduct_eigvecOf hM (bandProjector M hM a b *ᵥ y)
      (bandProjector M hM a b *ᵥ y), dotProduct_eigvecOf hM y y]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [eigvecOf_dotProduct_bandProjector_mulVec hM a b hab i y]
    by_cases hband : a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b
    · rw [if_pos hband, one_mul]
    · rw [if_neg hband, zero_mul, zero_mul]
      exact mul_self_nonneg _
  have habs : |‖pack (bandProjector M hM a b *ᵥ y)‖| ≤ ‖pack y‖ := by
    refine abs_le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [norm_pack_sq, norm_pack_sq]
    exact hsq
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- The shifted band commutation (the scalar shift commutes with
everything). -/
private theorem mulVec_bandProjector_comm_shift {M : Matrix V V ℝ}
    (hM : M.IsSymm) (a b c : ℝ) (u : V → ℝ) :
    (M - c • 1) *ᵥ ((bandProjector M hM a b) *ᵥ u)
      = (bandProjector M hM a b) *ᵥ ((M - c • 1) *ᵥ u) := by
  have hL : (M - c • 1) *ᵥ (bandProjector M hM a b *ᵥ u)
      = M *ᵥ (bandProjector M hM a b *ᵥ u)
        - c • (bandProjector M hM a b *ᵥ u) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
  have hR : bandProjector M hM a b *ᵥ ((M - c • 1) *ᵥ u)
      = bandProjector M hM a b *ᵥ (M *ᵥ u)
        - c • (bandProjector M hM a b *ᵥ u) := by
    simp only [Matrix.sub_mulVec, Matrix.mulVec_sub,
      Matrix.smul_mulVec_assoc, Matrix.one_mulVec, Matrix.mulVec_smul]
  rw [hL, hR, mulVec_bandProjector_comm hM a b u]

/-- The A/B split of the shifted action (pure algebra). -/
private theorem sub_one_mulVec_split {M N : Matrix V V ℝ} (c : ℝ)
    (u : V → ℝ) :
    (M - c • 1) *ᵥ u = (N - c • 1) *ᵥ u + (M - N) *ᵥ u := by
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    Matrix.mulVec_sub]
  abel

/-- **The core engine** (private; the two interval theorems below are
the public interface): at eigenvalue-window form — `A`'s in-band
eigenvalues within `r` of `c`, `B`'s in-band eigenvalues at least
`r + δ` from `c` — the product bound with constant 1. -/
private theorem l2OpNorm_bandProjector_mul_bandProjector_le_core
    (hA : A.IsSymm) (hB : B.IsSymm)
    (a₁ b₁ a₂ b₂ c r δ : ℝ) (hab₁ : a₁ ≤ b₁) (hab₂ : a₂ ≤ b₂)
    (hδ : 0 < δ) (hr : 0 ≤ r)
    (hnear : ∀ i, a₁ < eigvalOf A hA i → eigvalOf A hA i ≤ b₁ →
      |eigvalOf A hA i - c| ≤ r)
    (hfar : ∀ j, a₂ < eigvalOf B hB j → eigvalOf B hB j ≤ b₂ →
      r + δ ≤ |eigvalOf B hB j - c|) :
    ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖ ≤ ‖A - B‖ / δ := by
  have hQidem := bandProjector_idempotent B hB a₂ b₂ hab₂
  have hrδ : 0 ≤ r + δ := by linarith
  have hpos : 0 < r + δ := by linarith
  have hCnn : 0 ≤ (r * ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖
      + ‖A - B‖) / (r + δ) :=
    div_nonneg (add_nonneg (mul_nonneg hr (norm_nonneg _)) (norm_nonneg _))
      (le_of_lt hpos)
  -- the per-vector master inequality
  have hmaster : ∀ y : V → ℝ,
      ‖pack ((bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁) *ᵥ y)‖
        ≤ ((r * ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖
          + ‖A - B‖) / (r + δ)) * ‖pack y‖ := by
    intro y
    have hzQ : bandProjector B hB a₂ b₂ *ᵥ
        ((bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁) *ᵥ y)
        = (bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁) *ᵥ y := by
      calc bandProjector B hB a₂ b₂ *ᵥ
          ((bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁) *ᵥ y)
          = (bandProjector B hB a₂ b₂
              * (bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁)) *ᵥ y :=
            Matrix.mulVec_mulVec y (bandProjector B hB a₂ b₂)
              (bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁)
        _ = (bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁) *ᵥ y := by
            rw [← Matrix.mul_assoc, hQidem]
    have hF2 := norm_pack_shift_apply_ge hB a₂ b₂ c r δ hab₂ hrδ hfar _ hzQ
    have hsplit : (B - c • 1) *ᵥ
        ((bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁) *ᵥ y)
        = bandProjector B hB a₂ b₂ *ᵥ ((A - c • 1) *ᵥ
            (bandProjector A hA a₁ b₁ *ᵥ y))
          + bandProjector B hB a₂ b₂ *ᵥ ((B - A) *ᵥ
            (bandProjector A hA a₁ b₁ *ᵥ y)) := by
      have e1 : (B - c • 1) *ᵥ
          ((bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁) *ᵥ y)
          = (B - c • 1) *ᵥ (bandProjector B hB a₂ b₂ *ᵥ
              (bandProjector A hA a₁ b₁ *ᵥ y)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
          Matrix.mulVec_mulVec]
      rw [e1, mulVec_bandProjector_comm_shift hB a₂ b₂ c
        (bandProjector A hA a₁ b₁ *ᵥ y),
        sub_one_mulVec_split c (bandProjector A hA a₁ b₁ *ᵥ y),
        Matrix.mulVec_add]
    have hT1 : ‖pack (bandProjector B hB a₂ b₂ *ᵥ ((A - c • 1) *ᵥ
        (bandProjector A hA a₁ b₁ *ᵥ y)))‖
        ≤ ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖
          * (r * ‖pack y‖) := by
      have hw : bandProjector A hA a₁ b₁ *ᵥ ((A - c • 1) *ᵥ
          (bandProjector A hA a₁ b₁ *ᵥ y))
          = (A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y) :=
        bandProjector_mulVec_shift_self hA a₁ b₁ c hab₁ y
      have hact : bandProjector B hB a₂ b₂ *ᵥ ((A - c • 1) *ᵥ
          (bandProjector A hA a₁ b₁ *ᵥ y))
          = (bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁) *ᵥ
              ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y)) := by
        conv_lhs => rw [← hw]
        rw [Matrix.mulVec_mulVec]
      rw [hact]
      have h1 := l2OpNorm_mulVec_le (bandProjector B hB a₂ b₂
        * bandProjector A hA a₁ b₁) ((A - c • 1) *ᵥ
        (bandProjector A hA a₁ b₁ *ᵥ y))
      have h2 := norm_pack_shift_bandProjector_mulVec_le hA a₁ b₁ c r hab₁ hr
        hnear y
      calc ‖pack ((bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁) *ᵥ
              ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y)))‖
          ≤ ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖
              * ‖pack ((A - c • 1) *ᵥ
                  (bandProjector A hA a₁ b₁ *ᵥ y))‖ := h1
        _ ≤ ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖
              * (r * ‖pack y‖) :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have hT2 : ‖pack (bandProjector B hB a₂ b₂ *ᵥ ((B - A) *ᵥ
        (bandProjector A hA a₁ b₁ *ᵥ y)))‖
        ≤ ‖A - B‖ * ‖pack y‖ := by
      have h1 := l2OpNorm_mulVec_le (B - A)
        (bandProjector A hA a₁ b₁ *ᵥ y)
      have h2 := norm_pack_bandProjector_mulVec_le hA a₁ b₁ hab₁ y
      have hkey : ‖pack (bandProjector B hB a₂ b₂ *ᵥ ((B - A) *ᵥ
          (bandProjector A hA a₁ b₁ *ᵥ y)))‖
          ≤ ‖pack ((B - A) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y))‖ :=
        norm_pack_bandProjector_mulVec_le hB a₂ b₂ hab₂ _
      calc ‖pack (bandProjector B hB a₂ b₂ *ᵥ ((B - A) *ᵥ
              (bandProjector A hA a₁ b₁ *ᵥ y)))‖
          ≤ ‖pack ((B - A) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y))‖ := hkey
        _ ≤ ‖B - A‖ * ‖pack (bandProjector A hA a₁ b₁ *ᵥ y)‖ := h1
        _ ≤ ‖B - A‖ * ‖pack y‖ :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = ‖A - B‖ * ‖pack y‖ := by rw [norm_sub_rev]
    -- combine the two pieces through the triangle inequality
    have hmid : (r + δ) * ‖pack ((bandProjector B hB a₂ b₂
        * bandProjector A hA a₁ b₁) *ᵥ y)‖
        ≤ (r * ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖
            + ‖A - B‖) * ‖pack y‖ := by
      have hsplitnorm : ‖pack ((B - c • 1) *ᵥ
          ((bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁) *ᵥ y))‖
          ≤ (r * ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖
              + ‖A - B‖) * ‖pack y‖ := by
        have hadd : ‖pack ((B - c • 1) *ᵥ
            ((bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁) *ᵥ y))‖
            ≤ ‖pack (bandProjector B hB a₂ b₂ *ᵥ ((A - c • 1) *ᵥ
                (bandProjector A hA a₁ b₁ *ᵥ y)))‖
              + ‖pack (bandProjector B hB a₂ b₂ *ᵥ ((B - A) *ᵥ
                (bandProjector A hA a₁ b₁ *ᵥ y)))‖ := by
          have hvec : pack ((B - c • 1) *ᵥ
              ((bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁) *ᵥ y))
              = pack (bandProjector B hB a₂ b₂ *ᵥ ((A - c • 1) *ᵥ
                  (bandProjector A hA a₁ b₁ *ᵥ y)))
                + pack (bandProjector B hB a₂ b₂ *ᵥ ((B - A) *ᵥ
                  (bandProjector A hA a₁ b₁ *ᵥ y))) := by
            rw [hsplit, pack_add]
          rw [hvec]
          exact norm_add_le _ _
        calc ‖pack ((B - c • 1) *ᵥ ((bandProjector B hB a₂ b₂
                  * bandProjector A hA a₁ b₁) *ᵥ y))‖
            ≤ ‖pack (bandProjector B hB a₂ b₂ *ᵥ ((A - c • 1) *ᵥ
                (bandProjector A hA a₁ b₁ *ᵥ y)))‖
              + ‖pack (bandProjector B hB a₂ b₂ *ᵥ ((B - A) *ᵥ
                (bandProjector A hA a₁ b₁ *ᵥ y)))‖ := hadd
          _ ≤ (r * ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖
                + ‖A - B‖) * ‖pack y‖ := by
                have hsum2 := add_le_add hT1 hT2
                calc ‖pack (bandProjector B hB a₂ b₂ *ᵥ ((A - c • 1) *ᵥ
                        (bandProjector A hA a₁ b₁ *ᵥ y)))‖
                      + ‖pack (bandProjector B hB a₂ b₂ *ᵥ ((B - A) *ᵥ
                        (bandProjector A hA a₁ b₁ *ᵥ y)))‖
                    ≤ (‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖
                        * (r * ‖pack y‖)) + (‖A - B‖ * ‖pack y‖) := hsum2
                  _ = (r * ‖bandProjector B hB a₂ b₂
                        * bandProjector A hA a₁ b₁‖ + ‖A - B‖) * ‖pack y‖ := by ring
      exact le_trans hF2 hsplitnorm
    have h3 : ‖pack ((bandProjector B hB a₂ b₂
        * bandProjector A hA a₁ b₁) *ᵥ y)‖
        ≤ ((r * ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖
            + ‖A - B‖) / (r + δ)) * ‖pack y‖ := by
      have hgoal : ‖pack ((bandProjector B hB a₂ b₂
          * bandProjector A hA a₁ b₁) *ᵥ y)‖ * (r + δ)
          ≤ (r * ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖
            + ‖A - B‖) * ‖pack y‖ := by
        rw [mul_comm]
        exact hmid
      have h2 := (le_div_iff₀ hpos).2 hgoal
      rw [div_mul_eq_mul_div]
      exact h2
    exact h3
  -- transport through the pairing engine, then the algebraic finish
  have hpair : ∀ x y : V → ℝ,
      |y ⬝ᵥ ((bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁) *ᵥ x)|
        ≤ ((r * ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖
            + ‖A - B‖) / (r + δ)) * Real.sqrt (x ⬝ᵥ x)
          * Real.sqrt (y ⬝ᵥ y) := by
    intro x y
    have hcs : |y ⬝ᵥ ((bandProjector B hB a₂ b₂
        * bandProjector A hA a₁ b₁) *ᵥ x)|
        ≤ ‖pack y‖ * ‖pack ((bandProjector B hB a₂ b₂
          * bandProjector A hA a₁ b₁) *ᵥ x)‖ := by
      have h := abs_dotProduct_le y ((bandProjector B hB a₂ b₂
        * bandProjector A hA a₁ b₁) *ᵥ x)
      rwa [← norm_euclidean_eq_sqrt, ← norm_euclidean_eq_sqrt] at h
    have hact := hmaster x
    have hrew : ‖pack y‖ * (((r * ‖bandProjector B hB a₂ b₂
        * bandProjector A hA a₁ b₁‖ + ‖A - B‖) / (r + δ))
      * ‖pack x‖) = ((r * ‖bandProjector B hB a₂ b₂
        * bandProjector A hA a₁ b₁‖ + ‖A - B‖) / (r + δ))
      * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
      rw [norm_euclidean_eq_sqrt, norm_euclidean_eq_sqrt]
      ring
    calc |y ⬝ᵥ ((bandProjector B hB a₂ b₂
            * bandProjector A hA a₁ b₁) *ᵥ x)|
        ≤ ‖pack y‖ * ‖pack ((bandProjector B hB a₂ b₂
            * bandProjector A hA a₁ b₁) *ᵥ x)‖ := hcs
      _ ≤ ‖pack y‖ * (((r * ‖bandProjector B hB a₂ b₂
              * bandProjector A hA a₁ b₁‖ + ‖A - B‖) / (r + δ))
          * ‖pack x‖) := mul_le_mul_of_nonneg_left hact (norm_nonneg _)
      _ = ((r * ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖
            + ‖A - B‖) / (r + δ)) * Real.sqrt (x ⬝ᵥ x)
            * Real.sqrt (y ⬝ᵥ y) := hrew
  have hnorm := l2OpNorm_le_of_abs_dotProduct_le hCnn hpair
  have hstep : (r + δ) * ‖bandProjector B hB a₂ b₂
      * bandProjector A hA a₁ b₁‖
      ≤ r * ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖
        + ‖A - B‖ := by
    have h := (le_div_iff₀ hpos).1 hnorm
    linarith
  have hfinal : δ * ‖bandProjector B hB a₂ b₂
      * bandProjector A hA a₁ b₁‖ ≤ ‖A - B‖ := by linarith
  exact (le_div_iff₀ hδ).2 (by rw [mul_comm]; exact hfinal)

end Engine

variable {A B : Matrix V V ℝ}

/-! ## The public theorems

Two interval-separated orientations; in each, the center/radius
instantiation (`c = (a₁ + b₁)/2`, `r = (b₁ - a₁)/2`) is discharged by
interval arithmetic, so consumers state only window endpoints and the
separation. The junk-band guards `a₁ ≤ b₁`, `a₂ ≤ b₂` are load-bearing:
the band projector's total definition is the *negated* band at
reversed endpoints. -/

/-- **Band Davis–Kahan, B's window strictly above A's.** If `A`'s band
`(a₁, b₁]` and `B`'s band `(a₂, b₂]` are separated by at least `δ`
(`b₁ + δ ≤ a₂`), then the product of `B`'s and `A`'s band projectors is
bounded by the perturbation over the separation:
`‖Q * P‖ ≤ ‖A - B‖ / δ`, with constant 1.

No rank hypothesis (the product form needs none), no sorted-spectrum
index, no eigenvalue of the difference computed. Load-bearing on four
delivered layers at once: Band's idempotence and eigenbasis action,
Spectral's Parseval and eigenaction, PolyFilter's band component
action, and Duhamel's pairing/norm engine.

Source (route provenance; the statement is proved, not admitted):
Vershynin, *High-Dimensional Probability*, 2018, Thm 4.1.15–4.1.16 —
see the module documentation and
`proposals/band-davis-kahan.md`.

QA: the rotated 2×2 witness, the ε = 0 attainment, and the
overlapping-window fence in
`Scaffold/QA/Perturbation/BandDavisKahan_QA.lean`. -/
theorem l2OpNorm_bandProjector_mul_bandProjector_le_of_lt
    (hA : A.IsSymm) (hB : B.IsSymm)
    (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : a₁ ≤ b₁) (hb₂ : a₂ ≤ b₂)
    {δ : ℝ} (hδ : 0 < δ) (hsep : b₁ + δ ≤ a₂) :
    ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖ ≤ ‖A - B‖ / δ := by
  refine l2OpNorm_bandProjector_mul_bandProjector_le_core hA hB a₁ b₁ a₂ b₂
    ((a₁ + b₁) / 2) ((b₁ - a₁) / 2) δ ha₁ hb₂ hδ (by linarith) ?_ ?_
  · intro i h1 h2
    rw [abs_le]
    constructor <;> linarith
  · intro j h1 h2
    have hnn : 0 ≤ eigvalOf B hB j - (a₁ + b₁) / 2 := by linarith
    rw [abs_of_nonneg hnn]
    linarith

/-- **Band Davis–Kahan, B's window strictly below A's.** The mirror
orientation: `b₂ + δ ≤ a₁`. Same constant, same conclusion. -/
theorem l2OpNorm_bandProjector_mul_bandProjector_le_of_gt
    (hA : A.IsSymm) (hB : B.IsSymm)
    (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : a₁ ≤ b₁) (hb₂ : a₂ ≤ b₂)
    {δ : ℝ} (hδ : 0 < δ) (hsep : b₂ + δ ≤ a₁) :
    ‖bandProjector B hB a₂ b₂ * bandProjector A hA a₁ b₁‖ ≤ ‖A - B‖ / δ := by
  refine l2OpNorm_bandProjector_mul_bandProjector_le_core hA hB a₁ b₁ a₂ b₂
    ((a₁ + b₁) / 2) ((b₁ - a₁) / 2) δ ha₁ hb₂ hδ (by linarith) ?_ ?_
  · intro i h1 h2
    rw [abs_le]
    constructor <;> linarith
  · intro j h1 h2
    have hnple : eigvalOf B hB j - (a₁ + b₁) / 2 ≤ 0 := by linarith
    rw [abs_of_nonpos hnple]
    linarith

/-! ## The rank supplier

The difference form's equal-rank hypothesis is the statement's one
supply-side burden; these lemmas make it checkable: the rank of a band
projector *is* the count of in-band eigenvalues (via the trace).
`proposals/band-davis-kahan-difference.md` Step 0, gap 3.
-/

section RankSupplier

variable {M : Matrix V V ℝ}

omit [DecidableEq V] in
/-- Filter-card of a predicate equals the subtype card (the
`rank_eq_card_non_zero_eigs` bridge; the ProjectionGap idiom). -/
private theorem card_filter_univ_eq' {p : V → Prop} [DecidablePred p] :
    (Finset.univ.filter p).card = Fintype.card {i // p i} := by
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  refine ⟨fun x => ⟨x.1, (Finset.mem_filter.1 x.2).2⟩,
    fun y => ⟨y.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, y.2⟩⟩,
    ?_, ?_⟩
  · intro x; simp
  · intro y; simp

/-- **The exact spectrum of an idempotent:** every eigenvalue of a
symmetric idempotent satisfies `μ² = μ` (apply `S² = S` to the
eigen-equation), hence lies in `{0, 1}` *exactly* — the membership
form `eigvalOf_isSymm_idempotent_mem` gives only `[0, 1]`. -/
private theorem eigvalOf_isSymm_idempotent_sq {S : Matrix V V ℝ}
    (hS : S.IsSymm) (hSS : S * S = S) (i : V) :
    eigvalOf S hS i * eigvalOf S hS i = eigvalOf S hS i := by
  have hev : S *ᵥ eigvecOf S hS i = eigvalOf S hS i • eigvecOf S hS i :=
    (isHermitian_of_isSymm hS).mulVec_eigenvectorBasis i
  have hv0 : eigvecOf S hS i ≠ 0 := by
    intro h
    have hnn := eigvecOf_inner S hS i i
    rw [h, if_pos rfl] at hnn
    simp at hnn
  have hL : S *ᵥ (S *ᵥ eigvecOf S hS i)
      = eigvalOf S hS i • eigvalOf S hS i • eigvecOf S hS i := by
    rw [hev, Matrix.mulVec_smul_assoc, hev]
  have hR : S *ᵥ (S *ᵥ eigvecOf S hS i)
      = eigvalOf S hS i • eigvecOf S hS i := by
    rw [Matrix.mulVec_mulVec _ S S, hSS, hev]
  have key : (eigvalOf S hS i * eigvalOf S hS i - eigvalOf S hS i)
      • eigvecOf S hS i = 0 := by
    rw [sub_smul, sub_eq_zero, mul_smul, ← hL, hR]
  rcases smul_eq_zero.mp key with h | h
  · linarith
  · exact absurd h hv0

/-- The trace of a threshold projector is the count of eigenvalues at
or below the threshold: each outer product `v vᵀ` contributes its unit
eigenvector's squared diagonal (`Finset.sum_comm` over the outer
product's definition). -/
theorem trace_spectralProjector_eq_card (hM : M.IsSymm) (c : ℝ) :
    (spectralProjector M hM c).trace
      = ((Finset.univ.filter fun i => eigvalOf M hM i ≤ c).card : ℝ) := by
  have hvv : ∀ i : V,
      ∑ a : V, eigvecOf M hM i a * eigvecOf M hM i a = 1 := by
    intro i
    have h := eigvecOf_inner M hM i i
    rw [if_pos rfl] at h
    exact h
  calc (spectralProjector M hM c).trace
      = ∑ a : V, ∑ i ∈ Finset.univ.filter
          (fun i => eigvalOf M hM i ≤ c),
          eigvecOf M hM i a * eigvecOf M hM i a := by
        simp only [Matrix.trace, Matrix.diag_apply, spectralProjector,
          Matrix.of_apply]
    _ = ∑ i ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c),
          ∑ a : V, eigvecOf M hM i a * eigvecOf M hM i a :=
          Finset.sum_comm
    _ = ∑ i ∈ Finset.univ.filter (fun i => eigvalOf M hM i ≤ c), (1 : ℝ) :=
          Finset.sum_congr rfl fun i _ => hvv i
    _ = _ := by simp

/-- The trace of a band projector is the count of in-band eigenvalues
(the count splits at the threshold `a` when `a ≤ b`). -/
theorem trace_bandProjector_eq_card (hM : M.IsSymm) (a b : ℝ)
    (hab : a ≤ b) :
    (bandProjector M hM a b).trace
      = ((Finset.univ.filter fun i =>
          a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b).card : ℝ) := by
  have hcardsplit : (Finset.univ.filter fun i => eigvalOf M hM i ≤ b).card
      = (Finset.univ.filter fun i => eigvalOf M hM i ≤ a).card
        + (Finset.univ.filter fun i =>
            a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b).card := by
    have hunion : (Finset.univ.filter fun i => eigvalOf M hM i ≤ b)
        = (Finset.univ.filter fun i => eigvalOf M hM i ≤ a)
          ∪ (Finset.univ.filter fun i =>
              a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union]
      constructor
      · intro hb
        rcases le_or_lt (eigvalOf M hM i) a with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, hb⟩
      · intro h
        rcases h with h | ⟨h1, h2⟩
        · exact h.trans hab
        · exact h2
    have hdisj : Disjoint (Finset.univ.filter fun i => eigvalOf M hM i ≤ a)
        (Finset.univ.filter fun i =>
          a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b) := by
      rw [Finset.disjoint_right]
      intro i hi hin
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hin
      obtain ⟨hi1, _⟩ := hi
      linarith
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  rw [bandProjector, Matrix.trace_sub,
    trace_spectralProjector_eq_card hM b,
    trace_spectralProjector_eq_card hM a, hcardsplit]
  push_cast
  ring

/-- **The rank supplier.** The rank of a band projector is exactly the
count of in-band eigenvalues — the checkable form of the difference
theorem's equal-rank hypothesis (a symmetric idempotent's rank is its
trace because its spectrum lies in `{0, 1}` exactly). -/
theorem rank_bandProjector_eq_card (hM : M.IsSymm) (a b : ℝ)
    (hab : a ≤ b) :
    (bandProjector M hM a b).rank
      = (Finset.univ.filter fun i =>
          a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b).card := by
  have hBP : (bandProjector M hM a b).IsSymm :=
    bandProjector_symmetric M hM a b
  have hBPidem := bandProjector_idempotent M hM a b hab
  have hrank' : (bandProjector M hM a b).rank
      = (Finset.univ.filter fun i =>
          eigvalOf (bandProjector M hM a b) hBP i ≠ 0).card := by
    rw [card_filter_univ_eq']
    have hcard : (bandProjector M hM a b).rank = Fintype.card
        {i // (isHermitian_of_isSymm hBP).eigenvalues i ≠ 0} :=
      (isHermitian_of_isSymm hBP).rank_eq_card_non_zero_eigs
    rw [hcard]
    simp only [eigvalOf]
  -- the spectrum of the projector lies in {0, 1} exactly
  have h01 : ∀ i, eigvalOf (bandProjector M hM a b) hBP i = 0 ∨
      eigvalOf (bandProjector M hM a b) hBP i = 1 := by
    intro i
    have hsq := eigvalOf_isSymm_idempotent_sq hBP hBPidem i
    have h' : eigvalOf (bandProjector M hM a b) hBP i
        * (eigvalOf (bandProjector M hM a b) hBP i - 1) = 0 := by
      rw [mul_sub, mul_one, hsq, sub_self]
    rcases mul_eq_zero.1 h' with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  -- so the nonzero count is the eigenvalue sum, which is the trace
  have hcardsum : ((Finset.univ.filter fun i =>
      eigvalOf (bandProjector M hM a b) hBP i ≠ 0).card : ℝ)
      = ∑ i, eigvalOf (bandProjector M hM a b) hBP i := by
    calc ((Finset.univ.filter fun i =>
          eigvalOf (bandProjector M hM a b) hBP i ≠ 0).card : ℝ)
        = ∑ i ∈ Finset.univ.filter
            (fun i => eigvalOf (bandProjector M hM a b) hBP i ≠ 0), (1 : ℝ) :=
            by simp
      _ = ∑ i ∈ Finset.univ.filter
            (fun i => eigvalOf (bandProjector M hM a b) hBP i ≠ 0),
            eigvalOf (bandProjector M hM a b) hBP i := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [Finset.mem_filter] at hi
            rcases h01 i with h | h
            · exact absurd h hi.2
            · exact h.symm
      _ = ∑ i, eigvalOf (bandProjector M hM a b) hBP i := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases h : eigvalOf (bandProjector M hM a b) hBP i ≠ 0
            · rw [if_pos h]
            · rw [if_neg h, not_not.mp h]
  have htrace : ∑ i, eigvalOf (bandProjector M hM a b) hBP i
      = (bandProjector M hM a b).trace := eigvalOf_sum_eq_trace _ hBP
  have hcast : (((bandProjector M hM a b).rank : ℕ) : ℝ)
      = ((Finset.univ.filter fun i =>
          a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b).card : ℝ) := by
    rw [hrank', hcardsum, htrace,
      trace_bandProjector_eq_card hM a b hab]
  exact Nat.cast_inj.mp hcast

end RankSupplier

/-! ## The difference form

The product engine re-run at the complement projector
`Q' = 1 - bandProjector B a₂ b₂`: the equal-rank gap identity turns
`‖P - Q‖` into `‖Q' * P‖`, and the same r-cancellation assembly bounds
it. The only genuinely new mathematical fact is the *complement
expansion* — for vectors fixed by `Q'`, the in-band eigencomponents
vanish, so Parseval leaves the out-of-band modes where the separation
hypothesis lives. The bounded A-window is load-bearing exactly as in
the product form (finite `r` + range invariance); the complement
window being unbounded is harmless because the expansion side never
needs a containment radius.
-/

section DifferenceForm

variable {A B : Matrix V V ℝ}

/-- The complement of a band projector is symmetric. -/
private theorem one_sub_bandProjector_isSymm {M : Matrix V V ℝ}
    (hM : M.IsSymm) (a b : ℝ) :
    ((1 : Matrix V V ℝ) - bandProjector M hM a b).IsSymm := by
  show ((1 : Matrix V V ℝ) - bandProjector M hM a b)ᵀ
    = (1 : Matrix V V ℝ) - bandProjector M hM a b
  rw [Matrix.transpose_sub, Matrix.transpose_one,
    (bandProjector_symmetric M hM a b).eq]

/-- The complement of an idempotent is idempotent. -/
private theorem one_sub_bandProjector_mul_self {M : Matrix V V ℝ}
    (hM : M.IsSymm) (a b : ℝ) (hab : a ≤ b) :
    (1 - bandProjector M hM a b) * (1 - bandProjector M hM a b)
      = (1 : Matrix V V ℝ) - bandProjector M hM a b := by
  have hQQ := bandProjector_idempotent M hM a b hab
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    hQQ, sub_self, sub_zero]

/-- **(F2′) complement expansion:** for a vector fixed by the complement
of `B`'s band projector, the shifted action expands by at least
`r + δ` whenever every *out-of-window* eigenvalue of `B` lies at
distance `≥ r + δ` from `c`. (The mirror of the product form's F2:
there the in-band components survived; here they vanish.) -/
private theorem norm_pack_shift_apply_ge_compl (hB : B.IsSymm)
    (a₂ b₂ c r δ : ℝ) (hab₂ : a₂ ≤ b₂) (hrδ : 0 ≤ r + δ)
    (hfar : ∀ j, ¬(a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂) →
      r + δ ≤ |eigvalOf B hB j - c|)
    (z : V → ℝ)
    (hz : (1 - bandProjector B hB a₂ b₂) *ᵥ z = z) :
    (r + δ) * ‖pack z‖ ≤ ‖pack ((B - c • 1) *ᵥ z)‖ := by
  have hzBPzero : bandProjector B hB a₂ b₂ *ᵥ z = 0 := by
    have hzR : (1 : Matrix V V ℝ) *ᵥ z = z := Matrix.one_mulVec z
    have hzL : (1 : Matrix V V ℝ) *ᵥ z
        - bandProjector B hB a₂ b₂ *ᵥ z = z := by
      rw [← Matrix.sub_mulVec]
      exact hz
    have hz' : z - bandProjector B hB a₂ b₂ *ᵥ z = z := by
      have this' := hzL
      rwa [hzR] at this'
    calc bandProjector B hB a₂ b₂ *ᵥ z
        = z - (z - bandProjector B hB a₂ b₂ *ᵥ z) :=
          (sub_sub_cancel z (bandProjector B hB a₂ b₂ *ᵥ z)).symm
      _ = 0 := by rw [hz', sub_self]
  have hzcomp : ∀ j, Matrix.dotProduct (eigvecOf B hB j) z
      = (if a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂ then (0 : ℝ) else 1)
        * Matrix.dotProduct (eigvecOf B hB j) z := by
    intro j
    have hpair := eigvecOf_dotProduct_bandProjector_mulVec hB a₂ b₂ hab₂ j z
    rw [hzBPzero, Matrix.dotProduct_zero] at hpair
    by_cases hband : a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂
    · rw [if_pos hband, zero_mul]
      rw [if_pos hband, one_mul] at hpair
      exact hpair.symm
    · rw [if_neg hband, one_mul]
  have hcomp : ∀ j, Matrix.dotProduct (eigvecOf B hB j) ((B - c • 1) *ᵥ z)
      = (eigvalOf B hB j - c) * Matrix.dotProduct (eigvecOf B hB j) z := by
    intro j
    simp only [Matrix.sub_mulVec, Matrix.dotProduct_sub,
      dotProduct_eigvecOf_mulVec hB,
      Matrix.smul_mulVec_assoc, Matrix.one_mulVec, Matrix.mulVec_smul,
      Matrix.dotProduct_smul, smul_eq_mul, sub_mul]
  have hsum : (r + δ) * (r + δ) * (z ⬝ᵥ z)
      ≤ ((B - c • 1) *ᵥ z) ⬝ᵥ ((B - c • 1) *ᵥ z) := by
    have hsplit : (r + δ) * (r + δ) * (z ⬝ᵥ z)
        = ∑ j, (r + δ) * (r + δ)
          * (Matrix.dotProduct (eigvecOf B hB j) z
            * Matrix.dotProduct (eigvecOf B hB j) z) := by
      rw [dotProduct_eigvecOf hB z z, ← Finset.mul_sum]
    rw [hsplit, dotProduct_eigvecOf hB ((B - c • 1) *ᵥ z)
      ((B - c • 1) *ᵥ z)]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hcomp j, hzcomp j]
    by_cases hband : a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂
    · simp [hband]
    · rw [if_neg hband, one_mul]
      have habs := hfar j hband
      have hkey : (r + δ) * (r + δ)
          ≤ (eigvalOf B hB j - c) * (eigvalOf B hB j - c) :=
        le_trans (mul_self_le_mul_self hrδ habs)
          (le_of_eq (abs_mul_abs_self _))
      nlinarith [hkey, mul_self_nonneg (Matrix.dotProduct (eigvecOf B hB j) z)]
  have hnn : 0 ≤ ‖pack z‖ := norm_nonneg _
  have hnn' : 0 ≤ ‖pack ((B - c • 1) *ᵥ z)‖ := norm_nonneg _
  have hsqrt : ((r + δ) * ‖pack z‖) ^ 2
      ≤ ‖pack ((B - c • 1) *ᵥ z)‖ ^ 2 := by
    rw [mul_pow, norm_pack_sq, norm_pack_sq, pow_two]
    exact hsum
  have habs := abs_le_of_sq_le_sq hsqrt hnn'
  rwa [abs_of_nonneg (mul_nonneg hrδ hnn)] at habs

/-- The shifted *complement* commutation (pure algebra from the band
commutation). -/
private theorem mulVec_one_sub_bandProjector_comm_shift {M : Matrix V V ℝ}
    (hM : M.IsSymm) (a b c : ℝ) (u : V → ℝ) :
    (M - c • 1) *ᵥ ((1 - bandProjector M hM a b) *ᵥ u)
      = (1 - bandProjector M hM a b) *ᵥ ((M - c • 1) *ᵥ u) := by
  have hsplitv : (1 - bandProjector M hM a b) *ᵥ u
      = u - bandProjector M hM a b *ᵥ u := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hR : (1 - bandProjector M hM a b) *ᵥ ((M - c • 1) *ᵥ u)
      = (M - c • 1) *ᵥ u
        - bandProjector M hM a b *ᵥ ((M - c • 1) *ᵥ u) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hcomm := mulVec_bandProjector_comm_shift hM a b c u
  rw [hR, hsplitv, Matrix.mulVec_sub, hcomm]

/-- **The complement's action is contractive** (Pythagoras at the
orthogonal projector `1 - Q`). -/
private theorem norm_pack_one_sub_bandProjector_mulVec_le
    {M : Matrix V V ℝ} (hM : M.IsSymm) (a b : ℝ) (hab : a ≤ b)
    (w : V → ℝ) :
    ‖pack ((1 - bandProjector M hM a b) *ᵥ w)‖ ≤ ‖pack w‖ := by
  have hSymm := one_sub_bandProjector_isSymm hM a b
  have hIdem := one_sub_bandProjector_mul_self hM a b hab
  have hle := dotProduct_mulVec_self_le_of_isSymm_idempotent hSymm hIdem w
  have habs : |‖pack ((1 - bandProjector M hM a b) *ᵥ w)‖|
      ≤ ‖pack w‖ := by
    refine abs_le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [norm_pack_sq, norm_pack_sq]
    exact hle
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- **The difference-form engine** (private; the public theorem below
instantiates the shift). The product engine re-run at the complement
projector: A's in-band eigenvalues within `r` of `c`, B's
*out-of-window* eigenvalues at least `r + δ` from `c`. -/
private theorem l2OpNorm_one_sub_bandProjector_mul_bandProjector_le_core
    (hA : A.IsSymm) (hB : B.IsSymm)
    (a₁ b₁ a₂ b₂ c r δ : ℝ) (hab₁ : a₁ ≤ b₁) (hab₂ : a₂ ≤ b₂)
    (hδ : 0 < δ) (hr : 0 ≤ r)
    (hnear : ∀ i, a₁ < eigvalOf A hA i → eigvalOf A hA i ≤ b₁ →
      |eigvalOf A hA i - c| ≤ r)
    (hfar : ∀ j, ¬(a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂) →
      r + δ ≤ |eigvalOf B hB j - c|) :
    ‖(1 - bandProjector B hB a₂ b₂) * bandProjector A hA a₁ b₁‖
      ≤ ‖A - B‖ / δ := by
  have hQidem := one_sub_bandProjector_mul_self hB a₂ b₂ hab₂
  have hrδ : 0 ≤ r + δ := by linarith
  have hpos : 0 < r + δ := by linarith
  have hCnn : 0 ≤ (r * ‖(1 - bandProjector B hB a₂ b₂)
      * bandProjector A hA a₁ b₁‖ + ‖A - B‖) / (r + δ) :=
    div_nonneg (add_nonneg (mul_nonneg hr (norm_nonneg _)) (norm_nonneg _))
      (le_of_lt hpos)
  -- the per-vector master inequality
  have hmaster : ∀ y : V → ℝ,
      ‖pack (((1 - bandProjector B hB a₂ b₂)
        * bandProjector A hA a₁ b₁) *ᵥ y)‖
        ≤ ((r * ‖(1 - bandProjector B hB a₂ b₂)
          * bandProjector A hA a₁ b₁‖ + ‖A - B‖) / (r + δ)) * ‖pack y‖ := by
    intro y
    have hzQ : (1 - bandProjector B hB a₂ b₂) *ᵥ
        (((1 - bandProjector B hB a₂ b₂)
          * bandProjector A hA a₁ b₁) *ᵥ y)
        = ((1 - bandProjector B hB a₂ b₂)
          * bandProjector A hA a₁ b₁) *ᵥ y := by
      calc (1 - bandProjector B hB a₂ b₂) *ᵥ
          (((1 - bandProjector B hB a₂ b₂)
            * bandProjector A hA a₁ b₁) *ᵥ y)
          = ((1 - bandProjector B hB a₂ b₂)
              * ((1 - bandProjector B hB a₂ b₂)
                * bandProjector A hA a₁ b₁)) *ᵥ y :=
            Matrix.mulVec_mulVec y (1 - bandProjector B hB a₂ b₂)
              ((1 - bandProjector B hB a₂ b₂)
                * bandProjector A hA a₁ b₁)
        _ = ((1 - bandProjector B hB a₂ b₂)
              * bandProjector A hA a₁ b₁) *ᵥ y := by
            rw [← Matrix.mul_assoc, hQidem]
    have hF2 := norm_pack_shift_apply_ge_compl hB a₂ b₂ c r δ hab₂ hrδ
      hfar _ hzQ
    have hsplit : (B - c • 1) *ᵥ
        (((1 - bandProjector B hB a₂ b₂)
          * bandProjector A hA a₁ b₁) *ᵥ y)
        = (1 - bandProjector B hB a₂ b₂) *ᵥ ((A - c • 1) *ᵥ
            (bandProjector A hA a₁ b₁ *ᵥ y))
          + (1 - bandProjector B hB a₂ b₂) *ᵥ ((B - A) *ᵥ
            (bandProjector A hA a₁ b₁ *ᵥ y)) := by
      have e1 : (B - c • 1) *ᵥ
          (((1 - bandProjector B hB a₂ b₂)
            * bandProjector A hA a₁ b₁) *ᵥ y)
          = (B - c • 1) *ᵥ ((1 - bandProjector B hB a₂ b₂) *ᵥ
              (bandProjector A hA a₁ b₁ *ᵥ y)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          ← Matrix.mul_assoc, Matrix.mulVec_mulVec]
      rw [e1, mulVec_one_sub_bandProjector_comm_shift hB a₂ b₂ c
        (bandProjector A hA a₁ b₁ *ᵥ y),
        sub_one_mulVec_split c (bandProjector A hA a₁ b₁ *ᵥ y),
        Matrix.mulVec_add]
    have hT1 : ‖pack ((1 - bandProjector B hB a₂ b₂) *ᵥ ((A - c • 1) *ᵥ
        (bandProjector A hA a₁ b₁ *ᵥ y)))‖
        ≤ ‖(1 - bandProjector B hB a₂ b₂)
            * bandProjector A hA a₁ b₁‖ * (r * ‖pack y‖) := by
      have hw : bandProjector A hA a₁ b₁ *ᵥ ((A - c • 1) *ᵥ
          (bandProjector A hA a₁ b₁ *ᵥ y))
          = (A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y) :=
        bandProjector_mulVec_shift_self hA a₁ b₁ c hab₁ y
      have hact : (1 - bandProjector B hB a₂ b₂) *ᵥ ((A - c • 1) *ᵥ
          (bandProjector A hA a₁ b₁ *ᵥ y))
          = ((1 - bandProjector B hB a₂ b₂)
              * bandProjector A hA a₁ b₁) *ᵥ
              ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y)) := by
        conv_lhs => rw [← hw]
        rw [Matrix.mulVec_mulVec]
      rw [hact]
      have h1 := l2OpNorm_mulVec_le ((1 - bandProjector B hB a₂ b₂)
        * bandProjector A hA a₁ b₁) ((A - c • 1) *ᵥ
        (bandProjector A hA a₁ b₁ *ᵥ y))
      have h2 := norm_pack_shift_bandProjector_mulVec_le hA a₁ b₁ c r
        hab₁ hr hnear y
      calc ‖pack (((1 - bandProjector B hB a₂ b₂)
              * bandProjector A hA a₁ b₁) *ᵥ
              ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y)))‖
          ≤ ‖(1 - bandProjector B hB a₂ b₂)
              * bandProjector A hA a₁ b₁‖
              * ‖pack ((A - c • 1) *ᵥ
                  (bandProjector A hA a₁ b₁ *ᵥ y))‖ := h1
        _ ≤ ‖(1 - bandProjector B hB a₂ b₂)
              * bandProjector A hA a₁ b₁‖ * (r * ‖pack y‖) :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have hT2 : ‖pack ((1 - bandProjector B hB a₂ b₂) *ᵥ ((B - A) *ᵥ
        (bandProjector A hA a₁ b₁ *ᵥ y)))‖
        ≤ ‖A - B‖ * ‖pack y‖ := by
      have h1 := l2OpNorm_mulVec_le (B - A)
        (bandProjector A hA a₁ b₁ *ᵥ y)
      have h2 := norm_pack_bandProjector_mulVec_le hA a₁ b₁ hab₁ y
      have hkey : ‖pack ((1 - bandProjector B hB a₂ b₂) *ᵥ ((B - A) *ᵥ
          (bandProjector A hA a₁ b₁ *ᵥ y)))‖
          ≤ ‖pack ((B - A) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y))‖ :=
        norm_pack_one_sub_bandProjector_mulVec_le hB a₂ b₂ hab₂ _
      calc ‖pack ((1 - bandProjector B hB a₂ b₂) *ᵥ ((B - A) *ᵥ
              (bandProjector A hA a₁ b₁ *ᵥ y)))‖
          ≤ ‖pack ((B - A) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y))‖ := hkey
        _ ≤ ‖B - A‖ * ‖pack (bandProjector A hA a₁ b₁ *ᵥ y)‖ := h1
        _ ≤ ‖B - A‖ * ‖pack y‖ :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = ‖A - B‖ * ‖pack y‖ := by rw [norm_sub_rev]
    -- combine the two pieces through the triangle inequality
    have hmid : (r + δ) * ‖pack (((1 - bandProjector B hB a₂ b₂)
        * bandProjector A hA a₁ b₁) *ᵥ y)‖
        ≤ (r * ‖(1 - bandProjector B hB a₂ b₂)
            * bandProjector A hA a₁ b₁‖ + ‖A - B‖) * ‖pack y‖ := by
      have hsplitnorm : ‖pack ((B - c • 1) *ᵥ
          (((1 - bandProjector B hB a₂ b₂)
            * bandProjector A hA a₁ b₁) *ᵥ y))‖
          ≤ (r * ‖(1 - bandProjector B hB a₂ b₂)
              * bandProjector A hA a₁ b₁‖ + ‖A - B‖) * ‖pack y‖ := by
        have hadd : ‖pack ((B - c • 1) *ᵥ
            (((1 - bandProjector B hB a₂ b₂)
              * bandProjector A hA a₁ b₁) *ᵥ y))‖
            ≤ ‖pack ((1 - bandProjector B hB a₂ b₂) *ᵥ ((A - c • 1) *ᵥ
                (bandProjector A hA a₁ b₁ *ᵥ y)))‖
              + ‖pack ((1 - bandProjector B hB a₂ b₂) *ᵥ ((B - A) *ᵥ
                (bandProjector A hA a₁ b₁ *ᵥ y)))‖ := by
          have hvec : pack ((B - c • 1) *ᵥ
              (((1 - bandProjector B hB a₂ b₂)
                * bandProjector A hA a₁ b₁) *ᵥ y))
              = pack ((1 - bandProjector B hB a₂ b₂) *ᵥ ((A - c • 1) *ᵥ
                  (bandProjector A hA a₁ b₁ *ᵥ y)))
                + pack ((1 - bandProjector B hB a₂ b₂) *ᵥ ((B - A) *ᵥ
                  (bandProjector A hA a₁ b₁ *ᵥ y))) := by
            rw [hsplit, pack_add]
          rw [hvec]
          exact norm_add_le _ _
        calc ‖pack ((B - c • 1) *ᵥ (((1 - bandProjector B hB a₂ b₂)
                  * bandProjector A hA a₁ b₁) *ᵥ y))‖
            ≤ ‖pack ((1 - bandProjector B hB a₂ b₂) *ᵥ ((A - c • 1) *ᵥ
                (bandProjector A hA a₁ b₁ *ᵥ y)))‖
              + ‖pack ((1 - bandProjector B hB a₂ b₂) *ᵥ ((B - A) *ᵥ
                (bandProjector A hA a₁ b₁ *ᵥ y)))‖ := hadd
          _ ≤ (r * ‖(1 - bandProjector B hB a₂ b₂)
                * bandProjector A hA a₁ b₁‖ + ‖A - B‖) * ‖pack y‖ := by
                have hsum2 := add_le_add hT1 hT2
                calc ‖pack ((1 - bandProjector B hB a₂ b₂) *ᵥ
                        ((A - c • 1) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y)))‖
                      + ‖pack ((1 - bandProjector B hB a₂ b₂) *ᵥ
                        ((B - A) *ᵥ (bandProjector A hA a₁ b₁ *ᵥ y)))‖
                    ≤ (‖(1 - bandProjector B hB a₂ b₂)
                        * bandProjector A hA a₁ b₁‖ * (r * ‖pack y‖))
                      + (‖A - B‖ * ‖pack y‖) := hsum2
                  _ = (r * ‖(1 - bandProjector B hB a₂ b₂)
                        * bandProjector A hA a₁ b₁‖ + ‖A - B‖)
                      * ‖pack y‖ := by ring
      exact le_trans hF2 hsplitnorm
    have h3 : ‖pack (((1 - bandProjector B hB a₂ b₂)
        * bandProjector A hA a₁ b₁) *ᵥ y)‖
        ≤ ((r * ‖(1 - bandProjector B hB a₂ b₂)
            * bandProjector A hA a₁ b₁‖ + ‖A - B‖) / (r + δ))
          * ‖pack y‖ := by
      have hgoal : ‖pack (((1 - bandProjector B hB a₂ b₂)
          * bandProjector A hA a₁ b₁) *ᵥ y)‖ * (r + δ)
          ≤ (r * ‖(1 - bandProjector B hB a₂ b₂)
            * bandProjector A hA a₁ b₁‖ + ‖A - B‖) * ‖pack y‖ := by
        rw [mul_comm]
        exact hmid
      have h2 := (le_div_iff₀ hpos).2 hgoal
      rw [div_mul_eq_mul_div]
      exact h2
    exact h3
  -- transport through the pairing engine, then the algebraic finish
  have hpair : ∀ x y : V → ℝ,
      |y ⬝ᵥ (((1 - bandProjector B hB a₂ b₂)
        * bandProjector A hA a₁ b₁) *ᵥ x)|
        ≤ ((r * ‖(1 - bandProjector B hB a₂ b₂)
            * bandProjector A hA a₁ b₁‖ + ‖A - B‖) / (r + δ))
          * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
    intro x y
    have hcs : |y ⬝ᵥ (((1 - bandProjector B hB a₂ b₂)
        * bandProjector A hA a₁ b₁) *ᵥ x)|
        ≤ ‖pack y‖ * ‖pack (((1 - bandProjector B hB a₂ b₂)
          * bandProjector A hA a₁ b₁) *ᵥ x)‖ := by
      have h := abs_dotProduct_le y (((1 - bandProjector B hB a₂ b₂)
        * bandProjector A hA a₁ b₁) *ᵥ x)
      rwa [← norm_euclidean_eq_sqrt, ← norm_euclidean_eq_sqrt] at h
    have hact := hmaster x
    have hrew : ‖pack y‖ * (((r * ‖(1 - bandProjector B hB a₂ b₂)
          * bandProjector A hA a₁ b₁‖ + ‖A - B‖) / (r + δ))
      * ‖pack x‖) = ((r * ‖(1 - bandProjector B hB a₂ b₂)
        * bandProjector A hA a₁ b₁‖ + ‖A - B‖) / (r + δ))
      * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
      rw [norm_euclidean_eq_sqrt, norm_euclidean_eq_sqrt]
      ring
    calc |y ⬝ᵥ (((1 - bandProjector B hB a₂ b₂)
            * bandProjector A hA a₁ b₁) *ᵥ x)|
        ≤ ‖pack y‖ * ‖pack (((1 - bandProjector B hB a₂ b₂)
            * bandProjector A hA a₁ b₁) *ᵥ x)‖ := hcs
      _ ≤ ‖pack y‖ * (((r * ‖(1 - bandProjector B hB a₂ b₂)
              * bandProjector A hA a₁ b₁‖ + ‖A - B‖) / (r + δ))
          * ‖pack x‖) := mul_le_mul_of_nonneg_left hact (norm_nonneg _)
      _ = ((r * ‖(1 - bandProjector B hB a₂ b₂)
            * bandProjector A hA a₁ b₁‖ + ‖A - B‖) / (r + δ))
          * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := hrew
  have hnorm := l2OpNorm_le_of_abs_dotProduct_le hCnn hpair
  have hstep : (r + δ) * ‖(1 - bandProjector B hB a₂ b₂)
      * bandProjector A hA a₁ b₁‖
      ≤ r * ‖(1 - bandProjector B hB a₂ b₂)
        * bandProjector A hA a₁ b₁‖ + ‖A - B‖ := by
    have h := (le_div_iff₀ hpos).1 hnorm
    linarith
  have hfinal : δ * ‖(1 - bandProjector B hB a₂ b₂)
      * bandProjector A hA a₁ b₁‖ ≤ ‖A - B‖ := by linarith
  exact (le_div_iff₀ hδ).2 (by rw [mul_comm]; exact hfinal)

end DifferenceForm

variable {A B : Matrix V V ℝ}

/-! ## The public difference-form theorems

The separation is stated one-sided at eigenvalue level (B's
out-of-window spectrum against A's window closure), with the
interval-margin corollary for the common contained-window case. In
each, the center/radius instantiation (`c = (a₁ + b₁)/2`,
`r = (b₁ - a₁)/2`) is discharged inside, so consumers state only
window endpoints, the separation, and the rank equality (checkable
through `rank_bandProjector_eq_card`). -/

/-- **Band Davis–Kahan, difference form (sin Θ).** If the band
projectors of `A` (window `(a₁, b₁]`) and `B` (window `(a₂, b₂]`) have
equal rank, and every eigenvalue of `B` *outside* its window lies
δ-away from A's window closure `[a₁, b₁]` (below: `μ ≤ a₂ → μ ≤ a₁ − δ`;
above: `b₂ < μ → b₁ + δ ≤ μ`), then the projectors are close:

`‖P_A - P_B‖ ≤ ‖A - B‖ / δ`, constant 1.

This is the classical Davis–Kahan / Yu–Wang–Samworth Theorem 1
operator-norm difference shape at one-sided eigenvalue separation: no
constraint on B's in-window eigenvalues (the clusters overlap — that
is the point), the equal-dimension hypothesis as projector-rank
equality. Route (all proved; no axiom): the equal-rank gap identity
`l2OpNorm_sub_eq_of_rank_eq` (Kato Ch. I §4 — its first consumer)
reduces the difference to `‖(I − Q) * P‖`, and the commutator/shift
engine bounds that at the complement projector.

QA: `Scaffold/QA/Perturbation/BandDavisKahanDiff_QA.lean` — the
rotated two-route witness, the ε = 0 attainment, the
margin-corollary instance, and the rank fence. -/
theorem l2OpNorm_bandProjector_sub_bandProjector_le
    (hA : A.IsSymm) (hB : B.IsSymm)
    (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂)
    {δ : ℝ} (hδ : 0 < δ)
    (hrank : (bandProjector A hA a₁ b₁).rank
      = (bandProjector B hB a₂ b₂).rank)
    (hlo : ∀ j, eigvalOf B hB j ≤ a₂ → eigvalOf B hB j ≤ a₁ - δ)
    (hhi : ∀ j, b₂ < eigvalOf B hB j → b₁ + δ ≤ eigvalOf B hB j) :
    ‖bandProjector A hA a₁ b₁ - bandProjector B hB a₂ b₂‖
      ≤ ‖A - B‖ / δ := by
  rw [l2OpNorm_sub_eq_of_rank_eq
    (bandProjector_symmetric A hA a₁ b₁)
    (bandProjector_idempotent A hA a₁ b₁ ha₁)
    (bandProjector_symmetric B hB a₂ b₂)
    (bandProjector_idempotent B hB a₂ b₂ ha₂) hrank]
  refine l2OpNorm_one_sub_bandProjector_mul_bandProjector_le_core
    hA hB a₁ b₁ a₂ b₂ ((a₁ + b₁) / 2) ((b₁ - a₁) / 2) δ ha₁ ha₂ hδ
    (by linarith) ?_ ?_
  · intro i h1 h2
    rw [abs_le]
    constructor <;> linarith
  · intro j hj
    rcases le_or_lt (eigvalOf B hB j) a₂ with hlow | hlow
    · have h := hlo j hlow
      have hnple : eigvalOf B hB j - (a₁ + b₁) / 2 ≤ 0 := by linarith
      rw [abs_of_nonpos hnple]
      linarith
    · have hb₂ : b₂ < eigvalOf B hB j := by
        by_contra hcon
        push_neg at hcon
        exact hj ⟨hlow, hcon⟩
      have h := hhi j hb₂
      have hnn : 0 ≤ eigvalOf B hB j - (a₁ + b₁) / 2 := by linarith
      rw [abs_of_nonneg hnn]
      linarith

/-- **Band Davis–Kahan, difference form, margin version.** The
interval-level corollary: B's window contains A's with δ-margin on
both sides (`a₂ + δ ≤ a₁`, `b₁ + δ ≤ b₂`) — then every B-eigenvalue
outside B's window is at least δ away from `[a₁, b₁]`. -/
theorem l2OpNorm_bandProjector_sub_bandProjector_le_of_mem
    (hA : A.IsSymm) (hB : B.IsSymm)
    (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂)
    {δ : ℝ} (hδ : 0 < δ)
    (hrank : (bandProjector A hA a₁ b₁).rank
      = (bandProjector B hB a₂ b₂).rank)
    (hlo : a₂ + δ ≤ a₁) (hhi : b₁ + δ ≤ b₂) :
    ‖bandProjector A hA a₁ b₁ - bandProjector B hB a₂ b₂‖
      ≤ ‖A - B‖ / δ :=
  l2OpNorm_bandProjector_sub_bandProjector_le hA hB a₁ b₁ a₂ b₂ ha₁ ha₂
    hδ hrank (fun j hj => by linarith) (fun j hj => by linarith)

/-! ## The cluster form — pairwise (YWS-literal) separation

`proposals/band-davis-kahan-cluster.md` (the difference form's own
first recorded follow-on): the separation hypothesis stated *between
the clusters' spectra* rather than through A's window closure — the
literal Yu–Wang–Samworth Theorem 1 `δ` (every eigenvalue of `B`
outside its window δ-away from every eigenvalue of `A` inside its
window), at constant 1. This is strictly weaker than the closure
separation above: when A's cluster has an internal gap of width `≥ 2δ`,
a B-eigenvalue can sit *inside* A's window yet δ-away from *every*
in-window A-eigenvalue.

The route has two regimes, worked through in the proposal:

- **Interior** (a B-eigenvalue strictly inside A's cluster range, in a
  gap): *every* A-eigenvalue is then δ-away from it (in-window by the
  pairwise hypothesis; the flanks because `a₁ < λmin` and `λmax ≤ b₁`),
  so the projector-free expansion at that B-eigenvector gives
  `δ ≤ ‖A − B‖` — the trivial regime, closed by `‖P − Q‖ ≤ 1`. No
  Weyl/`evals` bridge is needed: the eigenvector equation does all the
  work. This regime is mathematically forced: at an interior `μ` no
  shift `c, r` can satisfy both compression and expansion (`|μ − c| <
  r + δ` whenever all in-band eigenvalues lie within `r` of `c`), so
  the commutator/shift engine cannot cover it directly.
- **Boundary**: every out-of-window B-eigenvalue is δ-outside the
  cluster *range* `[lmin, lmax]`. Shrink A's window to
  `((a₁ + lmin)/2, lmax]` — it selects exactly the same cluster
  (`bandProjector_eq_of_forall_mem_iff`, the window-existence
  argument's transfer step) — and run the complement engine at the
  *cluster range* center/radius `c = (lmin + lmax)/2`,
  `r = (lmax − lmin)/2`, where the expansion side needs exactly the
  range separation, with no slack. (At the *window's* center/radius
  the assembly would strand `+ r` — the recorded catch, which is why
  the core takes arbitrary `c, r`.) -/
section ClusterForm

variable {A B : Matrix V V ℝ}

/-- **The projector-free expansion:** every eigenvalue of a symmetric
matrix δ-away from `c` forces `δ * ‖z‖ ≤ ‖(A − cI) *ᵥ z‖` — F2 with no
projector condition (all eigencomponents survive). The interior case of
the cluster form runs this at a B-eigenvector. -/
private theorem norm_pack_shift_apply_ge_any (hA : A.IsSymm) (c δ : ℝ)
    (hδ : 0 ≤ δ)
    (hfar : ∀ i, δ ≤ |eigvalOf A hA i - c|)
    (z : V → ℝ) :
    δ * ‖pack z‖ ≤ ‖pack ((A - c • 1) *ᵥ z)‖ := by
  have hcomp : ∀ j, Matrix.dotProduct (eigvecOf A hA j)
      ((A - c • 1) *ᵥ z)
      = (eigvalOf A hA j - c) * Matrix.dotProduct (eigvecOf A hA j) z := by
    intro j
    simp only [Matrix.sub_mulVec, Matrix.dotProduct_sub,
      dotProduct_eigvecOf_mulVec hA,
      Matrix.smul_mulVec_assoc, Matrix.one_mulVec, Matrix.mulVec_smul,
      Matrix.dotProduct_smul, smul_eq_mul, sub_mul]
  have hsum : δ * δ * (z ⬝ᵥ z)
      ≤ ((A - c • 1) *ᵥ z) ⬝ᵥ ((A - c • 1) *ᵥ z) := by
    have hsplit : δ * δ * (z ⬝ᵥ z)
        = ∑ j, δ * δ
          * (Matrix.dotProduct (eigvecOf A hA j) z
            * Matrix.dotProduct (eigvecOf A hA j) z) := by
      rw [dotProduct_eigvecOf hA z z, ← Finset.mul_sum]
    rw [hsplit, dotProduct_eigvecOf hA ((A - c • 1) *ᵥ z)
      ((A - c • 1) *ᵥ z)]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hcomp j]
    have hkey : δ * δ
        ≤ (eigvalOf A hA j - c) * (eigvalOf A hA j - c) :=
      le_trans (mul_self_le_mul_self hδ (hfar j))
        (le_of_eq (abs_mul_abs_self _))
    nlinarith [hkey, mul_self_nonneg (Matrix.dotProduct (eigvecOf A hA j) z)]
  have hnn : 0 ≤ ‖pack z‖ := norm_nonneg _
  have hnn' : 0 ≤ ‖pack ((A - c • 1) *ᵥ z)‖ := norm_nonneg _
  have hsqrt : (δ * ‖pack z‖) ^ 2
      ≤ ‖pack ((A - c • 1) *ᵥ z)‖ ^ 2 := by
    rw [mul_pow, norm_pack_sq, norm_pack_sq, pow_two]
    exact hsum
  have habs := abs_le_of_sq_le_sq hsqrt hnn'
  rwa [abs_of_nonneg (mul_nonneg hδ hnn)] at habs

/-- A B-eigenvalue δ-far from A's *whole* spectrum forces the
perturbation norm to be at least `δ`: at the (unit) eigenvector `v`
with `Bv = μv`, the shift `A − μI` and the perturbation `A − B` agree
(`(μI)v = Bv`), the projector-free expansion lower-bounds the action,
and the vector action bound upper-bounds it by `‖A − B‖`. The interior
case's trivial regime, without Weyl or `evals`. -/
private theorem norm_sub_ge_of_far_eigvalOf (hA : A.IsSymm)
    (hB : B.IsSymm) {δ : ℝ} (hδ : 0 < δ) (j : V)
    (hfar : ∀ i, δ ≤ |eigvalOf A hA i - eigvalOf B hB j|) :
    δ ≤ ‖A - B‖ := by
  have hev : B *ᵥ eigvecOf B hB j
      = eigvalOf B hB j • eigvecOf B hB j :=
    (isHermitian_of_isSymm hB).mulVec_eigenvectorBasis j
  have hvunit : ‖pack (eigvecOf B hB j)‖ = 1 := by
    have h := eigvecOf_inner B hB j j
    rw [if_pos rfl] at h
    rw [norm_euclidean_eq_sqrt,
      show eigvecOf B hB j ⬝ᵥ eigvecOf B hB j = 1 by
        simpa [Matrix.dotProduct] using h, Real.sqrt_one]
  have hshift : (A - eigvalOf B hB j • 1) *ᵥ eigvecOf B hB j
      = (A - B) *ᵥ eigvecOf B hB j := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec_assoc, Matrix.one_mulVec, hev]
  have hexp := norm_pack_shift_apply_ge_any hA (eigvalOf B hB j) δ
    (le_of_lt hδ) hfar (eigvecOf B hB j)
  rw [hshift] at hexp
  have hact := l2OpNorm_mulVec_le (A - B) (eigvecOf B hB j)
  calc δ = δ * ‖pack (eigvecOf B hB j)‖ := by rw [hvunit, mul_one]
    _ ≤ ‖pack ((A - B) *ᵥ eigvecOf B hB j)‖ := hexp
    _ ≤ ‖A - B‖ * ‖pack (eigvecOf B hB j)‖ := hact
    _ = ‖A - B‖ := by rw [hvunit, mul_one]

/-- **Capture equality.** Two (non-junk) windows selecting the same
eigenvalues give the same band projector — the cluster is a class of
the window, not the window. The guards are load-bearing: at reversed
endpoints the total definition is the *negated* band, so two
always-empty windows need not agree. Basis injectivity on the component
action. -/
theorem bandProjector_eq_of_forall_mem_iff {M : Matrix V V ℝ}
    (hM : M.IsSymm) (a b a' b' : ℝ) (hab : a ≤ b) (hab' : a' ≤ b')
    (hiff : ∀ i, (a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b)
      ↔ (a' < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b')) :
    bandProjector M hM a b = bandProjector M hM a' b' := by
  have hact : ∀ y : V → ℝ, bandProjector M hM a b *ᵥ y
      = bandProjector M hM a' b' *ᵥ y := by
    intro y
    refine eq_of_forall_dotProduct_eigvecOf_eq hM _ _ fun i => ?_
    rw [eigvecOf_dotProduct_bandProjector_mulVec hM a b hab i y,
      eigvecOf_dotProduct_bandProjector_mulVec hM a' b' hab' i y]
    by_cases hmem : a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b
    · rw [if_pos hmem, if_pos ((hiff i).1 hmem)]
    · rw [if_neg hmem, if_neg (fun h => hmem ((hiff i).2 h))]
  have hcol : ∀ i j : V,
      (bandProjector M hM a b - bandProjector M hM a' b') i j = 0 := by
    intro i j
    have hzero : (bandProjector M hM a b
        - bandProjector M hM a' b') *ᵥ (Pi.single j (1 : ℝ)) = 0 := by
      rw [Matrix.sub_mulVec, hact (Pi.single j (1 : ℝ)), sub_self]
    have hj := congrFun hzero i
    simpa [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply,
      Matrix.sub_apply] using hj
  exact Matrix.ext fun i j => sub_eq_zero.mp (hcol i j)

/-- The empty-cluster corner: a non-junk window selecting no eigenvalue
gives the zero projector (the component action vanishes identically). -/
theorem bandProjector_eq_zero_of_forall_not_mem {M : Matrix V V ℝ}
    (hM : M.IsSymm) (a b : ℝ) (hab : a ≤ b)
    (h : ∀ i, ¬(a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b)) :
    bandProjector M hM a b = 0 := by
  have hact : ∀ y : V → ℝ, bandProjector M hM a b *ᵥ y = 0 := by
    intro y
    refine eq_of_forall_dotProduct_eigvecOf_eq hM _ _ fun i => ?_
    rw [eigvecOf_dotProduct_bandProjector_mulVec hM a b hab i y,
      if_neg (h i), zero_mul, Matrix.dotProduct_zero]
  have hcol : ∀ i j : V, bandProjector M hM a b i j = 0 := by
    intro i j
    have hj := congrFun (hact (Pi.single j (1 : ℝ))) i
    simpa [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply] using hj
  exact Matrix.ext fun i j => hcol i j

/-- **Band Davis–Kahan, difference form, pairwise (cluster)
separation.** If the band projectors of `A` (window `(a₁, b₁]`) and `B`
(window `(a₂, b₂]`) have equal rank, and every eigenvalue of `B`
*outside* its window is δ-away from every eigenvalue of `A` *inside*
its window — the literal Yu–Wang–Samworth Theorem 1 separation, the
pairwise inf over the two cluster spectra — then the projectors are
close:

`‖P_A - P_B‖ ≤ ‖A - B‖ / δ`, constant 1.

Strictly more general than
`l2OpNorm_bandProjector_sub_bandProjector_le` above (whose
closure-separation hypotheses imply `hsep` here): when A's cluster has
an internal gap of width `≥ 2δ`, a B-eigenvalue may sit inside A's
window yet δ-away from every in-window A-eigenvalue — the closure form
does not apply, this form does. The interior configuration is handled
inside the proof (it forces `δ ≤ ‖A - B‖`, the trivial regime); the
boundary one re-runs the complement engine at the cluster-range
center/radius through `bandProjector_eq_of_forall_mem_iff`.

Route provenance (the statement is proved, not admitted): Yu, Wang &
Samworth 2015, Theorem 1 — the pairwise mixed separation at constant 1,
already the cited source of `davis_kahan_sin_theta`; see the module
documentation and `proposals/band-davis-kahan-cluster.md`.

QA: `Scaffold/QA/Perturbation/BandDavisKahanCluster_QA.lean` — the
interior witness (new coverage, closure separation refuted on the
fixture), the rotated two-route witness, the ε = 0 attainment, and the
separation fence. -/
theorem l2OpNorm_bandProjector_sub_bandProjector_le_of_pairwise
    (hA : A.IsSymm) (hB : B.IsSymm)
    (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂)
    {δ : ℝ} (hδ : 0 < δ)
    (hrank : (bandProjector A hA a₁ b₁).rank
      = (bandProjector B hB a₂ b₂).rank)
    (hsep : ∀ j, ¬(a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂) →
      ∀ i, a₁ < eigvalOf A hA i → eigvalOf A hA i ≤ b₁ →
      δ ≤ |eigvalOf B hB j - eigvalOf A hA i|) :
    ‖bandProjector A hA a₁ b₁ - bandProjector B hB a₂ b₂‖
      ≤ ‖A - B‖ / δ := by
  classical
  rcases le_or_lt δ ‖A - B‖ with htriv | hcont
  · -- the trivial regime
    refine le_trans (l2OpNorm_sub_le_one_of_isSymm_idempotent
      (bandProjector_symmetric A hA a₁ b₁)
      (bandProjector_idempotent A hA a₁ b₁ ha₁)
      (bandProjector_symmetric B hB a₂ b₂)
      (bandProjector_idempotent B hB a₂ b₂ ha₂)) ?_
    rw [le_div_iff₀ hδ]
    linarith
  -- A's cluster as an index set, its range as a value set
  set SA : Finset V := Finset.univ.filter
    fun i => a₁ < eigvalOf A hA i ∧ eigvalOf A hA i ≤ b₁ with hSAdef
  set SAv : Finset ℝ := SA.image fun i => eigvalOf A hA i with hSAvdef
  rcases SA.eq_empty_or_nonempty with hempty | hne
  · -- the empty-cluster corner: both projectors vanish
    have hPzero : bandProjector A hA a₁ b₁ = 0 :=
      bandProjector_eq_zero_of_forall_not_mem hA a₁ b₁ ha₁
        (fun i hmem => absurd
          (show i ∈ SA from Finset.mem_filter.2 ⟨Finset.mem_univ _, hmem⟩)
          (by simp [hempty]))
    have hcardB : (Finset.univ.filter
        fun j => a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂).card = 0 := by
      have h := hrank
      rw [rank_bandProjector_eq_card hA a₁ b₁ ha₁,
        rank_bandProjector_eq_card hB a₂ b₂ ha₂] at h
      rw [hSAdef] at hempty
      rw [hempty] at h
      simpa using h.symm
    have hQBempty : (Finset.univ.filter
        fun j => a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂) = ∅ :=
      Finset.card_eq_zero.1 hcardB
    have hQzero : bandProjector B hB a₂ b₂ = 0 :=
      bandProjector_eq_zero_of_forall_not_mem hB a₂ b₂ ha₂
        (fun j hmem => absurd
          (show j ∈ Finset.univ.filter
            fun j => a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂ from
            Finset.mem_filter.2 ⟨Finset.mem_univ _, hmem⟩)
          (by simp [hQBempty]))
    rw [hPzero, hQzero, sub_zero, norm_zero]
    exact div_nonneg (norm_nonneg _) (le_of_lt hδ)
  -- the cluster range
  have hSAvne : SAv.Nonempty := hne.image _
  obtain ⟨i₀, hi₀SA, hi₀val⟩ := Finset.mem_image.1 (SAv.min'_mem hSAvne)
  obtain ⟨i₁, hi₁SA, hi₁val⟩ := Finset.mem_image.1 (SAv.max'_mem hSAvne)
  have hwin₀ : a₁ < eigvalOf A hA i₀ ∧ eigvalOf A hA i₀ ≤ b₁ :=
    (Finset.mem_filter.1 hi₀SA).2
  have hwin₁ : a₁ < eigvalOf A hA i₁ ∧ eigvalOf A hA i₁ ≤ b₁ :=
    (Finset.mem_filter.1 hi₁SA).2
  have hminle : ∀ i ∈ SA, SAv.min' hSAvne ≤ eigvalOf A hA i := by
    intro i hi
    have hvv : eigvalOf A hA i ∈ SAv :=
      Finset.mem_image.2 ⟨i, hi, rfl⟩
    rw [show SAv.min' hSAvne = SAv.min' ⟨eigvalOf A hA i, hvv⟩ from
      congrArg (SAv.min') (proof_irrel hSAvne ⟨eigvalOf A hA i, hvv⟩)]
    exact SAv.min'_le _ hvv
  have hlemax : ∀ i ∈ SA, eigvalOf A hA i ≤ SAv.max' hSAvne := by
    intro i hi
    have hvv : eigvalOf A hA i ∈ SAv :=
      Finset.mem_image.2 ⟨i, hi, rfl⟩
    rw [show SAv.max' hSAvne = SAv.max' ⟨eigvalOf A hA i, hvv⟩ from
      congrArg (SAv.max') (proof_irrel hSAvne ⟨eigvalOf A hA i, hvv⟩)]
    exact SAv.le_max' _ hvv
  -- the cluster range brackets
  have hlimA : a₁ < SAv.min' hSAvne := by
    rw [← hi₀val]; exact hwin₀.1
  have hlmaxB : SAv.max' hSAvne ≤ b₁ := by
    rw [← hi₁val]; exact hwin₁.2
  have hshalmax : SAv.min' hSAvne ≤ SAv.max' hSAvne := by
    have h₀ := hminle i₁ hi₁SA
    rw [hi₁val] at h₀
    exact h₀
  -- the dichotomy: every out-of-window B-eigenvalue is δ-outside the
  -- cluster range, or the perturbation is already at least δ
  have hkey : ∀ j : V, ¬(a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂) →
      eigvalOf B hB j ≤ SAv.min' hSAvne - δ
        ∨ SAv.max' hSAvne + δ ≤ eigvalOf B hB j
        ∨ δ ≤ ‖A - B‖ := by
    intro j hjout
    rcases lt_or_ge (eigvalOf B hB j) (SAv.min' hSAvne) with hμ | hμ
    · refine Or.inl ?_
      have h := hsep j hjout i₀ hwin₀.1 hwin₀.2
      rw [hi₀val] at h
      have hnn : 0 ≤ SAv.min' hSAvne - eigvalOf B hB j := by linarith
      rw [abs_sub_comm, abs_of_nonneg hnn] at h
      linarith
    rcases lt_or_ge (eigvalOf B hB j) (SAv.max' hSAvne) with hμ' | hμ'
    · -- between the range endpoints: the interior case
      rcases eq_or_ne (eigvalOf B hB j) (SAv.min' hSAvne) with heq | hne'
      · have h := hsep j hjout i₀ hwin₀.1 hwin₀.2
        rw [hi₀val, ← heq, sub_self, abs_zero] at h
        exact absurd h (not_le.2 hδ)
      rcases eq_or_ne (eigvalOf B hB j) (SAv.max' hSAvne) with heq' | hne''
      · have h := hsep j hjout i₁ hwin₁.1 hwin₁.2
        rw [hi₁val, ← heq', sub_self, abs_zero] at h
        exact absurd h (not_le.2 hδ)
      -- strictly interior: every A-eigenvalue is δ-away from it
      have hbelow : SAv.min' hSAvne + δ ≤ eigvalOf B hB j := by
        have h := hsep j hjout i₀ hwin₀.1 hwin₀.2
        rw [hi₀val] at h
        have hnn : 0 ≤ eigvalOf B hB j - SAv.min' hSAvne := by linarith
        rw [abs_of_nonneg hnn] at h
        linarith
      have habove : eigvalOf B hB j ≤ SAv.max' hSAvne - δ := by
        have h := hsep j hjout i₁ hwin₁.1 hwin₁.2
        rw [hi₁val] at h
        have hnn : 0 ≤ SAv.max' hSAvne - eigvalOf B hB j := by linarith
        rw [abs_sub_comm, abs_of_nonneg hnn] at h
        linarith
      refine Or.inr (Or.inr ?_)
      refine norm_sub_ge_of_far_eigvalOf hA hB hδ j ?_
      intro i
      rcases le_or_lt (eigvalOf A hA i) a₁ with hlowA | hlowA
      · -- out-of-window below: below a₁ < lmin ≤ μ − δ
        have habs : 0 ≤ eigvalOf B hB j - eigvalOf A hA i := by linarith
        rw [abs_sub_comm, abs_of_nonneg habs]
        linarith
      rcases le_or_lt (eigvalOf A hA i) b₁ with hhighA | hhighA
      · -- in-window: the pairwise hypothesis itself
        rw [abs_sub_comm]
        exact hsep j hjout i hlowA hhighA
      · -- out-of-window above: above b₁ ≥ lmax ≥ μ + δ
        have habs : 0 ≤ eigvalOf A hA i - eigvalOf B hB j := by linarith
        rw [abs_of_nonneg habs]
        linarith
    · refine Or.inr (Or.inl ?_)
      rcases eq_or_ne (eigvalOf B hB j) (SAv.max' hSAvne) with heq' | hne''
      · have h := hsep j hjout i₁ hwin₁.1 hwin₁.2
        rw [hi₁val, ← heq', sub_self, abs_zero] at h
        exact absurd h (not_le.2 hδ)
      have h := hsep j hjout i₁ hwin₁.1 hwin₁.2
      rw [hi₁val] at h
      have hnn : 0 ≤ eigvalOf B hB j - SAv.max' hSAvne := by linarith
      rw [abs_of_nonneg hnn] at h
      linarith
  -- the contentful regime kills the interior case
  have hfarwin : ∀ j : V, ¬(a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂) →
      eigvalOf B hB j ≤ SAv.min' hSAvne - δ
        ∨ SAv.max' hSAvne + δ ≤ eigvalOf B hB j := by
    intro j hj
    rcases hkey j hj with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (not_le.2 hcont)
  -- the window-existence transfer: the shrunk window selects A's cluster
  have hshrink : bandProjector A hA ((a₁ + SAv.min' hSAvne) / 2)
      (SAv.max' hSAvne) = bandProjector A hA a₁ b₁ := by
    refine bandProjector_eq_of_forall_mem_iff hA _ _ _ _
      (by linarith) ha₁ ?_
    intro i
    constructor
    · rintro ⟨hlow, hhigh⟩
      exact ⟨by linarith, le_trans hhigh hlmaxB⟩
    · rintro ⟨hlow, hhigh⟩
      have hiSA : i ∈ SA :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hlow, hhigh⟩⟩
      exact ⟨by have := hminle i hiSA; linarith, hlemax i hiSA⟩
  -- the identity reduces the difference; the transfer moves it to the
  -- shrunk window; the engine runs at the cluster-range center/radius
  rw [l2OpNorm_sub_eq_of_rank_eq
    (bandProjector_symmetric A hA a₁ b₁)
    (bandProjector_idempotent A hA a₁ b₁ ha₁)
    (bandProjector_symmetric B hB a₂ b₂)
    (bandProjector_idempotent B hB a₂ b₂ ha₂) hrank, ← hshrink]
  refine l2OpNorm_one_sub_bandProjector_mul_bandProjector_le_core
    hA hB ((a₁ + SAv.min' hSAvne) / 2) (SAv.max' hSAvne) a₂ b₂
    ((SAv.min' hSAvne + SAv.max' hSAvne) / 2)
    ((SAv.max' hSAvne - SAv.min' hSAvne) / 2) δ
    (by linarith) ha₂ hδ (by linarith) ?_ ?_
  · intro i h₁ h₂
    have hiSA : i ∈ SA := Finset.mem_filter.2 ⟨Finset.mem_univ _,
      ⟨by linarith, le_trans h₂ hlmaxB⟩⟩
    have hlo := hminle i hiSA
    have hhi := hlemax i hiSA
    rw [abs_le]
    constructor <;> linarith
  · intro j hj
    rcases hfarwin j hj with h | h
    · rw [le_abs]
      right
      have hneg : (SAv.max' hSAvne - SAv.min' hSAvne) / 2 + δ
          ≤ (SAv.min' hSAvne + SAv.max' hSAvne) / 2
            - eigvalOf B hB j := by
        have heq : ((SAv.min' hSAvne + SAv.max' hSAvne) / 2
              - eigvalOf B hB j)
            - ((SAv.max' hSAvne - SAv.min' hSAvne) / 2 + δ)
            - (SAv.min' hSAvne - eigvalOf B hB j - δ) = 0 := by ring
        linarith
      linarith
    · rw [le_abs]
      left
      have hpos : (SAv.max' hSAvne - SAv.min' hSAvne) / 2 + δ
          ≤ eigvalOf B hB j - (SAv.min' hSAvne + SAv.max' hSAvne) / 2 := by
        have heq : eigvalOf B hB j - (SAv.min' hSAvne + SAv.max' hSAvne) / 2
            - ((SAv.max' hSAvne - SAv.min' hSAvne) / 2 + δ)
            - (eigvalOf B hB j - (SAv.max' hSAvne + δ)) = 0 := by ring
        linarith
      exact hpos

end ClusterForm

/-! ## The symmetric form — two-sided separation, no rank hypothesis

`proposals/band-davis-kahan-symmetric.md` (the cluster form's own
first recorded follow-on): the separation stated on *both* sides — B's
out-of-window spectrum δ-away from A's in-window spectrum *and* A's
out-of-window spectrum δ-away from B's in-window spectrum — buys
dropping the rank hypothesis entirely, at constant 2 (the
Yu–Wang–Samworth Theorem 1 both-gaps selling point: the consumer
states spectral separation and nothing else — no multiplicity
counting).

The route (worked through in the proposal before any Lean):

- **Trivial regime** (`δ/2 ≤ ‖A − B‖`): `‖P − Q‖ ≤ 1 ≤ 2‖A − B‖/δ`.
- **Contentful regime** (`‖A − B‖ < δ/2`): the interior case of the
  cluster dichotomy is impossible (it forces `δ ≤ ‖A − B‖`), so the
  rank-free pairwise product bound below — the cluster theorem's
  dichotomy/shrink/engine body, factored once, with the identity
  conversion simply not performed — gives `‖(I − Q) * P‖ ≤ ‖A − B‖/δ`
  and, at swapped argument roles, `‖(I − P) * Q‖ ≤ ‖A − B‖/δ`. The
  ring identity `P − Q = (I − Q) * P − Q * (I − P)`, with the new
  public `l2OpNorm_transpose` moving the right-action product under
  the swapped bound (`P`, `Q` symmetric), closes by the triangle
  inequality. **The constant 2 is exactly that triangle** — no hidden
  loss. Unequal ranks cannot break the statement: they force
  `δ ≤ ‖A − B‖` (the eigenvector route), i.e. the trivial regime. -/
section SymmetricForm

variable {A B : Matrix V V ℝ}

/-- **Transpose invariance of the ℓ² operator norm.** `‖Mᵀ‖ = ‖M‖`: a
pairing `y ⬝ᵥ (Mᵀ *ᵥ x)` is a pairing `x ⬝ᵥ (M *ᵥ y)` of the original
matrix (the pin's `Matrix.dotProduct_mulVec` +
`Matrix.vecMul_transpose` + `Matrix.dotProduct_comm`), so the pairing
characterization bounds each side by the other. Absent from the
pinned Mathlib and from the shelf before this section; any consumer
that bounds a right action while the engine states the left action
(the exact situation of every two-sided perturbation argument) needs
it. -/
theorem l2OpNorm_transpose (M : Matrix V V ℝ) : ‖Mᵀ‖ = ‖M‖ := by
  have hle : ∀ N : Matrix V V ℝ, ‖Nᵀ‖ ≤ ‖N‖ := by
    intro N
    refine l2OpNorm_le_of_abs_dotProduct_le (norm_nonneg N) ?_
    intro x y
    have hcomm : y ⬝ᵥ (Nᵀ *ᵥ x) = x ⬝ᵥ (N *ᵥ y) := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      exact Matrix.dotProduct_comm _ _
    have hy : ‖pack y‖ = Real.sqrt (y ⬝ᵥ y) := norm_euclidean_eq_sqrt y
    have hny : ‖pack (N *ᵥ y)‖
        = Real.sqrt ((N *ᵥ y) ⬝ᵥ (N *ᵥ y)) := norm_euclidean_eq_sqrt (N *ᵥ y)
    have hact := l2OpNorm_mulVec_le N y
    rw [hcomm]
    calc |x ⬝ᵥ (N *ᵥ y)|
        ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt ((N *ᵥ y) ⬝ᵥ (N *ᵥ y)) :=
          abs_dotProduct_le x (N *ᵥ y)
      _ = Real.sqrt (x ⬝ᵥ x) * ‖pack (N *ᵥ y)‖ := by rw [← hny]
      _ ≤ Real.sqrt (x ⬝ᵥ x) * (‖N‖ * ‖pack y‖) :=
          mul_le_mul_of_nonneg_left hact (Real.sqrt_nonneg _)
      _ = ‖N‖ * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
          rw [← hy]; ring
  refine le_antisymm (hle M) ?_
  have h := hle Mᵀ
  rwa [Matrix.transpose_transpose] at h

/-- The difference of two square matrices decomposes along the two
one-sided complements (pure ring identity, no hypotheses):
`(I − Q) * P − Q * (I − P) = P − Q * P − (Q − Q * P) = P − Q`. The
symmetric form's triangle step. -/
private theorem sub_eq_one_sub_mul_sub_mul_one_sub (P Q : Matrix V V ℝ) :
    P - Q = (1 - Q) * P - Q * (1 - P) := by
  rw [sub_mul, mul_sub, mul_one, one_mul, sub_sub_sub_cancel_right]

/-- **The rank-free pairwise product bound** (private; the contentful
regime of the symmetric form, factored once and instantiated below at
both argument orders). Under pairwise separation *and* `‖A − B‖ < δ`,
the interior case of the cluster dichotomy is impossible (it forces
`δ ≤ ‖A − B‖`), so every out-of-window B-eigenvalue is δ-outside the
cluster *range*, and the complement engine runs at the cluster-range
center/radius through the window-shrink transfer. No rank hypothesis:
the empty-cluster corner is `P = 0` (norm 0), not the delivered
theorem's rank transfer. -/
private theorem l2OpNorm_one_sub_bandProjector_mul_bandProjector_le_pairwise
    (hA : A.IsSymm) (hB : B.IsSymm)
    (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ j, ¬(a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂) →
      ∀ i, a₁ < eigvalOf A hA i → eigvalOf A hA i ≤ b₁ →
      δ ≤ |eigvalOf B hB j - eigvalOf A hA i|)
    (hE : ‖A - B‖ < δ) :
    ‖(1 - bandProjector B hB a₂ b₂) * bandProjector A hA a₁ b₁‖
      ≤ ‖A - B‖ / δ := by
  classical
  -- A's cluster as an index set, its range as a value set
  set SA : Finset V := Finset.univ.filter
    fun i => a₁ < eigvalOf A hA i ∧ eigvalOf A hA i ≤ b₁ with hSAdef
  set SAv : Finset ℝ := SA.image fun i => eigvalOf A hA i with hSAvdef
  rcases SA.eq_empty_or_nonempty with hempty | hne
  · -- the empty-cluster corner: the product itself vanishes
    have hPzero : bandProjector A hA a₁ b₁ = 0 :=
      bandProjector_eq_zero_of_forall_not_mem hA a₁ b₁ ha₁
        (fun i hmem => absurd
          (show i ∈ SA from Finset.mem_filter.2 ⟨Finset.mem_univ _, hmem⟩)
          (by simp [hempty]))
    rw [hPzero, mul_zero, norm_zero]
    exact div_nonneg (norm_nonneg _) (le_of_lt hδ)
  -- the cluster range
  have hSAvne : SAv.Nonempty := hne.image _
  obtain ⟨i₀, hi₀SA, hi₀val⟩ := Finset.mem_image.1 (SAv.min'_mem hSAvne)
  obtain ⟨i₁, hi₁SA, hi₁val⟩ := Finset.mem_image.1 (SAv.max'_mem hSAvne)
  have hwin₀ : a₁ < eigvalOf A hA i₀ ∧ eigvalOf A hA i₀ ≤ b₁ :=
    (Finset.mem_filter.1 hi₀SA).2
  have hwin₁ : a₁ < eigvalOf A hA i₁ ∧ eigvalOf A hA i₁ ≤ b₁ :=
    (Finset.mem_filter.1 hi₁SA).2
  have hminle : ∀ i ∈ SA, SAv.min' hSAvne ≤ eigvalOf A hA i := by
    intro i hi
    have hvv : eigvalOf A hA i ∈ SAv :=
      Finset.mem_image.2 ⟨i, hi, rfl⟩
    rw [show SAv.min' hSAvne = SAv.min' ⟨eigvalOf A hA i, hvv⟩ from
      congrArg (SAv.min') (proof_irrel hSAvne ⟨eigvalOf A hA i, hvv⟩)]
    exact SAv.min'_le _ hvv
  have hlemax : ∀ i ∈ SA, eigvalOf A hA i ≤ SAv.max' hSAvne := by
    intro i hi
    have hvv : eigvalOf A hA i ∈ SAv :=
      Finset.mem_image.2 ⟨i, hi, rfl⟩
    rw [show SAv.max' hSAvne = SAv.max' ⟨eigvalOf A hA i, hvv⟩ from
      congrArg (SAv.max') (proof_irrel hSAvne ⟨eigvalOf A hA i, hvv⟩)]
    exact SAv.le_max' _ hvv
  -- the cluster range brackets
  have hlimA : a₁ < SAv.min' hSAvne := by
    rw [← hi₀val]; exact hwin₀.1
  have hlmaxB : SAv.max' hSAvne ≤ b₁ := by
    rw [← hi₁val]; exact hwin₁.2
  have hshalmax : SAv.min' hSAvne ≤ SAv.max' hSAvne := by
    have h₀ := hminle i₁ hi₁SA
    rw [hi₁val] at h₀
    exact h₀
  -- the dichotomy: every out-of-window B-eigenvalue is δ-outside the
  -- cluster range (the interior case forces δ ≤ ‖A - B‖, excluded)
  have hfarwin : ∀ j : V, ¬(a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂) →
      eigvalOf B hB j ≤ SAv.min' hSAvne - δ
        ∨ SAv.max' hSAvne + δ ≤ eigvalOf B hB j := by
    intro j hjout
    rcases lt_or_ge (eigvalOf B hB j) (SAv.min' hSAvne) with hμ | hμ
    · refine Or.inl ?_
      have h := hsep j hjout i₀ hwin₀.1 hwin₀.2
      rw [hi₀val] at h
      have hnn : 0 ≤ SAv.min' hSAvne - eigvalOf B hB j := by linarith
      rw [abs_sub_comm, abs_of_nonneg hnn] at h
      linarith
    rcases lt_or_ge (eigvalOf B hB j) (SAv.max' hSAvne) with hμ' | hμ'
    · -- between the range endpoints: the interior case, impossible here
      have hbelow : SAv.min' hSAvne + δ ≤ eigvalOf B hB j := by
        have h := hsep j hjout i₀ hwin₀.1 hwin₀.2
        rw [hi₀val] at h
        have hne' : eigvalOf B hB j ≠ SAv.min' hSAvne := by
          intro heq
          rw [heq] at h
          rw [sub_self, abs_zero] at h
          exact absurd h (not_le.2 hδ)
        have hnn : 0 ≤ eigvalOf B hB j - SAv.min' hSAvne := by linarith
        rw [abs_of_nonneg hnn] at h
        linarith
      have habove : eigvalOf B hB j ≤ SAv.max' hSAvne - δ := by
        have h := hsep j hjout i₁ hwin₁.1 hwin₁.2
        rw [hi₁val] at h
        have hne' : eigvalOf B hB j ≠ SAv.max' hSAvne := by
          intro heq
          rw [heq] at h
          rw [sub_self, abs_zero] at h
          exact absurd h (not_le.2 hδ)
        have hnn : 0 ≤ SAv.max' hSAvne - eigvalOf B hB j := by linarith
        rw [abs_sub_comm, abs_of_nonneg hnn] at h
        linarith
      -- δ ≤ ‖A - B‖ by the eigenvector route — contradicting hE
      have hfar : ∀ i, δ ≤ |eigvalOf A hA i - eigvalOf B hB j| := by
        intro i
        rcases le_or_lt (eigvalOf A hA i) a₁ with hlowA | hlowA
        · have habs : 0 ≤ eigvalOf B hB j - eigvalOf A hA i := by linarith
          rw [abs_sub_comm, abs_of_nonneg habs]
          linarith
        rcases le_or_lt (eigvalOf A hA i) b₁ with hhighA | hhighA
        · rw [abs_sub_comm]
          exact hsep j hjout i hlowA hhighA
        · have habs : 0 ≤ eigvalOf A hA i - eigvalOf B hB j := by linarith
          rw [abs_of_nonneg habs]
          linarith
      have := norm_sub_ge_of_far_eigvalOf hA hB hδ j hfar
      exact absurd this (not_le.2 hE)
    · refine Or.inr ?_
      have hne' : eigvalOf B hB j ≠ SAv.max' hSAvne := by
        intro heq
        have h := hsep j hjout i₁ hwin₁.1 hwin₁.2
        rw [hi₁val, ← heq, sub_self, abs_zero] at h
        exact absurd h (not_le.2 hδ)
      have h := hsep j hjout i₁ hwin₁.1 hwin₁.2
      rw [hi₁val] at h
      have hnn : 0 ≤ eigvalOf B hB j - SAv.max' hSAvne := by linarith
      rw [abs_of_nonneg hnn] at h
      linarith
  -- the window-existence transfer: the shrunk window selects A's cluster
  have hshrink : bandProjector A hA ((a₁ + SAv.min' hSAvne) / 2)
      (SAv.max' hSAvne) = bandProjector A hA a₁ b₁ := by
    refine bandProjector_eq_of_forall_mem_iff hA _ _ _ _
      (by linarith) ha₁ ?_
    intro i
    constructor
    · rintro ⟨hlow, hhigh⟩
      exact ⟨by linarith, le_trans hhigh hlmaxB⟩
    · rintro ⟨hlow, hhigh⟩
      have hiSA : i ∈ SA :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hlow, hhigh⟩⟩
      exact ⟨by have := hminle i hiSA; linarith, hlemax i hiSA⟩
  -- the engine runs at the cluster-range center/radius, no identity
  -- conversion (that is the entire difference from the cluster form)
  rw [← hshrink]
  refine l2OpNorm_one_sub_bandProjector_mul_bandProjector_le_core
    hA hB ((a₁ + SAv.min' hSAvne) / 2) (SAv.max' hSAvne) a₂ b₂
    ((SAv.min' hSAvne + SAv.max' hSAvne) / 2)
    ((SAv.max' hSAvne - SAv.min' hSAvne) / 2) δ
    (by linarith) ha₂ hδ (by linarith) ?_ ?_
  · intro i h₁ h₂
    have hiSA : i ∈ SA := Finset.mem_filter.2 ⟨Finset.mem_univ _,
      ⟨by linarith, le_trans h₂ hlmaxB⟩⟩
    have hlo := hminle i hiSA
    have hhi := hlemax i hiSA
    rw [abs_le]
    constructor <;> linarith
  · intro j hj
    rcases hfarwin j hj with h | h
    · rw [le_abs]
      right
      have hneg : (SAv.max' hSAvne - SAv.min' hSAvne) / 2 + δ
          ≤ (SAv.min' hSAvne + SAv.max' hSAvne) / 2
            - eigvalOf B hB j := by
        have heq : ((SAv.min' hSAvne + SAv.max' hSAvne) / 2
              - eigvalOf B hB j)
            - ((SAv.max' hSAvne - SAv.min' hSAvne) / 2 + δ)
            - (SAv.min' hSAvne - eigvalOf B hB j - δ) = 0 := by ring
        linarith
      linarith
    · rw [le_abs]
      left
      have hpos : (SAv.max' hSAvne - SAv.min' hSAvne) / 2 + δ
          ≤ eigvalOf B hB j - (SAv.min' hSAvne + SAv.max' hSAvne) / 2 := by
        have heq : eigvalOf B hB j - (SAv.min' hSAvne + SAv.max' hSAvne) / 2
            - ((SAv.max' hSAvne - SAv.min' hSAvne) / 2 + δ)
            - (eigvalOf B hB j - (SAv.max' hSAvne + δ)) = 0 := by ring
        linarith
      exact hpos

/-- **Band Davis–Kahan, difference form, two-sided (symmetric)
separation — no rank hypothesis.** If every eigenvalue of `B`
*outside* its window is δ-away from every eigenvalue of `A` *inside*
its window, **and** every eigenvalue of `A` *outside* its window is
δ-away from every eigenvalue of `B` *inside* its window, then

`‖P_A - P_B‖ ≤ 2 * ‖A - B‖ / δ`, constant 2,

with **no hypothesis on the projectors' ranks** — the
Yu–Wang–Samworth Theorem 1 both-gaps selling point: the consumer
states spectral separation and nothing else (no multiplicity
counting through `rank_bandProjector_eq_card`). The constant 2 is
exactly the triangle inequality at the decomposition
`P - Q = (I - Q) * P - Q * (I - P)`; no hidden loss. On equal-rank
inputs the pairwise theorem above gives the strictly better constant
1; this form's value is uniformity. When the ranks differ, `δ ≤ ‖A -
B‖` is forced (the eigenvector route inside the proof), so the bound
degrades to the trivial regime `1 ≤ 2‖A - B‖/δ` — honest, exactly as
in the textbook both-gaps form. `hsepBA` is verbatim the pairwise
theorem's `hsep`; `hsepAB` is its mirror.

Route provenance (the statement is proved, not admitted): Yu, Wang &
Samworth 2015, Theorem 1 — the two-sided (both-gaps) variants at
constant 2, already the cited source family of the band forms; see
the module documentation and `proposals/band-davis-kahan-symmetric.md`.

QA: `Scaffold/QA/Perturbation/BandDavisKahanSymm_QA.lean` — the
unequal-rank rank-free witness (the delivered family's hypothesis
exhibited failing on the very fixture this theorem covers), the ε = 0
attainment, the `hsepAB`-isolated fence (the mirror of the cluster
QA's `hsep` fence — together the two separation sides are isolated
across the QA family), and the decomposition-coherence witness. -/
theorem l2OpNorm_bandProjector_sub_bandProjector_le_two_of_symm
    (hA : A.IsSymm) (hB : B.IsSymm)
    (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂)
    {δ : ℝ} (hδ : 0 < δ)
    (hsepAB : ∀ i, ¬(a₁ < eigvalOf A hA i ∧ eigvalOf A hA i ≤ b₁) →
      ∀ j, a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂ →
      δ ≤ |eigvalOf A hA i - eigvalOf B hB j|)
    (hsepBA : ∀ j, ¬(a₂ < eigvalOf B hB j ∧ eigvalOf B hB j ≤ b₂) →
      ∀ i, a₁ < eigvalOf A hA i → eigvalOf A hA i ≤ b₁ →
      δ ≤ |eigvalOf B hB j - eigvalOf A hA i|) :
    ‖bandProjector A hA a₁ b₁ - bandProjector B hB a₂ b₂‖
      ≤ 2 * ‖A - B‖ / δ := by
  rcases le_or_lt (δ / 2) ‖A - B‖ with htriv | hcont
  · -- the trivial regime
    calc ‖bandProjector A hA a₁ b₁ - bandProjector B hB a₂ b₂‖
        ≤ 1 := l2OpNorm_sub_le_one_of_isSymm_idempotent
          (bandProjector_symmetric A hA a₁ b₁)
          (bandProjector_idempotent A hA a₁ b₁ ha₁)
          (bandProjector_symmetric B hB a₂ b₂)
          (bandProjector_idempotent B hB a₂ b₂ ha₂)
      _ ≤ 2 * ‖A - B‖ / δ := by
          rw [le_div_iff₀ hδ]
          linarith
  · -- the contentful regime: both product bounds, then decompose
    have hE1 : ‖A - B‖ < δ := by linarith
    have hE2 : ‖B - A‖ < δ := by rw [norm_sub_rev]; exact hE1
    have h1 := l2OpNorm_one_sub_bandProjector_mul_bandProjector_le_pairwise
      hA hB a₁ b₁ a₂ b₂ ha₁ ha₂ hδ hsepBA hE1
    have h2 := l2OpNorm_one_sub_bandProjector_mul_bandProjector_le_pairwise
      hB hA a₂ b₂ a₁ b₁ ha₂ ha₁ hδ
      (fun i hi j h1 h2' => hsepAB i hi j ⟨h1, h2'⟩) hE2
    have hBA : ‖B - A‖ = ‖A - B‖ := norm_sub_rev B A
    rw [hBA] at h2
    have hPT : (bandProjector A hA a₁ b₁)ᵀ
        = bandProjector A hA a₁ b₁ := bandProjector_symmetric A hA a₁ b₁
    have hQT : (bandProjector B hB a₂ b₂)ᵀ
        = bandProjector B hB a₂ b₂ := bandProjector_symmetric B hB a₂ b₂
    have hIPT : (1 - bandProjector A hA a₁ b₁)ᵀ
        = 1 - bandProjector A hA a₁ b₁ := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, hPT]
    have htrans : bandProjector B hB a₂ b₂
        * (1 - bandProjector A hA a₁ b₁)
        = ((1 - bandProjector A hA a₁ b₁)
            * bandProjector B hB a₂ b₂)ᵀ := by
      rw [Matrix.transpose_mul, hQT, hIPT]
    calc ‖bandProjector A hA a₁ b₁ - bandProjector B hB a₂ b₂‖
        = ‖(1 - bandProjector B hB a₂ b₂) * bandProjector A hA a₁ b₁
            - bandProjector B hB a₂ b₂
              * (1 - bandProjector A hA a₁ b₁)‖ := by
          rw [sub_eq_one_sub_mul_sub_mul_one_sub]
      _ ≤ ‖(1 - bandProjector B hB a₂ b₂) * bandProjector A hA a₁ b₁‖
          + ‖bandProjector B hB a₂ b₂
              * (1 - bandProjector A hA a₁ b₁)‖ := norm_sub_le _ _
      _ = ‖(1 - bandProjector B hB a₂ b₂) * bandProjector A hA a₁ b₁‖
          + ‖(1 - bandProjector A hA a₁ b₁)
              * bandProjector B hB a₂ b₂‖ := by
          rw [htrans, l2OpNorm_transpose]
      _ ≤ ‖A - B‖ / δ + ‖A - B‖ / δ := add_le_add h1 h2
      _ = 2 * ‖A - B‖ / δ := by ring

end SymmetricForm


/-! ## The set form — cluster projectors, no windows

`proposals/cluster-projector.md` (the cluster/symmetric deliveries'
recorded follow-on): the same commutator/shift engine re-run at
`GraphTheory.ClusterProjector`'s set-valued projectors, with the
hypotheses stated *between the clusters as sets* — A's cluster within
`r` of `c`, B's cluster δ-far outside — and **no interior/boundary
dichotomy**: the difference form reduces to the product form through the
complement law `1 − Q_T = Q_{Tᶜ}` (a definition-level fact the window
family lacks, which is why the window difference form needed its
separate complement engine). The component action
`eigvecOf_dotProduct_clusterProjector_mulVec` is the engine's only
projector input, exactly as for bands. -/

section SetForm

variable {A B : Matrix V V ℝ}

/-- **(F1, set form) compression:** the shifted action on A's
cluster-filtered vector has norm at most `r * ‖y‖`, whenever every
in-cluster eigenvalue of `A` lies within `r` of `c`. -/
private theorem norm_pack_shift_clusterProjector_mulVec_le
    (hA : A.IsSymm) (S : Set ℝ) (c r : ℝ) (hr : 0 ≤ r)
    (hnear : ∀ i, eigvalOf A hA i ∈ S → |eigvalOf A hA i - c| ≤ r)
    (y : V → ℝ) :
    ‖pack ((A - c • 1) *ᵥ (clusterProjector A hA S *ᵥ y))‖
      ≤ r * ‖pack y‖ := by
  classical
  have hcomp : ∀ i : V, Matrix.dotProduct (eigvecOf A hA i)
      ((A - c • 1) *ᵥ (clusterProjector A hA S *ᵥ y))
      = (eigvalOf A hA i - c)
        * (if eigvalOf A hA i ∈ S then (1 : ℝ) else 0)
        * Matrix.dotProduct (eigvecOf A hA i) y := by
    intro i
    simp only [Matrix.sub_mulVec, Matrix.dotProduct_sub,
      dotProduct_eigvecOf_mulVec hA,
      eigvecOf_dotProduct_clusterProjector_mulVec hA S i,
      Matrix.smul_mulVec_assoc, Matrix.one_mulVec, Matrix.mulVec_smul,
      Matrix.dotProduct_smul, smul_eq_mul, sub_mul]
    ring
  have hsq : ((A - c • 1) *ᵥ (clusterProjector A hA S *ᵥ y)) ⬝ᵥ
      ((A - c • 1) *ᵥ (clusterProjector A hA S *ᵥ y))
      ≤ r * r * (y ⬝ᵥ y) := by
    have hterm : ∀ i : V,
        (Matrix.dotProduct (eigvecOf A hA i)
          ((A - c • 1) *ᵥ (clusterProjector A hA S *ᵥ y)))
          * (Matrix.dotProduct (eigvecOf A hA i)
          ((A - c • 1) *ᵥ (clusterProjector A hA S *ᵥ y)))
        ≤ (r * r)
          * (Matrix.dotProduct (eigvecOf A hA i) y
            * Matrix.dotProduct (eigvecOf A hA i) y) := by
      intro i
      rw [hcomp i]
      by_cases hband : eigvalOf A hA i ∈ S
      · rw [if_pos hband, mul_one]
        have habs := hnear i hband
        obtain ⟨hl, hu⟩ := abs_le.mp habs
        have hkey : (eigvalOf A hA i - c) * (eigvalOf A hA i - c)
            ≤ r * r := by
          have := sq_le_sq' hl hu
          simpa [sq] using this
        nlinarith [hkey, mul_self_nonneg
          (Matrix.dotProduct (eigvecOf A hA i) y)]
      · rw [if_neg hband]
        have hzero : ((eigvalOf A hA i - c) * (0 : ℝ)
            * Matrix.dotProduct (eigvecOf A hA i) y)
            * ((eigvalOf A hA i - c) * (0 : ℝ)
            * Matrix.dotProduct (eigvecOf A hA i) y) = 0 := by ring
        rw [hzero]
        exact mul_nonneg (mul_nonneg hr hr) (mul_self_nonneg _)
    rw [dotProduct_eigvecOf hA ((A - c • 1) *ᵥ
      (clusterProjector A hA S *ᵥ y)) ((A - c • 1) *ᵥ
      (clusterProjector A hA S *ᵥ y))]
    calc ∑ i : V, (Matrix.dotProduct (eigvecOf A hA i)
          ((A - c • 1) *ᵥ (clusterProjector A hA S *ᵥ y)))
          * (Matrix.dotProduct (eigvecOf A hA i)
          ((A - c • 1) *ᵥ (clusterProjector A hA S *ᵥ y)))
        ≤ ∑ i : V, (r * r)
            * (Matrix.dotProduct (eigvecOf A hA i) y
              * Matrix.dotProduct (eigvecOf A hA i) y) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = r * r * (y ⬝ᵥ y) := by
          rw [show y ⬝ᵥ y = ∑ i, Matrix.dotProduct (eigvecOf A hA i) y
              * Matrix.dotProduct (eigvecOf A hA i) y from
            dotProduct_eigvecOf hA y y, ← Finset.mul_sum]
  have hnn : 0 ≤ ‖pack ((A - c • 1) *ᵥ
      (clusterProjector A hA S *ᵥ y))‖ := norm_nonneg _
  have hnn' : 0 ≤ ‖pack y‖ := norm_nonneg _
  have hsqrt : ‖pack ((A - c • 1) *ᵥ
      (clusterProjector A hA S *ᵥ y))‖ ^ 2
      ≤ (r * ‖pack y‖) ^ 2 := by
    rw [mul_pow, norm_pack_sq, norm_pack_sq, pow_two]
    exact hsq
  have habs := abs_le_of_sq_le_sq hsqrt (mul_nonneg hr hnn')
  rwa [abs_of_nonneg hnn] at habs

/-- **Range invariance, set form:** the shifted cluster-filtered vector
stays in the cluster's range — its out-of-cluster eigencomponents
vanish, so the cluster projector fixes it. -/
private theorem clusterProjector_mulVec_shift_self (hA : A.IsSymm)
    (S : Set ℝ) (c : ℝ) (y : V → ℝ) :
    clusterProjector A hA S *ᵥ
      ((A - c • 1) *ᵥ (clusterProjector A hA S *ᵥ y))
      = (A - c • 1) *ᵥ (clusterProjector A hA S *ᵥ y) := by
  classical
  refine eq_of_forall_dotProduct_eigvecOf_eq hA _ _ fun i => ?_
  rw [eigvecOf_dotProduct_clusterProjector_mulVec hA S i]
  have hcomp : Matrix.dotProduct (eigvecOf A hA i)
      ((A - c • 1) *ᵥ (clusterProjector A hA S *ᵥ y))
      = (eigvalOf A hA i - c)
        * (if eigvalOf A hA i ∈ S then (1 : ℝ) else 0)
        * Matrix.dotProduct (eigvecOf A hA i) y := by
    simp only [Matrix.sub_mulVec, Matrix.dotProduct_sub,
      dotProduct_eigvecOf_mulVec hA,
      eigvecOf_dotProduct_clusterProjector_mulVec hA S i,
      Matrix.smul_mulVec_assoc, Matrix.one_mulVec, Matrix.mulVec_smul,
      Matrix.dotProduct_smul, smul_eq_mul, sub_mul]
    ring
  rw [hcomp]
  by_cases hband : eigvalOf A hA i ∈ S
  · rw [if_pos hband, one_mul]
  · rw [if_neg hband]
    ring

/-- **(F2, set form) expansion:** for a vector fixed by B's cluster
projector, the shifted action expands by at least `r + δ`, whenever
every in-cluster eigenvalue of `B` lies at distance `≥ r + δ` from
`c`. -/
private theorem norm_pack_shift_apply_ge_of_mem (hB : B.IsSymm)
    (T : Set ℝ) (c r δ : ℝ) (hrδ : 0 ≤ r + δ)
    (hfar : ∀ j, eigvalOf B hB j ∈ T → r + δ ≤ |eigvalOf B hB j - c|)
    (z : V → ℝ) (hz : clusterProjector B hB T *ᵥ z = z) :
    (r + δ) * ‖pack z‖ ≤ ‖pack ((B - c • 1) *ᵥ z)‖ := by
  classical
  have hzcomp : ∀ j, Matrix.dotProduct (eigvecOf B hB j) z
      = (if eigvalOf B hB j ∈ T then (1 : ℝ) else 0)
        * Matrix.dotProduct (eigvecOf B hB j) z := by
    intro j
    calc Matrix.dotProduct (eigvecOf B hB j) z
        = Matrix.dotProduct (eigvecOf B hB j)
            (clusterProjector B hB T *ᵥ z) := by rw [hz]
      _ = (if eigvalOf B hB j ∈ T then (1 : ℝ) else 0)
          * Matrix.dotProduct (eigvecOf B hB j) z :=
          eigvecOf_dotProduct_clusterProjector_mulVec hB T j z
  have hcomp : ∀ j, Matrix.dotProduct (eigvecOf B hB j) ((B - c • 1) *ᵥ z)
      = (eigvalOf B hB j - c)
        * Matrix.dotProduct (eigvecOf B hB j) z := by
    intro j
    simp only [Matrix.sub_mulVec, Matrix.dotProduct_sub,
      dotProduct_eigvecOf_mulVec hB,
      Matrix.smul_mulVec_assoc, Matrix.one_mulVec, Matrix.mulVec_smul,
      Matrix.dotProduct_smul, smul_eq_mul, sub_mul]
  have hsum : (r + δ) * (r + δ) * (z ⬝ᵥ z)
      ≤ ((B - c • 1) *ᵥ z) ⬝ᵥ ((B - c • 1) *ᵥ z) := by
    have hsplit : (r + δ) * (r + δ) * (z ⬝ᵥ z)
        = ∑ j, (r + δ) * (r + δ)
          * (Matrix.dotProduct (eigvecOf B hB j) z
            * Matrix.dotProduct (eigvecOf B hB j) z) := by
      rw [dotProduct_eigvecOf hB z z, ← Finset.mul_sum]
    rw [hsplit, dotProduct_eigvecOf hB ((B - c • 1) *ᵥ z)
      ((B - c • 1) *ᵥ z)]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hcomp j, hzcomp j]
    by_cases hband : eigvalOf B hB j ∈ T
    · rw [if_pos hband, one_mul]
      have habs := hfar j hband
      have hkey : (r + δ) * (r + δ)
          ≤ (eigvalOf B hB j - c) * (eigvalOf B hB j - c) :=
        le_trans (mul_self_le_mul_self hrδ habs)
          (le_of_eq (abs_mul_abs_self _))
      nlinarith [hkey, mul_self_nonneg (Matrix.dotProduct (eigvecOf B hB j) z)]
    · simp [hband]
  have hnn : 0 ≤ ‖pack z‖ := norm_nonneg _
  have hnn' : 0 ≤ ‖pack ((B - c • 1) *ᵥ z)‖ := norm_nonneg _
  have hsqrt : ((r + δ) * ‖pack z‖) ^ 2
      ≤ ‖pack ((B - c • 1) *ᵥ z)‖ ^ 2 := by
    rw [mul_pow, norm_pack_sq, norm_pack_sq, pow_two]
    exact hsum
  have habs := abs_le_of_sq_le_sq hsqrt hnn'
  rwa [abs_of_nonneg (mul_nonneg hrδ hnn)] at habs

/-- The cluster projector's action is contractive (Parseval +
component action: the filtered signal's squared norm is a sub-sum of
the input's eigencomponent energy). -/
private theorem norm_pack_clusterProjector_mulVec_le {M : Matrix V V ℝ}
    (hM : M.IsSymm) (S : Set ℝ) (y : V → ℝ) :
    ‖pack (clusterProjector M hM S *ᵥ y)‖ ≤ ‖pack y‖ := by
  classical
  have hsq : (clusterProjector M hM S *ᵥ y) ⬝ᵥ
      (clusterProjector M hM S *ᵥ y) ≤ y ⬝ᵥ y := by
    rw [dotProduct_eigvecOf hM (clusterProjector M hM S *ᵥ y)
      (clusterProjector M hM S *ᵥ y), dotProduct_eigvecOf hM y y]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [eigvecOf_dotProduct_clusterProjector_mulVec hM S i y]
    by_cases hband : eigvalOf M hM i ∈ S
    · rw [if_pos hband, one_mul]
    · rw [if_neg hband, zero_mul, zero_mul]
      exact mul_self_nonneg _
  have habs : |‖pack (clusterProjector M hM S *ᵥ y)‖| ≤ ‖pack y‖ := by
    refine abs_le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [norm_pack_sq, norm_pack_sq]
    exact hsq
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- The shifted cluster commutation (the scalar shift commutes with
everything). -/
private theorem mulVec_clusterProjector_comm_shift {M : Matrix V V ℝ}
    (hM : M.IsSymm) (S : Set ℝ) (c : ℝ) (u : V → ℝ) :
    (M - c • 1) *ᵥ ((clusterProjector M hM S) *ᵥ u)
      = (clusterProjector M hM S) *ᵥ ((M - c • 1) *ᵥ u) := by
  have hL : (M - c • 1) *ᵥ (clusterProjector M hM S *ᵥ u)
      = M *ᵥ (clusterProjector M hM S *ᵥ u)
        - c • (clusterProjector M hM S *ᵥ u) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
  have hR : clusterProjector M hM S *ᵥ ((M - c • 1) *ᵥ u)
      = clusterProjector M hM S *ᵥ (M *ᵥ u)
        - c • (clusterProjector M hM S *ᵥ u) := by
    simp only [Matrix.sub_mulVec, Matrix.mulVec_sub,
      Matrix.smul_mulVec_assoc, Matrix.one_mulVec, Matrix.mulVec_smul]
  rw [hL, hR, mulVec_clusterProjector_comm hM S u]

/-- **Band Davis–Kahan, set form, product.** If `P_S` and `Q_T` are
the cluster projectors of two symmetric matrices `A` and `B` at sets
`S` and `T`, and there are `c, r` with every in-`S` eigenvalue of `A`
within `r` of `c` and every in-`T` eigenvalue of `B` at distance at
least `r + δ` from `c` — the hypotheses the algebraic engine actually
consumes, stated between the clusters as sets — then

`‖Q_T * P_S‖ ≤ ‖A - B‖ / δ`, constant 1.

No interval structure is assumed of `S` or `T`: the clusters may be
unions of intervals, scattered sets, anything. At `S = Set.Ioc a₁ b₁`
and `T = Set.Ioc a₂ b₂` this specializes to the window product theorem
above through `clusterProjector_eq_bandProjector`.

Route provenance (the statement is proved, not admitted): the
Vershynin/Davis–Kahan commutator-shift technique as in this module's
window forms; the set statement shape is the cluster form of
Yu–Wang–Samworth 2015 Theorem 1 (see `proposals/cluster-projector.md`).

QA: `Scaffold/QA/Perturbation/ClusterProjector_QA.lean` — the
non-interval difference witness and fence below, plus the interface
witnesses in the same file. -/
theorem l2OpNorm_clusterProjector_mul_clusterProjector_le
    (hA : A.IsSymm) (hB : B.IsSymm) (S T : Set ℝ) (c r δ : ℝ)
    (hδ : 0 < δ) (hr : 0 ≤ r)
    (hnear : ∀ i, eigvalOf A hA i ∈ S → |eigvalOf A hA i - c| ≤ r)
    (hfar : ∀ j, eigvalOf B hB j ∈ T → r + δ ≤ |eigvalOf B hB j - c|) :
    ‖clusterProjector B hB T * clusterProjector A hA S‖
      ≤ ‖A - B‖ / δ := by
  classical
  have hQidem := clusterProjector_idempotent B hB T
  have hrδ : 0 ≤ r + δ := by linarith
  have hpos : 0 < r + δ := by linarith
  have hCnn : 0 ≤ (r * ‖clusterProjector B hB T
      * clusterProjector A hA S‖ + ‖A - B‖) / (r + δ) :=
    div_nonneg (add_nonneg (mul_nonneg hr (norm_nonneg _)) (norm_nonneg _))
      (le_of_lt hpos)
  have hmaster : ∀ y : V → ℝ,
      ‖pack ((clusterProjector B hB T
        * clusterProjector A hA S) *ᵥ y)‖
        ≤ ((r * ‖clusterProjector B hB T
          * clusterProjector A hA S‖ + ‖A - B‖) / (r + δ)) * ‖pack y‖ := by
    intro y
    have hzQ : clusterProjector B hB T *ᵥ
        ((clusterProjector B hB T * clusterProjector A hA S) *ᵥ y)
        = (clusterProjector B hB T * clusterProjector A hA S) *ᵥ y := by
      calc clusterProjector B hB T *ᵥ
          ((clusterProjector B hB T * clusterProjector A hA S) *ᵥ y)
          = (clusterProjector B hB T
              * (clusterProjector B hB T * clusterProjector A hA S)) *ᵥ y :=
            Matrix.mulVec_mulVec y (clusterProjector B hB T)
              (clusterProjector B hB T * clusterProjector A hA S)
        _ = (clusterProjector B hB T * clusterProjector A hA S) *ᵥ y := by
            rw [← Matrix.mul_assoc, hQidem]
    have hF2 := norm_pack_shift_apply_ge_of_mem hB T c r δ hrδ hfar _ hzQ
    have hsplit : (B - c • 1) *ᵥ
        ((clusterProjector B hB T * clusterProjector A hA S) *ᵥ y)
        = clusterProjector B hB T *ᵥ ((A - c • 1) *ᵥ
            (clusterProjector A hA S *ᵥ y))
          + clusterProjector B hB T *ᵥ ((B - A) *ᵥ
            (clusterProjector A hA S *ᵥ y)) := by
      have e1 : (B - c • 1) *ᵥ
          ((clusterProjector B hB T * clusterProjector A hA S) *ᵥ y)
          = (B - c • 1) *ᵥ (clusterProjector B hB T *ᵥ
              (clusterProjector A hA S *ᵥ y)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
          Matrix.mulVec_mulVec]
      rw [e1, mulVec_clusterProjector_comm_shift hB T c
        (clusterProjector A hA S *ᵥ y),
        sub_one_mulVec_split c (clusterProjector A hA S *ᵥ y),
        Matrix.mulVec_add]
    have hT1 : ‖pack (clusterProjector B hB T *ᵥ ((A - c • 1) *ᵥ
        (clusterProjector A hA S *ᵥ y)))‖
        ≤ ‖clusterProjector B hB T * clusterProjector A hA S‖
          * (r * ‖pack y‖) := by
      have hw : clusterProjector A hA S *ᵥ ((A - c • 1) *ᵥ
          (clusterProjector A hA S *ᵥ y))
          = (A - c • 1) *ᵥ (clusterProjector A hA S *ᵥ y) :=
        clusterProjector_mulVec_shift_self hA S c y
      have hact : clusterProjector B hB T *ᵥ ((A - c • 1) *ᵥ
          (clusterProjector A hA S *ᵥ y))
          = (clusterProjector B hB T * clusterProjector A hA S) *ᵥ
              ((A - c • 1) *ᵥ (clusterProjector A hA S *ᵥ y)) := by
        conv_lhs => rw [← hw]
        rw [Matrix.mulVec_mulVec]
      rw [hact]
      have h1 := l2OpNorm_mulVec_le (clusterProjector B hB T
        * clusterProjector A hA S) ((A - c • 1) *ᵥ
        (clusterProjector A hA S *ᵥ y))
      have h2 := norm_pack_shift_clusterProjector_mulVec_le hA S c r hr
        hnear y
      calc ‖pack ((clusterProjector B hB T
              * clusterProjector A hA S) *ᵥ
              ((A - c • 1) *ᵥ (clusterProjector A hA S *ᵥ y)))‖
          ≤ ‖clusterProjector B hB T * clusterProjector A hA S‖
              * ‖pack ((A - c • 1) *ᵥ
                  (clusterProjector A hA S *ᵥ y))‖ := h1
        _ ≤ ‖clusterProjector B hB T * clusterProjector A hA S‖
              * (r * ‖pack y‖) :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have hT2 : ‖pack (clusterProjector B hB T *ᵥ ((B - A) *ᵥ
        (clusterProjector A hA S *ᵥ y)))‖
        ≤ ‖A - B‖ * ‖pack y‖ := by
      have h1 := l2OpNorm_mulVec_le (B - A)
        (clusterProjector A hA S *ᵥ y)
      have h2 := norm_pack_clusterProjector_mulVec_le hA S y
      have hkey : ‖pack (clusterProjector B hB T *ᵥ ((B - A) *ᵥ
          (clusterProjector A hA S *ᵥ y)))‖
          ≤ ‖pack ((B - A) *ᵥ (clusterProjector A hA S *ᵥ y))‖ :=
        norm_pack_clusterProjector_mulVec_le hB T _
      calc ‖pack (clusterProjector B hB T *ᵥ ((B - A) *ᵥ
              (clusterProjector A hA S *ᵥ y)))‖
          ≤ ‖pack ((B - A) *ᵥ (clusterProjector A hA S *ᵥ y))‖ := hkey
        _ ≤ ‖B - A‖ * ‖pack (clusterProjector A hA S *ᵥ y)‖ := h1
        _ ≤ ‖B - A‖ * ‖pack y‖ :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = ‖A - B‖ * ‖pack y‖ := by rw [norm_sub_rev]
    have hmid : (r + δ) * ‖pack ((clusterProjector B hB T
        * clusterProjector A hA S) *ᵥ y)‖
        ≤ (r * ‖clusterProjector B hB T * clusterProjector A hA S‖
            + ‖A - B‖) * ‖pack y‖ := by
      have hsplitnorm : ‖pack ((B - c • 1) *ᵥ
          ((clusterProjector B hB T * clusterProjector A hA S) *ᵥ y))‖
          ≤ (r * ‖clusterProjector B hB T * clusterProjector A hA S‖
              + ‖A - B‖) * ‖pack y‖ := by
        have hadd : ‖pack ((B - c • 1) *ᵥ
            ((clusterProjector B hB T * clusterProjector A hA S) *ᵥ y))‖
            ≤ ‖pack (clusterProjector B hB T *ᵥ ((A - c • 1) *ᵥ
                (clusterProjector A hA S *ᵥ y)))‖
              + ‖pack (clusterProjector B hB T *ᵥ ((B - A) *ᵥ
                (clusterProjector A hA S *ᵥ y)))‖ := by
          have hvec : pack ((B - c • 1) *ᵥ
              ((clusterProjector B hB T * clusterProjector A hA S) *ᵥ y))
              = pack (clusterProjector B hB T *ᵥ ((A - c • 1) *ᵥ
                  (clusterProjector A hA S *ᵥ y)))
                + pack (clusterProjector B hB T *ᵥ ((B - A) *ᵥ
                  (clusterProjector A hA S *ᵥ y))) := by
            rw [hsplit, pack_add]
          rw [hvec]
          exact norm_add_le _ _
        calc ‖pack ((B - c • 1) *ᵥ ((clusterProjector B hB T
                  * clusterProjector A hA S) *ᵥ y))‖
            ≤ ‖pack (clusterProjector B hB T *ᵥ ((A - c • 1) *ᵥ
                  (clusterProjector A hA S *ᵥ y)))‖
              + ‖pack (clusterProjector B hB T *ᵥ ((B - A) *ᵥ
                  (clusterProjector A hA S *ᵥ y)))‖ := hadd
          _ ≤ (r * ‖clusterProjector B hB T
                * clusterProjector A hA S‖ + ‖A - B‖) * ‖pack y‖ := by
                have hsum2 := add_le_add hT1 hT2
                calc ‖pack (clusterProjector B hB T *ᵥ ((A - c • 1) *ᵥ
                        (clusterProjector A hA S *ᵥ y)))‖
                      + ‖pack (clusterProjector B hB T *ᵥ ((B - A) *ᵥ
                        (clusterProjector A hA S *ᵥ y)))‖
                    ≤ (‖clusterProjector B hB T
                        * clusterProjector A hA S‖
                        * (r * ‖pack y‖)) + (‖A - B‖ * ‖pack y‖) := hsum2
                  _ = (r * ‖clusterProjector B hB T
                        * clusterProjector A hA S‖ + ‖A - B‖) * ‖pack y‖ := by ring
      exact le_trans hF2 hsplitnorm
    have h3 : ‖pack ((clusterProjector B hB T
        * clusterProjector A hA S) *ᵥ y)‖
        ≤ ((r * ‖clusterProjector B hB T * clusterProjector A hA S‖
            + ‖A - B‖) / (r + δ)) * ‖pack y‖ := by
      have hgoal : ‖pack ((clusterProjector B hB T
          * clusterProjector A hA S) *ᵥ y)‖ * (r + δ)
          ≤ (r * ‖clusterProjector B hB T * clusterProjector A hA S‖
              + ‖A - B‖) * ‖pack y‖ := by
        rw [mul_comm]
        exact hmid
      have h2 := (le_div_iff₀ hpos).2 hgoal
      rw [div_mul_eq_mul_div]
      exact h2
    exact h3
  have hpair : ∀ x y : V → ℝ,
      |y ⬝ᵥ ((clusterProjector B hB T
        * clusterProjector A hA S) *ᵥ x)|
        ≤ ((r * ‖clusterProjector B hB T
            * clusterProjector A hA S‖ + ‖A - B‖) / (r + δ))
          * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
    intro x y
    have hcs : |y ⬝ᵥ ((clusterProjector B hB T
        * clusterProjector A hA S) *ᵥ x)|
        ≤ ‖pack y‖ * ‖pack ((clusterProjector B hB T
          * clusterProjector A hA S) *ᵥ x)‖ := by
      have h := abs_dotProduct_le y ((clusterProjector B hB T
        * clusterProjector A hA S) *ᵥ x)
      rwa [← norm_euclidean_eq_sqrt, ← norm_euclidean_eq_sqrt] at h
    have hact := hmaster x
    have hrew : ‖pack y‖ * (((r * ‖clusterProjector B hB T
        * clusterProjector A hA S‖ + ‖A - B‖) / (r + δ))
      * ‖pack x‖) = ((r * ‖clusterProjector B hB T
        * clusterProjector A hA S‖ + ‖A - B‖) / (r + δ))
      * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
      rw [norm_euclidean_eq_sqrt, norm_euclidean_eq_sqrt]
      ring
    calc |y ⬝ᵥ ((clusterProjector B hB T
            * clusterProjector A hA S) *ᵥ x)|
        ≤ ‖pack y‖ * ‖pack ((clusterProjector B hB T
          * clusterProjector A hA S) *ᵥ x)‖ := hcs
      _ ≤ ‖pack y‖ * (((r * ‖clusterProjector B hB T
              * clusterProjector A hA S‖ + ‖A - B‖) / (r + δ))
          * ‖pack x‖) := mul_le_mul_of_nonneg_left hact (norm_nonneg _)
      _ = ((r * ‖clusterProjector B hB T * clusterProjector A hA S‖
            + ‖A - B‖) / (r + δ)) * Real.sqrt (x ⬝ᵥ x)
            * Real.sqrt (y ⬝ᵥ y) := hrew
  have hnorm := l2OpNorm_le_of_abs_dotProduct_le hCnn hpair
  have hstep : (r + δ) * ‖clusterProjector B hB T
      * clusterProjector A hA S‖
      ≤ r * ‖clusterProjector B hB T * clusterProjector A hA S‖
        + ‖A - B‖ := by
    have h := (le_div_iff₀ hpos).1 hnorm
    linarith
  have hfinal : δ * ‖clusterProjector B hB T
      * clusterProjector A hA S‖ ≤ ‖A - B‖ := by linarith
  exact (le_div_iff₀ hδ).2 (by rw [mul_comm]; exact hfinal)

/-- **Band Davis–Kahan, set form, difference (equal rank).** If the
cluster projectors of `A` at `S` and `B` at `T` have equal rank, every
in-`S` eigenvalue of `A` lies within `r` of `c`, and every
*out-of-`T`* eigenvalue of `B` lies at distance at least `r + δ` from
`c`, then the projectors are close:

`‖P_A(S) - P_B(T)‖ ≤ ‖A - B‖ / δ`, constant 1.

**No dichotomy, no interior case:** the equal-rank identity reduces the
difference to the one-sided residual `‖(1 − Q_T) P_S‖`, the complement
law `one_sub_clusterProjector` rewrites `1 − Q_T` as the cluster
projector of `Tᶜ` — a definition-level fact unavailable to the window
family — and the product form above applies. The out-of-`T` separation
is the honest form of what the engine consumes; the YWS-literal
*pairwise* set shape (no center/radius) is a recorded open follow-on
(see the proposal: an out-of-`S` A-eigenvalue can sit inside `S`'s
range, killing the interior-case trivial regime).

QA: `Scaffold/QA/Perturbation/ClusterProjector_QA.lean` — the
non-interval difference witness at exact-fit `c, r, δ`, the ε = 0
attainment, and the `hfar` fence on the interior-gap configuration. -/
theorem l2OpNorm_clusterProjector_sub_clusterProjector_le
    (hA : A.IsSymm) (hB : B.IsSymm) (S T : Set ℝ) (c r δ : ℝ)
    (hδ : 0 < δ) (hr : 0 ≤ r)
    (hrank : (clusterProjector A hA S).rank
      = (clusterProjector B hB T).rank)
    (hnear : ∀ i, eigvalOf A hA i ∈ S → |eigvalOf A hA i - c| ≤ r)
    (hfar : ∀ j, eigvalOf B hB j ∉ T → r + δ ≤ |eigvalOf B hB j - c|) :
    ‖clusterProjector A hA S - clusterProjector B hB T‖
      ≤ ‖A - B‖ / δ := by
  classical
  rw [l2OpNorm_sub_eq_of_rank_eq
    (clusterProjector_symmetric A hA S)
    (clusterProjector_idempotent A hA S)
    (clusterProjector_symmetric B hB T)
    (clusterProjector_idempotent B hB T) hrank,
    one_sub_clusterProjector hB T]
  refine l2OpNorm_clusterProjector_mul_clusterProjector_le hA hB S
    (Tᶜ) c r δ hδ hr hnear ?_
  intro j hj
  exact hfar j ((Set.mem_compl_iff _ _).mp hj)

/-- **Band Davis–Kahan, set form, two-sided difference (no rank
hypothesis).** If `P_A(S)` and `P_B(T)` are the cluster projectors of
two symmetric matrices at arbitrary eigenvalue sets, and *both*
out-of-cluster flanks are δ-separated in the center/radius membership
form — every in-`S` eigenvalue of `A` within `rS` of `cS` with every
out-of-`T` eigenvalue of `B` at least `rS + δ` from `cS`, and every
in-`T` eigenvalue of `B` within `rT` of `cT` with every out-of-`S`
eigenvalue of `A` at least `rT + δ` from `cT` — then

`‖P_A(S) - P_B(T)‖ ≤ 2 * ‖A - B‖ / δ`,

with **no rank hypothesis anywhere**: the consumer states the two
spectral separations and nothing else — no multiplicity counting. This
is the Yu–Wang–Samworth Theorem 1 both-gaps shape at arbitrary
eigenvalue sets (the set twin of
`l2OpNorm_bandProjector_sub_bandProjector_le_two_of_symm`); on inputs
where the equal-rank difference form above applies, that form gives the
strictly better constant 1.

The route is a pure composition, and the set form is *easier* than its
window sibling: the ring identity
`P - Q = (1 - Q) * P - Q * (1 - P)` reduces to the two one-sided
residuals, the complement law `one_sub_clusterProjector` turns each
into a cluster projector (`Q_{Tᶜ} * P_S` and `Q_T * Q_{Sᶜ}`), the
delivered set-form product bound — which, unlike the window pairwise
engine, carries **no** smallness regime — bounds each at its own
argument order (the second moved under `l2OpNorm_transpose`; cluster
projectors are symmetric), and **the constant 2 is exactly the
resulting triangle inequality**, no hidden loss. When the clusters'
ranks genuinely differ, both separations can still hold — the theorem
is rank-free because nothing in this route ever touches rank.

Statement-shape note: two center/radius pairs, one per cluster. A
single common center would also drive the composition but excludes
configurations where an out-of-`S` A-eigenvalue lies *between* the
clusters (near neither's complement margin); the two-pair form is the
honest minimal hypothesis set.

QA: `Scaffold/QA/Perturbation/ClusterProjector_QA.lean` — the
unequal-rank non-interval witness (the delivered equal-rank family's
hypothesis exhibited failing), the ε = 0 attainment, and the two-sided
fence isolating each separation flank. -/
theorem l2OpNorm_clusterProjector_sub_clusterProjector_le_two_of_symm
    (hA : A.IsSymm) (hB : B.IsSymm) (S T : Set ℝ) (cS rS cT rT δ : ℝ)
    (hδ : 0 < δ) (hrS : 0 ≤ rS) (hrT : 0 ≤ rT)
    (hnearS : ∀ i, eigvalOf A hA i ∈ S → |eigvalOf A hA i - cS| ≤ rS)
    (hfarT : ∀ j, eigvalOf B hB j ∉ T → rS + δ ≤ |eigvalOf B hB j - cS|)
    (hnearT : ∀ j, eigvalOf B hB j ∈ T → |eigvalOf B hB j - cT| ≤ rT)
    (hfarS : ∀ i, eigvalOf A hA i ∉ S → rT + δ ≤ |eigvalOf A hA i - cT|) :
    ‖clusterProjector A hA S - clusterProjector B hB T‖
      ≤ 2 * ‖A - B‖ / δ := by
  -- The first one-sided residual, as a cluster product
  have h1 : ‖(1 - clusterProjector B hB T) * clusterProjector A hA S‖
      ≤ ‖A - B‖ / δ := by
    rw [one_sub_clusterProjector hB T]
    refine l2OpNorm_clusterProjector_mul_clusterProjector_le hA hB S
      (Tᶜ) cS rS δ hδ hrS hnearS ?_
    intro j hj
    exact hfarT j ((Set.mem_compl_iff _ _).mp hj)
  -- The second one-sided residual, moved under the transpose
  have h2 : ‖clusterProjector B hB T * (1 - clusterProjector A hA S)‖
      ≤ ‖A - B‖ / δ := by
    have hsymmA : (clusterProjector A hA (Sᶜ))ᵀ
        = clusterProjector A hA (Sᶜ) :=
      clusterProjector_symmetric A hA (Sᶜ)
    have hsymmB : (clusterProjector B hB T)ᵀ
        = clusterProjector B hB T :=
      clusterProjector_symmetric B hB T
    have htrans : clusterProjector B hB T * clusterProjector A hA (Sᶜ)
        = (clusterProjector A hA (Sᶜ) * clusterProjector B hB T)ᵀ := by
      rw [Matrix.transpose_mul, hsymmB, hsymmA]
    rw [one_sub_clusterProjector hA S, htrans, l2OpNorm_transpose]
    have h := l2OpNorm_clusterProjector_mul_clusterProjector_le hB hA T
      (Sᶜ) cT rT δ hδ hrT hnearT
      (fun i hi => hfarS i ((Set.mem_compl_iff _ _).mp hi))
    rwa [norm_sub_rev] at h
  -- The ring identity plus the triangle inequality: 2 is exactly it
  calc ‖clusterProjector A hA S - clusterProjector B hB T‖
      = ‖(1 - clusterProjector B hB T) * clusterProjector A hA S
          - clusterProjector B hB T * (1 - clusterProjector A hA S)‖ :=
        by rw [sub_eq_one_sub_mul_sub_mul_one_sub]
    _ ≤ ‖(1 - clusterProjector B hB T) * clusterProjector A hA S‖
        + ‖clusterProjector B hB T * (1 - clusterProjector A hA S)‖ :=
          norm_sub_le _ _
    _ ≤ ‖A - B‖ / δ + ‖A - B‖ / δ := add_le_add h1 h2
    _ = 2 * ‖A - B‖ / δ := by ring

end SetForm


end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation
