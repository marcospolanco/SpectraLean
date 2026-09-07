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
import Scaffold.Mathlib.GraphTheory.Cheeger
import Scaffold.Mathlib.GraphTheory.Mixing

/-!
# The quantized Cheeger inequality

The repository's first numerical-robustness layer: how rounding the
spectral gap `λ₂` into `b`-bit integer buckets propagates through
Cheeger's inequality, as an explicit two-sided error envelope
(`proposals/quantized-cheeger-bound.md`, delivered 2026-09-07).

Everything here is hard crust — composition on the two already-proved,
zero-admitted Cheeger theorems (`cheeger_upper_bound`,
`cheeger_lower_bound`) plus Mathlib's rounding primitive
`abs_sub_round : |x - round x| ≤ 1/2`. No axioms are touched.

**Layout.** The graph-agnostic quantizer lives in the nested
`Quantization` namespace (a uniform `b`-bit bucket quantizer over a
known range `[0, R]`); the two range bridges transport the proved
a priori spectral interval of the normalized Laplacian to the
`regularNormalizedLaplacian` spelling the Cheeger theorems use; and
`quantized_cheeger_le` is the resulting sandwich — `φ(G)` bracketed
purely in terms of the quantized, `b`-bit-representable `λ̃₂`:

`(λ̃₂ - 2^-(b+1)·2) / 2 ≤ φ ≤ √(2 (λ̃₂ + 2^-(b+1)·2))`, i.e.
`(λ̃₂ - 1/2^b)/2 ≤ φ(G) ≤ √(2 (λ̃₂ + 1/2^b))`.

The two directions are not symmetric — the error enters linearly in
the lower bound and inside the square root in the upper — a genuine
feature of Cheeger's own asymmetric pair, stated explicitly rather
than smoothed into a single uniform `±ε` shape.

**Scope decision** (recorded in the proposal): this module quantizes
`λ₂` alone, matching what Cheeger's inequality actually constrains
here; a top-`k` quantization theory (spectral embeddings,
`k`-way constants) would be a different proposal with a different
consumer.

**Module note.** This cannot live in `Cheeger.lean`: the Step-2 range
cap `secondEval_normalizedLaplacian_le_two` lives in `Mixing.lean`,
and `Mixing → Stationary → RandomWalk → Cheeger` is an import cycle.
The proposal pre-authorized a standalone file for exactly this
Step-0-survey outcome.

QA: `Scaffold/QA/SpectralGraph/QuantizedCheeger_QA.lean` — the
tie-breaking value pins, the error bound's sharpness at ties, the
boundary-count fence (`2^b + 1` distinct representable values, not
`2^b`), and the K₂ sandwich instantiated at `b = 0` and `b = 3` with
the visible tightening `1/2 < 15/16 ≤ φ`.
-/

open scoped Matrix

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Step 1: the uniform `b`-bit quantizer
-/

namespace Quantization

/-- **The uniform `b`-bit quantizer over a known range**: rescale `x`
into `[0, 2^b]` units, round to the nearest integer (Mathlib's
`round`), rescale back. The reported integer `round (x * 2^b / R)` is
the "`b`-bit integer bucket index"; the returned value is the
midpoint-representative of whichever of the `2^b` equal-width buckets
of `[0, R]` the input falls into.

Noncomputable because `round : ℝ → ℤ` is. Tie behavior (input exactly
halfway between bucket representatives, in scaled units) is
`round`'s: half-up, toward `+∞` (`round x = ⌊x + 1/2⌋`, so
`round 2⁻¹ = 1` but `round (−2⁻¹) = 0`) — NOT symmetric about zero:
positive ties round up to the bucket above, negative ties round up
to the bucket nearer zero (pinned side by side in QA at
`±1/8`, `b = 3`). At the `x = R` endpoint the up-rounding lands on
the bucket index `2^b`, so a closed range admits `2^b + 1`
representable points, not `2^b` — the off-by-one every
closed-interval uniform quantizer has, fenced in QA rather than
silently rounded down. At the degenerate range `R = 0` the junk
division collapses the quantizer to the constant `0` (fenced: the
error bound's `0 < R` clause is load-bearing there).

QA: `QuantizedCheeger_QA.lean`'s tie pins (`qcTie_b0`, `qcTie_b3`,
and the negative-tie asymmetry `qcNegTie_b3` /
`qcTie_asymmetry_b3`), the exact-value pin `qcK2_quantize_eval`, the
boundary-count fence (`qcBoundaryCount`, `qcBoundaryCount_b2`), and
the degenerate-range fence (`qcZeroRange_fence_QA`). -/
noncomputable def quantize (b : ℕ) (R x : ℝ) : ℝ :=
  (R / 2 ^ b) * (round (x * 2 ^ b / R) : ℝ)

/-- **The bucket-representative fixed points**: every point of the form
`(R / 2^b) * k` with `k : ℤ` is exactly representable — quantizing it
returns it unchanged. On `k ∈ {0, …, 2^b}` these are the `2^b + 1`
distinct representable values on `[0, R]` (with `k = 0` the zero
endpoint and `k = 2^b` the `R` endpoint), the substance of the
boundary-count fence: a closed-interval uniform `b`-bit quantizer
attains one more value than it has buckets.

Unconditional in `R` — the corner audit (2026-09-07) found the
first-draft `0 < R` hypothesis truth-removable: at `R = 0` both
sides evaluate to the junk zero `0 · round 0`, so the identity holds
there too (this is *not* true of the sibling error bound
`abs_sub_quantize_le`, whose `0 < R` clause is load-bearing and
fenced).

QA: consumed as the engine of `qcBoundaryCount` (injectivity of the
`Fin (2^b + 1)` family) and `qcBoundaryCount_b2` (the `b = 2` card
pin), and by `qcK2_quantize_eval`. -/
theorem quantize_mul_step (b : ℕ) (R : ℝ) (k : ℤ) :
    quantize b R ((R / 2 ^ b) * k) = (R / 2 ^ b) * k := by
  rcases eq_or_ne R 0 with hR0 | hR0
  · subst hR0
    show (0 / 2 ^ b) * (round ((0 / 2 ^ b) * (k : ℝ) * 2 ^ b / 0) : ℝ)
      = (0 / 2 ^ b) * (k : ℝ)
    rw [div_zero]
    norm_num
  · have h1 : ((R / 2 ^ b) * (k : ℝ)) * 2 ^ b / R = (k : ℝ) := by
      field_simp
    show (R / 2 ^ b) * (round ((R / 2 ^ b) * (k : ℝ) * 2 ^ b / R) : ℝ)
      = (R / 2 ^ b) * (k : ℝ)
    rw [h1, round_intCast]

/-- **The quantization error bound**: quantizing over a known range
`[0, R]` errs by at most half a bucket width, `R / 2^(b+1)`
— pure rescaling of Mathlib's `abs_sub_round : |x - round x| ≤ 1/2`,
with no graph content. At the a priori Cheeger range `R = 2` this is
the envelope `ε_Q = 1 / 2^b` the sandwich below carries.

The bound is sharp: it is attained with equality exactly at bucket
boundaries (ties), where `round` jumps — fenced numerically in QA
(`qcTie_b3_error_eq`, and at the negative tie `qcNegTie_error_eq`).
The `0 < R` clause is load-bearing: at the degenerate range `R = 0`
the junk division `x · 2^b / 0 = 0` collapses the quantizer to the
constant `0` and the statement refutes at every `x ≠ 0` (the
hypothesis-form fence `qcZeroRange_fence_QA`, generic in `b`).

QA: `QuantizedCheeger_QA.lean`'s `qcTie_b0`, `qcTie_b3`,
`qcTie_b3_error_eq` (sharpness), and `qcTie_b3_bound_QA` (the bound
instantiated beside the raw computation); the engine of
`quantized_cheeger_le`. -/
theorem abs_sub_quantize_le (b : ℕ) (R : ℝ) (hR : 0 < R) (x : ℝ) :
    |x - quantize b R x| ≤ R / 2 ^ (b + 1) := by
  have key : x - quantize b R x =
      (R / 2 ^ b) * (x * 2 ^ b / R - (round (x * 2 ^ b / R) : ℝ)) := by
    rw [quantize]
    field_simp
    ring
  rw [key, abs_mul, abs_of_pos (by positivity)]
  calc (R / 2 ^ b) * |x * 2 ^ b / R - (round (x * 2 ^ b / R) : ℝ)|
      ≤ (R / 2 ^ b) * (1 / 2) :=
        mul_le_mul_of_nonneg_left (abs_sub_round (x * 2 ^ b / R)) (by positivity)
    _ = R / 2 ^ (b + 1) := by
        rw [pow_succ]
        field_simp

end Quantization

/-!
## Step 2: the a priori range bridge

The quantizer needs a fixed range to resolve; for the normalized
Laplacian's second eigenvalue the proved a priori interval is `[0, 2]`
(`secondEval_normalizedLaplacian_le_two` for the cap, PSD-ness for the
floor). These two bridges transport that interval to the
`regularNormalizedLaplacian` spelling the Cheeger theorems are stated
at, through `normalizedLaplacian_eq_regularNormalizedLaplacian` (the
two normalizations agree exactly on `d`-regular input) and
`secondEval_congr` (proof-irrelevance transport across equal operator
spellings).
-/

/-- **The spectral floor at the regular normalized Laplacian**:
`0 ≤ λ₂(L_sym)` on a `d`-regular graph — the PSD floor of the
operator's spectrum, read off `evals` at the sorted second entry
through `evals_mem_eigvalOf` and `quadForm_eigvecOf_self`. The lower
half of the a priori interval `[0, 2]` the quantizer's range choice
`R = 2` rests on (the cap is `secondEval_regularNormalizedLaplacian_
le_two` below).

QA: `QuantizedCheeger_QA.lean`'s K₂ sandwich pins consume it through
`quantized_cheeger_le`; the fixture's pinned spectrum `[0, 2]` is the
interval at its extreme points. -/
theorem secondEval_regularNormalizedLaplacian_nonneg (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j) (d : ℝ)
    (hd : ∀ i, deg A i = d) (hdpos : 0 < d) (hcard : 2 ≤ Fintype.card V) :
    0 ≤ secondEval (regularNormalizedLaplacian A d)
        (regularNormalizedLaplacian_symmetric A hA d) hcard := by
  have hLsym := regularNormalizedLaplacian_symmetric A hA d
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf hLsym ⟨1, by omega⟩
  have hse : secondEval (regularNormalizedLaplacian A d) hLsym hcard
      = eigvalOf (regularNormalizedLaplacian A d) hLsym i := by
    rw [show secondEval (regularNormalizedLaplacian A d) hLsym hcard
      = evals hLsym ⟨1, by omega⟩ from rfl, hi]
  rw [hse]
  have h := regularNormalizedLaplacian_psd A hA hnonneg d hd hdpos
    (eigvecOf (regularNormalizedLaplacian A d) hLsym i)
  rw [quadForm_eigvecOf_self hLsym i] at h
  exact h

/-- **The spectral cap at the regular normalized Laplacian**:
`λ₂(L_sym) ≤ 2` on a `d`-regular graph — the proved cap
`secondEval_normalizedLaplacian_le_two` (`Mixing.lean`) transported to
the Cheeger theorems' operator spelling. Together with
`secondEval_regularNormalizedLaplacian_nonneg` this packages the full
a priori interval `[0, 2]` — the closed range over which the uniform
`b`-bit quantizer of Step 1 has fixed resolution, and the input that
makes `quantize b 2` the right quantizer for `λ₂` in Step 3.

QA: consumed by `quantized_cheeger_le`'s K₂ instantiation in
`QuantizedCheeger_QA.lean` (the fixture sits exactly at the cap
`λ₂ = 2`). -/
theorem secondEval_regularNormalizedLaplacian_le_two (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j) (d : ℝ)
    (hd : ∀ i, deg A i = d) (hdpos : 0 < d) (hcard : 2 ≤ Fintype.card V) :
    secondEval (regularNormalizedLaplacian A d)
        (regularNormalizedLaplacian_symmetric A hA d) hcard ≤ 2 := by
  have hLsym := regularNormalizedLaplacian_symmetric A hA d
  have hdeg : ∀ i, 0 < deg A i := fun i => by rw [hd i]; exact hdpos
  rw [secondEval_congr hLsym (normalizedLaplacian_symmetric A hA)
    (normalizedLaplacian_eq_regularNormalizedLaplacian A d hd hdpos).symm hcard]
  exact secondEval_normalizedLaplacian_le_two A hA hnn hdeg hcard

/-!
## Step 3: the quantized Cheeger sandwich
-/

/-- **The quantized Cheeger inequality**: with `λ̃₂` the `b`-bit
quantized spectral gap (`quantize b 2 λ₂`, over the proved a priori
range `[0, 2]`) and error envelope `ε_Q = 1/2^b`, the true Cheeger
constant is bracketed purely in terms of the rounded,
`b`-bit-representable quantity:

`(λ̃₂ - ε_Q) / 2 ≤ φ(G) ≤ √(2 (λ̃₂ + ε_Q))`.

Route: pure algebra over the two already-proved Cheeger theorems and
the quantizer's error bound — `abs_sub_quantize_le` gives the two-sided
inclusion `λ₂ ∈ [λ̃₂ - ε_Q, λ̃₂ + ε_Q]`; the easy direction
`λ₂ ≤ 2φ` pushes the left endpoint through division; the hard
direction `φ²/2 ≤ λ₂` pushes the right endpoint through the square
root (monotone at `Real.le_sqrt`, the nonnegativity floors supplied by
`cheegerConstant_nonneg` and the Step-2 floor). The hypothesis set is
exactly `cheeger_upper_bound`/`cheeger_lower_bound`'s — nothing new is
assumed, and no axiom is touched.

QA: `QuantizedCheeger_QA.lean`'s `qcK2_sandwich_b0_QA` /
`qcK2_sandwich_b3_QA` (the sandwich numerically collapsed at the
fixture with exact pinned values, at `b = 0` and `b = 3`) and
`qcK2_tightening_QA` (the envelope visibly tightening as `b` grows:
`1/2 < 15/16 ≤ φ`). -/
theorem quantized_cheeger_le (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d)
    (hdpos : 0 < d) (hcard : 2 ≤ Fintype.card V) (b : ℕ) :
    (Quantization.quantize b 2 (secondEval (regularNormalizedLaplacian A d)
        (regularNormalizedLaplacian_symmetric A hA d) hcard) - 1 / 2 ^ b) / 2
      ≤ cheegerConstant A ∧
      cheegerConstant A ≤ Real.sqrt (2 *
        (Quantization.quantize b 2 (secondEval (regularNormalizedLaplacian A d)
          (regularNormalizedLaplacian_symmetric A hA d) hcard) + 1 / 2 ^ b)) := by
  have hLsym := regularNormalizedLaplacian_symmetric A hA d
  have hnn : 0 ≤ secondEval (regularNormalizedLaplacian A d) hLsym hcard :=
    secondEval_regularNormalizedLaplacian_nonneg A hA hnonneg d hd hdpos hcard
  have hq := Quantization.abs_sub_quantize_le b 2 (by norm_num)
    (secondEval (regularNormalizedLaplacian A d) hLsym hcard)
  have hε : (2:ℝ) / 2 ^ (b + 1) = 1 / 2 ^ b := by
    have h2 : (0:ℝ) < 2 ^ b := by positivity
    rw [pow_succ]
    field_simp
    ring
  rw [hε] at hq
  obtain ⟨hlo, hhi⟩ := abs_le.1 hq
  constructor
  · have hup := cheeger_upper_bound A hA hnonneg d hd hdpos hcard
    have hlower : Quantization.quantize b 2
        (secondEval (regularNormalizedLaplacian A d) hLsym hcard) - 1 / 2 ^ b
        ≤ secondEval (regularNormalizedLaplacian A d) hLsym hcard := by linarith
    linarith
  · have hφnn : 0 ≤ cheegerConstant A := cheegerConstant_nonneg A hnonneg
    have hlow := cheeger_lower_bound A hA hnonneg d hd hdpos hcard
    have hy : 0 ≤ 2 * (Quantization.quantize b 2
        (secondEval (regularNormalizedLaplacian A d) hLsym hcard) + 1 / 2 ^ b) := by
      have hle : secondEval (regularNormalizedLaplacian A d) hLsym hcard
          ≤ Quantization.quantize b 2
            (secondEval (regularNormalizedLaplacian A d) hLsym hcard)
            + 1 / 2 ^ b := by linarith
      linarith
    have hkey : (cheegerConstant A) ^ 2
        ≤ 2 * (Quantization.quantize b 2
          (secondEval (regularNormalizedLaplacian A d) hLsym hcard) + 1 / 2 ^ b) := by
      have e1 : (cheegerConstant A) ^ 2
          = 2 * ((cheegerConstant A) ^ 2 / 2) := by ring
      rw [e1]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      linarith
    exact (Real.le_sqrt hφnn hy).mpr hkey

end SpectralGraphTheory
