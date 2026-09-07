/-
  QuantizedCheeger_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.QuantizedCheeger`: the
  uniform `b`-bit quantizer, its error bound, and the quantized Cheeger
  sandwich (`proposals/quantized-cheeger-bound.md`, 2026-09-07).

  The pins make the quantizer's numerical behavior concrete rather
  than implicit: the tie values (bucket boundaries) are computed
  exactly — ties round half-up, toward `+∞` (positive ties up to the
  bucket above, negative ties up to the bucket nearer zero, the
  asymmetry pinned side by side), the error bound is shown sharp by
  attaining equality at ties, the boundary-count fence checks the
  closed-range off-by-one (the `b`-bit family on `[0, R]` attains
  `2^b + 1` distinct values, not `2^b` — generic injectivity plus a
  concrete `b = 2` card pin), and the sandwich is numerically
  collapsed at the K₂ fixture — whose spectrum `[0, 2]` and Cheeger
  constant `φ = 1` are pinned independently in `Cheeger_QA.lean` —
  at `b = 0` and `b = 3`, with the envelope visibly tightening as
  `b` grows (`1/2 < 15/16 ≤ φ`).

  The triangle section is the first interior-`λ₂` fixture (`λ₂ = 3/2`,
  pinned in `Mixing_QA.lean`): there the quantizer genuinely errs at
  small `b`, so the section adds the triangle's own
  `cheegerConstant = 1` cut enumeration (generic, card-based), the
  spectrum bridge to the sandwich's operator spelling, quantizer value
  pins at `b = 0/1/2`, the sandwich instantiations, the `b = 1`
  envelope-center phenomenon (the tie's up-rounding cancels the
  budget — the lower bound attains the un-quantized `λ₂/2`), the
  strictly tightening upper envelope `√6 > √5 > √(7/2)`, and the
  honest non-monotonicity of the lower envelope.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA checks the
  interface and its numerical consequences; it does not validate any
  external source.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.QuantizedCheeger
import Scaffold.QA.SpectralGraph.Cheeger_QA
import Scaffold.QA.SpectralGraph.Mixing_QA

open scoped Matrix

namespace SpectralGraphTheory.QA

/-!
## The tie pins: values, error, and sharpness
-/

/-- **The exact-representability pin**: `2` (the K₂ spectral gap, and
any `λ₂` at the a priori cap) is exactly representable at every bit
depth — `quantize b 2 2 = 2` — so the K₂ sandwich pins below isolate
the envelope's own arithmetic, with zero quantization error. Route:
`quantize_mul_step` at the bucket index `k = 2^b`, the top endpoint
of the closed range (itself an instance of the off-by-one: `2^b`, not
`2^b - 1`). -/
theorem qcK2_quantize_eval (b : ℕ) :
    Quantization.quantize b 2 2 = 2 := by
  have hcast : (((2 ^ b : ℕ) : ℤ) : ℝ) = ((2:ℝ) ^ b) := by
    push_cast
    simp [Nat.cast_pow]
  have hnat : ((2:ℝ) * 2 ^ b / 2) = (((2 ^ b : ℕ) : ℤ) : ℝ) := by
    rw [hcast]
    field_simp
  show (2 / 2 ^ b) * (round ((2:ℝ) * 2 ^ b / 2) : ℝ) = 2
  rw [hnat, round_intCast, hcast]
  field_simp

/-- **The coarsest quantizer at the tie** (`b = 0`, `R = 2`): the
input `1` sits exactly halfway between the representatives `0` and
`2`, and the quantizer rounds *up*, to `2` — `round 2⁻¹ = 1` made
concrete at the coarsest depth where the whole range is one bucket
pair. The hand computation `1 · 2⁰ / 2 = 2⁻¹` is kept visible in the
proof. -/
theorem qcTie_b0 : Quantization.quantize 0 2 1 = 2 := by
  have h1 : ((1:ℝ) * 2 ^ 0 / 2) = 2⁻¹ := by
    rw [pow_zero, one_mul, one_div]
  show (2 / 2 ^ 0) * (round ((1:ℝ) * 2 ^ 0 / 2) : ℝ) = 2
  rw [h1, round_two_inv]
  norm_num

/-- **A bucket boundary at `b = 3`** (`R = 2`, bucket width `1/4`):
the input `1/8` is the boundary between the `0`-bucket and the
`1/4`-bucket, and the quantizer rounds *up*, to `1/4` — the
tie-breaking direction pinned at a nontrivial depth (the raw
arithmetic `1/8 · 8 / 2 = 2⁻¹` is again kept visible). -/
theorem qcTie_b3 : Quantization.quantize 3 2 ((1:ℝ) / 8) = 1 / 4 := by
  have h1 : ((1:ℝ) / 8 * 2 ^ 3 / 2) = 2⁻¹ := by norm_num
  show (2 / 2 ^ 3) * (round ((1:ℝ) / 8 * 2 ^ 3 / 2) : ℝ) = 1 / 4
  rw [h1, round_two_inv]
  norm_num

/-- **Sharpness of the error bound**: at the `b = 3` tie above, the
quantization error is *exactly* the bound `R / 2^(b+1) = 2 / 2⁴ =
1/8` — `abs_sub_quantize_le` is attained, not slack, at bucket
boundaries. Computed raw (`qcTie_b3` plus arithmetic); the theorem's
own instance is the companion below. -/
theorem qcTie_b3_error_eq :
    |(1:ℝ) / 8 - Quantization.quantize 3 2 ((1:ℝ) / 8)|
      = 2 / 2 ^ (3 + 1) := by
  rw [qcTie_b3]
  norm_num

/-- **The error bound instantiated** at the same tie — the theorem
route beside the raw computation of `qcTie_b3_error_eq` (two routes,
one value). -/
theorem qcTie_b3_bound_QA :
    |(1:ℝ) / 8 - Quantization.quantize 3 2 ((1:ℝ) / 8)|
      ≤ 2 / 2 ^ (3 + 1) :=
  Quantization.abs_sub_quantize_le 3 2 (by norm_num) ((1:ℝ) / 8)

/-!
## The boundary-count fence
-/

/-- **The closed-range off-by-one, generic form**: the `2^b + 1`
bucket-representative points `(R / 2^b) · k`, `k ∈ {0, …, 2^b}`, are
*distinct* under `quantize` — the family `k ↦ quantize` on
`Fin (2^b + 1)` is injective, through `quantize_mul_step` (each point
fixed) and the positivity of the step `R / 2^b`. A uniform `b`-bit
quantizer on the *closed* range `[0, R]` therefore attains `2^b + 1`
distinct values, not `2^b` — the honest endpoint overflow (`x = R`
lands on bucket index `2^b`) checked rather than asserted. -/
theorem qcBoundaryCount (b : ℕ) {R : ℝ} (hR : 0 < R) :
    Function.Injective (fun k : Fin (2 ^ b + 1) =>
      Quantization.quantize b R ((R / 2 ^ b) * ((k : ℕ) : ℤ))) := by
  intro k₁ k₂ h
  dsimp only at h
  have e₁ : Quantization.quantize b R ((R / 2 ^ b) * ((k₁ : ℕ) : ℤ))
      = (R / 2 ^ b) * ((k₁ : ℕ) : ℤ) :=
    Quantization.quantize_mul_step b R _
  have e₂ : Quantization.quantize b R ((R / 2 ^ b) * ((k₂ : ℕ) : ℤ))
      = (R / 2 ^ b) * ((k₂ : ℕ) : ℤ) :=
    Quantization.quantize_mul_step b R _
  rw [e₁, e₂] at h
  have hstep : (R / 2 ^ b : ℝ) ≠ 0 :=
    div_ne_zero hR.ne' (by positivity)
  have hz : (((k₁ : ℕ) : ℤ) : ℝ) = (((k₂ : ℕ) : ℤ) : ℝ) :=
    mul_left_cancel₀ hstep h
  exact Fin.val_injective
    (Nat.cast_injective (Int.cast_injective hz))

/-- **The boundary-count fence at `b = 2`**: the concrete card —
`2^2 + 1 = 5` distinct quantized values on `[0, 4]`, where the
representatives are the integers `0, 1, 2, 3, 4` themselves. The
generic injectivity (`qcBoundaryCount`) is the engine; this pins the
count at a decidable depth. -/
theorem qcBoundaryCount_b2 :
    (Finset.univ.image (fun k : Fin 5 =>
      Quantization.quantize 2 4 ((4 / 2 ^ 2) * ((k : ℕ) : ℤ)))).card = 5 := by
  have hinj : Function.Injective (fun k : Fin 5 =>
      Quantization.quantize 2 4 ((4 / 2 ^ 2) * ((k : ℕ) : ℤ))) :=
    qcBoundaryCount 2 (by norm_num)
  rw [Finset.card_image_of_injOn hinj.injOn]
  simp

/-!
## The range bridge at the fixture: K₂ attains the cap
-/

/-- **The a priori cap bridge's first consumer**: the transported bound
`λ₂(L_sym) ≤ 2` instantiated at K₂ — where the pinned exact spectrum
(`edge_normLap_secondEval_eq_two_QA`) shows the fixture sits AT the
cap, the bound attained with equality. Load-bearing on the transport
itself: a wrong operator spelling, direction, or regularity discharge
in the bridge fails the first conjunct, and the equality join exposes
any bound that certified something other than the pinned operator.
This is also the design-level justification the sandwich's `R = 2`
choice rests on, now value-consumed rather than merely cited. -/
theorem qcK2_cap_via_bridge_QA :
    secondEval (regularNormalizedLaplacian cheegerEdgeAdj 1)
      (regularNormalizedLaplacian_symmetric cheegerEdgeAdj
        cheegerEdgeAdj_symmetric 1)
      cheegerEdgeAdj_card ≤ 2 ∧
    secondEval (regularNormalizedLaplacian cheegerEdgeAdj 1)
      (regularNormalizedLaplacian_symmetric cheegerEdgeAdj
        cheegerEdgeAdj_symmetric 1)
      cheegerEdgeAdj_card = 2 := by
  refine ⟨secondEval_regularNormalizedLaplacian_le_two cheegerEdgeAdj
    cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg 1
    cheegerEdgeAdj_regular (by norm_num) cheegerEdgeAdj_card,
    edge_normLap_secondEval_eq_two_QA⟩

/-!
## The sandwich at K₂: `b = 0`, `b = 3`, and the tightening

`Cheeger_QA.lean`'s `cheegerEdgeAdj` (K₂) carries the independently
pinned spectrum `[0, 2]` (`edge_normLap_secondEval_eq_two_QA`) and
Cheeger constant `edge_cheegerConstant : φ = 1`; `qcK2_quantize_eval`
makes `λ̃₂ = 2` exact at every depth. Each instantiation below is the
theorem applied at the fixture with the envelope numerically collapsed
— a positive witness that the sandwich is honest (non-vacuous) at
known values, and that both asymmetric directions hold.
-/

/-- **The sandwich at `b = 0`**: the one-bit quantizer's envelope
collapses to `1/2 ≤ φ ≤ √6` — at K₂, `1/2 ≤ 1 ≤ √6`, both sides
genuine (the lower bound strict, the upper slack by `√6 − 1`). -/
theorem qcK2_sandwich_b0_QA :
    (1 / 2 : ℝ) ≤ cheegerConstant cheegerEdgeAdj ∧
      cheegerConstant cheegerEdgeAdj ≤ Real.sqrt 6 := by
  have h := quantized_cheeger_le cheegerEdgeAdj cheegerEdgeAdj_symmetric
    cheegerEdgeAdj_nonneg 1 cheegerEdgeAdj_regular (by norm_num)
    cheegerEdgeAdj_card 0
  have hsec : secondEval (regularNormalizedLaplacian cheegerEdgeAdj 1)
      (regularNormalizedLaplacian_symmetric cheegerEdgeAdj
        cheegerEdgeAdj_symmetric 1)
      cheegerEdgeAdj_card = 2 := edge_normLap_secondEval_eq_two_QA
  rw [hsec, qcK2_quantize_eval] at h
  obtain ⟨h1, h2⟩ := h
  have hnum1 : ((2:ℝ) - 1 / 2 ^ 0) / 2 = 1 / 2 := by norm_num
  have hnum2 : Real.sqrt (2 * (2 + 1 / 2 ^ 0)) = Real.sqrt 6 := by
    congr 1
    norm_num
  rw [hnum1] at h1
  rw [hnum2] at h2
  exact ⟨h1, h2⟩

/-- **The sandwich at `b = 3`**: the three-bit envelope collapses to
`15/16 ≤ φ ≤ √(2 · (2 + 1/8))` — at K₂, `15/16 ≤ 1`, the lower bound
within `1/16` of the truth. -/
theorem qcK2_sandwich_b3_QA :
    (15 / 16 : ℝ) ≤ cheegerConstant cheegerEdgeAdj ∧
      cheegerConstant cheegerEdgeAdj ≤ Real.sqrt (2 * (2 + 1 / 8)) := by
  have h := quantized_cheeger_le cheegerEdgeAdj cheegerEdgeAdj_symmetric
    cheegerEdgeAdj_nonneg 1 cheegerEdgeAdj_regular (by norm_num)
    cheegerEdgeAdj_card 3
  have hsec : secondEval (regularNormalizedLaplacian cheegerEdgeAdj 1)
      (regularNormalizedLaplacian_symmetric cheegerEdgeAdj
        cheegerEdgeAdj_symmetric 1)
      cheegerEdgeAdj_card = 2 := edge_normLap_secondEval_eq_two_QA
  rw [hsec, qcK2_quantize_eval] at h
  obtain ⟨h1, h2⟩ := h
  have hnum1 : ((2:ℝ) - 1 / 2 ^ 3) / 2 = 15 / 16 := by norm_num
  have hnum2 : Real.sqrt (2 * (2 + 1 / 2 ^ 3)) = Real.sqrt (2 * (2 + 1 / 8)) := by
    congr 1
    norm_num
  rw [hnum1] at h1
  rw [hnum2] at h2
  exact ⟨h1, h2⟩

/-- **The tightening with `b`**: the lower envelope improves strictly
from `b = 0` to `b = 3` — `1/2 < 15/16` — and the improved bound is
still valid at the fixture (`15/16 ≤ φ`). Doubling the bit budget
tightens the bracket; this witnesses it concretely between the two
instantiated depths. -/
theorem qcK2_tightening_QA :
    (1 / 2 : ℝ) < 15 / 16 ∧ 15 / 16 ≤ cheegerConstant cheegerEdgeAdj := by
  constructor
  · norm_num
  · exact qcK2_sandwich_b3_QA.1

/-!
## The triangle: the first interior-`λ₂` fixture

K₂ sits exactly at the a priori cap (`λ₂ = 2`), where quantization is
exact at every bit depth — the envelope's slack never engages. The
triangle (Mixing_QA's `triAdj`, 2-regular) is the fixture the K₂ pins
cannot replace: its spectral gap `λ₂ = 3/2` is interior and lands
*inside* a bucket, so the quantizer genuinely errs at small `b` and
the `±ε_Q` envelope is load-bearing for the first time. This section
pins the triangle's Cheeger constant (`1` — every nonempty proper cut
is a `1|2` split of conductance `1`, by a generic card-based
enumeration), bridges the already-pinned spectrum
(`tri_secondEval_QA`) to the sandwich's operator spelling, and
instantiates the sandwich at `b = 0, 1, 2` — with the depth behavior
K₂ cannot show: the upper envelope strictly tightening
(`√6 > √5 > √(7/2)`), the `b = 1` envelope-center phenomenon (the
tie's up-rounding cancels the budget exactly), and the honest
non-monotonicity of the lower envelope.
-/

section Triangle

/-- The triangle adjacency is nonnegative — the sandwich's hypothesis
supplier at the fixture. -/
theorem qcTri_nonneg : ∀ i j : Fin 3, 0 ≤ triAdj i j := by
  intro i j
  rw [triAdj_apply]
  split <;> norm_num

theorem qcTri_vol_singleton (a : Fin 3) : vol triAdj {a} = 2 := by
  simp [vol, triAdj_deg_eq]

theorem qcTri_vol_compl_singleton (a : Fin 3) : vol triAdj {a}ᶜ = 4 := by
  have hsd : ∑ j : Fin 3 in ((Finset.univ : Finset (Fin 3)) \ {a}), deg triAdj j
      + ∑ j : Fin 3 in ({a} : Finset (Fin 3)), deg triAdj j
      = ∑ j : Fin 3 in (Finset.univ : Finset (Fin 3)), deg triAdj j :=
    Finset.sum_sdiff (fun x _ => Finset.mem_univ x)
  have hcomp : ({a}ᶜ : Finset (Fin 3))
      = (Finset.univ : Finset (Fin 3)) \ {a} := Finset.compl_eq_univ_sdiff _
  have hvoldef : vol triAdj ((Finset.univ : Finset (Fin 3)) \ {a})
      = ∑ j : Fin 3 in ((Finset.univ : Finset (Fin 3)) \ {a}), deg triAdj j := rfl
  have hsing : ∑ j : Fin 3 in ({a} : Finset (Fin 3)), deg triAdj j = 2 :=
    qcTri_vol_singleton a
  have huniv : ∑ j : Fin 3 in (Finset.univ : Finset (Fin 3)), deg triAdj j = 6 :=
    tri_vol_QA
  rw [hcomp, hvoldef]
  linarith

theorem qcTri_boundary_singleton (a : Fin 3) : boundary triAdj {a} = 2 := by
  have hrow : ∑ j : Fin 3, triAdj a j = 2 := by
    fin_cases a <;> simp [triAdj_apply, Fin.sum_univ_three] <;> norm_num
  have hdiag : ∑ j : Fin 3 in ({a} : Finset (Fin 3)), triAdj a j = 0 := by
    simp [triAdj_apply]
  have hsd : ∑ j : Fin 3 in ((Finset.univ : Finset (Fin 3)) \ {a}), triAdj a j
      + ∑ j : Fin 3 in ({a} : Finset (Fin 3)), triAdj a j
      = ∑ j : Fin 3 in (Finset.univ : Finset (Fin 3)), triAdj a j :=
    Finset.sum_sdiff (fun x _ => Finset.mem_univ x)
  have hcomp : ({a}ᶜ : Finset (Fin 3))
      = (Finset.univ : Finset (Fin 3)) \ {a} := Finset.compl_eq_univ_sdiff _
  show ∑ i : Fin 3 in ({a} : Finset (Fin 3)),
      ∑ j : Fin 3 in ({a}ᶜ : Finset (Fin 3)), triAdj i j = 2
  rw [hcomp]
  have h5 : ∑ i : Fin 3 in ({a} : Finset (Fin 3)),
      ∑ j : Fin 3 in ((Finset.univ : Finset (Fin 3)) \ {a}), triAdj i j
      = ∑ j : Fin 3 in ((Finset.univ : Finset (Fin 3)) \ {a}), triAdj a j := by
    simp
  have h6 : ∑ j : Fin 3 in (Finset.univ : Finset (Fin 3)), triAdj a j
      = ∑ j : Fin 3, triAdj a j := rfl
  rw [h5]
  rw [h6, hdiag] at hsd
  linarith

theorem qcTri_conductance_singleton (a : Fin 3) :
    conductance triAdj {a} = 1 := by
  rw [conductance, qcTri_boundary_singleton a, qcTri_vol_singleton a,
    qcTri_vol_compl_singleton a]
  norm_num

/-- **The triangle's Cheeger constant is `1`**: every nonempty proper
cut of the triangle is a `1|2` split, and every such cut has
conductance `1` — the cut set is exactly `{1}`. Route (generic, no
literal-subset matching): a valid cut's card is `1` or `2` (the
complement-count split `S.card + Sᶜ.card = 3`), card `1` cuts are
singletons (`Finset.card_eq_one`), and card `2` cuts are complements
of singletons — reduced to the singleton case by the shelf's
`conductance_compl` (complement-symmetry at symmetric input). The
conductance computation itself is definitional arithmetic on the
delivered degree/row facts (`vol {a} = 2`, `vol {a}ᶜ = 4`,
`boundary {a} = 2`), independent of the sandwich. -/
theorem qcTri_cheegerConstant : cheegerConstant triAdj = 1 := by
  have hset : {c : ℝ | ∃ S : Finset (Fin 3), S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance triAdj S = c} = {1} := by
    ext c
    constructor
    · rintro ⟨S, hne, hcn, rfl⟩
      have hcard : S.card + Sᶜ.card = 3 := by
        rw [Finset.card_add_card_compl]
        decide
      have hb : S.card ≤ 3 := by omega
      rcases hS : S.card with _ | _ | _ | _ | _
      · rw [Finset.card_eq_zero.mp hS] at hne
        exact absurd hne (by simp)
      · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hS
        rw [ha]
        simpa using qcTri_conductance_singleton a
      · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (show Sᶜ.card = 1 by omega)
        have hS2 : S = {a}ᶜ := by
          rw [← compl_compl S, ha]
        rw [hS2, conductance_compl triAdj triAdj_isSymm]
        simpa using qcTri_conductance_singleton a
      · rw [Finset.card_eq_zero.mp (show Sᶜ.card = 0 by omega)] at hcn
        exact absurd hcn (by simp)
      · exact absurd hS (by omega)
    · rintro ⟨rfl⟩
      exact ⟨{0}, by decide, by decide, qcTri_conductance_singleton 0⟩
  rw [cheegerConstant, hset]
  simp

/-- **The pinned spectrum at the sandwich's operator spelling**: the
triangle's `λ₂(L_sym) = 3/2` (Mixing_QA's `tri_secondEval_QA`, proved
from the eigenvalue classification `{0, 3/2}` + the trace) bridged to
`regularNormalizedLaplacian` through the `d`-regularity agreement —
the same `secondEval_congr` route as the delivered cap bridge. Load-
bearing on the bridge: a wrong direction or spelling fails here, and
the sandwich pins below collapse against the wrong operator. -/
theorem qcTri_secondEval_regular :
    secondEval (regularNormalizedLaplacian triAdj 2)
      (regularNormalizedLaplacian_symmetric triAdj triAdj_isSymm 2)
      (by norm_num) = 3 / 2 := by
  rw [secondEval_congr (regularNormalizedLaplacian_symmetric triAdj
      triAdj_isSymm 2) (normalizedLaplacian_symmetric triAdj triAdj_isSymm)
    (normalizedLaplacian_eq_regularNormalizedLaplacian triAdj 2
      triAdj_deg_eq (by norm_num)).symm (by norm_num)]
  exact tri_secondEval_QA

/-! ### Quantizer value pins at interior input -/

/-- `round (3/4) = 1` through `round_eq` (`⌊x + 1/2⌋`): the interior
residual `3/4` rounds up. -/
theorem qcTri_round_three_quarters : (round ((3:ℝ) / 4) : ℤ) = 1 := by
  rw [round_eq]
  norm_num

/-- `round (3/2) = 2`: at `b = 1` the scaled input lands exactly on the
tie `3/2`, and the tie rounds up — the mechanism behind the envelope
center below. -/
theorem qcTri_round_three_halves : (round ((3:ℝ) / 2) : ℤ) = 2 := by
  rw [round_eq]
  norm_num

/-- At `b = 0` the interior `λ₂ = 3/2` quantizes to `2` — an error of
`1/2`, the full budget `ε_Q = 1/2^0 = 1` engaged for the first time at
a real (non-tie) interior point. -/
theorem qcTri_quantize_b0 : Quantization.quantize 0 2 (3 / 2) = 2 := by
  have h1 : ((3:ℝ) / 2 * 2 ^ 0 / 2) = 3 / 4 := by norm_num
  show (2 / 2 ^ 0) * (round ((3:ℝ) / 2 * 2 ^ 0 / 2) : ℝ) = 2
  rw [h1, qcTri_round_three_quarters]
  norm_num

/-- At `b = 1` the scaled input is exactly the tie `3/2`, which rounds
up to `2` — `λ̃₂ ≠ λ₂` with the error exactly the budget `1/2`. -/
theorem qcTri_quantize_b1 : Quantization.quantize 1 2 (3 / 2) = 2 := by
  have h1 : ((3:ℝ) / 2 * 2 ^ 1 / 2) = 3 / 2 := by norm_num
  show (2 / 2 ^ 1) * (round ((3:ℝ) / 2 * 2 ^ 1 / 2) : ℝ) = 2
  rw [h1, qcTri_round_three_halves]
  norm_num

/-- At `b = 2` the interior value becomes exactly representable
(`3/2 = (2/4) · 3`): quantization is exact — the error budget is pure
slack. -/
theorem qcTri_quantize_b2 : Quantization.quantize 2 2 (3 / 2) = 3 / 2 := by
  have h1 : ((3:ℝ) / 2 * 2 ^ 2 / 2) = 3 := by norm_num
  show (2 / 2 ^ 2) * (round ((3:ℝ) / 2 * 2 ^ 2 / 2) : ℝ) = 3 / 2
  rw [h1]
  norm_num

/-- **The `b = 1` envelope-center phenomenon**: the tie rounds `3/2` UP
to `2`, and the up-rounding EXACTLY cancels the error budget — the
envelope's center `λ̃₂ − ε_Q` recovers the true eigenvalue `3/2`, so
the quantized lower bound at `b = 1` is the un-quantized easy-direction
bound `λ₂/2 = 3/4`. A coincidence of the tie, not a general fact —
at `b = 2` the value is exact and the budget is slack, making the
`b = 2` lower bound *weaker* (see `qcTri_lower_nonmonotone_QA`). -/
theorem qcTri_envelope_center_b1 :
    Quantization.quantize 1 2 (3 / 2) - 1 / 2 ^ 1 = 3 / 2 := by
  rw [qcTri_quantize_b1]
  norm_num

/-! ### The sandwich at b = 0, 1, 2 -/

/-- **The sandwich at `b = 0`**: collapsed to `1/2 ≤ φ ≤ √6` — at the
triangle (`φ = 1`, `λ₂ = 3/2` quantized up to `2`), both sides
genuine. -/
theorem qcTri_sandwich_b0_QA :
    (1 / 2 : ℝ) ≤ cheegerConstant triAdj ∧
      cheegerConstant triAdj ≤ Real.sqrt 6 := by
  have h := quantized_cheeger_le triAdj triAdj_isSymm qcTri_nonneg 2
    triAdj_deg_eq (by norm_num) (by norm_num) 0
  have hsec : secondEval (regularNormalizedLaplacian triAdj 2)
      (regularNormalizedLaplacian_symmetric triAdj triAdj_isSymm 2)
      (by norm_num) = 3 / 2 := qcTri_secondEval_regular
  rw [hsec, qcTri_quantize_b0] at h
  obtain ⟨h1, h2⟩ := h
  have hnum1 : ((2:ℝ) - 1 / 2 ^ 0) / 2 = 1 / 2 := by norm_num
  have hnum2 : Real.sqrt (2 * (2 + 1 / 2 ^ 0)) = Real.sqrt 6 := by
    congr 1
    norm_num
  rw [hnum1] at h1
  rw [hnum2] at h2
  exact ⟨h1, h2⟩

/-- **The sandwich at `b = 1`**: collapsed to `3/4 ≤ φ ≤ √5` — the
lower bound ATTAINS `λ₂/2 = 3/4`, the un-quantized easy-direction
value (the tie's up-rounding cancels the budget:
`qcTri_envelope_center_b1`). -/
theorem qcTri_sandwich_b1_QA :
    (3 / 4 : ℝ) ≤ cheegerConstant triAdj ∧
      cheegerConstant triAdj ≤ Real.sqrt 5 := by
  have h := quantized_cheeger_le triAdj triAdj_isSymm qcTri_nonneg 2
    triAdj_deg_eq (by norm_num) (by norm_num) 1
  have hsec : secondEval (regularNormalizedLaplacian triAdj 2)
      (regularNormalizedLaplacian_symmetric triAdj triAdj_isSymm 2)
      (by norm_num) = 3 / 2 := qcTri_secondEval_regular
  rw [hsec, qcTri_quantize_b1] at h
  obtain ⟨h1, h2⟩ := h
  have hnum1 : ((2:ℝ) - 1 / 2 ^ 1) / 2 = 3 / 4 := by norm_num
  have hnum2 : Real.sqrt (2 * (2 + 1 / 2 ^ 1)) = Real.sqrt 5 := by
    congr 1
    norm_num
  rw [hnum1] at h1
  rw [hnum2] at h2
  exact ⟨h1, h2⟩

/-- **The sandwich at `b = 2`**: collapsed to `5/8 ≤ φ ≤ √(7/2)` — the
value now exactly representable, the envelope at its honest slack. -/
theorem qcTri_sandwich_b2_QA :
    (5 / 8 : ℝ) ≤ cheegerConstant triAdj ∧
      cheegerConstant triAdj ≤ Real.sqrt (7 / 2) := by
  have h := quantized_cheeger_le triAdj triAdj_isSymm qcTri_nonneg 2
    triAdj_deg_eq (by norm_num) (by norm_num) 2
  have hsec : secondEval (regularNormalizedLaplacian triAdj 2)
      (regularNormalizedLaplacian_symmetric triAdj triAdj_isSymm 2)
      (by norm_num) = 3 / 2 := qcTri_secondEval_regular
  rw [hsec, qcTri_quantize_b2] at h
  obtain ⟨h1, h2⟩ := h
  have hnum1 : ((3:ℝ) / 2 - 1 / 2 ^ 2) / 2 = 5 / 8 := by norm_num
  have hnum2 : Real.sqrt (2 * (3 / 2 + 1 / 2 ^ 2)) = Real.sqrt (7 / 2) := by
    congr 1
    norm_num
  rw [hnum1] at h1
  rw [hnum2] at h2
  exact ⟨h1, h2⟩

/-! ### The envelope's depth behavior, pinned honestly -/

/-- **The upper envelope strictly tightens with `b`** at this fixture:
`√6 > √5 > √(7/2)` — the ceiling `√(2(λ̃₂ + ε_Q))` decreases
monotonically as the buckets refine (the K₂ pins' tightening witness,
now at a fixture where `λ̃₂` itself moves). -/
theorem qcTri_upper_tightens_QA :
    Real.sqrt 6 > Real.sqrt 5 ∧ Real.sqrt 5 > Real.sqrt (7 / 2) := by
  constructor
  · show Real.sqrt 5 < Real.sqrt 6
    exact Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 5)
      (by norm_num : (5:ℝ) < 6)
  · show Real.sqrt (7 / 2) < Real.sqrt 5
    exact Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 7 / 2)
      (by norm_num : (7 / 2 : ℝ) < 5)

/-- **The lower envelope is NOT monotone in `b` at interior input**: the
`b = 1` bound `3/4` is LARGER than the `b = 2` bound `5/8` (and both
exceed the `b = 0` bound `1/2`). The lower bound is a worst-case
envelope whose tightness oscillates with the quantization residual —
at `b = 1` the tie's up-rounding cancels the error budget exactly
(`qcTri_envelope_center_b1`), at `b = 2` the value is exact and the
budget is pure slack. A genuine, non-obvious feature of the quantized
pair's asymmetric error propagation, pinned rather than assumed. -/
theorem qcTri_lower_nonmonotone_QA :
    (1 / 2 : ℝ) < 3 / 4 ∧ (5 / 8 : ℝ) < 3 / 4 ∧ (1 / 2 : ℝ) < 5 / 8 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end Triangle

/-!
## The corner audit: the degenerate range and the negative tie

The numerical layer's own adversarial audit (2026-09-07, the
standing "delivered-but-unfenced surfaces" agenda applied to the
newest public module): the error bound's `0 < R` clause fenced at
the junk corner, and the tie direction corrected and pinned —
Mathlib's `round` is `⌊x + 1/2⌋`, half-up toward `+∞`, so the tie
behavior is NOT symmetric about zero: the positive boundary `+1/8`
rounds up to `1/4` (delivered pin `qcTie_b3`) while the negative
boundary `−1/8` rounds up to `0`, the bucket nearer zero.
-/

section CornerAudit

/-- **The junk collapse at the degenerate range**: at `R = 0` the
quantizer is the constant `0` — the scaled input `x · 2^b / R` is the
junk zero (`div_zero`), `round 0 = 0`, and the rescaling factor is
`0`. The mechanism behind the error bound's fence below. -/
theorem qcZeroRange_quantize (b : ℕ) (x : ℝ) :
    Quantization.quantize b 0 x = 0 := by
  show (0 / 2 ^ b) * (round (x * 2 ^ b / 0) : ℝ) = 0
  rw [div_zero]
  norm_num

/-- **The `0 < R` fence for the error bound** (hypothesis form,
generic in `b`): dropping `hR` and instantiating at the degenerate
range `R = 0`, the bound `|x − quantize b 0 x| ≤ 0 / 2^(b+1) = 0`
refutes at every `x ≠ 0` — the junk-division collapse makes the
quantizer report `0` for every input. The clause is load-bearing
exactly at this corner (compare `quantize_mul_step`, where the same
clause was truth-removable and removed from the public statement). -/
theorem qcZeroRange_fence_QA (b : ℕ) :
    ¬ (∀ x : ℝ, |x - Quantization.quantize b 0 x| ≤ 0 / 2 ^ (b + 1)) := by
  intro h
  have h1 := h 1
  rw [qcZeroRange_quantize b 1] at h1
  have h2 : (0:ℝ) / 2 ^ (b + 1) = 0 := by simp
  rw [h2] at h1
  have h3 : (1:ℝ) - 0 = 1 := by norm_num
  rw [h3] at h1
  exact absurd h1 (by norm_num)

/-- **The negative tie at `b = 3`**: the boundary `−1/8` rounds to
`0` — the bucket NEARER ZERO — while its positive mirror `+1/8`
rounds to `1/4` (`qcTie_b3`). Mathlib's `round` is half-up
(`round_eq : round x = ⌊x + 1/2⌋`: `round 2⁻¹ = 1`,
`round (−2⁻¹) = 0`), so the quantizer's tie behavior is asymmetric
about zero — a genuine numerical-layer fact this audit pinned after
the first delivery's docstrings mischaracterized it as "away from
zero" (corrected in the same delivery line, uncommitted). -/
theorem qcNegTie_b3 : Quantization.quantize 3 2 ((-1:ℝ) / 8) = 0 := by
  have h1 : ((-1:ℝ) / 8 * 2 ^ 3 / 2) = -(2⁻¹) := by norm_num
  show (2 / 2 ^ 3) * (round ((-1:ℝ) / 8 * 2 ^ 3 / 2) : ℝ) = 0
  rw [h1, round_neg_two_inv]
  norm_num

/-- **The tie asymmetry, side by side**: `+1/8 → 1/4` (up, away from
the origin) but `−1/8 → 0` (up, toward the origin) — the same
half-up rule producing opposite geometric behavior on the two sides
of zero. -/
theorem qcTie_asymmetry_b3 :
    Quantization.quantize 3 2 ((1:ℝ) / 8) = 1 / 4 ∧
      Quantization.quantize 3 2 ((-1:ℝ) / 8) = 0 :=
  ⟨qcTie_b3, qcNegTie_b3⟩

/-- **Sharpness at the negative tie**: the error at `−1/8` is
EXACTLY the bound `2 / 2^4 = 1/8` — attained on both sides of zero,
the bound sharp at both tie polarities. -/
theorem qcNegTie_error_eq :
    |(-1:ℝ) / 8 - Quantization.quantize 3 2 ((-1:ℝ) / 8)|
      = 2 / 2 ^ (3 + 1) := by
  rw [qcNegTie_b3]
  norm_num

/-- **The error bound instantiated at the negative tie** — the theorem
route beside `qcNegTie_error_eq`'s raw computation (two routes, one
value). -/
theorem qcNegTie_bound_QA :
    |(-1:ℝ) / 8 - Quantization.quantize 3 2 ((-1:ℝ) / 8)|
      ≤ 2 / 2 ^ (3 + 1) :=
  Quantization.abs_sub_quantize_le 3 2 (by norm_num) ((-1:ℝ) / 8)

end CornerAudit

end SpectralGraphTheory.QA
