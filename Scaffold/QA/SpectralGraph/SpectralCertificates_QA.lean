/-
  SpectralCertificates_QA.lean

  Purpose
  -------
  QA for `Scaffold.Mathlib.GraphTheory.SpectralCertificates` — Step 3
  of `proposals/decidable-spectral-certificates.md`: the computable
  certificate layer (the ℚ specification checker, its soundness
  theorem, and the kernel-verifiable ℤ cross-multiplied twin).

  Style follows the falsification convention of the sibling QA files:

  - *Kernel-`decide` demonstrations.* The integer twin's accept,
    reject, non-orthogonal, zero-vector, and fractional-bound paths
    are all evaluated by plain kernel `decide` on the four-cycle
    fixture — the executable entry point of the whole chain, with no
    `native_decide` anywhere.
  - *End-to-end soundness instances.* The accepted certificates feed
    the soundness theorems: `lambda2 (C₄) ≤ 2` (attained) and
    `lambda2 (C₄) ≤ 5/2` (fractional), each consuming a `decide`d
    hypothesis — integer arithmetic → kernel check → proved bridge →
    real spectral bound.
  - *The bridge is load-bearing.* The ℚ specification checker is NOT
    kernel-decidable (the Step 0 reducibility wall); it is proved
    `= true` on the fixture only through the proved
    cross-multiplication bridge from the `decide`d integer twin — the
    exact consumption route the module exists to provide.
  - *Arithmetic meaning pinned.* The raw integer sums behind the
    checker (`dotOne = 0`, `denom = 2`, `rawNumer = 8`) and the real
    Rayleigh quotient of the test vector (`4/2 = 2`) are computed
    from the raw definitions, so the certified bound `2` is seen to
    be exactly the test vector's quotient.
  - *Negative witnesses.* The bound `1` is rejected (the certificate
    method cannot certify below the quotient with this vector); a
    non-orthogonal and the zero test vector are rejected; and the
    guard-free statement shape "no orthogonality needed,
    `lambda2 ≤ rayleigh v` for every `v`" is *refuted* at `onesVec`
    (`rayleigh = 0 < lambda2` on the connected `C₄`) — the
    orthogonality conjunct is load-bearing, exactly as the proposal's
    Sharp Edge 2 demands.

  Fixtures are declared under fresh names rather than imported from
  sibling QA modules: QA modules are built independently and must not
  import each other (they share the `SpectralGraphTheory.QA`
  namespace).

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks interfaces; it does not prove any
  axiom's truth.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.SpectralCertificates
import Scaffold.Mathlib.GraphTheory.Fiedler
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## The four-cycle fixture `0 — 1 — 2 — 3 — 0`
-/


/-- Adjacency of the cycle `C₄` on `Fin 4`, over ℤ: symmetric, unit
weights, all degrees `2`. This is the certificate data — integer, as
the kernel-verifiable twin requires. -/
def certCycleAdj4 : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0]

theorem certCycleAdj4_isSymm : certCycleAdj4.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [certCycleAdj4]

theorem certCycleAdj4_nonneg : ∀ i j, (0 : ℤ) ≤ certCycleAdj4 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [certCycleAdj4]

/-- The real four-cycle adjacency the soundness theorem bounds. -/
def certAdj4ℝ : Matrix (Fin 4) (Fin 4) ℝ :=
  certCycleAdj4.map (fun a => (a : ℝ))

theorem certAdj4ℝ_isSymm : certAdj4ℝ.IsSymm :=
  isSymm_map_intCastReal certCycleAdj4_isSymm

/-- The alternating test vector `![1, 0, −1, 0]` over ℤ: orthogonal to
`onesVec`, unit squares summed to `2`. -/
def certTestVec4 : Fin 4 → ℤ :=
  ![1, 0, -1, 0]

/-!
## The checker's arithmetic, pinned from the raw definitions
-/


/-- The orthogonality sum vanishes. -/
theorem cert4_dotOne_QA : ∑ i, certTestVec4 i = 0 := by
  decide

/-- The squared norm is `2`. -/
theorem cert4_denom_QA : ∑ i, (certTestVec4 i) ^ 2 = 2 := by
  decide

/-- The raw Dirichlet sum over the ordered pairs of the cycle is `8`
(each of the four edges contributes `1` in each direction). The
certificate's quotient is therefore `8 / (2 • 2) = 2`. -/
theorem cert4_rawNumer_QA :
    ∑ i, ∑ j, certCycleAdj4 i j * (certTestVec4 i - certTestVec4 j) ^ 2 = 8 := by
  decide

/-!
## Kernel-`decide` demonstrations on the integer twin
-/


/-- Accept path: the attained bound `2` is accepted by plain kernel
`decide`. -/
theorem cert4_accepted_QA :
    isSpectralUpperBoundCertificateInt certCycleAdj4 certTestVec4 2 = true := by
  decide

/-- Reject path: the bound `1` is rejected — the certificate method
cannot certify below the test vector's quotient. -/
theorem cert4_rejected_QA :
    isSpectralUpperBoundCertificateInt certCycleAdj4 certTestVec4 1 = false := by
  decide

/-- A non-orthogonal test vector is rejected (the orthogonality
conjunct fires). -/
theorem cert4_nonorthogonal_rejected_QA :
    isSpectralUpperBoundCertificateInt certCycleAdj4 ![1, 1, 0, 0] 2 = false := by
  decide

/-- The zero test vector is rejected (the positive-norm conjunct
fires). -/
theorem cert4_zero_rejected_QA :
    isSpectralUpperBoundCertificateInt certCycleAdj4 ![0, 0, 0, 0] 2 = false := by
  decide

/-- Fractional accept path: the bound `5/2` is accepted by kernel
`decide` in the cross-multiplied form `2 • 8 ≤ 2 • 5 • 2`. -/
theorem cert4_frac_accepted_QA :
    isSpectralUpperBoundCertificateIntFrac certCycleAdj4 certTestVec4 5 2 = true := by
  decide

/-- Fractional reject path: the bound `3/2` is rejected
(`2 • 8 ≤ 2 • 3 • 2` fails). -/
theorem cert4_frac_rejected_QA :
    isSpectralUpperBoundCertificateIntFrac certCycleAdj4 certTestVec4 3 2 = false := by
  decide

/-!
## The bridge is load-bearing: the ℚ specification is unreachable by
kernel computation, reachable through the proved bridge
-/


/-- The ℚ specification checker accepts the cast data at the
fractional bound `5/2` — proved **through the cross-multiplication
bridge** from the `decide`d integer twin, since plain kernel `decide`
cannot evaluate ℚ arithmetic (Step 0's recorded reducibility wall).
This is the module's headline consumption route. -/
theorem cert4_spec_via_bridge_QA :
    isSpectralUpperBoundCertificate (certCycleAdj4.map (Int.cast : ℤ → ℚ))
      (toRat certTestVec4) (((5 : ℤ) : ℚ) / ((2 : ℤ) : ℚ)) = true :=
  (isSpectralUpperBoundCertificateIntFrac_iff certCycleAdj4 certTestVec4 5 2
    (by decide)).mp cert4_frac_accepted_QA

/-!
## End-to-end soundness instances: `decide`d integer data → verified
real spectral bounds
-/


/-- The accepted integer certificate certifies `lambda2 (C₄) ≤ 2` in
the real spectral center — the full chain: integer arithmetic, kernel
check, proved bridge, proved soundness. -/
theorem cert4_lambda2_le_two_QA :
    lambda2 certAdj4ℝ certAdj4ℝ_isSymm (by decide : 2 ≤ Fintype.card (Fin 4))
      ≤ ((2 : ℤ) : ℝ) :=
  lambda2_le_of_certificateInt certCycleAdj4_isSymm certCycleAdj4_nonneg
    (by decide) certTestVec4 2 cert4_accepted_QA

/-- The accepted fractional certificate certifies
`lambda2 (C₄) ≤ 5/2`. -/
theorem cert4_lambda2_le_five_halves_QA :
    lambda2 certAdj4ℝ certAdj4ℝ_isSymm (by decide : 2 ≤ Fintype.card (Fin 4))
      ≤ 5 / 2 := by
  have h := lambda2_le_of_certificateIntFrac certCycleAdj4_isSymm
    certCycleAdj4_nonneg (by decide) certTestVec4 5 2 (by decide)
    cert4_frac_accepted_QA
  norm_num at h ⊢
  exact h

/-!
## The certified bound is exactly the test vector's Rayleigh quotient
-/


set_option linter.unnecessarySeqFocus false in
/-- The Laplacian action on the (real) alternating vector is twice the
vector — computed from the raw definitions. -/
theorem cert4_laplacian_mulVec_QA :
    (laplacian certAdj4ℝ).mulVec ![1, 0, -1, 0] = ![2, 0, -2, 0] := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, Matrix.mulVec, Matrix.dotProduct,
      certAdj4ℝ, certCycleAdj4, Matrix.map_apply, Matrix.of_apply,
      Fin.sum_univ_four] <;> norm_num

set_option linter.unnecessarySeqFocus false in
/-- The Dirichlet energy of the alternating vector is `4`. -/
theorem cert4_quadForm_QA :
    quadForm (laplacian certAdj4ℝ) ![1, 0, -1, 0] = 4 := by
  show Matrix.dotProduct (![1, 0, -1, 0] : Fin 4 → ℝ)
    ((laplacian certAdj4ℝ).mulVec ![1, 0, -1, 0]) = 4
  rw [cert4_laplacian_mulVec_QA]
  simp [Matrix.dotProduct, Fin.sum_univ_four] <;> norm_num

set_option linter.unnecessarySeqFocus false in
/-- The Rayleigh quotient of the alternating vector is exactly `2`:
the certified bound is the quotient itself, with no slack. -/
theorem cert4_rayleigh_eq_two_QA :
    rayleigh (laplacian certAdj4ℝ) ![1, 0, -1, 0] = 2 := by
  have hne : (![1, 0, -1, 0] : Fin 4 → ℝ) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hnorm : Matrix.dotProduct (![1, 0, -1, 0] : Fin 4 → ℝ)
      ![1, 0, -1, 0] = 2 := by
    simp [Matrix.dotProduct, Fin.sum_univ_four] <;> norm_num
  rw [rayleigh, if_neg hne, cert4_quadForm_QA, hnorm]
  norm_num

/-!
## The orthogonality guard is load-bearing
-/


/-- The support graph of the real four-cycle is connected — walks from
`0` to every vertex around the cycle. -/
theorem cert4_supportGraph_connected :
    (supportGraph certAdj4ℝ certAdj4ℝ_isSymm).Connected := by
  have hreach : ∀ v : Fin 4,
      (supportGraph certAdj4ℝ certAdj4ℝ_isSymm).Reachable 0 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
        ⟨by decide, by simp [certAdj4ℝ, certCycleAdj4, Matrix.map_apply]⟩
        SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 3) (w := 2)
        ⟨by decide, by simp [certAdj4ℝ, certCycleAdj4, Matrix.map_apply]⟩
        (SimpleGraph.Walk.cons (u := 3) (v := 2) (w := 2)
          ⟨by decide, by simp [certAdj4ℝ, certCycleAdj4, Matrix.map_apply]⟩
          SimpleGraph.Walk.nil)⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 3) (w := 3)
        ⟨by decide, by simp [certAdj4ℝ, certCycleAdj4, Matrix.map_apply]⟩
        SimpleGraph.Walk.nil⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, hreach⟩

/-- The algebraic connectivity of the four-cycle is positive. -/
theorem cert4_lambda2_pos_QA :
    0 < lambda2 certAdj4ℝ certAdj4ℝ_isSymm
      (by decide : 2 ≤ Fintype.card (Fin 4)) :=
  lambda2_pos_of_connected certAdj4ℝ certAdj4ℝ_isSymm
    (fun i j => Int.cast_nonneg.2 (certCycleAdj4_nonneg i j))
    (by decide) cert4_supportGraph_connected

/-- The Rayleigh quotient of `onesVec` is `0` — computed from the raw
definitions (the Laplacian rows of a `2`-regular network sum to
zero). -/
theorem cert4_rayleigh_onesVec_eq_zero_QA :
    rayleigh (laplacian certAdj4ℝ) onesVec = 0 := by
  have hne : (onesVec : Fin 4 → ℝ) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [onesVec] at this
  rw [rayleigh, if_neg hne, quadForm]
  simp [laplacian, degreeMatrix, deg, Matrix.mulVec, Matrix.dotProduct,
    certAdj4ℝ, certCycleAdj4, Matrix.map_apply, Matrix.of_apply,
    Fin.sum_univ_four, onesVec]

/-- **The guard-free statement shape is refuted.** Dropping the
orthogonality conjunct from the certificate (or from
`lambda2_le_rayleigh`) would assert `lambda2 ≤ rayleigh v` for *every*
vector `v`; at `v = onesVec` this reads `lambda2 (C₄) ≤ 0`, false
since the cycle is connected. The same refutation covers the
zero-vector guard (the junk branch of `rayleigh` is also `0`). -/
theorem cert4_orthogonality_guard_load_bearing_QA :
    ¬ (lambda2 certAdj4ℝ certAdj4ℝ_isSymm
        (by decide : 2 ≤ Fintype.card (Fin 4))
      ≤ rayleigh (laplacian certAdj4ℝ) onesVec) := by
  intro h
  rw [cert4_rayleigh_onesVec_eq_zero_QA] at h
  exact absurd h (not_le.2 cert4_lambda2_pos_QA)

end SpectralGraphTheory.QA
