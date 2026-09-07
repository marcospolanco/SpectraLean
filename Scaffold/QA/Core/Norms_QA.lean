/-
  Norms_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.Core.Norms`: the pointwise `L∞` size
  `l_infty_norm` (an `sInf` of uniform bounds) and its nonnegativity
  theorem — the concentration interface's shared norm utilities, the
  census's last never-consumed shelf theorem outside the matrix-Azuma
  structure fields (2026-09-07, `proposals/zero-inert-census.md`).

  The value pin computes `l_infty_norm` at a bounded two-outcome
  fixture BOTH ways (`sInf ≤` by membership, `≤ sInf` by the lower
  bound at the maximal atom), with `l_infty_norm_nonneg` consumed as
  the theorem route beside the raw arithmetic route; the junk corner
  pins the documented unbounded behavior (`sInf ∅ = 0`) at the
  identity variable on `ℕ` under the trivial σ-algebra — the
  definition never consults the measurable structure, so any
  `MeasurableSpace ℕ` serves.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA checks the
  interface and its numerical consequences; it does not validate any
  external source.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Core.Norms

open MeasureTheory Scaffold.Mathlib.Core

namespace Scaffold.Mathlib.Core.QA

/-!
## The bounded fixture: `2` on true, `0` on false
-/

/-- The bounded fixture variable on the coin space (stated at the raw
function type; `RV` is a definitional synonym and `l_infty_norm`
accepts it by unfolding). -/
def lnX (ω : (Fin 1) → Bool) : ℝ :=
  if ω 0 = true then (2 : ℝ) else (0 : ℝ)

/-- The value `2` is an admissible uniform bound. -/
theorem lnX_mem : (2 : ℝ) ∈ {M : ℝ | 0 ≤ M ∧ ∀ ω, |lnX ω| ≤ M} := by
  refine ⟨by norm_num, ?_⟩
  intro ω
  cases h : ω 0
  · rw [lnX, if_neg (by simp [h])]
    norm_num
  · rw [lnX, if_pos (by simp [h])]
    norm_num

/-- No smaller bound is admissible: the true atom forces `2 ≤ M`. -/
theorem lnX_ge {M : ℝ}
    (hM : M ∈ {M : ℝ | 0 ≤ M ∧ ∀ ω, |lnX ω| ≤ M}) : 2 ≤ M := by
  have h := hM.2 (![true] : (Fin 1) → Bool)
  rw [lnX, if_pos (by simp : (![true] : Fin 1 → Bool) 0 = true)] at h
  simpa using h

/-- **The value pin**: `l_infty_norm lnX = 2`, the supremum of `|lnX|`
— both `sInf` directions raw, the definition unfolded at an honest
bounded variable. -/
theorem lnX_norm_eq_two : l_infty_norm lnX = 2 := by
  refine le_antisymm ?_ ?_
  · exact csInf_le ⟨0, fun m hm => hm.1⟩ lnX_mem
  · exact le_csInf ⟨2, lnX_mem⟩ fun m hm => lnX_ge hm

/-- The target theorem consumed: nonnegativity through
`l_infty_norm_nonneg`. -/
theorem lnX_norm_nonneg_pin : 0 ≤ l_infty_norm lnX :=
  l_infty_norm_nonneg lnX

/-- Raw companion: the pinned value is nonnegative by arithmetic —
two routes, one fact. -/
theorem lnX_norm_nonneg_raw : 0 ≤ l_infty_norm lnX := by
  rw [lnX_norm_eq_two]
  norm_num

/-- The documented junk corner: an unbounded variable on an infinite
space has an empty bound set (for every `M` some `n` exceeds it), so
the `sInf` is the junk `0` of `sInf ∅` — the docstring's honest
"consumers must establish boundedness". -/
theorem lnJunk :
    @l_infty_norm ℕ (⊤ : MeasurableSpace ℕ) (fun n => (n : ℝ)) = 0 := by
  have hempty : {M : ℝ | 0 ≤ M ∧ ∀ n : ℕ, |(n : ℝ)| ≤ M} = ∅ := by
    refine Set.eq_empty_iff_forall_not_mem.2 ?_
    rintro M ⟨-, hM⟩
    obtain ⟨n, hn⟩ := exists_nat_gt M
    have habs : |(n : ℝ)| = (n : ℝ) :=
      abs_of_nonneg (by exact_mod_cast n.zero_le)
    have hle := hM n
    rw [habs] at hle
    exact absurd hn (not_lt.2 hle)
  rw [l_infty_norm, hempty, Real.sInf_empty]

end Scaffold.Mathlib.Core.QA
