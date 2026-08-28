/-
  EdgePerturbationDrift.lean

  Purpose
  -------
  The concentration → subspace-stability pipeline: the composed
  high-probability Fiedler drift under the centered Bernoulli edge
  design — the first join of the two most recent center deliveries
  (`fiedlerLine_stability`/`fiedlerSubspace_stability` and
  `edgePerturbation_norm_tail`), in the `eventStreamProjectorDrift`
  inclusion idiom at the new design.

  - `edgePerturbation_fiedlerSubspace_drift`: on the product-Bernoulli
    space at `p ∈ [0, 1]`, if the base graph's spectral gap `λ₃ − λ₂`
    exceeds `t + δ`, the bottom-2 Laplacian subspace rotates by more
    than `t/δ` with probability at most `2 d exp(−t²/(2‖∑ₑ L_e²‖))`.
  - `edgePerturbation_fiedlerLine_drift`: the same tail for the Fiedler
    *line* itself (the payoff — the kernel component is common to both
    graphs on the connectivity stack, so the residual rotation is the
    Fiedler mode's own), under the additional per-outcome nonnegativity
    and connectivity design constraints the kernel identification needs.

  Both are CONDITIONAL ON THE `matrix_hoeffding` AXIOM via the tail
  alone (`edgePerturbation_norm_tail`, Tropp 2012, Theorem 1.4, as
  repaired 2026-08-28) and must never be described as foundationally
  proved. The deterministic side is proved: the Davis–Kahan wrapper, the
  common-kernel identification, the packaging identity
  `laplacian_perturbWeight`, and the separation discharge from the base
  gap via the proved `weyl_inequality` on the tail event's complement.

  The separation hypothesis is stated against the *base* graph's gap
  (deterministic — no per-outcome spectral hypothesis): by Weyl at
  index 2, a perturbation of norm below `t` can depress `λ₃` by at most
  `t`, so on the complement of the tail event the Davis–Kahan
  separation `δ ≤ λ₃(A + E_ω) − λ₂(A)` holds whenever
  `t + δ ≤ λ₃(A) − λ₂(A)`.

  QA: `Scaffold/QA/Derived/EdgePerturbation_QA.lean`, the drift section —
  the closed-form Fiedler-line instance on the three-path
  (`6 exp(−1/24)`).
-/

import Scaffold.Derived.EdgePerturbationTail
import Scaffold.Mathlib.GraphTheory.Fiedler
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl

open MeasureTheory ProbabilityTheory
open SpectralGraphTheory
open Scaffold.Derived.EdgePerturbationTail
open Scaffold.Mathlib.Probability.BernoulliProduct
open Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation
open scoped BigOperators Matrix Matrix.L2OpNorm

namespace Scaffold.Derived.EdgePerturbationDrift

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Private helper: on the complement of the tail event, the base
graph's spectral gap discharges the Davis–Kahan separation via Weyl at
index 2 — the random perturbation can only depress the third eigenvalue
by its norm, which is below `t` there. -/
private theorem separation_of_norm_lt (A : WAdj (V := V)) (hA : A.IsSymm)
    (p : (V × V) → ℝ) (ω : (V × V) → Bool)
    (hcard : 3 ≤ Fintype.card V)
    {δ t : ℝ} (hgap : t + δ ≤ evals (laplacian_symmetric A hA) ⟨2, by omega⟩
      - evals (laplacian_symmetric A hA) ⟨1, by omega⟩)
    (hlt : ‖∑ e : V × V, perturbSummand A p e ω‖ < t) :
    δ ≤ evals (laplacian_symmetric (A + perturbWeight A p ω)
        (hA.add (perturbWeight_isSymm A p ω))) ⟨2, by omega⟩
      - evals (laplacian_symmetric A hA) ⟨1, by omega⟩ := by
  have hE : (perturbWeight A p ω).IsSymm := perturbWeight_isSymm A p ω
  have hL : (laplacian A).IsSymm := laplacian_symmetric A hA
  have hLE : (laplacian (perturbWeight A p ω)).IsSymm := laplacian_symmetric _ hE
  have hsum : (laplacian A + laplacian (perturbWeight A p ω)).IsSymm := hL.add hLE
  have hwy := abs_le.mp (weyl_inequality (laplacian A)
    (laplacian (perturbWeight A p ω)) hL hLE ⟨2, by omega⟩)
  rw [show ‖laplacian (perturbWeight A p ω)‖
      = ‖∑ e : V × V, perturbSummand A p e ω‖ from by
        rw [laplacian_perturbWeight]] at hwy
  rw [evals_congr (laplacian_symmetric (A + perturbWeight A p ω)
    (hA.add hE)) hsum (laplacian_add A (perturbWeight A p ω)) ⟨2, by omega⟩]
  linarith

/-- **Fiedler-subspace drift under random edge resampling** — the
concentration → subspace-stability pipeline at the bottom-2 subspace
level: on the product-Bernoulli space at inclusion probabilities
`p ∈ [0, 1]`, if the base graph's spectral gap `λ₃ − λ₂` exceeds
`t + δ`, then the probability that the bottom-2 Laplacian subspace
(the Fiedler cluster on a connected base) rotates by more than `t/δ`
is at most `2 d exp(−t²/(2‖∑ₑ L_e²‖))`.

The event inclusion is `eventStreamProjectorDrift`'s idiom: on the
complement of the tail event, the packaging identity transports the
norm bound to `‖laplacian E_ω‖`, Weyl discharges the separation from
the base gap, and the *proved* `fiedlerSubspace_stability` bounds the
rotation — so the drift event lies inside the tail event.

CONDITIONAL ON THE `matrix_hoeffding` AXIOM via the tail alone; the
Davis–Kahan side and the Weyl discharge are proved. -/
theorem edgePerturbation_fiedlerSubspace_drift (A : WAdj (V := V))
    (hA : A.IsSymm) (p : (V × V) → ℝ) (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (hcard : 3 ≤ Fintype.card V)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : 0 ≤ t)
    (hgap : t + δ ≤ evals (laplacian_symmetric A hA) ⟨2, by omega⟩
      - evals (laplacian_symmetric A hA) ⟨1, by omega⟩) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        ‖initialProjector (laplacian (A + perturbWeight A p ω))
            (laplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) ⟨1, by omega⟩
          - initialProjector (laplacian A) (laplacian_symmetric A hA)
            ⟨1, by omega⟩‖ ≥ t / δ}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) := by
  haveI : Nonempty V := ⟨(Fintype.equivFin V).symm ⟨0, by omega⟩⟩
  refine le_trans (measure_mono ?_)
    (edgePerturbation_norm_tail A p hp0 hp1 t ht)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hlt
  have hnorm : ‖∑ e : V × V, perturbSummand A p e ω‖ < t := lt_of_not_ge hlt
  have hsep := separation_of_norm_lt A hA p ω hcard hgap hnorm
  have hdk := fiedlerSubspace_stability A (perturbWeight A p ω) hA
    (perturbWeight_isSymm A p ω) hcard δ hδ hsep
  rw [show ‖laplacian (perturbWeight A p ω)‖
      = ‖∑ e : V × V, perturbSummand A p e ω‖ from by
        rw [laplacian_perturbWeight]] at hdk
  have hkey : ‖initialProjector (laplacian (A + perturbWeight A p ω))
      (laplacian_symmetric (A + perturbWeight A p ω)
        (hA.add (perturbWeight_isSymm A p ω))) ⟨1, by omega⟩
    - initialProjector (laplacian A) (laplacian_symmetric A hA) ⟨1, by omega⟩‖
      < t / δ := by
    exact lt_of_le_of_lt hdk (by
      rw [div_lt_div_iff₀ hδ hδ]
      exact mul_lt_mul_of_pos_right hnorm hδ)
  exact absurd hω (not_le_of_lt hkey)

/-- **Fiedler-line drift under random edge resampling** — the pipeline's
payoff: the same tail controls the rotation of the Fiedler *line* itself
(the rank-2 cluster's kernel component is the same matrix on both
graphs under the connectivity stack, so the residual rotation is
exactly the Fiedler mode's own). Hypotheses are the subspace variant's
plus the per-outcome design constraints (`hnnAE`, `hconnAE`) that make
the common-kernel identification true — e.g. both hold universally when
`p_{ij} + p_{ji} ≤ 1` on every positive-weight pair, so every edge
survives in every outcome.

CONDITIONAL ON THE `matrix_hoeffding` AXIOM via the tail alone; the
Davis–Kahan side, the kernel identification, and the packaging identity
are proved. -/
theorem edgePerturbation_fiedlerLine_drift (A : WAdj (V := V))
    (hA : A.IsSymm) (p : (V × V) → ℝ) (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1)
    (hnnA : ∀ i j, 0 ≤ A i j)
    (hnnAE : ∀ ω i j, 0 ≤ (A + perturbWeight A p ω) i j)
    (hconnA : (supportGraph A hA).Connected)
    (hconnAE : ∀ ω, (supportGraph (A + perturbWeight A p ω)
      (hA.add (perturbWeight_isSymm A p ω))).Connected)
    (hcard : 3 ≤ Fintype.card V)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : 0 ≤ t)
    (hgap : t + δ ≤ evals (laplacian_symmetric A hA) ⟨2, by omega⟩
      - evals (laplacian_symmetric A hA) ⟨1, by omega⟩) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        ‖(initialProjector (laplacian (A + perturbWeight A p ω))
            (laplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) ⟨1, by omega⟩
          - initialProjector (laplacian (A + perturbWeight A p ω))
            (laplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) ⟨0, by omega⟩)
        - (initialProjector (laplacian A) (laplacian_symmetric A hA)
            ⟨1, by omega⟩
          - initialProjector (laplacian A) (laplacian_symmetric A hA)
            ⟨0, by omega⟩)‖ ≥ t / δ}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) := by
  haveI : Nonempty V := ⟨(Fintype.equivFin V).symm ⟨0, by omega⟩⟩
  refine le_trans (measure_mono ?_)
    (edgePerturbation_norm_tail A p hp0 hp1 t ht)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hlt
  have hnorm : ‖∑ e : V × V, perturbSummand A p e ω‖ < t := lt_of_not_ge hlt
  have hsep := separation_of_norm_lt A hA p ω hcard hgap hnorm
  have hdk := fiedlerLine_stability A (perturbWeight A p ω) hA
    (perturbWeight_isSymm A p ω) hnnA (hnnAE ω) hconnA (hconnAE ω)
    hcard δ hδ hsep
  rw [show ‖laplacian (perturbWeight A p ω)‖
      = ‖∑ e : V × V, perturbSummand A p e ω‖ from by
        rw [laplacian_perturbWeight]] at hdk
  have hkey : ‖(initialProjector (laplacian (A + perturbWeight A p ω))
      (laplacian_symmetric (A + perturbWeight A p ω)
        (hA.add (perturbWeight_isSymm A p ω))) ⟨1, by omega⟩
    - initialProjector (laplacian (A + perturbWeight A p ω))
      (laplacian_symmetric (A + perturbWeight A p ω)
        (hA.add (perturbWeight_isSymm A p ω))) ⟨0, by omega⟩)
    - (initialProjector (laplacian A) (laplacian_symmetric A hA) ⟨1, by omega⟩
    - initialProjector (laplacian A) (laplacian_symmetric A hA)
      ⟨0, by omega⟩)‖ < t / δ := by
    exact lt_of_le_of_lt hdk (by
      rw [div_lt_div_iff₀ hδ hδ]
      exact mul_lt_mul_of_pos_right hnorm hδ)
  exact absurd hω (not_le_of_lt hkey)

end Scaffold.Derived.EdgePerturbationDrift
