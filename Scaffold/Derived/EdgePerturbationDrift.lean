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
  - `edgePerturbation_fiedlerSubspace_drift'` and
    `edgePerturbation_fiedlerLine_drift'`: the sharpened,
    matched-threshold pair — the `s/(γ−s)`-shaped statements mirroring
    `eventStreamProjectorDrift` exactly, at `0 < s < γ ≤ λ₃ − λ₂`: the
    gap parameter is consumed inline (no separate `t + δ` split) and
    the threshold is matched to the tail level. At a fixed threshold
    `u` this is the envelope-optimal instance of the `t/δ` family: the
    constraint `t + δ ≤ γ` at `t/δ = u` maximizes the exponent `t²` at
    `t = γu/(1+u)`, which is exactly the `s` of the sharpened
    statement (`s/(γ−s) = u`).
  - The rank-`k` spectral-encoding drift pipeline (2026-08-31,
    `proposals/spectral-encoding-drift-pipeline.md`):
    `edgePerturbation_spectralEncodingSubspace_drift{'}` and
    `edgePerturbation_spectralEncoding_drift{'}` — the same pipeline at
    arbitrary encoding rank, consuming the general-rank stability pair
    and discharging the separation inline from the base graph's
    rank-`k` gap by Weyl at index `k + 1` (the LapPE delivery's priced
    automatic-`δ` follow-on).

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
  (`6 exp(−1/24)`), and the sharpened-interface section (the envelope
  arithmetic and the matched-threshold instances).
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

/-!
## The sharpened (matched-threshold) drift interface

The two theorems above bound `μ{‖rotation‖ ≥ t/δ}` by a tail sitting at
level `t`: at a fixed threshold `u = t/δ` the exponent `t²` is *not*
envelope-optimal — the constraint `t + δ ≤ γ` (where `γ` is any lower
bound on the base gap) maximizes `t` at `t = γu/(1+u)`. The statements
below consume the gap parameter inline and sit exactly at that envelope
point: with `s := γu/(1+u)` one has `s/(γ−s) = u`, so the threshold and
the tail level are matched, mirroring `eventStreamProjectorDrift`'s
statement shape exactly. Both are the delivered pair instantiated at
`t := s`, `δ := γ − s` (`0 < γ` is derivable from `0 < s < γ`, so no
explicit positivity hypothesis on `γ` is carried).
-/

/-- **Fiedler-subspace drift, sharpened (matched-threshold) form** — the
`s/(γ−s)`-shaped statement mirroring `eventStreamProjectorDrift`
exactly: at any `0 < s < γ ≤ λ₃(L A) − λ₂(L A)`, the probability that
the bottom-2 Laplacian subspace rotates by more than `s/(γ−s)` is at
most `2 d exp(−s²/(2‖∑ₑ L_e²‖))` — the gap consumed inline, threshold
matched to tail, and the pointwise-strongest instance of the
`t/δ`-family at every threshold (at threshold `u = s/(γ−s)` the
exponent `s² = (γu/(1+u))²` is the maximum of `t²` over all valid
`(t, δ)` splits of the delivered statement).

CONDITIONAL ON THE `matrix_hoeffding` AXIOM via the delivered
`t/δ`-form alone; that theorem's deterministic side (Davis–Kahan, Weyl
separation discharge) is proved. -/
theorem edgePerturbation_fiedlerSubspace_drift' (A : WAdj (V := V))
    (hA : A.IsSymm) (p : (V × V) → ℝ) (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (hcard : 3 ≤ Fintype.card V)
    (γ : ℝ)
    (hgap : γ ≤ evals (laplacian_symmetric A hA) ⟨2, by omega⟩
      - evals (laplacian_symmetric A hA) ⟨1, by omega⟩)
    (s : ℝ) (hs : 0 < s) (hsg : s < γ) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        ‖initialProjector (laplacian (A + perturbWeight A p ω))
            (laplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) ⟨1, by omega⟩
          - initialProjector (laplacian A) (laplacian_symmetric A hA)
            ⟨1, by omega⟩‖ ≥ s / (γ - s)}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(s ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) :=
  edgePerturbation_fiedlerSubspace_drift A hA p hp0 hp1 hcard (γ - s)
    (sub_pos.mpr hsg) s hs.le (by linarith)

/-- **Fiedler-line drift, sharpened (matched-threshold) form** — the
payoff statement of the pipeline in the `s/(γ−s)` shape of
`eventStreamProjectorDrift`: at any `0 < s < γ ≤ λ₃(L A) − λ₂(L A)`,
the probability that the Fiedler *line* itself rotates by more than
`s/(γ−s)` is at most `2 d exp(−s²/(2‖∑ₑ L_e²‖))` — the gap consumed
inline and the threshold matched to the tail (the envelope-optimal
instance of the delivered `t/δ` form at every threshold). Hypotheses
are the sharpened subspace variant's plus the per-outcome design
constraints the common-kernel identification needs.

CONDITIONAL ON THE `matrix_hoeffding` AXIOM via the delivered
`t/δ`-form alone; the Davis–Kahan side, the kernel identification, and
the packaging identity are proved. -/
theorem edgePerturbation_fiedlerLine_drift' (A : WAdj (V := V))
    (hA : A.IsSymm) (p : (V × V) → ℝ) (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1)
    (hnnA : ∀ i j, 0 ≤ A i j)
    (hnnAE : ∀ ω i j, 0 ≤ (A + perturbWeight A p ω) i j)
    (hconnA : (supportGraph A hA).Connected)
    (hconnAE : ∀ ω, (supportGraph (A + perturbWeight A p ω)
      (hA.add (perturbWeight_isSymm A p ω))).Connected)
    (hcard : 3 ≤ Fintype.card V)
    (γ : ℝ)
    (hgap : γ ≤ evals (laplacian_symmetric A hA) ⟨2, by omega⟩
      - evals (laplacian_symmetric A hA) ⟨1, by omega⟩)
    (s : ℝ) (hs : 0 < s) (hsg : s < γ) :
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
            ⟨0, by omega⟩)‖ ≥ s / (γ - s)}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(s ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) :=
  edgePerturbation_fiedlerLine_drift A hA p hp0 hp1 hnnA hnnAE hconnA
    hconnAE hcard (γ - s) (sub_pos.mpr hsg) s hs.le (by linarith)

/-!
## The rank-`k` spectral-encoding drift pipeline (general rank)

`proposals/spectral-encoding-drift-pipeline.md` (delivered 2026-08-31):
the same pipeline at *arbitrary encoding rank* `k`, consuming the
general-rank stability pair of
`proposals/spectral-positional-encoding-stability.md`
(`spectralEncodingSubspace_stability`/`spectralEncoding_stability`,
which made the `k = 1` theorems above corollaries). This is that
delivery's priced deferred follow-on — automatic `δ` certification: the
separation hypothesis no longer appears as a caller obligation; it is
discharged inline from the base graph's deterministic rank-`k` gap by
the proved `weyl_inequality` at index `k + 1` on the tail event's
complement. The caller supplies only the base gap — never a
perturbed-spectrum `δ`.
-/

/-- Private helper, general rank: on the complement of the tail event,
the base graph's rank-`k` spectral gap discharges the Davis–Kahan
separation via Weyl at index `k + 1` — the random perturbation can only
depress the `k + 2`-nd eigenvalue by its norm, which is below `t`
there. -/
private theorem separation_of_norm_lt' (A : WAdj (V := V)) (hA : A.IsSymm)
    (p : (V × V) → ℝ) (ω : (V × V) → Bool)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    {δ t : ℝ} (hgap : t + δ ≤ evals (laplacian_symmetric A hA) ⟨(k : ℕ) + 1, hk⟩
      - evals (laplacian_symmetric A hA) k)
    (hlt : ‖∑ e : V × V, perturbSummand A p e ω‖ < t) :
    δ ≤ evals (laplacian_symmetric (A + perturbWeight A p ω)
        (hA.add (perturbWeight_isSymm A p ω))) ⟨(k : ℕ) + 1, hk⟩
      - evals (laplacian_symmetric A hA) k := by
  have hE : (perturbWeight A p ω).IsSymm := perturbWeight_isSymm A p ω
  have hL : (laplacian A).IsSymm := laplacian_symmetric A hA
  have hLE : (laplacian (perturbWeight A p ω)).IsSymm := laplacian_symmetric _ hE
  have hsum : (laplacian A + laplacian (perturbWeight A p ω)).IsSymm := hL.add hLE
  have hwy := abs_le.mp (weyl_inequality (laplacian A)
    (laplacian (perturbWeight A p ω)) hL hLE ⟨(k : ℕ) + 1, hk⟩)
  rw [show ‖laplacian (perturbWeight A p ω)‖
      = ‖∑ e : V × V, perturbSummand A p e ω‖ from by
        rw [laplacian_perturbWeight]] at hwy
  rw [evals_congr (laplacian_symmetric (A + perturbWeight A p ω)
    (hA.add hE)) hsum (laplacian_add A (perturbWeight A p ω)) ⟨(k : ℕ) + 1, hk⟩]
  linarith

/-- **Spectral-encoding subspace drift, general rank** — the
concentration → subspace-stability pipeline at arbitrary encoding rank:
on the product-Bernoulli space at inclusion probabilities `p ∈ [0, 1]`,
if the base graph's rank-`k` gap `evals ⟨k+1⟩ − evals k` exceeds
`t + δ`, then the probability that the bottom-`k+1` Laplacian subspace
(the `k`-dimensional positional-encoding subspace of the LapPE
program) rotates by more than `t/δ` is at most
`2 d exp(−t²/(2‖∑ₑ L_e²‖))`. The `k = 1` instance of this shape is
`edgePerturbation_fiedlerSubspace_drift` above; the rank parameter is
the ML-facing content (practical encodings use `k ≫ 1`).

CONDITIONAL ON THE `matrix_hoeffding` AXIOM via the tail alone; the
Davis–Kahan side and the Weyl separation discharge are proved. -/
theorem edgePerturbation_spectralEncodingSubspace_drift (A : WAdj (V := V))
    (hA : A.IsSymm) (p : (V × V) → ℝ) (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : 0 ≤ t)
    (hgap : t + δ ≤ evals (laplacian_symmetric A hA) ⟨(k : ℕ) + 1, hk⟩
      - evals (laplacian_symmetric A hA) k) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        ‖initialProjector (laplacian (A + perturbWeight A p ω))
            (laplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) k
          - initialProjector (laplacian A) (laplacian_symmetric A hA) k‖ ≥ t / δ}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) := by
  haveI : Nonempty V := ⟨(Fintype.equivFin V).symm ⟨1, by omega⟩⟩
  refine le_trans (measure_mono ?_)
    (edgePerturbation_norm_tail A p hp0 hp1 t ht)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hlt
  have hnorm : ‖∑ e : V × V, perturbSummand A p e ω‖ < t := lt_of_not_ge hlt
  have hsep := separation_of_norm_lt' A hA p ω k hk hgap hnorm
  have hdk := spectralEncodingSubspace_stability A (perturbWeight A p ω) hA
    (perturbWeight_isSymm A p ω) k hk δ hδ hsep
  rw [show ‖laplacian (perturbWeight A p ω)‖
      = ‖∑ e : V × V, perturbSummand A p e ω‖ from by
        rw [laplacian_perturbWeight]] at hdk
  have hkey : ‖initialProjector (laplacian (A + perturbWeight A p ω))
      (laplacian_symmetric (A + perturbWeight A p ω)
        (hA.add (perturbWeight_isSymm A p ω))) k
    - initialProjector (laplacian A) (laplacian_symmetric A hA) k‖
      < t / δ := by
    exact lt_of_le_of_lt hdk (by
      rw [div_lt_div_iff₀ hδ hδ]
      exact mul_lt_mul_of_pos_right hnorm hδ)
  exact absurd hω (not_le_of_lt hkey)

/-- **Spectral-encoding drift, general rank, kernel-isolated** — the
pipeline's ML-facing payoff: the same tail controls the rotation of the
*informative* rank-`k` component `P_k − P₀` of the positional encoding
itself (the constants subtracted off; on the connectivity stack the
kernel projector is the same matrix on both graphs, so the rotation is
entirely the encoding's own). Hypotheses are the subspace variant's
plus the per-outcome design constraints (`hnnAE`, `hconnAE`) that make
the common-kernel identification true — e.g. both hold when
`p_{ij} + p_{ji} ≤ 1` on every positive-weight pair. The `k = 1`
instance is `edgePerturbation_fiedlerLine_drift` above.

CONDITIONAL ON THE `matrix_hoeffding` AXIOM via the tail alone; the
Davis–Kahan side, the kernel identification, and the Weyl discharge
are proved. -/
theorem edgePerturbation_spectralEncoding_drift (A : WAdj (V := V))
    (hA : A.IsSymm) (p : (V × V) → ℝ) (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1)
    (hnnA : ∀ i j, 0 ≤ A i j)
    (hnnAE : ∀ ω i j, 0 ≤ (A + perturbWeight A p ω) i j)
    (hconnA : (supportGraph A hA).Connected)
    (hconnAE : ∀ ω, (supportGraph (A + perturbWeight A p ω)
      (hA.add (perturbWeight_isSymm A p ω))).Connected)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : 0 ≤ t)
    (hgap : t + δ ≤ evals (laplacian_symmetric A hA) ⟨(k : ℕ) + 1, hk⟩
      - evals (laplacian_symmetric A hA) k) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        ‖(initialProjector (laplacian (A + perturbWeight A p ω))
            (laplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) k
          - initialProjector (laplacian (A + perturbWeight A p ω))
            (laplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) ⟨0, by omega⟩)
        - (initialProjector (laplacian A) (laplacian_symmetric A hA) k
          - initialProjector (laplacian A) (laplacian_symmetric A hA)
            ⟨0, by omega⟩)‖ ≥ t / δ}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) := by
  haveI : Nonempty V := ⟨(Fintype.equivFin V).symm ⟨1, by omega⟩⟩
  refine le_trans (measure_mono ?_)
    (edgePerturbation_norm_tail A p hp0 hp1 t ht)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hlt
  have hnorm : ‖∑ e : V × V, perturbSummand A p e ω‖ < t := lt_of_not_ge hlt
  have hsep := separation_of_norm_lt' A hA p ω k hk hgap hnorm
  have hdk := spectralEncoding_stability A (perturbWeight A p ω) hA
    (perturbWeight_isSymm A p ω) hnnA (hnnAE ω) hconnA (hconnAE ω) k hk δ hδ hsep
  rw [show ‖laplacian (perturbWeight A p ω)‖
      = ‖∑ e : V × V, perturbSummand A p e ω‖ from by
        rw [laplacian_perturbWeight]] at hdk
  have hkey : ‖(initialProjector (laplacian (A + perturbWeight A p ω))
      (laplacian_symmetric (A + perturbWeight A p ω)
        (hA.add (perturbWeight_isSymm A p ω))) k
    - initialProjector (laplacian (A + perturbWeight A p ω))
      (laplacian_symmetric (A + perturbWeight A p ω)
        (hA.add (perturbWeight_isSymm A p ω))) ⟨0, by omega⟩)
    - (initialProjector (laplacian A) (laplacian_symmetric A hA) k
      - initialProjector (laplacian A) (laplacian_symmetric A hA)
        ⟨0, by omega⟩)‖
      < t / δ := by
    exact lt_of_le_of_lt hdk (by
      rw [div_lt_div_iff₀ hδ hδ]
      exact mul_lt_mul_of_pos_right hnorm hδ)
  exact absurd hω (not_le_of_lt hkey)

/-- **Spectral-encoding subspace drift, sharpened (matched-threshold)
form, general rank** — the `s/(γ−s)` shape at any encoding rank: at any
`0 < s < γ ≤ evals ⟨k+1⟩ (L A) − evals k (L A)`, the probability that
the bottom-`k+1` encoding subspace rotates by more than `s/(γ−s)` is at
most `2 d exp(−s²/(2‖∑ₑ L_e²‖))` — the gap consumed inline, threshold
matched to tail, the envelope-optimal instance of the `t/δ` family at
every threshold (the `k = 1` instance is
`edgePerturbation_fiedlerSubspace_drift'` above).

CONDITIONAL ON THE `matrix_hoeffding` AXIOM via the delivered `t/δ`
form alone. -/
theorem edgePerturbation_spectralEncodingSubspace_drift' (A : WAdj (V := V))
    (hA : A.IsSymm) (p : (V × V) → ℝ) (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (γ : ℝ)
    (hgap : γ ≤ evals (laplacian_symmetric A hA) ⟨(k : ℕ) + 1, hk⟩
      - evals (laplacian_symmetric A hA) k)
    (s : ℝ) (hs : 0 < s) (hsg : s < γ) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        ‖initialProjector (laplacian (A + perturbWeight A p ω))
            (laplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) k
          - initialProjector (laplacian A) (laplacian_symmetric A hA) k‖
            ≥ s / (γ - s)}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(s ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) :=
  edgePerturbation_spectralEncodingSubspace_drift A hA p hp0 hp1 k hk
    (γ - s) (sub_pos.mpr hsg) s hs.le (by linarith)

/-- **Spectral-encoding drift, kernel-isolated, sharpened
(matched-threshold) form, general rank** — the ML-facing payoff
statement at any encoding rank: at any `0 < s < γ ≤` the base graph's
rank-`k` gap, the informative encoding component `P_k − P₀` rotates by
more than `s/(γ−s)` with probability at most
`2 d exp(−s²/(2‖∑ₑ L_e²‖))`. Hypotheses are the sharpened subspace
variant's plus the per-outcome design constraints the kernel
identification needs (the `k = 1` instance is
`edgePerturbation_fiedlerLine_drift'` above).

CONDITIONAL ON THE `matrix_hoeffding` AXIOM via the delivered `t/δ`
form alone. -/
theorem edgePerturbation_spectralEncoding_drift' (A : WAdj (V := V))
    (hA : A.IsSymm) (p : (V × V) → ℝ) (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1)
    (hnnA : ∀ i j, 0 ≤ A i j)
    (hnnAE : ∀ ω i j, 0 ≤ (A + perturbWeight A p ω) i j)
    (hconnA : (supportGraph A hA).Connected)
    (hconnAE : ∀ ω, (supportGraph (A + perturbWeight A p ω)
      (hA.add (perturbWeight_isSymm A p ω))).Connected)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (γ : ℝ)
    (hgap : γ ≤ evals (laplacian_symmetric A hA) ⟨(k : ℕ) + 1, hk⟩
      - evals (laplacian_symmetric A hA) k)
    (s : ℝ) (hs : 0 < s) (hsg : s < γ) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        ‖(initialProjector (laplacian (A + perturbWeight A p ω))
            (laplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) k
          - initialProjector (laplacian (A + perturbWeight A p ω))
            (laplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) ⟨0, by omega⟩)
        - (initialProjector (laplacian A) (laplacian_symmetric A hA) k
          - initialProjector (laplacian A) (laplacian_symmetric A hA)
            ⟨0, by omega⟩)‖ ≥ s / (γ - s)}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(s ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) :=
  edgePerturbation_spectralEncoding_drift A hA p hp0 hp1 hnnA hnnAE hconnA
    hconnAE k hk (γ - s) (sub_pos.mpr hsg) s hs.le (by linarith)

end Scaffold.Derived.EdgePerturbationDrift
