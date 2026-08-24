# Davis & Kahan 1970 - Rotation of Eigenvectors by a Perturbation

## Bibliographic Information

- **Authors**: Chandler Davis, William M. Kahan
- **Title**: The rotation of eigenvectors by a perturbation
- **Journal**: SIAM Journal on Numerical Analysis
- **Volume/Issue**: 7(1)
- **Pages**: 1–46
- **Year**: 1970
- **Secondary source**: Yu, Y., Wang, T., Samworth, R. J., "A useful
  variant of the Davis–Kahan theorem for statisticians", Annals of
  Statistics 43(3):2028–2061, 2015, Theorem 1 — the classical Davis–Kahan
  sin Θ bound restated with mixed population/sample separation and
  constant 1; the operator-norm variant used here is noted in the paper.
  (Corrected 2026-08-21 from "Theorem 2": the paper's Theorem 2 is a
  population-gap, constant-2 result, a different statement — see
  `proposals/discharge-perturbation-axioms.md`'s Step-0 survey.)

## Scope of Results Used

The sin Θ theorem for invariant spectral subspaces, in the projector
form used by the event-driven persistence frontier.

## Theorem to Declaration Mapping

| Theorem | Lean Declaration | Module |
|---------|------------------|--------|
| §3 (sin Θ theorem) via Yu–Wang–Samworth Thm 1 (operator-norm variant, bottom cluster) | `davis_kahan_sin_theta` (**proved theorem** — retired from axiom 2026-08-21 by the Duhamel/exponential-integral route of `proposals/discharge-perturbation-axioms.md`; `#print axioms` reads only `propext, Classical.choice, Quot.sound`) | `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan` |
| §3 (sin Θ theorem), the *difference* (subspace-distance) shape at one-sided eigenvalue separation and equal rank | `l2OpNorm_bandProjector_sub_bandProjector_le` / `_le_of_mem` (**proved theorems**, 2026-08-24, `proposals/band-davis-kahan-difference.md`; through the equal-rank gap identity of `ProjectionGap.lean` plus the commutator/shift engine at the complement projector; constant 1) | `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan` |
| YWS 2015 Theorem 1 in its *literal* form: the pairwise mixed separation `δ = inf{|λ̂ − λ| : λ in the population cluster, λ̂ in the sample outside-cluster set|}` at constant 1 — the eigenvalue-cluster-separated generalization of the difference form (strictly weaker hypotheses; interior perturbation eigenvalues handled in-proof) | `l2OpNorm_bandProjector_sub_bandProjector_le_of_pairwise` (**proved theorem**, 2026-08-24, `proposals/band-davis-kahan-cluster.md`; interior case by the projector-free Parseval expansion at a B-eigenvector, boundary case by the capture-equality window transfer `bandProjector_eq_of_forall_mem_iff` + the engine at the cluster-range center/radius) | `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan` |
| YWS 2015 Theorem 1's *both-gaps* variants: separation assumed on both the population and sample spectra at constant 2, no dimension hypothesis — restated here as the pairwise-separation analog (both out-of-window flanks δ-separated pairwise, the two mirror-shaped hypotheses) | `l2OpNorm_bandProjector_sub_bandProjector_le_two_of_symm` (**proved theorem**, 2026-08-24, `proposals/band-davis-kahan-symmetric.md`; constant 2 is exactly the triangle inequality at the decomposition `P − Q = (I−Q)P − Q(I−P)`, the rank-free pairwise product bound at both argument orders, `l2OpNorm_transpose` moving the right action; unequal ranks force `δ ≤ ‖A − B‖` in-proof) | `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan` |

## Notes

- The Scaffold statement is for the projector onto the `k+1` smallest
  eigenvalues, with the two-cluster separation hypothesis on sorted
  eigenvalues, distance measured by the ℓ² operator norm
  (`Matrix.L2OpNorm`).
- A per-step consequence, `spectral_persistence`, formerly composed the
  per-step Davis–Kahan bound with Weyl gap stability along an event
  stream. Deprecated 2026-08-17 (zero non-QA consumers) and retired
  2026-08-20: the derived layer's two-endpoint chain
  (`davisKahanTwoPoint`, `eventStreamProjectorDrift`) covers the
  motivating use — see `docs/6_SGT_BACKLOG.md` for the retirement
  record.

- `l2OpNorm_clusterProjector_sub_clusterProjector_le_two_of_symm`
  (proved 2026-08-24, `proposals/cluster-projector-symmetric.md`): the
  *both-gaps* difference shape at arbitrary eigenvalue sets —
  `‖P_A(S) − P_B(T)‖ ≤ 2‖A − B‖/δ` under two-flank center/radius
  separation with no rank hypothesis, the set twin of the window
  symmetric form and this source's Theorem-statement lineage completed
  to the set-valued cluster projectors. Route provenance only (the
  statement is proved, not admitted).
- `l2OpNorm_clusterProjector_mul_clusterProjector_le` /
  `l2OpNorm_clusterProjector_sub_clusterProjector_le` (proved 2026-08-24,
  `proposals/cluster-projector.md`): the set-form pair at
  `GraphTheory.ClusterProjector`'s cluster projectors — the theorem
  family's statements lifted from interval windows to arbitrary
  eigenvalue sets, matching the cluster form this source's Theorem-statement
  lineage is actually stated in; center/radius membership separation, the
  difference form at equal rank. Route provenance only (the statements are
  proved, not admitted); the YWS-literal *pairwise* set shape is a recorded
  open follow-on, not claimed.

## See Also

- [Perturbation map](../map/perturbation.md)
