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

## See Also

- [Perturbation map](../map/perturbation.md)
