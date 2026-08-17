# Spectral Graph Theory

This index maps the SGT center: Laplacians, sorted spectra, cuts and
conductance, Cheeger theory, interlacing, and event-driven dynamics.

## Status

**Implemented and build-certified** (see the QA scoreboard):
`Scaffold.Mathlib.GraphTheory.{Spectral,Cheeger,Dynamics}`.

## Modules and Declarations

### `Scaffold.Mathlib.GraphTheory.Spectral` (SGT center)

Real definitions: `WAdj`, `deg`, `degreeMatrix`, `laplacian`,
`quadForm`, `rayleigh`, `onesVec`, `evals` (sorted spectrum),
`lambda2`, `spectralGap`, `spectralProjector`, `initialProjector`,
`eigvecOf`, `eigvalOf`, `vol`, `boundary`, `conductance`,
`cheegerConstant`, `eventUpdate`.

Proved theorems (no admission): `degreeMatrix_*`, `laplacian_symmetric`,
`laplacian_ones_in_kernel`, `evals_sorted`, `laplacian_quadForm`
(Dirichlet form), `laplacian_psd`, `eventUpdate_preserves_symmetry`,
`principalSubmatrix_symmetric`, `spectralProjector_symmetric`,
`conductance_nonneg`, `cheegerConstant_nonneg`,
`conductance_ge_cheegerConstant`.

Admitted axioms:

| Axiom | Description | Source |
|-------|-------------|--------|
| `eigen_interlacing_principal_submatrix` | Cauchy interlacing for principal submatrices | [Horn & Johnson](../sources/horn_johnson_matrix_analysis.md) |
| `lambda2_variational` | Courant–Fischer characterization of λ₂ | [Horn & Johnson](../sources/horn_johnson_matrix_analysis.md), [Chung](../sources/chung_spectral_graph.md) |

### `Scaffold.Mathlib.GraphTheory.Cheeger`

Real definition: `regularNormalizedLaplacian`.

| Axiom | Description | Source |
|-------|-------------|--------|
| `cheeger_lower_bound` | `φ(G)²/2 ≤ λ₂(L_sym)` for `d`-regular graphs | [Chung](../sources/chung_spectral_graph.md) |
| `cheeger_upper_bound` | `λ₂(L_sym) ≤ 2 φ(G)` for `d`-regular graphs | [Chung](../sources/chung_spectral_graph.md) |

### `Scaffold.Mathlib.GraphTheory.Dynamics` (dynamic frontier)

Real definitions: `TimeVaryingGraph`, `laplacianSequence`,
`IsEventDriven`, `laplacianSequence_symmetric`.

| Axiom | Description | Source |
|-------|-------------|--------|
| `spectral_persistence` | Per-step projector stability `≤ ε/γ` under gap-separated event streams | [Davis & Kahan 1970](../sources/davis_kahan_1970.md) |

## Applications

These declarations feed the perturbation bridge
([Perturbation map](perturbation.md)) and the spectral-persistence
research objective described in
[docs/3_SPECTRAL_THEORY.md](../../docs/3_SPECTRAL_THEORY.md).
