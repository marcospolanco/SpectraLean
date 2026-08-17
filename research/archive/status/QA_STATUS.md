# QA Policy Application Status

This document tracks the application of QA policy to existing axiom files.

## spectral.lean

### Completed QA Documentation

| Axiom/Theorem | QA Lemma | Status | Location |
|--------------|----------|--------|----------|
| `laplacian_symmetric` | `laplacian_preserves_symmetry_QA` | ✅ Done | Basic_QA.lean:44 |
| `laplacian_ones_in_kernel` | `laplacian_ones_in_kernel_QA` | ✅ Done | Basic_QA.lean:67 |
| `degreeMatrix_diagonal` | `degreeMatrix_is_diagonal_QA` | ✅ Done | Basic_QA.lean:34 |
| `degreeMatrix_diagonal` | `degreeMatrix_diagonal_nonneg_QA` | ✅ Done | Basic_QA.lean:44 |
| `cheeger_lower_bound` | `cheegerConstant_nonneg_QA` | ✅ Done | Basic_QA.lean:171 |
| `eventUpdate` (def) | `eventUpdate_preserves_symmetry_QA` | ✅ Done | Basic_QA.lean:107 |
| `vol` (def) | `vol_nonneg_QA` | ✅ Done | Basic_QA.lean:187 |
| `boundary` (def) | `boundary_nonneg_QA` | ✅ Done | Basic_QA.lean:205 |
| `conductance` (def) | `conductance_nonneg_QA` | ✅ Done | Basic_QA.lean:225 |
| `vol_add_disjoint` | `vol_add_disjoint_QA` | ✅ Done | Basic_QA.lean:128 |
| `boundary_complement_symmetry` | `boundary_complement_symmetry_QA` | ✅ Done | Basic_QA.lean:144 |

### TODO: Need QA Lemmas

| Axiom/Theorem | Proposed QA Lemma | Priority |
|--------------|------------------|----------|
| `cheeger_upper_bound` | Simple consequence of upper bound | Medium |
| `eventUpdate_bounded` | Norm bound verification | High |
| `spectral_persistence_under_events` | Basic persistence check | High |
| `laplacian_psd` | PSD property check | Medium |
| `laplacian_zero_multiplicity_eq_components` | Component count check | Low |

### Axioms with True Conclusions (Need Fixing)

| Axiom/Theorem | Issue | Action Required |
|--------------|-------|-----------------|
| `laplacian_evals_sorted` | Returns `True` | Replace with proper type |
| `cheeger_normalized_laplacian` | Returns `True` | Replace with proper type |
| `eigen_interlacing_principal_submatrix` | Returns `True` | Replace with proper type |
| `weyl_perturbation_bound` | Returns `True` | Replace with proper type |
| `davis_kahan_subspace_stability` | Returns `True` | Replace with proper type |
| `courant_fischer_minmax` | Returns `True` | Replace with proper type |
| `lambda2_variational` | Returns `True` | Replace with proper type |
| All random walk theorems | Return `True` | Replace with proper types |
| All expander theorems | Return `True` | Replace with proper types |
| All spanning tree theorems | Return `True` | Replace with proper types |
| All heat kernel theorems | Return `True` | Replace with proper types |

## LLM Assessment Log (Sniff Tests)

| Date | Target Layer | Result | Judge | Notes |
|------|--------------|--------|-------|-------|
| 2026-02-10 | Spectral Graph QA (29 lemmas) | ✅ **PASSED** | Gemini CLI | Lemmas are well-known (e.g., ones vector in kernel, symmetry preservation) and properly articulate axioms. Zero innovation detected. |

## Summary

- **Total axioms/theorems**: ~50
- **With QA documentation**: 11 (22%)
- **With QA lemmas created**: 11 (22%)
- **Need immediate QA**: 3 (eventUpdate_bounded, spectral_persistence, cheeger_upper)
- **Have True conclusions**: ~20 (40%) - need fixing per QUALITY_CRITERIA.md

## Next Steps

1. **High Priority**: Create QA lemmas for event-driven axioms (eventUpdate_bounded, spectral_persistence)
2. **Medium Priority**: Fix `True` conclusions in Cheeger and interlacing sections
3. **Low Priority**: Fix `True` conclusions in advanced sections (random walk, expanders, heat kernel)

## QA Lemma Quality Check

All created QA lemmas follow the thin layer policy:
- ✅ 1-5 line proofs
- ✅ Simple unfolding and application
- ✅ Well-known consequences
- ✅ Would fail if axiom was wrong

Example from `vol_nonneg_QA`:
```lean
theorem vol_nonneg ... :
  0 ≤ vol A S := by
  rw [vol]
  apply Finset.sum_nonneg
  intro i _
  apply hnonneg
```
This is 4 lines, directly from definition, exercises the nonnegativity axiom.

---

Last updated: 2025-02-10
