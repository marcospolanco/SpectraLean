# Information Theory (Finite Distributions)

**Status:** Canonical topic map  
**Last reviewed:** August 22, 2026

## Scope

Relative entropy (Kullback–Leibler divergence) and Shannon entropy for
distributions on a `Fintype`, with the classical inequalities that make
them usable. Everything in this area is **proved hard crust — no
axioms** (delivered 2026-08-22 by `proposals/finite-relative-entropy.md`;
verified by `#print axioms`: only `propext, Classical.choice,
Quot.sound`).

## Module

| Module | Contents |
| --- | --- |
| `Scaffold/Mathlib/InformationTheory/Entropy.lean` | `klTerm`, `klDiv`, `shannonEntropy`, Gibbs' inequality and the entropy maximum |

## Declarations

| Declaration | Kind | Statement |
| --- | --- | --- |
| `klTerm` | definition | One KL summand `a * log (a / b)` with the explicit `a = 0 ↦ 0` junk convention |
| `klDiv` | definition | Relative entropy `∑ i, klTerm (p i) (q i)` of `p` from `q` |
| `shannonEntropy` | definition | `−∑ i, klTerm (p i) 1` — the sign is visible in the definition |
| `sub_le_klTerm` | theorem | Term-wise information inequality: `a − b ≤ klTerm a b` under `0 ≤ a`, `0 < b` |
| `eq_of_klTerm_eq_sub` | theorem | Its strict companion: `klTerm a b = a − b` forces `a = b` |
| `klDiv_nonneg` | theorem | **Gibbs' inequality**: `0 ≤ klDiv p q` for probability vectors `p` against strictly positive `q` |
| `klDiv_eq_zero_iff` | theorem | Gibbs' equality case: `klDiv p q = 0 ↔ p = q` |
| `sum_inv_card_eq_one` | theorem | The uniform distribution on a nonempty `Fintype` sums to one (real coercion) |
| `klDiv_apply_uniform` | theorem | The uniform bridge: `klDiv p (n⁻¹) = log n − shannonEntropy p` |
| `shannonEntropy_le_log_card` | theorem | The **entropy maximum**: `shannonEntropy p ≤ log |V|` |
| `shannonEntropy_eq_log_card_iff` | theorem | Equality case: the maximum is attained exactly at the uniform distribution |
| `shannonEntropy_nonneg` | theorem | Entropy is nonnegative |

## Usage patterns

- The mixing-time program's `chiSquareDistance`
  (`GraphTheory.Mixing`) is the quadratic member of the same
  distribution-distance family; relative entropy against the stationary
  measure `stationaryVec` is the classical refinement of the same
  ℓ²(π) geometry and is the natural future consumer.
- `docs/3_SPECTRAL_THEORY.md`'s retained x90 pipeline names a "spectral
  entropy H(t)"; `shannonEntropy` now gives that quantity a real
  definition (spectral entropy itself — `H` of the normalized
  eigenvalue distribution — remains deferred per the proposal).

## QA

`Scaffold/QA/InformationTheory/Entropy_QA.lean` (31 declarations): the
divergence and entropy of the biased coin hand-computed, the equality
case exercised in both directions against raw computations, the uniform
bridge numerically cross-checked, the maximum attained at uniform and
strictly missed away from it (strictness only through the equality-case
iff), and the junk convention exhibited at the delta distribution.

## Cross-references

- [Proposal](../../proposals/finite-relative-entropy.md)
- [Sources Index](../sources/README.md) — no entries: this area has no
  admitted axioms, so no source citations are required.
- [Backlog item 6](../../docs/6_SGT_BACKLOG.md) — the entropy half of
  the thermodynamics/statistical-mechanics item.
