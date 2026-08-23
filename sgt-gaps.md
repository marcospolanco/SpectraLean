# Requested Scaffold mathematics for the spectral-proof rewrite

The graph heat semigroup dependency is **resolved** by Scaffold commit
`7f379e91d797e520d99d9545642c7cb02939aacc`. Do not redo that work.

This list contains only standard finite-dimensional mathematics that the
remaining `proofs/spectral-proof/REWRITE_PLAN.md` theorems need. Scaffold
should own these reusable facts; `spectral-proof` will own the lifecycle
definitions, choice of bands, controller interpretation, and hub-removal
counterfactual.

## 1. Tikhonov hard-filter limit

For the existing `tikhonovShrinkage π λ = π / (λ + π)` API, provide the
standard positive-eigenvalue limit

```lean
Filter.Tendsto (fun π : ℝ => tikhonovShrinkage π λ) (𝓝 0) (𝓝 0)
```

under `0 < λ`, plus the finite spectral-sum/Parseval corollary: if every mode
in a finite selected tail has `gap ≤ λᵢ` with `0 < gap`, its squared filtered
coefficient energy tends to zero as `π → 0⁺` (or along an explicitly stated
positive filter). The result must be phrased as suppression of the selected
positive-eigenvalue tail, **not** as convergence to an arbitrary two-sided
band projector: ordinary Tikhonov is a low-pass filter and cannot erase modes
below a band's lower endpoint.

## 2. Discrete affine-control convergence

Provide a finite-vector wrapper around the standard scalar fact
`r^n → 0` for `|r| < 1`, suitable for functions `V → ℝ` with finite `V`:

```lean
Filter.Tendsto (fun n : ℕ => r ^ n • x) Filter.atTop (nhds 0)
```

under `|r| < 1`. A companion affine-iteration theorem is welcome:

```lean
xₙ₊₁ = (1 - α) • xₙ + α • equilibrium
```

converges to `equilibrium` for `0 < α` and `α < 2`. This is textbook
finite-dimensional dynamics, and it lets the rewrite state the controlled
transient without rebuilding topology over finite function spaces.

## 3. Finite graph heat-flow derivative and a first-order remainder bound

For `heatKernel A t = exp (-t • laplacian A)`, provide the standard
matrix-exponential calculus at time zero and a usable finite-time estimate.
The minimum API is:

```lean
HasDerivAt (fun t : ℝ => heatKernel A t *ᵥ x) (-(laplacian A *ᵥ x)) 0
```

and an explicit first-order remainder bound on a bounded interval, either in
Euclidean norm or entrywise. A semigroup-only equivalent is acceptable if it
supports a Taylor/mean-value bound for an observable formed from boundary
coordinates. State all symmetry/nonnegative-weight hypotheses only where they
are mathematically needed.

This is the standard analytic input for the rewrite's dissolution theorem;
the definition of lifecycle leakage and any interpretation of the resulting
bound remain in `spectral-proof`.

## Acceptance

Each item should be a proved public Scaffold theorem, without `axiom`,
`sorry`, or `admit`, accompanied by a small numeric QA fixture and a negative
or boundary-case witness for the stated hypotheses. Once these interfaces are
available, no further standard-mathematics request is currently anticipated.
