# Mathlib Upstream Coverage Map

**Status:** Canonical reference, dated snapshot against a pinned dependency  
**Pinned Mathlib:** v4.14.0 (`lakefile.lean`)  
**Survey date:** 2026-08-19 (electrical/flow row re-surveyed for
`proposals/electrical-flow-routing.md` step 0; other rows as of 2026-08-18)

## Purpose

This document answers a different question than the [SGT Radar](7_SGT_RADAR.md).
The radar scores what *Scaffold* has built — proved and admitted — on top of
its dependencies. This document records what the *pinned Mathlib itself*
provides, per discipline, independent of anything Scaffold has done with it.
Read together: nearly every axiom Scaffold admits correlates with a gap
recorded here, and that correlation is the point — Scaffold's trust
boundary is not an arbitrary editorial choice, it traces Mathlib's actual
gaps.

[Strategy](1_STRATEGY.md)'s "Why spectral graph theory is a useful focus"
names the tendrils SGT crosses: finite graph combinatorics, matrices and
operator norms, probability and concentration, and perturbation theory.
This document surveys each, plus the narrower SGT-specific areas the [SGT
Radar](7_SGT_RADAR.md)'s eight subject axes track (random walks, electrical
structure, functional inequalities, nonnegative-matrix theory).

**This is a snapshot, not a promise.** Re-run the survey (methodology
below) whenever the Mathlib pin in `lakefile.lean` changes, or when a
proposal's own targeted search finds something this map missed — record
the correction here so it doesn't live only inside one proposal.

## Coverage by tendril

| Tendril | Coverage | Evidence |
|---|---|---|
| Finite graph combinatorics | **Strong** | `Mathlib/Combinatorics/SimpleGraph/` — 48 files: `LapMatrix.lean` (Laplacian, kernel-reachability, component-rank), `Walk.lean`/`Path.lean` (connectivity), `Clique.lean`, `Coloring.lean`, `StronglyRegular.lean`, `Turan.lean`, `Hamiltonian.lean`, `Matching.lean`, `Girth.lean`, `Diam.lean`, `AdjMatrix.lean`, `DegreeSum.lean`. Scaffold's `SimpleGraphAdapter.lean` bridges directly into this. |
| Matrix / spectral linear algebra | **Solid core, stops at extremes** | `Matrix.IsHermitian` spectral theorem (`LinearAlgebra/Matrix/Spectrum.lean`), `PosDef.lean`/`PosSemidef`; the extreme-eigenvalue variational principle `LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional`/`_iSup_` (`Analysis/InnerProductSpace/Rayleigh.lean:230,249`) plus invariant-subspace restriction (`invariant_orthogonalComplement_eigenspace`, `Analysis/InnerProductSpace/Spectrum.lean:65`; `IsSymmetric.restrict_invariant`, `Analysis/InnerProductSpace/Symmetric.lean:127`). **Absent:** general Courant–Fischer min-max for arbitrary eigenvalue index, Cauchy interlacing, Weyl's eigenvalue-perturbation inequality — zero hits repo-wide for all three, under any naming, as of this survey. Operator norms: `Mathlib/Analysis/CStarAlgebra/Matrix.lean` supplies the scoped `Matrix.L2OpNorm` instances (`NormedRing`, `CStarRing (Matrix n n ℝ)`) that Scaffold's Weyl axiom and resolvent module use, but **no norm↔eigenvalue bridge exists for real symmetric matrices** — the C*-algebra thread `IsSelfAdjoint.spectralRadius_eq_nnnorm` is stated for `[CStarAlgebra A]`, which extends `NormedAlgebra ℂ A`, and is structurally inapplicable to real matrices (elaboration-verified 2026-08-19); Scaffold's `Analysis.OperatorTheory.Resolvent` proves the bridge (`l2OpNorm_eq_max_abs_evals`) locally from the spectral theorem instead. |
| Probability & concentration | **Foundational only** | `Mathlib/Probability/` — 60+ files, but primitives: `Moments.lean`, `Variance.lean`, martingale/stopping-time infrastructure, `StrongLaw.lean`, `BorelCantelli.lean`, standard distributions (`Gaussian.lean`, `Binomial.lean`, `Poisson.lean`). **Zero** named concentration inequalities — no Hoeffding, no Bernstein, no sub-Gaussian package under any name. This is why Scaffold's `hoeffding_iid`/`bernstein_iid` could be converted from admitted to proved (`docs/7_SGT_RADAR.md`, axiom minimization axis): the ingredients exist upstream, the named theorems don't. |
| Perturbation theory (Weyl / Davis–Kahan / interlacing) | **Absent** | Zero matches anywhere in the pinned tree, under any naming — checked directly against `Mathlib/LinearAlgebra`, `Mathlib/Analysis`. This is the weakest tendril outright, and it is exactly the set Scaffold carries at the perturbation boundary: Weyl and Davis–Kahan as admitted axioms (the perturbation bridges), while interlacing — still absent upstream — was proved *locally* on 2026-08-18 from Scaffold's own Courant–Fischer engine (itself built on Mathlib's spectral theorem), retiring its axiom. Not a coincidence: absence upstream forced the local engine. |
| Random walks / Markov chains (graph-native) | **Absent** | No transition-matrix or stationary-distribution package for graphs. The only "Markov" hits in the pinned tree are Markov's inequality (`Function/LpSeminorm/ChebyshevMarkov.lean`) and the Riesz–Markov–Kakutani representation theorem — unrelated to stochastic processes on graphs. `Data/Matrix/DoublyStochastic.lean` exists (Birkhoff–von Neumann territory) but is not graph-native. |
| Electrical structure (resistance, Kirchhoff, Matrix-Tree) | **Absent** | No Moore–Penrose pseudoinverse — `LinearAlgebra/Matrix/NonsingularInverse.lean:17` states explicitly: "pseudoinverses which we do not consider here." No resistance, no spanning-tree enumeration, no Kirchhoff identity under any naming. Re-surveyed 2026-08-19 for the electrical-flow proposal: also no network-flow/max-flow/circulation API, no graph-native divergence (the only `Divergence` files are the box/measure-integral divergence *theorems* on continua), and no flow/energy API on the one oriented-edge type (`SimpleGraph.Dart` is counting machinery) — the flow representation decision is recorded in that proposal. |
| Functional inequalities (Poincaré, log-Sobolev, Dirichlet forms) | **Absent** | The only "Poincaré" hit in the entire pinned tree is `Geometry/Manifold/PoincareConjecture.lean` — the topological conjecture, unrelated to the functional-analysis inequality. No log-Sobolev, no Dirichlet-form theory under any naming. |
| Perron–Frobenius / nonnegative-matrix theory | **Absent** | Zero hits, checked against `Mathlib/LinearAlgebra` and `Mathlib/Combinatorics` directly (the only "Perron" hits anywhere in the pinned tree are unrelated `BoxIntegral` files — Perron integration, a different Oskar Perron result). |

## The pattern

Scaffold's axiom boundary is not an arbitrary trust decision — it is close
to a direct trace of this map. Weyl, Davis–Kahan, and the Cheeger hard
direction are admitted because nothing upstream exists to build them
from. Hoeffding/Bernstein got proved, not admitted, because Mathlib
supplies the raw probability machinery even though it lacks the named
theorems. Where Mathlib has a partial tendril — the extreme-eigenvalue
Rayleigh principle plus invariant-subspace restriction — Scaffold built
the full Courant–Fischer min–max engine locally and then proved both the
λ₂ instance (2026-08-18, `lambda2_variational`) and interlacing
(`eigen_interlacing_principal_submatrix`, retired from axiom the same
day) on top of it, even though the general min–max theorem isn't
upstream.

The radar's per-axis ceilings inherit this directly: axes 2–3 (spectral
linear algebra, variational methods) are ceiling-limited by Mathlib
stopping at extreme eigenvalues; axes 5–6 (random walks, electrical
structure) are ceiling-limited by Mathlib having no graph-native or
resistance theory at all, so everything there is Scaffold-original; axis
7's perturbation half is ceiling-limited by Weyl/Davis–Kahan/interlacing
being genuinely unformalized upstream, not merely unintegrated.

## Survey methodology

Direct repository-wide search against `.lake/packages/mathlib` at the pin
recorded in `lakefile.lean`: `find`/`grep -rl` for each tendril's standard
names and known synonyms, cross-checked by reading the matched files'
declarations rather than trusting filename matches alone (e.g. the "Weyl"
and "Markov" false positives — `RootSystem` files and
`ChebyshevMarkov.lean` — were opened and excluded on content, not assumed
irrelevant from the name). Absence claims are therefore search-based, not
exhaustive proof of absence; if the Mathlib pin advances, re-run before
relying on a row here.

## Source provenance

Assessed directly against `.lake/packages/mathlib` at the `lakefile.lean`
pin, 2026-08-18, in support of `proposals/prove-lambda2-variational.md` and
general backlog prioritization under [Strategy](1_STRATEGY.md)'s
[load-bearing growth](1_STRATEGY.md#load-bearing-growth-the-path-to-falsifiability)
principle.
