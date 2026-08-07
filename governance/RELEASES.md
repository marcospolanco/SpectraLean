# Release Notes

## [Unreleased]

## [0.1.0] - 2024-XX-XX

### Initial Release

First public release of Scaffold, providing mathlib-compatible axioms for modern concentration inequalities.

#### Added - Scalar Concentration

- **Subgaussian**: Norm definition, tail bounds, moment growth, linear combinations
- **Subexponential**: Norm definition, tail bounds, closure properties
- **Hoeffding**: Bounded independent variables tail inequality
- **Bernstein**: Variance-dependent tail inequality

#### Added - Core

- **RandomVariable**: Basic type alias for measurable functions
- **Norms**: Shared norm definitions and properties

#### Added - Infrastructure

- Lake build configuration with mathlib v4.12.0 dependency
- CI/CD with guardrails against `sorry` in public API
- Governance policies (Axiom, Deprecation, Contributing)
- Index structure for source mapping

#### Documentation

- Comprehensive README with quick start guide
- Axiom policy and deprecation policy
- Source indices for Vershynin and Tropp
- Topic maps for concentration inequalities

#### Known Limitations

- All concentration inequalities are axioms (not proved)
- Matrix concentration not yet included (planned for v0.2.0)
- Martingale inequalities not yet included (planned for v0.2.0)

#### Mathlib Version

- Pinned to mathlib v4.12.0
