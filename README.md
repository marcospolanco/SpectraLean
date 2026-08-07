# Scaffold

Scaffold is a mathlib compatible Lean library that provides a **textbook anchored**, **axiom level** foundation for modern applied mathematics.

## Overview

Scaffold treats trusted textbook results as explicit axioms with precise citations, so developers can build formally checked new reasoning today. Each axiom is designed to be replaced by fully proved mathlib theorems over time.

### Key Features

- **Mathlib compatible**: Mirrors mathlib's namespace conventions and directory layout
- **Textbook anchored**: Every axiom includes precise citations to primary sources
- **Explicit assumptions**: All unproven results are declared as `axiom` (not hidden `sorry`)
- **Replaceable**: Designed for easy migration to mathlib theorems as they become available
- **Minimal blast radius**: Small, stable core with many focused axioms

## Installation

Add Scaffold as a dependency in your `lakefile.lean`:

```lean
require scaffold from git "https://github.com/your-org/scaffold.git" @ "main"
```

## Quick Start

Import specific modules as needed:

```lean
import Scaffold.Mathlib.Probability.Concentration.Scalar.Subgaussian
import Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding
import Scaffold.Mathlib.Probability.Concentration.Scalar.Bernstein
```

## Project Structure

```
Scaffold/
├── Mathlib/           # Public API - mathlib compatible axioms
│   ├── Core/          # Shared definitions
│   └── Probability/   # Concentration inequalities
├── Trusted/           # Policy documentation
└── Internal/          # Internal utilities
```

## Citation Policy

Every axiom in Scaffold includes:

- A doc comment explaining the mathematical statement
- A precise citation (author, title, edition, chapter/section, theorem number, page)
- A note mapping the formal statement to the mathematical source

See `index/sources/` for detailed mappings from theorems to Lean identifiers.

## Phase 1 Scope

Initial release focuses on high-impact concentration inequalities:

- **Scalar concentration**: Subgaussian, Subexponential, Hoeffding, Bernstein, Azuma, Freedman
- **Matrix concentration**: Matrix Hoeffding, Matrix Bernstein, Gaussian spectral bounds
- **Perturbation theory**: Davis-Kahan, resolvent bounds, spectral projector stability

See `governance/ROADMAP.md` for future plans.

## License

Apache 2.0 - see [LICENSE](LICENSE) for details.

## Contributing

Scaffold welcomes contributions! See `governance/CONTRIBUTING.md` for guidelines.

## QA and Trust

Scaffold uses a three-layer architecture to ensure trustworthiness:

1. **Trusted Axioms** (`Scaffold/Trusted/`) - Textbook results as explicit axioms with citations
2. **QA Lemmas** (`Scaffold/QA/`) - Real Lean proofs of simple consequences that sanity-check axioms
3. **Derived Work** (`Scaffold/Derived/`) - Novel mathematics built on top

The QA layer provides a **thin but real** verification that axioms are stated correctly. Every axiom is exercised by QA lemmas with actual Lean proofs, ensuring the formalization matches intended mathematical meaning.

**Key principle**: QA lemmas are trivial (1-5 line proofs) but catch mis-specifications. If axioms are wrong, these simple sanity checks fail.

See [QA Policy](governance/QA_POLICY.md) for details on the three-layer architecture and verification process.

## Test Coverage

Track axiom verification status through our QA scoreboards:

- [Spectral Graph Theory Scoreboard](Scaffold/QA/SpectralGraph/QA_SCOREBOARD.md) - 31 QA lemmas tracking Cheeger inequalities, Laplacian properties, and spectral gap bounds

Each scoreboard shows:
- ✅ COMPILES - QA lemma verified with real Lean proof
- ⚠️ PARTIAL - Statement compiles with `sorry` proof
- ❌ BROKEN - Type errors or missing definitions
- 📋 TODO - Not yet attempted

## Disclaimer

Scaffold does not aim to replace mathlib. Axioms are intended as temporary placeholders until mathlib provides formalized versions. Always check `governance/AXIOM_POLICY.md` for usage guidelines.

## Links

- [Axiom Policy](governance/AXIOM_POLICY.md)
- [QA Policy](governance/QA_POLICY.md)
- [Deprecation Policy](governance/DEPRECATION_POLICY.md)
- [Contributing Guidelines](governance/CONTRIBUTING.md)
- [Source Index](index/sources/)
- [Topic Maps](index/map/)
