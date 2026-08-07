# Core Definitions

This module contains shared definitions and utilities used across Scaffold.

## Modules

### `RandomVariable.lean`

Basic type definition for real-valued random variables.

- **Type**: `RV Ω` - alias for `Ω → ℝ`
- **Purpose**: Minimal definition for measurable functions
- **Dependencies**: mathlib's MeasureTheory

### `Norms.lean`

Shared norm definitions for concentration inequalities.

- **Definitions**: `l_infty_norm`
- **Purpose**: Essential supremum norm for bounded variables
- **Dependencies**: mathlib's Analysis.Normed

## Design Principles

1. **Minimal**: Keep core definitions as small as possible
2. **Mathlib-first**: Use existing mathlib definitions when available
3. **Stable**: Core API should change rarely and with good reason

## Adding to Core

Before adding to Core, consider:

- Is this definition used by multiple modules?
- Is there an equivalent in mathlib we should use instead?
- Is this definition stable and well-designed?
