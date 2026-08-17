# Deprecation Policy

This document defines the deprecation and migration policy for Scaffold.

## Goals

1. **Minimize disruption**: Downstream projects should continue working with minimal changes
2. **Clear communication**: All changes are documented and announced in advance
3. **Migration path**: Provide clear upgrade instructions

## Deprecation Process

### 1. Mathlib Replacement

When mathlib adds an equivalent theorem:

**Preferred: Direct Replacement**
```lean
-- Before (axiom)
namespace Scaffold.Mathlib.Probability.Concentration
axiom hoeffding_inequality : ...

-- After (mathlib re-export)
namespace Scaffold.Mathlib.Probability.Concentration
-- Import from mathlib and re-export with same name
theorem hoeffding_inequality := Mathlib.Probability.HoeffdingInequality
```

**If Rename Required:**
```lean
-- Mark old name as deprecated
@[deprecated hoeffding_inequality_v2]
alias hoeffding_inequality := hoeffding_inequality_v2
```

### 2. API Changes

For breaking changes to non-axiom APIs:

1. **Announce**: Add deprecation notice at least one minor release before removal
2. **Document**: Update `governance/RELEASES.md` with migration guide
3. **Warn**: Use `@[deprecated]` attribute with clear message

### 3. Timeline

- **Patch releases** (0.x.z): Bug fixes, emergency deprecations
- **Minor releases** (0.y.0): New features, deprecation warnings
- **Major releases** (x.0.0): Remove deprecated items

## Release Notes Template

```markdown
## Deprecated in v0.y.z

### `Scaffold.Mathlib.Probability.Concentration.hoeffding_inequality`
- **Reason**: Now available in mathlib as `Mathlib.Probability.hoeffding`
- **Migration**: No action needed - automatically uses mathlib version
- **Removes**: v0.z.0

### `Scaffold.Mathlib.Core.oldNorm`
- **Reason**: Replaced by `newNorm` for clarity
- **Migration**: Replace `oldNorm` with `newNorm` in your code
- **Removes**: v0.z.0
```

## Emergency Deprecation

If an axiom is found to be incorrect:

1. **Immediate patch release** with deprecation
2. **Security notice** if applicable
3. **Clear workaround** in release notes

## Migration Support

- Maintain migration guides in `governance/RELEASES.md`
- Provide search/replace patterns when possible
- Keep deprecation period at least one minor release (≥ 1 month)
