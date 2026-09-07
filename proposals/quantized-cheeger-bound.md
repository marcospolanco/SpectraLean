# Proposal: A Quantized Cheeger Inequality

**Status:** Proposed. Restated in pure-mathematics form 2026-09-07 from
an external request relayed by the operator (not tracked in this
repository — see `.gitignore`); no operational, product, or patent
framing survives into this document, only the underlying mathematical
ask. Authorizes no Lean changes, axiom admissions, document rewrites,
or transit-map edits.

Companion to `Scaffold/Mathlib/GraphTheory/Cheeger.lean`
(`cheeger_upper_bound`/`cheeger_lower_bound`, both complete, zero-
admitted hard crust — the theorem this proposal quantizes, not
extends) and `Scaffold/Mathlib/GraphTheory/Mixing.lean`
(`secondEval_normalizedLaplacian_le_two`, the a priori spectral range
this proposal's quantizer needs).

## The claim this document is answering

The relayed request's framing was accurate: eigenvalues and
eigenvectors are treated as exact real numbers throughout this
project, with no rounding/discretization apparatus anywhere. The
request asks how rounding "the top-`k` eigenvalues" into `b`-bit
integer buckets propagates through Cheeger's inequality, as an
explicit error envelope `±ε_Q`.

**A scope correction, found here:** Cheeger's inequality, as proved in
this project (`cheeger_upper_bound`/`cheeger_lower_bound`), is a
statement about exactly *one* eigenvalue — `λ₂`, the spectral gap
(`secondEval`) — not a general top-`k` family. Quantizing "through
Cheeger's inequality" specifically therefore only needs quantizing
`λ₂`, not a `k`-eigenvalue set; the request's "top-`k`" framing is
likely inherited from a broader spectral-embedding context (where
several eigenvalues matter) that does not apply to this specific
target. This document answers the well-posed sub-question — a
quantized `λ₂` propagated through the two already-proved Cheeger
inequalities — which is exactly what "propagates through Cheeger's
inequality" can mean for a single-eigenvalue theorem.

## What's already on the shelf

- **Both directions of Cheeger's inequality, complete, zero-admitted**
  — `cheeger_upper_bound` (`Cheeger.lean:395`): `secondEval
  (regularNormalizedLaplacian A d) ≤ 2 * cheegerConstant A`; and
  `cheeger_lower_bound` (`Cheeger.lean:1527`): `(cheegerConstant A)^2 /
  2 ≤ secondEval (regularNormalizedLaplacian A d)`. Together these
  give the classical two-sided sandwich `λ₂/2 ≤ φ(G) ≤ √(2λ₂)` — pure
  algebra from the two theorems, not separately proved anywhere as its
  own combined statement, but immediate.
- **The a priori range for `λ₂`** — `secondEval_normalizedLaplacian_
  le_two` (`Mixing.lean:3770`): `secondEval (normalizedLaplacian A) ≤
  2` (paired with the trivial `0 ≤ secondEval` from
  `regularNormalizedLaplacian_psd`-style nonnegativity elsewhere in
  the shelf), giving the closed interval `[0, 2]` — exactly the range
  a `b`-bit quantizer needs a fixed resolution over. The bridge to
  `regularNormalizedLaplacian` (the operator `cheeger_upper_bound`/
  `cheeger_lower_bound` are actually stated in terms of) is
  `normalizedLaplacian_eq_regularNormalizedLaplacian` (`Normalized.
  lean:325`, same `hd`/`hdpos` hypotheses `cheeger_upper_bound` already
  carries) plus `secondEval_congr` (proof-irrelevance transport across
  equal operator spellings, `Spectral.lean`).
- **The exact rounding-error primitive, already in the pinned
  Mathlib** — `round : α → ℤ` and `abs_sub_round (x : α) : |x - round
  x| ≤ 1 / 2` (`Mathlib.Algebra.Order.Floor:1489`): the nearest-
  integer rounding error is at most `1/2`, unconditionally. This is
  the entire numerical content a uniform quantizer needs; nothing
  about it is graph-specific or needs re-derivation.

## What's not on the shelf

- **Any quantization/rounding apparatus for graph-spectral quantities**
  — confirmed absent by search (no `quantiz`/`bucket`/`round` usage
  anywhere under `Scaffold/`). The one new object this proposal needs
  is a **uniform `b`-bit quantizer over a known range**: given a value
  `x ∈ [0, R]`, report the midpoint of whichever of `2^b` equal-width
  buckets `x` falls into. This is standard and small — a linear
  rescaling wrapped around Mathlib's `round` — but it does not exist
  in this project and needs to be defined, not merely cited.

## The route: define, bound, then substitute

**The quantizer.** For `b : ℕ` and `R : ℝ` with `0 < R`,
```
noncomputable def quantize (b : ℕ) (R x : ℝ) : ℝ :=
  (R / 2 ^ b) * (round (x * 2 ^ b / R) : ℝ)
```
— rescale `x` into `[0, 2^b]` units, round to the nearest integer
(Mathlib's `round`), rescale back. The reported integer `round (x *
2^b / R) : ℤ` is literally the "`b`-bit integer bucket index" the
request names (at the boundary `x = R` it lands on the bucket index
`2^b` rather than `2^b − 1` — `2^b + 1` representable points, not
`2^b`, the honest off-by-one every closed-interval uniform quantizer
has; worth stating precisely rather than silently rounding down).

**The quantization error bound.**
```
theorem abs_sub_quantize_le (b : ℕ) {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |x - quantize b R x| ≤ R / 2 ^ (b + 1)
```
Route: `|x - quantize b R x| = (R / 2^b) * |x * 2^b / R - round (x *
2^b / R)|` (factor `R/2^b` out, using `hR.ne'`/`pow_pos` for the
division algebra) `≤ (R / 2^b) * (1/2)` (`abs_sub_round` applied at `x
* 2^b / R`) `= R / 2^(b+1)`. Five to ten lines of field algebra around
one Mathlib lemma — no new inequality technique.

**The quantized Cheeger sandwich.** Set `R := 2` (the a priori range),
`ε_Q := 2 / 2 ^ (b + 1) = 1 / 2 ^ b`, and let `λ̃₂ := quantize b 2
(secondEval (regularNormalizedLaplacian A d) _ hcard)` be the
quantized spectral gap. Then:
```
theorem quantized_cheeger_le (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d)
    (hdpos : 0 < d) (hcard : 2 ≤ Fintype.card V) (b : ℕ) :
    (λ̃₂ - 1 / 2 ^ b) / 2 ≤ cheegerConstant A ∧
      cheegerConstant A ≤ Real.sqrt (2 * (λ̃₂ + 1 / 2 ^ b))
```
Route: purely algebraic, from the two already-proved Cheeger
inequalities and `abs_sub_quantize_le`'s two-sided form (`λ₂ - ε_Q ≤
λ̃₂ ≤ λ₂ + ε_Q`, hence `λ₂ ∈ [λ̃₂ - ε_Q, λ̃₂ + ε_Q]`):
- **Lower bound on `φ`:** `cheeger_upper_bound` gives `λ₂ ≤ 2φ`, i.e.
  `φ ≥ λ₂ / 2 ≥ (λ̃₂ - ε_Q) / 2` (monotonicity, `λ₂ ≥ λ̃₂ - ε_Q`).
- **Upper bound on `φ`:** `cheeger_lower_bound` gives `φ² ≤ 2λ₂`, so
  (nonnegativity of `φ`, `Real.sqrt_le_sqrt` monotonicity) `φ ≤ √(2λ₂)
  ≤ √(2(λ̃₂ + ε_Q))` (again `λ₂ ≤ λ̃₂ + ε_Q`).

This is exactly the requested "error envelope `±ε_Q`" — an explicit,
closed-form two-sided bound on the true Cheeger constant purely in
terms of the rounded, `b`-bit-representable `λ̃₂`, with the error
`ε_Q = 1/2^b` appearing linearly in the lower bound and inside the
square root in the upper bound (the two directions of Cheeger's own
inequality are not symmetric, so neither is their quantized error
propagation — a genuine, non-obvious-until-computed feature of the
answer worth stating explicitly rather than assuming a single uniform
`±ε_Q` shape).

## Scope decision: single eigenvalue, not top-`k`

Recorded once already above, restated as a decision: this proposal
targets `λ₂` alone, matching what Cheeger's inequality actually
constrains in this project. A genuine top-`k` quantization story (e.g.
for a spectral embedding into `ℝ^k` or a `k`-way Cheeger statement)
would be a different, larger proposal with a different consumer
(`multiway-cheeger-hard-direction.md`'s embedding, if that were ever
adopted) — not conflated with this one.

## Build order

### Step 1: The quantizer and its error bound

`quantize` and `abs_sub_quantize_le` above — pure real-number algebra,
no graph content, no dependency on Cheeger's own machinery. Natural
home: a small new section, either inside `Cheeger.lean` (since it is
this proposal's only consumer) or a minimal standalone file if a
Step-0 survey finds a cleaner fit; either is fine, left to the
implementing run.

### Step 2: The a priori range bridge

`secondEval (regularNormalizedLaplacian A d) (regularNormalizedLaplacian_symmetric A hA d) hcard ≤ 2`
— transported from `secondEval_normalizedLaplacian_le_two` through
`normalizedLaplacian_eq_regularNormalizedLaplacian` and
`secondEval_congr`, plus the companion `0 ≤ secondEval (...)`
(nonnegativity of the normalized Laplacian's spectrum, already on the
shelf via its PSD-ness). Packages the range `[0, 2]` `quantize` needs
at `R := 2`.

### Step 3: The quantized sandwich

`quantized_cheeger_le` above, assembled from Step 1, Step 2, and the
two already-complete Cheeger theorems. Pure composition — the last
piece of genuinely new proof content is Step 1; Step 3 is algebra.

### Deferred and removed

- **A general top-`k` quantization theory** — out of scope (see
  "Scope decision").
- **A non-uniform / entropy-optimal quantizer** — the request asks for
  `b`-bit integer buckets, which is the uniform-quantizer shape; a
  variable-rate or Lloyd–Max-optimal quantizer is a different, larger
  problem not asked for here.
- **Extending the quantizer to the multiway/`k`-way Cheeger constant**
  (`Multiway.lean`'s `maxPartConductance`) — a plausible future
  follow-on once (if) `multiway-cheeger-hard-direction.md` or its
  sibling `multiway-expansion.md` machinery names a consumer for it;
  not proposed here.

## QA plan

- `abs_sub_quantize_le` numeric pins: `b = 0` (the coarsest single-bit
  quantizer, `ε_Q = 1`, `R = 2` — checked against a hand computation),
  and a `b = 3` instance with a specific `x` landing exactly on a
  bucket boundary (the `round`-at-`.5` tie-breaking behavior made
  concrete, not left implicit).
- The boundary-count fence: an explicit witness that `quantize b R`
  attains `2^b + 1` distinct values on `[0, R]`, not `2^b` — the
  off-by-one finding above, checked rather than asserted.
- `quantized_cheeger_le` on the K₂/path/cycle fixtures already
  carrying exact `secondEval` pins elsewhere in `Cheeger_QA.lean`,
  confirming the quantized sandwich's two bounds both hold at the
  fixture's *exact* known `cheegerConstant` value (a positive witness
  that the envelope is honest, not vacuous) at a couple of concrete
  `b` values, with the bound visibly tightening as `b` grows.

## Gate — Medium, no dependency

Like `boundary-outflow-lemma.md` and `rank-one-edge-perturbation-norm.
md`, this needs no operator sign-off or technical-direction decision:
Cheeger's inequality is core, complete, zero-admitted, and not part of
any gated backlog item (unlike `nonautonomous-propagator-gronwall-
bound.md`'s territory); the one new object (`quantize`) is elementary
real-number algebra around an already-proved Mathlib lemma. Tracked as
**Medium** in `proposals/README.md`'s Active priority table.

## Operating instructions for an autonomous run

- Steps 1–3 are small enough to plausibly land in a single run.
- **No new axioms.** Everything stays inside already-proved
  `Cheeger.lean`/`Mixing.lean`/`Normalized.lean`/`Spectral.lean`
  machinery plus Mathlib's `round`/`abs_sub_round`; if the a priori
  range bridge (Step 2) needs something genuinely absent, stop and
  record the precise obstruction in `docs/6_SGT_BACKLOG.md` rather
  than admitting anything.
- Ship the boundary-count fence and the tightening-with-`b` witness
  (QA plan above) in the same delivery as Step 3, not as a follow-on
  audit pass.

## Open next step

Ready to pick up immediately — no dependency on any other proposal's
status.
