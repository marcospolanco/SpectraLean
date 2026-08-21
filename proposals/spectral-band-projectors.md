# Proposal: Spectral Band Projectors

**Status:** Step 4 DELIVERED 2026-08-21 — the program is COMPLETE (see
the delivery record under "Build order"). Priority **High**.
Assistant's assessment of project direction, requested 2026-08-19,
promoted from `sgt-gaps.md` item 5. Authorizes no Lean changes, axiom
admissions, or external publication.

Companion to `sgt-gaps.md` and `Scaffold/Mathlib/GraphTheory/Spectral.lean`'s
already-delivered `spectralProjector`, of which this proposal is a direct
generalization. No backlog gate applies.

## Clean-room boundary

Internal prioritization and analysis. If counsel approves a public
repository export, restate from standard functional-analysis sources.
Do not copy this proposal verbatim.

Assessed from `Spectral.lean:271` (`spectralProjector M hM c`, the
below-threshold projector already delivered and load-bearing for
`initialProjector`) and
`.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Projection.lean`
(the Hilbert projection theorem, confirmed present 2026-08-19).

## External consumer

Bandpass filtering in graph signal processing; frequency-selective
analysis (e.g., functional-connectivity work studying a specific band of
a network's spectrum rather than the whole thing).

## Recommendation

Define the two-sided band projector for an interval `[a, b]` of the
spectrum and prove: idempotence, self-adjointness, orthogonality of
disjoint bands, and completeness when a family of bands **partitions**
the spectrum. Add the Hilbert-projection-theorem specialization: the band
projector's output is the closest point in its range to the input.

## Why this is cheaper than the original assessment rated it

`spectralProjector M hM c` (`Spectral.lean:271`) **already is** the
below-threshold half of this construction: it projects onto every
eigenvector with `eigvalOf ≤ c`. A two-sided band is the *difference* of
two existing `spectralProjector` calls:

```
bandProjector M hM a b := spectralProjector M hM b - spectralProjector M hM a
```

restricted conceptually to eigenvalues in `(a, b]`. This is not a
from-scratch construction — it is composition of an object already
delivered and QA'd, which is why this is rated cheaper than the original
outside assessment's "medium," and a clean instance of this repository's
own "reuse what's proved" discipline actually paying off.

## Design note — parameterize by interval, not index

Do not hard-code the construction to the low end (a "top-`k`" or
"bottom-`k`" projector). Parameterize the band by a spectral interval
`(a, b]`, with the below-threshold case falling out as `bandProjector M
hM (-∞) c` conceptually (or as `spectralProjector` directly, kept as the
named special case rather than re-derived). A construction that only
expresses low bands states strictly less and closes off the general
result. Bands that **partition** the spectrum (a finite, ordered sequence
of thresholds covering the full range) avoid the specific failure mode
where a gapped definition silently ignores every mode strictly between
two thresholds — the completeness theorem should be stated over a
partition, not assumed pairwise.

## Build order

### Step 1: The two-sided band projector and its basic properties

**DELIVERED 2026-08-20** (zero new axioms; `#print axioms` on all seven
new public theorems reads only `propext, Classical.choice,
Quot.sound`). The mandated pre-edit survey found the projector lemma
set already carries symmetry, idempotence, and the extreme-threshold
theorems — nothing reproved. **Route finding recorded before stating:**
idempotence of the *difference* does not transfer from idempotence of
each factor (differences of idempotents are not idempotent in
general); the load-bearing missing piece is the nestedness cross-law,
delivered in `GraphTheory.Spectral` as
`spectralProjector_mul_spectralProjector`
(`P_{c₁} * P_{c₂} = P_{min c₁ c₂}`, no order constraint; ordered
shapes `_of_le` / `_of_le'` for direct consumption, the flipped form
by transposing symmetry). The existing `spectralProjector_idempotent`
is **re-derived from the master law at unchanged statement** — its
50-line entrywise proof is now one rewrite. Alongside it, the complete
projector-eigenvector action description
`spectralProjector_mulVec_eigvecOf`
(`P_c *ᵥ vᵢ = if λᵢ ≤ c then vᵢ else 0`) with its `_self` / `_of_lt`
specializations — the bandpass-selection interface this proposal's
external consumer names. In the new `GraphTheory.Band`:
`bandProjector M hM a b := spectralProjector M hM b − spectralProjector M hM a`
(total definition, the `a > b` negated-band junk documented rather
than type-guarded; every property carries `a ≤ b` exactly where
needed), `bandProjector_symmetric`, `bandProjector_idempotent` (`a ≤ b`),
the action interface `bandProjector_mulVec_eigvecOf_self` /
`_eq_zero_left` / `_eq_zero_right`, the design note's named special
case `bandProjector_eq_spectralProjector_of_lt` (`spectralProjector`
kept, not re-derived), and the covering band `bandProjector_eq_one`
(the two-band instance of Step 3's completeness statement).
**QA** `SpectralGraph/Band_QA.lean` (27 declarations): the diagonal
fixture `!![1,0;0,3]` — one-dimensional eigenspaces force computable
eigenvector *directions* (`λ = 1 ⇒ v = ![±1,0]`, sign-independent
outer products) — with the spectrum `{1,3}` pinned from
trace+determinant independent of the machinery under test; the
projector at any threshold in `[1,3)` pinned to the hand-computed
outer product `e₀e₀ᵀ = !![1,0;0,0]`; band values computed
independently (`B(−1,2] = diag(1,0)`, `B(2,4] = diag(0,1)`,
`B(−1,4] = 1`, and the between-eigenvalues band `B(3/2,5/2] = 0` —
the gapped-definition guard this proposal's design note names);
idempotence both through the theorem and by raw literal
multiplication; the cross-law instantiated numerically in both orders;
and mode selection witnessed in both directions — the excluded mode
**annihilated and provably not fixed** (`B(2,4] *ᵥ v₁ = 0 ≠ v₁`, with
`v₁ ≠ 0` from unit norm; a definition silently keeping out-of-band
modes would fail this), the strictly-interior mode (`λ = 3 ∈ (2,4]`)
fixed, and the low-band action recomputed by raw arithmetic.
**Verification:** `lake env lean` on `Spectral`, `Band`, and `Band_QA`
(zero errors, zero warnings); `#print axioms` on seven public and nine
headline QA theorems (three standard axioms only); all thirty-four QA
modules batch-elaborated, zero errors; full `lake build` ✔; the lint /
citation / link checks pass; scoreboard 917/12/0.

Define `bandProjector M hM a b := spectralProjector M hM b -
spectralProjector M hM a` (for `a ≤ b`). Prove idempotence and
self-adjointness — both should transfer cheaply from
`spectralProjector_symmetric` and the existing idempotence argument for
`spectralProjector` itself (survey whether that idempotence lemma already
exists before reproving it). *(Survey outcome: the idempotence lemma
exists; the transfer needed the new nestedness cross-law, as recorded
above.)*

### Step 2: Orthogonality of disjoint bands

**DELIVERED 2026-08-20** (zero new axioms; count stays 11 after the
operator-directed `spectral_persistence` removal; `#print axioms` on all
four new public theorems reads only `propext, Classical.choice,
Quot.sound`). **Route as the Open-next-step section recorded:** the
cross-law's ordered forms expand `(P_b − P_a)(P_d − P_c)` to
`P_{min b d} − P_{min b c} − P_{min a d} + P_{min a c}`, which collapses
to `0` under the ordering — each product rewrites through
`spectralProjector_mul_spectralProjector_of_le` (forward order; the
flipped theorem through `_of_le'`), the residue being literally
`X − X`, closed by `sub_self`. Hypotheses folded to `a ≤ b`, `c ≤ d`,
`b ≤ c`: the `b ≤ c` line is *exactly* disjointness of the half-open
intervals `(a, b]` and `(c, d]`, so it is load-bearing rather than
decorative. Delivered in `GraphTheory.Band`:
`bandProjector_mul_bandProjector_eq_zero` (forward order),
`bandProjector_mul_bandProjector_eq_zero'` (flipped, direct
four-term expansion — not a transpose wrapper),
`bandProjector_inner_eq_zero` (the vector-level form:
`(B_{a,b} *ᵥ x) ⬝ᵥ (B_{c,d} *ᵥ y) = 0`, by moving the first band across
the dot product — `vecMul_transpose`, `dotProduct_mulVec`,
`vecMul_vecMul` — its symmetry making the transpose itself), and
`eq_zero_of_bandProjector_mulVec_eq_self` (the subspace-level reading
of the step's "they share no eigenvector": a vector fixed by two
disjoint bands is zero, since the second band annihilates the first
band's image). **QA** `Band_QA.lean` (+16, 43 in file): the disjoint
low/high bands' composition to zero checked through the theorem *and*
by raw literal multiplication on the pinned band values, in both
orders; image orthogonality on concrete vectors by both routes, with
the **same-band counter-witness** (`1 ≠ 0`) showing the vanishing is
about disjointness, not the fixture's zero entries; the composed action
annihilating a filtered signal by both routes; a low-band range vector
killed by the high band (the numeric companion of the shared-mode
theorem); and the **overlap guard** — bands `(−1, 3]` and `(1, 4]`
sharing the eigenvalue `3` compose to the provably nonzero `diag(0,1)`,
refuting the hypothesis-free form. **Verification:** `lake env lean` on
`Band` and `Band_QA` (zero errors, zero warnings); `#print axioms` on
all four public and twelve headline QA theorems (three standard axioms
only); the QA-module batch and full `lake build` per the scoreboard's
verification record; lint/citation/link checks pass; scoreboard
932/11/0.

For `a ≤ b ≤ c ≤ d`, prove `bandProjector M hM a b` and `bandProjector M
hM c d` project onto orthogonal subspaces (they share no eigenvector,
since the eigenbasis is orthonormal and the two eigenvalue ranges are
disjoint).

### Step 3: Completeness under a partition

**DELIVERED 2026-08-20** (zero new axioms; count stays 11;
`#print axioms` on all four new public theorems reads only `propext,
Classical.choice, Quot.sound`). **Route as the Open-next-step section
recorded:** the algebraic engine is an *unconditional* telescoping law
— `sum_range_bandProjector_eq_sub`: `∑_{k<n} B(t_k, t_{k+1}) =
P_{t_n} − P_{t_0}` for **any** threshold sequence `t : ℕ → ℝ`, ordered
or not, by `Finset.sum_range_succ` induction with the residue closed
by `abel` (load-bearing on the band definition's exact difference
shape — a sign-flipped or transposed definition would leave an
uncancellable residue; the QA witnesses this on a deliberately
non-monotone family whose junk band `−1` cancels the covering band
`1`). Completeness — `sum_range_bandProjector_eq_one` — then consumes
exactly the two endpoint covering hypotheses (`t₀` strictly below
every eigenvalue ⇒ `P_{t₀} = 0`; every eigenvalue `≤ tₙ` ⇒
`P_{tₙ} = 1`), both load-bearing: the QA endpoint guards refute the
hypothesis-free form in both directions (a family starting at `2`
drops the mode below it, a family truncated at `2` drops the mode
above it — the design note's "silently ignores a mode" failure mode).
**Statement-shape decision recorded before stating:** monotonicity of
the threshold family is deliberately *not* a hypothesis of the sum
identity (the telescoping law does not consume it — folding it in
would make it decorative, against the no-decorative-hypotheses
discipline); it is delivered as its own theorem
`bandProjector_mul_bandProjector_eq_zero_of_monotone`, where it is
exactly what is consumed — `Monotone t` supplies the interval
disjointness `t (k+1) ≤ t m` that Step 2's composition law takes — so
together with completeness the identity resolves into *mutually
orthogonal* band projectors: the partition character, stated rather
than assumed. The consumer's form
`sum_range_bandProjector_mulVec_eq_self` (`∑ B_k *ᵥ x = x` under the
same covering hypotheses — the frequency-band decomposition the
external consumer filters with) is proved through the inlined `mulVec`
analog of Mathlib's `Matrix.sum_mul` (sum-interchange; not present in
the pinned snapshot in that shape — `Finset.sum_apply` cannot see
through the `Matrix.of` wrapper, `Matrix.sum_apply` can).
**QA** `Band_QA.lean` (+41, 84 in file, 973 total): the partition
witness on the pinned fixture — the covering two-band family
`t k = 2k`, summed to the identity through the theorem *and* from
independently pinned band values; a three-band partition `t k = k`
whose middle band `(1,2]` is empty (zero-width member, value `0`)
and whose top threshold exactly touches the eigenvalue `3` (the
closed right endpoint exercised); the two **endpoint guards**, each
with its violated covering hypothesis separately proved violated at
the pinned spectrum; the **non-monotone telescoping witness** (both
sides of the law independently computed to `0` from pinned projectors
and band values); monotone-family orthogonality instantiated; and the
vector decomposition on a concrete signal by theorem and raw routes.
**Verification:** `lake env lean` on `Band` and `Band_QA` (zero
errors, zero warnings after two QA proof-shape fixes — the
`Finset.sum_range_succ` append-on-the-right shape and the `rw`-closes-
`3 ≤ 3`-by-itself linter trap, both recorded in the scoreboard's
provenance note); `#print axioms` on all four public and thirteen
headline QA theorems (three standard axioms only); the QA-module
batch and full `lake build` per the scoreboard's verification record;
lint/citation/link checks pass; scoreboard 973/11/0.

For a finite ordered sequence of thresholds `t₀ < t₁ < ... < tₙ` covering
the full spectrum's range, prove the sum of the resulting band projectors
equals the identity — the completeness statement the design note above
requires be stated over a partition, not pairwise. *(Delivered with the
recorded statement-shape sharpening: the sum identity itself needs only
the two covering endpoints because the telescoping law is unconditional;
the ordered/partition character is the separate monotone-family
orthogonality theorem, where monotonicity is load-bearing.)*

### Step 4: The Hilbert-projection-theorem specialization

**DELIVERED 2026-08-21 (zero new axioms; count stays 11; `#print
axioms` on all three new public theorems reads only `propext,
Classical.choice, Quot.sound`). The program is complete.** The
proposal's mandatory pre-step survey (exact lemma signatures) ran
against the pinned snapshot before any edit and found the whole shelf
present: `eq_orthogonalProjection_of_mem_of_inner_eq_zero`
(the identification lemma — membership plus `⟪u − v, w⟫ = 0` for every
`w ∈ K` forces `orthogonalProjection K u = v`),
`orthogonalProjection_minimal` (`‖u − proj_K u‖ = ⨅ c : K, ‖u − c‖`),
`HasOrthogonalProjection.ofCompleteSpace` (resolving on
finite-dimensional `EuclideanSpace` submodules), and the transport
spine — `EuclideanSpace.inner_piLp_equiv_symm` (`rfl` on this
snapshot) and `Matrix.toEuclideanLin_piLp_equiv_symm` (also `rfl`) —
the resolvent Step-0 record's `toEuclideanCLM` precedent, one
notation-level cleaner (`toEuclideanLin` needs no coercion). No
obstruction; the stop-and-record clause was not triggered.

**Delivered in `GraphTheory.Band`** (with the two Mathlib imports
`Analysis.InnerProductSpace.{Projection,PiL2}` added):

- `bandProjector_residual_dotProduct_eq_zero` — the engine:
  `(x − B *ᵥ x) ⬝ᵥ (B *ᵥ z) = 0`, load-bearing on exactly the two
  Step-1 facts (symmetry moves the band across the dot product;
  idempotence collapses `B *ᵥ (x − B *ᵥ x)` to `0`). No new machinery
  consumed — the whole Step-4 section reduces to Step 1 plus Mathlib.
- `bandProjector_toEuclidean_apply_eq_orthogonalProjection` — the
  identification: `orthogonalProjection (range (toEuclideanLin B))
  (e x) = e (B *ᵥ x)`, by `eq_orthogonalProjection_of_mem_of_inner_eq_zero`
  with membership via the transport (witness `e x` itself) and
  orthogonality via the engine (every range member is `e (B *ᵥ z')`).
- `norm_sub_bandProjector_apply_le` — the closest-point property: for
  every fixed point `y` of the band — equivalent to range membership
  by idempotence, and stated without an existential —
  `‖e x − e (B *ᵥ x)‖ ≤ ‖e x − e y‖`, from `orthogonalProjection_minimal`
  composed with the identification and `ciInf_le` (conditionally
  complete over ℝ; the `BddBelow` witness is `0` by norm
  nonnegativity).

**Statement-shape decision recorded before stating:** both
Euclidean-level statements are made at `EuclideanSpace ℝ V`, not at
the bare `V → ℝ` — the bare type's default norm instance is the sup
norm, and a closest-point claim there would be silently wrong-normed.
The fixed-point hypothesis form (`B *ᵥ y = y`) was chosen over the
range-membership existential deliberately (equivalent by idempotence;
no witness juggling for consumers).

**QA** `SpectralGraph/Band_QA.lean` (+25 by the generator metric, 109
in file, 998 total): the band `(0, 2] = diag(1,0)` pinned from the
pinned threshold projectors; the identification instantiated
(`orthogonalProjection` at the transported range of the packaged band
equals the packaged `![3, 0]`); the residual-orthogonality engine
witnessed **through the theorem and by raw literal arithmetic**
(`![0,4] ⬝ᵥ ![1,0] = 0`, both routes meeting at `0`); the
closest-point minimality instantiated at three competitors —
**attained** (the signal-to-projection distance is exactly `4`),
**strict over the zero signal** (`4 ≤ 5` — the 3-4-5 triangle), and
**generic over the whole range line** (`band_diag13_hilb_min_line`:
`4 ≤ ‖![3−t, 4]‖`, `_sqrt` form `4 ≤ √((3−t)²+16)`) — with
`band_diag13_hilb_min_line_raw` proving the *same* line inequality by
bare square-positivity (`4 = √16 ≤ √(16 + (3−t)²)` via
`Real.sqrt_le_sqrt`), an independent hand-check of closest-point on
the band's range line that the transported theorem's claim must
reproduce; the **high band** instantiated too (`3 ≤ 5` — the property
is not fixture-locked to the low band); and the **fixed-space guard**
(`band_diag13_hilb_guard`): the hypothesis-free form "the projection
beats every vector" is refuted at the unfiltered signal itself —
distance `0 < 4`, the signal provably not fixed by the band — so the
fixed-point hypothesis is load-bearing. Norm pins route through
`‖e v‖² = v ⬝ᵥ v` (the Resolvent QA idiom, restated locally) plus a
small nonnegative-square-pin helper. **Verification:** `lake env lean`
on `Band` and `Band_QA` — zero errors, zero warnings (public module
after two argument-shape fixes recorded in the scoreboard's
verification row: `LinearMap.mem_range` carries no explicit arguments
on this snapshot and `orthogonalProjection_minimal` takes its
submodule implicitly; `iInf_le` does not apply over ℝ — the
conditionally-complete `ciInf_le` with a `BddBelow` witness does);
`#print axioms` on the three public and nine headline QA theorems ✔
(three standard axioms only); oleans produced during iteration; **all
thirty-four QA modules batch-elaborated, zero errors (BATCH-DONE
fail=0)**; **full `lake build` ✔ (2186 targets, "Build completed
successfully", detached log + poll)**; `lint_axioms` (11),
`check_citations`, `check_markdown_links` pass; scoreboard
regeneration idempotent (**998/11/0**). Environment healthy at run
start (correct-path olean check: 5387 present, no fetch needed).

Prove `bandProjector M hM a b x` is the closest point in its range to
`x`, by instantiating Mathlib's Hilbert projection theorem
(`Analysis/InnerProductSpace/Projection.lean`) at the band's eigenspace,
survey the exact lemma signature first. *(Delivered as recorded above;
the survey found everything needed, the transport is the resolvent
Step-0 spine via `toEuclideanLin`, and the range form
`LinearMap.range (toEuclideanLin B)` was used rather than an
eigenspace-span form — for an idempotent self-adjoint band projector
they coincide, and the range form needs no extra agreement theorem.)*

## QA plan

- Positive witness: a small fixture with a known multi-eigenvalue
  spectrum (reuse an existing pinned-spectrum fixture from
  `CourantFischer_QA.lean` or `Variational_QA.lean`), the band projector
  computed at a concrete interval and checked against a hand-computed
  eigenvector sum.
- Partition witness: the completeness identity instantiated on the same
  fixture with a concrete partition, the sum checked to equal the
  identity matrix from independent computation.
- Negative witness: a band interval that excludes a mode strictly between
  its endpoints on a fixture with a tight eigenvalue gap, confirming the
  excluded mode is genuinely absent from the projector's range — guards
  the "silently ignores a mode" failure mode the design note names.

## Operating instructions for an autonomous run

- One step per run.
- **No new axioms.** Every step composes `spectralProjector` (already
  proved) with either elementary linear algebra or Mathlib's Hilbert
  projection theorem. If Step 4's instantiation needs machinery not on
  the shelf, stop and record the exact obstruction.
- Survey `spectralProjector`'s existing lemma set precisely before Step 1
  — reuse rather than reprove idempotence/symmetry if already available
  in a directly usable shape.

## Open next step

None — the program is complete (Step 4 delivered 2026-08-21; the
four-step build order ran one step per run: Steps 1–3 on 2026-08-20,
Step 4 on 2026-08-21). Named residual, not a step: the Step-4 range
form `LinearMap.range (toEuclideanLin B)` coincides with the
in-band-eigenspace span for the band projector (idempotent,
self-adjoint), but no explicit agreement theorem with
`Submodule.span` of the in-band eigenvectors was delivered — a
consumer needing the span *form* specifically would add it as its own
lemma.
