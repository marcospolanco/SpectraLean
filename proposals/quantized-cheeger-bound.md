# Proposal: A Quantized Cheeger Inequality

**Status:** **COMPLETE** (delivered 2026-09-07, run
`20260907T181653Z-run-1`, session
`ses_f82ef3914ffezcZvjOFblSpnJ1` — see the delivery record at the
end of this document). **The module's public surface is now fully
audited: the quantizer trio by the corner audit (run
`20260907T190059Z-run-1`), the two range bridges by the clause audit
(run `20260907T203339Z-run-1`, both records below) — `hnonneg` fenced
at both bridge spellings; the sandwich carries no new clause.**
Originally restated in pure-mathematics form
2026-09-07 from an external request relayed by the operator (not
tracked in this repository — see `.gitignore`); no operational,
product, or patent framing survives into this document, only the
underlying mathematical ask.

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

## Delivery record (2026-09-07)

**Delivered at the full designed scope — Steps 1–3 plus the QA plan's
fences, all in one run as the operating instructions priced.** The new
public module `Scaffold/Mathlib/GraphTheory/QuantizedCheeger.lean`
(registered in the umbrella, 64 public modules):

- **Step 1** — `Quantization.quantize` (the rescale-round-rescale
  definition, `noncomputable` through Mathlib's `round`),
  `Quantization.quantize_mul_step` (the bucket-midpoint fixed points,
  stated at every `k : ℤ` — stronger than the plan needed, since the
  identity carries no `k ≤ 2^b` bound), and
  `Quantization.abs_sub_quantize_le` (`|x − quantize b R x| ≤
  R / 2^(b+1)`, the route exactly as designed: factor `R/2^b` out,
  `abs_sub_round` at `x · 2^b/R`, fold `2^(b+1) = 2 · 2^b`).
- **Step 2** — `secondEval_regularNormalizedLaplacian_nonneg` (the
  floor, read off `evals` at the sorted second entry through
  `evals_mem_eigvalOf` + `quadForm_eigvecOf_self` at PSD-ness — the
  plan's "already on the shelf via its PSD-ness" was *derivable*, not
  packaged; this is its first standalone statement) and
  `secondEval_regularNormalizedLaplacian_le_two` (the cap
  transported through
  `normalizedLaplacian_eq_regularNormalizedLaplacian` +
  `secondEval_congr`, with the `0 < deg` clause discharged from
  `d`-regularity).
- **Step 3** — `quantized_cheeger_le` exactly as stated in this
  document, both conjuncts; pure `linarith`/`Real.le_sqrt` assembly
  over the two Cheeger theorems and the error bound.

**The Step-0 survey's one finding changed the file plan, not the
math:** the sandwich needs `Mixing.lean`'s range cap, but
`Mixing → Stationary → RandomWalk → Cheeger` is an import cycle, so
`Cheeger.lean` cannot host Steps 2–3. The pre-authorized "minimal
standalone file" branch applies; the graph-agnostic quantizer lives in
the nested `Quantization` namespace so a future non-Cheeger consumer
can find it without Cheeger's transitive weight.

QA: the new `Scaffold/QA/SpectralGraph/QuantizedCheeger_QA.lean`
(11 theorems), per this document's own QA plan: the tie pins
(`qcTie_b0` at `b = 0`: `quantize 0 2 1 = 2`, rounding UP at the
coarsest depth; `qcTie_b3` at `b = 3`: `quantize 3 2 (1/8) = 1/4`,
the boundary between the `0`- and `1/4`-buckets — the `round 2⁻¹ = 1`
tie-breaking made concrete at two depths), the **sharpness pin**
(`qcTie_b3_error_eq`: the error at the `b = 3` tie is EXACTLY the
bound `2/2⁴ = 1/8` — attained, not slack — with the theorem's own
instance `qcTie_b3_bound_QA` beside it), the **boundary-count fence**
(`qcBoundaryCount`: injectivity of the `Fin (2^b+1)` representative
family through `quantize_mul_step`, plus `qcBoundaryCount_b2`, the
`b = 2` card pin `5` on `[0, 4]`), and **the K₂ sandwich** at `b = 0`
(`1/2 ≤ φ ≤ √6`) and `b = 3` (`15/16 ≤ φ ≤ √(2(2 + 1/8))`),
numerically collapsed through the independently pinned
`edge_normLap_secondEval_eq_two_QA` and `edge_cheegerConstant`, with
`qcK2_quantize_eval` (the cap value exactly representable at every
depth) isolating the envelope's own arithmetic, and the tightening
witness `qcK2_tightening_QA` (`1/2 < 15/16 ≤ φ`), and **`qcK2_cap_via_bridge_QA` — the Step-2 cap bridge's own consumer, added when the delivery's first census pass caught the cap unconsumed** (the sandwich never proof-depends on its own range justification — the cap justifies the `R = 2` design choice): the transported bound instantiated at K₂, where the pinned spectrum shows it attained with equality, load-bearing on the transport itself. **Scope note
against the plan:** the sandwich pins run at K₂ only — the plan named
"path/cycle fixtures already carrying exact `secondEval` pins", but
the only exact `λ₂` pin in QA is K₂'s; path/cycle pins would first
need their own spectral pinning (priced below, not owed).

**Verification:** spike-first (`wip/qcheb_spike.lean`, green after
five fix rounds). Traps recorded: **`λ` is a reserved token** —
`hλ2` as an identifier is a parse error whose cascade surfaced two
theorems downstream; **a standalone numeric `have` defaults its
literals to ℕ** — `2 / 2^(b+1) = 1/2^b` elaborated as a `Nat`
statement (true there, but by truncation, not field algebra), making
every field tactic report "no progress" — the `(2:ℝ)` ascription is
load-bearing (a numerical-elaboration cousin of the §5 hazard-class
discipline: check the elaborated shape, not the apparent one);
`rw [h₁, h₂] at h₃ h₄` fails when each lemma matches only one
hypothesis (single-instantiation per call); an implicit `{R}` before
`hR : 0 < R` leaves `R` a metavariable at application time (the
quantizer API takes `R` explicit); `secondEval_congr`'s equality
direction (`.symm`); the `1/2^3` vs `1/8` display-normalization
bridge (`congr 1; norm_num`). Full ladder: **17-declaration axiom
audit via `wip/qcheb_axcheck.lean` — every one exactly `propext,
Classical.choice, Quot.sound`** (the 5 public theorems, the quantizer
def, all 11 QA theorems) — zero axiom contact; both landed modules
elaborate with zero output; explicit builds ✔; full `lake build` +
`check_build_completeness.py` — **138/138 fresh, 0 stale, 0 missing,
exit 0** (both new modules in the default target); `lint_axioms`
exit 0 (4 axioms unchanged); `check_refutation_independence`
(24-tag clean); `check_public_reachability` (64 modules);
`check_citations`; `check_markdown_links`; `check_qa_name_uniqueness`
(the new `qc*` names collision-free); `check_backlog_freshness` clean;
**consumption closure verified by the tool: the census re-run
(`wip/census_20260907_post19.txt`) shows exactly the 5 new public
theorems landing consumed — 1374 → 1379 value-consumed, never-touched
0 → 0, the inert set held at the zero the previous run closed it to
(the first pass caught the cap bridge `_le_two` inert;
`qcK2_cap_via_bridge_QA` closed it before any record was written)**;
scoreboard regenerated (**1376 → 1381 functional / 6803 → 6814 QA /
4 axioms / 0 sorries**) with the verification row; map freshness
exit 0 after the 1381/6814 sync in both map data tables + SVG
regeneration (49 stations, no status change — this proposal has no
map station); index coverage added (`index/map/spectral_graph.md`,
three rows).

**Honest scope and residue (priced, not owed):** `λ₂` alone, not
top-`k` (the scope decision above); the K₂ sandwich at one fixture at
two bit depths; the boundary-count fence at the representative family
with the concrete card pinned at `b = 2` only; tie behavior pinned at
positive inputs (the next run's corner audit CORRECTED this
delivery's aside that negative ties are "symmetric by design" —
Mathlib's `round` is half-up toward `+∞` (`round (−2⁻¹) = 0`), so
negative ties round toward zero; the docstrings were corrected and
the asymmetry pinned, see the follow-on audit below); a path/cycle
sandwich pin blocked on those fixtures lacking exact spectral pins;
a negative-input or floating-point-style relative-error quantizer not
asked for and not built.

### Follow-on delivered (2026-09-07, run `20260907T184945Z-run-1`)

The priced residue above — "path/cycle sandwich pins blocked on
exact spectral pins" — resolved by a better fixture than the priced
one: **the triangle**, whose normalized spectrum `{0, 3/2, 3/2}` was
already pinned by `Mixing_QA.lean`'s `tri_secondEval_QA` (eigenvalue
classification + trace, no new spectral proof needed) and whose
`λ₂ = 3/2` is **interior** — the first fixture where the quantizer
genuinely errs (K₂ sits at the a priori cap `λ₂ = 2`, exactly
representable at every depth, so its envelope slack never engaged).
+18 QA theorems in `QuantizedCheeger_QA.lean`'s new triangle section
(QA 6814 → 6832), zero axiom contact (18-declaration audit, all at
the standard three):

- the triangle's `cheegerConstant = 1` — a generic card-based cut
  enumeration (no literal-subset matching: card 1 or 2 by the
  complement-count split, card-2 cuts reduced to singletons through
  the shelf's `conductance_compl`), the conductance arithmetic
  independent of the sandwich;
- the spectrum bridge to the sandwich's operator spelling (the same
  `secondEval_congr` route as the delivered cap bridge);
- value pins `3/2 → 2 → 2 → 3/2` at `b = 0/1/2`;
- the sandwich instantiations `1/2 ≤ φ ≤ √6`, `3/4 ≤ φ ≤ √5`,
  `5/8 ≤ φ ≤ √(7/2)`;
- **the `b = 1` envelope-center phenomenon** — the tie's up-rounding
  cancels the budget exactly (`λ̃₂ − ε_Q = λ₂`), the quantized lower
  bound attaining the un-quantized easy-direction `λ₂/2 = 3/4`;
- the strictly tightening upper envelope `√6 > √5 > √(7/2)`;
- **the honest non-monotonicity of the lower envelope** (`3/4 > 5/8`)
  — a worst-case bound whose tightness oscillates with the
  quantization residual; the asymmetric pair's error propagation made
  concrete, pinned rather than smoothed.

Full ladder green (build + completeness 138/138; `lint_axioms` 4
unchanged; the 24-tag independence check; reachability 64; citations;
links; QA-name uniqueness `qcTri*`; backlog freshness; scoreboard
1381/6832/4/0 with the verification row; map freshness exit 0 after
the sync). Spike traps recorded in the scoreboard row, headline: an
unimported tactic (`interval_cases`) surfaces as a *parse* error
("expected command"), and `Finset.card_eq_one.mp (by omega)` leaves
the implicit set a metavariable. Remaining residue: path/cycle
sandwich pins (their `λ₂ = 1` is bucket-representable at every depth
— strictly less informative than the triangle); ~~negative-input ties
(symmetry of `round`'s away-from-zero design)~~ — **corrected by the
corner audit below: the design is half-up toward `+∞`, NOT symmetric
about zero; the negative tie is now pinned.**

### Corner audit delivered (2026-09-07, run `20260907T190059Z-run-1`)

The standing "delivered-but-unfenced surfaces" agenda applied to this
proposal's own module — the §5-style Step 0 the numerical layer
never had. Three findings, all closed in the same run:

1. **A real documentation defect, found and corrected.** This
   proposal's records and the module's first-draft docstrings claimed
   tie behavior "rounds away from zero". False: Mathlib's `round` is
   `⌊x + 1/2⌋` (half-up, toward `+∞`) — `round 2⁻¹ = 1` but
   `round (−2⁻¹) = 0` (`round_neg_two_inv`). Negative ties round
   toward zero. The docstrings (quantize's tie paragraph,
   `abs_sub_quantize_le`'s fence note), the QA header, the scoreboard
   row's honest-scope sentence, and both residue sentences above are
   corrected; the asymmetry is now PINNED (`qcTie_asymmetry_b3`:
   `+1/8 → 1/4` beside `−1/8 → 0` at `b = 3`), with sharpness at the
   negative tie (`qcNegTie_error_eq` — the bound attained at both
   tie polarities) and the theorem instance beside it
   (`qcNegTie_bound_QA`). No Lean statement was ever false — an
   Errata entry is not owed (the disposition record for materially
   false statements); the defect was prose mischaracterization.
2. **The `0 < R` clause of `abs_sub_quantize_le` is load-bearing and
   now fenced**: at the degenerate range the junk division
   `x · 2^b / 0 = 0` collapses the quantizer to the constant `0`
   (`qcZeroRange_quantize`), and the bound refutes at every `x ≠ 0` —
   the hypothesis-form fence `qcZeroRange_fence_QA`, generic in `b`.
3. **The `0 < R` clause of `quantize_mul_step` is truth-removable and
   removed**: at `R = 0` both sides evaluate to the junk zero, so the
   identity holds unconditionally — the public theorem is now stated
   without the hypothesis (a strengthening of the same run's
   uncommitted delivery; no consumer change beyond dropping the
   argument at two QA call sites).

+6 QA theorems (QA 6832 → 6838), the public signature strengthened,
zero axiom contact (6-declaration audit, all at the standard three).
Spike (`wip/qcfence_spike.lean`) green on the first round. Remaining
residue: negative-range (`R < 0`) behavior unpinned (outside the
quantizer's contract — a known positive range); the relative-error
quantizer still not asked for.

## Range-bridges clause-audit record (2026-09-07, run `20260907T203339Z-run-1`)

The standing "delivered-but-unfenced surfaces" agenda applied to this
delivery's remaining public surface: the corner audit (the record
above) covered the quantizer trio; the two range bridges delivered
beside them were never audited. The numerical layer is now fully
audited.

**Finding: `hnonneg` is load-bearing at both bridge spellings, and
every existing fence provably cannot cover them.** The PSD engine's
fence (`rcF_psd_hnn_fence_QA`) and the regular-Cheeger family's `hnn`
fences are all 2-vertex; a 2-vertex signed d-regular fixture has
`L_sym` spectrum exactly `{2w/d, 0}` — `secondEval = 0` — so both
bridges' dropped statements (`0 ≤ 0` and `0 ≤ 2`) are TRUE at every
2-vertex witness the existing fence class can supply. The refutation
needs the **multiplicity-2 phenomenon** (two Laplacian eigenvalues
crossing the degree to the same side — requiring ≥ 3 vertices), a
witness shape new to this audit family:

- **The floor fence** (`qcF_floor_hnn_fence_QA`): `A₋ = 2I − (1/3)J`
  — diag `5/3`, off-diag `−1/3`; symmetric, `deg ≡ 1`, `0 < 1`,
  `3 ≥ 2` vertices, `hnonneg` failing at the off-diagonal (isolation
  companion `qcF_floor_hnn_isolation_QA`). `spec(A₋) = {1, 2, 2}`
  (two A-eigenvalues above the degree), so
  `spec(L_sym) = {0, −1, −1}` and `secondEval = −1`: the dropped
  statement reads `0 ≤ −1`.
- **The cap fence** (`qcF_cap_hnn_fence_QA`): the mirror `A₊ = J − 2I`
  — diag `−1`, off-diag `1`; same hypothesis profile. `spec(A₊) =
  {1, −2, −2}` (two below), so `spec(L_sym) = {0, 3, 3}` and
  `secondEval = 3`: the dropped statement reads `3 ≤ 2`.

The spectra are pinned by the triangle's established idiom
(`tri_secondEval_QA`'s eigenvalue-cases + trace count + sortedness)
adapted to a sign-indefinite operator through the **coordinate-sum
eigen-equation trick**: entrywise the eigen equation reads
`μ·v j = (1/3)·(∑v) − v j` (floor) or `μ·v j = 3·v j − (∑v)` (cap);
summing over `j` collapses the constant term, giving `μ·(∑v) = 0`,
and the two cases each pin `μ` (`∑v = 0` forces the mode value by
nonvanoneness of the eigenvector — `eigvecOf_inner`'s unit norm;
`∑v ≠ 0` forces `μ = 0`). All consumed through row-form action
lemmas (`qcFloorAdj_rowsum`/`qcCapAdj_rowsum` +
`qcFloorL_mulVec_apply`/`qcCapL_mulVec_apply`) — the matrix is never
unfolded inside the eigen equation (the named-def vs literal atom
mismatch that defeats `ring`).

**Classifications, no fence owed:** `hdpos` has no failing fixture
with `hnonneg` genuine — degree-regular nonnegative forces `d ≥ 0`,
and `d = 0` forces `A = 0`, where the junk `0⁻¹ = 0` gives
`L_sym = 1` and both bridge values (`0 ≤ 1 ≤ 2`) hold benignly;
`hcard` and `hA` are structurally carried by the `secondEval`
spelling (unstatable without them); the sandwich `quantized_cheeger_le`
carries no NEW clause — its hypothesis set is exactly the Cheeger
pair's, already fenced by the regular-Cheeger fence audit
(`rcF_upper/lower_{hnn,hd,hdpos}_fence_QA`), and `b` is a free
parameter.

**Proof traps recorded** (spike `wip/qcbridge_spike.lean`, green
after six fix rounds; the landed section built first-round): the
Fin-3 index-`2` entry needs FULL `simp` — `cons_val_succ'` is a
default simp lemma, while a hand `simp only` list with the cons-val
names leaves `![a, b, c] 2` unreduced (Fin-2 work never meets this);
`Finset.mul_sum`'s direction in this snapshot is
`a * ∑ f = ∑ a * f`; the row-form action lemma is load-bearing for
the eigen pins; the `Fin (Fintype.card (Fin 3))` index type needs
tri's `hsum3` defeq cast before `Fin.sum_univ_three`; `inv_one` (not
`one_inv`); Fin monotonicity by `decide` (not `norm_num`).

**Verification:** full ladder green — `lake build` + completeness
138/138 fresh, 0 stale, 0 missing (one documented artifact-removal
remediation after `touch`-based diagnostics, plus one explicit-target
rebuild — the default umbrella target does not cover QA modules);
8-declaration axiom audit (`wip/qcbridge_axcheck.lean`: both fences,
both isolations, both cases lemmas, both secondEval pins) — every one
exactly `propext, Classical.choice, Quot.sound`; `lint_axioms` (4
unchanged), `check_refutation_independence` (24-tag),
`check_public_reachability` (64 modules), `check_citations`,
`check_markdown_links`, `check_qa_name_uniqueness`
(`qcFloor*`/`qcCap*`/`qcF_*` collision-free), `check_backlog_
freshness`; scoreboard 1380 / 6866 / 4 / 0 with the verification row;
map freshness exit 0 after the 6866 sync. No census re-run owed —
QA-only, no new shelf declaration, the inert set's zero stands.

**Residue update:** the quantizer's own residue (negative-range
behavior, the relative-error quantizer) is unchanged; the bridge
residue is now closed at the `hnonneg` clause (this record), with the
general mixed-sign regular-graph eigenvalue route (char-poly, beyond
the `I`/`J` combinations) priced not owed.
