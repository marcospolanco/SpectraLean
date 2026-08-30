# Retire `hoeffding_lemma` by the Pointwise-Collapse Route

**Status:** COMPLETE (delivered 2026-08-30, run `20260830T165957Z-run-1`)
**Type:** Trust-surface reduction (priority item 4) — an honest axiom
retired by local proof, no Errata entry (the statement was never false
in its repaired shape)

## Summary

`hoeffding_lemma` — the last scalar concentration axiom and the last
zero-consumer axiom — was retired from admitted axiom to proved theorem
at its **unchanged public statement** (probability measure, bounded
`|X ω| ≤ a`, mean zero, conclusion `subgaussianNorm X μ ≤ √6 · a`),
axioms 6 → 5. The retirement closes both gaps in one slice: after it,
**every remaining admitted axiom** (`perron_frobenius`,
`primitive_power_tendsto`, `matrix_hoeffding`, `matrix_bernstein`,
`matrix_azuma_hoeffding`) **has a theorem consumer**, and the scalar
concentration subtree is axiom-free end to end.

## The Step-0 finding: the pointwise collapse

The retirement route is elementary, and the reason it is elementary is
itself the finding. `subgaussianNorm`'s defining set is

```lean
{K : ℝ | 0 < K ∧ ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ ≤ 2}
```

and this set **cannot see the mean of `X`** — only the bound
`|X ω| ≤ a` and the mass of `μ`. Pointwise,

```text
exp (X ω² · log 2 / a²) ≤ exp (log 2) = 2
```

puts `K = a/√(log 2)` in the defining set on any probability measure,
giving the sharper companion with **no mean-zero hypothesis, no
measurability hypothesis, and no numeric pins**:

```lean
theorem subgaussianNorm_le_of_bounded [IsProbabilityMeasure μ]
    (ha : 0 ≤ a) (h_bound : ∀ ω, |X ω| ≤ a) :
    subgaussianNorm X μ ≤ a / Real.sqrt (Real.log 2)
```

(The integral step is `integral_mono_of_nonneg` against the constant
`2` — valid for any `X`; junk-zero integrals only shrink the left
side.) The retired shape follows: `1/√(log 2) ≤ √6` from
`Real.one_sub_inv_le_log_of_pos` at `x = 2` (`1/2 ≤ log 2`), scaled by
`a ≥ 0`.

**The honest content of the finding:** at the `√6 · a` constant, the
admitted statement never carried the λ-form content of its citation
(Vershynin Lemma 2.6.2). The 2026-08-28 repair chose `√6` from a
layer-cake derivation of the source's λ-form tail — a route that
genuinely needs mean-zero — but the *statement it landed on* is so
slack that boundedness alone proves it. This is the mirror image of the
"wrong constant" hazard class in `docs/2_ARCHITECTURE.md` §5: there the
constant was too strong to be true; here it is too weak to carry the
source. The source's actual content is proved independently as
`hoeffding_lemma_mgf` in `Hoeffding.lean` (retired from axiom
2026-08-30). The mean-zero hypothesis is retained in the retired
theorem purely for statement stability; the docstring and the
deliberate `set_option linter.unusedVariables false in` record that it
is unused.

## The sharpness of the companion

`a/√(log 2)` is the **exact** uniform constant over all bounded
variables, not a loose bound: the defining-set membership condition at
`|X| ≡ a` reads `exp (a²/K²) ≤ 2`, i.e. `K ≥ a/√(log 2)` with equality
admitted. Both directions are pinned in QA:

```lean
theorem rademacher_norm_eq_QA :
    subgaussianNorm rademacherX rademacherMeasure = 1 / Real.sqrt (Real.log 2)
```

(the upper side is the companion's defining membership — the moment
condition holds *with equality* at `K = 1/√(log 2)`; the lower side is
every member forced above it, `exp (1/K²) ≤ 2 → 1/K² ≤ log 2`). This
one pin simultaneously (a) proves the companion's constant attained,
(b) re-derives the 2026-08-28 refutation's lower-bound class
(`rademacher_norm_ge_QA : 6/5 ≤ norm`) two-sided — the three facts
`1.2 ≤ 1.2011… ≤ 1/√(log 2)` are provably consistent — and (c) is
load-bearing on the exact defining-set shape: a different moment
threshold or a dropped `0 < K` guard breaks it immediately.

## Degenerate-corner analysis (recorded before the statements landed)

- **`a = 0`:** the conclusion reads `subgaussianNorm ≤ 0`; `h_bound`
  forces `X ≡ 0` pointwise, every positive `K` is admissible
  (`∫ 1 = 1 ≤ 2`), and the squeeze
  (`subgaussianNorm_eq_zero_of_forall_eq_zero`, via `Real.sInf_le_iff`
  at `ε/2 ∈ S` for every `ε > 0`) gives exactly `0`. No junk division
  is touched — the corner never divides by `a`.
- **Non-measurable `X`:** the proof never requires measurability. If
  the integrand is not ae-strongly-measurable the Bochner integral is
  the junk `0` (`integral_undef`) and the membership condition holds
  a fortiori — the conclusion is an upper bound and both recorded junk
  mechanisms collapse the norm *downward*. This is the honest reason
  the axiom's missing measurability guard (noted in the 2026-08-28
  audit) was safe: the junk corners could never falsify this
  particular statement. The retirement makes that argument a proof.
- **Mass guard:** the probability-measure instance is load-bearing for
  the companion exactly as it was for the admitted statement — at mass
  `M > 1` the members satisfy `M · exp (1/K²) ≤ 2`, i.e.
  `K ≥ 1/√(log (2/M))`, which exceeds `1/√(log 2)`. Refuted in QA at
  the mass-`19/10` fixture with the norm computed **exactly**:
  `1/√(log (20/19))`, attained.
- **Strictness corners:** no `≤`/`<` boundary is load-bearing anywhere:
  membership conditions are non-strict (`≤ 2`) and both the membership
  witnesses attain equality, so no strict-versus-closed trap exists.

## Delivered

1. **Shelf** (`Scaffold/Mathlib/Probability/Concentration/Scalar/Subgaussian.lean`):
   `subgaussianNorm_eq_zero_of_forall_eq_zero` (the corner),
   `subgaussianNorm_le_of_bounded` (the sharp companion),
   `hoeffding_lemma` (axiom → theorem, unchanged statement; docstring
   keeps the citation, the repair history, and adds the retirement
   record; module docstring updated).
2. **QA** (`Scaffold/QA/Concentration/Scalar_QA.lean`, +3, 3160 → 3163):
   `rademacher_norm_eq_QA` (the exact pin),
   `subgaussianNorm_le_of_bounded_uncentered_QA` (the uncentered
   witness — the companion at `X ≡ 1`, mean `1 ≠ 0`),
   `subgaussianNorm_le_of_bounded_guard_refuted_QA` (the companion's
   mass-guard fence). The pre-existing consumers
   (`subgaussian_norm_zero_QA`, `hoeffding_lemma_rademacher_QA`) now
   consume the theorem, strictly lighter, unchanged.
3. **Records:** scoreboard verification row + regeneration (3163/5/0),
   README (5 axioms / 3163 QA / the scalar-stack-axiom-free clause),
   radar (both rows synced, scores held per protocol), coverage map
   (the admitted-set paragraph), `index/map/probability_concentration.md`
   (the retired row + two companion rows), `index/sources/vershynin_hdp.md`
   (Lemma 2.6.2 row), `index/sources/wainwright_hds.md`,
   `index/load_bearing_axioms.md` (hoeffding_lemma and
   bernstein_inequality entries closed; the priority line repaired to
   the five remaining axioms), `Scalar/README.md` (fully de-staled to
   the proved state), map stamps 6 → 5 axioms / 3163 QA in both map
   files + regenerated SVG.

## Verification

- Spike first: `wip/hlretire_spike.lean` iterated to zero errors before
  any shelf edit (the only residue the dead `h_mean` warning, silenced
  deliberately on the shelf with the documented `set_option ... in`).
- `lake env lean` zero errors on `Subgaussian.lean` (warnings: the one
  pre-existing HEAD note only) and on `Scalar_QA.lean` (warning multiset
  identical to the working-tree baseline by file-pair elaboration; the
  +2 vs git-HEAD are the Bernstein run's recorded pair, outside this
  section).
- Explicit `lake build` targets ✔ on
  `Scaffold.Mathlib.Probability.Concentration.Scalar.Subgaussian` and
  `Scaffold.QA.Concentration.Scalar_QA`.
- **`#print axioms` via `wip/hlretire_axcheck.lean` (11 declarations)**:
  the retired name, both companions, `subgaussian_tail_bound`, the
  three new QA declarations, and the four pre-existing consumers each
  exactly `propext, Classical.choice, Quot.sound` — hard crust, no
  axiom contact; blast radius zero.
- **Full `lake build` ✔ immediately followed by
  `check_build_completeness.py` — 129 source files, 129 fresh
  artifacts, 0 stale, 0 missing, exit 0.**
- `lint_axioms` (5; both PF findings allowlisted-confirmed),
  `check_citations`, `check_markdown_links` pass; scoreboard
  regenerated (**3163/5/0**); **map freshness exit 0** (45 stations;
  no proposal status header changed — this proposal has no station).

## Technique findings

- **`set_option ... in` placement:** a docstring *before*
  `set_option linter.unusedVariables false in` fails to parse
  ("unexpected token"); the modifier goes first, the docstring between
  it and the theorem — the same lesson the MatrixMDS repair recorded
  for `omit ... in`.
- **`rw` with a bare numeral pollutes:** rewriting
  `show (2:ℝ) = exp (log 2)` rewrites every `2` in the goal including
  the `2` inside `log 2` (producing `log (exp (log 2))`); `calc`
  steps with `Real.exp_log (by norm_num : (0:ℝ) < 2)` avoid the
  pattern everywhere.
- **`Real.exp_log` instantiates from its argument:** passing
  `h : 0 < log 2` yields `exp (log (log 2)) = log 2` — the positivity
  proof must be about the *inner* `x` (`0 < 2` / `0 < 20/19`).
- **`Real.sqrt_lt_sqrt` is an implication** in this pin
  (`0 ≤ a → a < b → √a < √b`), not an iff; `Real.sqrt_mul` takes the
  nonneg proof about the *first* factor explicitly.
- **nlinarith cannot square past a product atom:** deriving `1 ≤ √L·K`
  from `1 ≤ L·K²` needs the strict-monotonicity route
  (`by_contra` + `sq_lt_sq'` with `-1 < y` as its real first
  hypothesis), not nlinarith on the atoms.
- `Real.sInf_le_iff` (with `BddBelow` + `Nonempty` supplied) is the
  one-line squeeze for `sInf S ≤ 0` when every positive `ε/2` is a
  member — no Archimedean argument needed.

## Follow-ons

None owed. The remaining trust surface is the PF pair and the matrix
trio; the natural next frontier on the concentration side is the matrix
trio's own retirement route (the matrix MGF machinery — Lieb-class,
multi-run), for which the scalar pattern has now been proved three
times over.
