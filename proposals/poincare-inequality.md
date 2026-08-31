# Proposal: The Poincaré Inequality for the Combinatorial and Normalized Laplacians

**Status:** IN PROGRESS — proposed and (if all steps below land) delivered in
the same run (`20260831T161132Z-run-1`), per the same-run pattern of
`total-variation-mixing-conversion.md` and
`spectral-encoding-drift-pipeline.md`. Zero new axioms planned: every
statement below is a corollary of proved shelf engines.

Companion to [Strategy](../docs/1_STRATEGY.md), [SGT Radar](../docs/7_SGT_RADAR.md)
axis 3 (variational and functional methods), whose score line names
"Absent: Poincaré, log-Sobolev" — the axis's own definition names Poincaré
as one of its four content pillars — and to the mixing program
(`mixing-time-bound.md`), whose ℓ²(π) contraction is Poincaré in walk form.

---

## Clean-room boundary

This planning document is internal prioritization and analysis. If counsel
approves a public repository export, restate the technical specifications
independently from standard textbook sources on spectral graph theory (the
Poincaré inequality for graph Laplacians is classical; see Sources below).
Do not copy this proposal verbatim.

## The obligation this discharges

Radar axis 3 (variational and functional methods) has sat at 4.0 since the
Courant–Fischer delivery with the named absent pair "Poincaré, log-Sobolev"
— the functional-inequality half of the axis's charter ("Rayleigh/min–max
principles, Dirichlet forms, Poincaré and log-Sobolev inequalities"). Axis
3 and axis 1 are the two lowest actionable subject axes (4.0; axis 8 is
deliberately gated).

Poincaré-shaped facts already exist on the shelf only as *per-fixture QA
certificates*: `SpectralCertificates_QA.lean`'s C₄/C₆ Wirtinger pins and
`Expander_QA.lean`'s K₃ equality (used there to pin spectra). The general
inequality — variance controlled by Dirichlet energy at the spectral gap,
for *every* function on *every* graph in the shelf's hypothesis class — is
absent. This proposal delivers it in both the combinatorial and the
normalized (degree-weighted, π-measure) forms, plus its first cut-level
consumer.

### Named consumers

1. **The mixing program** (`GraphTheory.Mixing`): the delivered ℓ²(π)
   contraction `∑ π ((Pᵗ g))² ≤ r^{2t} ∑ π g²` under a hypothesis-shaped
   rate is Poincaré in walk form; the normalized statement here is the
   standing functional inequality that certification of `r` from `λ₂`
   composes with. The π-form is stated in the mixing program's own
   degree-weighted idiom (`∑ deg · (f − E_π f)²` against `fᵀLf`), so it
   composes with `stationaryVec` without any measure-theoretic wrapper.
2. **The heat-semigroup family** (`GraphTheory.Heat`): eigenmode decay is
   delivered; variance decay under `e^{-tL}` (`Var(f_t) ≤ e^{-2tλ₂}Var(f)`)
   is the natural priced follow-on this inequality feeds (named, not
   delivered here).
3. **A genuinely new cut-level statement** (delivered here): composing the
   combinatorial form with `Multiway.lean`'s indicator energy identity
   `quadForm_laplacian_partIndicator` gives the linear-in-λ₂ edge expansion
   bound `λ₂ · |S||V∖S|/|V| ≤ boundary A S` for *every* vertex set — a
   shape the Cheeger family does not carry (Cheeger's lower bound is
   quadratic in φ; this is linear in λ₂, set-by-set, no sweep, no median).
   This is also `Multiway.lean`'s indicator identity's first consumer
   outside its own module — load-bearing growth on a definition not yet
   stress-tested elsewhere.

### Step 0: statement design (settled before any Lean)

**Combinatorial form.** For symmetric nonnegative `A` with
`2 ≤ card V` and `0 < λ₂ := secondEval (laplacian A)`:

```
∀ f : V → ℝ,  ∑ i, (f i − (∑ j, f j)/|V|)²  ≤  quadForm (laplacian A) f / λ₂
```

Proof route: `secondEval_le_rayleigh` (the proved general-kernel Rayleigh
lower bound at `w = onesVec`) applied at the centered vector
`x = f − mean f • onesVec`, which is orthogonal to `onesVec` by the choice
of the mean, combined with the kernel invariance
`quadForm L (f − c • 1) = quadForm L f` (row sums zero). The division-free
engine form `λ₂ · ∑ (f − mean f)² ≤ quadForm L f` holds with *no*
positivity hypothesis on λ₂ at all (at `λ₂ = 0` it is vacuously true); the
division form is that plus `0 < λ₂`. Connectivity enters only as the route
to `0 < λ₂` (`lambda2_pos_of_connected`), through `lambda2_eq_secondEval`.

**Normalized (π) form.** For symmetric nonnegative `A` with positive
degrees, `2 ≤ card V`, and `0 < λ₂^sym := secondEval (normalizedLaplacian A)`:

```
∀ f,  ∑ i, deg i · (f i − (∑ j, deg j · f j)/(∑ j, deg j))²
        ≤  quadForm (laplacian A) f / λ₂^sym
```

Proof route: `secondEval_le_rayleigh_of_ker` at `M = L_sym` with kernel
witness `w = √D · 1` (`normalizedLaplacian_mulVec_degreeSqrt_onesVec`,
hypothesis-free beyond positive degrees) applied at
`x = √D ⊙ (f − E_π f)`, which is orthogonal to `w` by mass conservation;
the congruence `√D L_sym √D = laplacian A`
(`degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt`) converts the energy
`quadForm L_sym x` into `quadForm L f` (kernel shift invariance again).
Note the eigenvalue in the denominator is `L_sym`'s own second eigenvalue,
*not* a combinatorial one — the two are not scalar-related on irregular
graphs, which is exactly why this is a separate theorem and not a
corollary of the first.

**Edge-expansion corollary.** Instantiating the combinatorial form at
`f = partIndicator S` (Multiway's set indicator): the variance collapses
to `|S|·|V∖S|/|V|` and `quadForm L (partIndicator S) = boundary A S`
(delivered identity), giving

```
λ₂ · |S| · (|V| − |S|) / |V| ≤ boundary A S
```

for every `S : Finset V`, no hypothesis beyond the engine's.

### Degenerate corners (the §5 hazard classes, checked before stating)

- **`card V = 0/1`**: excluded by the engines' own `2 ≤ card V`. At
  `card V = 1` the division by `card V` in the mean is fine but the
  statement degenerates (variance identically `0`); the guard is the
  engines', not new.
- **`λ₂ = 0` (disconnected)**: the division form is *not* stateable — and
  the QA fence proves something stronger: on a disconnected fixture a
  positive-variance, zero-energy function exists, so **no finite constant**
  makes any Poincaré-shaped inequality true. The hypothesis `0 < λ₂` is
  not merely convenient; it is the exact boundary of the true region.
- **Division-by-zero junk in the mean**: at `card V ≥ 2` never fires; the
  normalized form's `∑ deg` denominator is guarded by positive degrees
  (empty or zero sum impossible).
- **No measures, no integrals** anywhere — the vector idiom throughout, so
  the junk-integral hazard class does not reach these statements.

## The Lean

**New module `Scaffold/Mathlib/GraphTheory/Poincare.lean`**
(umbrella-imported), planned declarations:

1. `poincare_variance_mul_le` — the division-free combinatorial engine
   form (no positivity hypothesis on λ₂);
2. `poincare_inequality` — the division form at `0 < λ₂`;
3. `poincare_inequality_of_connected` — the connected convenience twin;
4. `poincare_inequality_normalized` — the π/degree-weighted division form;
5. `poincare_inequality_normalized_of_connected` — its connected twin;
6. `spectral_gap_edge_expansion` — the indicator corollary.

**New QA file `Scaffold/QA/SpectralGraph/Poincare_QA.lean`**, planned
obligations (the repo's counted fixture family):

- **K₂ exact attainment**: at the Fiedler vector `f = (1,−1)`, both sides
  compute to `2` (`λ₂ = 2`, energy `4`) — the constant sharp, no smaller
  denominator constant possible;
- **P₃ exact attainment**: at `f = (1,0,−1)` (P₃'s Fiedler vector), both
  sides compute to `2` (`λ₂ = 1`, energy `2`);
- **K₃ normalized exact attainment**: at `f = (1,−1,0)` with
  `λ₂(L_sym) = 3/2` (pinned through `L_sym(K₃) = (1/2) • L(K₃)` and the
  scaling lemma, with `λ₂(L) = 3` pinned by the repo's established
  sandwich idiom), both sides compute to `4`;
- **wrong-constant refutation**: at the K₂ Fiedler vector the shape with
  `λ₂` replaced by `3` reads `2 ≤ 4/3` — refuted, so the attained constant
  is load-bearing, not slack;
- **the no-constant connectivity fence**: on the disconnected two-edge
  fixture, `f` = component indicator has variance `1 > 0` and energy
  exactly `0`, so *for every* `c : ℝ` the inequality
  `variance ≤ c * energy` is false — connectivity (equivalently `0 < λ₂`)
  is exactly the boundary of the true region, not a convenience;
- **edge-expansion instances**: K₂ at `S` a singleton
  (`2·1·1/2 = 1 = boundary`, attained) and K₃ at `S` a singleton
  (`3·1·2/3 = 2 = boundary`, attained) — both tight, both consuming
  Multiway's indicator identity;
- small supporting pins (the K₂/P₃/K₃ spectra and boundary values,
  reconstructed locally by the repo's established idioms).

## Acceptance criteria — all met

1. **Seven shelf declarations proved** (the six planned plus the
   centering-invariance helper `quadForm_laplacian_sub_const`, which
   both headline proofs consume), zero new axioms, `#print axioms`
   exactly `propext, Classical.choice, Quot.sound` on every audited
   declaration via `wip/poincare_axcheck.lean` (55 declarations).
2. **The QA obligations landed** — three exact-attainment pins (K₂, P₃,
   K₃-normalized), the wrong-constant refutation, the no-constant
   connectivity fence, and both edge-expansion instances attained with
   equality; `Scaffold/QA/SpectralGraph/Poincare_QA.lean`, +44 QA
   declarations (3338 → 3382).
3. **Full verification ladder passes**: `lake build` ✔ (2408/2409) +
   `check_build_completeness.py` (133 source files, 133 fresh
   artifacts, 0 stale, 0 missing, exit 0); `lint_axioms` exit 0 (5
   axioms, both PF findings allowlisted-confirmed — no axiom surface
   touched); `check_refutation_independence` (10 tagged, clean — no
   tags added); `check_public_reachability` clean (63 repo modules,
   the new module umbrella-imported); `check_citations` and
   `check_markdown_links` pass; scoreboard regenerated at
   **3382/5/0**; `check_scaffold_map_freshness` exit 0 after the
   3338 → 3382 stats sync in both map files and SVG regeneration (this
   proposal has no station).
4. **Radar axis 3 updated and re-scored 4.0 → 4.5**: Poincaré marked
   delivered in the evidence row, removed from the absent list
   (log-Sobolev remains the named gap, with its re-score trigger
   named); the stale "weakest axes" summary paragraph repaired to
   match the verified table (axis 5's 4.5 and axis 3's 4.5).

## Delivery record

**Statement design as planned, two design findings from the proving:**

- The division-free engine form `poincare_variance_mul_le` carries *no*
  λ₂-positivity hypothesis at all — at `λ₂ = 0` (disconnected input) it
  is vacuously true, and the QA no-constant fence proves this is the
  exact boundary: on the disconnected two-edge fixture no finite
  constant makes any Poincaré-shaped inequality true. The `0 < λ₂`
  hypothesis therefore sits only on the division form, where it is
  load-bearing, and connectivity enters only through the two
  `_of_connected` twins.
- The normalized form's proof needs the kernel *membership*
  `L_sym *ᵥ (√D·1) = 0` (hypothesis-free beyond positive degrees) but
  not the full kernel *characterization* — the iff is never opened.

**Technique findings (recorded so they are not re-derived):**

1. `rw` cannot consume `Finset.sum_congr rfl (fun …)` as an equation —
   elaboration sticks on a `Fintype` metavariable. Goal-directed forms
   (`apply`/`refine`), per-entry simp (`simp only [hxdef]` with a
   `∀ i` entry equation), or term-mode `have`s with fully concrete
   types all work.
2. `le_div_iff₀ hc : a ≤ b/c ↔ a*c ≤ b`: to *conclude* the division
   form use `.2`, and the supplied product must read `a * c` — a
   `mul_comm` bridge is needed when the engine form was stated in the
   other order. (`.1` is the analysis direction and was used only to
   *consume* division-form Rayleigh bounds.)
3. The pinned Mathlib's near-synonyms differ in shape:
   `Real.sqrt_mul_self (h) : √(x*x) = x` but
   `Real.mul_self_sqrt (h) : √x * √x = x`; collapsing `√d * √d` wants
   the latter. `neg_sub` is `-(a - b) = b - a` — `← neg_sub a b` is
   the usable direction. `Finset.sum_mul` is stated
   `(∑ f) * a = ∑ (f * a)`, so the `←` direction factors a
   constant-times-summand product.
4. Anonymous-constructor proofs of `A ∧ B ∧ <theorem-instance>` with
   `by`-blocks written directly in the *statement* elaborate badly
   (metavars leak; errors read "expected `Prop : Type`"). Named
   hypothesis lemmas (the repo's `edgeAdj_card := le_refl 2` idiom)
   plus separate instance-pin and value-pin theorems avoid the class
   entirely and read better.
5. `ite`s at literal `Fin` indices do not reduce under `norm_num` —
   `simp` (reduceIte) or explicit `if_pos/if_neg (by decide)` is
   needed; the expK3 literal-matrix energy-identity idiom
   (`simp only [Matrix.of_apply, Fin.sum_univ_three, cons_val_*]` +
   `ring`) ports cleanly to `Fin 2`/`Fin 4` with the vecHead/vecTail
   extensions.
6. `Real.sqrt_ne_zero'` is an iff (`√x ≠ 0 ↔ 0 < x`), so
   `.mpr (hd i)` yields the disequality directly.

**Radar:** axis 3 re-scored 4.0 → 4.5 (the axis's charter names
Poincaré as its functional-inequality pillar; a proved, composable
family with a new cut-level consumer, not packaging); the QA axis held
at 4.0 per protocol (its named gap, parametric/randomized QA,
untouched).

## Deferred (named, not queued)

- Log-Sobolev: the other named absent category; needs a consumer naming
  which entropy inequality it needs (the `InformationTheory.Entropy`
  module's Gibbs inequality is the natural composition point).
- Heat-variance decay `Var(e^{-tL}f) ≤ e^{−2tλ₂}Var(f)`: the heat-family
  consumer named above; ~~semigroup-plus-Poincaré route needs derivative
  machinery not priced here~~ — **delivered 2026-08-31** by
  `proposals/heat-variance-decay.md` (`heatKernel_variance_decay`), the
  derivative-machinery cost dissolved by the eigenbasis-contraction
  route; see that proposal for the delivery record.
- A `t_mix`-style packaged depth from the normalized form joined to the
  oversmoothing ceiling: consumer-gated on the TV proposal's own deferred
  `t_mix` object.

## Sources

The Poincaré inequality for graph Laplacians is classical; standard
references include Chung, *Spectral Graph Theory* (1997), §1.3 (the
normalized form, stated for connected graphs) and the variational
characterization of λ₂ in Levin–Peres–Wilmer, *Markov Chains and Mixing
Times* (2009), Chapter 12 (the π-form for reversible chains). No statement
is admitted on these citations — everything here is *proved* from the
shelf's delivered engines — so the citations are provenance for the
statement *shapes*, not trust boundaries. Page-level locators stay
unconfirmed per the standing locator rule until checked against a physical
copy.
