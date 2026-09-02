# Proposal: The Self-Contained Empirical PageRank Capstone

**Status:** COMPLETE — proposed and delivered in the same run
(`20260902T150123Z-run-1`), per the same-run pattern of
`empirical-lazy-stationary-sampling.md`. Zero new axioms (count stays
4): `#print axioms` via `wip/selfpr_axcheck.lean` on all 9 audited
declarations (1 shelf + 8 QA, the composed layers audited in place by
their own deliveries and re-checked here) reads exactly
`[propext, Classical.choice, Quot.sound]` — pure hard crust. QA
3734 → 3738.

Companion to [Strategy](../docs/1_STRATEGY.md), to
[cesaro-stationary-existence.md](cesaro-stationary-existence.md) (the
re-proof that made this composition honest — its "next handoff" named
this item first), to
[directed-uniform-mixing-time.md](directed-uniform-mixing-time.md)
(the worst-start capstone this composes), and to
[empirical-stationary-distribution-concentration.md](empirical-stationary-distribution-concentration.md)
(the sampling program this completes on the directed axis).

---

## Clean-room boundary

This planning document is internal prioritization and analysis. If
counsel approves a public repository export, restate the technical
specifications independently from standard textbook sources (PageRank
as the stationary distribution of the teleportation-regularized walk,
Doeblin/teleportation mixing rates, and Hoeffding-type concentration
of empirical frequencies are classical; see Sources below). Do not
copy this proposal verbatim.

## The obligation this discharges

`cesaro-stationary-existence.md`'s closing handoff names this exact
item first: *"a load-bearing consumer of the now-unconditional
stationary layer (the empirical PageRank capstone's `π` through the
proved `∃!` as a fully hard-crust composition)."*

### Why the capstone's `π` was a hypothesis at all

The delivered empirical PageRank capstones
(`empiricalPageRank_stationary_tail_of_depth`,
`empiricalPageRank_uniform_tail_of_depth`) take the target
distribution as caller hypotheses (`hπsum`, `hπstat`, and `hπnn` on
the uniform side). That was a forced design, not an oversight: until
2026-09-02 the only supplier — `existsUnique_pageRankVec` — was
conditional on the admitted `perron_frobenius`, so a "self-contained"
statement packaging the sampling guarantee *with* its produced target
would have been an axiom-mediated packaging pretending to be a
closing of the loop. The honest shape then was: caller supplies the
stationary vector, theorem supplies the guarantee.

The Cesàro stationary-existence delivery re-proved the whole
stationary layer (`exists_pageRankVec`, `existsUnique_pageRankVec`,
`pageRankVec_pos`) without the axiom. The composition this proposal
names is now hard crust end to end, and the self-contained statement
becomes honest: **the theorem itself hands the agent its target.**

## Statement design (recorded before stating)

One public theorem, `Derived/EmpiricalStationary.lean`'s
`PageRankLimit` section:

```
empiricalPageRank_tail_selfcontained_of_depth
  (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
  {α : ℝ} (hα : 0 < α) (hα' : α < 1) [Nonempty V]
  {ε : ℝ} (hε : 0 < ε) (i : V) {n : ℕ} (hn : n ≠ 0) :
  ∃ π : V → ℝ, (∀ j, 0 < π j) ∧ (∑ j, π j = 1) ∧
    (π ᵥ* googleMatrix A α = π) ∧
    ∀ (t₀ : ℕ), Nat.ceil (Real.log (2 / ε) / Real.log (1 / α)) ≤ t₀ →
      ∀ (x : V), [n trajectories of length t₀ from x estimate π i
        to ε at ≤ 2 exp (−n ε²/2)]
```

- **`∃ π`, not `∃! π`**: the extended predicate (certificate clauses
  plus guarantee) *is* unique in the mathematical sense — the
  certificate clauses alone already are, by the proved `∃!` — but the
  `∃!` packaging would invite the misreading that the *sampling data*
  determines `π`. Plain `∃` with the full certificate carried
  explicitly; the QA consumes the `∃!` where it does the work (the
  identification pin).
- **Certificate clauses in the strict form** (`0 < π j`, not
  `0 ≤ π j`): the supplier `exists_pageRankVec` produces strict
  positivity for free (power positivity), and the uniform capstone's
  `hπnn` is then `le_of_lt` — no information is dropped, and the
  statement pins the produced vector's shape exactly.
- **The threshold is the display ceiling at `ε/2`**:
  `⌈log(1/(ε/2))/log(1/α)⌉ = ⌈log(2/ε)/log(1/α)⌉`, the uniform
  α-ceiling's own display form (`pageRankMixingTime_le_of_rate'`,
  which folds the simplex diameter `d̄(0) ≤ 1` in). One
  start-independent, `π`-independent, computable-from-`(α, ε)`
  threshold — the display form is the right packaging precisely
  because the caller no longer holds `π` (the refined form's `d̄(0)`
  mentions it). Its slack against the exact uniform object is
  witnessed in QA (`2 < 3` on the fixture).
- **`0 < α` (strict), not `0 ≤ α`**: inherited from both composed
  layers (the display ceiling's `log (1/α)` and the capstone's
  hypothesis set). At `α = 0` the chain mixes in one step and the
  logarithm degenerates — the same honest window the depth-form rate
  theorem documents.
- **`hn : n ≠ 0` load-bearing**, exactly as in every sampler theorem
  on the shelf (the `n = 0` junk boundary is fenced in the Step-1 QA
  against the engine's own documented behavior).

## Corner analysis (Step 0, adversarial)

- *Empty type*: excluded by `[Nonempty V]` — without it no
  distribution exists (the `∃` would be false, not vacuous-true; the
  floor `(1 − α)·|V|⁻¹` degenerates at `card V = 0` to `0⁻¹`-junk).
- *`ε ≤ 0`*: excluded by `hε`. At `ε = 0` the threshold's `log 0`
  side is junk and the guarantee set is empty for a non-degenerate
  law — nothing claimed.
- *`α ∉ (0,1)`*: excluded by `hα`/`hα'`; the endpoint fences are
  already delivered in `PageRank_QA` (uniqueness dies at `α = 1` on
  reducible input and at `α = −1` by degeneration) — this theorem
  composes only on the open window.
- *Could the produced `π` be wrong?* The certificate clauses pin it
  exactly; the QA's identification pin proves any vector carrying
  them equals the hand-verified `u2` through the `∃!`'s uniqueness
  clause — the composition's falsification surface.
- *Is the threshold tight?* No — it is the Doeblin display bound
  (start-free `d̄(0) ≤ 1`), witnessed slackful in QA against the
  pinned exact uniform object. The sharp `|λ₂| = α` layer stays
  consumer-gated, unchanged.

## QA design

On `DirectedMixing_QA`'s Section-G/H fixture (the periodic 2-cycle's
Google matrix at `α = 1/2`, uniform stationary `u2`, the exact
uniform object pinned `t_mix^unif(1/8) = 2`):

1. **The identification pin** (`PR_selfcontained_vec_QA`): any vector
   carrying the theorem's three certificate clauses equals `u2` —
   through `existsUnique_pageRankVec`'s uniqueness clause against the
   hand-verified `u2` certificate. This is the load-bearing join to
   the re-proved stationary layer: if any certificate clause drifted,
   this proof fails to elaborate.
2. **The threshold pin** (`PR_selfcontained_threshold_QA`): the
   display threshold at `ε = 1/4` is exactly `⌈log 8/log 2⌉ = 3`
   (joining `PRU_display_ceiling_arith_QA` at `2/ε = 8 = 1/(1/8)`).
3. **The display-slack witness**
   (`PR_selfcontained_display_slack_QA`): the exact uniform object is
   `2 < 3` = the display threshold — the start-free packaging's price
   made visible on the fixture where the exact object is known.
4. **The fully-self-contained instance**
   (`PR_selfcontained_instance_QA`): the theorem instantiated at
   `ε = 1/4`, `n = 1`, `i = 1` — the produced vector identified as
   `u2` and the guarantee clause discharged at `t₀ = 3` for *every*
   start, closing at `2 exp(−1/32)`.

## Delivery record

DELIVERED as proposed, zero deviations from the statement design
above. The theorem is a five-line composition (supplier → ceiling →
capstone), which is the point: the whole loop is hard crust, so the
self-contained statement *should* be short — its weight is in what it
no longer asks the caller for. QA +4 (3734 → 3738), all four lemmas
as designed. Verification: spike first (`wip/selfpr_spike.lean`, the
theorem + full QA + the axiom audit, iterated to zero errors/zero
warnings before any shelf edit); `lake env lean` zero errors/zero
warnings on both touched modules; explicit `lake build` targets ✔;
`#print axioms` via `wip/selfpr_axcheck.lean` on the new theorem and
all 8 QA/supporting declarations — every one exactly
`propext, Classical.choice, Quot.sound`; full `lake build` ✔ +
`check_build_completeness.py` (133 files, 0 stale, 0 missing);
`lint_axioms` exit 0 (4 axioms, unchanged);
`check_refutation_independence` (9-tag clean — no tags touched);
`check_public_reachability` clean; `check_citations` clean;
`check_markdown_links` clean; `check_backlog_freshness` clean;
scoreboard regenerated (3738/4/0); map freshness exit 0 after the
3734 → 3738 sync in both map data files + SVG regeneration.

### Technique findings

1. `pageRankMixingTime_le_of_rate'` at `ε/2` speaks
   `log (1 / (ε/2))`, while the display packaging wants
   `log (2/ε)`; the join is a `field_simp`-proved
   `(2:ℝ)/ε = 1/(ε/2)` rewritten *backwards* into the goal
   (`rw [← hkey]`), not into the hypothesis — rewriting the goal
   keeps the composed ceiling's statement untouched for `exact`.
2. The `∃`-destructured guarantee clause binds `t₀` then `x`; the QA
   instance applies `hguar 3 _ x` with the threshold side condition
   discharged by `rw [PR_selfcontained_threshold_QA]` followed by
   `norm_num` — the `rw` leaves `3 ≤ 3` (not `rfl`-closed), so the
   trailing tactic is required.
3. `rw [hπu2] at h` (identifying the produced vector with the hand
   value inside the instance's measure statement) works because `π`
   occurs in exactly one position — the event's centering term; the
   `iidPMF` probability-certification arguments mention only the law,
   never `π`. Worth recording: keep supplier-produced opaque vectors
   out of the sampling-space arguments, or this rewrite pattern dies.
4. The `∃!`-supplier consumption pattern for the identification pin:
   `obtain ⟨π', -, huniq⟩ := existsUnique_pageRankVec ...` then
   `(huniq π ⟨...⟩).trans (huniq u2 ⟨...⟩).symm` — the anonymous
   constructor for the predicate's three clauses takes the *nonneg*
   form (`0 ≤`), so the theorem's strict `0 <` clauses enter through
   `le_of_lt`.

## Sources

The composition consumes only Scaffold-delivered hard crust
(`exists_pageRankVec`, `pageRankMixingTime_le_of_rate'`,
`empiricalPageRank_uniform_tail_of_depth`) whose own sources are
recorded in their modules and index entries (Page–Brin–Motwani–
Winograd 1999 for the teleportation construction; Levin–Peres–Wilmer
ch. 4–5 for the uniform mixing-time display bound; Hoeffding 1963
for the empirical-frequency tail). No new external result is relied
on; no citation surface changed.
