# The directed uniform (worst-start) mixing time

**Status:** COMPLETE — delivered 2026-09-02 (same-run proposal, run
`20260902T110117Z-run-1`, session `ses_f9e3e9a44ffe4KnUjXii6DPDXw`)
**Type:** Pure hard crust (zero new axioms; count stays 4)

## The gap

After `proposals/directed-mixing-time-object.md`, the `t_mix` object
family is complete at the per-start level across
plain/lazy/discrete/continuous/directed and carries one uniform
(worst-start) member — the undirected `walkMixingTime`. The directed
uniform twin is the family's one remaining gap, left consumer-gated by
two consecutive deliveries ("the directed uniform twin … each still
gated on a named consumer"). On the directed axis the gate is not a
formality: the undirected uniform object's submultiplicativity class
was proved through a bespoke walk-matrix contraction living in the
undirected mixing stack, which the directed layer deliberately does
not import.

## Why this run, and the gate discharge

`proposals/README.md`'s Active table held only Low rows (all blocked
on human decisions), so the center-out policy governed; the standing
handoff named three natural frontiers and this is the third.

The consumer gate discharges the same way the undirected uniform
object's did — two halves that consume each other:

1. **The uniform object's consumer is the submultiplicativity /
   ε-escalation class.** `d(s+t) ≤ d(s)d(t)`, `d̄(s+t) ≤ d̄(s)d(t)`,
   and "one certified evaluation time yields every ε-level mixing
   time" are worst-start statements, unstatable per-start: what
   iterates is the worst start's certificate.
2. **The escalation's consumer plus the named empirical capstone is
   the worst-start sampling guarantee**: `empiricalPageRank_uniform_tail_of_depth`
   — past *one* start-independent threshold, `n` simulated
   random-surfer trajectories estimate `π i` to `ε` at
   `2 exp(−nε²/2)` for **every** start `x` simultaneously. The
   per-start capstone needs a per-start threshold; an agent that
   cannot control or does not know the surfer's start vertex gets a
   single certificate. On directed input the entire symmetric
   `evals`/`eigvecOf` toolkit is unavailable, so this uniform Doeblin
   certificate is the only route the sampling program consumes there.

## Statement design (pinned before Lean)

- **The generic engine goes in `Mixing.lean`, matrix-level and
  sign-free**, not bespoke in the directed module:
  `tvDobrushinCoeff Q := max_{x,y} TV(Q_x, Q_y)` (rows as vectors, no
  `Pi.single` plumbing), the sharp contraction
  `TV(μ ᵥ* Q, ν ᵥ* Q) ≤ TV(μ, ν) · δ(Q)` at equal masses only, and
  `δ(Q^(s+t)) ≤ δ(Q^s)·δ(Q^t)` at row stochasticity. This is the
  mechanism the undirected delivery proved at `(Pᵀ)^t` — promoted to
  the matrix level it is consumable by every chain on the shelf
  (undirected, lazy, directed, any row action), and the undirected
  `walkTVPair` family is a candidate future join (not touched here:
  no existing public statement changes).
- **The pairing core `abs_sum_mul_le_of_pairwise` is promoted** from
  `Oversmoothing.lean`-private to a public `Mixing.lean` member —
  that module's own docstring anticipated promoting it "to a shared
  home if a third consumer appears"; this is the second consumer, and
  `Oversmoothing.lean` (already importing `Mixing`) keeps working
  against the promoted copy with its private original deleted.
- **The Google-law layer** (`DirectedMixing.lean`) follows LPW's
  objects: `pageRankTVPair A α t` (LPW's `d(t)`) defined in the law
  form mirroring `walkTVPair`, joined to the engine by
  `pageRankTVPair_eq_tvDobrushinCoeff`; `pageRankTVUniform A α π t`
  (`d̄(t)`) at the given-`π` design of the rate theorem; the law
  evolution `pageRankDistribution_add`; the Google contraction
  instance; `d`-submultiplicativity; `d̄ ≤ d` **by the contraction at
  the pair `(δ_x, π)` plus the simplex diameter** — no stationary
  mixture identity, no TV convexity lemma, no reversibility:
  hypothesis-lighter than the undirected twin's route through those
  two private Oversmoothing lemmas; the mixed form and escalation
  engine iterated from it; TV monotonicity in time
  (`pageRankDistribution_tvDistance_anti`, the Doeblin rate at the
  residual exponent through the law evolution).
- **The object** `pageRankMixingTime A α π ε` at LPW's `∀ s ≥ t, ∀ x`
  reading, with `_bddBelow`/`_le_of_cert`/`_spec` (well-ordered
  attainment), the witness-load-bearing per-start domination
  (`pageRankMixingTimeFrom_le_pageRankMixingTime` — the un-witnessed
  statement has no reason to hold at the `sInf ∅ = 0` junk corner,
  mirroring the undirected twin), the sup interchange
  (`_eq_sup_pageRankMixingTimeFrom`), and:
  - **the refined α-ceiling** `t_mix(ε) ≤
    ⌈log(d̄(0)/ε)/log(1/α)⌉` at the worst-start constant
    `d̄(0) = max_x TV(δ_x, π)` — the per-start ceiling's uniform
    twin, **attained exactly** on the fixture where the per-start one
    is (QA below);
  - **the display form** `t_mix(ε) ≤ ⌈log(1/ε)/log(1/α)⌉` at a
    nonnegative mass-one `π` (the simplex diameter folded in), and
    **the well-posedness supplier**
    `exists_pageRankMixingTime_witness` (every `ε` reachable from
    every start simultaneously on the teleportation window) — the
    existence half of the object's specification and the capstone's
    witness;
  - **the ε-escalation corollaries** (`≤ (k+1)·t₀` at `ε₀ρᵏ ≤ ε`, and
    the ⌈log⌉ display), consuming TV monotonicity for the leftover
    steps exactly as the undirected one does.

### Corner analysis (the §5 floor, applied)

- **Degenerate cardinality:** every statement is per-finite-type;
  `[Nonempty V]` appears only where a `sup'` needs a witness
  (`pageRankTVPair`, `pageRankTVUniform`) — the α-ceilings and the
  escalation need none beyond the engine's own. At `card V = 1`:
  `d(t) = d̄(t) = 0`, the uniform object is `0` at every `ε > 0`, and
  the refined ceiling degenerates honestly (`d̄(0) = 0`, the calculus
  twin's `C = 0` branch closing trivially).
- **`ε = 0` junk corner:** the witness set is empty when TV is
  eventually positive (the periodic fixture: `TV_s = (1/2)^{s+1} >
  0` at every `s`), so the object reads `sInf ∅ = 0` — pinned and
  documented (`PRU_tmix_zero_junk_QA`), mirroring the per-start
  fence.
- **Witness-load-bearing domination:** `From_le_ uniform` carries the
  uniform-witness hypothesis; on Google chains the α-ceiling supplies
  one unconditionally, and no theorem instantiates without one.
- **Strictness:** the ceilings' `0 < α` is honest (at `α = 0` the
  chain mixes in one step and the logarithm degenerates); the
  escalation's `0 < ρ < 1` mirrors LPW's.
- **No axiom contact:** everything consumes proved statements
  (`pageRank_tvDistance_le`, the Doeblin engine, the TV toolkit) —
  verified mechanically below.

## Delivery record

**The shelf.** `Mixing.lean` (the TV toolkit's new Dobrushin section):
the promoted **`abs_sum_mul_le_of_pairwise`** (public; the private
Oversmoothing original deleted), **`tvDobrushinCoeff`** +
`_nonneg`, **`tvDistance_vecMul_le_tvDobrushinCoeff`** (the sharp
matrix-level contraction, equal masses only), and
**`tvDobrushinCoeff_pow_add_le`** (generic power submultiplicativity
at row stochasticity). `DirectedMixing.lean` (the new directed
uniform-mixing-time section): `pageRankDistribution_eq_row`,
`pageRankDistribution_add`, **`pageRankTVPair`** (LPW's `d`) +
`_nonneg` + **the engine join** `_eq_tvDobrushinCoeff`,
**`tvDistance_vecMul_pow_googleMatrix_le`** (the Google contraction
instance), **`pageRankTVPair_submul`**, `piSingle_nonneg`,
**`pageRankTVUniform`** (LPW's `d̄`) + `_nonneg`, **`pageRankTVUniform_le_pageRankTVPair`**
(`d̄ ≤ d` by the contraction at `(δ_x, π)` + the simplex diameter),
**`pageRankDistribution_tvDistance_anti`** (discrete TV monotonicity),
**`pageRankTVUniform_mul_pageRankTVPair_le`** (`d̄(s+t) ≤ d̄(s)d(t)`),
**`pageRankTVUniform_succ_mul_le`** (the escalation engine), **`pageRankMixingTime`**
(the uniform object) with `_bddBelow`/`_le_of_cert`/`_spec`/
`pageRankMixingTimeFrom_le_pageRankMixingTime` (witness-load-bearing)/
`_eq_sup_pageRankMixingTimeFrom`, the private ceiling certificate
`pageRank_ceiling_cert`, **`exists_pageRankMixingTime_witness`**,
**`pageRankMixingTime_le_of_rate`** (the refined α-ceiling at `d̄(0)`),
**`pageRankMixingTime_le_of_rate'`** (the display form), and
**`pageRankMixingTime_le_mul_of_escalation`** /
**`_le_of_escalation`** (LPW's ε-escalation at the Google law).
`Derived/EmpiricalStationary.lean`: **`empiricalPageRank_uniform_tail_of_depth`**
— the worst-start capstone, composed from the uniform object's `_spec`
+ the witness supplier + the delivered per-start capstone (the
per-start domination supplying each start's threshold from the one
uniform certificate).

**The QA** (`DirectedMixing_QA.lean`'s Section H, +28, and
`EmpiricalStationary_QA.lean`'s uniform capstone instance, +1): on the
periodic 2-cycle Google fixture, against Section F/G's closed forms —

- **the exact closed form `d(t) = (1/2)^t`** from raw law literals
  (`PRU_pair_closed_QA`; the two rows are `u2 ± (1/2)(−1/2)^t•yd`),
  with **submultiplicativity attained with equality at every time**
  (`PRU_pair_submul_attained_QA`: `(1/2)^{s+t} = (1/2)^s(1/2)^t`);
- **the Dobrushin contraction attained exactly** at the basis pair on
  one Google step (`PRU_contraction_attained_QA`:
  `TV(e0 ᵥ* G, e1 ᵥ* G) = 1/2 = TV(e0, e1)·δ(G)`, both sides
  independently pinned — the new matrix-level engine's sharp constant
  load-bearing on the directed axis);
- **the worst-start closed form `d̄(t) = (1/2)^{t+1}`** with
  `d̄ = d/2` pinned exactly beside the domination theorem instance
  (`PRU_uniform_le_pair_QA`);
- **the mixed submultiplicativity attained with equality at every
  time** (`PRU_uniform_submul_attained_QA`);
- **the uniform object `t_mix^unif(1/8) = 2` pinned in both
  directions** through the sup interchange, both starts pinned `2`
  independently (`PR_tmix_one_eighth_QA` the new start-`1` twin,
  `PRU_tmix_eighth_QA`);
- **the refined α-ceiling attained exactly** (`PRU_tmix_ceiling_attained_QA`:
  `⌈log((1/2)/(1/8))/log 2⌉ = ⌈2⌉ = 2` = the object) with **the
  display form's slack witnessed** (`2 < ⌈log 8/log 2⌉ = 3` — the
  simplex diameter costs exactly the factor the refined form saves
  on this fixture);
- **the escalation corollary attained exactly**
  (`PRU_escalation_attained_QA`: with `t₀ = 2` certified at the
  fixture's own pinned distances `d̄(2) = 1/8`, `d(2) = 1/4`, the
  corollary reads `t_mix(1/32) ≤ (1+1)·2 = 4` and the truth — pinned
  in both directions (`PRU_tmix_thirtysecond_QA`) — is exactly `4`);
- **the `ε = 0` junk corner fenced** (`PRU_tmix_zero_junk_QA`);
- **the worst-start capstone instance** at `2 exp(−1/32)`,
  instantiated at the start `x = 1` — the same uniform threshold pin
  certifying the start whose per-start pin it subsumes.

**Verification:** spiked to zero errors/zero warnings in
`wip/unifdtv_spike.lean` (shelf + full QA + axiom audit) before any
shelf edit; `lake env lean` zero errors/zero warnings on all five
touched modules (`Mixing.lean`, `Oversmoothing.lean` after the
promotion, `DirectedMixing.lean`, `Derived/EmpiricalStationary.lean`,
both QA modules); explicit `lake build` targets ✔; **`#print axioms`
via `wip/unifdtv_axcheck.lean` on all 56 audited declarations (25
shelf + 31 QA): every one exactly `propext, Classical.choice,
Quot.sound`**; **full `lake build` ✔ immediately followed by
`check_build_completeness.py` — 133 source files, 133 fresh
artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` exit 0 (4
current axioms, unchanged; only the allowlisted-confirmed PF finding);
`check_refutation_independence` (9-tag clean — no tags added, nothing
touches an axiom); `check_public_reachability` clean (63 repo
modules); `check_citations` ("All axioms have proper citations!");
`check_markdown_links` clean; `check_backlog_freshness` clean;
scoreboard regenerated (**3712/4/0**); map-freshness exit 0 after the
3683 → 3712 stats sync in both map files and SVG regeneration (no
station — no tier change).

## Technique findings (for the next run)

1. **`rw` cannot act inside an un-beta-reduced `sup'` goal.**
   `refine Finset.sup'_le … fun p _ => ?_` leaves the goal as the
   beta-redex `(fun p => f p) p ≤ C`; `calc`/`exact` close it by
   defeq, but `rw` needs the pattern syntactically — open with
   `show f p ≤ C` first. (The Oversmoothing originals avoided this by
   using `calc` throughout.)
2. **Higher-order unification fails silently against bare vectors.**
   Applying the contraction with `_ _` for `μ ν` when the goal's right
   argument is a *bare* `π` (not `π ᵥ* M`) leaves `?ν ᵥ* M =?= π`
   unassignable; the reported error is a misleading "failed to
   synthesize Nonempty V". Restructure the calc step to state the
   evolved pair `(π ᵥ* M)` and pass `μ ν` explicitly.
3. **`omit [DecidableEq V] in` must precede the docstring** — between
   a docstring and its theorem it is a parse error ("unexpected token
   'omit'; expected 'lemma'").
4. **Private declarations are module-scoped** (re-confirmed): a spike
   re-declaring a module's to-be-extended section needs a local copy
   of that module's private helpers; at landing the new section sits
   in the module and the original is in scope.
5. **`rw` of a numeric closed form can close the goal by `rfl`**
   (`4 = (1+1)*2`), making subsequent tactics error "no goals" —
   state attainment QA as a conjunction (the truth value and the
   theorem's bound separately).
6. **`pow_succ'` vs `pow_succ`**: the two `rw`-lemmas carry opposite
   multiplication orders (`a^(n+1) = a·a^n` vs `a^n·a`); the
   `mul_comm` residue decides which one a rewrite can find.
7. **`(Finset.univ : Finset 2)` elaborates `2` at type level**
   (error: `OfNat (Type ?u) 2`) — the intended annotation is
   `Finset (Fin 2)`.

## Honest scope

- The α-ceiling is the Doeblin bound: attained exactly on the fixture
  (and the refined uniform form is tight there), but no sharpness
  *theorem* for general primitive chains is delivered — the sharp
  `|λ₂| = α` layer (Haveliwala–Kamvar) stays gated exactly as before,
  now the directed-rate program's only remaining item.
- The undirected `walkTVPair` family is *not* refactored onto the new
  matrix-level engine (no existing public statement or proof was
  touched); the join `walkTVPair A t = tvDobrushinCoeff
  ((walkTransitionMatrix A)^t)` is a priced follow-on if a consumer
  names it.
- The escalation class's constants are chain-certified (`ε₀`, `ρ`
  from one evaluation time), not spectral — that is LPW's design, and
  the Google instance's closed form comes from the α-rate instead.
