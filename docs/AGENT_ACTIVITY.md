# Agent activity

This is an append-only, operator-facing journal of autonomous work. Entries
record intentions, material decisions, verification, and the next handoff;
they are summaries, not model transcripts.

## Required format for new entries

Use a heading and metadata block in this form. `run` is the wrapper invocation
identifier; `session` is the OpenCode session ID. Obtain the timestamp with
`date -u +%Y-%m-%dT%H:%M:%SZ` and inspect the session list before the terminal
entry. If a session ID cannot be established from repository evidence, write
`unavailable` rather than inventing one.

```markdown
## 2026-08-17T12:34:56Z — Short milestone title

**Run:** `20260817T123456Z-run-1`  
**Session:** `ses_…`  
**Status:** in-progress | completed | blocked | interrupted | superseded  
**Milestone:** One-sentence objective and SGT-leverage rationale.
```

Follow the metadata with concise `Changes`, `Verification`, `Remaining risk`,
and `Next handoff` paragraphs as applicable.

Since 2026-08-25, any entry claiming a verified full build must record
`python3 scripts/check_build_completeness.py` passing immediately after
the `lake build` it cites (see `proposals/verify-build-completeness.md`
for the incident that made this mandatory: a full build once printed
"Build completed successfully" over a three-error QA file).

Since 2026-08-28, any entry reporting a delivery that changes a
proposal's status header must also record
`python3 scripts/check_scaffold_map_freshness.py` passing (see
`proposals/verify-scaffold-map-freshness.md` for the stale-map incident
that made this mandatory: the pre-commit hook re-rendered the map on
every commit while its hand-maintained data tables drifted for days).

## 2026-08-29T15:58:56Z — The floor and sweep-cut admissibility dissolution: completing the window family

**Run:** `20260829T155521Z-run-1`  
**Session:** `ses_fb1c46bedffeAFT236lxoisIv7`  
**Status:** superseded by the completed entry below (this was the
in-progress record; the milestone was delivered the same run)  
**Milestone:** the previous delivery's own priced follow-on, selected
per priority item 0 (no High rows; the Medium-High
empirical-stationary Step 2 row consumer-gated; all Low rows
human-decision-gated): apply the delivered admissibility-dissolution
decomposition to the window family's two remaining conditional members
— `edgePerturbation_normalized_cheeger_floor` and
`edgePerturbation_fiedler_sweep_cut_tail` still carry their
`perturbAdmissible` conjuncts. Deliverable: the two unconditional
theorems (each the same "some deviation ≥ s, or all < s and then
admissible" union with the delivered transfer helper and all-vertices
degree tail; honestly two-axiom — `matrix_hoeffding` via the window
theorem, `hoeffding_inequality` via the degree tail), plus QA: the
all-false disconnectedness witness, the strict-containment witness
(the unconditional sweep event genuinely larger than the conditional
one), and the two closed-form instances. Pure composition outside the
two honestly-carried axioms; zero new axioms.

**Changes (planned):** `Scaffold/Derived/EdgePerturbationTail.lean`
(two theorems + section/header docstrings),
`Scaffold/QA/Derived/EdgePerturbation_QA.lean` (dissolution-completion
QA section). Records to follow: the degree-concentration proposal's
follow-on delivery record, `proposals/README.md`, README, radar,
scoreboard, index maps, map stamps, this plan, the activity log.

**Verification (planned):** spike to zero errors/warnings before any
shelf edit; `lake env lean` on the touched modules; explicit `lake
build` targets; `#print axioms` on the new declarations; full `lake
build` + `check_build_completeness.py`; `lint_axioms`,
`check_citations`, `check_markdown_links`; scoreboard regeneration and
map-freshness sync.

## 2026-08-29T16:11:10Z — The dissolution completion delivered: the window family unconditional throughout (terminal)

**Run:** `20260829T155521Z-run-1`  
**Session:** `ses_fb1c46bedffeAFT236lxoisIv7`  
**Status:** completed  
**Milestone:** the floor and swept-cut admissibility dissolution,
**delivered** — the previous run's decomposition applied to the window
family's two remaining conditional members, completing the family:
every measured event (floor, bracket, swept cut) now reads with **no
conditioning conjunct**, at the honest price of one degree-tail term.
Zero new axioms; the family's two-axiom shape (`matrix_hoeffding` +
`hoeffding_inequality`) now three members.

**Changes:** `Derived/EdgePerturbationTail.lean` (the
AdmissibilityDissolution section's completion): the delivered
`hsplit`/`measure_union_le`/`add_le_add` skeleton applied verbatim at
the two conditional theorems —
`edgePerturbation_normalized_cheeger_floor_unconditional` (`μ {λ₂(L_sym
G_ω) ≤ (dmin·φ²/2 − t)/dmax} ≤ window tail at t + degree tail at s`)
and `edgePerturbation_fiedler_sweep_cut_tail_unconditional` (the
capstone: the failure of "connected with a swept Fiedler cut at
`conductance² ≤ 2·(2·dmax·φ + t)/dmin`" bounded the same way, at the
same stack plus the floor-positivity guard); the entire new content is
the set-comprehension shapes. QA +5 (3003 → 3008, the
AdmissibilityDissolution completion subsection): the all-false
disconnectedness witness (kernel-constancy contrapositive at the zero
adjacency); the **strict-containment witness** (the all-false outcome
provably *in* the unconditional sweep bad event while provably *not*
admissible — the dissolution genuinely enlarged the measured event, the
degree-tail term its honest price; hard crust); the good-outcome
conjunction (`conductance² ≤ 4` inside the ceiling `81/4` — the bad
event not all of `Ω`); and the two closed-form instances (`4
exp(−1/4096) + 4 exp(−1/16)` each at `p ≡ 1/10`, window `[1/2, 5/2]`,
`s = 1/2`, `t = 1/16`). Records: the proposal's completion delivery
record (status line extended, follow-on list empty, the floor-guard
carried-over note), `proposals/README.md`, README (3008), the radar QA
axis (score held at 4.0 per protocol), the scoreboard (verification
row + interpretation bullet + the three script rows), the
probability-concentration index map (two rows), the map stamps +
regenerated SVG, the execution plan, this log.

**Verification:** spike first (`wip/dissolve2_spike.lean`, every piece
to zero errors/warnings before any shelf edit; one technique finding:
an anonymous-constructor `?_` under `exact` fails to leave its goal —
`refine` the fix); `lake env lean` zero errors on both touched modules
(the Derived module zero output; the QA module at its recorded
three-note `Try this: ring_nf` baseline, none added); explicit `lake
build` targets ✔ on `EdgePerturbationTail` (2229/2229) and
`EdgePerturbation_QA`; `#print axioms` via `wip/dissolve2_axcheck.lean`
exactly as designed (7 declarations: three hard-crust witnesses; two
theorems and two pins honestly carrying both axioms); **full `lake
build` ✔ (2405/2406) immediately followed by
`check_build_completeness.py` — 128 source files, 128 fresh artifacts,
0 stale, 0 missing, exit 0**; `lint_axioms` exit 0 (10, both findings
allowlisted-confirmed), `check_citations` pass, `check_markdown_links`
pass; scoreboard regenerated idempotent (**3008/10/0**); **map
freshness exit 0** after the stats-stamp sync (3003 → 3008 in both map
files; no proposal status header changed). Nothing committed; the
prior runs' deliveries preserved untouched.

**Remaining risk:** none owed by the delivery — the decomposition and
witnesses are unconditional hard crust. The two new Derived theorems
are conditional on `matrix_hoeffding` and `hoeffding_inequality`
together and must never be described as foundationally proved. The
sweep member's floor-positivity guard remains proof-load-bearing (its
C₄ dropped-guard refutation fixture carries over verbatim — the guard
is a hypothesis of both members); the pair condition and the
shrunk-window hypotheses remain genuine design/regularity prices.

**Next handoff:** the Active table's only actionable row remains the
empirical-stationary Step 2, still gated on a consumer pricing the
bias-term shape; otherwise the next load-bearing gap
`docs/6_SGT_BACKLOG.md` names (all remaining items consumer-gated) or
a consumer of the now-complete unconditional window family (none named
— the family's natural next frontier).

## 2026-08-29T14:28:12Z — The admissibility dissolution: the window family's first unconditional measured event

**Run:** `20260829T142812Z-run-1`  
**Session:** `ses_fb219d698ffe1iBdJS5qlFOmt6`  
**Status:** in-progress  
**Milestone:** the degree-concentration proposal's sole priced
follow-on, selected per priority item 0 (no High rows; the Medium-High
empirical-stationary Step 2 row consumer-gated; all Low rows
human-decision-gated) as the standing handoff's top priced follow-on,
now unblocked by the two prior runs' degree tails: union the
all-vertices degree tail with
`edgePerturbation_normalized_connectivity_bracket` to dissolve the
admissibility conjunct — the nonnegativity half derived from the pair
design condition `p e + p (e.2, e.1) ≤ 1` (exact at the uniform
`p ≡ ½`), the degree half from base degrees in a shrunk window
`[dmin + s, dmax − s]` plus `|dev| < s`. Deliverable: the public
engine lemma `perturbWeight_entry_nonneg` (WeightSpace section), the
transfer helper + the unconditional bracket theorem in the Derived
module (honestly conditional on `matrix_hoeffding` via the bracket and
`hoeffding_inequality` via the degree tail), and the QA section
(boundary entry pin, dropped-condition negative witness at `p ≡ 9/10`,
positive transfer witness at `p ≡ 1/10`, closed-form K₂ instance).
Pure hard crust outside the two honestly-carried axioms; zero new
axioms.

**Changes (planned):** `Scaffold/Mathlib/GraphTheory/EdgePerturbation.lean`
(nonnegativity engine), `Scaffold/Derived/EdgePerturbationTail.lean`
(transfer helper + unconditional bracket, new final section),
`Scaffold/QA/Derived/EdgePerturbation_QA.lean` (dissolution section).
Records to follow: the degree-concentration proposal's follow-on
delivery record, README count, radar QA axis, scoreboard, map stamps,
this plan, the activity log.

**Verification (planned):** spike to zero errors/warnings before any
shelf edit; `lake env lean` on the touched modules; explicit `lake
build` targets; `#print axioms` on the new declarations (engine and QA
hard crust at the standard three; the theorem honestly carrying both
axioms); full `lake build` + `check_build_completeness.py`;
`lint_axioms`, `check_citations`, `check_markdown_links`; scoreboard
regeneration and map-freshness sync.

## 2026-08-29T14:53:21Z — The admissibility dissolution delivered: the window family's first unconditional measured event (terminal)

**Run:** `20260829T142812Z-run-1`  
**Session:** `ses_fb219d698ffe1iBdJS5qlFOmt6`  
**Status:** completed  
**Milestone:** the degree-concentration proposal's sole priced
follow-on, **delivered** — `perturbAdmissible` no longer hypothesized
but *derived*: the nonnegativity half from the pair design condition
`p e + p (e.2, e.1) ≤ 1` (the public engine
`perturbWeight_entry_nonneg`), the degree half from base degrees in the
shrunk window `[dmin + s, dmax − s]` plus the delivered all-vertices
degree tail (the transfer helper), giving the window family's first
measured event with **no admissibility conjunct** — the recorded
honesty note dissolved on its degree half. Zero new axioms; the
family's first deliberate two-axiom member.

**Changes:** `EdgePerturbation.lean` (WeightSpace section): the public
engine `perturbWeight_entry_nonneg` — off-diagonal
`A i j · (1 + δ_{ij} + δ_{ji} − p_{ij} − p_{ji})` by symmetry,
diagonal `A i i · (1 + δ_{ii} − p_{ii})`, no `hp0` clause needed —
plus the module docstring's design-condition clause.
`Derived/EdgePerturbationTail.lean`: the new AdmissibilityDissolution
section — `perturbAdmissible_of_degDev_lt` (the degree-window transfer;
no `0 ≤ s` hypothesis, the strictness carries the sign through
`abs_lt`) and `edgePerturbation_normalized_connectivity_bracket_unconditional`
(leaving the two-sided normalized-connectivity window — an
*unconditioned* event — is bounded by the window tail at `t` plus the
degree tail at `s`, by the decomposition "some deviation ≥ s, or all
< s and then admissible"), conditional on `matrix_hoeffding` AND
`hoeffding_inequality` together, each via its own sub-theorem.
QA +16 (2987 → 3003, the AdmissibilityDissolution section): the pair
condition at both uniform designs (`½ + ½ = 1` the boundary, `1/10`
with slack); the boundary entry pin (the `p ≡ ½` all-false
off-diagonal entry exactly `0` — the engine's inequality *tight* at
the boundary); the **dropped-pair-condition fence** (`p ≡ 9/10`: the
entry exactly `−4/5` at a design legal in every other respect); the
transfer's positive witness (`p ≡ 1/10`: deviations `|−1/5| < 1/2`,
base degrees `1` in the shrunk window `[1, 2]`, derived degree `4/5`
by `deg_resampled`); the strictness-boundary coherence (the `p ≡ ½`
all-false outcome in the degree event exactly where the transfer does
not apply, and provably *not* admissible); the ∀-vertex statistic; and
the closed-form instance `4 exp(−1/4096) + 4 exp(−1/16)` on `K₂` at
window `[1/2, 5/2]`, `s = 1/2`, `t = 1/16`. Degenerate-corner analysis
recorded pre-statement (`s = 0` harmless — the deviation event becomes
all of `Ω`, the bound vacuous but true; `card V = 0` fenced by the
inherited `hcard`; the diagonal corner of the pair condition stronger
than needed but satisfiable at uniform designs). Records: the
proposal's dissolution delivery record (four technique findings, the
residual honesty note), `proposals/README.md`'s Delivered-row clause,
README (3003; one highlights clause; one module-table clause), the
radar (QA axis synced, 4.0 held per protocol), the scoreboard
(verification row + interpretation bullet), both index maps, both map
stamps + regenerated SVG, the execution plan, this entry.

**Verification:** spike first (`wip/dissolve_spike.lean`, every piece
to zero errors/warnings pre-shelf — three genuine elaboration slips
caught: the `add_le_add` argument order crossing the calc's addition
(fixed by swapping the decomposition union's order),
`norm_num`'s inability to normalize inside a `Real.exp` atom (the
exponent arithmetic proved as a standalone equation and `rw`-en), and
an extra `(by norm_num)` sliding into the `[Nonempty V]` instance
slot); `lake env lean` zero errors on all three touched modules
(`EdgePerturbation.lean` at zero warnings; the QA module at its
recorded three-note `Try this: ring_nf` baseline — the pre-degree-tail
HEAD baseline is one note, the post-Bernstein three, this delivery's
calls add none, verified against the stashed tree); explicit `lake
build` targets ✔ on `EdgePerturbation`, `EdgePerturbationTail`,
`EdgePerturbation_QA`; `#print axioms` via `wip/dissolve_axcheck.lean`
on all 17 audited declarations exactly as designed (the engine,
transfer, and fourteen QA lemmas at `propext, Classical.choice,
Quot.sound`; the theorem and closed-form pin honestly carrying both
axioms); **full `lake build` ✔ immediately followed by
`check_build_completeness.py` — after the documented mtime remediation
(the baseline stash-cycle touched five source mtimes; remove artifact +
rebuild once), 128 source files, 128 fresh artifacts, 0 stale, 0
missing, exit 0**; `lint_axioms` (10, both findings
allowlisted-confirmed), `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (**3003/10/0**, idempotent); **map freshness
exit 0** after the stats-stamp sync (2987 → 3003 in both map files; no
proposal status header changed).

**Remaining risk:** none owed — the engine and transfer are
unconditional hard crust. The new Derived theorem is conditional on
`matrix_hoeffding` and `hoeffding_inequality` together and must never
be described as foundationally proved. The pair condition is a genuine
design restriction (uniform designs mean `p ≤ ½`; the `p ≡ 9/10` fence
shows what breaks without it); no theorem-level dropped-pair
refutation is claimed at fixture scale (the shrunk-window hypotheses
cannot hold on the `K₂`-class fixtures without window slack — the
standing junk-window obstruction); the piece-level `−4/5` fence
carries the falsification content.

**Next handoff:** the Active table's only actionable row remains the
empirical-stationary Step 2, still gated on a consumer pricing the
bias-term shape; otherwise the same decomposition applied to the floor
and sweep-cut theorems' own admissibility conjuncts (priced, not owed),
or the next load-bearing gap `docs/6_SGT_BACKLOG.md` names (all
remaining items consumer-gated).

## 2026-08-29T09:27:50Z — The normalized-Laplacian degenerate-degree corner audit: the parked junk-spectrum finding settled in proved form

**Run:** `20260829T092750Z-run-1`  
**Session:** `ses_fb3359cafffedSVqHfQWT6erXC`  
**Status:** in-progress  
**Milestone:** the corner audit the standing handoff names as its
falsification-frontier residue — the parked spike-level finding that the
normalized Laplacian's junk value at zero-degree corners is the
*identity's* spectrum (`λ₂ = 1`), not the zero matrix's — currently
recorded only in prose honesty notes and now to be pinned as hard crust.
Selection context: no High rows in the Active table (the one Medium-High
row, empirical-stationary Step 2, is consumer-gated; all others are
Low human-decision-gated), the backlog's remaining items all
consumer-gated; the run first *attacked* the shelf's two named
dropped-guard targets (the sharpened drift's `s = γ` corner via
variance scaling — fails: the stated variance proxy is the deterministic
`‖∑ L_e²‖`, p-independent, and the exponent is weight-scale-invariant,
capped ≈ 2/3 on hand fixtures vs. the needed `ln(2d)`; the window
family's dropped admissibility via negative-adjacency outcomes — fails:
a resampled adjacency with at most one positive eigendirection forces
`μ₂ ≤ 0`, i.e. `λ₂(L_sym) ≥ 1`, by congruence inertia), both honesty
notes survived, and that analysis is exactly what prices the parked
corner audit: the junk-prediction facts it needs are consumed three
times over by such refutation analyses and should be shelf lemmas, not
spike findings. Deliverable: `degreeInvSqrt`-vanishing iff (both the
zero-degree and the hitherto-unrecorded *negative*-degree corners),
`normalizedLaplacian A = 1` at all-nonpositive degrees, `evals_one`
(the identity's sorted spectrum), and the QA audit section — the K₂
all-false outcome's spectral contrast (`λ₂(L) = 0` beside
`λ₂(L_sym) = 1`), the negative-degree corner at `p ≡ 1`, and the
floor-condition consequence the honesty note claims, all in proved form.
Pure hard crust, zero new axioms.

**Changes (planned):** a degenerate-degree-corners section in
`Scaffold/Mathlib/GraphTheory/Normalized.lean`
(`degreeInvSqrt_apply_eq_zero_iff`,
`normalizedLaplacian_eq_one_of_forall_deg_nonpos`), `evals_one` (+ its
`eigvalOf_one` engine) in `Spectral.lean`, and the audit section in
`Scaffold/QA/Derived/EdgePerturbation_QA.lean` beside the honesty note
that names the finding. Records to follow: the proposal's
honesty-note update (the parked finding settled; the two adversarial
analyses recorded), README QA count, radar QA axis, scoreboard, map
stamps, this plan, and the activity log.

**Verification (planned):** spike to zero errors/warnings before any
shelf edit; `lake env lean` on the touched modules; explicit `lake
build` targets; `#print axioms` on the new declarations (expect exactly
`propext, Classical.choice, Quot.sound`); full `lake build` +
`check_build_completeness.py`; `lint_axioms`, `check_citations`,
`check_markdown_links`; scoreboard regeneration and map-freshness sync.

Since 2026-08-28, any entry reporting a **new axiom admission** must
record `python3 scripts/lint_axioms.py` passing with the admitted axiom
settled against the degenerate-corner guard check — guarded, or
allowlisted with the reason recorded in the script at admission time
(see `proposals/lint-axiom-degenerate-corner-guards.md`: both axiom
repairs of that week had the missing-guard half of their defect visible
in the signature alone).

Since 2026-08-28: **`README.md`'s "Recent highlights" list and "What's
here" table entries stay to one line each — a module name and a single
clause, no dates, step numbers, or proof-technique detail.** This
journal is the place for the full delivery narrative; the proposal's own
record is the place for technique findings. A "Records swept" list that
updates README should add or tighten one line, not append a paragraph —
the exhaustive per-delivery prose that used to accumulate directly in
README (until a full rewrite on 2026-08-28, prompted by an operator
readability complaint: individual lines had grown past 8,000 characters)
belongs here and only here.

## 2026-08-29T03:29:49Z — Degree eigenvalue sandwich delivered: the `dmin/dmax` spectrum bridge to `normalizedLaplacian`, the irregular-window engine (terminal)

**Run:** `20260829T025710Z-run-1`  
**Session:** `ses_fb49d4316ffei9OpmdCbq7BaSn`  
**Status:** completed  
**Milestone (delivered):** the standing handoff's top named follow-on
prerequisite — the irregular/volume-weighted Cheeger window's own
named missing piece, "the degree bridge to `normalizedLaplacian`" —
**DELIVERED as zero new axioms (count stays 10; `#print axioms` on the
audited engine, interface, and headline QA declarations: exactly
`propext, Classical.choice, Quot.sound` — pure hard crust). QA
2865 → 2902 (+37, the new `DegreeSandwich_QA.lean`).**

**Changes:** (1) **The engine** — `GraphTheory/VariationalTransfer.lean`'s
new sandwich section: `evals_normalizedLaplacian_le_div` and
`div_le_evals_normalizedLaplacian` —
`λₖ(laplacian A)/dmax ≤ evals (normalizedLaplacian A) k ≤
λₖ(laplacian A)/dmin` at **every** sorted index, on arbitrary symmetric
nonnegative positive-degree graphs (no connectivity — the irregular
Cheeger pair's own hypothesis shape) — plus the degree stretch as a
linear equivalence (`degreeSqrtEquiv`), the two degree-weighted
denominator bounds, the two pointwise Rayleigh-quotient bracket
lemmas, the supporting `normalizedLaplacian_evals_zero` pin (the
normalized counterpart of `laplacian_evals_zero`), the
`lambda2`/`secondEval` interface pair, and division-free mul forms.
Pre-delivery analysis established **no pointwise test-vector route
exists** (the `x ⊥ 1` vs `x ⊥ √D·1` constraint sets mismatch under the
degree substitution), so the proof rides the shelf's subspace
Courant–Fischer machinery (`evals_min_max` with both witness forms,
witness subspaces transported through the stretch) — load-bearing on
the congruence, `laplacian_psd`, and the CF engine. (2) **QA (+37)** —
the new `DegreeSandwich_QA.lean`: the P₃ exact pin `λ₂(L_sym) = 1` by
two independent raw computations (eigenpair-witness `≤` side;
constraint-algebra `≥` side), the upper side of the sandwich
**attained at equality** (`1 = λ₂/dmin`), the wrong-constant pairing
fence (`1 ≤ 1/2` refuted), the lower-side instance with the bracket's
honest slack, the engine at a non-second index through trace-route
pins (`3/2 ≤ 2`), the K₂ regular squeeze tight on both ends
(`2 ≤ 2 ≤ 2`), and the **`dmin = 0` isolated-vertex fence** — on
`K₂ ⊕` an isolated vertex the degree-floor hypothesis still holds at
`dmin = 0` while the un-guarded upper side reads `1 ≤ lambda2/0 = 0`:
refuted, the junk-instantiation failure mode the positivity guard
fences. (3) **Records**: the new proposal
`proposals/degree-eigenvalue-sandwich.md` (COMPLETE + delivery record
with the no-pointwise-route analysis finding, one caught proof-design
slip — the lower side's competitor form must run on the *normalized*
dominating set — and the technique findings: the `Fin (Fintype.card
(Fin 3))` binder-spelling sum trap with the recorded type-ascription
fix, `set`-naming to resolve `csInf_le`'s TC metavariable, the 3×3
`!![…]`-literal entry stall with the `Matrix.of`-if + decide-simp
idiom, `mul_le_mul_of_nonneg_left`'s side-sensitivity,
`Real.inv_mul_cancel` absent for `inv_mul_cancel₀`),
`proposals/README.md` (the Delivered-table row), README (2902; date;
one module-table clause), the radar (QA axis synced to 2902/66
modules, held at 4.0 per protocol), the scoreboard (verification row +
interpretation bullet), the backlog (item 3's update clause), the
index map (the sandwich section's rows), the map stamps + regenerated
SVG, this plan, and this log.

**Verification:** spike first (`wip/ds_spike.lean`, `wip/ds_qa_spike.lean`
— every piece to zero errors/warnings before any shelf edit); explicit
`lake build` targets ✔ (`Scaffold.Mathlib.GraphTheory.VariationalTransfer`
2190/2190, `Scaffold.QA.SpectralGraph.DegreeSandwich_QA` 2230/2230);
`#print axioms` exactly as designed; **full `lake build` ✔ (2405/2406)
immediately followed by `check_build_completeness.py` — 128 source
files, 128 fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms`
exit 0 (10 axioms, both findings allowlisted-confirmed),
`check_citations` and `check_markdown_links` pass; scoreboard
regenerated idempotent (**2902/10/0**); **map freshness exit 0** after
the stats-stamp sync (2865 → 2902 in both map files). Nothing
committed; the prior run's uncommitted sharpened-drift delivery and
`b9717df` below it preserved untouched.

**Remaining risk:** none owed — the sandwich is unconditional hard
crust. The open priced follow-on is the irregular Cheeger window
assembly (now unblocked), whose Step-0 design questions are recorded
in the proposal: the keep-or-drop resampling design can isolate
vertices (making `L_sym(G_ω)` junk at those outcomes), and which side
of the sandwich each inclusion consumes must be settled against the
delivered λ₂ tails' shapes.

**Next handoff:** the Active table's only actionable row remains the
empirical-stationary Step 2 (still gated on a consumer pricing the
bias-term shape); otherwise the irregular Cheeger window assembly
(priced, not owed; its engine now delivered), or the next load-bearing
gap `docs/6_SGT_BACKLOG.md` names.

## 2026-08-29T02:57:10Z — Degree eigenvalue sandwich in delivery: the `dmin/dmax` spectrum bridge to `normalizedLaplacian`

**Run:** `20260829T025710Z-run-1`  
**Session:** `ses_fb49d4316ffei9OpmdCbq7BaSn`  
**Status:** in-progress  
**Milestone:** the standing handoff's top named follow-on prerequisite —
the irregular/volume-weighted Cheeger window's own named missing piece,
"the degree bridge to `normalizedLaplacian`". Deliver the classical
two-sided eigenvalue sandwich `λₖ(laplacian A)/dmax ≤
evals (normalizedLaplacian A) k ≤ λₖ(laplacian A)/dmin` at every sorted
index (engine), plus the `secondEval`/`lambda2` interface pair the
window consumes. Analysis on the current tree established that no
pointwise test-vector route exists (the `x ⊥ 1` vs `x ⊥ √d` constraint
sets mismatch under the degree substitution), so the proof must ride the
shelf's subspace min–max (`evals_min_max`, both Courant–Fischer witness
forms, `finrank_map_eq_of_injective`) composed with the proved
congruence and `laplacian_psd` — load-bearing on all of them. Zero new
axioms expected. QA plan: the P₃ instance with the upper side attained
at equality (`λ₂(L_sym) = 1 = λ₂(L)/dmin`), the wrong-constant pairing
fence (`¬(1 ≤ 1/2)`), the K₂ regular squeeze (both sides `2 ≤ 2 ≤ 2`),
a non-second index instance at `k = 2` (trace route), and the `dmin = 0`
isolated-vertex junk fence (`λ₂(L_sym) = 1` against `λ₂/0 = 0`).

## 2026-08-29T01:38:22Z — Sharpened drift interface delivered: the matched-threshold `s/(γ−s)` pair, the envelope arithmetic proved (terminal)

**Run:** `20260829T012051Z-run-1`  
**Session:** `ses_fb4e9d34cffevjpNTzrZmfXFxU`  
**Status:** completed  
**Milestone (delivered):** the standing handoff's top named priced
follow-on — the `t/δ`-sharpened drift interface — **DELIVERED as zero
new axioms (count stays 10; `#print axioms` via
`wip/sharpdrift_axcheck.lean` on all 12 audited declarations: the five
envelope-arithmetic/gap QA lemmas and the strict-improvement pin
exactly `propext, Classical.choice, Quot.sound`; the two sharpened
Derived theorems and the four theorem-instantiating QA pins honestly
carrying `matrix_hoeffding` alone — the same conditional structure as
the delivered pair). QA 2855 → 2865 (+10,
`EdgePerturbation_QA.lean`'s sharpened-interface section).**

**Changes:** (1) **The sharpened pair** —
`Derived/EdgePerturbationDrift.lean`'s new sharpened section:
`edgePerturbation_fiedlerSubspace_drift'` and
`edgePerturbation_fiedlerLine_drift'` — at `0 < s < γ ≤ λ₃(L A) −
λ₂(L A)`, `μ{‖rotation‖ ≥ s/(γ−s)} ≤ 2 d exp(−s²/(2‖∑ₑ L_e²‖))` — the
delivered `t/δ` pair instantiated at `t := s`, `δ := γ − s`: the gap
consumed inline, the threshold matched to the tail, the exact
statement shape of `eventStreamProjectorDrift`; the envelope-optimal
instance of the `t/δ` family at every threshold (at threshold
`u = s/(γ−s)` the exponent is maximized at `s = γu/(1+u)`). (2) **QA
(+10)** — the envelope arithmetic *proved*: domination (`t ≤ γt/(t+δ)`
at every valid instance) and the same-threshold identity
(`(γt/(t+δ))/(γ−γt/(t+δ)) = t/δ` — together: the sharpened family *is*
the envelope of the delivered family), both joined to concrete
numerics at the naive `(1, ½)` instance of `γ = 2` (envelope point
`4/3`); the closed-form three-path instances at the join point
(`6 exp(−1/24)`, both variants) and at the non-trivial threshold `2`
(`s = 4/3`, `6 exp(−2/27)`); the naive delivered-theorem instance at
threshold `2`; and the strict-improvement pin `6 exp(−2/27) <
6 exp(−1/24)` — matching threshold to tail is a real strengthening,
not a reparametrization. (3) **Records**: the matrix-Hoeffding
proposal (the sharpened-interface follow-on delivery record with
technique findings — the goal-side numeral-type ascription trap
(`(2:ℝ)` needed where the corresponding `have` infers ℝ), the
stale-olen recurrence at exactly the recorded boundary (QA elaboration
reports the new Derived theorems as unknown identifiers until the
artifact refresh) — and the honesty note that the `s < γ` guard admits
no cheap refutation fixture: at `s = γ` the junk threshold makes the
event all of `Ω` but `2 d exp(−γ²/(2‖∑ L_e²‖)) > 1` on every available
fixture, so the guard is *proof*-load-bearing, not fixture-refutable),
`proposals/README.md` (the Delivered-table row's follow-on clause),
README (2865; one module-table clause), the radar (QA axis synced,
held at 4.0 per protocol), the scoreboard (verification row +
interpretation bullet + reviewed date), the backlog (item 4's pipeline
clause), the index map (the module blurb + the two sharpened rows),
the map stamps + regenerated SVG, this plan, and this log.

**Verification:** spike first (`wip/sharpdrift_spike.lean`, every
piece to zero errors/warnings before any shelf edit); `lake env lean`
zero errors on both touched modules with output exactly at the
pre-existing baseline (the QA module's lone pre-existing
`Try this: ring_nf` note verified present on the unmodified tree by
stash); explicit `lake build` targets ✔ (2236/2236); `#print axioms`
exactly as designed (12 declarations); **full `lake build` ✔
(2405/2406) immediately followed by `check_build_completeness.py` —
after the documented single-module mtime remediation, 127/127 fresh,
0 stale, 0 missing, exit 0**; `lint_axioms` (10, both findings
allowlisted-confirmed), `check_citations`, `check_markdown_links` pass;
scoreboard regenerated idempotent (**2865/10/0**); **map freshness
exit 0** after the stats-stamp sync (2855 → 2865 in both map files;
no proposal status header changed). Nothing committed; the prior
runs' deliveries are committed at `b9717df` and preserved untouched.

**Remaining risk:** none owed — the pipeline family's priced
follow-on list is empty. The two sharpened theorems remain conditional
on `matrix_hoeffding` and must never be described as foundationally
proved.

**Next handoff:** the Active table's only actionable row remains the
empirical-stationary Step 2 (gated on a consumer pricing the
bias-term shape); otherwise the irregular/volume-weighted analogue of
the Cheeger window (needs the degree bridge to
`normalizedLaplacian`) — or the next load-bearing gap
`docs/6_SGT_BACKLOG.md` names.

## 2026-08-29T01:20:51Z — Sharpened drift interface in delivery: the matched-threshold `s/(γ−s)` pair for the edge-resampling design

**Run:** `20260829T012051Z-run-1`  
**Session:** `ses_fb4e9d34cffevjpNTzrZmfXFxU`  
**Status:** in-progress  
**Milestone:** the standing handoff's top priced follow-on — the
`t/δ`-sharpened drift interface. The delivered
`edgePerturbation_fiedlerSubspace_drift`/`edgePerturbation_fiedlerLine_drift`
bound `μ{‖rotation‖ ≥ t/δ} ≤ 2 d exp(−t²/(2‖∑ₑ L_e²‖))` under
`t + δ ≤ λ₃ − λ₂`; deliver the `s/(γ−s)`-shaped pair mirroring
`eventStreamProjectorDrift` exactly (at `0 < s < γ ≤ gap`:
`μ{‖rotation‖ ≥ s/(γ−s)} ≤ 2 d exp(−s²/(2σ²))`), the delivered pair at
`t := s`, `δ := γ − s` — the gap consumed inline, threshold matched to
tail, envelope-optimal at every threshold. Zero new axioms expected
(conditional on `matrix_hoeffding` via the delivered pair alone). QA
plan: the envelope arithmetic pinned (domination `t ≤ γt/(t+δ)` +
same-threshold identity, general and at the concrete `(1, ½)` instance),
the closed-form three-path instances (`6 exp(−1/24)` at γ = 2, s = 1;
`6 exp(−2/27)` at threshold 2), and the strict-improvement pin over a
valid non-envelope instance at the same threshold.

## 2026-08-28T23:23:58Z — Cheeger-window consumer of the λ₂ tail delivered: the high-probability connectivity window under random edge resampling (terminal)

**Run:** `20260828T230752Z-run-1`  
**Session:** `ses_fb564f6d3ffe0r0ERiz5rQ57Ht`  
**Status:** completed  
**Milestone (delivered):** the standing handoff's named
"conductance/Cheeger-level consumer of the new λ₂ tail" (priced, not
owed) — the first join of the edge-perturbation concentration family to
the Cheeger center — **DELIVERED as zero new axioms (count stays 10;
`#print axioms` via `wip/cheegerfloor_axcheck.lean` on all 16 audited
declarations: the two engine lemmas and ten hard-crust QA lemmas
exactly `propext, Classical.choice, Quot.sound`; the two Derived
theorems and the two closed-form QA instances honestly carrying
`matrix_hoeffding` alone). QA 2843 → 2855 (+12,
`EdgePerturbation_QA.lean`'s Cheeger-window section).**

**Changes:** (1) `GraphTheory/Cheeger.lean`'s public-API engine pair —
the combinatorial-Laplacian spelling of both Cheeger bounds on
d-regular graphs: `cheeger_lower_bound_laplacian` (`d·φ²/2 ≤ lambda2`)
and `cheeger_upper_bound_laplacian` (`lambda2 ≤ 2 d φ`), pure
composition of the proved pair with `smul_regularNormalizedLaplacian`
(`L = d • L_sym`) and `secondEval_smul_of_pos` — closing the
regular-Cheeger ↔ `lambda2` interface gap. (2)
`Derived/EdgePerturbationTail.lean`'s CheegerWindow section —
`edgePerturbation_lambda2_cheeger_floor` (`μ{λ₂(G_ω) ≤ d·φ²/2 − t} ≤
2 d exp(−t²/(2‖∑ₑ L_e²‖))` by `measure_mono` into the delivered λ₂
lower tail) and `edgePerturbation_connectivity_bracket` (leaving
`[d·φ²/2 − t, 2dφ + t]` implies leaving the two-sided eigenvalue tail
at the *same* constant — the window contains the eigenvalue ball; both
Cheeger directions load-bearing on the inclusion). (3) QA +12: the
φ(K₂) = 1 and 1-regularity pins transferred at definitional equality
from `Cheeger_QA`'s fixture, the base λ₂ = 2 at the `lambda2`
interface, the engine window with the **ceiling attained at equality**
(`λ₂ = 2 = 2·(1·φ)`), the closed-form floor/bracket instances at
`t = 1/2` (`4 exp(−1/64)`), and **non-vacuity witnesses for both
window sides** (all-false below the floor with `λ₂ = 0` attained at
equality; all-true above the ceiling at `λ₂ = 4 ≥ 5/2`).

**Verification:** spike first (`wip/cheegerfloor_spike.lean`, zero
errors/warnings before any shelf edit); direct `lake build` targets ✔
on all three touched modules; `#print axioms` exactly as designed;
**full `lake build` ✔ (2405/2406) immediately followed by
`check_build_completeness.py` — 127/127 fresh, 0 stale, 0 missing, exit
0**; `lint_axioms` (10, both findings allowlisted-confirmed),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
idempotent (**2855/10/0**); **map freshness exit 0** after the
stats-stamp sync (2843 → 2855). Records updated: the proposal (the
Cheeger-window follow-on delivery record with technique findings — the
direct `have h0 := laplacian_evals_zero …` re-tripping the recorded
`Fin`-spelling linarith trap, the `degreeMatrix 0` unfold order — and
the honesty note on the absence of a K₂-shaped dropped-guard refutation
fixture), `proposals/README.md`, README (2855 + one module-table
clause), the radar (QA axis synced, held at 4.0 per protocol), the
scoreboard, the backlog (item 7), both index maps, the execution plan,
and this log. Nothing committed; prior runs' deliveries committed at
`c9a6044` and preserved untouched.

**Remaining risk:** none owed. The delivery's conditional structure is
unchanged: the two Derived theorems are conditional on
`matrix_hoeffding` and must never be described as foundationally
proved.

**Next handoff:** the Active table's only actionable row remains the
empirical-stationary Step 2 (gated on a consumer pricing the bias-term
shape); otherwise the priced follow-ons on record — the `t/δ`-sharpened
drift interface (an `s/(γ−s)`-shaped statement mirroring
`eventStreamProjectorDrift`), the irregular/volume-weighted analogue of
the new window (needs the degree bridge to `normalizedLaplacian`) — or
the next load-bearing gap `docs/6_SGT_BACKLOG.md` names.

## 2026-08-28T23:07:52Z — Cheeger-window consumer of the λ₂ tail: high-probability expansion window under random edge resampling (terminal; closed by operator verification)

**Run:** `20260828T230752Z-run-1`  
**Session:** `ses_fb564f6d3ffe0r0ERiz5rQ57Ht`  
**Status:** completed  

**Closing note (operator, 2026-08-28):** the run exited after writing the
plan below and the actual Lean work, but before its own terminal entry —
the records-gap pattern seen earlier this session. Verified independently
before closing: the planned `Cheeger.lean` pair
(`cheeger_lower_bound_laplacian`, `cheeger_upper_bound_laplacian`) and the
planned `Derived/EdgePerturbationTail.lean` consumers
(`edgePerturbation_lambda2_cheeger_floor`,
`edgePerturbation_connectivity_bracket`) are all present and match this
plan; full `lake build` (2406 targets, "Build completed successfully");
`check_build_completeness.py` (127/127 fresh, 0 stale, 0 missing);
`lint_axioms` (10, both prior findings still allowlisted-confirmed);
`check_scaffold_map_freshness.py` exit 0; `check_citations`,
`check_markdown_links` pass; QA 2843 → 2855 (+12,
`EdgePerturbation_QA.lean`'s Cheeger-window section). `#print axioms`
independently re-run: the two `Cheeger.lean` corollaries are unconditional
hard crust (`propext, Classical.choice, Quot.sound` only); the two Derived
consumers carry exactly `matrix_hoeffding` and nothing else, matching the
plan's own claim. No `sorry`/`admit` found in any touched file.
**Milestone:** the standing handoff's named "conductance/Cheeger-level
consumer of the new λ₂ tail" (priced, not owed) — the first join of the
edge-perturbation concentration family to the Cheeger center: the
resampled graph's algebraic connectivity stays inside the Cheeger-driven
window `[d·φ²/2 − t, 2dφ + t]` outside a set of the eigenvalue tail's
measure, with both Cheeger directions load-bearing on the inclusion.
Zero new axioms planned (conditional on `matrix_hoeffding` via the
delivered tail alone).

**Changes (planned):** (1) `Cheeger.lean` public-API engine pair — the
combinatorial-Laplacian spelling of both Cheeger bounds on d-regular
graphs (`d·φ²/2 ≤ lambda2` / `lambda2 ≤ 2dφ`), a pure composition of
`smul_regularNormalizedLaplacian`, `secondEval_smul_of_pos`, and the
proved pair; (2) `Derived/EdgePerturbationTail.lean`'s Cheeger-window
section — the floor tail `μ{λ₂(G_ω) ≤ d·φ²/2 − t} ≤ 2 d exp(…)` and the
two-sided bracket (both directions consumed); (3) K₂ QA: the φ(K₂) = 1
join to Cheeger_QA's pinned value, the tight ceiling equality
`λ₂ = 2dφ` attained, closed-form tail instances at t = 1/2, and the
all-false/all-true non-vacuity witnesses (both window sides provably
fire at concrete outcomes).

**Next handoff (interim):** spike in `wip/cheegerfloor_spike.lean` to
zero errors/warnings before any shelf edit.

## 2026-08-28T22:00:09Z — Eigenvalue-level edge-perturbation tail delivered: spectral-gap concentration via proved Weyl ∘ matrix-Hoeffding tail (terminal)

**Run:** `20260828T214358Z-run-1`  
**Session:** `ses_fb5af754effe6Y0M4rrPcZCfGU`  
**Status:** completed  
**Milestone (delivered):** the standing handoff's named "third
concentration-axiom consumer" candidate in its SGT-native member —
`proposals/matrix-hoeffling-spectral-gap-estimation.md`'s follow-on
delivery record (its filename namesake application and its priced
uniform-form residual) — **DELIVERED as zero new axioms (count stays
10; `#print axioms` via `wip/ept_axcheck.lean` on all 17 audited
declarations: the 9 hard-crust QA lemmas exactly `propext,
Classical.choice, Quot.sound`; the four Derived theorems and the four
closed-form QA instances honestly carrying `matrix_hoeffding` alone).
QA 2830 → 2843 (+13, `EdgePerturbation_QA.lean`'s spectral-gap
section).**

**Changes:** (1) `Derived/EdgePerturbationTail.lean`'s new eigenvalue
section — `edgePerturbation_eval_tail`
(`μ{t ≤ |λᵢ(L(A+E_ω)) − λᵢ(L A)|} ≤ 2 d exp(−t²/(2‖∑ₑ L_e²‖))` at
every sorted index, the norm tail transferred to the sorted spectrum
through the *proved* `weyl_inequality` — the Weyl side has been hard
crust since its 2026-08-20 retirement — via the packaging identity,
`laplacian_add`, `evals_congr`), the one-sided gap-survival form, the
λ₂-spelled corollary at the `lambda2` interface, and the priced
uniform/existential-x quadratic-form packaging (its `x ≠ 0` guard
proved load-bearing by the fence below). (2) QA +13: the base and
perturbed K₂ spectra by the kernel-plus-trace route (`λ₂ = 2`; `λ₂ = 4`
at the all-true outcome where the resampled graph is the weight-2
edge), **the Weyl transfer pinned tight at a genuine design outcome**
(`|4 − 2| = ‖L(E_ω)‖ = 2`, both sides by independent routes — a
constant mistake anywhere on the transfer path breaks the proved
equality), the closed-form instances on K₂ and the three-path, and the
`x = 0` guard fence refuting the un-guarded uniform statement in
proved arithmetic (the un-guarded event is all of `Ω`, measure `1`,
against `4 exp(−49/16) < 1` from `Real.add_one_le_exp`). (3) Records:
the proposal (residual struck through + the follow-on delivery record
with technique findings — the auto-bound-identifier trap, the
`Fin (Fintype.card V)` vs `Fin n` spelling split inside `linarith`,
the section-variable argument-order trap), `proposals/README.md`,
README (2843 + the module-table clause), the radar QA axis (held at
4.0 per protocol), the scoreboard, the backlog, the index map (four
Derived-consumer rows), both map stamps, the execution plan, and this
log.

**Verification:** spike first (`wip/ept_spike.lean`, zero
errors/warnings before any shelf edit); `lake env lean` zero
errors/zero warnings on both touched modules (the Derived module after
its explicit olen rebuild — the stale-olen recurrence); explicit
`lake build` targets ✔; `#print axioms` exactly as designed; **full
`lake build` ✔ (2405/2406) immediately followed by
`check_build_completeness.py` — 127/127 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10, both findings allowlisted-confirmed),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
idempotent (**2843/10/0**); **map freshness exit 0** after the
stats-stamp sync (mandatory — this delivery changes a proposal's
status header). Nothing committed; the prior runs' committed
deliveries preserved untouched.

**Remaining risk:** none owed — the proposal's priced residual list is
now empty. The four new theorems are conditional on `matrix_hoeffding`
and must never be described as foundationally proved.

**Next handoff:** the Active table's only actionable row remains the
empirical-stationary Step 2 (gated on a consumer pricing the bias-term
shape); otherwise the `t/δ`-sharpened drift interface, a
conductance/Cheeger-level consumer of the new λ₂ tail (priced, not
owed), or the next load-bearing gap `docs/6_SGT_BACKLOG.md` names.

## 2026-08-28T21:43:58Z — Eigenvalue-level edge-perturbation tail in delivery: spectral-gap concentration via Weyl ∘ tail

**Run:** `20260828T214358Z-run-1`  
**Session:** `ses_fb5af754effe6Y0M4rrPcZCfGU`  
**Status:** in-progress  
**Milestone:** the standing handoff's named "third concentration-axiom
consumer" candidate in its SGT-native member — the eigenvalue-level
packaging of `edgePerturbation_norm_tail`: `μ{|λᵢ(L(A+E_ω)) − λᵢ(L A)|
≥ t} ≤ 2 d exp(−t²/(2‖∑ₑ L_e²‖))` at every sorted index (the parent
proposal's filename namesake), plus the priced uniform/existential-x
quadratic-form residual and the one-sided gap-survival form. Zero new
axioms; conditional on `matrix_hoeffding` via the tail alone, with the
Weyl side proved. Spiking first in `wip/ept_spike.lean` before any
shelf edit.

## 2026-08-28T12:18:48Z — Matrix-Hoeffding consumer delivered with the degenerate-dimension repair of all three matrix concentration axioms (terminal)

**Run:** `20260828T090419Z-run-1`  
**Session:** `ses_fb86ae73cffeN8L6vhbZxPoF60`  
**Status:** completed  
**Milestone (delivered):** `proposals/matrix-hoeffding-spectral-gap-estimation.md`
(the Active table's remaining Medium row, the standing handoff's top
named milestone) — **Steps 0+1 DELIVERED as zero new axioms (count stays
10; `#print axioms` via `wip/mh_axcheck.lean`: engine + hard-crust QA
exactly `propext, Classical.choice, Quot.sound`; the two Derived tails
and the tail-instance QA pin honestly carrying `matrix_hoeffding`
alone). QA 2749 → 2765 (+16).** The in-progress entry's finding was
confirmed by the spike and drove the repair-first sequencing.

**Changes:** (1) **The repair (Slice A)** — all three matrix
concentration axioms (`matrix_hoeffding`, `matrix_bernstein`,
`matrix_azuma_hoeffding`) were materially false at
`Fintype.card V = 0`, `t = 0` (the tail event is all of `Ω`, so a
probability measure gives `1` against the `2 · card V` prefactor's
`0`; each instantiated axiom read `1 ≤ 0`, i.e. was inconsistent —
every conditional theorem in the family was vacuous until this
repair). Repaired in place with the `[Nonempty V]` guard the cited
Tropp statements carry implicitly (statement-history docstrings);
hypothesis-form refutation records + the `t = 0` honesty lemma added
to `Matrix_QA.lean`; guard threaded through `eventStreamTail`, both
`sparsification_*_tail` (binder) and `eventStreamProjectorDrift`
(derived internally from its own `k : Fin (card V)`, no signature
change). (2) **The consumer (Slice B)** — new
`GraphTheory/EdgePerturbation.lean` (single-edge algebra joined to the
`rankOne` family by `laplacian_edgeAdj`; `Matrix.PosSemidef` helpers
the pin lacks, including squares-of-symmetric-PSD through
`dotProduct_mulVec_comm_of_isSymm`; the centered Bernoulli edge design
`(δ_e − p_e) • L_e` with every repaired-axiom clause proved —
**sign-free: no hypothesis on the weight matrix at all**, the only
load-bearing clause hypothesis being `p ∈ [0,1]`) and new
`Derived/EdgePerturbationTail.lean` (`matrix_hoeffding_quadForm` at
the load-bearing `x ≠ 0` guard — at `x = 0` the event is all of `Ω`
and the statement false for large `t` — plus the assembled norm and
quadratic-form tails, `Fin n` transport by `Fintype.equivFin` +
`Equiv.sum_comp`); umbrella imports added. (3) **QA** (+16): the
variance statistic pinned exactly (`∑_e L_e² = 4 • v vᵀ`,
`‖∑_e L_e²‖ = 8`, the rank-one norm proved two-sided by the
squared-action bound), the all-true outcome's sum exactly the unit
edge Laplacian (quadratic form `1` at `e₀`), the closed-form tail
instance `4 exp(−1/16)`, the degenerate zero-weight graph, the
`p ≡ 2` interval fence (the semidefinite clause provably fails outside
`[0,1]`), and the negative-weight sign-free witness. (4) **Records**:
the proposal (COMPLETE header, Step-0 verdicts, the repair record,
Step-1 delivery with technique findings — this pin's reversed
`sub_smul`, the ℕ-vs-ℝ smul-literal trap on `Fin 2`, `IsSymm`-not-a-
structure, `omit` before docstrings, PosSemidef's defeq-star clause,
sum-bound `ring` failures), `proposals/README.md` (row retired to the
Delivered table), README (2765; one module-table line), the radar (QA
axis synced; axis 7's third-consumer clause with the score held at 4.5
per protocol), the backlog, both index maps + the Tropp source row,
`docs/2_ARCHITECTURE.md`'s debt note, the scoreboard (verification row
+ interpretation bullet), the map stats stamps, this plan, and this
log.

**Verification:** spike first (`wip/mh0_spike.lean` — probes for the
refutation (elaborated live against the pre-repair axiom), the
repair-side arithmetic, the edge algebra, the PSD helpers, the clause
lemmas, and the generic corollary — all to zero errors/warnings before
any shelf edit); `lake env lean` zero errors on every touched module
with `Matrix_QA.lean` at its exact 16-warning and `EventStream_QA.lean`
at its 3-warning baseline (verified against the stashed pre-change
tree); explicit `lake build` targets ✔; **full `lake build` ✔
(2404/2405) immediately followed by `check_build_completeness.py` —
126/126 fresh, 0 stale, 0 missing, exit 0** (after the documented
single-module remediation for the one QA module outside the umbrella's
closure); `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated idempotent
(**2765/10/0**); **map freshness exit 0** (mandatory — the proposal's
status header changed; the check caught the 2749 → 2765 stamp drift on
first run, as designed). Nothing committed; the prior runs' uncommitted
deliveries preserved untouched.

**Remaining risk:** none blocking on the repaired trio — the corner is
fenced by refutation records and the zero-QAs instantiate the repaired
statements. Priced follow-ons recorded in the proposal: the
sampled-graph packaging identity (needs `laplacian_smul`/`laplacian_sum`),
the uniform (existential-x) quadratic-form packaging, and the
matrix-martingale golden-factor question (source-level, not a repair).

**Next handoff:** per priority item 0 — no High rows and no open Medium
rows remain in the Active table (the sparsification and
empirical-stationary follow-ons stay Medium-priced; Step 2 of the
latter still gated on a consumer pricing the bias-term shape); the
Fiedler program's named concentration → subspace-stability pipeline is
now natural from both ends (`fiedlerLine_stability` ×
`edgePerturbation_norm_tail` share the `[Nonempty V]`/probability-space
interfaces).

## 2026-08-28T07:53:36Z — Integrability audit delivered: `hoeffding_lemma` caught materially false in two new ways and repaired; the other three audited safe with proved safety lemmas (terminal)

**Run:** `20260828T070330Z-run-1`  
**Session:** `ses_fb8e05e3affewNe8eAGtMVuuex`  
**Status:** completed  
**Milestone (delivered):** the Active table's 2026-08-28 Medium audit row
(`audit-scalar-concentration-integrability-hazard.md`), selected over the
additive `matrix_hoeffding` consumer row per the priority order's
trust-surface item — **Step 0 complete on all four zero-consumer scalar
concentration axioms; DELIVERED as zero new axioms (count stays 10;
`#print axioms` via `wip/asc_axcheck.lean` on all 21 audited
declarations: the 17 refutation-family QA lemmas and both proved safety
lemmas exactly `propext, Classical.choice, Quot.sound`; the two axiom
consumers honestly carrying `hoeffding_lemma` alone). QA 2731 → 2749
(+18).**

**Changes:** (1) `hoeffding_lemma` **repaired in place** in
`Subgaussian.lean`: `[IsProbabilityMeasure μ]` added, conclusion's
constant corrected `a → √6·a` with the derivation in the docstring
(cited λ-form → two-sided tail → layer-cake gives
`E exp(X²/(6a²)) ≤ 2` exactly at `K² = 6a²`; junk-safe because both junk
mechanisms collapse the norm downward and the conclusion is an upper
bound). The pre-repair shape was **materially false in two Lean-verified
ways beyond the two recorded junk mechanisms**, both found by pre-spike
hand analysis and confirmed by the spike: the *constant defect*
(`old_hoeffding_lemma_refuted_constant_QA` — at the fair-coin Rademacher
probability fixture every old hypothesis holds genuinely, yet
`subgaussianNorm ≥ 6/5 > 1 = a`; `Real.log_two_lt_d9` arithmetic, no
junk anywhere) and the *guard defect*
(`old_hoeffding_lemma_refuted_guard_QA` — at the mass-19/10 rescaling
with the mean still genuinely zero, the norm is `≥ 21/5`, so no constant
`≤ 4` repairs the old shape; rational arithmetic via
`Real.log_le_sub_one_of_pos` + `Real.add_one_lt_exp`). (2) The three
guarded axioms confirmed safe with the discharge *proved on the shelf*:
`integrable_of_bounded_measurable` (`Hoeffding.lean`) and
`integrable_sq_sub_mean` (`Bernstein.lean`) — `Integrable.mono'` at
`integrable_const` from exactly each axiom's guard set. (3) QA +18 in
`Scalar_QA.lean`: the two refutation witnesses, the norm lower bounds,
the re-instantiation `hoeffding_lemma_rademacher_QA` (`≤ √6·1` at the
fixture that kills the old constant), the safety-lemma instances (the
fixture's mean routed through the first lemma — its first consumer), and
the arithmetic cores. (4) Records: the proposal (verdicts + delivery
record + technique findings), the retired subgaussian proposal's
adjacent-hazard note resolved, `proposals/README.md` (row retired to
Delivered), the three index files (including the corrected false
dependency claim "used by Hoeffding and Bernstein inequalities" and the
closed stale `subgaussian_tail_bound`-as-axiom entry), the Scalar
README, README's status count, the radar QA axis, the map files' stats
stamps, the scoreboard (verification row + interpretation bullet), the
execution plan, and this log.

**Decisive commands and outcomes:** spike first — `lake env lean
wip/asc_spike.lean` iterated to **zero errors/zero warnings** before any
shelf edit (catches recorded in the proposal: the pin's `Measurable.pow`
is the exponent-*function* form — use `Measurable.mul` + `pow_two` for
natural powers; `le_csInf` requires `Set.Nonempty` + the ∀∈ bound, each
defining set needing an explicit member — `K = 2` at the probability
fixture via `exp (1/4) ≤ 2`, `K = 100` at the scaled fixture via
`exp (1/10000) < 10000/9999` from `add_one_lt_exp` at the negative point
composed with `exp(x)·exp(−x) = 1`; the strictness discipline — `le_csInf`
is non-strict, so the scaled refutation proves `≥ 21/5` and refutes
`≤ 4`, never `≤ 21/5`; numeral-normalization bridges (`show
(2:ℝ)^2 = 4 from by norm_num`) before matching decimal-statement lemmas
at `K = 2`/`K = 100` instantiations; the stale-olen recurrence twice at
the module/QA import boundaries). Then `lake env lean` — zero errors on
all three changed modules at exactly the pre-existing warning baselines
(1/2/2, line-shifted) and zero errors on the QA file, whose warning
count *improved* 9 → 8 (the repair gives `subgaussian_norm_zero_QA` a
use for its instance); explicit `lake build` targets ✔ (three modules
1970/1970, QA module); `lake env lean wip/asc_axcheck.lean` — the trust
boundary exactly as designed; **full `lake build` ✔ (2402/2403, "Build
completed successfully") immediately followed by
`python3 scripts/check_build_completeness.py` — after the documented
mtime remediation (remove artifact + rebuild once) for the one post-build
docstring rewrap, 123/123 fresh, 0 stale, 0 missing, exit 0**;
`lint_axioms` (10, no issues), `check_citations` (pass, after one
prose-line-wrap repair: the checker's `^axiom` pattern had matched the
docstring phrase "axiom materially false" at a line start),
`check_markdown_links` pass; scoreboard regenerated idempotent
(**2749/10/0**); **`python3 scripts/check_scaffold_map_freshness.py`
exit 0 — mandatory since this run changes a proposal's status header;
the check caught the 2731 → 2749 stats-stamp drift on its first run, as
designed, and passed after both map files were synced**.

**Verification:** the two refutation witnesses are negative-witness QA
in the strategy document's exact sense — fixtures built to knock the
axiom over, with every hypothesis *genuinely* discharged (bounded
variable, honest mean-zero integral of an integrable function), so the
falsity is classical, not a junk-value artifact; the first is
load-bearing on `subgaussianNorm`'s exact MGF-set definition (a wrong
threshold constant anywhere breaks the `6/5` lower bound), the second
proves the repaired axiom's probability-measure hypothesis load-bearing
by refuting every constant alternative. The repaired statement's own
interface is exercised at the same fixture (`≤ √6·1`, consistent with
the proved `6/5 < √6`). QA does not and did not prove `hoeffding_lemma`;
its two consumers report it honestly in `#print axioms`.

**Remaining risk:** none blocking on the audited four. The recorded open
residual is the matrix trio's own `MatrixMDS`-shaped junk surface
(`matrix_hoeffding`/`matrix_bernstein`/`matrix_azuma_hoeffding`), per
the proposal's Non-goals — `matrix_hoeffding`'s consumer proposal should
run its Step 0 against it before building.

**Next handoff:** per priority item 0 — the remaining Medium rows: the
sampled-Laplacian quadratic-form consumer for `matrix_hoeffding` (its
Step 0 now includes the `MatrixMDS` junk-surface check this audit
surfaced), the sparsification follow-ons, and the empirical-stationary
Step 2 once a consumer prices the bias-term shape.

## 2026-08-28T07:03:30Z — Scalar-concentration junk-hazard audit in delivery: four zero-consumer axioms, two candidate defects found in `hoeffding_lemma`

**Run:** `20260828T070330Z-run-1`  
**Session:** (recorded at terminal entry)  
**Status:** in-progress  
**Milestone:** the Active table's 2026-08-28 Medium audit row
(`audit-scalar-concentration-integrability-hazard.md`), selected over the
additive `matrix_hoeffding` consumer row per the priority order's
trust-surface item — the same file family produced one materially false
axiom on 2026-08-22 and left an explicit warning on these siblings.
Pre-spike hand analysis found two candidate defects in `hoeffding_lemma`
beyond the two recorded junk mechanisms: a wrong-constant defect
(Rademacher threshold `a/√(ln 2) ≈ 1.201a > a` at probability measures)
and a missing-mass-guard defect (mass-just-under-2 measures make the
threshold exceed any fixed constant). Plan: spike both refutations plus
the three safe axioms' integrability discharges, then — if the
refutations hold — repair `hoeffding_lemma` in place
(`[IsProbabilityMeasure μ]` + `√6 * a`, derivation recorded), mirror the
`old_subgaussian_tail_bound_refuted_QA` family, sweep the three index
files and the retired proposal's adjacent-hazard note, and run the full
ladder. Zero new axioms; count stays 10.

## 2026-08-28T04:24:18Z — Fiedler Davis–Kahan Step 2 delivered: the Fiedler-line rotation via the common-kernel identification, the proposal COMPLETE (terminal)

**Run:** `20260828T034649Z-run-1`  
**Session:** `ses_fb98ef508ffeCWFaXVOXrZBbFi`  
**Status:** completed  
**Milestone (delivered):** the delivered Fiedler row's priced-deferred payoff slice, selected per priority item 0 fall-through (no High rows; the empirical-stationary Step 2 gated on a consumer; the sparsification row follow-ons-only) — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/fsd2_axcheck.lean` on all 24 audited declarations — 7 module + 17 QA: exactly `propext, Classical.choice, Quot.sound`, every one; the statement consumes only *proved* theorems, so the whole chain is unconditional). QA 2714 → 2731 (+17, `Fiedler_QA.lean`'s new `FiedlerLineStability` section). The proposal's program is COMPLETE (Steps 0+1+2).**

**Changes:** (1) `Spectral.lean`'s projector section gains the uniqueness layer: `dotProduct_mulVec_comm_of_isSymm` (the self-adjoint coordinate form), **`eq_of_isSymm_idempotent_of_forall_mulVec_eq`** (the Step-0-priced piece (i): symmetric idempotents determined by fixed space — `ker P = Fix(P)ᗮ` algebraically, the fixed-space hypothesis transferring kernels, `Q ∘ P = P` collapsing the action; nothing in the pin supplies it), **`spectralProjector_mulVec_eq_sum`** (the projector's action expanded in its own eigenbasis), and **`eigvecOf_expansion`** (every vector is its eigenbasis expansion, `sum_repr'` restated at plain-function eigenvectors). (2) `Spectral.lean` after `laplacian_evals_zero` gains the identification: **`initialProjector_laplacian_zero_fix_iff`** — the index-0 projector's fixed space is exactly the kernel with *no* connectivity hypothesis (filtered eigenvectors have eigenvalue exactly `0` by the two spectral pins; kernel coordinates vanish above the threshold) — and **`initialProjector_laplacian_zero_eq_of_connected`** — any two connected Laplacians carry the *same* index-0 projector (the uniqueness lemma joined to `laplacian_mulVec_eq_zero_iff_exists_const`, making the kernel-characterization ecosystem load-bearing on a projector-equality statement for the first time). (3) `Fiedler.lean` gains the headline **`fiedlerLine_stability`**: at Step 1's stack plus connectivity/nonnegativity of base and perturbed graph, `‖(P₁' − P₀') − (P₁ − P₀)‖ ≤ ‖laplacian E‖/δ` — the identification rewrites `P₀' = P₀`, the residual telescopes (`abel`) to the Step-1 projector difference; the proposal's actual payoff, the Fiedler vector's own rotation. (4) QA per obligation 3: the **P₃ → K₃ edge-addition instance** (separation `δ = 2` discharged against the two pinned spectra — the load-bearing step; the single-edge perturbation's Laplacian identified as `rankOne ![1,0,-1]`, its norm pinned **exactly `2` from both sides** with the rank-one bound and the quadForm witness consumed cross-module from the Sparsification delivery — so the derived bound is exactly `≤ 1`, the perturbed side sitting on Davis–Kahan's own tie branch with zero slack), the **identification instance** at the genuine two-spectrum pair P₃/K₃, the **fix-iff vector pins**, and the **disconnected fence** (the empty graph's index-0 projector provably ≠ P₃'s, witnessed by `e₀` — connectivity load-bearing, both iff directions exercised). Obligation 3's hand-computed angular movement honestly narrowed (entrywise projector values depend on `eigvecOf` choices). Records swept: the proposal (COMPLETE header + Step-2 delivery record with technique findings + the narrowing note), `proposals/README.md` (the row retired to the Delivered table with the program-COMPLETE result), README (2731; the module-table Step-2 clause), the radar (QA axis synced 2714 → 2731; axis 4's Step-2 clause, score held at 5.0 per protocol — load-bearing identification-layer engine inside the counted families, not a new theorem family), the scoreboard (verification row + interpretation bullet + header date; regenerated idempotent 2731/10/0), the backlog (the closure clause), the index map (the `fiedlerLine_stability` row + the identification-layer note), the QA module docstring, this plan, and this log.

**Decisive commands and outcomes:** spike first — `lake env lean wip/fsd2_spike.lean` iterated to **zero errors/zero warnings** before any shelf Lean (catches recorded in the proposal: the EuclideanSpace/Pi elaboration seam at `sum_repr'` — the eigenbasis expansion must restate the EuclideanSpace-typed sum at the Pi type *inside* a `have` before `Finset.sum_apply`/`Pi.smul_apply` rewrites match (rw patterns miss PiLp instances; mirror `eigvecOf_complete`'s idiom with per-term `rfl`); the `Matrix.smul_dotProduct` parse direction — ⬝ᵥ binds tighter than •, so the lemma is `x • (v ⬝ᵥ w)` and `(λ • v) ⬝ᵥ f` needs the dotProduct-unfold + `Finset.mul_sum` + per-term `ring` route; the self-referential-rewrite trap — `Q *ᵥ (Q *ᵥ y) = Q *ᵥ y` backwards loops, so the orthogonality chain is four `have`s joined by `.trans`; `sub_sub_sub_cancel_left` in this pin is `c − a − (c − b)`, not `a − c − (b − c)` — `abel` is the robust telescoping route; the `first | exact absurd rfl hij | (simp …; try norm_num)` idiom for entrywise matrix identities under `by_cases`; `laplacian_mulVec_apply` (diffusion form) as the cheap route for concrete `L *ᵥ x`; the stale-olen recurrence twice at import boundaries — module targets rebuilt before each consumer's elaboration). Then `lake env lean` — zero errors/zero warnings on `Fiedler.lean` and `Fiedler_QA.lean`, `Spectral.lean` at exactly its pre-existing 8-warning baseline; explicit `lake build` targets ✔ (Spectral, Fiedler 2205/2205, QA 2224/2224); `lake env lean wip/fsd2_axcheck.lean` — all 24 declarations exactly the standard three; **full `lake build` ✔ (2402/2403, "Build completed successfully") immediately followed by `python3 scripts/check_build_completeness.py` — 123 source files, 123 fresh artifacts, 0 stale, 0 missing, exit 0** (after the documented mtime remediation for the one post-build QA docstring edit); `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass after the record sweep; scoreboard regenerated idempotent (**2731/10/0**).

**Verification:** the delivery is unconditional hard crust — no axiom contact anywhere (`#print axioms`-verified on every new public declaration), and the QA is falsification-oriented in layers: the headline instance's separation is discharged against the two exact spectrum pins (only `3 − 1` admits `δ = 2`); the perturbation norm is pinned from *both* sides (a wrong constant anywhere in the rank-one/norm→form chain breaks exactly one side); the disconnected fence *refutes* the identification on the empty graph, proving the connectivity hypotheses load-bearing rather than decorative; and the two fix-iff directions are each exercised at a concrete vector. The identification is itself load-bearing on the kernel-characterization ecosystem — an error in `laplacian_mulVec_eq_zero_iff_exists_const`, the projector definition, or the eigenbasis machinery breaks exactly this chain.

**Remaining risk:** none blocking — the proposal records COMPLETE. Natural priced follow-ons now that both ends exist: the concentration → subspace-stability pipeline (composing `fiedlerLine_stability` with `sparsification_norm_tail`, the named companion consumer), and the sampled-Laplacian quadratic-form consumer for `matrix_hoeffding` (the remaining Medium row, whose Step-0 norm-transfer check is already half-answered by the delivered `abs_quadForm_le_of_l2OpNorm_le`).

**Next handoff:** per priority item 0 — the remaining Medium-High/Medium rows (the sampled-Laplacian quadratic-form consumer for `matrix_hoeffding`; the sparsification follow-ons; the empirical-stationary Step 2 once a consumer prices the bias-term shape), or the concentration → stability pipeline above.

## 2026-08-28T03:46:49Z — Fiedler Davis–Kahan Step 2 in delivery: the Fiedler-line rotation via the common-kernel identification

**Run:** `20260828T034649Z-run-1`  
**Session:** (recorded at terminal entry)  
**Status:** in-progress  
**Milestone:** the delivered Fiedler row's priced-deferred payoff slice, selected per priority item 0 fall-through (no High rows; the empirical-stationary Step 2 gated on a consumer; the sparsification row follow-ons-only) — **`fiedlerLine_stability`: the Fiedler vector's own rotation, not the rank-2 subspace containing it.** The Step-0 pricing recorded two cheap pieces (the telescoping `(P₁ − P₀) − (Q₁ − Q₀) = P₁ − Q₁` at a common kernel projector; the Step-1 bound) and one genuinely priced piece, both halves of which this run builds: (i) a symmetric-idempotent-determined-by-fixed-space uniqueness lemma (`ker P = Fix(P)⊥` algebraically, then `Q ∘ P = P` and `ker` transfer), and (ii) the fixed-space characterization `Fix(initialProjector L 0) = ker L` — connectivity-free, via the `spectralProjector` eigenbasis expansion, `laplacian_evals_zero`, and `evals_first_le_eigvalOf` — joined to `laplacian_mulVec_eq_zero_iff_exists_const` for the identification `initialProjector (L A) 0 = initialProjector (L A') 0` at two connected Laplacians. Zero new axioms; spike first (`wip/fsd2_spike.lean`). QA plan per the proposal's obligation 3: the P₃→K₃ edge-addition headline instance (separation `δ = 2` discharged against the pinned `{0,1,3}` and `{0,3,3}` spectra — the perturbed side sits exactly on Davis–Kahan's own tie branch, the derived bound `≤ 1` tight), the identification instance at the genuine two-spectrum pair, concrete fix-iff pins at vectors, and the disconnected fence (the empty graph's kernel projector provably ≠ P₃'s — connectivity load-bearing).

## 2026-08-28T02:34:49Z — Fiedler-subspace Davis–Kahan Step 0+1 delivered: `davis_kahan_sin_theta`'s first graph-theoretic consumer (terminal)

**Run:** `20260828T013901Z-run-1`  
**Session:** `ses_fba07a23effe3uCrc65sDqurcY`  
**Status:** completed  
**Milestone (delivered):** the Active table's top actionable Medium-High row (no High rows; priority item 0 fall-through; the other Medium-High row's Step 2 gated on a consumer) — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/fsd_axcheck.lean` on all 22 audited declarations — 5 module + 17 QA, private helpers and the `k3Adj` fixture covered transitively: exactly `propext, Classical.choice, Quot.sound`, every one; the wrapper consumes a *proved* theorem, so the whole chain is unconditional). QA 2695 → 2714 (+19, `Fiedler_QA.lean`'s new `FiedlerSubspaceStability` section).**

**Changes:** (1) Step 0's three verdicts, recorded in the proposal before any shelf Lean: the "zero consumers anywhere" premise corrected (`davisKahanTwoPoint` in the derived layer invokes the theorem in a proof term — the true gap was the zero Mathlib-layer/graph-theoretic one, now closed); the delivered Band Davis–Kahan family does NOT subsume Step 1 (two-sided windows vs the one-sided bottom-2 projector — more plumbing, and the band route would bypass the target theorem); Step 2's residual-projector route priced (the subprojector law is the delivered master product law, the telescoping is immediate — the priced piece is the common-kernel identification `initialProjector L 0 = initialProjector L' 0`). (2) `Spectral.lean` +4: `laplacian_zero`, `laplacian_add` (the perturbed-adjacency Laplacian identity — the proposal draft's statement-shape correction), `evals_congr` (general-index proof-irrelevance, sibling of `secondEval_congr`), `laplacian_evals_zero` (the bottom-Laplacian-eigenvalue pin, no connectivity). (3) `Fiedler.lean` (imports `Perturbation.DavisKahan`, no cycle): the headline **`fiedlerSubspace_stability`** — `‖initialProjector (laplacian (A+E)) 1 − initialProjector (laplacian A) 1‖ ≤ ‖laplacian E‖/δ` at `3 ≤ card V` and `δ ≤ λ₃(L(A+E)) − λ₂(L A)`, consuming `davis_kahan_sin_theta` verbatim at `k = 1`; no connectivity hypothesis (the docstring records that connectivity is what interprets the projector as the Fiedler cluster, not what the bound needs). (4) QA per the proposal's obligations 1–2: exact combinatorial P₃ pins (λ₂ = 1 — the `≥` side new by the sum-of-squares identity `E(x) = ‖x‖² + 3(x₀+x₂)²` on the zero-sum constraint; λ₃ = 3 by `laplacian_evals_zero` + the λ₂ pin + trace `0+1+λ₃ = 4`), the two-route zero-perturbation cross-check (the wrapper's instance at `δ = 2`, separation discharge load-bearing against the pinned `{0,1,3}` spectrum, vs the raw `P₃ + 0 = P₃` matrix identity — meeting at distance exactly `0`), and the K₃ tie-witness (λ₂ = λ₃ = 3 both sides exact; the wrapper's hypothesis set provably EMPTY at the tie — tie-awareness inherited from Davis–Kahan's own case split, vacuous not silently bounded); the honest narrowing recorded in the proposal (entrywise projector values at fixtures need Step-2 machinery, so the independent cross-check route is the matrix identity). (5) Records: the proposal (status header + premise-correction note + verdicts + delivery record with technique findings), `proposals/README.md` (row delivered + Delivered-table row), README (2714; module-table clause), radar (QA axis synced 2695 → 2714; axis 4 evidence clause, score held at 5.0 per protocol), scoreboard (verification row + interpretation bullet), backlog, index map (the Fiedler wrapper row + engine-lemma note), the execution plan, this log. Nothing committed.

**Decisive commands and outcomes:** spike first — `lake env lean wip/fsd_spike.lean` green (zero errors/warnings) before any shelf Lean; technique findings in the proposal's delivery record (the `Fin (card V)` plain-numeral elaboration trap — `⟨1, by omega⟩` spelling with `by show (1:ℕ)+1 < card; omega` side conditions; the `evals`-typed sum re-stated at `Fin 3` by a defeq `have` before `Fin.sum_univ_three`; `deg` at fixtures by `rw [deg, Fin.sum_univ_three] <;> norm_num [adjacency]` where `simp` leaves classical filter-card goals `decide` cannot close; the pinned Mathlib's asymmetric `le_csInf (Nonempty) (∀∈)` vs `csInf_le (BddBelow) (∈)` signatures; `one_le_div`/`le_div_iff₀` for Rayleigh quotients; `linear_combination hsum3 * (…)` constraint identities; the stale-olen recurrence at the import boundary — module target rebuilt before the consumer's elaboration). Then `lake env lean` — zero errors/zero warnings on Fiedler.lean and Fiedler_QA.lean, Spectral.lean at exactly its pre-existing 8-warning baseline; explicit `lake build` targets ✔ (module, QA); `#print axioms` — the standard three only, all 22; **full `lake build` ✔ (2402/2403, "Build completed successfully") immediately followed by `python3 scripts/check_build_completeness.py` — 123/123 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass after the record sweep; scoreboard regenerated (**2714/10/0**).

**Verification:** the delivery is unconditional hard crust — the wrapper consumes the proved `davis_kahan_sin_theta`, so nothing in the chain carries an axiom beyond the standard three, and the QA is falsification-oriented: the spectrum pins are what a wrong index convention or wrong operator in the wrapper's separation would break (only `λ₃ − λ₂ = 3 − 1` admits `δ = 2` on `{0,1,3}`), the two routes to the zero-perturbation distance share no mechanism, and the tie-witness identifies the vacuity boundary exactly rather than waving at it.

**Remaining risk:** none blocking. Step 2 (the Fiedler-*line* rotation via the common-kernel projector identification) is priced with its exact route and deferred as its own slice; the concentration → subspace-stability pipeline (composing this wrapper with `sparsification_norm_tail`) is the natural companion consumer now that both ends exist.

**Next handoff:** per priority item 0 — the remaining Medium-High/Medium rows (the sampled-Laplacian quadratic-form consumer for `matrix_hoeffding`; the sparsification follow-ons), Step 2 above, or the empirical-stationary Step 2 once a consumer prices the bias-term shape.

## 2026-08-28T01:39:01Z — Fiedler-subspace Davis–Kahan Step 0+1 in delivery: `davis_kahan_sin_theta`'s first graph-theoretic consumer

**Run:** `20260828T013901Z-run-1`  
**Session:** (recorded at terminal entry)  
**Status:** in-progress  
**Milestone:** the Active table's top actionable Medium-High row (no High rows; priority item 0 fall-through; the other Medium-High row's Step 2 is gated on a consumer) — Step 0's survey verdict plus Step 1: `fiedlerSubspace_stability` in `Fiedler.lean`, giving `davis_kahan_sin_theta` (proved 2026-08-21, zero Mathlib-layer consumers, never exercised at a graph object) its first graph-theoretic consumer. Step-0 findings from source evidence: the proposal's "zero consumers anywhere" premise is stale (`davisKahanTwoPoint` invokes the theorem in `Derived/ProjectorDrift.lean` — the true gap is Mathlib-layer/graph-theoretic, to be corrected in the proposal); the delivered Band Davis–Kahan family does not subsume Step 1 as a one-line corollary (two-sided windows vs the one-sided bottom-2 projector); Step 2's residual-projector lemma has a cheap two-thirds route with the common-kernel identification (`initialProjector L 0 = initialProjector L' 0` via fixed-space uniqueness) priced as its own deferred slice. Plan: `evals_congr` + `laplacian_add` in `Spectral.lean`, the headline wrapper in `Fiedler.lean`, QA per the proposal's obligations 1–2 (P₃ combinatorial spectrum pins λ₂ = 1 exact and λ₃ = 3; the zero-perturbation two-route instance; the K₃ tie-awareness witness with the hypothesis set provably empty at the λ₁ = λ₂ = 3 tie). Zero new axioms; spike first (`wip/fsd_spike.lean`).

## 2026-08-28T00:24:07Z — Empirical-stationary-distribution Steps 0+1 delivered: the V-valued i.i.d. sampling space and `hoeffding_empirical`'s first consumer (terminal)

**Run:** `20260827T234233Z-run-1`  
**Session:** `ses_fba69b163ffe0E5xVN6134I68B`  
**Status:** completed  
**Milestone (delivered):** the Active table's top Medium-High row (no High rows; priority item 0 fall-through) — **DELIVERED as zero new axioms (count stays 10; `#print axioms` via `wip/esd_axcheck.lean`/`wip/esd_qa_axcheck.lean`: the 14 `IIDProduct` declarations + both Mixing lemmas exactly `propext, Classical.choice, Quot.sound`; the two Derived theorems and the three tail-instantiating QA pins honestly carry `hoeffding_empirical` — the delivery's entire trust boundary). QA 2666 → 2695 (+29, two new QA files).**

**Changes:** (1) the Step-0 survey verdict, recorded in the proposal before any shelf Lean: no V-valued i.i.d. measure exists in the shelf; the minimal one is BernoulliProduct's construction at an arbitrary normalized `q : V → ℝ`, with the σ-algebra on `V` carried as `[MeasurableSpace V] [MeasurableSingletonClass V]` instance hypotheses (automatic on `Fin n` fixtures); one graph-side gap found — `walkDistribution_nonneg`. (2) `Scaffold/Mathlib/Probability/IIDProduct.lean` (new): `iidMass`/`iidPMF`, the one-/two-coordinate factorized marginals, cylinder measures, `indepFun_coord`, and the three `hoeffding_empirical` clause shapes at coordinate indicators (`measurable_indicator_coord`, `integral_indicator`, `indepFun_indicator_coord`) — pure hard crust, consumer-neutral. (3) `walkTransitionMatrix_nonneg` + `walkDistribution_nonneg` in `Mixing.lean` (the walk law certified a probability vector beside `sum_walkDistribution`). (4) `Scaffold/Derived/EmpiricalStationary.lean` (new): `hoeffding_empirical_iid` (the generic composition; `n ≠ 0` load-bearing at the centering collapse) and `empiricalWalkDistribution_tail` — `P{|p̂_i(n) − ν_{t₀} i| ≥ t} ≤ 2 exp(−2nt²)` at nonnegative weights + positive degrees, no symmetry/connectivity/mixing hypothesis — both conditional on the axiom alone. (5) QA per the proposal's three named obligations plus fences: `IIDProduct_QA` (the four-atom fixture with every level pinned raw — joint masses, total by two routes, the indicator marginal, the centering integral, the numeric independence split `2/3·2/3 = 4/9` against the raw atom, the non-normalized-`q` fence `4 ≠ 1`) and `EmpiricalStationary_QA` (the path-fixture instance with the event honestly characterized empty at `t = 1`; the `n = 0` boundary identified — event `univ`, bound `2` — plus the `n ≠ 0` centering fence `0 ≠ 2/3`; the raw two-sample measure `1/9` meeting the axiom-backed bound `2 exp(−1)` at a number proved from `Real.add_one_le_exp` at `−1/2`). (6) Records: the proposal (verdict + delivery record with technique findings + Step-2 deferral), `proposals/README.md`, README (2695, two module rows, snapshot axis 7 → 4.5 dated), radar (QA axis 2695/64 modules; **axis 7 re-scored 4.0 → 4.5** per the axis's own recorded raise trigger, now met twice — `matrix_bernstein` at Slice 3, credited here as a records repair, and `hoeffding_empirical` here), scoreboard, backlog, both index maps, the execution plan, this log.

**Decisive commands and outcomes:** spike first — `lake env lean wip/esd0_spike.lean` green (zero errors/warnings) before any shelf Lean; technique findings in the proposal's delivery record (the function-space-∑ binder-annotation trap `∑ ω : ι → V, …`; the semantic-vs-linter `omit` tension — `iidPMF`'s `Finset.univ` pulls `DecidableEq V` into its signature so downstream omits fail while the linter still flags it, resolved by a local `set_option linter.unusedSectionVars false`; `Pi.single`/term-`if`s referencing `DecidableEq V`; the `Fin 2`-value enumeration via `(by omega : (ω i).val = 0 ∨ …)` + `Fin.ext` around the recorded `fin_cases`-wrapper quirk; the left-associated 4-atom `← add_assoc` chain; the Nat-cast spelling `↑2` in exponent rewrites; `abs_of_nonpos` for negative deviations; `ENNReal.ofReal_sum_of_nonneg`'s `←` direction; `univ`-enumeration of `Fin 2 → Fin 2` by `omega`-oracles + `funext`+`fin_cases` membership). Then `lake env lean` — zero errors/zero warnings on all five touched/new files; explicit `lake build` targets ✔ (2006/2006, 2192/2192, 2210/2210); `#print axioms` audits exactly as designed; **full `lake build` ✔ (2402/2403, "Build completed successfully") immediately followed by `python3 scripts/check_build_completeness.py` — one finding (the new Derived QA module outside the umbrella's closure, no artifact) closed by the documented `lake build <module>` remediation, then 123/123 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass after the record sweep; scoreboard regenerated (**2695/10/0**).

**Verification:** the sampling module and both graph lemmas are unconditional hard crust; the two Derived theorems and exactly three QA pins carry `hoeffding_empirical` and are reported as such — never described as proving the axiom. QA is two-route and falsification-oriented: the fixture's masses/marginals/independence each pinned raw against the ∑-∏ machinery (the raw computations are axiom-free by `#print axioms`); the `n = 0` junk boundary is identified, not waved at, and the clean form's `n ≠ 0` hypothesis is proved load-bearing; the empirical-measure `1/9` and the bound `2 exp(−1)` meet at a number proved independently of the axiom.

**Remaining risk:** none blocking. The stationarity-limit form (concentration around `stationaryVec`, mixing decay as a bias term) is the proposal's priced deferred Step 2, gated on a consumer naming the bias-term shape. The sampling space's σ-algebra instance hypotheses are the one interface note for abstract-`V` consumers.

**Next handoff:** per priority item 0 — the remaining Medium-High/Medium rows (the sampled-Laplacian quadratic-form consumer for `matrix_hoeffding`; the Fiedler-subspace Davis–Kahan Step-0 check against the delivered Band family; the sparsification follow-ons), or Step 2 once a consumer prices the bias-term shape.

## 2026-08-27T23:42:33Z — Empirical-stationary-distribution Step 0+1 in delivery: the V-valued i.i.d. sampling space and `hoeffding_empirical`'s first consumer

**Run:** `20260827T234233Z-run-1`  
**Session:** `ses_fba69b163ffe0E5xVN6134I68B`  
**Status:** in-progress  
**Milestone:** the Active table's top Medium-High row (no High rows remain; per priority item 0 fall-through) — Step 0's survey verdict plus, if tractable, Step 1: the fixed-time empirical-stationary-distribution concentration theorem, giving `hoeffding_empirical` (admitted axiom, zero theorem consumers) its first real consumer. Survey evidence already in hand: no V-valued i.i.d. product measure exists in the shelf (only `bernPMF` on `ι → Bool`); the minimal object is the BernoulliProduct pattern at an arbitrary normalized `q : V → ℝ` (the two-atom Bernoulli factor replaced by `q`), with the σ-algebra on `V` carried as `[MeasurableSpace V] [MeasurableSingletonClass V]` instance hypotheses — both discharge automatically on the graph fixtures' `Fin n` vertex types. Plan: `Scaffold/Mathlib/Probability/IIDProduct.lean` (mass/PMF, marginals, cylinder measures, `indepFun_coord`, the indicator `h_meas`/`h_indep`/mean clause shapes), `walkDistribution_nonneg` in `Mixing.lean` (the one graph-side gap — only `sum_walkDistribution` exists), and `Scaffold/Derived/EmpiricalStationary.lean` (`hoeffding_empirical_iid` at general `q` + `empiricalWalkDistribution_tail` at `walkDistribution A t₀ x`, conditional on the axiom, honestly reported via `#print axioms`); QA per the proposal's three obligations (closed-form `walkDistribution` fixture, the `n = 0` junk boundary, the raw two-sample instantiation) plus the non-normalized-`q` fence. Zero new axioms; spike first (`wip/esd0_spike.lean`).

## 2026-08-27T05:24:00Z — Alon–Boppana Step 3b in delivery: the energy half of the Rayleigh quotient

**Run:** `20260827T052400Z-run-1`  
**Session:** `ses_fbe5b5e50ffeFh22vJDpED2MWm`  
**Status:** in-progress  
**Milestone:** the Active table's adopted High row's named next action — Step 3b, the numerator of Nilli's Rayleigh quotient: the level-Lipschitz property of `levE` along support-adjacent edges and the parent lemma (`1 ≤ levE z → ∃ p, A z p ≠ 0 ∧ levE p + 1 = levE z`) as the interface layer, the interior (levels-1..k) level-sum bridge, and the headline lower bound `2 + 4k(d−1)ρ ≤ quadForm A (radialVec …)` under the existing `IsTreeBall` plus a 0-or-≥1 weight hypothesis — the parent-edges-from-below route answering the recorded hard piece (cardinality equations give level sizes, not edge counts; a lower bound on the numerator is all the variational route needs) — with the Rayleigh-quotient corollary joining it to the delivered 3a denominator. QA planned: the C₈ numerator pin by two independent routes (tight at `6 = 2 + 4·1·1·1`), the pseudo-edge `hedge` fence, and the fractional-weight fence. Zero new axioms; spike first (`wip/ab3b_spike.lean`).

## 2026-08-27T07:26:00Z — Alon–Boppana Step 3b delivered: the energy half of Nilli's numerator (terminal; records closed by the next run)

**Run:** `20260827T052400Z-run-1`  
**Session:** `ses_fbe5b5e50ffeFh22vJDpED2MWm`  
**Status:** completed  
**Milestone:** **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/ab3b_axcheck.lean` on all 19 audited declarations — 8 public + 11 QA: exactly `propext, Classical.choice, Quot.sound`, every one). QA 2549 → 2560 (+11, the Step-3b section of `AlonBoppana_QA.lean`).** The `Energy` section of `GraphTheory/AlonBoppana.lean`: `levE_le_levE_add_one_of_adj` (BFS levels 1-Lipschitz along support edges, junk-safe), `exists_levE_parent` (the parent lemma, connectivity-free — the from-below harvest dissolving the recorded "level sizes, not edge counts" obstruction without strengthening `IsTreeBall`), `interiorE` with its level-sum bridge, the headline `radialVec_quadForm_ge` (`2 + 4 k (d−1) ρ ≤ xᵀAx` under the existing tree-ball predicate plus the 0-or-≥1 weight discipline), and the Rayleigh corollary `radialVec_rayleigh_ge` — Nilli's quotient before the Step-5 `√` packaging, the interface Step 4 consumes.

**Terminal-entry note (closing run `20260827T072423Z-run-1`):** the delivery session completed the Lean, the proposal delivery record, and the records sweep (README, radar, scoreboard verification rows, backlog, index map, `proposals/README.md`'s next action → Step 4) but exited before this terminal entry and the execution plan's Active-block retirement — the recurring records-gap pattern, fourth instance. The closing run re-verified the delivery from scratch before writing this entry: `lake env lean` zero errors/zero warnings on both changed files; `lake env lean wip/ab3b_axcheck.lean` — all 19 declarations exactly the standard three (output re-read line by line); full `lake build` ✔ ("Build completed successfully") immediately followed by `check_build_completeness.py` — 113/113 fresh, 0 stale, 0 missing, exit 0; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass. One residual records gap found and closed by the closing run: the scoreboard's generated-metrics block had been left stale at 2549/2026-08-26 (the delivery session's +9-line sweep touched only the verification rows); regeneration brought it to **2560/10/0, 2026-08-27**, matching the proposal's recorded claim.

**Remaining risk:** the program is 0–3b of 5 steps — Step 4 (the two-vector orthogonalization) and Step 5 (the diameter-dependent theorem) remain; `d = 1` degeneracies and the `IsDRegular`-to-`IsTreeBall` `d`-join stay deferred to the Step-5 packaging, per the delivery records.

**Next handoff:** Step 4 per the Active table's named next action (the two far-apart edges' vectors joined into one orthogonal to `onesVec`, concluded through `secondEval_le_rayleigh` at `M = d•1 − A`).

## 2026-08-27T09:46:30Z — Alon–Boppana Step 4 delivered: the two-vector orthogonalization — the program's first eigenvalue-level statement (terminal)

**Run:** `20260827T072423Z-run-1`  
**Session:** `ses_fbde7efecffevF28sENIAPtEdS`  
**Status:** completed  
**Milestone (delivered):** the Active table's adopted High row's named next action — Step 4: join the two far-apart edges' radial test vectors into `twoEdgeVec := radialVec(x,y) − radialVec(u,v)`, prove it orthogonal to `onesVec` (the equal-mass lemma `radialVec_sum_eq` — both balls' sums reduce to the same function of `(d, ρ, k)` by `IsTreeBall`'s level equations), its squared norm `4 (k+1)` exact (disjoint radius-`k` balls), and its adjacency quadratic form at the doubled 3b bound `2 · (2 + 4 k (d−1) ρ)` (the cross term eliminated by 3b's own level-Lipschitz lemma plus `(k+1)+(k+1) < distEdge` ball disjointness — the far-apart theorem's first theorem consumer beyond disjointness), then conclude through `secondEval_le_rayleigh` at `M = d•1 − A` (PSD and kernel hypotheses from the delivered Step-1 facts `quadForm_le_of_isDRegular`/`adjacency_mulVec_onesVec`): `secondEval (d•1 − A) ≤ d − (2 + 4 k (d−1) ρ)/(2 (k+1))`. QA planned: the C₈ antipodal-pair instance with the interface pinned raw (orthogonality, norm `4`, numerator `4`, Rayleigh `1` tight) plus an independent engine route to the same `secondEval ≤ 1` at an integer-entry hand vector; the near-pair `hfar` fence (k = 1 numerator refuted at `8 < 12`), the P₃ overlap fence (norm identity refuted), and the loop-pair orthogonality fence. Zero new axioms; spike first (`wip/ab4_spike.lean`).

**Changes:** (1) this run first closed the interrupted Step-3b run's records gap — re-verified its delivery from scratch (`lake env lean` both files 0/0; the axcheck re-read; full build + completeness 113/113; lint/citations/links), appended its terminal entry, retired the execution-plan Active block, and repaired the scoreboard's stale generated-metrics block (2549/2026-08-26 → 2560/2026-08-27). (2) The Step-4 delivery: `GraphTheory/AlonBoppana.lean`'s new `TwoEdge` section — `radialVec_sum_eq` (equal mass), `twoEdgeVec` + orthogonality/norm/nonvanishing, the cross-edge elimination via 3b's Lipschitz lemma at the exact far-apart threshold, `dotProduct_mulVec_symm`/`quadForm_sub`, the doubled numerator bound + Rayleigh form, the engine layer at `d•1 − A`, and the headline `twoEdgeVec_secondEval_le` through `secondEval_le_rayleigh`; QA +16 in `AlonBoppana_QA.lean`'s Step-4 section (the C₈ antipodal positive — orthogonality two routes, norm `8 = 4(k+1)`, numerator raw `8 = 6 + 6 − 2·2`; the `hfar` fence `8 < 12` at `k = 1`; the P₃ overlap fence `2 ≠ 4`; the headline instance `secondEval (2•1 − abC8) ≤ 1` at `IsDRegular abC8 2`). (3) Records: the proposal (delivery record with technique findings + open-next → Step 5), `proposals/README.md` (next action → Step 5), README (2576 + module clause), radar (QA axis), scoreboard (verification row), backlog item 3, index map (8 new rows + section title), module/QA docstrings, the execution plan, this log.

**Decisive commands and outcomes:** spike first — `lake env lean wip/ab4_spike.lean` green (module side and QA side, zero errors/warnings) before any shelf Lean; the recorded catches now in the proposal's delivery record: `include` re-includes section variables with their original implicit binders (use local explicit binders), `rw` with an equation about a def's application unfolds the def throughout the goal (use `simp only` with have-equations), the fin_cases `(fun i => i) ⟨k, ⋯⟩` wrapper (enumerate by rcases-with-show), Fin-literal if-conditions undecidable to `norm_num`/`omega` (state point-lemma oracles or ¬-condition haves), `Matrix.one_mulVec` vs `mulVec_one` in this pin, `div_le_div_iff₀`, `mul_div_cancel₀`'s shape (use `field_simp`), the have-bound-walk opacity (hit again — inline in `dist_le`), `Finset.disjoint_right.1`'s implicit element binder, and the width-8 row-sum recipe (`Fin.sum_univ_eight` + rfl-entry haves + `simp only` + `norm_num`). Then `lake env lean` — zero errors/zero warnings on both changed files; explicit `lake build` targets ✔ (module 2010/2010, then QA after the module rebuild — the stale-olean remediation applied once); `#print axioms` via `wip/ab4_axcheck.lean` — the standard three only, all 34; **full `lake build` ✔ (2388/2389, "Build completed successfully") immediately followed by `python3 scripts/check_build_completeness.py` — 113/113 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass after the record sweep; scoreboard regenerated idempotent (**2576/10/0**).

**Verification:** the delivery is unconditional hard crust — no axiom contact anywhere (`#print axioms`-verified on every public declaration after the final source state). QA is load-bearing at three levels: the orthogonality by two routes (the theorem consumes `IsTreeBall`'s level equations; the raw route enumerates at independent value oracles — a wrong level pin breaks exactly one); the fence isolates the far-apart threshold at its exact constant (both radius-2 tree balls genuine, norm identity surviving, numerator refuted); the headline instance exercises the full engine stack (Step-1 regularity facts → PSD/kernel → `secondEval_le_rayleigh` → the two-edge vector) on a real graph.

**Remaining risk:** Step 5 (the diameter-dependent statement) is the program's last step — the far-apart-to-diameter bridge was priced and deferred in Step 2 (`dist_le_diam` needs an `edism ≠ ⊤` supplier); the `d : ℝ`/`d : ℕ` join and the `√` packaging are its recorded content. Two named QA residuals (the loop-pair orthogonality fence on P₃ `(0,1)`/`(2,2)`; an independent engine route to `secondEval ≤ 1` at the integer witness `![1, 1, 0, −1, −1, −1, 0, 1]` with `R_A = 4/3 ≥ 1` — computed, not formalized) are priced with fixtures on file.

**Next handoff:** per priority item 0 — Alon–Boppana **Step 5** (with the two QA residuals alongside), or the sparsification High row's Step-0 survey; otherwise the Medium-High/Medium rows (empirical-stationary-distribution Step 0; the sampled-Laplacian quadratic-form consumer; the Fiedler-subspace Davis–Kahan Step-0 check).

## 2026-08-27T01:49:02Z — Alon–Boppana Step 3a delivered: the radial test vector and its normalization (terminal)

**Run:** `20260827T012700Z-run-1`  
**Session:** `ses_fbf2e0bb0ffev5V6pH6hJgLx97`  
**Status:** completed  
**Milestone:** the Active priority table's adopted High row's named next action — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/ab3_axcheck.lean` on all 18 audited declarations — 8 public + 10 QA, the two private QA level-oracle helpers covered transitively: exactly `propext, Classical.choice, Quot.sound`, every one). QA 2539 → 2549 (+10, the Step-3 section of `AlonBoppana_QA.lean`).**

**Changes:** the new `RadialVector` section of `Scaffold/Mathlib/GraphTheory/AlonBoppana.lean` (no new imports, no umbrella change): **`radialVec`** — Nilli's radial test vector, `ρ ^ levE z` per BFS level on the radius-`k` edge ball and `0` outside, the d-regular-tree normalization carried by consumers as the hypothesis `ρ ^ 2 = ((d−1 : ℕ) : ℝ)⁻¹` (the `√` plumbing deliberately deferred to the Step-5 packaging with the `IsDRegular` `d : ℝ` join); the interface (`radialVec_apply`, `radialVec_of_mem_ballE`, `radialVec_eq_zero_of_not_mem_ballE`, `radialVec_left` — the always-`1` endpoint seed — and `radialVec_ne_zero`); **the layer-cake sum bridge `sum_ballE_eq_sum_levels`** (`ballE_card_eq_sum`'s summation form at a function); and the headline **`radialVec_dotProduct_self`** — `⟨ρ^{lev}, ρ^{lev}⟩ = 2 (k+1)` exactly under `IsTreeBall` at radius `k+1`: per level the geometric growth `2 (d−1)^j` cancels the vector's decay `ρ^{2j}` to exactly `2`. This is the denominator of Nilli's Rayleigh quotient and the first theorem consumer of the Step-2 level machinery — load-bearing growth in the strategy's sense (a wrong `levE`, `ballE` shape, or `IsTreeBall` equation breaks the identity's type or truth). `1 < d` load-bearing at the `mul_inv_cancel₀` cancellation. QA: the C₈ squared-norm pin `4 = 2 (k+1)` **by two independent routes** (the theorem through `abC8_isTreeBall` vs raw per-vertex enumeration at the level-0/level-1 membership oracles, `decide`-computed card — the routes share no mechanism), the `k = 0` pair both routes (the theorem at `isTreeBall_one_of_connected` — that Step-2 lemma's first consumer), and the K₂ **`d = 1` degeneracy fence** (the tree-ball predicate holds at `d = 1`, the normalization hypothesis is junk-satisfiable at `ρ = 0` through `0⁻¹ = 0`, and the vector `![1, 1]` refutes the identity at `2 ≠ 4`). Records: the proposal (status header + Step-3a delivery record with technique findings + open next step → Step 3b), `proposals/README.md` (the High row's next action), the scoreboard (two verification rows + the interpretation bullet), the radar (QA axis), the index map, backlog item 3, README, both docstrings, the execution plan, and this log. **Two records repairs in the same sweep:** the committed README/radar QA counts had been left at the Step-1 value 2520 by the Step-2 commit (both now 2549 with the Step-2 clauses folded into the Steps-1–3a clauses), and **the inherited signed-graphs index-map gap is closed** (the `GraphTheory.Signed` section that `7ca544b` had omitted, flagged as a bounded records task by the Step-1 run — this run touched the index map, so it delivered the section, including `Magnetic.lean`'s kernel-at-action row).

**Decisive commands and outcomes:** spike first — `lake env lean wip/ab3_spike.lean` iterated to zero errors/zero warnings before any shelf Lean (technique findings recorded in the proposal's delivery record: the `mul_assoc`-before-`← mul_pow` reassociation at the `2`-headed per-level product; `nsmul_eq_mul` as the root ℕ-smul converter where `Nat.smul_one` does not exist; the named-`have` requirement for `Finset.sum_subset`'s zero function — an inline `by rw` leaves metavariable-headed membership; `intro`-then-`rcases` for disjunct patterns; `simp` flattening nested `Finset.mem_insert` in reverse insertion order; and `.le` on an equation rewriting at the equation's own constant); then `lake env lean` zero errors/zero warnings on the module and the QA file (the QA pass hit the recorded stale-olean trap once — unknown `radialVec` until the explicit module-target rebuild); explicit `lake build` targets ✔ (2010/2010, 2011/2011); `#print axioms` — the standard three only, all 18; **full `lake build` ✔ (2388/2389, "Build completed successfully") immediately followed by `python3 scripts/check_build_completeness.py` — 113 source files, 113 fresh artifacts, 0 stale, 0 missing, exit 0** (the run hit the mtime half of the documented staleness remediation twice through its own `touch`-based warning checks — the artifact-removal rebuild closed it both times, exactly the documented remediation); `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass after the record sweep; scoreboard regenerated idempotent (**2549/10/0**, md5-stable).

**Verification:** every changed module elaborates directly and sits fresh-certified by the completeness reconciliation; the delivery is unconditional hard crust — no axiom consumed anywhere (`#print axioms`-verified after the final source state). QA is falsification-oriented at two levels: the two-route C₈ pin (a wrong level count, level power, or normalization constant breaks exactly one of the two routes at the same number), and the `d = 1` fence proving the module's own docstring claim materially — the normalization hypothesis is junk-satisfiable exactly where the truncated `(d−1)^j` kills the counts, so `1 < d` carries real content at the precise step named.

**Remaining risk:** the program is 0–3a of 5 steps — the theorem itself needs the energy half (Step 3b), the orthogonalization (Step 4), and the diameter-dependent statement (Step 5). Step 3b's known hard piece is that the cardinality equations give level sizes, not level-to-level edge counts, so its spike must price whether counting parents-from-below suffices (each level-`j` vertex has a neighbor at level `j−1`) or `IsTreeBall` needs strengthening. C₈'s 2-regularity remains not cheaply computable at `Fin 8` (the recorded `vecCons` opacity) — no Step-3b QA should assume it.

**Next handoff:** per priority item 0 — Alon–Boppana **Step 3b** (the energy half of the Rayleigh quotient; one sub-slice per run), or the sparsification High row's Step-0 survey (verifying `matrix_bernstein`'s clause set supports the leverage-score argument); otherwise the Medium-High/Medium rows (empirical-stationary-distribution Step 0; the sampled-Laplacian quadratic-form consumer; the Fiedler-subspace Davis–Kahan Step-0 check against the delivered Band family).

## 2026-08-27T01:27:00Z — Alon–Boppana Step 3 (sub-slice 3a) in delivery: the radial test vector and its normalization

**Run:** `20260827T012700Z-run-1`  
**Session:** `ses_fbf2e0bb0ffev5V6pH6hJgLx97`  
**Status:** in-progress (completed; see the terminal entry above)  
**Milestone:** Alon–Boppana Step 3's first sub-slice (the proposal prices Step 3 for sub-decomposition across runs), the Active table's adopted High row pursued per priority item 0: the radial test vector `radialVec A hA x y ρ k` (constant `ρ ^ levE z` per BFS level on the radius-`k` edge ball, `0` outside — Nilli's `ρ = (d−1)^{-1/2}` carried as the hypothesis `ρ ^ 2 = ((d−1:ℕ):ℝ)⁻¹`), its entry/support lemmas and nonvanishing, the layer-cake sum bridge `sum_ballE_eq_sum_levels`, and the squared-norm identity `⟨ρ^{lev}, ρ^{lev}⟩ = 2 (k+1)` under `IsTreeBall` — the denominator of the Rayleigh quotient and the first theorem consumer of the Step-2 level machinery. QA: the C₈ two-route norm pin at `k = 1` (theorem through `abC8_isTreeBall` vs raw per-vertex enumeration), the `k = 0` instance (first consumer of `isTreeBall_one_of_connected`), and the K₂ `d = 1` degeneracy fence (with `ρ = 0` junk-admissible through `0⁻¹ = 0`, the identity refuted at `2 ≠ 4` — `1 < d` load-bearing). Zero new axioms; spike first (`wip/ab3_spike.lean`).

## 2026-08-26T23:24:19Z — Alon–Boppana Step 2 in delivery: the tree-ball interface at module level

**Run:** `20260826T232419Z-run-1`  
**Session:** `ses_fbfa8f9d1ffeX7tB8vWXB8JTCV`  
**Status:** in-progress  
**Milestone:** Alon–Boppana Step 2, the Active table's adopted High row pursued per priority item 0 (named next action from Steps 0+1; the other High row — sparsification — stays a Step-0 survey). Content per the Step-0 verdict: the `levE`/`levClass`/`ballE` definitions promoted from the spike to `GraphTheory/AlonBoppana.lean` (BFS levels of an edge against `SimpleGraph.dist` on `supportGraph`), the tree-ball predicate as the level-cardinality equations `#{z | levE z = j} = 2 (d−1)^j` (`IsTreeBall`), the far-apart condition (`distEdge` + ball disjointness via the connected triangle inequality), and the layer-cake cardinality bridge (ball card = geometric sum) — the substrate Steps 3–5 consume. QA: the C₈ positive (tree-ball instance at the antipodal edge, `Disjoint` balls, level-0 from the general connected iff), the C₄ wrap-around negative (`IsTreeBall` fails at k = 3 — level 2 empty), and the threshold-tightness fence (near-antipodal balls at min cross-distance exactly `r + s` provably intersect). Zero new axioms; spike first (`wip/ab2_spike.lean`); the `dist` junk-zero trap guarded by connectivity hypotheses throughout.

## 2026-08-26T22:10:03Z — Alon–Boppana Steps 0+1 delivered: the tree-ball verdict and the d-regularity interface (completed)

**Run:** `20260826T215003Z-run-1`  
**Session:** `ses_fbff90392ffe55AQRtqmh5ZHtV`  
**Status:** completed  
**Milestone:** the Active priority table's top High row — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/ab_axcheck.lean` on all 22 audited declarations — 4 public + 18 QA: exactly `propext, Classical.choice, Quot.sound`, every one). QA 2506 → 2520 (+14, `AlonBoppana_QA` a new file).**

**Changes:** first, the records repair: closed the prior signed-graphs run's gap (terminal entry below + the plan's Active-block retirement; its full delivery and verification were already committed in `7ca544b` — this run re-confirmed the 93-declaration axiom audit against the committed state before closing). Then the milestone. **Step 0** (`wip/ab_spike.lean`): the tree-ball hypothesis priced as BFS level-cardinality equations `#{z | levE z = j} = 2 (d−1)^j` against `SimpleGraph.dist` on `supportGraph` (`levE`/`levClass`/`ballE`; ball-`Disjoint` = the far-apart condition) — not a tree-ness predicate; unit cost one distance value per vertex-level pair (adjacency/self one-liners; j-step values need pre-named-Adj walks inline in `dist_le`, a `have`-bound walk being `rfl`-opaque); connectivity amortizes every reachability refutation; the `dist` junk-zero trap and the explicit `SimpleGraph.Metric` import recorded; Q₃/K₃,₃ identified as the honest negative fixtures, C₈ the smallest full-hypothesis cycle; the verdict recorded in the proposal. **Step 1**: the new `Scaffold/Mathlib/GraphTheory/AlonBoppana.lean` (imports `Spectral` only; umbrella import added; the program's home for Steps 2–5) — `IsDRegular` (the shelf's `d : ℝ` hypothesis idiom), `adjacency_mulVec_onesVec` (`A *ᵥ onesVec = d • onesVec`), the AM–GM row-sum domination `quadForm_le_of_isDRegular` (`xᵀAx ≤ d ‖x‖²`; `hnn` load-bearing at the entrywise step), and the top-eigenvalue identification `evals_last_eq_of_isDRegular` (`evals ⟨last⟩ = d` from both sides — the `onesVec` witness and the unit-eigenvector domination; load-bearing on the sorted-spectrum API at its extremes). QA: the C₄/K₂ instances at raw entrywise eigen-equation pins, the P₃ non-regularity fence (`onesVec` provably not an adjacency eigenvector), the `hnn` fence (signed 0-regular `!![1,−1;−1,1]]`, domination refuted at `![1,0]`). Records: the proposal (Step-0 verdict + Step-1 delivery record with technique findings + status header), `proposals/README.md` (the High row → Step 2 next), README (2520; status-paragraph clause; module-table row), the radar (QA axis synced across 59 modules), the scoreboard (verification row + interpretation bullet, regenerated idempotent), the index map (the AlonBoppana section + 4 rows), backlog item 3, both docstrings, the execution plan, this log.

**Decisive commands and outcomes:** spike first — `lake env lean wip/ab_spike.lean` green (module side, QA side, tree-ball pricing) before any shelf Lean, after the recorded fixes (this pin's swapped `Finset.mul_sum`/`sum_mul` naming; `pow_two` reading `a ^ 2 = a * a` without `.symm`; the double `← Finset.sum_div` assembly for the AM–GM double-sum split; `onesVec ≠ (0 : V → ℝ)` by `Fintype.card_pos_iff` + `congrFun`; the inline-walk requirement in `dist_le ... |>.trans_eq rfl`; the `⟨0, ⋯⟩`-vs-`OfNat` literal mismatch making `fin_cases`-on-`z` + per-distance-`have` the reliable C₄ idiom); then `lake env lean` zero errors/zero warnings on the module and QA file; explicit `lake build` targets ✔ (2009/2009, 2010/2010); `#print axioms` on all 22 — the standard three only; **full `lake build` ✔ (2387/2388, "Build completed successfully") immediately followed by `python3 scripts/check_build_completeness.py` — 113 source files, 113 fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass after the record sweep; scoreboard regenerated idempotent (md5-stable; **2520/10/0**).

**Verification:** every changed module elaborates directly and sits fresh-certified by the completeness reconciliation; the delivery is unconditional hard crust — no axiom consumed anywhere (`#print axioms`-verified after the final source state). QA is falsification-oriented at three levels: the theorem instances joined to raw entrywise pins with no theorem input (the top-eigenvalue identification would fail visibly if either half of its two-sided proof were wrong — the eigenvalue witness or the domination); the non-regularity fence refuting the constant-eigenvector property at the interface's own witness; and the `hnn` fence isolating the AM–GM step on a graph satisfying every other hypothesis of the domination lemma.

**Remaining risk:** the program is 0+1 of 5 steps — the diameter-dependent theorem (Steps 2–5) is future runs, and this delivery's QA witnesses are interface-shaped by design (the proposal's QA plan assigns the spectral-gap-shaped witnesses to the steps that have the theorem). Inherited and flagged: the signed-graphs delivery's index-map section is missing (`index/map/spectral_graph.md` has no `Signed` rows — the `7ca544b` index diff covered only the irregular/multiway work); a bounded records task for the next run touching the index map. Radar axis scores deliberately unchanged (interface work; the axis claim moves with the theorem).

**Next handoff:** per priority item 0 — Alon–Boppana **Step 2** (the `levE`/`levClass` module-level definitions and the tree-ball predicate per the Step-0 verdict; one step per run per the proposal's operating instructions), or the sparsification High row's Step-0 survey (verifying `matrix_bernstein`'s clause set supports the leverage-score argument); otherwise the Medium-High/Medium rows (empirical-stationary-distribution Step 0; the sampled-Laplacian quadratic-form consumer; the Fiedler-subspace Davis–Kahan Step-0 check against the delivered Band family).

## 2026-08-26T21:50:03Z — Alon–Boppana Steps 0+1 in delivery: the tree-ball spike and the d-regularity interface

**Run:** `20260826T215003Z-run-1`  
**Session:** `ses_fbff90392ffe55AQRtqmh5ZHtV`  
**Status:** in-progress (completed; see the terminal entry above)  
**Milestone:** the Active priority table's High row the operator adopted 2026-08-26 (`proposals/alon-boppana-bound.md`, commit `d86e181`; pursued per priority item 0 over the other High row — sparsification-via-leverage-scores — whose next action is a Step-0 survey that may re-scope it, while this one is fully unblocked with every dependency surveyed proved and zero new axioms). Step 0: the tree-ball spike in `wip/ab_spike.lean` — pricing the "radius-r ball around an edge is tree-like" hypothesis in Scaffold's fixed-`V` idiom (working form derived: BFS level-cardinality equations `#{z | dist (z, e) = j} = 2 (d−1)^j` against `SimpleGraph.dist` on `supportGraph`, guarding the `dist` junk-zero-at-unreachable trap), discharged by hand on a concrete `Fin 8` fixture (C₈ at k = 2) with the honest negative witnesses (Q₃'s balls not full, K₃,₃'s edges not far apart) checked — the verdict lands in the proposal. Step 1: the new `GraphTheory/AlonBoppana.lean` (the program's home) — `IsDRegular`, `adjacency_mulVec_onesVec` (`A *ᵥ onesVec = d • onesVec`), the AM–GM row-sum domination `quadForm A x ≤ d ‖x‖²` (hnn load-bearing), and the top-eigenvalue identification `evals ⟨n−1⟩ = d` (both sides: domination + the eigenvalue witness through `exists_eigvalOf_eq_of_mulVec_eq_smul` at `onesVec`); QA in a new `AlonBoppana_QA.lean` — C₄/K₂ instances at independent raw pins, the P₃ non-regular fence (`onesVec` provably not an eigenvector), the hnn fence at the signed 0-regular `!![1,−1;−1,1]]`. Zero new axioms; spike first; one step per the proposal's operating instructions (Steps 2–5 remain future runs). This run also first closed the prior run's records gap (see the terminal entry below).

## 2026-08-26T21:50:03Z — Signed graphs delivered (terminal record; appended retrospectively)

**Run:** `20260826T194844Z-run-1`  
**Session:** unavailable (a Claude Code session, per the commit trailer of `7ca544b`; not an OpenCode session)  
**Status:** completed (terminal record appended retrospectively by run `20260826T215003Z-run-1` — the session exited after committing `7ca544b` and updating the scoreboard/radar/backlog/index/proposal/README, but before this entry and the execution plan's Active-block retirement; both closed by that run on the evidence below; the recurring records-gap pattern, third instance)  
**Milestone:** the signed-graph slice of the graph-model axis — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/sg_axcheck.lean` on all 93 audited declarations — 32 public (28 `Signed.lean` + 4 `Magnetic.lean`'s kernel section) + 61 QA — reads exactly `propext, Classical.choice, Quot.sound`, every one; independently re-confirmed by the closing run against the committed state). QA 2444 → 2506 (+62, `Signed_QA` a new file).**

**Changes:** the new `Scaffold/Mathlib/GraphTheory/Signed.lean` (umbrella import added): `signedAdj`/`signedLaplacian` (`D − A_σ` at a `{±1}` signing — loop-unsigned by balance itself, no separate loop-sign hypothesis), `IsBalanced` (switching existence), `signFlux` (the π-flux potential; `e^{i·flux} = s` entrywise), the entrywise magnetic join `magneticLaplacian_signFlux_apply`, the signed Dirichlet energy identity **derived from the delivered `magnetic_energy`** (the load-bearing join — a defect in the magnetic identity breaks the signed theorems; real and complex forms), the row-sum identity, the kernel↔edge-alignment characterization, the walk collapse to a `{±1}` switching (`supportGraph.Walk` induction), the **Harary balance theorem in kernel form** `isBalanced_iff_exists_ne_zero_mulVec_eq_zero` on connected symmetric nonnegative input, positive definiteness under frustration, and the **switching similarity** `diag(g) · L_σ · diag(g) = laplacian A` with two-way eigenpair transfer; plus `Magnetic.lean`'s kernel-at-action-level section (`magneticLaplacian_mulVec_eq_zero_iff`). QA: the balanced path (headline iff both directions, kernel pinned raw to the switching, energy identities pinned numerically real+complex), the frustrated triangle (`¬IsBalanced` proved from the switching equations' cyclic contradiction, kernel trivial two routes), the disconnected conclusion-level fence (kernel vector coexisting with global unbalance — connectivity load-bearing), the negative-loop boundary, the `hnn` mechanism fence, the switching-similarity and eigen-transfer pins at the independently verified path eigenpair.

**Decisive commands and outcomes (recorded in `7ca544b`'s scoreboard rows, re-confirmed where re-run):** full `lake build` ✔ (2386/2387, "Build completed successfully") immediately followed by `check_build_completeness.py` — 111/111 fresh, 0 stale, 0 missing, exit 0; both changed modules and the QA file elaborate directly, zero errors/zero warnings; explicit targets ✔ (2192/2192, 2193/2193); `#print axioms` on all 93 — the standard three only (re-run by the closing run: same result).

**Verification:** every changed module elaborates and sits fresh-certified by the completeness reconciliation; unconditional hard crust, no axiom consumed anywhere. Records already in `7ca544b`: scoreboard (two verification rows + the interpretation bullet), radar axis 1 (the signed category occupied), backlog, README (2506), index map, the proposal COMPLETE header + delivery record.

**Remaining risk:** none identified beyond the priced follow-ons recorded in the proposal (multiset-level spectrum equality, signed Cheeger, frustration-index theory — all gated). 

**Next handoff:** superseded by this run's active milestone (the adopted Alon–Boppana Steps 0+1, above).

## 2026-08-26T19:48:44Z — Signed graphs in delivery: the balance theorem via the magnetic π-flux bridge

**Run:** `20260826T194844Z-run-1`  
**Session:** unavailable (a Claude Code session, per the commit trailer of `7ca544b`; not an OpenCode session)  
**Status:** in-progress (completed; terminal record appended retrospectively by the next run — see above)  
**Milestone:** a fresh center-out candidate on radar axis 1 (graph and Laplacian models, 3.5, signed-graph theory its named absent category), selected per the empty High/Medium Active table per the standing handoff. Delivering: (1) `Magnetic.lean`'s new "kernel at the action level" section (`aligned → magneticLaplacian *ᵥ x = 0` row algebra at unit modulus, composed with the delivered form-level gauge iff into a kernel characterization — the magnetic module's own strengthening); (2) the new `GraphTheory/Signed.lean` — `signedAdj`/`signedLaplacian` (matrix-first, `s : V → V → ℝ` with explicit ±1 + loop-unsigned hypotheses), the π-flux join `magneticLaplacian A (signFlux s) = (signedLaplacian A s : ℂ)` entrywise, the signed energy identity **proved through the delivered `magnetic_energy`** (the load-bearing join: a wrong magnetic identity breaks the signed theorems), the row-sum identity, kernel ↔ edge-alignment, the walk collapse to a ±1 switching function (supportGraph Walk induction), the **Harary-balance headline** `IsBalanced A s ↔ ∃ x ≠ 0, signedLaplacian A s *ᵥ x = 0` on connected symmetric nonnegative input, positive definiteness under frustration, and the **switching similarity** `diagonal g * L_σ * diagonal g = laplacian A` with eigenpair transfer at switched vectors; (3) QA in a new `Signed_QA.lean` (the balanced one-negative-edge path with kernel pinned to the switching function, the frustrated one-negative-edge triangle with `¬IsBalanced` proved from the switching equations and the kernel trivial, the disconnected balanced⊕frustrated conclusion-level fence isolating `hconn`, the loop-sign fence isolating the unsigned-loop convention, the switching-agreement entrywise pin and the eigen-transfer instance at the independently known path eigenpair `![1,0,−1] @ 1`). Zero new axioms planned; spike first in `wip/`; prior runs' uncommitted deliveries preserved untouched. The radar axis-1 row's stale "absent: directed graphs" clause (delivered 2026-08-22/25 under item 8) is to be repaired in the record sweep.

## 2026-08-26T13:31:18Z — Multiway expansion in delivery (continuation): engine, application layer, headline, QA

**Run:** `20260826T133118Z-run-1`  
**Session:** `ses_fc1bdd405ffegvU5gnobbUx5RF`  
**Status:** in-progress  
**Milestone:** continuing the active multiway-expansion milestone (Step 0 + Step 1 — the higher-order Cheeger easy direction's every-family form) opened by run `20260826T083858Z-run-1`, which recorded the Step-0 verdict in `proposals/multiway-expansion.md` and drafted the full spike `wip/mw_spike.lean` before its session ended pre-record. This run verifies the spike green, spikes the two QA-support spin-offs (`evals_sum_eq_trace`, `exists_eigvalOf_eq_of_mulVec_eq_smul`), lands the order-statistics↔counting bridge and the general-k subspace Rayleigh–Ritz engine in `Spectral.lean`, and the application layer (part indicators, the pointwise `(a−b)² ≤ 2a²+2b²` absorption at constant exactly 2) plus the headlines `cheeger_upper_bound_multiway` / `_conductance` in a new focused `Multiway.lean`, then the QA file at the proposal's six obligations (K₂ k=2 equality; P₃ k=2 non-covering family; P₃ k=3 with λ₃ = 2 pinned independently; C₄ k=4 singleton equality; the C₄ cyclic-pair overlap fence with disjointness refuted and the conclusion refuted at `2 > 1`; the k=1 edge instance). Load-bearing on `laplacian_quadForm`, `quadForm_eigvalOf`/`dotProduct_eigvecOf`, the irregular family's congruence bridge, and `vol_pos_of_pos_deg`. Zero new axioms; spike-first discipline; prior runs' uncommitted deliveries preserved untouched.

## 2026-08-26T07:17:05Z — The irregular Fiedler instantiation delivered: the family's algorithm-facing capstone at `conductance² ≤ 2λ₂` (completed)

**Run:** `20260826T064300Z-run-1`  
**Session:** `ses_fc3387ac4ffeZHTaAuYbLTFpAK`  
**Status:** completed  
**Milestone:** the standing handoff's named bounded candidate — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/ifc_axcheck.lean` on all 23 audited declarations — 14 public + 9 QA: exactly `propext, Classical.choice, Quot.sound`, every one). QA 2340 → 2349 (+9 in `IrregularCheeger_QA.lean`).** The irregular Cheeger family is now algorithm-facing end to end: `fiedler_sweep_cut_normalized` — on every connected symmetric nonnegative positive-degree graph, an explicit closed superlevel/sublevel cut of the sweep vector itself satisfies `conductance S² ≤ 2 λ₂ (L_sym)`, exactly the regular family's `fiedler_sweep_cut` constant `2λ₂/d` on the cone.

**Changes:** (1) `VariationalTransfer.lean`'s new "The irregular Fiedler instantiation" section (no new imports, no umbrella change) — the normalized Fiedler interface (`fiedlerIndexNormalized`/`fiedlerVectorNormalized`: eigen equation, unit norm, `quadForm`/`rayleigh = λ₂`), the sweep vector `fiedlerSweepVector := D^{-1/2} u` with the stretch cancellation `√D f = u` and nonvanishing, the constraint conversion `fiedlerSweepVector_sum_deg_eq_zero` (the sweep family's own hypothesis obtained from the eigen-orthogonality hinge at `√D·1`, `0 < λ₂` from the delivered connectivity transfer — connectivity's exact entry point), and the headline composing `cheeger_sweep_cut_normalized` at its first eigenvector input. (2) QA +9: the exact pin `λ₂ (L_sym P₃) = 1` (new `≥ 1` side by the `2 x₁²` sum-of-squares through the sInf engine, nonemptiness witnessed by the concrete eigenpair at Rayleigh exactly `1` — the `≤ 1` side predates the family, non-circular; the Cheeger bracket on P₃ collapses to `1/2 ≤ 1 ≤ 2`), the instances on P₃/K₂ at independent pins, the pullback algebra and constraint hinge raw at the concrete eigenpair, and the connectivity mechanism fenced on the disconnected fixture (a kernel eigenvector provably violating the hinge at the pinned `λ₂ = 0` — kernel-ness does not supply the constraint, the gap does; the fence lives at the mechanism because the conclusion-level statement is unfalsifiable there: a kernel vector's sweep may find a conductance-0 component cut). (3) Records: the proposal (follow-on delivered + the Fiedler-instantiation delivery record with technique findings), `proposals/README.md` (Delivered row; candidates re-ranked), README (2349; module-table clause), the radar (QA sync 2340 → 2349; axis-4 clause held 4.5 with the protocol reason), the scoreboard (two verification rows + the interpretation bullet), the index map (section + 9 rows), backlog item 3 (update + the multiway multi-run pricing), both docstrings, the execution plan, this log. Also recorded in the execution plan: multiway expansion (the family's other named follow-on) is priced as a multi-run program — its easy direction needs a partition-space definition plus genuinely new engine content (centered indicators sum to zero; combinations re-introduce cross-part energy; quotient-matrix/interlacing or iterated-assembly routes) — a dedicated run should start with that Step-0.

**Decisive commands and outcomes:** spike first — `lake env lean wip/ifc_spike.lean` and `wip/ifc_qa_spike.lean` green before any module touched, after the recorded fixes (the scoped `Matrix` notation (`*ᵥ`) needing `open scoped Matrix` in standalone files; `le_csInf` taking the set's nonemptiness in this pin, discharged by exhibiting the concrete eigenpair as an element with Rayleigh exactly `1`; the matrix-literal/degree evaluation recipe `simp [icPathAdj, hdeglit, Real.sqrt_one]`; `Real.sqrt_ne_zero'.mpr`; `linear_combination` for `√2`-comm rearrangements; unary-minus shaping in scalar lemmas so `rw` patterns match; `Finset.sum_pos'` for dot-product positivity). Then `lake env lean` on both changed modules — zero errors/zero warnings; explicit `lake build` targets ✔ (module 2190/2190, QA 2193/2193); `#print axioms` via `wip/ifc_axcheck.lean` — all 23 the standard three (hit once by the stale-olean trap: the QA identifiers unknown until the explicit QA-target rebuild, exactly the documented remediation); **full `lake build` ✔ (2384/2385, "Build completed successfully") immediately followed by `python3 scripts/check_build_completeness.py` — 107/107 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass after the record sweep; scoreboard regenerated idempotent (md5-stable; **2349/10/0**).

**Verification:** every changed module elaborates directly and sits fresh-certified by the completeness reconciliation. The delivery is unconditional hard crust — no axiom consumed anywhere (`#print axioms`-verified after the final source state). QA is load-bearing at four levels: the exact spectral pin produced by a genuinely new route (the sum-of-squares lower bound, independent of the Fiedler family, closing `λ₂ (L_sym P₃)` to the point value `1`); the theorem instances joined to *independently produced* pins on both fixtures (the pre-existing eigenpair `≤ 1`, the pinned classical `λ₂ = 2`, the exhaustive all-cuts-are-`1`); the pullback hinge verified raw at a concrete, reader-checkable witness through the same public lemmas the choice-defined Fiedler route consumes; and the mechanism fence isolating exactly where connectivity enters (the orthogonality hinge fails for kernel eigenvectors on the pinned-`λ₂ = 0` fixture — the honest fence location given the conclusion itself may survive there).

**Remaining risk:** the sweep vector is classical-choice-defined (as every `eigvecOf` object is), so QA pins its properties and mechanism rather than its entries — the standard treatment the regular Fiedler family also receives. The `2 ≤ card V` hypothesis is carried exactly as by the family (the one-vertex degenerate case out of scope by design). Route provenance for the classical statement is the standard normalized-Cheeger treatment (Chung Ch. 2, section-level locator, the standing verify-against-physical-copy caveat; the statement is proved, so no axiom citation applies). QA fixtures are `Fin 2`/`Fin 3`/`Fin 4`; the theorems are size- and weight-general. The remaining priced follow-on: multiway expansion (multi-run program, Step-0 first).

**Next handoff:** the Active priority table remains empty (no High, no Medium — every remaining row a Low blocked on a human or technical decision). Next run falls through to the center-out SGT policy with the re-ranked named candidates: multiway expansion (the family's last priced follow-on, now explicitly priced as a multi-run program — the next run touching it should deliver its Step-0 survey and the partition-space definition design, not attempt the full easy direction), the standing gated candidates (directed-axis rate; magnetic spectral, each gated on a named consumer; a consumer pricing the wide-band minimax filter designs), or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-26T06:45:17Z — The irregular Fiedler instantiation in delivery: the sweep family's first eigenvector input

**Run:** `20260826T064300Z-run-1`  
**Session:** (recorded at terminal entry)  
**Status:** in-progress  
**Milestone:** the standing handoff's named bounded candidate — the irregular Cheeger family's algorithm-facing capstone, selected per the empty High/Medium Active table by the center-out policy. Delivering in `VariationalTransfer.lean`: the normalized-Laplacian Fiedler interface (`fiedlerIndexNormalized`/`fiedlerVectorNormalized` — the `Fiedler.lean` pattern at `L_sym` — with the eigen equation, nonvanishing, `rayleigh = λ₂`) and `fiedlerSweepVector := degreeInvSqrt *ᵥ u` (the pullback with `√D f = u` cancellation, nonvanishing, and the degree-weighted zero-sum through `eigvecOf_ortho_of_mulVec_eq_zero` at `√D·1`, `0 < λ₂` from the delivered connectivity transfer), closed by the headline `fiedler_sweep_cut_normalized`: on connected symmetric nonnegative positive-degree input, an explicit closed superlevel/sublevel cut of the sweep vector itself with `conductance S² ≤ 2 λ₂ (L_sym)` — `cheeger_sweep_cut_normalized` consumed at its first eigenvector input (exactly the regular family's `2λ₂/d` on the cone). Load-bearing on the connectivity transfer, the sweep family's constraint shape, the stretch/pullback cancellation, and `quadForm_eigvecOf_self`. QA: the exact `λ₂(L_sym P₃) = 1` pin (new `≥ 1` side by the `(x₀+x₂)²/√2` sum-of-squares through `secondEval_variational_of_ker`), the theorem instances on P₃/K₂ joined to independent pins, the regular-constant agreement on K₂, the pullback algebra raw pins, the zero-sum hinge raw at the concrete eigenpair. Zero new axioms; spike first in `wip/`. Also recorded in the execution plan: multiway expansion (the family's other named follow-on) is priced as a multi-run program — its easy direction needs a partition-space definition plus genuinely new engine content (centered indicators sum to zero; combinations re-introduce cross-part energy; quotient-matrix/interlacing or iterated assembly routes) — and is deliberately not started by this run.

## 2026-08-26T02:45:28Z — The connectivity transfer: `0 < λ₂(L_sym) ↔ connected` (in delivery)

**Run:** `20260826T024528Z-run-1`  
**Session:** (recorded at terminal entry)  
**Status:** in-progress  
**Milestone:** the irregular-Cheeger family's top named priced follow-on — the connectivity-free `λ₂ > 0` transfer for `normalizedLaplacian`, selected per the empty High/Medium Active table by the center-out policy. Delivering in `VariationalTransfer.lean`: the kernel characterization `normalizedLaplacian_mulVec_eq_zero_iff` (`L_sym *ᵥ x = 0 ↔ ∃ c, x = c • (√D·1)` on connected symmetric nonnegative positive-degree input, through the left-cancellation identity `√D · L_sym = L · D^{-1/2}` and the electrical program's `laplacian_mulVec_eq_zero_iff_exists_const`), `secondEval_normalizedLaplacian_pos_of_connected` (the Fiedler mirror: PSD pin + sorted + multiplicity pin + kernel iff + orthonormality), `secondEval_normalizedLaplacian_eq_zero_of_not_connected` (component indicator → combinatorial kernel → stretched kernel vector → Gram–Schmidt against `√D·1` → `secondEval_le_rayleigh_of_ker`), the packaged iff, and the consumer corollary `cheegerConstant_pos_of_connected` (joining the delivered easy direction — makes the irregular Cheeger pair's positivity content explicit). Load-bearing on the newest engine (`secondEval_le_rayleigh_of_ker`), the kernel characterization, the PSD transfer, and the delivered Cheeger pair. Zero new axioms planned; QA extension of `IrregularCheeger_QA.lean` with the P₃/K₂ positive joins to existing independent pins, the disconnected two-edge negative witness (λ₂ = 0 by two independent routes), and the hconn/hnn fences in proved form. Spike first in `wip/`; prior runs' uncommitted deliveries preserved untouched.

## 2026-08-26T03:54:02Z — The connectivity transfer delivered: `0 < λ₂(L_sym) ↔ connected` (completed)

**Run:** `20260826T024528Z-run-1`  
**Session:** `ses_fc41636b4ffeBvbvj5AvJOcOQC`  
**Status:** completed  
**Milestone:** the irregular-Cheeger family's top priced follow-on — the connectivity-free `λ₂ > 0` transfer for `normalizedLaplacian` — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/ctc_axcheck.lean` on all 31 audited declarations — 7 public + 24 QA: exactly `propext, Classical.choice, Quot.sound`, every one). QA 2280 → 2330 (+50 in `IrregularCheeger_QA.lean`, the file 116 → 166).** With it, algebraic connectivity *is* connectivity in the volume-weighted world: `secondEval_normalizedLaplacian_pos_iff_connected` on every symmetric nonnegative positive-degree graph, through the kernel characterization `normalizedLaplacian_mulVec_eq_zero_iff` (the stretched-constant line), the Fiedler mirror, the disconnected converse, and the Cheeger consumer corollary `cheegerConstant_pos_of_connected` — the delivered pair's positivity content made explicit.

**Changes:** (1) `VariationalTransfer.lean`'s new "The connectivity transfer" section — the algebra layer (`degreeSqrt_mul_normalizedLaplacian`, the kernel-cone lift), the kernel iff (consuming the electrical program's `laplacian_mulVec_eq_zero_iff_exists_const`), `secondEval_normalizedLaplacian_pos_of_connected` (consuming the PSD transfer and both multiplicity pins — the Fiedler mirror load-bearing on all three), the disconnected converse (consuming the newest engine `secondEval_le_rayleigh_of_ker` via the component-indicator Gram–Schmidt route), the packaged iff, and `cheegerConstant_pos_of_connected` (consuming the delivered easy direction). (2) QA +50: the P₃/K₂ positive joins to the file's existing independent spectral pins (non-circular), the kernel iff both directions on irregular input, the disconnected two-edge negative witness with `λ₂ = 0` by two independent routes, the `hconn` fence, and the `hnn` fence on a *connected* signed fixture — at the characterization and at the headline, the latter isolating exactly where nonnegativity enters (the shelf PSD supplier needs `hnn`; the engine and the fixture-specific squares supplier do not). (3) Records: the proposal (follow-on delivered + delivery record with technique findings), `proposals/README.md` (re-ranked candidates), README (2330; module-table clause), the radar (QA sync; axis-3 clause), the scoreboard (two verification rows), the index map (section + 7 rows), backlog item 3, the execution plan, this log.

**Decisive commands and outcomes:** spike first — `lake env lean wip/ctc_spike.lean` and the QA spike green (zero errors/warnings) before any module touched, after the recorded fixes (protected `SimpleGraph.Reachable.refl/trans` constructors; `mul_inv_cancel₀`/`inv_mul_cancel₀` shapes at this pin; the `mulVec_mulVec` rewrite direction; the `show`-unfold of `secondEval` to `evals`; the stale-olean trap — the QA file's first direct elaboration failed on unknown identifiers until the module's explicit target rebuild, exactly the documented remediation). Then `lake env lean` on both changed modules — zero errors/zero warnings (three QA-warnings trimmed to zero); explicit `lake build` targets ✔ (module 2190/2190, QA 2193/2193); `#print axioms` on all 31 — the standard three only, no admitted-axiom contact anywhere; **full `lake build` ✔ (2384/2385, "Build completed successfully") immediately followed by `python3 scripts/check_build_completeness.py` — 107/107 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass after the record sweep; scoreboard regenerated idempotent (md5-stable; **2330/10/0**).

**Verification:** every changed module elaborates directly and sits fresh-certified by the completeness reconciliation. The delivery is unconditional hard crust. QA is load-bearing at four levels: the positive instances joined to *independently produced* spectral pins (the `≤ 1` eigenpair witness and the exact `= 2` predate the connectivity family); the negative witness produced twice by disjoint routes; the fences isolate `hconn` and `hnn` in proved form on fixtures satisfying every other hypothesis; and the `hnn` headline fence exercises that the engine survives without the shelf's PSD supplier — pinning the exact entry point of the nonnegativity hypothesis.

**Remaining risk:** the `2 ≤ card V` hypothesis is carried by both directions exactly as by the family (the one-vertex degenerate case out of scope by design). The Fiedler-mirror route reuses the multiplicity-pin machinery whose own QA history is on record; the disconnected route's component indicator needs classical decidability of reachability (Prop-valued, `classical` in the proof, `Classical.choice` in the axiom audit as expected). QA fixtures are `Fin 2`/`Fin 3`/`Fin 4`; the theorems are size- and weight-general. The remaining priced follow-ons: the volume-weighted sweep-cut extraction, multiway expansion.

**Next handoff:** the Active priority table remains empty (no High, no Medium — every remaining row a Low blocked on a human or technical decision). Next run falls through to the center-out SGT policy with the re-ranked named candidates: the irregular family's remaining priced follow-ons (the volume-weighted sweep-cut extraction; multiway expansion — radar axis 4's remaining absent category), the standing gated candidates (directed-axis rate; magnetic spectral, each gated on a named consumer; a consumer pricing the wide-band minimax filter designs), or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-26T01:31:43Z — Irregular Cheeger hard direction delivered: the volume-weighted pair complete; the proposal COMPLETE (both halves)

**Run:** `20260826T010711Z-run-1` (continuation of `20260825T221207Z-run-1`)  
**Session:** `ses_fc465e735ffeoGnaPCN5GlCAld`  
**Status:** completed  
**Milestone:** `proposals/irregular-cheeger-variational-transfer.md`'s deferred hard half — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/ich_axcheck.lean` on all 40 audited declarations — 16 public + 24 QA: exactly `propext, Classical.choice, Quot.sound`, every one; re-certified after the final source state). QA 2249 → 2280 (+31 in `IrregularCheeger_QA.lean`, the file 85 → 116).** The opening session drafted the full Lean (the `VolumeHardDirection` section of `Cheeger.lean`, the `secondEval_variational_of_ker` engine in `Spectral.lean`, the sweep + headline in `VariationalTransfer.lean`, the QA extension, the spike/axcheck files) but was interrupted before any verification; this continuation run verified, checked, and recorded everything. With both halves delivered, **the full Cheeger pair `φ²/2 ≤ λ₂(L_sym) ≤ 2φ` holds in the volume-weighted measure on every symmetric nonnegative positive-degree graph** — no regularity, no connectivity — the family's last regular-only caveat retired (radar axis 4's held-back absent clause closed; the axis held at 4.5 per protocol with the honest reason recorded: completion of the counted family to its irregular generality, multiway expansion the remaining absent category).

**Changes:** (1) `Cheeger.lean`'s new `VolumeHardDirection` section — the volume arithmetic, the volume median `exists_median_vol` (the same Finset argument with `vol` replacing `card`), minority conductance at volume strength (`boundary_ge_of_minority_vol` — where `min (vol S) (vol Sᶜ) = vol S` is pure `vol_compl` arithmetic), the degree-weighted layer-cake `coarea_core_vol`, the per-part bound `hardDirection_perPart_vol` (the Step-0 finding holding: the regular family's `core_sum_abs_sq_sub_sq` and fused contraction are already degree-weighted and consumed verbatim — no regularity bridge anywhere), the minority parts, the weighted norm split. (2) `Spectral.lean` — `secondEval_variational_of_ker`, the sInf Courant–Fischer form at an arbitrary kernel vector (the delivered `secondEval_le_rayleigh_of_ker` reused as its hard half; the new witness half producing an orthogonal candidate at both `0 < λ₂` and the `λ₂ = 0` double bottom; every future irregular consumer — operator killed by `√D·1`, not `1` — shares it). (3) `VariationalTransfer.lean` (one new import — Cheeger, acyclic) — the weighted inner-product pair, the irregular sweep lemma `cheeger_sweep_normalized`, and the headline `cheeger_lower_bound_normalized` (the sInf engine at the true kernel vector; the sInf set's nonemptiness witnessed by the easy direction's own cut test vector — one test object, both directions of the pair). (4) QA +31: the P₃ volume-median pins (pinned and forced), the K₂ coarea equality raw and as a theorem instance, the sweep instances on K₂ and on P₃'s shared cut test vector (`1/2 ≤ 4/3`), the headline joined to the easy delivery's independently pinned spectral bracket (`φ²/2 = 1/2 ≤ λ₂` with the eigenpair-witness `λ₂ ≤ 1` — non-circular), the K₂ regular recovery at `λ₂ = 2` raw, and the proved-form fences (minority-drop at the full vertex set; nonnegativity-drop on the headline at the signed adjacency with `cheegerConstant = −1` — exactly `hnn` isolated). (5) Records: the proposal (both-halves COMPLETE header + the hard-direction delivery record + re-priced follow-ons), `proposals/README.md` (the Delivered row; the natural-candidates paragraph re-ranked), README (2280; the hard-direction status clause; the module-table row; the radar-snapshot table synced to current scores — a factual repair, drifted since August 22), the radar (axis-4 clause + QA-axis sync 2249 → 2280 + the review date), the scoreboard (two verification rows + the interpretation bullet), `index/map/spectral_graph.md` (the `VolumeHardDirection` rows, the engine row, the hard-direction table), backlog item 3, the execution plan (active block retired), this log.

**Decisive commands and outcomes:** the continuation found the drafted Lean complete and green as drafted — `lake env lean` zero errors on all three public modules and the QA file (only the documented pre-existing warning sets); the `sorry`/`admit` scan clean; `#print axioms` via `wip/ich_axcheck.lean` — all 40 the standard three, no admitted-axiom contact anywhere. During the record sweep, three module/QA docstring dates were corrected to `2026-08-25/26` (the drafting vs verification dates), and the re-verification after those edits exercised the completeness fence exactly as designed: the full `lake build` printed "Build completed successfully" **while the QA module's artifact was stale** (the changed QA source sat outside the default target's rebuild that pass), `check_build_completeness.py` failed at 106/107 with the file listed, and the documented remediation (`lake build Scaffold.QA.SpectralGraph.IrregularCheeger_QA` — a real 2193-target re-elaboration, then a fresh full `lake build` ✔) closed it: **107/107 fresh, 0 stale, 0 missing, exit 0 immediately after the final full build**. `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass after the full record sweep; scoreboard regenerated idempotent (md5-stable; **2280/10/0**); `git status` — only the milestone's intended files plus the prior runs' preserved uncommitted deliveries.

**Verification:** every changed module elaborates directly (zero errors; zero new warnings) and sits fresh-certified in the tree by the completeness reconciliation; the QA module additionally re-elaborated by its explicit target after the final source state. The delivery is unconditional hard crust — no axiom consumed anywhere (`#print axioms`-verified twice, before and after the final source state). QA is load-bearing at four levels: the median/layer-cake layer pinned on genuinely irregular input with the norm split's remainder visible; the coarea equality pinned two ways (raw and as a theorem instance — a mis-shaped instance hypothesis breaks one and not the other); the sweep and headline joined to the easy delivery's *independently produced* witnesses (the same P₃ cut test vector both directions consume, and the eigenpair spectral bracket bounded without the theorem family — non-circular); and the fences isolate exactly `hnn` (nonnegativity) and the minority hypothesis in proved form on fixtures satisfying every other hypothesis.

**Remaining risk:** route provenance for the classical statement is Chung Ch. 2 (proof citation, section-level locator, the standing verify-against-physical-copy caveat; `check_citations` passes — the statements are proved, so no axiom citation applies). The `2 ≤ card V` cardinality hypothesis is carried by both irregular statements exactly as by the regular family (the degenerate one-vertex case is out of scope by design). QA fixtures are `Fin 2`/`Fin 3`; the theorems are size- and weight-general. Priced follow-ons recorded in the proposal: the connectivity-free `λ₂ > 0` transfer for `normalizedLaplacian`, the volume-weighted sweep-cut extraction, multiway expansion.

**Next handoff:** the Active priority table remains empty (no High, no Medium — every remaining row a Low blocked on a human or technical decision). Next run falls through to the center-out SGT policy with the re-ranked named candidates: the irregular-Cheeger delivery's own priced follow-ons (the `λ₂ > 0` transfer; the volume-weighted sweep-cut extraction; multiway expansion), the standing gated candidates (directed-axis rate; magnetic spectral, each gated on a named consumer; a consumer pricing the wide-band minimax filter designs), or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-26T01:07:11Z — Irregular Cheeger hard direction (continuation): verifying the interrupted run's drafted Lean

**Run:** `20260826T010711Z-run-1`  
**Session:** `ses_fc465e735ffeoGnaPCN5GlCAld`  
**Status:** in-progress  
**Milestone:** continuation of the irregular-Cheeger *hard* direction opened by run `20260825T221207Z-run-1` (that session recorded intent and drafted the full Lean — `Cheeger.lean`'s `VolumeHardDirection` section, `secondEval_variational_of_ker` in `Spectral.lean`, `cheeger_sweep_normalized` + `cheeger_lower_bound_normalized` in `VariationalTransfer.lean`, the ~600-line `IrregularCheeger_QA.lean` extension, and the spike/axcheck files in `wip/` — but was interrupted before any verification or records). This run: elaborate every changed module directly, run the `#print axioms` audit, the full build + completeness fence, the script battery, then the record sweep (the proposal's delivery record, `proposals/README.md`, README, radar, index map, backlog item 3, the scoreboard, the execution plan, this log). Zero new axioms planned; the prior runs' uncommitted deliveries preserved untouched.

## 2026-08-25T22:12:07Z — Irregular Cheeger hard direction in delivery: the volume-weighted coarea/median program

**Run:** `20260825T221207Z-run-1`  
**Session:** `ses_fc50c95edffe84we0FbpJNliVX`  
**Status:** in-progress  
**Milestone:** the irregular-Cheeger *hard* direction — the delivered easy direction's own priced follow-on and the top natural candidate named in the standing handoff (`cheegerConstant A ^ 2 / 2 ≤ secondEval (normalizedLaplacian A)` on arbitrary symmetric nonnegative positive-degree graphs, no regularity, no connectivity). Leverage: closes the last "regular graphs only" caveat on the Cheeger family (radar axis 4's held-back half-point) and forces a genuinely load-bearing volume-weighted re-derivation of the coarea/median machinery. Step-0 survey from source: Component A (`core_sum_abs_sq_sub_sq`) and the fused contraction (`sum_edgeWeight_sq_posPart_add_sq_negPart_le`) are already degree-weighted and regularity-free — reused verbatim; regularity enters only through the cardinality median/coarea layer and `sum_deg_mul_eq_of_regular`, so the new work is a volume-median (`exists_median_vol`), minority-conductance at volume strength (`boundary_ge_of_minority_vol` — where `min (vol S) (vol Sᶜ) = vol S` is *pure volume arithmetic*, no regularity bridge), the degree-weighted layer-cake (`coarea_core_vol`), per-part and norm-split analogues, a new general-kernel `secondEval_variational_of_ker` sInf engine in `Spectral.lean` (the delivered `secondEval_le_rayleigh_of_ker` is its hard half, reused), and the f-level sweep plus headline in `VariationalTransfer.lean` beside `cheeger_upper_bound_normalized`. QA extends `IrregularCheeger_QA.lean`: the P₃ hard-bound pin joined to the easy direction's pinned λ₂-bracket and test vector, the K₂ regular recovery, the coarea equality pin, and proved-form fences (minority drop; the signed-weights `!![2,−1;−1,2]` refutation isolating `hnn`). Zero new axioms planned. Baseline verified before editing (full `lake build` ✔ + completeness 107/107 fresh — the prior run's uncommitted resolvent delivery preserved untouched). Spike first in `wip/ich_spike.lean`.

## 2026-08-25T21:03:01Z — Resolvent identity delivered: the Tikhonov filter as π times the shifted inverse; the general-symmetric avoidance layer; the bridge-consumer family closed

**Run:** `20260825T203027Z-run-1`  
**Session:** `ses_fc5670a28ffeLeOt9ffzyl1Ml5`  
**Status:** completed  
**Milestone:** the two priced follow-ons of `proposals/hermitian-calculus-consumer-tikhonov-heat.md` — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/resid_axcheck.lean` on all 17 audited declarations — 6 public + 11 QA — reads exactly `propext, Classical.choice, Quot.sound`, every one). QA 2238 → 2249 (+11 in `FunctionalCalculus_QA.lean` Section G).** This run also closed the prior run's records gap (the magnetic delivery's terminal entry and plan retirement — see the entry below).

**Changes:** the new "The resolvent identity" section of `GraphTheory/FunctionalCalculus.lean` (one new import — Resolvent, no cycle; `Tikhonov.lean` untouched): (1) the *general-symmetric normal equation* under spectrum-avoidance `x + π ≠ 0` — no PSD, no `0 < π`; the delivered PSD statement re-derived from it, shape unchanged; (2) the *general-symmetric resolvent identity* by the calculus route (`cfc_inv` + `Matrix.nonsing_inv_eq_ring_inverse` at the additive layer — no determinant anywhere); (3) the headline `f(L) = π • (L + π•1)⁻¹` by the matrix-algebra route — consuming the Aug-19 resolvent program's `isUnit_det_add_smul_one_of_quadForm_nonneg` (its first FunctionalCalculus consumer) with `laplacian_psd`; (4) the same statement by the calculus route (two technologies, one statement); (5) the consumer corollary `x* = π • ((L + π•1)⁻¹ *ᵥ y)` — the textbook shifted-inverse solve. QA Section G on the shared `K₂` fixture: the raw inverse pinned, both routes delivering the same concrete matrix as Section E's calculus instance, the minimizer three-way join to the hand-solved Gaussian `tik_K2_eq`, the supplier witnessed (`det = 3`), and two fences at the `π = -2` degeneration — the avoidance failure *proved spectral*, the singular inverse pinned to junk zero, the identity refuted at `1/2 ≠ 0`.

**Decisive commands and outcomes:** spike first (`wip/resid_spike.lean` green before any module touched; recurring catches: the QA file's section-scoped `open Tikhonov.QA` must be repeated per section, the spectrum rewrite wants its explicit `IsHermitian` argument at concrete types, matrices are not a `CommMagma` so the smul-slide `M * (π • 1) = π • M` is entrywise, and the QA spike must run after rebuilding the public module's olean); `lake env lean` zero errors/warnings on both changed files; explicit `lake build` targets ✔ (module 2327/2327, QA 2331/2331); `#print axioms` on all 17 — the standard three only; **full `lake build` ✔ (2384/2385 targets, "Build completed successfully") immediately followed by `check_build_completeness.py` — 107/107 fresh, 0 stale, 0 missing, exit 0 — re-run in the same form after the final docstring edits with the same result**; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**2249/10/0**, idempotent by md5); `git status` — the ten intended record/source files plus the `wip/` spikes, nothing else.

**Verification:** both changed files elaborate directly with zero errors/warnings and sit in the default build; module and QA additionally certified by explicit targets. Unconditional hard crust — no axiom consumed anywhere (`#print axioms`-verified), so no conditional-status caveat. QA is load-bearing at three levels: the two proof technologies pinned to one concrete matrix (a wrong `cfc_inv` specialization or junk-inverse misalignment breaks the calculus route while the algebra route stands), the minimizer joined across three constructions (resolvent, eigenbasis calculus, hand-solved Gaussian), and the fences isolate exactly the theorem-relevant hypothesis at the shared degeneration (`hπ` for the headline, avoidance for the general theorem, the failure proved spectral rather than asserted).

**Remaining risk:** the general-symmetric resolvent identity's junk surface — `Ring.inverse` of a non-unit is `0` by convention, and the identity aligns that convention with `Matrix.inv` through `nonsing_inv_eq_ring_inverse`; the avoidance hypothesis keeps both surfaces non-junk simultaneously, and the QA fence exhibits their collision at `π = -2`, but consumers applying the general theorem at merely-symmetric input should note the hypothesis is exactly spectrum-avoidance, nothing weaker. Route provenance: pure hard crust (the consumed calculus is Mathlib's proved `ContinuousFunctionalCalculus`).

**Next handoff:** the Active priority table remains empty (no High, no Medium — every remaining row a Low blocked on a human or technical decision), and the bridge-consumer family plus all its priced follow-ons is now closed. Next run falls through to the center-out SGT policy with `proposals/README.md`'s named candidates: the **irregular-Cheeger hard direction** (the delivered easy direction's priced follow-on — the volume-weighted coarea/median program), the standing gated candidates (directed-axis rate; magnetic spectral, each gated on a named consumer), a named consumer pricing the wide-band minimax filter designs, or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-25T20:30:27Z — Resolvent identity in delivery: the Tikhonov filter as π times the shifted resolvent, with the general-symmetric avoidance layer

**Run:** `20260825T203027Z-run-1`  
**Session:** `ses_fc5670a28ffeLeOt9ffzyl1Ml5`  
**Status:** in-progress (completed; terminal record appended by the same run — see above)  
**Milestone:** the two priced follow-ons of the now-complete consumer stub `proposals/hermitian-calculus-consumer-tikhonov-heat.md` — the resolvent identity `(tikhonovShrinkage π)(L) = π • (L + π•1)⁻¹` and the general-symmetric normal equation (spectrum-avoidance in place of PSD + `0 < π`) — named the top remaining unblocked bridge follow-on in `proposals/README.md`'s standing handoff; selected per the empty High/Medium Active table by the center-out policy. Leverage: a three-layer load-bearing join (the consumer stub's normal equation + the Aug-19 resolvent program's invertibility supplier, its first FunctionalCalculus consumer, + `laplacian_psd`), with Mathlib's `cfc_inv` as the independent second route — two proof technologies, one number, and the textbook `x* = π•(L+πI)⁻¹y` form as a shelf theorem. Plus the records closure for the prior run (below). Zero new axioms planned. Spike first in `wip/`.

**Next:** spike green → the FunctionalCalculus resolvent subsection + QA Section G on the K₂ fixture → full verification ladder → records.

## 2026-08-25T20:30:27Z — Magnetic heat propagator delivered (terminal record, closed retrospectively by the next run)

**Run:** `20260825T180957Z-run-1`  
**Session:** `ses_fc5e9a9cfffeFnvgiHYSs8gayf`  
**Status:** completed (terminal record appended by the next run, `20260825T203027Z-run-1`: that session exited after committing `fac3019` but before writing this terminal entry and retiring the execution plan's Active block — no source gap resulted)  
**Milestone:** `proposals/hermitian-calculus-consumer-magnetic.md` — the bridge's first complex consumer — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/magcfc_axcheck.lean` on all 30 audited declarations — 8 public + 22 accessible QA — reads exactly `propext, Classical.choice, Quot.sound`). QA 2216 → 2238 (`MagneticCalculus_QA` a new file).**

**Changes:** the magnetic section of `GraphTheory/FunctionalCalculus.lean` (one new import — Magnetic; `Magnetic.lean` untouched): `magneticHeat` (the calculus of the delivered `magneticLaplacian` at `x ↦ e^{-t·x}` through Mathlib's `RCLike`-generic `cfc` at 𝕜 = ℂ, hypothesis-free for any directed weights and phases), the general eigen-action engine `cfc_mulVec_eq_smul_of_mulVec_eq_smul` (calculus acts at eigenvalues on EVERY eigenvector, by pure matrix algebra through unitary diagonalization; Mathlib's CFC file lacks it), the entry form, the action interfaces, time zero, and the semigroup through the complex calculus algebra; plus `MagneticCalculus_QA.lean` (the flux-pair `K₂` closed form by two independent routes, the gauge cross-check, the diffusion fence, the zero-phase join to the real `heatKernel`).

**Verification (recorded in commit `fac3019` and the scoreboard's 2026-08-25 rows):** full `lake build` ✔ (2385 targets) immediately followed by `check_build_completeness.py` — 107/107 fresh, 0 stale, 0 missing, exit 0; `lint_axioms` (10), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (2238/10/0). Proposal COMPLETE-headered, `proposals/README.md` delivered row added, README/radar/scoreboard/index updated — all inside the commit.

**Next handoff:** the resolvent identity — the consumer stub's priced follow-on and the top remaining unblocked bridge candidate (now the active milestone).

## 2026-08-25T18:09:57Z — Magnetic heat propagator in delivery: the bridge's first complex consumer

**Run:** `20260825T180957Z-run-1`  
**Session:** `ses_fc5e9a9cfffeFnvgiHYSs8gayf`  
**Status:** in-progress (completed; terminal record appended retrospectively by the next run — see above)  
**Milestone:** `proposals/hermitian-calculus-consumer-magnetic.md` — a gated stub whose gate is now satisfied (the bridge's Steps 1–3 delivered 2026-08-25, the complex-Hermitian half confirmed by QA witness `fcM2c_cfc_id`); selected per the empty High/Medium Active table by the center-out policy as the top natural candidate named in all three standing handoffs, the one-per-delivery indexing-and-pursuit decision recorded in the execution plan at the boundary. Deliverable: the magnetic heat propagator `e^{-tM}` of the delivered `magneticLaplacian` at 𝕜 = ℂ through Mathlib's `RCLike`-generic `cfc` (no second wrapper, per the bridge's Step-0 verdict), its eigenvector action at the complex eigenbasis, and one QA fixture on the flux pair `K₂` at antisymmetric phase π/2 checked against a hand computation — two independent routes. The substantive general lemma: `cfc_mulVec_of_mulVec_eq_smul` (calculus action at ANY eigenvector, by pure matrix algebra through unitary diagonalization — no completeness machinery). Zero new axioms planned. Spike first in `wip/magcfc_spike.lean`; the prior runs' uncommitted deliveries preserved untouched.

**Next:** spike green → the FunctionalCalculus magnetic section + the new `MagneticCalculus_QA.lean` → full verification ladder → records.

## 2026-08-25T17:29:12Z — Heat-as-calculus-instance delivered: the spectral-mapping reconciliation plus the calculus-side semigroup; the consumer stub COMPLETE, both halves

**Run:** `20260825T163517Z-run-1`  
**Session:** `ses_fc640c548ffeP87CROGwiwmNgq`  
**Status:** completed  
**Milestone:** the Heat half of `proposals/hermitian-calculus-consumer-tikhonov-heat.md` (the delivered Tikhonov sibling's own priced follow-on; selected per the empty High/Medium Active table by the center-out policy as the top natural candidate named in all three standing handoffs, with the one-per-delivery rule's indexing-and-pursuit decision recorded at the boundary) — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/heatcfc_axcheck.lean` on all 15 new declarations — 4 public + 11 QA: exactly `propext, Classical.choice, Quot.sound`, every one). QA 2205 → 2216 (+11 in `FunctionalCalculus_QA.lean`'s Section F, no new file). The parent pricing's prediction confirmed: this is the consumer reconciliation with genuine mathematical content — `Heat.lean`'s from-scratch exponential-series stack and Mathlib's `cfc` are two independent proof stacks, and their agreement is now a shelf theorem.**

**Changes:** (1) The "Recovered instances: the heat semigroup" section of `Scaffold/Mathlib/GraphTheory/FunctionalCalculus.lean` (`Heat.lean` untouched per the stub's non-goals; one new import — Heat, no cycle; no umbrella change): the action-equality helper `matrix_eq_of_forall_mulVec_eq` (matrices are their `mulVec` actions, entries recovered at `Pi.single j 1`), the headline `heatKernel_eq_spectralCalc_exp` (`heatKernel A t = spectralCalc (laplacian A) hL (fun x => Real.exp (-(t * x)))` — in effect the spectral mapping theorem for `exp` at real-symmetric matrices, joined at the shared filter-sum shape: `heatKernel_mulVec_eq_sum` against `spectralCalc_mulVec_apply`), and the substantive second layer `spectralCalc_exp_mul` (the semigroup at the exponential family through the generic calculus algebra — `cfc_mul` then `cfc_congr` promoting pointwise `Real.exp_add` from the spectrum, eigenbasis-free) composed into `heatKernel_mul_heatKernel_of_spectralCalc` (a second proof technology for `Heat.lean`'s hypothesis-free `heatKernel_mul_heatKernel`, the `Matrix.exp_add_of_commute` route; the docstring records honestly that this route needs `A.IsSymm` where the original does not, and the original remains primary). (2) `FunctionalCalculus_QA.lean` Section F (+11, on the same `Tikhonov_QA` K₂ fixture as Section E — the two consumer reconciliations pinned against one shared, independently delivered eigenbasis): the closed form `!![(1±e^{-2t})/2]` by two independent routes (`_calculus_route` through the equality theorem + the Section-E master lemma vs `_series_route` through the series engine + the sign-free outer-product pins — no `cfc` anywhere on that route); the semigroup at times `1, 2` by two independent routes plus the numeric pin `(1±e^{-6})/2` and a raw closed-form product check (`Real.exp_add` the only scalar input); time zero preserved through the calculus; eigenmode decay through the calculus action interface at both modes; and the **nontriviality fence** `fc_heat_K2_not_one` — `heatKernel K₂ 1 ≠ 1` by `Real.exp_lt_exp` (`e^{-2} < 1`), refuting any degenerate constant-collapse reading. (3) Records: the proposal (both-halves COMPLETE header + the Heat delivery record with pin-technique findings and post-Heat priced follow-ons), `proposals/README.md` (the Delivered row extended to both halves; the progress paragraph; the closing paragraph now headed by the magnetic heat propagator), README (2216; the status-paragraph clause and the FunctionalCalculus module-table row), the radar (QA axis synced 2205/55 → 2216/55, held 4.0), the scoreboard (two verification rows + the interpretation bullet; regenerated idempotent), `index/map/spectral_graph.md` (+4 declaration rows + the second-consumer reconciliation paragraph), the execution plan, and this log.

**Decisive commands and outcomes:** spike first (`wip/heatcfc_spike.lean` + `wip/heatcfc_qa_spike.lean`, the full routes green before any module touched; the recurring catches: `λ` is not a legal Lean binder name — the spike's first syntax errors; `Real.exp_add` at this pin is `exp (x+y) = exp x * exp y`, so the product-to-sum step needs `← Real.exp_add`; the `fin_cases`-on-`Fin 2` redex trap in the raw product lemma closed by `Matrix.mul_apply`/`Fin.sum_univ_two` pre-rewrites plus per-branch definitional `show`s at numeral indices — the sibling's recorded pin technique holding again; a factor-2 slip in the off-diagonal `linear_combination` certificates caught by ring's residual diagnostic and corrected; the QA spike initially failed to see the new public theorems because it resolved imports from the stale pre-edit `.olean` — rebuild the public module before spiking QA against it); `lake env lean` on both changed files — zero errors, zero warnings each; explicit `lake build` targets ✔ (module 2309/2309, QA 2313/2313); `#print axioms` via `wip/heatcfc_axcheck.lean` on all 15 — the standard three only; **full `lake build` ✔ (2385 targets, "Build completed successfully") immediately followed by `check_build_completeness.py` — 106/106 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass (re-run after the full record sweep); scoreboard regenerated (**2216/10/0**, idempotent by md5 `9e01b98f…` across two runs); `git status` — this milestone's intended files plus the prior runs' preserved deliveries and the `wip/` spikes, nothing else touched.

**Verification:** both changed files elaborate directly with zero errors/warnings and sit in the default build; module and QA additionally certified by explicit targets. The delivery is unconditional hard crust — no axiom consumed anywhere (`#print axioms`-verified), so there is no conditional-status caveat to carry. QA is load-bearing at three levels: the closed form is reached by two genuinely independent proof stacks (a wrong series engine, a wrong `cfc` specialization, or a mismatched eigenbasis convention breaks one route's pin); the semigroup law holds by two independent technologies (calculus algebra vs commuting exponents) agreeing on one number, cross-checked by raw matrix arithmetic; and the fence proves the reconciliation non-vacuous (the kernel at `t = 1` is provably not the identity, so no constant-collapse reading survives).

**Remaining risk:** the equality theorem is proved at the action level (via `matrix_eq_of_forall_mulVec_eq`) rather than by a direct operator-level identity — the mathematical content is the reconciliation of the two expansions, and the record says so rather than overstating the matrix-lift's depth. The calculus-side semigroup needs `A.IsSymm` where the delivered original is hypothesis-free; recorded in the docstring, the original primary. Route provenance: no axiom involved (pure hard crust); the consumed calculus is Mathlib's proved `ContinuousFunctionalCalculus` API. QA fixtures are `Fin 2`; the theorems are size- and weight-general. Priced follow-ons in the proposal: the magnetic heat propagator (the second consumer stub, now the top named candidate), the resolvent identity (`f(L) = π • (L + π•1)⁻¹` under invertibility, one `cfc_inv` step from the delivered normal equation), and the general-symmetric normal equation (spectrum-avoidance hypothesis in place of PSD + `π > 0`).

**Next handoff:** the Active priority table remains empty (no High, no Medium — every remaining row a Low blocked on a human or technical decision). Next run falls through to the center-out SGT policy with `proposals/README.md`'s named candidates: the **magnetic heat propagator** (the second bridge consumer stub — `exp` of the delivered `magneticLaplacian` as the complex calculus at `e^{-tλ}`, complex-half precondition already discharged by the bridge's `fcM2c_cfc_id` witness), the resolvent identity (the consumer stub's own priced follow-on), the irregular-Cheeger *hard* direction, the standing gated candidates (directed-axis rate; magnetic spectral; a consumer pricing the wide-band minimax filter designs), or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-25T16:35:17Z — Heat-as-calculus-instance in delivery: the consumer stub's second equality theorem plus a calculus-side semigroup law

**Run:** `20260825T163517Z-run-1`  
**Session:** `ses_fc640c548ffeP87CROGwiwmNgq`  
**Status:** in-progress (superseded by the completed entry above, same run)  
**Milestone:** the Heat half of `proposals/hermitian-calculus-consumer-tikhonov-heat.md` (the delivered Tikhonov sibling's own priced follow-on; the one-per-delivery rule's indexing-and-pursuit decision made this run and recorded in the execution plan — selected per the empty High/Medium Active table by the center-out policy as the top natural candidate named in all three standing handoffs) — the equality theorem `heatKernel A t = spectralCalc (laplacian A) hL (fun λ => Real.exp (-(t * λ)))`, the bridge's falsifiability test at the second real consumer and the reconciliation the parent pricing predicted would be a genuine proof (the from-scratch exponential-series expansion vs Mathlib's CFC, not a definitional identity), plus the substantive second layer: the semigroup law `f_s(L) * f_t(L) = f_{s+t}(L)` re-derived through the generic calculus algebra (`cfc_mul`/`cfc_congr` at `Real.exp_add`) — a second route to the delivered `heatKernel_mul_heatKernel`. Zero new axioms planned (pure hard crust). QA Section F on the `Tikhonov_QA` K₂ fixture: two routes to the closed form `!![(1±e^{-2t})/2]` (calculus vs series engine), the two-route semigroup, the time-zero calculus identity, and the nontriviality fence `heatKernel K₂ 1 ≠ 1`. Spike first in `wip/`; the prior runs' uncommitted deliveries preserved untouched (worktree carries only their files at start).

**Next:** spike green → the FunctionalCalculus heat section + QA Section F → full verification ladder → records.

## 2026-08-25T15:25:23Z — Tikhonov-as-calculus-instance delivered: the equality theorem plus the eigenbasis-free normal equation; the Tikhonov half of the consumer stub COMPLETE

**Run:** `20260825T145722Z-run-1`  
**Session:** `ses_fc697f241ffecVlI8L7N4uUzat`  
**Status:** completed  
**Milestone:** `proposals/hermitian-calculus-consumer-tikhonov-heat.md` (the first of the two bridge-consumer stubs unblocked by the 2026-08-25 Hermitian-functional-calculus-bridge delivery; the stub's Tikhonov-vs-Heat choice discharged by the parent proposal's recorded Step-0 pricing — Tikhonov's reconciliation gap smaller) — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/tikcfc_axcheck.lean` on all 19 new declarations — 3 public + 16 QA: exactly `propext, Classical.choice, Quot.sound`, every one). QA 2189 → 2205 (+16 in `FunctionalCalculus_QA.lean`'s Section E, no new file). The bridge's named falsifiability test at a real consumer now carries weight: the eigenbasis-defined Tikhonov minimizer is the calculus at the shrinkage function, and the normal equation has two independent proof routes.**

**Changes:** (1) The "Recovered instances" section of `Scaffold/Mathlib/GraphTheory/FunctionalCalculus.lean` (`Tikhonov.lean` untouched per the stub's non-goals; no new imports, no umbrella change): `continuousOn_of_finite_real_spectrum` (every function continuous on a matrix's finite real spectrum, via `Finite.instDiscreteTopology` — the supplier every future generic-CFC consumer needs, since `cfc_cont_tac`'s `fun_prop` cannot discharge spectrum-restricted continuity of spectral-data functions), the headline `tikhonovMinimizer_eq_spectralCalc_mulVec` (`x* = f(L) *ᵥ y` at `f = tikhonovShrinkage π`, **hypothesis-free** — the proof the definition identity the parent pricing predicted, the bridge's action form having been stated in exactly the minimizer's filter-sum shape), and the substantive second layer `add_smul_one_mul_spectralCalc_tikhonovShrinkage` — the normal equation `(L + π•1) * f(L) = π • 1` **re-derived through Mathlib's generic CFC algebra** (`cfc_add_const`/`cfc_id'`/`cfc_mul`/`cfc_congr`/`cfc_const` via `Matrix.IsHermitian.cfc_eq`; the pointwise `shrink π λ · (λ+π) = π` promoted from the spectrum by `cfc_congr`, PSD + `0 < π` keeping the division non-junk at spectral points) — an eigenbasis-free route to a statement the shelf had only through the eigenbasis expansion. (2) `FunctionalCalculus_QA.lean` Section E (+16, on the `Tikhonov_QA` K₂ fixture, now imported): the sign-free structure pins (kernel outer products all `1/2`; `λ = 2` outer products `±1/2` — no basis-orientation choice surviving), the arbitrary-`f` master entrywise lemma `fc_lapK2_calc`, the calculus instance pinned to `!![2/3, 1/3; 1/3, 2/3]` at `π = 1`, **the reconciliation witnessed numerically** (through the equality theorem the calculus routes `![1,0]` to `![2/3, 1/3]`, exactly the hand-solved Gaussian value `tik_K2_eq` pinned in the original Tikhonov delivery — two constructions, one number), the normal equation by two independent routes (`_calculus` through the public chain vs `_hand` through the pinned hand-solved system) plus a raw matrix-arithmetic check, the kernel-mode action instantiation, and the **fence at `π = -2`** (the junk shrinkage `0` at the spectral point `2 = -π` drives `f(L)` to the pure kernel average; the hypothesis-free normal equation refuted in proved form at the `(-1) ≠ 0` entry — `0 < π` load-bearing). (3) Records: the proposal (COMPLETE header + delivery record with the pin-technique list and priced follow-ons — the Heat sibling, the resolvent identity, the general-symmetric normal equation), `proposals/README.md` (the Delivered row; the progress paragraph; the natural-candidates closing paragraph now headed by the Heat half), README (2205; the FunctionalCalculus module-table row's consumer clause), the radar (QA axis synced 2189/55 → 2205/55, held 4.0), the scoreboard (two verification rows + the interpretation bullet; regenerated idempotent), `index/map/spectral_graph.md` (the FunctionalCalculus section: +3 declaration rows + the reconciliation paragraph), this plan's sibling `docs/EXECUTION_PLAN.md`, and this log.

**Decisive commands and outcomes:** spike first (`wip/tikcfc_spike.lean` then `wip/tikcfc_qa_spike.lean`, the full routes green before any module touched — the recurring fixes are the proposal's pin-technique list: generic-CFC rewrites require explicit `IsSelfAdjoint` ascriptions (`have hsa : IsSelfAdjoint M := hherm`), never the `IsHermitian` proof, or `rw` silently fails to match the instance argument — the goal-side `cfc` terms elaborate at `IsSelfAdjoint` via instance search; `cfc_add_const`'s `ha`/`hf` auto-params *do* resolve (aesop), only the continuity supplier needs passing; the `cfc_congr` EqOn proof must `show` the beta-redex, and the product order `(λ+π) * (π/(λ+π)) = π` is `mul_div_cancel₀`, not `div_mul_cancel₀`; `algebraMap ℝ (Matrix) π = π • 1` entrywise via `Matrix.algebraMap_matrix_apply` (no `Matrix.smul_one` at this pin); `ContinuousOn` is not defeq-visible to `exact continuous_of_discreteTopology` — go through `continuousOn_iff_continuous_restrict`; `mulVec_mulVec` at this pin associates `(M *ᵥ N) *ᵥ v` (column-family reading), not `M *ᵥ (N *ᵥ v)` — the vector-level composition needed an entrywise `Finset.sum_comm` associativity step; `fin_cases` on `Fin 2` binders leaves the known beta-redexes, closed by per-branch definitional `show`s; outer-product pins stated in raw `v a * v b` form (not `^2`) so `mul_assoc`-then-rewrite matches `(f λ * v a) * v b`; `tikhonovShrinkage_eq_one_iff` consumed through `.mpr rfl` with the expected type ascribed; `(hπ : 0 < π)` arguments ascribed `(by norm_num : (0:ℝ) < 1)` since `π` is implicit); `lake env lean` on both changed files — zero errors, zero warnings each; explicit `lake build` targets ✔ (module 2301/2301, QA 2305/2305); `#print axioms` via `wip/tikcfc_axcheck.lean` on all 19 — the standard three only; **full `lake build` ✔ (2385 targets, "Build completed successfully") immediately followed by `check_build_completeness.py` — 106/106 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass (re-run after the full record sweep); scoreboard regenerated idempotent (md5-stable); `git status` — exactly this milestone's intended files. The build-completeness fence earned its keep mid-verification: a `touch` of the module during linter-note triage tripped the STALE check exactly as calibrated, remediated by the documented artifact-removal + re-elaboration route before the recorded full build.

**Verification:** both changed files elaborate directly with zero errors/warnings and sit in the default build; module and QA additionally certified by explicit targets. The delivery is unconditional hard crust — no axiom consumed anywhere (`#print axioms`-verified), so there is no conditional-status caveat to carry. QA is load-bearing at three levels: the reconciliation witness pins two independently-built objects to one hand-solved number (a wrong calculus specialization, eigenbasis convention, or minimizer formula breaks the `2/3`/`1/3` pins); the normal equation's two proof routes agree on a nontrivial statement (the calculus-algebra route would fail if `cfc_mul`/`cfc_congr` were misapplied, the hand route if the pinned system were wrong); and the fence proves the `0 < π` hypothesis materially necessary (the junk-division mechanism exhibited, not merely an unused hypothesis).

**Remaining risk:** the equality theorem's proof is a definitional identity — by design and as priced (the bridge's action form was stated in the minimizer's shape); the mathematical content carried by this delivery is the calculus-algebra normal equation and the QA reconciliation, and the record says so rather than overstating the equality's depth. Route provenance: no axiom involved (pure hard crust); the generic CFC algebra consumed is Mathlib's proved `ContinuousFunctionalCalculus` API. QA fixtures are `Fin 2`; the theorems are size- and weight-general. The Heat half (expected a genuine proof through the `NormedSpace.exp` route), the resolvent identity (`f(L) = π • (L + π•1)⁻¹`), and the general-symmetric normal equation (spectrum-avoidance hypothesis in place of PSD) are priced follow-ons in the proposal, each needing its own authorization per the one-shape-per-proposal discipline.

**Next handoff:** the Active priority table is empty again (no High, no Medium). Next run falls through to the center-out SGT policy with `proposals/README.md`'s named candidates: the **Heat half** of the consumer stub (the sibling's own priced follow-on, needing its own indexing-and-pursuit decision), the magnetic heat propagator (the second consumer stub, complex-half precondition already discharged), the irregular-Cheeger *hard* direction, the standing gated candidates (directed-axis rate; magnetic spectral; a consumer pricing the wide-band minimax filter designs), or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-25T14:57:22Z — Tikhonov-as-calculus-instance in delivery: the bridge consumer stub's equality theorem plus a calculus-side normal equation

**Run:** `20260825T145722Z-run-1`  
**Session:** `ses_fc697f241ffecVlI8L7N4uUzat`  
**Status:** in-progress (superseded by the completed entry above, same run)  
**Milestone:** `proposals/hermitian-calculus-consumer-tikhonov-heat.md` (the first of the two bridge-consumer stubs unblocked by the 2026-08-25 Hermitian-functional-calculus-bridge delivery; the stub's Tikhonov-vs-Heat choice discharged by the parent proposal's own recorded Step-0 pricing — Tikhonov's reconciliation gap smaller) — the equality theorem `tikhonovMinimizer A hA π y = spectralCalc (laplacian A) hL (tikhonovShrinkage π) *ᵥ y` (the bridge's falsifiability test at a real consumer: the eigenbasis-defined minimizer is the calculus at `π ↦ π/(λ+π)`), plus the substantive second layer: the normal equation `(L + π•1) * spectralCalc L hL (tikhonovShrinkage π) = π • 1` derived through the generic CFC algebra API (`cfc_mul`/`cfc_add_const`/`cfc_congr` through `cfc_eq`) — a proof route independent of the shelf's eigenbasis machinery, two routes to one nontrivial statement. Zero new axioms planned (pure hard crust). QA on the `Tikhonov_QA` `K₂` fixture: the calculus instance pinned to `!![2/3, 1/3; 1/3, 2/3]` entrywise sign-free, the reconciliation witnessed against the hand-solved `![2/3, 1/3]`, and the `π`-hits-`-λ` fence proving the hypothesis-free normal equation false (the PSD/`0 < π` interaction load-bearing). Spike first in `wip/`; the prior runs' committed deliveries untouched (worktree clean at start).

**Next:** spike green → the FunctionalCalculus section + `FunctionalCalculus_QA` extension → full verification ladder → records.

## 2026-08-25T11:53:30Z — Hoffman independence bound delivered: the Expander Mixing Lemma's first theorem consumer; the proposal COMPLETE

**Run:** `20260825T064753Z-run-1`  
**Session:** `ses_fc8534c4cffeOO2egg7VeT55Ty`  
**Status:** completed  
**Milestone:** `proposals/expander-independence-number-bound.md` (found committed in `4e60ce6` but never indexed — the unindexed-proposal gap class; triaged per the previous run's explicit standing-handoff instruction, header priority Medium-High, indexed as the Active table's only High row, pursued per priority item 0) — **Steps 0+1 delivered in one run, pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/hoffman_axcheck.lean` on all 26 new declarations — 4 public + 22 QA: exactly `propext, Classical.choice, Quot.sound`, every one). QA 2152 → 2173 (+21 in `Expander_QA.lean`'s Step-5 section, no new file). The strategy's load-bearing-growth principle executed verbatim: `expander_mixing_lemma` — 24 declarations of proved discrepancy machinery with zero theorem consumers — now carries weight through its first consumer, and both of the proposal's open Step-0 questions are answered as proved facts rather than assumptions.**

**Changes:** (1) Section 8 of `Scaffold/Mathlib/GraphTheory/Expander.lean` (no new imports, no umbrella change): `IsIndependentSet` (diagonal-inclusive — `∀ i ∈ S, ∀ j ∈ S, A i j = 0`, the looped-graph reading that collapses `edgeWeight A S S = 0` in one `Finset.sum_eq_zero`, defined natively over `WAdj`/`Finset` per the proposal's Step-0 finding that the pinned Mathlib has no independence-number machinery), the collapse lemma, `deg_eq_zero_of_isIndependentSet_univ` (the whole-graph corner: independence of `univ` forces `deg ≡ 0`), and the headline `hoffman_independence_bound` — `|S| ≤ μ·n/(d+μ)` for every independent set at exactly the mixing lemma's own hypothesis set plus `hd : 0 < d` (consumed only through `0 < d + μ`, noted in the docstring). (2) `Expander_QA.lean`'s Step-5 section (+21): both classical tight cases attained with equality at the Step-4-exact `μ` pins (`C₄`'s opposite pair `2 = 2·4/(2+2)` — the bipartite Hoffman-equality regime; `K₃`'s singleton `1 = 1·3/(2+1)` — the clique regime, the bound pinning the maximum independent set exactly on the least-expanding fixture), the `∅` degenerate instance, the whole-graph fence pair (raw refutation + the corner-lemma join `2 = 0` false), the independence-hypothesis isolation (every other hypothesis verified on `C₄`, conclusion refuted at `univ`, the collapse mechanism pinned blocked via the internal cut weights `8 ≠ 0`/`2 ≠ 0` — the half set's conclusion holding numerically being exactly why the fence lives at the mechanism), and the **`d = 0` fence** on the new `2×2` zero-adjacency fixture: every other hypothesis verified *including* independence of `univ` and `μ = 0` exactly (the whole Laplacian spectrum pinned zero through the eigen-action `0 = λ • v` at unit eigenvectors + `evals_mem_eigvalOf`), the division-form conclusion `2 ≤ 0·2/(0+0) = 0` refuted — exactly `hd` isolated, the Step-0 verdict-3 answer in proved form. (3) Records: the proposal (COMPLETE + delivery record with the Step-0 verdicts, pin-technique list, and priced follow-ons), `proposals/README.md` (High row → Delivered; progress paragraph), README (2173; the status-paragraph clause; the module-table row), the radar (QA axis 2152/54 → 2173/54 held 4.0; the axis-4 Hoffman clause held 4.5; two factual drift repairs found mid-sweep: the axiom-minimization row-head's stale `9` → `10` with the missing 2026-08-24 primitive-power up-step restored to the trend chain, and backlog item 3's stale "admitted Cheeger lower bound" corrected to proved-2026-08-23), the scoreboard (all five verification rows + the interpretation bullet; regenerated idempotent 2173/10/0), `index/map/spectral_graph.md` (the Expander section header + 4 declaration rows), backlog item 3, the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/hoffman_spike.lean`, several rounds to green before any module touched — the recurring fixes are the proposal's pin-technique list: `Real.sqrt_mul_self` not `Real.mul_self_sqrt` at this pin; `0 - x` inside `abs` needs `zero_sub`+`abs_neg` not `sub_zero`; `0 < d + μ` from `0 < d`, `0 ≤ μ` via `linarith` (no `add_pos_nonneg`); `div_le_iff₀.mp` leaves the multiplied denominator for one `div_mul_cancel₀ _ hn.ne'`; Fin-literal set membership driven by `rcases hi with rfl | rfl` (the Exhaustive_QA pattern) — variable-index membership simp strands `(fun i => i) ⟨0, ⋯⟩` beta-redexes neither `simp` nor `decide` close; `(card : ℝ) = k` goals decide the ℕ equation then `exact_mod_cast`; rewriting a matrix def under proof-valued args fails on dependent motives — the durable route is a `funext` entrywise `have`; `Matrix.sub_apply` needs a definitional `show (degreeMatrix A - A) i j = 0` first); `lake env lean` on both changed modules — zero errors/warnings; `lake build Scaffold.Mathlib.GraphTheory.Expander` ✔ (2009/2009), `lake build Scaffold.QA.SpectralGraph.Expander_QA` ✔ (2010/2010); `#print axioms` via `wip/hoffman_axcheck.lean` — the standard three only, all 26; **full `lake build` ✔ (2264 targets, "Build completed successfully") immediately followed by `check_build_completeness.py` — 104/104 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (**10**, unchanged), `check_citations`, `check_markdown_links` pass (re-run after the full record sweep); scoreboard regenerated idempotent (md5-stable); `git status` — this milestone's intended files plus the prior runs' preserved deliveries, the `wip/` spikes, and (see remaining risk) the mid-run-appeared untracked Hermitian artifacts left as found.

**Verification:** both changed modules elaborate directly with zero errors/warnings and sit in the default build; the QA module is additionally certified by its explicit build target. The delivery is unconditional hard crust — no axiom consumed anywhere (`#print axioms`-verified), so there is no conditional-status caveat to carry. QA is load-bearing at every mandated level: the two tight cases attain the bound with equality at the exact `μ` pins (a wrong constant, endpoint, or hypothesis shape in either the mixing lemma or the corollary breaks the equalities `2 = 2` and `1 = 1` at the pinned values); the fences isolate exactly `hind` (conclusion refuted at `univ` with all else verified and the collapse mechanism numerically blocked) and exactly `hd` (the zero-adjacency isolation with the spectrum independently pinned zero); and the `∅`/whole-graph degenerate boundaries are proved witnesses, not avoided divisions.

**Remaining risk:** route provenance for the classical statement is docstring-level (Hoffman via Brouwer–Haemers *Spectra of Graphs*, in the mixing-lemma corollary form of the module's existing [AC]/[HLW]/[V] citations) — a proved theorem, so no axiom citation applies; section-level locator with the standing physical-copy caveat. The per-set form bounds the independence number without defining `α` (no independence-number packaging — one `Finset.exists_max_image` away, gated on a consumer naming it, per the proposal's priced follow-on). The spectral-diameter EML corollary remains out of scope exactly as the proposal prices it. QA fixtures are `Fin 2`/`Fin 3`/`Fin 4`; the theorems are size- and weight-general. **Observed mid-run (not this run's artifacts, left untouched and unindexed):** three untracked proposals — `hermitian-functional-calculus-bridge.md`, `hermitian-calculus-consumer-magnetic.md`, `hermitian-calculus-consumer-tikhonov-heat.md` — appeared in the worktree during this run (absent from the run-start `git status` and initial `proposals/` listing), together with a matching uncommitted edit to `docs/8_MATHLIB_COVERAGE_MAP.md`'s spectral-linear-algebra row (a Hermitian-functional-calculus correction citing the bridge proposal). The next run should triage them per the unindexed-proposal precedent.

**Next handoff:** the Active priority table is empty again (no High, no Medium). Next run falls through to the center-out SGT policy: **triage the three untracked Hermitian-calculus proposals** (this run's recorded observation — same gap class as `expander-independence-number-bound.md` and `irregular-cheeger-variational-transfer.md` before it), the irregular-Cheeger *hard* direction (the delivery's priced follow-on), the standing gated candidates (directed-axis rate; magnetic spectral; a consumer pricing the wide-band minimax filter designs), or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-25T06:49:30Z — Hoffman independence bound in delivery: Expander.lean's first theorem consumer

**Run:** `20260825T064753Z-run-1`  
**Session:** `ses_fc8534c4cffeOO2egg7VeT55Ty`  
**Status:** in-progress  
**Milestone:** `proposals/expander-independence-number-bound.md` (found committed in `4e60ce6` but never indexed — the unindexed-proposal gap class; triaged per the previous run's explicit standing-handoff instruction, header priority Medium-High, indexed as the Active table's only High row, pursued per priority item 0) — Steps 0+1: the Hoffman ratio bound `|S| ≤ μ·n/(d+μ)` for every independent set of a `d`-regular nonnegative symmetric network under exactly `expander_mixing_lemma`'s `μ` hypothesis, the proved-lemma's **first theorem consumer** (zero consumers confirmed by the proposal's `measure_load_bearing.py` evidence). Zero new axioms. Step-0 verdict recorded in the execution plan: diagonal-inclusive independence definition (the reading that collapses `edgeWeight A S S = 0` in one `Finset.sum_eq_zero`); whole-graph corner fenced as a lemma; `0 < d` proved NOT free (all-zero-adjacency counterexample with every other hypothesis verifiable — λ pins via eigen-action + `evals_mem_eigvalOf`) and therefore an explicit hypothesis with its own fence. QA plan: `C₄` and `K₃` both attain the bound with equality (the bipartite and clique tight cases), the `∅` degenerate instance, the whole-graph and non-independent fences, the `d = 0` fence. Spike first in `wip/hoffman_spike.lean`; prior runs' uncommitted deliveries preserved untouched.

**Next:** spike green → `Expander.lean` §8 + `Expander_QA.lean` Step 5 → full verification ladder → records.

## 2026-08-25T02:19:00Z — Magnetic Laplacian delivered: the directed-native Hermitian operator, energy identity, PSD, and gauge characterization; the proposal COMPLETE

**Run:** `20260825T021040Z-run-1`  
**Session:** `ses_fc951ab94ffeIK4PvF8Uc6TxqV`  
**Status:** completed  
**Milestone:** `proposals/magnetic-laplacian.md` (opened by run `20260825T001310Z-run-1`, completed by this continuation run) — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/mag_axcheck.lean` on all 39 accessible declarations — 14 public module + 8 QA fixture defs + 16 public QA theorems: `propext, Classical.choice, Quot.sound` only, every one). QA 2051 → 2067 (`Magnetic_QA` a new file at 16 by the generator metric, 30 declarations total). The shelf's first complex-valued object and the directed axis' third spectral toolkit: the energy/gauge layer that backlog item 8's named external consumer ("directed community detection via the magnetic Laplacian") needs.**

**Changes:** (1) `Scaffold/Mathlib/GraphTheory/Magnetic.lean` (drafted by run 1, verified green as-drafted by this run): `symDeg`, `magneticMatrix`, `magneticLaplacian` (`M := D_sym − ½(W + Wᴴ)` at the Crucoli–Pérez–Bungert–Van Mieghem directed convention — route provenance in the docstring, statements proved), `hermQuadForm`; `magneticLaplacian_isHermitian` (**hypothesis-free**), the cone lemma, the action interface, **the magnetic energy identity** (hypothesis-free), realness, **PSD** on nonnegative weights, **the balanced-potential gauge characterization** (frustrated cycle ⇒ trivial kernel — flux localization at form level), and the Θ = 0 / symmetric-cone agreements with the classical Laplacian. (2) `Scaffold/QA/SpectralGraph/Magnetic_QA.lean` (drafted by run 1; this run's verification found three first-pass errors — two redundant `match` alternatives and **one false numeric pin**: the zero-phase energy of `![1,−1]` on `K₂` drafted as `2` where the true value is `4`; `norm_num` had correctly reduced the goal to `False` — fixed in place, the statement corrected to the true value): all four mandated sections delivered (asymmetric-flux positive witnesses with the conjugate-pair entries `1 ± I/2` and the energy pin `5`; the frustrated-vs-consistent kernel pair; the classical bridge with the antipodal-outside pin at exactly `4`; the nonnegativity fence at `−1 < 0` with exactly `hA` isolated). (3) The umbrella `Scaffold.lean` import + doc clause. (4) Records: the proposal (COMPLETE + delivery record with the pin-technique list and priced follow-ons), `proposals/README.md` (the Delivered row; the progress paragraph — the magnetic slice retired, the magnetic *spectral* layer the new gated candidate), README (2067; the stale axiom-count cell 9 → 10 fixed to match the scoreboard authority; the status-paragraph clause; the module-table row), the radar (QA axis 2051/52 → 2067/53, held 4.0), the scoreboard (four verification rows + the interpretation bullet; regenerated idempotent 2067/10/0), `index/map/spectral_graph.md` (the Magnetic section + 15 declaration rows), backlog item 8 (the seventh update), the execution plan, this log.

**Decisive commands and outcomes:** `lake env lean Scaffold/Mathlib/GraphTheory/Magnetic.lean` — zero diagnostics (the interrupted draft was mathematically sound); `lake env lean Scaffold/QA/SpectralGraph/Magnetic_QA.lean` — three errors (2× redundant alternative at the `Fin 2` diagonal `match` arms; 1× unsolved goals reduced to `False` by `norm_num` at the false `= 2` pin), fixed by deleting the duplicated arms and correcting the statement to `= 4` with the docstring arithmetic repaired, then zero diagnostics; `lake build Scaffold.Mathlib.GraphTheory.Magnetic` ✔, `lake build Scaffold.QA.SpectralGraph.Magnetic_QA` ✔ (2192/2192), `lake build Scaffold` ✔ (**2264 targets, "Build completed successfully"**; zero warnings in the changed modules — the log's only Scaffold diagnostics the documented pre-existing `Normalized.lean` congr-1 and `Derived/ProjectorDrift.lean` unused-variable notes in untouched modules); `#print axioms` via `wip/mag_axcheck.lean` — the standard three only, all 39; `lint_axioms` (**10**, unchanged), `check_citations`, `check_markdown_links` pass (re-run after all record edits); scoreboard regenerated idempotent; `git status` — only this milestone's intended files.

**Verification:** both changed modules elaborate directly with zero errors/warnings and the public module is linked into the full default build; the QA module is additionally certified by its explicit build target. The delivery is unconditional hard crust — no axiom is consumed anywhere (`#print axioms`-verified), so there is no conditional-status caveat to carry. QA is load-bearing at all four mandated levels: the asymmetric witnesses pin the hypothesis-free theorems on genuinely directed input with genuinely complex phases (a wrong convention or energy identity contradicts the pinned conjugate-pair entries and the `5` pin); the kernel pair exhibits the gauge characterization *discriminating* (the same flux trivial on the triangle, surviving on `K₂` — a wrong iff direction or a wrong edge condition breaks one side); the classical bridge joins the zero-phase operator to the mapped `laplacian` entrywise (a wrong symmetrized-degree or coupling convention contradicts the pinned classical entries); and the fence refutes the hypothesis-free PSD conclusion in proved form with the nonnegativity hypothesis exactly isolated. The continuation run's own verification earned its keep: the false numeric pin is precisely the failure mode numeric QA exists to catch, and it was caught before anything was recorded as delivered.

**Remaining risk:** route provenance for the convention is section-level (arXiv:2202.02497 §2) with the standard verify-against-physical-copy caveat — no axiom involved, so nothing conditional. The gauge→component-constant transport at Θ = 0 exists only as QA fixtures, not a module-level walk induction (priced follow-on). QA fixtures are `Fin 2`/`Fin 3` with phases in `{0, π/2, π}`; the theorems are size- and phase-general. The complex spectral layer (eigenvalues of `M`, magnetic Cheeger, synchronization functionals) is deliberately out of scope — priced follow-on gated on a consumer naming a bound.

**Next handoff:** the Active priority table is empty again (no High, no Medium — every remaining row a Low blocked on a human or technical decision). Next run falls through to the center-out SGT policy: the directed-axis *rate* layer (gated on a separate admission + a named consumer), the magnetic *spectral* layer (gated on a consumer naming a bound), a named consumer pricing the wide-band minimax filter designs, the sweep-cut priced follow-ons, or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-25T02:10:40Z — Magnetic Laplacian delivery resumed: verification and record completion

**Run:** `20260825T021040Z-run-1`  
**Session:** `ses_fc951ab94ffeIK4PvF8Uc6TxqV`  
**Status:** in-progress  
**Milestone:** continuation of `proposals/magnetic-laplacian.md` (run `20260825T001310Z-run-1` recorded intent and drafted `GraphTheory/Magnetic.lean` + `Magnetic_QA.lean` but was interrupted before verification): this run elaborates both modules, wires the umbrella import, runs the full check battery, and completes the record sweep. Findings so far: the module elaborates green with zero diagnostics; the QA had three first-pass errors (two redundant match alternatives; one false numeric pin — the zero-phase energy of `![1,-1]` on `K₂` is `4`, not the drafted `2`; `norm_num` correctly refuted the drafted statement) — fixed in place, QA now green. Zero new axioms (count stays 10). Next: umbrella import, explicit builds, `#print axioms` audit, scripts, records.

## 2026-08-25T00:13:10Z — Magnetic Laplacian in delivery: the directed-native Hermitian operator, energy identity, PSD, and gauge characterization

**Run:** `20260825T001310Z-run-1`  
**Session:** `ses_fc9bf6f18ffet709xZMLkB4gSi`  
**Status:** in-progress  
**Milestone:** `proposals/magnetic-laplacian.md` (new this run) — backlog item 8's reserved "further, separate slice" and the strategy's 2026-08-19 scope-decision namesake: the magnetic Laplacian `M := D_sym − ½(A∘e^{iΘ} + (A∘e^{iΘ})ᴴ)` as the shelf's first complex Hermitian object, with the hypothesis-free Hermitian/energy layer (the Hermitian-part convention makes symmetry structural, the `directedNormalizedLaplacian` precedent), PSD and the gauge characterization `x*Mx = 0 ↔ x_u = e^{iΘ_uv} x_v on positive edges` (the balanced-potential condition that directed community detection consumes), and the Θ = 0 agreement with the complexified classical Laplacian (the join with the real shelf). Selected per the empty High/Medium Active priority table by the center-out policy: every alternative standing candidate is gated on an admission, a named consumer, or a human/technical decision; this one is named open. Zero new axioms (pure finite algebra — no complex spectral theorem needed at this slice); QA planned at four sections including the frustrated-vs-consistent-flux kernel pair (a π-phase edge on `K₃` forces the kernel trivial; the same flux on `K₂` leaves an antipodal kernel vector — the gauge characterization's content) and the nonnegativity fence (symmetric signed input refutes PSD, `hnonneg` isolated). Spike first in `wip/mag_spike.lean`; the previous runs' uncommitted deliveries preserved untouched.

## 2026-08-24T19:47:48Z — Resistance metric delivered: the maximum principle, definiteness, and the triangle inequality; the proposal COMPLETE

**Run:** `20260824T192530Z-run-1`  
**Session:** `ses_fcaca998affeXd1neL0pVj6Wgf`  
**Status:** completed  
**Milestone:** `proposals/resistance-metric.md` (new this run) — **Steps 0+1 delivered in one run, pure hard crust, zero new axioms (count stays 9; `#print axioms` via `wip/rm_axcheck.lean` on all 5 public + 28 QA declarations: `propext, Classical.choice, Quot.sound` only, every one). QA 1971 → 1999 (`ResistanceMetric_QA` a new file at 28). Backlog item 7's two named non-gated residuals are closed, and with the proved nonnegativity/symmetry/self-distance laws `effectiveResistance` is a genuine metric on every connected network — the classical resistance distance.**

**Changes:** (1) the new "resistance metric" section of `GraphTheory/Electrical.lean` (no new imports; module header updated): `laplacian_mulVec_eq_single_sub_single_le_max` (the **maximum principle** — at a max-point outside the boundary the diffusion form `∑ j, A x j (f x − f j) = 0` is a sum of nonnegative terms, so the max propagates across every positive-weight edge and a walk induction floods the connected graph; the kernel-characterization argument run at an inequality), `_min_le` (the min half at the negated demand), `effectiveResistance_pos_of_ne` (Dirichlet at the indicator `e u`: energy `∑_{j≠u} A u j > 0` by connectivity, voltage `1`), `effectiveResistance_eq_zero_iff` (the definiteness residual), and `effectiveResistance_le_add` (the **triangle**: `f + g` demand superposition, polarization at `t = −1`, cross term `f v − f w ≤ 0` by confinement + positivity). The Step-0 survey's finding is priced into the route: the eigenbasis route yields only the root-triangle — `R` is a squared Euclidean distance there and the cross term is what the sharp form must cancel, so the maximum principle is the crux. (2) `Scaffold/QA/SpectralGraph/ResistanceMetric_QA.lean` (+28): the path **equality case** `2 = 1 + 1` (new edge witnesses) plus the degenerate `v = u` instantiation; the `K₃` **strict case** `2/3 < 4/3` on imported Foster pins; the confinement/definiteness positive witnesses at the actual unit-current potential `![2,1,0]` (interior value pinned strictly between the boundary values; the `iff` consumed off-diagonal and on); and the **signed fence** `![0,1,1;1,0,−1;1,−1,0]` (symmetric, support graph connected, NOT nonnegative; entrywise-if definition per the `Foster_QA` vecTail note) — in-file solution-shape analysis pins `R(0,1) = 0` at distinct vertices (**definiteness refuted**), `R(0,2) = 0`, `R(2,1) = −2` (**triangle refuted** at `¬(0 ≤ 0 + (−2))`), and **confinement refuted for every solution** — exactly `hnonneg` isolated for all three theorems at once. (3) Records: the proposal (COMPLETE + delivery record with the pin-technique list and priced follow-ons), `proposals/README.md` (Delivered row; progress paragraph), README (1999; status clause; module-table row), the radar (QA axis 1971/50 → 1999/51 and the axis-6 delivery sentence, both held), the scoreboard (four verification rows + interpretation bullet), `index/map/spectral_graph.md` (5 rows), backlog item 7, the execution plan, and this log.

**Decisive commands and outcomes:** the module's maximum principle ran green after one structural fix — the walk-induction claim must be stated over the walk's *start* (`f s = M → …`), because `Walk.cons` peels the front edge and the natural endpoint-statement makes the induction hypothesis about the wrong vertex. The QA's recurring traps, recorded in the proposal's pin-technique list: a numeral RHS against a `Pi.single` LHS strands the dependent-family metavariable (fix: ascribe `(Pi.single u (1 : ℝ) : V → ℝ)`, or evaluate the applied RHS in place with `simp [Pi.sub_apply, Pi.single_apply] at h` — the Cheeger idiom); `(-f) x` is a function-negation atom `linarith` cannot relate to `f x` (`simp only [Pi.neg_apply] at h` first); `rw [a, b] at h1 h2` fails wholesale when `a` is absent from `h2`; `Walk.cons`'s induction case binds six names; matrix notation's vecTail leftovers reconfirmed (the entrywise-if fixture pattern); `Finset.sum_erase` does not exist at this pin — `Finset.sum_erase_add _ _ h` with the flipped orientation, and `Finset.single_le_sum` takes the `∀ i ∈ s` nonneg proof first. `lake build Scaffold.Mathlib.GraphTheory.Electrical` ✔ (2009/2009) then `lake env lean` on it and on `ResistanceMetric_QA.lean` — zero errors, zero warnings each; `lake build Scaffold.QA.SpectralGraph.ResistanceMetric_QA` ✔ (2015/2015); `#print axioms` via `wip/rm_axcheck.lean` on all 33 declarations — the standard three only; **full `lake build` ✔ (2261 targets, "Build completed successfully"; zero warnings in the changed modules)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1999/9/0**, idempotent).

**Verification:** both changed modules elaborate directly with zero errors/warnings and are linked into the default build (the QA module additionally certified by its explicit build target). The delivery is unconditional hard crust — no axiom is consumed anywhere (`#print axioms`-verified), so there is no conditional-status caveat to carry. QA is load-bearing at three levels: the equality fixture (`2 = 1 + 1`) would catch any proof route with a slack constant (the sharpness witness); the signed fence proves all three hypothesis-free conclusions false on a fixture satisfying the other two hypotheses, so the nonnegativity hypothesis is exercised, not decorated; and the confinement witness instantiates both halves at the actual unit-current potential whose voltage difference is the independently pinned resistance.

**Remaining risk:** the fence is honest evidence the theorems are false without nonnegativity — load-bearing, not a defect. The `MetricSpace` packaging (a connectedness-carrying type synonym), the reachability-pair strengthening of the `iff`, and the triangle's equality characterization are priced follow-ons recorded in the proposal, not gaps in what is claimed. Route locators (Doyle–Snell §3.5, Gutman–Xiao) carry the standing verify-against-physical-copy caveat. QA fixtures are Fin 3 (the strategy's small-fixture precedent); the theorems are size- and weight-general.

**Next handoff:** the Active priority table holds no High and no Medium rows — the standing gated candidates (directed-axis mixing/rate work gated on a primitivity-shaped admission; the honestly-blocked pairwise set shape; a named consumer pricing the wide-band minimax filter designs), the priced resistance-metric follow-ons (the `MetricSpace` packaging gated on a consumer), or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-24T19:25:30Z — Resistance metric in delivery: the maximum principle, definiteness, and the triangle inequality

**Run:** `20260824T192530Z-run-1`  
**Session:** `ses_fcaca998affeXd1neL0pVj6Wgf`  
**Status:** superseded (by the completed entry above, same run)  
**Milestone:** `proposals/resistance-metric.md` (new this run) — backlog item 7's two named non-gated residuals: `effectiveResistance_pos_of_ne` / `effectiveResistance_eq_zero_iff` (the definiteness residual `R u v = 0 ↔ u = v`) and `effectiveResistance_le_add` (the triangle inequality, the "resistance is a metric" theorem), both in a new section of `GraphTheory.Electrical` behind the new **maximum principle** for unit-demand potentials (`min (f u) (f v) ≤ f x ≤ max (f u) (f v)`). Selected per the empty High/Medium Active priority table by the center-out policy: the standing handoff candidates are gated (directed mixing on primitivity; wide-band filters on a named consumer) or honestly blocked (pairwise set shape), while backlog item 7 names exactly these two residuals as the electrical family's remaining unblocked work. Leverage: completing the four metric laws turns `effectiveResistance` into a genuine metric on every connected network, and every new theorem is load-bearing — the Step-0 survey records why the eigenbasis route yields only the root-triangle (the `√R` cross term), making the maximum principle (diffusion form + nonneg-termwise-zero + walk induction) the mathematical crux; Mathlib has no resistance or graph-harmonic-extremum content (re-surveyed). Zero new axioms planned; QA at four sections including a signed fixture (`!![0,1,1;1,0,−1;1,−1,0]`, symmetric + connected support + NOT nonnegative) refuting all three conclusions with exactly `hnonneg` isolated.

**Next handoff:** spike the maximum-principle walk induction (the cons-peeling direction needs the claim stated over the walk's start), then land the module section and the QA file, then full verification and records.

## 2026-08-24T18:17:15Z — Cluster-projector symmetric form delivered: the two-sided rank-free constant-2 set-form difference theorem; the proposal COMPLETE

**Run:** `20260824T175747Z-run-1`  
**Session:** `ses_fcb189168ffeTecv0Ps6r500Mt`  
**Status:** completed  
**Milestone:** `proposals/cluster-projector-symmetric.md` (new this run, selected per the empty High/Medium Active priority table as the same-day cluster-projector delivery's recorded open follow-on — "the two-sided rank-free constant-2 *set* form composes from the delivered pair but was not re-derived here") — **Steps 0+1 delivered in one run, pure hard crust, zero new axioms (count stays 9; `#print axioms` via `wip/cps_axcheck.lean` on the new public theorem + all 18 new QA declarations: `propext, Classical.choice, Quot.sound` only, every one). QA 1953 → 1971 (`ClusterProjector_QA` 28 → 46). The set-valued difference family is complete — product/difference/symmetric all at arbitrary eigenvalue sets, matching the window family's full shape.**

**Changes:** (1) the new SetForm theorem of `Perturbation/BandDavisKahan.lean` (**no new imports**): `l2OpNorm_clusterProjector_sub_clusterProjector_le_two_of_symm` — `‖P_A(S) − P_B(T)‖ ≤ 2‖A−B‖/δ` under both-flank center/radius membership separation at **two** center/radius pairs, **no rank hypothesis anywhere** (the YWS both-gaps shape at sets). The proof is the priced four-step composition — the ring identity `P − Q = (I−Q)P − Q(I−P)` (the module's private lemma), the complement law `1 − Q_T = Q_{Tᶜ}` at both residuals, the delivered set-form product bound at both argument orders (the second under `l2OpNorm_transpose`, the `IsSymm` proofs bridged to transpose equations by typed `have`s), the triangle inequality; **the constant 2 is exactly that triangle, with no case split anywhere** — the set product bound's unconditional hypotheses make the window sibling's private rank-free pairwise engine *and* trivial-regime split unnecessary, and that the set route is easier is the delivery's structural finding. The two-pair statement shape was recorded before stating: a single common center would exclude the QA's own unequal-rank witness, where an out-of-`S` A-eigenvalue sits between the clusters. (2) The new symmetric-form QA section of `ClusterProjector_QA.lean` (+18): the **unequal-rank non-interval witness** (`S = {0,5}` rank 2 vs `T = {5}` rank 1, the delivered equal-rank family's hypothesis exhibited failing through the rank supplier, theorem bound `≤ 4` via the imported perturbation norm against the independent raw lower `1` at `e₀`; two new entrywise pins — `P_A({0,5}) = diag(1,1,0)` from the exported `bandClusterA_eq`, `P_bm({5}) = diag(0,1,0)` from the extracted `spBm_four`/`spBm_six` threshold pair); the ε = 0 attainment through the new theorem with both flanks genuinely discharged; the **two-sided fence** on the interior-gap configuration with *each* `hfar` flank refuted in proved form at its own interior eigenvalue while both `hnear` sides hold and the hypothesis-free conclusion dies at norm `≥ 1`; and the ring-identity coherence witness pinned entrywise, independent of the private lemma. (3) Records: the proposal (COMPLETE + delivery record with the pin-technique list and open follow-ons), `proposals/README.md` (the High row retired to the Delivered table; the progress paragraph), README (1971; the Perturbation row's symmetric-set sentence), the radar (QA axis synced 1953/50 → 1971/50, held 4.0), the scoreboard (five verification rows + a new interpretation bullet), `index/map/perturbation.md` and `index/sources/davis_kahan_1970.md`, the execution plan, and this log.

**Decisive commands and outcomes:** the module's theorem ran green after one fix (the run's sharpest recorded technique: `rw [l2OpNorm_transpose]` cannot fire unless the transpose is *already syntactically present* in the goal — the durable structure is an explicit transpose-equation `have` built from `Matrix.transpose_mul` plus the two symmetry equations, `clusterProjector_symmetric` returning an `IsSymm` proof that is defeq to the transpose equation); the QA took two rounds whose seven first-pass errors were all one trap: this pin's `le_abs : b ≤ |a| ↔ b ≤ a ∨ b ≤ -b` — the negative-side eigenvalue takes the second disjunct with the *negated* argument, and `norm_num` on a false arithmetic goal normalizes it to a bare `⊢ False`, so the diagnostic that first looks like a missing contradiction is a wrong-disjunct sign error; plus `norm_num at h` on a hypothesis still carrying `‖A − A‖` over-unfolds the norm into a matrix equation — zero the norm and rewrite the arithmetic through an explicit `hrhs` instead. `lake build Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan` ✔ (2193/2193) then `lake env lean` on it and on `ClusterProjector_QA.lean` — zero errors, zero warnings each; `lake build Scaffold.QA.Perturbation.ClusterProjector_QA` ✔ (2198/2198); `#print axioms` via `wip/cps_axcheck.lean` on all 19 new declarations — the standard three only; **full `lake build` ✔ (2261 targets, "Build completed successfully"; zero warnings in the changed modules — the log's Scaffold-tree diagnostics are the documented pre-existing set in untouched modules, and the docPrime notes are upstream Mathlib package replay notes)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1971/9/0**, idempotent by content).

**Verification:** every changed module elaborates directly with zero errors/warnings and both are linked into the full default build (the QA module additionally certified by its explicit build target). The delivery is unconditional hard crust — no axiom is consumed anywhere (`#print axioms`-verified), so there is no conditional-status caveat to carry. QA is load-bearing at three levels: the unequal-rank witness is engineered to be unreachable by the delivered equal-rank form (the point of the theorem) and its raw lower bound shares no mechanism with the theorem (entrywise projector pins + the vector action bound at `e₀`); the two-sided fence isolates each `hfar` flank separately at its own interior eigenvalue with every other hypothesis verified — the two-sidedness itself exercised, neither separation decoration; and the ring-identity witness exhibits the composition's one identity numerically, independent of the module's private lemma.

**Remaining risk:** the delivered statement is the two-pair center/radius membership form; the YWS-literal *pairwise* set shape (no center/radius) remains honestly blocked exactly as `cluster-projector.md` records (an out-of-`S` A-eigenvalue can sit inside `S`'s range; whether the shape is true at all is open to this repo). Route locators carry the standing verify-against-physical-copy caveat. QA fixtures are Fin 3 diagonal (the strategy's small-fixture precedent); the theorem is size- and set-general, so the risk is QA breadth, not correctness.

**Next handoff:** the Active priority table holds no High and no Medium rows — the standing gated candidates (directed-axis mixing/rate work gated on a primitivity-shaped admission; the honestly-blocked pairwise set shape; a named consumer pricing the wide-band minimax filter designs) or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-24T18:00:42Z — Cluster-projector symmetric form in delivery: the two-sided rank-free constant-2 set-form difference theorem

**Run:** `20260824T175747Z-run-1`  
**Session:** `ses_fcb189168ffeTecv0Ps6r500Mt`  
**Status:** superseded (by the completed entry above, same run)  
**Milestone:** `proposals/cluster-projector-symmetric.md` (new this run, added to the Active priority table as its only High row) — `l2OpNorm_clusterProjector_sub_clusterProjector_le_two_of_symm`: `‖P_A(S) − P_B(T)‖ ≤ 2‖A−B‖/δ` at arbitrary eigenvalue sets under both-flank center/radius membership separation, **no rank hypothesis anywhere** (the YWS both-gaps dimension-freeness at sets). The recorded open follow-on of the same day's cluster-projector delivery ("composes from the delivered pair but was not re-derived here"), selected per the empty High/Medium queue with the alternative candidates gated on decisions a run cannot make. Leverage: load-bearing on the day-old layers exactly — the set-form product bound at both argument orders, the complement law `1 − Q_T = Q_{Tᶜ}` (which absorbs what the window symmetric form needed a private rank-free pairwise engine plus a trivial-regime split for: the set product bound is unconditional, so no case split exists here), `l2OpNorm_transpose`, and the ring identity `P − Q = (I−Q)P − Q(I−P)`; constant 2 is exactly the triangle inequality. Statement-shape decision recorded before stating: two center/radius pairs (`cS rS`, `cT rT`) — a single common center would exclude the QA's own unequal-rank witness, where an out-of-`S` A-eigenvalue sits between the two clusters. Zero new axioms (count stays 9); QA planned at four sections on the public `clusterA`/`bm` fixtures (unequal-rank witness `S = {0,5}` rank 2 vs `T = {5}` rank 1; ε = 0 attainment; the two-sided fence on the interior-gap configuration with both `hfar` sides isolated; the ring-identity coherence).

**Changes (intended):** the proposal document; the new theorem in `Perturbation/BandDavisKahan.lean`'s SetForm sections; a symmetric-form QA section extending `ClusterProjector_QA.lean` (two new threshold pins: the bm-side singleton extraction and the bm two-mode pin; the A-side `{0,5}` pin composes from the already-exported `bandClusterA_eq`); record updates.

**Next handoff:** deliver module + QA in this run (the composition is priced and every consumed declaration verified on shelf), then verification and records.

## 2026-08-24T16:51:56Z — Cluster projector delivered: the set-valued spectral projector and its Davis–Kahan pair; the proposal COMPLETE

**Run:** `20260824T161014Z-run-1`  
**Session:** `ses_fcb7c2335ffew3wz7WLzJ9A4eP`  
**Status:** completed  
**Milestone:** `proposals/cluster-projector.md` (new this run, selected per the empty High/Medium Active priority table and the cluster/symmetric deliveries' recorded follow-on "its own definition + proposal") — **Steps 0+1 delivered in one run, pure hard crust, zero new axioms (count stays 9; `#print axioms` via `wip/cp_axcheck.lean` on all 18 public module + 2 set-form + 27 public QA declarations: `propext, Classical.choice, Quot.sound` only, every one). QA 1925 → 1953 (`ClusterProjector_QA` a new Perturbation-domain file at 28). The projector shelf's interval constraint is gone: clusters are stated as sets.**

**Changes:** (1) the new `Scaffold/Mathlib/GraphTheory/ClusterProjector.lean` (minimal imports Spectral + Band; the umbrella importing it): the junk-free definition `clusterProjector M hM S := ∑_{λᵢ ∈ S} vᵢvᵢᵀ` and the interface — the component action (the engine's only projector input), the **intersection product law** `P_S * P_T = P_{S ∩ T}` by the action route, idempotence, disjoint-set orthogonality, guard-free mode selection, commutation, capture at sets, the **complement law** `1 − P_S = P_{Sᶜ}` (the structural fact the window family lacks), the **band agreement** `clusterProjector (Set.Ioc a b) = bandProjector a b`, and the trace/rank supplier. (2) The new `SetForm` sections of `Perturbation/BandDavisKahan.lean` (+1 import): the commutator/shift engine re-run at membership filters — the **set-form product bound** and, at equal rank, the **set-form difference bound** `‖P_A(S) − P_B(T)‖ ≤ ‖A−B‖/δ` under center/radius membership separation, needing **no dichotomy and no interior case** because the complement law replaces the window form's separate six-lemma complement engine. (3) `Scaffold/QA/Perturbation/ClusterProjector_QA.lean` (+28): the non-interval pin `P_{{0,11}} = diag(1,0,1)` through a four-lemma composition (a subspace no window expresses), the non-interval difference instance at exact-fit `c = 11/2, r = 11/2, δ = 1` with the raw lower `1 ≤ ‖P−Q‖` at `e₀` against the theorem's `≤ 1`, the ε = 0 attainment with the out-of-`T` separation genuinely discharged, and the `hfar` fence on the interior-gap configuration — the proposal's recorded obstruction itself exercised as a hypothesis fence (ranks 2 = 2, `hnear` verified, conclusion refuted at norm ≥ 1). (4) Records: the proposal (COMPLETE + delivery record with the pin-technique list and the honestly-blocked pairwise follow-on), `proposals/README.md` (the Delivered row; the progress paragraph — the table empty again), README (1953; the module-table row; the Perturbation row's set-form sentence), the radar (QA axis synced 1925/49 → 1953/50, held 4.0), the scoreboard (all four verification rows + a new interpretation bullet), `index/map/spectral_graph.md` and `index/map/perturbation.md` and `index/sources/davis_kahan_1970.md`, the umbrella, the execution plan, and this log.

**Decisive commands and outcomes:** the filter-instance trap cost most of the elaboration rounds and its fix is the run's sharpest recorded technique: `Finset.filter` at a set-membership predicate elaborates under *different* `DecidablePred` instances in definition-unfolded goals versus `classical`-tactic proofs, so filter-equality rewrites fail on definition-unfolded filters even when the displays match — the durable fixes (now in the proposal's list) are the *action/component* idiom for projector proofs (no filter rewrites at all; the intersection law's proof became shorter than the band nestedness proof while consuming the component action it is supposed to test) and trace-lemma-sourced count pins (`exact_mod_cast h.symm`, never a hand-stated filter-card `have`); plus `open Classical in` must precede the doc comment, `Set.mem_inter_iff`-family lemmas take explicit arguments defeating dot-projection (defeq `show` terms and forward forms instead), and QA-side simp's normNum fails on negative real literals and `abs` goals (explicit `abs_le`/`le_abs` with sign-chosen branches, `linarith` on hypotheses) while entrywise matrix goals need `simp` before `norm_num` (simp decides Fin-index `ite`s that norm_num cannot). `lake build Scaffold.Mathlib.GraphTheory.ClusterProjector` ✔ (2010/2010) then `lake env lean` on all three modules — zero errors, zero warnings each; explicit `lake build` targets on the perturbation module and QA ✔ (2193/2193, 2198/2198); `#print axioms` via `wip/cp_axcheck.lean` on all 47 accessible declarations — the standard three only; **full `lake build` ✔ (2261 targets, "Build completed successfully"; zero warnings in the changed modules — the log's remaining diagnostics are the documented pre-existing set plus upstream Mathlib package notes)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1953/9/0**, idempotent by md5).

**Verification:** every changed module elaborates directly with zero errors/warnings and all three are linked into the full default build (the QA module additionally certified by its explicit build target). The whole delivery is unconditional hard crust — no axiom is consumed anywhere (`#print axioms`-verified), so there is no conditional-status caveat to carry. QA is load-bearing at three levels: the non-interior pin composes four delivered lemmas (capture, complement, agreement, threshold pin) that share no mechanism with the pin's target — a misstatement in any breaks the chain; the difference instance's raw lower bound shares no mechanism with the theorem (entrywise projector pins + the vector action bound at `e₀`); and the fence isolates exactly `hfar` on the configuration the recorded obstruction names, with every other hypothesis verified — the hypothesis exercised as a fence, not decoration.

**Remaining risk:** the delivered statements are the center/radius membership forms — the YWS-literal *pairwise* set shape (no center/radius) is recorded as honestly blocked: an out-of-`S` A-eigenvalue can sit inside `S`'s range, killing the window proof's interior-case trivial regime (`δ ≤ ‖A−B‖` via δ-farness from A's whole spectrum), and the configuration is not trivial (neither projector sees the gap eigenvalue); whether that shape is true at all is open to this repo and needs eigenvalue-flow/Weyl-tracking machinery. The two-sided rank-free constant-2 *set* form composes from the delivered pair but was not re-derived. Route locators carry the standing verify-against-physical-copy caveat. QA is Fin 3 diagonal fixtures (the strategy's small-fixture precedent); the theorems are size- and set-general, so the risk is QA breadth, not correctness.

**Next handoff:** the Active priority table holds no High and no Medium rows — the center-out policy with the natural candidates on record: directed-axis mixing/rate work (gated on a primitivity-shaped admission), the pairwise set shape (honestly blocked, per this delivery's record), or a named consumer pricing the wide-band minimax filter designs.

## 2026-08-24T16:10:14Z — Cluster projector in delivery: the set-valued spectral projector and its Davis–Kahan pair

**Run:** `20260824T161014Z-run-1`  
**Session:** `ses_fcb7c2335ffew3wz7WLzJ9A4eP`  
**Status:** superseded (by the completed entry above, same run)  
**Milestone:** `proposals/cluster-projector.md` (new this run) — the set-valued spectral projector `clusterProjector M hM S := ∑_{λᵢ ∈ S} vᵢvᵢᵀ` with its interface (component action, the intersection product law, the complement law `P_{Sᶜ} = 1 − P_S` — the structural gap of the window family — mode selection, commutation, trace/rank supplier, and the public band-agreement bridge `clusterProjector (Ioc a b) = bandProjector a b`) plus the SetForm Davis–Kahan pair in `BandDavisKahan.lean`: `‖P_B(T) * P_A(S)‖ ≤ ‖A−B‖/δ` and the equal-rank difference form at center/radius membership hypotheses — the commutator/shift engine re-run at sets, where the complement law replaces the window form's separate complement engine and no interior/boundary dichotomy is needed. Selected per the cluster/symmetric deliveries' recorded follow-on ("its own definition + proposal") with the Active priority table empty of High/Medium rows; the two alternative candidates remain gated (primitivity-shaped admission; approximation-theory decisions). The YWS-literal pairwise set shape is recorded as honestly blocked — an out-of-`S` A-eigenvalue can sit inside `S`'s range, so the window proof's interior-case trivial regime (`δ ≤ ‖A−B‖` via δ-farness from A's whole spectrum) is unavailable and the configuration is not trivial; whether the shape is true at all is open to this repo. Pure hard crust, zero new axioms; QA planned at four sections (non-interval witness, agreement transport, theorem instances at exact-fit data, `hfar` fence on the interior-gap configuration).

## 2026-08-24T15:02:25Z — Band Davis–Kahan symmetric form delivered: the two-sided constant-2 difference theorem without rank equality; the proposal COMPLETE

**Run:** `20260824T141936Z-run-1`  
**Session:** `ses_fcbe876deffe6Id4h7cMXwIrbB`  
**Status:** completed  
**Milestone:** `proposals/band-davis-kahan-symmetric.md` (new this run, the Active table's only High row) — **Steps 0+1 delivered in one run, pure hard crust, zero new axioms (count stays 9; `#print axioms` via `wip/bdks_axcheck.lean` on both new public + all 17 public QA declarations: `propext, Classical.choice, Quot.sound` only, every one). QA 1908 → 1925 (`BandDavisKahanSymm_QA` a new Perturbation-domain file at 17 by the generator metric). The delivered difference family's rank obligation is now optional: consumers holding both pairwise separations state nothing about multiplicities.**

**Changes:** (1) the new `SymmetricForm` sections of `Perturbation/BandDavisKahan.lean` (**no new imports**): the public **`l2OpNorm_transpose`** (`‖Mᵀ‖ = ‖M‖` — a genuine pin/shelf gap, closed by two pairing-characterization applications) and the headline **`l2OpNorm_bandProjector_sub_bandProjector_le_two_of_symm`** — `‖P_A − P_B‖ ≤ 2‖A − B‖/δ` under two-sided pairwise separation with **no rank hypothesis anywhere** (the YWS both-gaps dimension-freeness; 2 is exactly the triangle inequality at `P − Q = (I−Q)P − Q(I−P)`, the private rank-free pairwise product bound — the cluster theorem's body minus the identity conversion — instantiated at both argument orders, the engine's 4th/5th consumers; unequal ranks force `δ ≤ ‖A − B‖` in-proof). One committed-statement correction recorded: `hsepAB`'s inner hypothesis restated in the family's conjunction shape (a one-line eta-expansion bridges to the engine). (2) `Scaffold/QA/Perturbation/BandDavisKahanSymm_QA.lean` (+17, on the **public** cluster fixtures — no new Fin 3 machinery): the unequal-rank witness (ranks pinned 2 ≠ 1 through the supplier — the delivered family's hypothesis exhibited failing on the covered fixture — raw norm ≥ 1 through an in-file eigen-equation support pin, bound ≤ 28; plus the constant comparison delivered ≤ 1 vs new ≤ 2 vs raw `√(1/10)`), the ε = 0 attainment cross-checked by the imported raw zero pin, the `hsepAB`-isolated fence (`hsepBA` provably vacuous-holding, `Q = 1` through `bandProjector_eq_one`, the hypothesis-free conclusion refuted — the mirror of the cluster QA's fence, both separation sides now isolated across the QA family), and the decomposition-coherence witness (the consumed identity's action-level content on rotated input). (3) Records: the proposal (status COMPLETE + delivery record with the statement correction, pin-technique list, open follow-ons), `proposals/README.md` (the Delivered row; the High row retired; the progress paragraph — the table empty again), README (1925; the Perturbation module-table row), the radar (QA axis 1908/48 → 1925/49, held 4.0), the scoreboard (four verification rows + an interpretation bullet; regenerated idempotent 1925/9/0), `index/map/perturbation.md`, `index/sources/davis_kahan_1970.md`, this plan, and this log.

**Decisive commands and outcomes:** the module's engine ran green on its **first complete pass** (two elaboration rounds only, both in QA); `lake env lean Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean` and on `Scaffold/QA/Perturbation/BandDavisKahanSymm_QA.lean` — zero errors, zero warnings each; `lake build` targets both ✔; `#print axioms` via `wip/bdks_axcheck.lean` on all 19 accessible declarations — the standard three only; **full `lake build` ✔ (2260 targets, +1 for the new QA module, "Build completed successfully"; zero warnings in the changed modules)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1925/9/0**, idempotent by md5). The QA elaboration rounds' recurring fixes recorded in the proposal's pin-technique list — the sharpest: `rw ... at` on a *conjunction* hypothesis silently normalizes it (decidable conjuncts collapse; the hypothesis can arrive at the use site as a bare comparison or `True`), so eigenvalue-derivation branches use `linarith [h, jin.2]` with inline projections (the goal `eigvalOf = c` is linear in the atom and follows from the contradiction) and goal-side per-component rewrites; also `div_le_div_right` is a deprecated iff at this pin, `norm_num` does not evaluate fractional `|9/4|` (pre-rewrite `abs_of_nonneg`), and `‖0‖` needs `norm_zero` added to the chain after `sub_self`.

**Verification:** every changed module elaborates directly with zero errors/warnings and both are linked into the full default build (the QA module additionally certified by its explicit build target). The whole delivery is unconditional hard crust — no axiom is consumed anywhere (`#print axioms`-verified on every accessible new declaration), so there is no conditional-status caveat to carry. QA is load-bearing at three levels: the unequal-rank witness proves the rank-freeness claim by exhibiting the delivered family's hypothesis failing on the covered fixture (a wrong claim would fail the rank pin or the discharge); the fence isolates exactly `hsepAB` with its mirror proved holding (the hypothesis exercised, not decorated); the coherence witness exhibits the consumed ring identity's action-level content with both parts computed from imported pins, independent of the module's private algebra.

**Remaining risk:** the delivered statement is the operator-norm symmetric form at constant 2 — the Frobenius-norm sin-Θ variants (YWS Theorem 1's other parts) would need a Frobenius pairing engine absent from the shelf, and a set-valued (non-interval) cluster projector needs its own definition + proposal (both recorded follow-ons, not gaps in what is claimed). The YWS locator is route provenance for a *proved* statement and carries the repo's standing verify-against-physical-copy caveat. The unequal-rank regime's bound is necessarily weak (`δ ≤ ‖A − B‖` forced, so `2E/δ ≥ 2`) — the theorem's value is uniformity, honestly documented in the docstring and QA.

**Next handoff:** the Active priority table holds no High and no Medium rows — the center-out policy with the natural candidates on record: directed-axis mixing/rate work (gated on a primitivity-shaped admission), a set-valued cluster projector (own definition + proposal, per the cluster/symmetric proposals' recorded follow-ons), or a named consumer pricing the wide-band minimax filter designs.

## 2026-08-24T14:19:36Z — Band Davis–Kahan symmetric form in delivery: the two-sided constant-2 difference theorem without rank equality

**Run:** `20260824T141936Z-run-1`  
**Session:** `ses_fcbe876deffe6Id4h7cMXwIrbB`  
**Status:** superseded (by the completed entry above, same run)  
**Milestone:** `proposals/band-davis-kahan-symmetric.md` (new this run, added to the Active priority table as its only High row) — the cluster-form delivery's own first recorded follow-on: `‖P_A − P_B‖ ≤ 2‖A − B‖/δ` under *two-sided* pairwise separation (B-out vs A-in *and* A-out vs B-in, both in the literal YWS shape) with **no rank hypothesis** — the both-gaps form's dimension-freeness at constant 2, where 2 is exactly the triangle inequality at the decomposition `P − Q = (I−Q)P − Q(I−P)`. The other two handoff candidates are gated (primitivity-shaped admission; scalar approximation theory absent from the pin). Route worked through before stating: trivial regime at `‖A−B‖ ≥ δ/2`; contentful regime `‖A−B‖ < δ/2` kills the interior case outright (it forces `δ ≤ ‖A−B‖`), so the rank-free pairwise product bound — the cluster theorem's dichotomy+shrink+engine body minus the identity conversion, factored once and instantiated at both argument orders (the engine's 4th/5th consumers) — gives both `‖(I−Q)P‖ ≤ E/δ` and `‖(I−P)Q‖ ≤ E/δ`, with a new public `l2OpNorm_transpose` (absent from pin and shelf; two pairing-characterization applications) moving `Q(I−P)` under the swapped bound. Pure hard crust, zero new axioms; QA planned at four sections (unequal-rank rank-free witness on the public cluster fixtures, ε = 0 attainment, hsepAB-isolated fence mirroring the cluster QA's hsepBA fence, decomposition-coherence witness).

## 2026-08-24T13:04:07Z — Band Davis–Kahan cluster form delivered: the pairwise (YWS-literal) difference theorem strictly generalizing the closure form; the proposal COMPLETE

**Run:** `20260824T122219Z-run-1`  
**Session:** `ses_fcc552010ffeN9uHbC3DG38a4B`  
**Status:** completed  
**Milestone:** `proposals/band-davis-kahan-cluster.md` (new this run, selected per the previous run's recorded next handoff — the delivered difference theorem's own first-named follow-on) — **Steps 0+1 delivered in one run, pure hard crust, zero new axioms (count stays 9; `#print axioms` via `wip/bdkc_axcheck.lean` on all 3 public + 37 QA declarations: `propext, Classical.choice, Quot.sound` only, every one). QA 1873 → 1908 (`BandDavisKahanCluster_QA` a new Perturbation-domain file at 35 by the generator metric). The closure-separated difference theorem is now a strict special case: the pairwise hypothesis covers configurations the closure form provably cannot reach.**

**Changes:** (1) new `ClusterForm` sections of `Perturbation/BandDavisKahan.lean` (**no new imports** — the Step-0 survey's decisive finding): the headline `l2OpNorm_bandProjector_sub_bandProjector_le_of_pairwise` — `‖P_A(a₁,b₁] − P_B(a₂,b₂]‖ ≤ ‖A − B‖/δ` at constant 1 under pairwise separation (every eigenvalue of B outside its window δ-away from every eigenvalue of A inside its window, the literal YWS Theorem 1 δ) — plus the public capture-equality lemma `bandProjector_eq_of_forall_mem_iff` (windows selecting the same eigenvalues give the same projector; window guards added over the committed draft as a recorded correction — the unguarded iff-form is false at reversed junk windows) and the empty-cluster zero lemma. The route's two new mathematical facts: the interior case forces `δ ≤ ‖A−B‖` by a projector-free Parseval expansion at a B-eigenvector (`Bv = μv` makes `A − μI` and `A − B` agree on `v`; **no Weyl/`evals` bridge anywhere**), closing the trivial regime through `‖P−Q‖ ≤ 1`; the boundary case shrinks A's window to the cluster range through capture-equality and re-runs the private complement engine at the cluster-range center/radius — the engine's third load-bearing consumer, at exactly the instantiation where its arbitrary-`c, r` generality is the point. (2) `Scaffold/QA/Perturbation/BandDavisKahanCluster_QA.lean` (+35, with an in-file Fin 3 spectral layer: distinct-entry diagonals force eigenvector support onto single coordinates, orthonormality forces eigenvalue classes to be singletons): the interior witness on `diag(0,5,11)` vs `diag(1,2,4)` — the closure shape *refuted in proved form* (`7 ≤ 4` false at the interior 4-mode) while the pairwise hypothesis discharges and both projectors pin entrywise to `diag(1,1,0)`, raw distance `0` against the theorem bound `≤ ‖A−B‖ ≤ 7`; the rotated two-route witness; the ε = 0 attainment at genuinely distinct windows through the capture lemma; and the separation fence refuted with ranks equal — exactly `hsep` isolated, the mirror of the sibling's rank fence. (3) Records: the proposal (status COMPLETE + delivery record with the pin-technique list and the statement-guard correction), `proposals/README.md`, README (1908; module row; status sentence), the radar (QA axis 1873/47 → 1908/48, held 4.0), the scoreboard (four verification rows + an interpretation bullet; regenerated idempotent 1908/9/0), `index/map/perturbation.md`, `index/sources/davis_kahan_1970.md`, this plan, and this log.

**Decisive commands and outcomes:** developed in-place (the sibling's precedent — the private engine is same-module); `lake env lean Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean` and on `Scaffold/QA/Perturbation/BandDavisKahanCluster_QA.lean` — zero errors, zero warnings each; `lake build Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan` ✔ (2192/2192) and `lake build Scaffold.QA.Perturbation.BandDavisKahanCluster_QA` ✔ (2196/2196); `#print axioms` via `wip/bdkc_axcheck.lean` on all 40 declarations — the standard three only; **full `lake build` ✔ (2260 targets, +1, "Build completed successfully"; zero warnings in the changed modules)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1908/9/0**, idempotent). One QA-module rebuild was needed before the axcheck because `lake env lean` reads stale oleans for imports (the module was rebuilt by explicit target first).

**Verification:** every changed module elaborates directly with zero errors/warnings and both are linked into the full default build (the QA module additionally certified by its explicit build target). The whole delivery is unconditional hard crust — no axiom is consumed anywhere (`#print axioms`-verified), so there is no conditional-status caveat to carry. QA is load-bearing at three levels: the interior witness proves the *new* coverage claim by refuting the delivered theorem's hypothesis shape on the very fixture where the new one discharges (a wrong weakening would either fail the refutation or fail the discharge); the raw projector pins (entrywise `diag(1,1,0)` through the in-file support/class-injectivity layer) share no mechanism with the theorem; and the separation fence exercises the new hypothesis as a proved refutation with every other hypothesis verified — the complement of the sibling's rank fence, so between the two QA files both supply-side hypotheses of the difference family are now isolated.

**Remaining risk:** the delivered statement is the one-sided pairwise form at constant 1 — the two-sided symmetric-gap constant-2 form and a set-valued (non-interval) cluster projector are recorded follow-ons, not gaps in what is claimed. The YWS locator is route provenance for a *proved* statement and carries the repo's standing verify-against-physical-copy caveat. QA's interior fixture is Fin 3 with distinct diagonal entries (the strategy's small-fixture precedent); the theorems are size-general and spectrum-general, so the risk is QA breadth, not correctness. The capture-equality lemma's guards mean it cannot transfer junk windows — deliberate, recorded in the docstring.

**Next handoff:** the Active priority table holds no High and no Medium rows — the center-out policy with the natural candidates on record: the two-sided symmetric-gap constant-2 form of the band Davis–Kahan difference family (own document, the cluster proposal's recorded follow-on), directed-axis mixing/rate work (gated on a primitivity-shaped admission), or a named consumer pricing the wide-band minimax filter designs.

## 2026-08-24T12:22:19Z — Band Davis–Kahan cluster form in delivery: the pairwise (YWS-literal) difference theorem

**Run:** `20260824T122219Z-run-1`  
**Session:** `ses_fcc552010ffeN9uHbC3DG38a4B`  
**Status:** superseded (by the completed entry above, same run)  
**Milestone:** `proposals/band-davis-kahan-cluster.md` (new this run) — the eigenvalue-cluster-separated generalization of the delivered difference form: `‖P_A(a₁,b₁] − P_B(a₂,b₂]‖ ≤ ‖A − B‖ / δ` at constant 1 under *pairwise* separation (B's out-of-window eigenvalues δ-away from each of A's in-window eigenvalues — the literal YWS Theorem 1 δ, strictly weaker than the delivered closure separation). The previous run's recorded next handoff (first-named candidate; the two alternatives gated on primitivity/admission and approximation-theory decisions a run cannot make). Route worked through before stating: interior B-eigenvalues (inside A's cluster range, in a gap) force every A-eigenvalue δ-away from μ, and the eigenvector equation gives δ ≤ ‖(A−μI)v‖ = ‖(A−B)v‖ ≤ ‖A−B‖ — a projector-free Parseval expansion in the module's own idiom, no Weyl/evals bridge; the trivial regime ‖P−Q‖ ≤ 1 then closes. Boundary ones give range separation, where the private engine re-runs at the cluster-range center/radius with a capture-equality window transfer (`bandProjector_eq_of_forall_mem_iff`, new public). Pure hard crust, zero new axioms; landing as new sections of `Perturbation/BandDavisKahan.lean` (no new imports), QA in a new `BandDavisKahanCluster_QA.lean` (interior witness on a pinned Fin 3 fixture where closure separation is refuted in proved form, the rotated two-route witness, ε = 0 attainment, and the hsep fence isolating the new hypothesis).

## 2026-08-24T11:05:34Z — Band Davis–Kahan difference form delivered: the equal-rank identity's first consumer; the proposal COMPLETE

**Run:** `20260824T102440Z-run-1`  
**Session:** `ses_fccbc7a13ffe7ZJefEa71gff32`  
**Status:** completed  
**Milestone:** `proposals/band-davis-kahan-difference.md` (new this run, selected per the previous run's recorded next handoff — the delivered product theorem's own open follow-on; the two alternative candidates gated) — **Steps 0+1 delivered in one run, pure hard crust, zero new axioms (count stays 9; `#print axioms` via `wip/bdkd_axcheck.lean` on all 5 public + 21 QA declarations: `propext, Classical.choice, Quot.sound` only, every one). QA 1852 → 1873 (`BandDavisKahanDiff_QA` a new Perturbation-domain file at 21). The equal-rank identity `ProjectionGap.l2OpNorm_sub_eq_of_rank_eq` — delivered 2026-08-21 but never until now consumed — carries its first weight, exactly the load-bearing-growth principle's use case.**

**Changes:** (1) new sections of `Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean` (one new import: ProjectionGap; no umbrella change): the headline pair `l2OpNorm_bandProjector_sub_bandProjector_le` / `_le_of_mem` — `‖P_A(a₁,b₁] − P_B(a₂,b₂]‖ ≤ ‖A − B‖ / δ` at constant 1 for equal-rank band projectors under one-sided eigenvalue separation (B's out-of-window eigenvalues δ-away from A's window closure), the margin corollary covering contained windows — the classical Davis–Kahan/YWS-Thm-1 operator-norm difference shape; the route is the equal-rank identity reducing the difference to `‖(I−Q_B)·P_A‖` plus the commutator/shift engine re-run verbatim at the complement projector `Q' = 1 − Q_band(B)` (F1 compression and range invariance reused unchanged; the one new mathematical fact the **complement expansion** — `Q'`-fixed vectors have vanishing in-band components, so Parseval leaves exactly the separated modes); plus the public **rank supplier** `rank_bandProjector_eq_card` (rank = in-band eigenvalue count via trace, through the exact `{0,1}` spectrum of a symmetric idempotent — new private `eigvalOf_isSymm_idempotent_sq` from the eigen-equation) with its trace parents, making the equal-rank hypothesis checkable rather than merely statable. (2) `Scaffold/QA/Perturbation/BandDavisKahanDiff_QA.lean` (+21, the reused `diag13`/`bdkB` fixtures by QA-to-QA import): the positive two-route witness (rank supplied through the new supplier; theorem bound `1` vs raw lower `1/√10` by the window-parametric sign-independent eigenbasis resolution `Q *ᵥ e₀ = ![9/10, −3/10]`); the **identity-coherence witness** (`(I−Q)·P` and `P−Q` actions pinned equal by two independent raw routes — the consumed identity's content exhibited numerically); the ε = 0 attainment with separation genuinely holding; the margin instance at δ = 1; and the **rank fence refuted in proved form** (A = B = diag13, windows empty vs occupied, ranks 0 ≠ 1 through the supplier, every other hypothesis verified — exactly `hrank` isolated). (3) Records: the proposal (status COMPLETE + full delivery record with the pin-technique list), `proposals/README.md` (Delivered row; progress paragraph — the table empty again), README (1873; the Perturbation module-table row), the radar (QA axis 1852/46 → 1873/47 held 4.0), the scoreboard (all four verification rows + a new interpretation bullet + the previous product-form bullet de-staled; regenerated idempotent 1873/9/0), `index/map/perturbation.md` (section extended + 5 rows + Deferred-Work de-staled), `index/sources/davis_kahan_1970.md` (the difference-form mapping row), backlog item 9 (the delivery closing the named program), the execution plan, this log.

**Decisive commands and outcomes:** developed in-place in the module (the private helpers are inaccessible to a separate spike file — the same-module decision's deliberate cost, repaid by the **engine compiling green on its first complete pass**; the elaboration rounds were in the rank supplier and QA); `lake env lean Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean` and on `Scaffold/QA/Perturbation/BandDavisKahanDiff_QA.lean` — zero errors, zero warnings each; `lake build Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan` ✔ (2192/2192) and `lake build Scaffold.QA.Perturbation.BandDavisKahanDiff_QA` ✔ (2195/2195); `#print axioms` via `wip/bdkd_axcheck.lean` on all 26 declarations — the standard three only; **full `lake build` ✔ (2260 targets, +1 for the new QA module, "Build completed successfully"; zero warnings in the changed modules — the log's Scaffold-tree warnings are the documented pre-existing set in untouched modules)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1873/9/0**, idempotent).

**Verification:** every changed module elaborates directly with zero errors/warnings and both are linked into the full default build (the QA module additionally certified by its explicit build target). The whole delivery is unconditional hard crust — no axiom is consumed anywhere (`#print axioms`-verified), so there is no conditional-status caveat to carry. QA is load-bearing at three levels: the raw lower-bound route shares no mechanism with the theorem (a wrong constant, separation orientation, or identity clause anywhere in the delivered chain contradicts the independent `1/√10` computation); the identity-coherence witness pins the consumed equal-rank identity's content numerically; and the rank fence exercises the new hypothesis as a proved refutation with every other hypothesis verified — not decoration.

**Remaining risk:** the delivered statement covers the one-sided eigenvalue-separation form at constant 1 — the eigenvalue-cluster-separated generalization (YWS Theorem 1's literal shape) and the two-sided symmetric-gap constant-2 form are recorded follow-ons, not gaps in what is claimed. The Davis–Kahan/Kato locators are route provenance for *proved* statements and carry the repo's standing verify-against-physical-copy caveat. QA is 2×2 fixtures (the strategy's small-fixture precedent); the theorems are size-general, so the risk is QA breadth, not correctness. The rank supplier's value rests on the exact-`{0,1}`-spectrum sub-fact, which is itself `#print axioms`-clean and consumed structurally.

**Next handoff:** the Active priority table holds no High and no Medium rows — the center-out policy with the natural candidates on record: the eigenvalue-cluster-separated generalization of the difference form (own document), directed-axis mixing/rate work (gated on a primitivity-shaped admission), or a named consumer pricing the wide-band minimax filter designs.

## 2026-08-24T10:24:40Z — Band Davis–Kahan difference form in delivery: the equal-rank identity's first consumer

**Run:** `20260824T102440Z-run-1`  
**Session:** `ses_fccbc7a13ffe7ZJefEa71gff32`  
**Status:** superseded (by the completed entry above, same run)  
**Milestone:** `proposals/band-davis-kahan-difference.md` (new this run) — the band Davis–Kahan *difference* form `‖P_A(a₁,b₁] − P_B(a₂,b₂]‖ ≤ ‖A − B‖ / δ` at constant 1: the previous run's recorded next handoff, the delivered product theorem's own open follow-on, and the first consumer of the delivered-but-unconsumed equal-rank identity `ProjectionGap.l2OpNorm_sub_eq_of_rank_eq`. Route worked through before stating: the identity reduces the difference to the one-sided residual `‖(I−Q_B)·P_A‖`, and the commutator/shift engine re-runs verbatim at the complement projector `Q' = I − bandProjector B a₂ b₂` (F1 compression and range invariance reused unchanged; new pieces: the complement-expansion fact — B's out-of-window eigenvalues δ-away from A's window closure, the classical one-sided sin-Θ separation — plus `Q'` commutation/contractivity and a public rank-supplier `rank_bandProjector_eq_card` = in-band eigenvalue count via trace). Pure hard crust, zero new axioms. Landing as new sections of `Perturbation/BandDavisKahan.lean` (shares the private helpers; +1 import ProjectionGap), QA in a new `BandDavisKahanDiff_QA.lean` on the reused `bdkB`/`diag13` fixtures: positive two-route witness at δ = 3/4 (raw lower `1/√10` fully independent vs theorem bound `1`), ε = 0 attainment, margin-corollary instance at δ = 1, and the rank-hypothesis fence refuted in proved form (A = B = `diag13`, windows `(3/2,5/2]` empty vs `(5/2,7/2]` occupied, every other hypothesis verified — exactly `hrank` isolated).

## 2026-08-24T09:12:56Z — Band Davis–Kahan delivered: perturbation stability for band projectors; the proposal COMPLETE, backlog item 9 closed

**Run:** `20260824T081731Z-run-1`  
**Session:** `ses_fcd30e22cffeDeC6TymF1as1zJ`  
**Status:** completed  
**Milestone:** `proposals/band-davis-kahan.md` (new this run, the Active priority table's only High row — the empty High/Medium queue's recorded handoff, backlog item 9's own candidate-first-slice record, and the Davis–Kahan Step-0/1 survey's named follow-on) — **Steps 0+1 delivered in one run, pure hard crust, zero new axioms (count stays 9; `#print axioms` via `wip/bdk_axcheck.lean` on all 5 public + 20 QA declarations: `propext, Classical.choice, Quot.sound` only, every one). QA 1832 → 1852 (`BandDavisKahan_QA` a new Perturbation-domain file at 20). The proposal is COMPLETE; backlog item 9 is closed.**

**Changes:** (1) the new `Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean` (minimal imports PolyFilter + Duhamel; the umbrella importing it): the headline pair `l2OpNorm_bandProjector_mul_bandProjector_le_of_lt`/`_of_gt` — `‖Q * P‖ ≤ ‖A − B‖ / δ` for the band projectors of two symmetric matrices on δ-separated windows, constant 1, no rank hypothesis — by the survey's algebraic commutator/shift route; **the proof's content is the r-cancellation** (the naive single-shift assembly strands `+ r`, exactly the recorded catch that kills the technique at the half-line window; the rescue is range invariance of `A`'s band under the shifted operator, bounding the compressed term by `r · ‖Q * P‖ · ‖y‖` so the `r` cancels algebraically) — load-bearing on four delivered layers at once (Band, Spectral, PolyFilter, Duhamel); plus the two Step-0-priced shelf gaps landed (`l2OpNorm_mulVec_le`, the vector action bound absent from the pinned Mathlib; `mulVec_bandProjector_comm`, the 2026-08-21 survey's spike-verified commutation). (2) `Scaffold/QA/Perturbation/BandDavisKahan_QA.lean` (+20, the `diag13` fixture reused from `Band_QA` plus the rotated `!![1, 3/4; 3/4, 3]`): the positive witness with `‖Q * P‖` pinned from below by `1/√10` completely independently of the theorem (eigenbasis resolution + eigen-equation direction constraints, no `eigvecOf` value assumed) against the delivered `3/4` upper bound; the ε = 0 attainment; the overlapping-window fence **refuted in proved form** with every `hsep`-shaped hypothesis exhibited impossible; the mirror `_of_gt` instance at δ = 1/2. (3) Records: the proposal (status COMPLETE + delivery record with the pin-technique list), `proposals/README.md` (High row → Delivered; progress paragraph), README (1852; proved-list sentence; module-table row), the radar (QA axis 1832/45 → 1852/46 held 4.0), the scoreboard (all four verification rows + an interpretation bullet; regenerated idempotent 1852/9/0), `index/sources/vershynin_hdp.md` (Chapter 4: route reference → the delivered mapping), `index/map/perturbation.md` (new section + 4 rows), backlog item 9 (DELIVERED + follow-on), the umbrella, the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/bdk_spike.lean`, several rounds to green — the sharpest recorded traps: `Matrix.mulVec_mulVec` takes the vector first and `rw` fires on the first-unified instance only, nested associativity identities robust only as explicit calc steps (underscores cause whnf timeouts); `norm_num` evaluates the ite band conditions after the eigenvalue rewrites, leaving exactly the coordinate-square goal; `le_div_iff₀` both projection directions in one proof; `pack_add` needed before `norm_add_le`; QA-side the `Fin 2` eta-expansion `show` technique and `linear_combination` with fixed rational coefficients for the direction constraints); `lake env lean Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean` and on `Scaffold/QA/Perturbation/BandDavisKahan_QA.lean` — zero errors, zero warnings each; `lake build` on both explicit targets ✔ (2192/2192, 2194/2194); `#print axioms` via `wip/bdk_axcheck.lean` on all 25 declarations — the standard three only; **full `lake build` ✔ (2260 targets, +1, "Build completed successfully"; zero warnings in the changed modules — the log's Scaffold-tree warnings are the documented pre-existing set in untouched modules)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1852/9/0**, idempotent).

**Verification:** every changed module elaborates directly with zero errors/warnings and both new modules are linked into the full default build (the QA module additionally certified by its explicit build target). The whole delivery is unconditional hard crust — no axiom is consumed anywhere (`#print axioms`-verified), so there is no conditional-status caveat to carry. QA is load-bearing at three levels: the raw lower-bound route shares no mechanism with the theorem (a wrong constant, window direction, or center/radius instantiation anywhere in the delivered chain contradicts the independent `1/√10` computation); the ε = 0 attainment pins the degenerate case exactly; and the fence exercises the interval-separation hypothesis as a proved refutation, not decoration.

**Remaining risk:** the delivered statement covers the *product* form for interval-separated windows — the *difference* form `‖P_A(S) − P_B(S')‖` (equal-rank identity route) and the eigenvalue-cluster-separated generalization are recorded follow-ons, not gaps in what is claimed. The Vershynin Thm 4.1.15–4.1.16 locator is route provenance for a *proved* statement and carries the repo's standing verify-against-physical-copy caveat. QA is 2×2 fixtures (the strategy's small-fixture precedent); the theorems are size-general, so the risk is QA breadth, not correctness.

**Next handoff:** the Active priority table holds no High and no Medium rows — the center-out policy with the natural candidates on record: the band Davis–Kahan *difference* form (the just-delivered theorem's own recorded follow-on, consuming the delivered equal-rank identity — needs its own proposal entry), directed-axis mixing/rate work (gated on a primitivity-shaped admission), or a named consumer pricing the wide-band minimax filter designs.

## 2026-08-24T08:17:31Z — Band Davis–Kahan in delivery: the bounded-window perturbation theorem for band projectors

**Run:** `20260824T081731Z-run-1`  
**Session:** `ses_fcd30e22cffeDeC6TymF1as1zJ`  
**Status:** superseded (by the completed entry above, same run)  
**Milestone:** `proposals/band-davis-kahan.md` (new this run, added to the Active priority table as its only High row — the empty High/Medium queue's recorded handoff, backlog item 9's own candidate-first-slice record, and the Davis–Kahan Step-0/1 survey's named follow-on): the product-projector bound `δ ‖B_band * A_band‖ ≤ ‖A − B‖` for two δ-separated spectral windows, by the survey's purely algebraic commutator/shift route (Vershynin HDP, route reference) — zero new axioms. Step 0 shelf survey complete: component action (`eigvecOf_dotProduct_bandProjector_mulVec`, PolyFilter), Parseval + eigenaction (Spectral), pairing/norm engine + Cauchy–Schwarz + norm-of-packaged-vector (Duhamel), idempotence + eigenbasis action (Band) all present; two gaps priced and to be landed (the vector action bound `‖M *ᵥ v‖ ≤ ‖M‖ ‖v‖` in the plain sqrt-packaging through `toEuclideanCLM` + `cstar_norm_def`; the operator↔band-projector vector commutation, componentwise). The `r`-cancellation crux worked through by hand: the single-shift inequality strands `+ r` unless the A-compressed term is bounded by `r · ‖QP‖` through range-invariance of A's band — that step is the theorem's mathematical content. Next: proposal record, spike, module `Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean` (two interval-separated theorems + supporting interface), QA `QA/Perturbation/BandDavisKahan_QA.lean` (rotated 2×2 witness with `‖QP‖` pinned from below raw, ε = 0 attainment, overlapping-window refutation fence, mirror instance), full verification battery, records.

## 2026-08-24T07:04:20Z — PolyFilter band projection delivered: the Chebyshev layer's second consumer; the proposal COMPLETE

**Run:** `20260824T064113Z-run-1`  
**Session:** `ses_fcd8744eaffeEX8FvKFeJOs8Y2`  
**Status:** completed  
**Milestone:** `proposals/polyfilter-band-projection.md` (new this run, the Active priority table's only High row — the empty High/Medium queue's recorded handoff, first-named candidate in all three records, and the Krylov Step-0 survey's own named follow-on) — **Steps 0+1 delivered in one run, pure hard crust, zero new axioms (count stays 9; `#print axioms` via `wip/polyfilter_axcheck.lean` on all 7 public + 30 QA declarations: `propext, Classical.choice, Quot.sound` only, every one). QA 1804 → 1832 (`PolyFilter_QA` a new file at 28 by the generator metric). The Krylov Chebyshev scalar layer is now a two-consumer layer and the Band module has its first approximation-theory consumer; the proposal is COMPLETE.**

**Changes:** (1) the new `Scaffold/Mathlib/GraphTheory/PolyFilter.lean` (namespace `SpectralGraphTheory`; minimal imports Band + Krylov + Resolvent; the umbrella importing it): the component-action pair (`eigvecOf_dotProduct_spectralProjector_mulVec`, `eigvecOf_dotProduct_bandProjector_mulVec` — the `dotProduct_eigvecOf_mulVec` mirrors at the two projectors through symmetry + the delivered eigenbasis action, the band one's `a ≤ b` guard load-bearing for the indicator form since the total definition is the negated band at `a > b`); **the filter-agnostic transfer theorem** `aeval_sub_bandProjector_l2OpNorm_le` — within `ε` of `1` at every in-band eigenvalue and of `0` at every out-of-band one ⇒ `‖p(M) − bandProjector M hM a b‖ ≤ ε` — whose proof cashes out the Step-0 survey's decisive structural finding: **no eigenvalues of the difference matrix are computed anywhere** (the Resolvent upper-bridge route: per-mode component identities from Krylov's polynomial transfer and the new band action, termwise-bounded through Parseval, transported by `opNorm_le_bound`/`cstar_norm_def`); the **power instantiation** `powFilter_l2OpNorm_le` (ε = `(t/c)^d`, the power-method rate); `chebyshevFilter` (`T_d ∘ w / T_d(w(Ltop))` at the Krylov `bandMap`) with its closed-form eval; and the **Chebyshev-damped instantiation** `chebyshevFilter_l2OpNorm_le` (ε = `1/T_d(w(Ltop))`) consuming `abs_T_eval_le_one`, `one_le_eval_T_of_one_le`, `bandMap` and three of its four pins. Load-bearing by the strategy's falsifiability test: the transfer theorem consumes the exact shapes of four delivered layers in one statement — a misstatement in any breaks it loudly. (2) `Scaffold/QA/SpectralGraph/PolyFilter_QA.lean` (+28, importing `Band_QA` for the `diag13` fixture — the QA-to-QA reuse precedent): the affine exact filter driving the engine to ε = 0 by theorem and raw routes (both sides pinned entrywise to `diag(0,1)`); the power instantiation with ε **attained** at the low mode and the filtered action cross-checked through the generic eigenvector action at a literal eigenvector; the Chebyshev instantiations at `d = 1, 2` with raw pins `T₁(3) = 3`, `T₂(3) = 17`, `T₁(−1) = −1`, ε attained, and the power-vs-Chebyshev comparison `1/17 < 4/9` proved at one gap; and the fence — the out-of-band quality hypothesis refuted at the low mode and the hypothesis-free conclusion refuted in proved form (`‖1 − B_{2,3}‖ ≥ 1 > 1/2` through the fixed unit vector, the `abs_eigvalOf_le_l2OpNorm` vector technique). (3) Records: the proposal (status COMPLETE, full delivery record with the pin-technique list — the `rw`-order-vs-syntactic-appearance interaction at negated conditions; the `ℤ`-cast trap's QA face, natCast-spelled pins bridged by `push_cast`; the statement-level numeric-default re-hit), `proposals/README.md` (High row retired to the Delivered table, progress paragraph rewritten — the table empty again), README (1832, the status-paragraph sentence, the module-table row), radar (QA axis synced 1804/44 → 1832/45, held 4.0), scoreboard (three verification rows, a new interpretation bullet, regenerated idempotent 1832/9/0), SGT index map (new section + 7 declaration rows), the umbrella, the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/polyfilter_spike.lean` — the transfer engine green on its first complete compile; the instantiation rounds' fixes recorded in the proposal's trap list); `lake env lean Scaffold/Mathlib/GraphTheory/PolyFilter.lean` and on `Scaffold/QA/SpectralGraph/PolyFilter_QA.lean` — zero errors, zero warnings each; `lake build Scaffold.Mathlib.GraphTheory.PolyFilter` ✔ (2051/2051) and `lake build Scaffold.QA.SpectralGraph.PolyFilter_QA` ✔ (2053/2053); `#print axioms` via `wip/polyfilter_axcheck.lean` on all 37 declarations — the standard three only; **full `lake build` ✔ (2259 targets, +1, "Build completed successfully"; zero warnings in the changed modules)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1832/9/0**, idempotent).

**Verification:** every changed module elaborates directly with zero errors/warnings and the new public module is linked into the full default build; the QA module is certified by direct elaboration plus its explicit build target. The whole delivery is unconditional hard crust — no axiom is consumed anywhere (`#print axioms`-verified), so there is no conditional-status caveat to carry. QA is load-bearing at three levels: every raw pin (matrix homomorphism laws, threshold-projector pins, Chebyshev values, the fixed-vector norm lower bound) is independent of the theorems it checks; the ε-attainment witnesses prove the design constants unimprovable rather than merely valid; and the fence exercises the out-of-band hypothesis as a refutation, not decoration.

**Remaining risk:** the delivered instantiations cover the *top-eigenspace* band only — the uniform wide-band pass-filter designs (minimax two-interval approximation) are recorded follow-ons gated on scalar approximation theory absent from the pinned Mathlib, as are the cosh-form non-vacuity corollary and any `d → ∞` limit statement. The transfer engine itself is size-general and filter-agnostic, so those designs would land on it unchanged. QA is a single 2×2 fixture (the strategy's small-fixture precedent), so the risk is QA breadth, not correctness.

**Next handoff:** the Active priority table holds no High and no Medium rows — the center-out policy with the natural candidates on record: directed-axis mixing/rate work (gated on a primitivity-shaped admission), backlog item 9's band Davis–Kahan (own proposal entry + Step-0 survey), or a named consumer pricing the wide-band minimax filter designs.

## 2026-08-24T06:41:13Z — PolyFilter band projection in delivery: the Chebyshev layer's second consumer

**Run:** `20260824T064113Z-run-1`  
**Session:** `ses_fcd8744eaffeEX8FvKFeJOs8Y2`  
**Status:** superseded (by the completed entry above, same run)  
**Milestone:** `proposals/polyfilter-band-projection.md` (new this run, the Active priority table's only High row — the empty High/Medium queue's recorded handoff, first-named candidate in all three records, and the Krylov Step-0 survey's own named follow-on). Step 0 CLEARED the recorded shape `‖p_d(M) − bandProjector M hM a b‖₂ ≤ ε(d, gaps)`: the transfer engine composes four delivered layers (Krylov's polynomial transfer, Band's projector action plus one new component lemma, Spectral's Parseval, Resolvent's norm spine — the survey's key finding is that no eigenvalues of the difference matrix are needed at all), and both instantiations — power filter ε = (t/Ltop)ᵈ and Chebyshev-damped ε = 1/T_d(w(Ltop)) through Krylov's `bandMap` — reduce to proved shelf scalar facts, making this the genuine second consumer of the Chebyshev layer. Step 1 in progress: `GraphTheory.PolyFilter` + QA on the `diag13` fixture (exact-projector recovery, attained ε constants, the power-vs-Chebyshev rate comparison, the out-of-band refutation fence). Pure hard crust, zero new axioms.

## 2026-08-24T05:31:19Z — PageRank delivered: teleportation extends the PF-consumer layer to reducible input; the proposal COMPLETE

**Run:** `20260824T045932Z-run-1`  
**Session:** `ses_fcde1012affej2ys3kGJOju7iK`  
**Status:** completed  
**Milestone:** `proposals/pagerank-distributions.md` (new this run, the Active table's only High row — the empty High/Medium queue's recorded handoff, backlog item 8's named second consumer, the PF admission's own follow-on list) — **Steps 0+1 delivered in one run, zero new axioms (count stays 9; `#print axioms` on all 12 public + 85 QA declarations via `wip/pagerank_axcheck.lean`: the 3 conditional PageRank theorems and the 6 axiom-route QA theorems list `perron_frobenius` + the standard three; the 9 structural public declarations and all other QA declarations — both endpoint refutation fences included — only `propext, Classical.choice, Quot.sound`). QA 1715 → 1804 (`PageRank_QA` a new file at 89 by the generator metric). The proposal is COMPLETE; backlog item 8's named-consumer program (irreducible stationary distributions, PageRank) is now fully delivered.**

**Changes:** (1) the new `Scaffold/Mathlib/GraphTheory/PageRank.lean` (namespace `SpectralGraphTheory`; minimal imports IrreducibleStationary + Normalized; the umbrella importing it): the nine unconditional structural declarations — `googleMatrix` with its entry form `α·P i j + (1−α)·(card V)⁻¹`, `walkTransitionMatrix_nonneg` (the sign-pattern reading, previously inline in the parent engine), `googleMatrix_nonneg`, **the teleportation floor `googleMatrix_pos`** (`0 < G i j` at every pair on `[0,1)` with nonempty `V`, regardless of the input walk's support/reducibility/asymmetry), the α-free `googleMatrix_row_sum` (affine — survives both fence endpoints where uniqueness dies), `googleMatrix_deg_eq_one`, **`googleMatrix_isIrreducible`** (irreducibility *derived*, not assumed: one `ReflTransGen.single` per pair through the floor), and the general bridge **`walkTransitionMatrix_eq_of_row_sum_one`** (any row-stochastic matrix is its own walk transition matrix — the composition point for future row-stochastic consumers) — and the three axiom-**conditional** theorems `exists_pageRankVec` / `existsUnique_pageRankVec` / `pageRankVec_pos`: existence, the `∃!`, and full support of the PageRank distribution on **reducible** input with **no irreducibility hypothesis anywhere**, pure compositions of the same-day `IrreducibleStationary` layer at `M := googleMatrix A α` (every hypothesis derived structurally, the conclusion translated through the bridge) — zero new axiom contact, the two axiom applications staying inside the delivered engine. Statement-shape decisions recorded in the proposal before stating: `0 ≤ α < 1` (not `0 < α` — pure teleportation legitimately covered), `[Nonempty V]` (the floor dies as `0⁻¹ = 0` on the empty type), the row-stochastic/transposed-convention difference from the Page–Brin source recorded in the module docstring, nothing about power-iteration convergence (needs the strict dominance the axiom deliberately does not claim). (2) `Scaffold/QA/SpectralGraph/PageRank_QA.lean` (+89, four sections, reusing `IrreducibleStationary_QA`'s fixtures by QA-to-QA import): structural pins (all 16 entries on the reducible fixture, the floor at a zero-support pair by theorem *and* raw route, row sums both routes, the bridge instantiated); the reducible-input positive witness — uniform `(1/4,1/4,1/4,1/4)` verified **completely raw** with the `∃!` join identifying every stationary distribution with the hand value, on the very fixture whose raw walk has two stationary distributions (the imported fence); the asymmetric star's PageRank `(4/9, 5/18, 5/18)` verified raw and provably **distinct** from the raw stationary `(1/2,1/4,1/4)` — teleportation shifting mass to the leaves, the quantity PageRank exists to compute; and both endpoint fences refuted in proved form with complementary fixtures — `α = 1` (teleportation removed, `googleMatrix A4 1 = walkTransitionMatrix A4` pinned entrywise, the `∃!` refuted through the imported witnesses with degrees/row sums intact, exactly `hα2` isolated) and `α = -1` on `K₂` (the mixture pinned to the identity, two distinct stationary point masses, row stochasticity provably surviving — exactly `hα` isolated). (3) Records: the proposal (status COMPLETE, delivery record with pin-technique notes and open follow-ons), `proposals/README.md` (High row → Delivered, progress paragraph rewritten — the table empty again), README (1804; PF-axiom paragraph's second-consumer sentence + module-table row), radar (QA axis 1715/43 → 1804/44 held 4.0), scoreboard (all four verification rows + interpretation bullet; regenerated idempotent 1804/9/0), SGT index map (new section + 12 declaration rows), backlog item 8 (fifth update), the umbrella `Scaffold.lean`, the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/pagerank_spike.lean` three rounds, `wip/pagerank_qa_spike.lean` two — the fixes recorded in the proposal's pin-technique list: `∑ j` over a constant summand needs its binder annotated (`∑ j : V`); the constant sum `∑ j, n⁻¹ = 1` built *backwards* through `Finset.mul_sum` + `∑ j, 1 = ↑n` (the pin's `Finset.sum_const` gives ℕ-smul with no general cast lemma); the `∃!` destructure needs explicit grouping `⟨π, ⟨h1, h2, h3⟩, huniq⟩` (flat patterns coalesce onto the last field); `Fintype.card_pos` inside `Nat.cast_pos.mpr` strands a `Fintype ?m` metavariable — isolate in a typed `have`; the `fin_cases` `Fin.mk`-index trap re-hit, worked around per the recorded literal-lemma/`simp`-at-predicate-level techniques; `simp` closes `0 ≤ 1/4` but not `0 ≤ 4/9` — append `norm_num`); `lake env lean Scaffold/Mathlib/GraphTheory/PageRank.lean` and on `Scaffold/QA/SpectralGraph/PageRank_QA.lean` — zero errors, zero warnings each; `lake build Scaffold.Mathlib.GraphTheory.PageRank` ✔ then `lake build Scaffold.QA.SpectralGraph.PageRank_QA` ✔; `#print axioms` via `wip/pagerank_axcheck.lean` — the intended split; **full `lake build` ✔ (2258 targets, +1, "Build completed successfully"; zero warnings in the changed modules — the build log's Scaffold-tree warnings are the documented pre-existing set)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1804/9/0**, idempotent).

**Verification:** every changed module elaborates directly with zero errors/warnings and the new public module is linked into the full default build; the QA module is certified by direct elaboration plus its explicit build target. The three PageRank theorems are **conditional on `perron_frobenius`** (verified by `#print axioms`) — Lean-checked deductions through the delivered consumer layer, never described as foundationally proved. QA is load-bearing at both levels: every raw witness (entry pins, both hand values, both fence identities `G(1) = P` and `G(-1) = 1`) is proved independent of the theorems, the `∃!` joins consume the theorems' uniqueness clauses against those raw values (a misstated floor, bridge, row sum, or parent-layer clause breaks a join loudly), and both endpoint hypotheses are *refuted in proved form* with complementary fixtures each violating exactly one — exercised as fences, not decoration.

**Remaining risk:** the theorems cover the stationary theory only — no convergence rate for the PageRank power iteration (strict dominance needs primitivity, which the axiom deliberately does not claim; the follow-on is gated on a primitivity-shaped admission, recorded). Teleportation is uniform only (the personalization-vector generalization `E = v vᵀ` is a recorded follow-on). The star fixture's PageRank was computed by hand from the pinned walk entries, not by an independent solver — the raw route checks stationarity/mass/nonnegativity directly, which is the load-bearing predicate set, but there is no second numeric route to the value itself (mitigated by the ∃! join making the theorem's uniqueness clause responsible for the value's identity). The QA fixtures are 3- and 4-vertex; the theorems are size-general, so the risk is to QA breadth, not correctness.

**Next handoff:** the Active priority table holds no High and no Medium rows — the center-out policy with the natural candidates on record: the Chebyshev-filter second consumer of the Krylov layer (own document, the Krylov Step-0 survey's recorded natural follow-on), directed-axis mixing/rate work (gated on a primitivity-shaped admission), or a backlog-gated item.

## 2026-08-24T04:59:32Z — PageRank in delivery: the teleportation floor extends the PF-consumer layer to reducible input

**Run:** `20260824T045932Z-run-1`  
**Session:** `ses_fcde1012affej2ys3kGJOju7iK`  
**Status:** superseded (by the completed entry above, same run)  
**Milestone:** `proposals/pagerank-distributions.md` (new this run, the Active table's only High row — the empty High/Medium queue's recorded handoff, backlog item 8's named second consumer, the PF admission's own follow-on list). The Google matrix `G = α • P + (1−α) • n⁻¹ • J`: the teleportation floor `0 < G i j` (α ∈ [0,1), nonempty V) makes `G` irreducible unconditionally — reducibility of the input walk is the *point*, not an obstruction — so `existsUnique_stationaryVec_of_irreducible` composes at `G` through the one-line bridge `walkTransitionMatrix M = M` for row-stochastic `M`: the PageRank vector exists, is unique among nonnegative distributions, and has full support, conditional on `perron_frobenius`. Zero new axioms. QA: the reducible two-edge fixture (uniform PageRank, contrasted with the raw walk's two stationary distributions), the asymmetric star at α = 1/2 (`(4/9, 5/18, 5/18)` verified raw, distinct from the raw stationary), and two fences (α = 1 on the reducible fixture — teleportation removed, uniqueness dies; α = −1 on K₂ — `G = 1`, uniqueness dies, exactly `hα` isolated). Spike first, then transfer.



## 2026-08-23T20:12:55Z — Discrete affine convergence delivered: both steps, the proposal COMPLETE

**Run:** `20260823T194800Z-run-1`  
**Session:** `ses_fcfd82a32ffeNysjmJH1Q52ya4`  
**Status:** completed  
**Milestone:** `proposals/discrete-affine-convergence.md` (the Active priority table's single remaining High row — `sgt-gaps.md` item 2, the external `spectral-proof` consumer's named interface, the previous run's recorded next handoff) — **both steps delivered in one run as pure hard crust, zero new axioms (count stays 9; `#print axioms` on all 28 declarations — 3 public + 25 QA — reads only `propext, Classical.choice, Quot.sound`). QA 1546 → 1571 (the new `Dynamics` domain, `DiscreteAffine_QA` a new file at 25). The proposal is COMPLETE; backlog item 5's discrete-affine slice opened (its remaining scope still gated).**

**Changes:** (1) the new `Scaffold/Mathlib/Dynamics/DiscreteAffine.lean` (namespace `Scaffold.Dynamics`, a new `Dynamics` area — no graph structure in the statements, per the proposal's scope note, so not the event-driven `GraphTheory/Dynamics`; minimal imports; the umbrella importing it): `tendsto_pow_smul_atTop_nhds_zero` (`r ^ n • x → 0` for `|r| < 1` — the pin's scalar fact lifted through `Filter.Tendsto.smul_const`), `affineIteration_eq` (the closed form, pure module induction), `affineIteration_tendsto_atTop` (convergence under `0 < α < 2` at the consumer's exact shape); statement-shape decision recorded: all three at a general real normed space, the drafted `V → ℝ`/`Fintype V` shape the instance. (2) `Scaffold/QA/Dynamics/DiscreteAffine_QA.lean` (+25, four sections): the wrapper and the convergence each by **two independent routes** (delivered theorem vs. entrywise/Pi-topology limit from the pin's scalar lemma); the positive fixture with closed form, per-step values, per-coordinate geometric decay, and numeric instances; and the proposal's two mandated boundary witnesses as **proved refutations** with complementary fixtures — `α = 2` oscillation (ε-δ non-convergence, `0 < α` intact, exactly `hα2` isolated) and `α = 0` constancy (`α < 2` intact, exactly `hα0` isolated). (3) Records: the proposal (status COMPLETE, delivery record with pin-technique notes), `proposals/README.md` (High row → Delivered, progress paragraph de-staled with all historical facts preserved in the Delivered table — the three previously paragraph-only slices consolidated into one row), README (1571; module-table row + proved-list sentence), radar (QA axis 1546/40 → 1571/41 held 4.0), scoreboard (three verification rows, lint row, new interpretation bullet; regenerated idempotent 1571/9/0), SGT index map (new section + 3 declaration rows), backlog item 5 (delivery note), the umbrella `Scaffold.lean`, the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/dac_spike.lean`, five rounds to green, the fixes becoming the recorded trap list: `Filter.Tendsto.congr`'s direction needs `Filter.tendsto_congr`'s `.mpr` for the reverse; `← add_smul` fires only after `add_assoc` reassociates `(a+b)+c`; bare `![2,4] i` in standalone ascriptions defaults to `ℕ` — the recorded numeric-default trap re-hit; `|(1:ℝ)/2| < 1` needs `abs_lt` before `norm_num`; `Metric.tendsto_atTop` the clean ε-δ non-convergence refutation engine); `lake env lean` on the module and QA — zero errors, zero warnings each; `lake build Scaffold.Mathlib.Dynamics.DiscreteAffine` ✔ then `lake build Scaffold.QA.Dynamics.DiscreteAffine_QA` ✔; `#print axioms` via `wip/dac_axcheck.lean` — the standard three only, all 28 declarations; **full `lake build` ✔ (2253 targets, +1 for the new umbrella-reachable module; zero warnings in the changed modules — the log's warning mass is the documented Mathlib-internal set)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1571/9/0**, idempotent).

**Verification:** every changed module elaborates directly with zero errors/warnings and the new public module is linked into the full default build; the QA module is certified by direct elaboration plus its explicit build target. The delivery is fully proved hard crust — nothing axiom-backed was added, so nothing is conditional. QA is load-bearing at both levels: each convergence statement is reached by two independent API paths (module-level smul lifting vs. entrywise Pi topology — a wrong lifting constant contradicts the raw route), the closed form and decay are pinned independently of the theorems, and both endpoint hypotheses are *refuted in proved form* with complementary fixtures each violating exactly one hypothesis — exercised as fences, not decoration.

**Remaining risk:** the theorems are stated at general normed-space generality but QA instantiates only the consumer's `Fin 2 → ℝ` case — the generality is free (the proofs never use finiteness) and the fixtures exercise the exact requested interface, so the risk is to QA breadth, not correctness. The external `spectral-proof` consumer has not yet been run against the delivered interface — its verification is outside this repository's authority. The proposals/README.md progress-paragraph consolidation relocated three delivery facts into a single Delivered-table row (band Step 1, mixing Step 1, mixing Step 3-component-1) — flagged for operator review as a deliberate de-staling.

**Next handoff:** the Active priority table holds no High rows — the Medium rows by leverage, starting with **approximate spectral projection Step 1a** (`proposals/approximate-spectral-projection.md` — the interface layer: the spike's four green lemmas plus the two priced shallow gaps into a new shelf module), then 1b (spectral discharge), 1c (statement + QA). The PF consumers (irreducible stationary distributions, PageRank) remain new-proposal candidates per the one-step discipline.

## 2026-08-23T19:48:00Z — Discrete affine convergence in delivery: the finite-vector decay wrapper + affine-iteration theorem

**Run:** `20260823T194800Z-run-1`  
**Session:** `ses_fcfd82a32ffeNysjmJH1Q52ya4`  
**Status:** in-progress  
**Milestone:** `proposals/discrete-affine-convergence.md` (the Active priority table's single remaining High row — `sgt-gaps.md` item 2, the external `spectral-proof` consumer's named interface, the previous run's recorded next handoff, and the proposal's own "authorized to begin immediately"). Step 1: the finite-vector geometric-decay wrapper `r ^ n • x → 0` for `|r| < 1` (pin's `tendsto_pow_atTop_nhds_zero_of_abs_lt_one` lifted through the pin's `Filter.Tendsto.smul_const` — both verified present in the pin before stating). Step 2: the affine-iteration convergence theorem (closed form by induction, then Step 1 at `r = 1 − α` under `0 < α < 2`). New focused module `Scaffold/Mathlib/Dynamics/DiscreteAffine.lean` (no graph structure in the statement — the proposal's own scope note — so not the event-driven `GraphTheory/Dynamics`); QA with the proposal's named witnesses (positive closed-form fixture; α = 2 oscillation refutation; α = 0 constancy refutation). Zero new axioms. Spike first, then transfer. Prior run's uncommitted Tikhonov Phase-2 delivery preserved untouched.

## 2026-08-23T19:01:27Z — Tikhonov Phase 2 delivered: the hard-filter limit + tail suppression; the proposal COMPLETE

**Run:** `20260823T183842Z-run-1`  
**Session:** `ses_fd01be2feffercFUCX8jzFXW4s`  
**Status:** completed  
**Milestone:** `proposals/tikhonov-shrinkage-filter.md` Phase 2 — the hard-filter limit and finite tail suppression (the Active priority table's first remaining High row, the external `sgt-gaps.md` item-1 consumer interface, and the execution plan's recorded next handoff), both steps delivered in one run as pure hard crust (**zero new axioms**, count stays 9; `#print axioms` on all three public and all 24 QA declarations reads only `propext, Classical.choice, Quot.sound`). QA 1522 → 1546 (`Tikhonov_QA` +24). **The proposal is COMPLETE** (original steps 2026-08-20, Phase 2 this run — the count was 12 at the first delivery, 9 unchanged at the second).

**Changes:** (1) `GraphTheory/Tikhonov.lean` Section 5: `tikhonovShrinkage_tendsto_zero` — the consumer's exact statement, two-sided (`𝓝 0`), via `ContinuousAt.div` at the nonzero denominator; `tikhonovShrinkage_tail_energy_tendsto_zero` — tail suppression for a *general symmetric matrix* (statement-shape decision: nothing in the proof uses PSD or the Laplacian, the `dotProduct_eigvecOf_filter` generality precedent), each tail term by Step 1 at its own eigenvalue, the sum by `tendsto_finset_sum`; `tikhonovMinimizer_tail_energy_tendsto_zero` — the consumer-facing Laplacian minimizer form, composed through the coefficient identity. **Suppression-stated per the requester's explicit non-overclaim instruction** — no band-projector convergence claimed in any statement or docstring. (2) `Tikhonov_QA.lean` +24 in three sections: the two-mode tail on the diagonal `diag13` fixture *reused from `Band_QA`* (QA-to-QA import, the DavisKahan/Weyl precedent) — energy pinned in closed form `tikhonovShrinkage π 1 ^ 2`, evaluated `1/121` at `π = 1/10` and `1/10201` at `π = 1/100`, corollary consumed at a concrete tolerance; the scalar `lam = 0` refutation (the hypothesis-free form false — no limit at all); the `K₂` tail boundary refutation (kernel mode included ⇒ energy provably `≥ 1/2` at every nonzero `π`, from the kernel-eigenvector line + unit norm + Parseval — the requester's mandated "mode below lam" witness); the minimizer-form instantiation with the `π = 1` tail energy pinned to `1/18`. (3) Records: the proposal (status header COMPLETE, Phase-2 delivery record with pin-technique notes), `proposals/README.md` (High row retired to Delivered, progress paragraph, delivered-table row), README (1546, Tikhonov proved-list entry), radar (QA axis 1522/40 → 1546/40 held 4.0, assurance-log note), scoreboard (three verification rows, lint row, new interpretation bullet; regenerated idempotent 1546/9/0), SGT index map (+3 rows, Phase-2 status), the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/tikP2_spike.lean`, several rounds to green, the fixes becoming the recorded trap list: `𝓝` needs `open scoped Topology`; `λ` in identifiers (`hλi`) unlexable — the ASP Step-0 trap re-hit; `tendsto_finset_sum` a non-greppable `to_additive` child of `tendsto_finset_prod` (re-verified the recorded `Finset.sum_neg_distrib` phenomenon); `tendsto_const_nhds`'s value implicit ⇒ ascribed `have` before `.mul`; coefficient lemmas in square shape cannot rewrite under an outer square ⇒ term-form `(a·b)² = a²·b²` lemmas; `fin_cases`-on-witness beta-redexes dissolved by type-ascribed `have`s; `Metric.tendsto_nhds_nhds`'s ε-δ form needs `Real.dist_eq, sub_zero`); `lake env lean` on the module and QA — zero errors, zero warnings each; `lake build Scaffold.Mathlib.GraphTheory.Tikhonov` ✔ then `lake build Scaffold.QA.SpectralGraph.Tikhonov_QA` ✔; `#print axioms` via `wip/tikP2_axcheck2.lean` — the standard three only; **full `lake build` ✔ (2252 targets, "Build completed successfully"; zero warnings in the changed modules)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1546/9/0**, idempotent).

**Verification:** every changed module elaborates directly with zero errors/warnings and is linked into the full default build; QA built by explicit target. The delivery is fully proved hard crust — nothing axiom-backed was added, so nothing is conditional. QA is load-bearing at both hypothesis levels: the closed-form two-mode pin means a wrong limit/factor/eigenvalue anywhere in the delivered chain contradicts an independent exact computation (`1/121`, `1/10201`), and both hypothesis-dropped forms are *refuted in proved form* (the scalar `lam = 0` form has no limit; the tail form with the kernel mode included stays `≥ 1/2`), so the hypotheses are exercised as fences, not decoration.

**Remaining risk:** the tail statement is per-selected-`Finset` — the consumer constructs its own selection; no claim about modes below `lam` is made or should be inferred (the boundary refutation is the fence). The `diag13` positive witness is 2×2 (a two-mode tail needs exactly a separated two-mode fixture; the closed form holds for all `π`, mitigating size-dependence — the theorems are size-general, so the risk is to QA coverage, not correctness). The external `spectral-proof` consumer has not yet been run against the delivered interface — its verification is outside this repository's authority.

**Next handoff:** the Active priority table's single remaining High row — **discrete affine convergence** (`proposals/discrete-affine-convergence.md`, `sgt-gaps.md` item 2: the finite-vector wrapper around the pin's `tendsto_pow_atTop_nhds_zero_of_abs_lt_one` plus the linear affine-iteration convergence theorem); then the Medium rows by leverage (approximate spectral projection Step 1a, the recorded open next step of its Step-0 survey).

## 2026-08-23T18:38:42Z — Tikhonov Phase 2 in delivery: the hard-filter limit + tail suppression

**Run:** `20260823T183842Z-run-1`  
**Session:** `ses_fd01be2feffercFUCX8jzFXW4s`  
**Status:** in-progress  
**Milestone:** `proposals/tikhonov-shrinkage-filter.md` Phase 2 (the Active priority table's first remaining High row — `sgt-gaps.md` item 1, a real external named consumer — and the execution plan's recorded next handoff). Step 1: `tikhonovShrinkage_tendsto_zero`, the scalar hard-filter limit at fixed `0 < lam`, in the consumer's exact two-sided `𝓝 0` shape. Step 2: the finite tail-suppression corollary, stated as suppression of the selected positive-eigenvalue tail (the requester's explicit non-overclaim instruction — no band-projector convergence phrasing), in a general symmetric-matrix coefficient form plus the Laplacian minimizer wrapper. Zero new axioms. QA: a two-mode tail on a diagonal fixture with the energy pinned in closed form and evaluated at decreasing π; the `lam = 0` scalar refutation and the tail-level refutation with the kernel mode included. Spike first, then transfer.

## 2026-08-23T14:05:44Z — Approximate spectral projection Step 0 delivered: Lanczos/Kaniel–Paige cleared; green axiom-clean skeleton spike

**Run:** `20260823T132040Z-run-1`  
**Session:** `ses_fd13aa4c3ffezaE4dDPuy193Fy`  
**Status:** completed  
**Milestone:** `proposals/approximate-spectral-projection.md` Step 0 — the mandatory scoping survey (the top Medium row with the Active table holding no High rows; both the heat-semigroup completion's next handoff and the execution plan named exactly this run). **Deliverable: the Lanczos/Kaniel–Paige shape is CLEARED as the one tractable shape**, recorded in the proposal's full Step-0 record (exact finite-`k` statement, machinery checklist with every dependency verified against pin and shelf, ~600–800-line Step-1 decomposition into 1a/1b/1c, per-shape decisions) plus a green axiom-clean skeleton spike — zero shelf Lean changes (count stays 9, QA stays 1503), the Cheeger Step-0 precedent followed exactly.

**Changes:** (1) `proposals/approximate-spectral-projection.md`: the Step-0 record — the **exact finite-`k` statement in existence form** (for symmetric `M` with simple top eigenvalue and unit `b = cos φ • u + sin φ • g`, the Krylov space `span{b, Mb, …, Mᵏ⁻¹b}` contains nonzero `x` with `λ₁ − R_M(x) ≤ (λ₁−λₙ)·tan²φ / T_{k−1}(1+2γ)²`; recorded shape decisions: no sup, no tridiagonal iteration, Chebyshev value explicit, `λ`-name lexical note); the **machinery checklist** (shelf: eigenbasis/Parseval/Rayleigh-sandwich/`Heat.pow_mulVec_smul`; pin: `T_real_cos` and the `aeval` layer; priced gaps: `Matrix.sum_mulVec`, `natDegree T`, cosh growth); the **skeleton-spike evidence**; the **Step-1 authorization** (1a interface layer → 1b spectral discharge → 1c statement + QA with the diagonal-3×3 two-route witness, `k = 1` case, `b = u` tightness, `λ₁ = λ₂` guard refutation); the **per-shape decisions** (Nyström deferred — sampling concentration and `Matrix.pinv` both absent; Chebyshev filters recorded as the second consumer, its original band-projector gate having dissolved 2026-08-20/21); and the **pin-technique record**. (2) `wip/asp_step0_spike.lean` (git-ignored): four declarations, all green, every `#print axioms` exactly `propext, Classical.choice, Quot.sound` — `abs_T_eval_le_one` (the Chebyshev band bound from `T_real_cos` + `Real.cos_arccos` + `Real.cos_mem_Icc`), `aeval_mulVec_eq_eval_smul` (polynomial action on eigenvectors, consuming `Heat.pow_mulVec_smul`), `aeval_mulVec_mem_krylovSpan` (Krylov membership, via the pin-gap `sum_mulVec` helper), and `kanielPaigeSkeleton` — the full Kaniel–Paige bound in hypothesis form, the spectral layer entering as five named discharge sites (`hp₁`/`horth`/`horthM`/`hbottom`/`hband`), proving the bound composes from exactly those plus the interface pieces. (3) Records: `proposals/README.md` (the Medium row), the execution plan (active milestone → None, the Step-0 delivered entry, next handoff → Step 1a), this log.

**Decisive commands and outcomes:** `lake env lean wip/asp_step0_spike.lean` — **zero errors, zero warnings; all four `#print axioms` the standard three** (roughly a dozen compile iterations; the fixes became the recorded technique list, the decisive one being that **the shelf's SGT interface is `V : Type` (Type 0) — matching it dissolved four apparent cross-module elaboration traps** (`rayleigh` and `Heat.pow_mulVec_smul` both fail to apply from a `Type*` context with postponed-instance stuck elaboration); others: `λ₁` not a lexable identifier, the pin's `pow_succ`/`mul_pow` orientations, `div_le_div_iff₀`, `Finset.induction`'s 2-binder insert case, the dependent `Finset.sum_comm` signature, `nlinarith`'s association-overload timeout fixed by `set` abbreviations); `python3 scripts/lint_axioms.py` (9, unchanged) — no issues; `check_citations` — pass; `check_markdown_links` — pass; `generate_qa_scoreboard.py` — regenerated idempotent (**1503/9/0**); `git status` — only the intended record/proposal files changed, the prior run's uncommitted heat delivery preserved untouched, spike confirmed git-ignored.

**Verification:** the spike is the tractability evidence: every load-bearing interface piece elaborated green with real proofs, and the hypothesis-form assembly proves the exact bound composes from the named spectral-layer discharge sites — no mathematical obstruction surfaced anywhere. No shelf or QA module was touched, so no module builds were required beyond the spike's elaboration against the built oleans; the axiom/QA counts are unchanged by construction and re-verified by the linter and the regenerated scoreboard.

**Remaining risk:** the cleared statement is exact-arithmetic/variational — no Lanczos recurrence, no rounding; the algorithm-to-quantity correspondence is deliberately out of scope (recorded). Step 1b's spectral discharge is priced medium-risk (expansion plumbing, all inputs verified present but not yet assembled). The Saad/Trefethen–Bau citations remain unverified against physical copies per the proposal's own clean-room note — nothing axiom-backed was added, so nothing is conditional.

**Next handoff:** **Step 1a — the interface layer** (one run): transfer the spike's four real lemmas plus the two priced shallow gaps (`natDegree (T ℝ n) = n`; the `1 ≤ T_m(x)` growth lemma at `x ≥ 1`) into a new shelf module (`GraphTheory/Krylov.lean` or an appropriate section), with the module-level survey note and the pin-technique record. Then 1b (the spectral discharge), then 1c (statement + QA). The proposal's operating instructions gate Step 1 to the cleared shape only, one shape per run, no new axioms.

## 2026-08-23T13:20:40Z — Approximate spectral projection Step 0 in delivery: the Lanczos-first scoping survey

**Run:** `20260823T132040Z-run-1`  
**Session:** `ses_fd13aa4c3ffezaE4dDPuy193Fy`  
**Status:** in-progress  
**Milestone:** `proposals/approximate-spectral-projection.md` Step 0 — the mandatory scoping survey (the top Medium row with the Active table holding no High rows; both the heat-semigroup completion's next handoff and the execution plan name exactly this run). For each of the three candidate shapes, in the proposal's own cost order (Lanczos, Nyström, Chebyshev filters): write the exact finite-`k` statement, check every proof dependency against the pinned Mathlib and the Scaffold shelf, record a real cost estimate, and decide — "not tractable at reasonable cost" is a valid recorded outcome that iceboxes the proposal. If a shape clears, verify the load-bearing skeleton as a green axiom-clean `wip/` spike in hypothesis form (the Cheeger Step-0 precedent). No new axioms; no shelf Lean changes authorized in this run.

## 2026-08-23T12:16:08Z — Reversibility Phase B Step 4 delivered: eigenmode decay + the DC limit; the proposal COMPLETE, the external consumer's interface fully discharged

**Run:** `20260823T112921Z-run-1`  
**Session:** `ses_fd1a53ce2ffeHLgMhDxvA6LrRM`  
**Status:** completed  
**Milestone:** `proposals/reversibility-and-heat-semigroup.md` Phase B Step 4 — the payoff statement, delivered as pure hard crust in `GraphTheory.Heat` (**zero new axioms**, count stays 9 at every Phase B step; `#print axioms` on all thirty-one new/rewritten public and QA declarations reads only `propext, Classical.choice, Quot.sound`). QA 1482 → 1503 (`Heat_QA` 25 → 46). **The proposal is COMPLETE** — the external consumer's (`sgt-gaps.md`) four-item interface (heat evolution on `laplacian A`, identity + semigroup law, mass conservation, eigenmode decay with the connected-graph DC-limit consequence) is fully discharged as hard crust. Radar axis 5 **re-scored 3.5 → 4.0** — the named trigger fired.

**Changes:** (1) `GraphTheory/Heat.lean`: the **eigenmode engine** `exp_mulVec_eq_smul_of_mulVec_eq_smul` (`M *ᵥ v = μ • v → exp ℝ M *ᵥ v = Real.exp μ • v`) — the load-bearing bridge the plan's Step-3 note required, its proof *being* Step 3's `expSeries_hasSum_exp` pushed through the continuous action at an eigenvector (`HasSum.map`), terms collapsed by the new power lemma `pow_mulVec_smul`, the scalar series summed by the pin's `NormedSpace.exp_series_hasSum_exp'` at ℝ via `Real.exp_eq_exp_ℝ`; Step 3's kernel engine re-derived as the `μ = 0` case at unchanged statement; the **rank-one-idempotent collapse** `exp_eq_one_add_of_mul_self_eq_smul` (`M * M = c • M → exp = 1 + ((exp c − 1)/c) • M`; scalar tail shifted by the pin's topological-group `hasSum_nat_add_iff'` — the pin has *no* plain tail-shift `HasSum` lemma — reassembled on `tsum_eq_zero_add` + `tsum_smul_const`); `heatKernel_mulVec_eigvecOf` (mode decay at every time); `heatKernel_decayFactor_antitone` + `_le_one` (the proposal's named monotonicity + PSD dissipation); the **eigenbasis expansion** `heatKernel_mulVec_eq_sum` (the spectral-calculus identity in action form — the recorded statement-shape decision: on `eigvecOf`/`eigvalOf` where the machinery lives, the sorted statement scalar); `tendsto_exp_neg_mul_atTop`; and the payoff **`heatKernel_mulVec_tendsto_atTop`** — on connected symmetric nonnegative graphs the heat flow of any vector converges to its mean `((∑ j, x j)/|V|) • onesVec` (PSD, kernel-mode existence via `det L = 0` + `det_eq_prod_eigenvalues`, the kernel characterization with uniqueness-by-orthogonality on the Fiedler line-template, finite-sum limit passage). (2) `Heat_QA.lean` +21: eigenmode decay **two independent routes to one statement** on K₂ (engine vs the new closed form `1 + ((e^{−2t} − 1)/2) • L` + hand arithmetic); the **engine⇄collapse cross-validation** at a nonzero eigenvalue (`exp m2 *ᵥ ![1,1] = e² • ![1,1]` both ways); the K₂ Laplacian **spectrum pinned `[0, 2]`** from trace/determinant/sortedness with the monotonicity instantiation `e^{−2} ≤ 1` reading both constants from the pin; and **the DC limit by two routes** (theorem with hand-computed mean vs the raw route `![2 − e^{−2t}, 2 + e^{−2t}] → ![2,2]` through the scalar decay lemma — independent of the theorem, the kernel characterization, PSD, and the eigenbasis). (3) Records: the proposal (status header COMPLETE, Step-4 delivery record with pin-technique notes, open-next-step closed), `proposals/README.md` (High row retired to Delivered; the Active table now holds no High rows), README (1503, proved-list + module-table updates), the radar (axis 5 **3.5 → 4.0**, Weakest-axes paragraph, QA axis count 1482/40 → 1503/40 held 4.0, assurance-log entry), the scoreboard (both Direct rows, `lake build` row, lint row, a new interpretation bullet; regenerated 1503/9/0 idempotent), the SGT index map (Heat +10 rows, status Steps 0–4 COMPLETE), the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/heat_step4_spike.lean`, six rounds to green — the fixes became the recorded trap list: `∑' (fun …)` missing-comma parse traps; the pin's `HasSum.congr`/tail-shift/`sum_range_1` absences with their replacements (`hasSum_of_eq` wrapper, `hasSum_nat_add_iff'` + `sum_range_succ`, explicit `show` after `exp_eq_tsum`'s beta-redex); `Filter.Tendsto.congr` taking pointwise-∀ not `EventuallyEq`; `rw` failing under binders (→ `simp only [theorem]`); ℕ-defaulting of bare scalar literals in vector statements (→ ascriptions); `div_mul_cancel₀`'s value-first argument order; `neg_pos` mis-elaborating); `lake env lean Scaffold/Mathlib/GraphTheory/Heat.lean` — zero errors, zero warnings; `lake build Scaffold.Mathlib.GraphTheory.Heat` ✔ then `lake env lean Scaffold/QA/SpectralGraph/Heat_QA.lean` — zero errors, zero warnings; `lake build Scaffold.QA.SpectralGraph.Heat_QA` ✔; `#print axioms` via `wip/heat_step4_axcheck.lean` on all thirty-one declarations — the standard three only; **full `lake build` ✔ (2252 targets, "Build completed successfully", detached per the recorded procedure; no warnings in the changed modules)**; `lint_axioms` (9, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1503/9/0**, idempotent under re-run).

**Verification:** every changed module elaborates directly with zero errors/warnings and is linked into the full default build; QA built by explicit target. The delivery is fully proved hard crust — nothing axiom-backed was added, so nothing is conditional. QA is load-bearing through route independence at every new theorem family (mode decay and the DC limit each proved twice by unrelated routes, so a wrong sign/factor/eigenvalue anywhere in either delivered chain contradicts an independent computation), through the cross-validation of the two new engines against each other, and through the spectrum pin (the monotonicity instantiation's constants read from trace/determinant arithmetic, not from the theorem).

**Remaining risk:** the DC limit is stated for the combinatorial Laplacian on symmetric nonnegative connected weights — the normalized-Laplacian analogue (the form the discrete mixing program's χ² statement takes) would be a new consumer-driven step, not claimed here. The QA fixtures are 2×2; the symbolic-time closed forms mitigate but do not eliminate size-dependence (the theorems are size-general; the risk is to QA coverage, not correctness). The `spectral-proof` external consumer has not yet been run against the delivered interface — its verification is outside this repository's authority.

**Next handoff:** no High rows remain in the Active priority table — next run falls through to the Medium rows by leverage: **approximate spectral projection** (`approximate-spectral-projection.md`, Step 0 first; "not tractable at reasonable cost" is a valid recorded outcome), with the PF consumers (irreducible stationary distributions, PageRank) as new-proposal candidates needing their own documents.

## 2026-08-23T11:29:21Z — Reversibility Phase B Step 4 in delivery: eigenmode decay + the connected-graph DC limit

**Run:** `20260823T112921Z-run-1`  
**Session:** `ses_fd1a53ce2ffeHLgMhDxvA6LrRM`  
**Status:** in-progress  
**Milestone:** `proposals/reversibility-and-heat-semigroup.md` Phase B Step 4 — the payoff statement: eigenmode decay through the proved orthonormal eigenbasis (`heatKernel A t *ᵥ eigvecOf i = e^{-t·λᵢ} • eigvecOf i`), the sorted-spectrum decay-factor monotonicity, the eigenbasis expansion of the heat action, and the connected-graph DC limit (free diffusion leaves only the mean component as `t → ∞`); pure hard crust, zero new axioms (the Active table's single High row at its recorded open next step — priority-0 rule). Pre-edit survey recorded in the execution plan: the eigenmode identity is proved *through* Step 3's `expSeries_hasSum_exp` bridge (generalized eigen-engine with the scalar series from `NormedSpace.exp_series_hasSum_exp'`); the DC limit assembles `laplacian_psd`/`quadForm_eigvecOf_self`, kernel-mode existence via `det L = 0` + `det_eq_prod_eigenvalues`, uniqueness by the Fiedler line-template, convergence via `Real.tendsto_exp_atBot` + finite-sum tendsto; a new `M * M = c • M` exponential collapse supplies the symbolic-`t` closed form on K₂ for two-route QA.

## 2026-08-23T10:19:26Z — Reversibility Phase B Step 3 delivered: mass conservation; the external consumer's three-item interface complete

**Run:** `20260823T092311Z-run-1`  
**Session:** `ses_fd223eb78ffe9qQj2p1mM0F3R7`  
**Status:** completed  
**Milestone:** `proposals/reversibility-and-heat-semigroup.md` Phase B Step 3 — mass conservation `heatKernel_mulVec_onesVec` (`heatKernel A t *ᵥ onesVec = onesVec` at every time, **hypothesis-free**), delivered as pure hard crust in `GraphTheory.Heat` (**zero new axioms**, count stays 9; `#print axioms` on all six new public and all eight new QA declarations reads only `propext, Classical.choice, Quot.sound`). QA 1474 → 1482 (`Heat_QA` 17 → 25). The Active priority table's single High row at its recorded open next step (priority-0 rule). With Steps 1–2, the external consumer's (`sgt-gaps.md`) three-item interface — identity, semigroup law, mass conservation — is now complete hard crust.

**Changes:** (1) `GraphTheory/Heat.lean`: the Step-3 section — the general kernel-vector engine `exp_mulVec_eq_of_mulVec_eq_zero` (`M *ᵥ v = 0 → exp ℝ M *ᵥ v = v`, conservation for *any* Laplacian-harmonic vector, not just `onesVec`) and the headline `heatKernel_mulVec_onesVec` (through the shelf's `laplacian_ones_in_kernel`; the Laplacian's row sums vanish identically, so no symmetry is needed); beneath them the summability infrastructure the proof had to build — the entrywise power bound `abs_pow_apply_le` (`|(M ^ n) i j| ≤ (∑ p q, |M p q|) ^ n`, `Matrix.mul_apply`-induction, norm-free), the comparison `summable_exp_term` (against `Real.summable_pow_div_factorial`), the pin-gap Pi-HasSum assembler `hasSum_pi` (the pin carries no `hasSum_pi`/`summable_pi` lemmas at all; assembled from `Filter.tendsto_pi_nhds` + `Finset.sum_apply`), and the assembled convergence `expSeries_hasSum_exp` (the exponential series converges to `NormedSpace.exp ℝ M` in the entrywise topology — the content the pin's normed `expSeries_summable'` does not provide at matrix type, and the foundation Step 4's eigenbasis expansion builds on). (2) `Heat_QA.lean` +8: conservation by two independent routes (theorem on the asymmetric fixture vs the closed form `!![1-t, t; -t, 1+t]` hand-multiplied onto `onesVec`), the raw kernel-instance check, the symmetric-fixture instantiation, the proposal's named **per-component no-leakage witness** on the new disconnected `Fin 3` fixture `disAdj` (the `{0,1}`-component indicator checked `L`-harmonic raw from the definitions then fixed by the engine at every time; the isolated-vertex indicator fixed too — heat provably does not cross components, so conservation is not accidentally vacuous on disconnected input), and the kernel-hypothesis guard (a non-kernel vector provably *not* fixed, `![0,-1] ≠ ![1,0]` — the hypothesis-free strengthening refuted with every other structural fact intact). (3) Records: the proposal (status header, Step-3 delivery record with pin-specific technique notes, open-next-step → Step 4), `proposals/README.md` (High row, progress paragraph, new Delivered row), README (1482; heat-semigroup sentence and module-table row gaining mass conservation), radar (axis 5 **held at 3.5** per protocol — the three-item interface complete but eigenmode decay (Step 4) the named re-score trigger; QA axis synced 1474/40 → 1482/40, held at 4.0), scoreboard (both Direct rows, `lake build`, lint, new interpretation bullet; regenerated idempotent at 1482/9/0), the SGT index map (Heat section +6 declaration rows, status → Steps 0–3), the execution plan (Step 3 retired to Delivered with the survey record; active milestone set to Step 4), and this log. Nothing committed; the prior runs' uncommitted deliveries preserved untouched.

**Decisive commands and outcomes:** spike first (`wip/heat_step3_spike.lean`, five rounds to green — the fixes were exactly the recorded trap list: `n !⁻¹` must be `(Nat.factorial n : ℝ)⁻¹`; application binds tighter than `^` so `(M ^ n) i j` needs parens; `pow_succ'` factors the wrong way (`a^(n+1) = a * a^n`) so the power annihilation goes through `pow_add` + `pow_one`; `Filter.tendsto_congr` is namespaced under `Filter`; `Finset.sum_apply` takes the index first; `Finset.sum_le_sum` needs `f`/`g` named args or the instance synthesis hangs on a metavariable; `Finset.sum_le_sum_of_subset` is canonically-ordered-only at this pin, so the singleton column bound goes through `Finset.sum_insert`/`insert_erase` + `le_add_of_nonneg_right`); `lake env lean Scaffold/Mathlib/GraphTheory/Heat.lean` — zero errors, zero warnings; `lake build Scaffold.Mathlib.GraphTheory.Heat` then `lake env lean Scaffold/QA/SpectralGraph/Heat_QA.lean` — zero errors, zero warnings (QA consumes the built olean, so the module build precedes the QA elaboration); `lake build Scaffold.QA.SpectralGraph.Heat_QA` ✔; `#print axioms` via `wip/heat_step3_axcheck.lean` on all fourteen new declarations — the standard three only; **full `lake build` ✔ (2252 targets, "Build completed successfully", detached per the recorded procedure)**; `lint_axioms` (9, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1482/9/0**). QA-side trap recorded: `Fin 3` cons-literals resist `simp`'s index-2 reduction, `fin_cases`' `⟨n, ⋯⟩`-form indices resist `rfl`, and kernel `decide` is blocked by `Real.decidableEq`'s classical path — the robust fixture encoding is an entrywise function with function-form indicators.

**Verification:** every changed module elaborates directly with zero errors/warnings and is linked into the full default build; QA built by explicit target per the recorded scope. The delivery is fully proved hard crust — nothing axiom-backed was added, so nothing is conditional. QA is load-bearing through route independence (the hand multiplication computes the same conservation the theorem produces, so a wrong sign/factor/transpose anywhere in the delivered chain contradicts an independent computation), through the per-component witness (the engine's per-kernel-vector generality consumed on genuinely disconnected input, with the harmonic check computed raw from the definitions — a mis-shaped `laplacian` would break it), and through the guard (the engine's kernel hypothesis tied to a refuted hypothesis-free form at a fixture where every other fact holds).

**Remaining risk:** `expSeries_hasSum_exp` states convergence in the entrywise topology with no rate; Step 4's eigenbasis expansion will need to identify `heatKernel` with the spectral sum, and the identification route (comparing two HasSums / applying `HasSum.unique`) is not yet scoped — the recorded suggestion is to make the Step-4 identity *consume* Step 3's convergence rather than sit beside it. The QA fixtures are 2×2 and 3×3; the symbolic-time instances mitigate but do not eliminate size-dependence (the theorems themselves are size-general, so the risk is to QA coverage, not correctness).

**Next handoff:** **Reversibility Phase B Step 4** — eigenmode decay: the spectral-calculus identity `heatKernel A t = ∑ k, Real.exp (-t * evals hA k) • spectralProjector …` through the proved eigenbasis, the decay-factor monotonicity theorem for sorted eigenvalues at `t ≥ 0`, and the connected-graph DC-limit consequence (the proposal's payoff statement; see the execution plan's active milestone for the selected scope and the load-bearing suggestion). After Phase B completes: the remaining Medium rows by leverage (approximate spectral projection Step 0; the PF consumers as new-proposal candidates).

## 2026-08-23T09:23:11Z — Reversibility Phase B Step 3 in delivery: mass conservation through the exponential series

**Run:** `20260823T092311Z-run-1`  
**Session:** `ses_fd223eb78ffe9qQj2p1mM0F3R7`  
**Status:** in-progress  
**Milestone:** `proposals/reversibility-and-heat-semigroup.md` Phase B Step 3 — mass conservation `heatKernel A t *ᵥ onesVec = onesVec` (`GraphTheory.Heat`, zero new axioms; the Active table's single High row at its recorded open next step — priority-0 rule). Pre-edit survey recorded in the proposal-facing plan: `NormedSpace.exp` is topological-algebra-level at this pin (no matrix norm needed), the pin lacks Pi-HasSum/summability lemmas entirely, and the selected route is entrywise (power bound `|Mⁿ i j| ≤ Bⁿ`, `Real.summable_pow_div_factorial` comparison, a pin-gap `hasSum_pi` helper, `HasSum.map` with the continuous additive action, `{0}`-support collapse), with QA on the square-zero fixture by two routes and the proposal's named per-component no-leakage witness.

## 2026-08-23T08:02:36Z — Reversibility Phase B Step 2 delivered: the heat semigroup law; the external consumer's two-item core interface complete

**Run:** `20260823T074418Z-run-1`  
**Session:** `ses_fd26d3834ffeRJpkHWkPjluTa7`  
**Status:** completed  
**Milestone:** `proposals/reversibility-and-heat-semigroup.md` Phase B Step 2 — the semigroup property `heatKernel_mul_heatKernel` (`heatKernel A s * heatKernel A t = heatKernel A (s + t)`, hypothesis-free), delivered as pure hard crust in `GraphTheory.Heat` (**zero new axioms**, count stays 9; `#print axioms` on both new public and all seven new QA declarations reads only `propext, Classical.choice, Quot.sound`). QA 1467 → 1474 (`Heat_QA` 10 → 17). The Active priority table's single High row at its recorded open next step (priority-0 rule). With Step 1's time-zero identity, the external consumer's (`sgt-gaps.md`) two-item core interface — "identity at time zero + semigroup law" — is now complete hard crust.

**Changes:** (1) `GraphTheory/Heat.lean`: the semigroup law via the pin's `Matrix.exp_add_of_commute` at the commuting negated scalar multiples of `laplacian A` (`(s • L) * (t • L) = (s * t) • (L * L)` both ways through `Algebra.smul_mul_assoc`/`Algebra.mul_smul_comm`/`smul_smul`; joined exponent reduced by `neg_add` + `add_smul`), **no ball/radius hypothesis** — the Step-0 survey's norm-free finding held exactly (re-verified against the pinned source: the wrapper `letI`s the `linftyOp` norm inside its own proof); plus the every-time square-zero collapse `exp_neg_smul_eq_one_add_of_mul_self_eq_zero` (`exp ℝ (-(t • M)) = 1 + -(t • M)` for `M * M = 0`, the exponent squaring to `(t·t) • (M·M) = 0`) — the Step-1 `t = 1` handle generalized to all times, the interface QA's symbolic-time evaluation consumes. (2) `Heat_QA.lean` +7: the law witnessed by **two independent routes to one closed-form statement** — `heatKernel_asym_semigroup_raw_QA` (the fixture's closed forms multiplied by hand, `Matrix.mul` on literals, every entry `ring`, independent of the theorem) vs. `heatKernel_asym_semigroup_theorem_QA` (the law composed with one closed form) — plus the every-time closed form `!![1-t, t; -t, 1+t]` for symbolic `t`, the numeric instance at `s = 2, t = 3` (`!![-4, 5; -5, 6]`), the **group property** `heatKernel asymAdj 1 * heatKernel asymAdj (-1) = 1` (forward-then-backward flow is the identity — the consumer's two core interface items working together), and the degenerate `t = 0` identities on K₂ (both orders). (3) Records: the proposal (status header, Step-2 delivery record, open-next-step → Step 3), `proposals/README.md` (High row, progress paragraph, new Delivered row), README (1474; the heat-semigroup sentence and module-table row gaining the semigroup law), radar (axis 5 **held at 3.5** per protocol — the core interface complete but the axis's remaining heat-kernel statements are Steps 3–4, the named re-score trigger; absent clause narrowed accordingly; QA axis synced 1467/40 → 1474/40, held at 4.0), scoreboard (both Direct rows, `lake build` row, lint row, new interpretation bullet; regenerated idempotent at 1474/9/0), the SGT index map (Heat section +2 declaration rows, status line → Steps 0–2), the execution plan (this delivery retired to Delivered; active milestone set to Step 3), and this log. Nothing committed; the worktree's prior-run uncommitted Steps-0+1 delivery preserved untouched.

**Decisive commands and outcomes:** spike first (`wip/heat_step2_spike.lean`: two rounds to green — the fixes were the `Commute` introduction (`constructor` finds no constructor at this pin; `show` of the unfolded equation works), and the fully-ground-`have` + `simp only [heatKernel] at h ⊢` shape for consuming `Matrix.exp_add_of_commute` — the naive `rw [← Matrix.exp_add_of_commute _ _ hcomm]` leaves instance metavariables unassignable and fails keyed matching even against a syntactically identical goal; also `add_smul` not `smul_add` for different scalars on one matrix); `lake env lean Scaffold/Mathlib/GraphTheory/Heat.lean` — zero errors, zero warnings; `lake build Scaffold.Mathlib.GraphTheory.Heat` then `lake env lean Scaffold/QA/SpectralGraph/Heat_QA.lean` — zero errors, zero warnings (QA consumes the built olean, so the module build must precede the QA elaboration); `lake build Scaffold.QA.SpectralGraph.Heat_QA` ✔; `#print axioms` via `wip/heat_step2_axcheck.lean` on all nine new declarations — the standard three only; **full `lake build` ✔ (2252 targets, "Build completed successfully", detached per the recorded procedure)**; `lint_axioms` (9, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1474/9/0**, idempotent — identical file hash on re-run).

**Verification:** every changed module elaborates directly with zero errors/warnings and is linked into the full default build; QA built by explicit target per the recorded scope. The delivery is fully proved hard crust — nothing axiom-backed was added, so nothing is conditional. The QA is load-bearing through route independence: the hand multiplication of the fixture's closed forms computes the same matrix the delivered theorem produces, so any wrong constant in the semigroup chain (a dropped time parameter, a mis-joined exponent) contradicts an independent computation; and the group-property instance composes the two interface theorems, so an error in either surfaces there.

**Remaining risk:** the semigroup law is stated hypothesis-free over all of ℝ² for `(s, t)` — for negative total time it is the growing backward semigroup (the documented Step-1 scope caveat, unchanged); no decay claim is made or implied by this step (that is Step 4's business). The QA fixture is 2×2; the symbolic two-parameter instance mitigates but does not eliminate size-dependence (the theorem itself is size-general, so the risk is to QA coverage, not correctness).

**Next handoff:** **Reversibility Phase B Step 3** — mass conservation `heatKernel A t *ᵥ onesVec = onesVec` through the exponential series at the already-proved `laplacian_ones_in_kernel` (per the proposal's sketch: `onesVec` is a fixed point of every positive power, so the series collapses; alternatively `mulVec`-commutes-with-sums through `Matrix.mulVec_add`/`smul_mulVec_assoc`), with the proposal's named negative-witness follow-on (heat does not cross components on a disconnected fixture) as Step-3 QA material; then Step 4 (eigenmode decay + the connected-graph DC limit) one run later. After Phase B completes: the Medium rows by leverage (approximate spectral projection Step 0; the PF consumers as new-proposal candidates).

## 2026-08-23T05:28:00Z — Fiedler Phase B delivered: the certified conductance cut, first consumer of the Cheeger retirement; the proposal complete

**Run:** `20260823T044903Z-run-1`  
**Session:** `ses_fd30cfa3effedhPliQNP3CHfHI`  
**Status:** completed  
**Milestone:** `proposals/fiedler-partitioning.md` Phase B — **the certified conductance cut, delivered as pure hard crust, zero new axioms (count stays 9)** — the first load-bearing consumer of the previous run's `cheeger_lower_bound`/`cheeger_sweep` retirement. The proposal's recorded operator gate ("run Phase B against the admitted Cheeger hard direction, or defer until it is proved") was **dissolved by the retirement itself**: the deferral option completed, so the run composed proved theorems only, adding no trust surface. The proposal is now COMPLETE (Phase A 2026-08-18, Phase B 2026-08-23).

**Changes:** `GraphTheory.Cheeger` — `cheegerConstant_attained` (the conductance `sInf` realized as a minimum by `Finset.exists_min_image` over the filtered powerset of nonempty proper subsets, no regularity hypothesis: the finiteness step converting Cheeger's inequality-about-an-infimum into a statement about an actual cut). `GraphTheory.Fiedler` (new Phase B section, importing `Cheeger`) — `fiedlerVector_rayleigh_regularNormalizedLaplacian` (`R_{L_sym}(f) = lambda2 / d`) and the headline `cheeger_cut_existence`: on every connected `d`-regular graph, `∃ S` nonempty proper with `conductance S ^ 2 ≤ 2 · lambda2 / d` — the classical Cheeger cut-existence corollary. **Statement-shape deviation recorded before stating** (proposal + module docstring): the sketch's sign-partition bound is not certifiable from the Cheeger inequalities (they bound the conductance *minimum*; no λ₂-only bound on the sign half-space holds in general); the certified object is the minimizer, and the swept-level-set extraction is the named strengthening follow-on. QA `Fiedler_QA` 57 → 65 (1457 total), on the K₂ fixture: `cheegerConstant (K₂) = 1` pinned both directions (every nonempty proper cut on `Fin 2` identified as a singleton by the card count); attainment instantiated; the Rayleigh transfer cross-checked against the independently pinned `lambda2 (K₂) = 2`; the certified cut identified with its bound theorem-sourced and displayed as `1 ≤ 4`; connectivity proved to hold; and the regularity refutation — the `hd`-dropped form at `d = 100` demands `1 ≤ 1/25`, false. Records: the proposal (status header COMPLETE, gate-dissolution record, Phase B delivery record), `proposals/README.md` (Medium row → Delivered; progress paragraph), README (1457, proved list, module table), radar (axis 4 **held at 4.5** per protocol — composition within the counted Cheeger family plus a finiteness attainment lemma, with the absent list updated: the swept-level-set certificate is the new named gap; QA axis synced 1457/39, held), scoreboard (both Direct rows, `lake build`, lint, new interpretation bullet), backlog item 4, SGT index map (+3 rows), Chung source index (corollary row), the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/fiedlerB_spike.lean` green, all `#print axioms` the standard three) then transfer; `lake env lean` on `Cheeger.lean` (only the documented pre-existing `unusedSectionVars` warning) and `Fiedler.lean` (zero errors, zero warnings) and `Fiedler_QA.lean` (zero errors, zero warnings); explicit `lake build` targets ✔; `#print axioms` via `wip/fiedlerB_axcheck{,2}.lean` on the three public and eight QA headline declarations — `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2250 targets, "Build completed successfully")**; `lint_axioms` (9, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated **1457/9/0**, idempotent. Pin-specific notes for the record: `le_div_iff₀` (not `div_le_iff₀`) matches the conclusion-side `/ d`; `inv_mul_eq_div` closes the `d⁻¹ * λ₂ = λ₂ / d` step; `(by omega)` inside `obtain ... := Finset.card_eq_one.1 (by omega)` sees no usable constraints — the card fact must be a tactic-mode `have`; `csInf_le` at this pin takes `BddBelow` (bounded by 0 via `conductance_nonneg`) while `le_csInf` takes nonemptiness; `Fin.sum_univ_two` (not `Finset.`); and `rw [← h]` on a hypothesis containing the value `1` rewrites the numeral too — a calc through `h3.symm` avoids it.

**Verification:** every changed module elaborates directly and is linked into the full default build (QA via explicit targets per the recorded scope). The delivery is fully proved hard crust — nothing axiom-backed was added. It is load-bearing on the retirement end-to-end: a wrong constant anywhere in the retired `cheeger_sweep` chain falsifies `cheeger_cut_existence` outright, the QA Rayleigh-transfer cross-check fails on any defective normalization, and the regularity refutation ties the hypothesis set to a refuted hypothesis-free form at a fixture satisfying every other hypothesis.

**Remaining risk:** the certified cut's *witness* is the conductance minimizer (classical choice over a finite search — existence, not extraction); the stronger algorithmic statement (certifying an explicit Fiedler level set by a sweep argument) is the named follow-on and needs new mathematics (a sweep-extraction lemma with averaging-over-levels strictness care) beyond the Cheeger inequalities. The QA certificate is displayed on `K₂` where the bound is loose (`1 ≤ 4`); tightness fixtures would need larger expanders not in the QA zoo.

**Next handoff:** the remaining Medium rows by leverage — **approximate spectral projection** (Step 0 first; a recorded "not tractable at reasonable cost" is a valid outcome) and the **PF consumers** (irreducible stationary distributions, PageRank) as new-proposal candidates per the one-step discipline; **reversibility Phase B** still needs its recorded operator decision; the **swept-level-set certified cut** is a new named new-proposal candidate.

## 2026-08-23T04:55:00Z — Fiedler Phase B: the certified conductance cut (the first consumer of the Cheeger retirement)

**Run:** `20260823T044903Z-run-1`  
**Session:** `ses_fd30cfa3effedhPliQNP3CHfHI`  
**Status:** superseded  
**Milestone:** The in-progress record for this run's Phase B work — superseded by the completed entry above (same run, same session).

## 2026-08-23T00:29:17Z — Cheeger hard-direction Step 1a delivered: the pure-algebra component, with the survey's constant budget corrected

**Run:** `20260823T001333Z-run-1`  
**Session:** `ses_fd40f0fb2fferjXqdE5FUMcbVE`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Step 1a — the spike-verified pure-algebra component transferred to `Cheeger.lean` at public shape with QA, **zero new axioms** (count stays 10; `#print axioms` on all five new public theorems and eight QA headlines reads only `propext, Classical.choice, Quot.sound`). The delivery's sharpest output is a **constant-budget correction to the survey record**, found by the pre-edit re-derivation before any statement was frozen: the survey's step-5 summation (`E'(u), E'(v) ≤ E'(x)` summed to `2E'(x)`) is loose by exactly the factor `2` the statement's `/2` spends, and its step-6 normalization `R = E'/(d‖x‖²)` omits `laplacian_quadForm`'s `/2` — as recorded the two errors cancel, which is why the twice-hand-checked writeup looked exact.

**Changes:** `GraphTheory.Cheeger` — Component A `core_sum_abs_sq_sub_sq` (verbatim from the spike, `IsSymm` guard), the fused median-part contraction `sq_posPart_sub_add_sq_negPart_sub_le` + `sum_edgeWeight_sq_posPart_add_sq_negPart_le` (the *tight* form: the pointwise pair-summed identity whose cross-edge slack `(u+v)² ≥ u²+v²` pays for carrying both parts, translation invariance absorbed into its RHS — the separate translation-invariance lemma the sketch named is inert and was not added), the regularity bridge `sum_deg_mul_eq_of_regular`, and the normalization `rayleigh_regularNormalizedLaplacian_eq` (`R = E'/(2d‖x‖²)`). `Cheeger_QA.lean` 33 → 59: Component A on `K₂` with all three quantities independently computed (the degree sum through the new bridge, load-bearing) and the strict gap `4 < 8` pinned; the contraction on `C₄` in an equality case (`4 + 4 = 8`) and a strict case (`4 + 4 < 16`); the normalization cross-checked against the independently pinned `λ₂(L_sym) = 2`; and two guard refutations — `IsSymm` at the nonnegative asymmetric `!![0,1/10;1,0]` (`121/100 ≤ 44/100` false, the column-vs-row-sum mismatch at vertex `0`), nonnegativity at the symmetric negative `!![0,-1;-1,0]` (`-1 ≤ -2` false) — each with the surviving structure proved to hold on the fixture. Records: the proposal (Step-1a delivery record, the inline dated correction at the survey's step 6 so 1b/1c cannot follow the loose route, status header, open-next-step → 1b), `proposals/README.md` (Medium row, no-High-rows paragraph), SGT index map (Cheeger section +4 rows + program note), README (1404, the trust-surface sentence), radar (QA axis held 4.0, count synced 1378/39 → 1404/39, hold logged), scoreboard (both Direct rows, `lake build` row, lint date, interpretation bullet), the execution plan, this log.

**Decisive commands and outcomes:** `lake env lean Scaffold/Mathlib/GraphTheory/Cheeger.lean` — zero errors (only the documented pre-existing `unusedSectionVars` warning at `regularNormalizedLaplacian_symmetric`, verified identical in HEAD by a `git stash` round-trip); `lake env lean Scaffold/QA/SpectralGraph/Cheeger_QA.lean` — zero errors, zero warnings; `lake build` on both targets ✔; `#print axioms` via `wip/` check files — the five public and eight QA headline declarations each `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2232 targets, "Build completed successfully")**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated **1404/10/0**, idempotent under re-run. Two pin-specific proof notes for the record: `max_eq_left ha` mis-instantiates when `ha` is the *threshold* comparison rather than `0 ≤ a−m` (side conditions written `(by linarith)` throughout), and `field_simp` mangles the Rayleigh-normalization goal into disjunctive junk — the robust route is `← div_div` + `simp only [div_eq_mul_inv]` + `ring`.

**Verification:** every changed module elaborates directly and is linked into the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional, and `cheeger_lower_bound` remains admitted, visible, and cited. The new theorems are load-bearing on the shelf they consume (`laplacian_quadForm`'s exact `/2`, `quadForm_regularNormalizedLaplacian`, `Finset.sum_mul_sq_le_sq_mul_sq`, `deg`'s row-sum shape): the QA normalization witness would fail if the `/2` were wrong, and the guard refutations tie each statement guard to a refuted hypothesis-free form at a fixture satisfying every other hypothesis.

**Remaining risk:** the corrected constant chain is now machine-checked at both endpoints (Component A, the fused contraction, the normalization) but its *middle* — the per-part combination `φ²d‖y‖² ≤ E'(y)` — lands with Step 1b's co-area core, still hand mathematics; the K₂/C₄ numeric pins above constrain it but do not prove it. Step 1b is rated moderate-high risk (no finite-sum/interval-integral interchange in the pin; ~30 lines of Finset-induction Fubini priced in). Step 1c must consume the corrected shapes per the proposal's inline annotation.

**Next handoff:** **Cheeger Step 1b** — the co-area core (`½ ∑ A |y i² − y j²| ≥ φ d ∑ y i²` for minority-level-set `y ≥ 0`), its own dedicated run per the Davis–Kahan precedent; then Step 1c (median + assembly) retires `cheeger_lower_bound` at the unchanged statement. Approximate spectral projection still needs its Step 0; the PF consumers (irreducible stationary distributions, PageRank) are new-proposal candidates. Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-23T00:13:33Z — Cheeger hard-direction Step 1a: the pure-algebra component (transfer run)

**Run:** `20260823T001333Z-run-1`  
**Session:** `ses_fd40f0fb2fferjXqdE5FUMcbVE`  
**Status:** superseded  
**Milestone:** The in-progress record for this run's Step-1a work — superseded by the completed entry above (same run, same session).

## 2026-08-22T23:05:59Z — Cheeger hard-direction Step 0 surveyed: decisive positive-with-large-cost, the gate opened

**Run:** `20260822T224324Z-run-1`  
**Session:** `ses_fd45b5b09ffeCDr541zsEJofYM`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md` open next step — the mandated per-axiom Step 0 tractability survey of `cheeger_lower_bound` (`Cheeger.lean:88`, `φ²/2 ≤ λ₂(L_sym)`, d-regular), the last remaining perturbation axiom after the Weyl (2026-08-20) and Davis–Kahan (2026-08-21) retirements. Top Medium row with no High rows and the plan's recorded next handoff naming it first. Delivered as survey + spike only, no Cheeger source edits, per the Davis–Kahan one-step precedent; the proposal's own gate now authorizes Step 1 as dedicated runs.

**Changes:** the survey record in the proposal (status header; the full record replacing the "unsurveyed" placeholder; per-axiom item 3; open-next-step → Step 1a) — the route with tight constants, the half-volume obstruction recorded with its counterexample shape so no future run re-derives the median trick, the pin facts with their traps, the 1a/1b/1c decomposition with cost estimates (550–900 lines over 2–3 runs); `proposals/README.md` (Medium row, no-High-rows paragraph); the execution plan; this log. The green spike `wip/cheeger_spike.lean` (git-ignored): the Cauchy–Schwarz core at final shape, the shifted-positive-part contraction, the variational-assembly skeleton in hypothesis form, and the scalar FTC primitive — every `#print axioms` clean.

**Decisive commands and outcomes:** `lake env lean wip/cheeger_spike.lean` — zero errors, `CheegerSpike.core_sum_abs_sq_sub_sq`, `abs_posPart_sub`, `assembly_skeleton` each depend on `propext, Classical.choice, Quot.sound` only; `lake build Scaffold.Mathlib.GraphTheory.Cheeger` ✔ (untouched module; no `Scaffold/**` file changed this run, so the spike's direct elaboration is the decisive check and the umbrella build certifies nothing new); `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated with zero diff (idempotent, 1378/10/0). Survey findings: the sInf reduction through the proved `secondEval_variational` dissolves the eigenvector/spectral side entirely; the two-median-part norm split `‖u‖²+‖v‖² = ‖x‖² + nm²` makes the factor-2 budget exactly the statement's `/2` — constants reconstructed and hand-checked twice, with the K₂-equality QA pin prescribed before Step 1's statements freeze.

**Verification:** the survey's positive verdict rests on elaboration-verified primitives (the spike), shelf lemmas read at their exact statements (`secondEval_variational`, `regularNormalizedLaplacian_psd`, `regularNormalizedLaplacian_mulVec_onesVec`, `conductance_ge_cheegerConstant`, `vol_eq_of_regular`, `laplacian_quadForm`, `quadForm_regularNormalizedLaplacian` — all already proved), and hand mathematics that remains unproved until Step 1 lands. Nothing here claims the axiom discharged; `cheeger_lower_bound` is still admitted, visible, and cited.

**Remaining risk:** the hand-verified constant chain is not machine-checked — the recorded mitigation is the numeric QA witness (K₂ equality, strict C₄/P₃) before Step 1's statements freeze, this repository having been burned by a false Cheeger shape before. The co-area core (Step 1b) is rated moderate-high risk; no finite-sum/interval-integral interchange exists at this pin (priced in as ~30 lines of Finset induction).

**Next handoff:** **Cheeger Step 1a** — transfer the spike-verified pure-algebra component into `Cheeger.lean` at its public shape (with the `IsSymm` statement guard) plus QA; then 1b (the crux) and 1c as dedicated runs. Approximate spectral projection still needs its Step 0; the PF consumers (irreducible stationary distributions, PageRank) are unblocked as new-proposal candidates. Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T22:53:19Z — Cheeger hard-direction Step 0: the survey that gates the last perturbation axiom

**Run:** `20260822T224324Z-run-1`  
**Session:** `pending`  
**Status:** superseded  
**Milestone:** The in-progress record for this run's survey work — superseded by the completed entry above (same run, same session once established).

## 2026-08-22T21:42:53Z — Perron–Frobenius admitted: the directed axis' second spectral toolkit

**Run:** `20260822T211552Z-run-1`  
**Session:** `ses_fd4b02ef7ffeucven25tSq36wL`  
**Status:** completed  
**Milestone:** `proposals/admit-perron-frobenius.md` — the scoped admission delivered: `Matrix.IsIrreducible` (combinatorial, global, Fintype-free) plus the admitted Horn–Johnson 8.4.4 axiom at the irreducible-case qualification level, QA with the mandated imprimitive-cycle negative witness, and the index/coverage/count records. One new explicit cited axiom (9 → 10) — the first admission since the 2026-08-19 scope decision, and deliberately so: the directed-operators program's PSD refutation showed the undirected positivity layer does not transfer, and this is the nonnegative-matrix theory that replaces the symmetric `evals` toolkit on the directed axis. No consumer work (stationary distributions, PageRank stay named follow-ons).

**Changes:** the new `Scaffold/Mathlib/LinearAlgebra/PerronFrobenius.lean` (namespace `Scaffold.LinearAlgebra`) and `Scaffold/QA/LinearAlgebra/PerronFrobenius_QA.lean` (36 declarations, the first LinearAlgebra-domain QA file); umbrella import + doc entry in `Scaffold.lean`; Horn–Johnson source-index row (Theorem 8.4.4) + scope note; the new `index/map/linear_algebra.md` + map README row; coverage map's named-absent Perron–Frobenius row updated to "Absent (upstream) / Admitted (Scaffold)"; backlog item 8 third update; README (10 axioms, 1378 QA, trust surface, module table); radar QA-axis sync (1342/38 → 1378/39, held 4.0); scoreboard (counts, both Direct rows, `lake build` row, lint row, interpretation bullet); the proposal's status header + full delivery record; `proposals/README.md` (row retired, paragraph rewritten, Delivered row); the execution plan. Statement-shape decisions recorded before stating: the `hex` degeneracy guard (exactly the missing strength at `card V ≤ 1`, derivable from irreducibility at `n ≥ 2`), `rootMultiplicity`-over-ℝ simplicity, the strong uniqueness clause with the explicit `μ = r` conjunct, spectral radius encoded through complex charpoly roots (no matrix spectral radius in the pin), and no strict-dominance clause.

**Decisive commands and outcomes:** `lake env lean` on the module and QA — zero errors, zero warnings each; explicit `lake build` targets for both ✔; `#print axioms` — the five axiom-consuming QA theorems (`perron_frobenius_P_QA`, `perron_frobenius_D_QA`, the only-eigenvalue cross-check, both domination instantiations) list exactly `Scaffold.LinearAlgebra.perron_frobenius` + `propext, Classical.choice, Quot.sound`, while the eleven hand theorems (including the centerpiece `strict_dominance_refuted_QA` and both hand-only only-eigenvalue theorems) read only the standard three; **full `lake build` ✔ (2232 targets, "Build completed successfully", zero errors, detached)**; `lint_axioms`, `check_citations`, `check_markdown_links` pass; scoreboard regenerated **1378/10/0**, idempotent under re-run. QA highlights: on the positive witness `!![1,2;1,0]` the Perron root is *derived to be exactly 2* from the axiom's eigen-equation on its unknown witness, with simplicity and complex-domination clauses pinned against hand factorizations; on the asymmetric directed 2-cycle `!![0,4;1,0]` the strengthening's `|μ| < r` is refuted at `|−2| = 2 = r` while the admitted `|−2| ≤ r` holds with equality — the fence the proposal's Calibration section demanded. Pin-specific techniques recorded in the proposal for future fixtures: plain `open Polynomial` (not `open scoped`) activates `X`/`C`; eta-expanded `fin_cases` indices need explicit `show`; C-numerals must be normalized to numerals before `ring` (this pin's `C_mul` points opposite to modern Mathlib, `C_eq_natCast` misses OfNat literals); scalar `2 • x` needs `(2:ℝ)` annotation; `charpoly_map`'s RingHom argument does not match `coe_algebraMap`'s coerced form — compute mapped charpolys directly.

**Verification:** the axiom is admitted, not proved — nothing here is described as foundationally established, and the QA's role is interface pinning plus the falsification fence, not validation of the axiom's truth. The axiom-transparency split is machine-checked: every axiom-consuming QA theorem shows the dependency, every hand theorem does not.

**Remaining risk:** low. The statement is guarded exactly where this repository has been burned before (no strict dominance; `hex` for the degenerate sizes), and the QA refutes the canonical misstatement. The named residuals are the follow-on consumers (irreducible stationary distributions, PageRank), each requiring its own proposal, and the standing note that an upstream Mathlib Perron–Frobenius would trigger the replacement lifecycle (a global `Matrix.IsIrreducible` from Scaffold would then be renamed).

**Next handoff:** the Medium rows by leverage — the **Cheeger hard-direction Step 0 survey** (known-hard; the last perturbation-axiom remainder) and **approximate spectral projection** (Step 0 first). The PF consumers are unblocked as new-proposal candidates. Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T21:15:52Z — Perron–Frobenius admission: the directed axis' second toolkit

**Run:** `20260822T211552Z-run-1`  
**Session:** `ses_fd4b02ef7ffeucven25tSq36wL`  
**Status:** in-progress  
**Milestone:** `proposals/admit-perron-frobenius.md` scoped admission — irreducibility via directed reachability, the Horn & Johnson 8.4.4 axiom at the irreducible-case qualification level (no strict-dominance clause), QA with the mandated imprimitive-cycle negative witness, and the index/coverage/axiom-count records. Top-ranked Medium row, Active table holding no High rows, and the recorded next handoff of the directed-operators completion (whose PSD refutation names this as what the directed spectral theory needs). One new explicit cited axiom (9 → 10); no consumer work.

**Changes:** intent recorded in the execution plan (pre-edit survey + statement-shape decisions: the `hex` degeneracy guard, the strong uniqueness clause, `rootMultiplicity`-over-ℝ simplicity, global `Matrix.IsIrreducible`, rational QA fixtures). Lean work pending below (`Scaffold/Mathlib/LinearAlgebra/PerronFrobenius.lean` + `Scaffold/QA/LinearAlgebra/PerronFrobenius_QA.lean`).

**Verification:** pending — module + QA elaboration, `#print axioms` on the axiom's QA consumers (must list the new axiom), explicit builds, full `lake build`, lint/citation/link checks, scoreboard regeneration at the milestone boundary.

**Remaining risk:** low — the statement is scoped by a proposal whose Calibration section was written against exactly the misstatement this repository has made before; the QA plan's negative witness is designed to fence it.

**Next handoff:** delivery record, records sync, terminal entry.

## 2026-08-22T20:10:13Z — Directed operators Step 2 delivered: the symmetrized normalized Laplacian; the proposal's Lean content complete

**Run:** `20260822T194020Z-run-1`  
**Session:** `ses_fd5032572ffe4qTynTCxjNs6hi`  
**Status:** completed  
**Milestone:** `proposals/directed-graph-operators.md` Step 2 (the directed normalized Laplacian `I − ½(SAS + SAᵀS)` at the Step-0-recorded out-degree-symmetrized convention) plus the Step-3 agreement brick (folded in per the Step-0 record's "one line from decision (b)" scoping) — the proposal's Lean content is complete. Top-ranked Medium row, Active table holding no High rows. Zero new axioms (count stays 9).

**Changes:** `GraphTheory.Directed` extended with `directedNormalizedLaplacian` (the shelf's `degreeInvSqrt`/`degreeSqrt` reused verbatim — `deg` *is* the out-degree), the entry form, **hypothesis-free symmetry** (the two defining halves are transposes of each other; the directed axis' one symmetric operator), the acceptance-bar agreement `= normalizedLaplacian` under `A.IsSymm`, and the square-root-free conjugate `√D L_dir √D = degreeMatrix A − ½(A + Aᵀ)`. QA `Directed_QA.lean` 41 → 88: all nine `L_dir dirA` entries computed from the entry form (exactly `[[1,−1,−1/2],[−1,1,0],[−1/2,0,1]]`), the symmetry theorem instantiated on asymmetric input, the conjugate's two sides independently hand-checked at `−2`, the symmetric-edge agreement pinned raw both sides, and the two new negative witnesses — undirected reuse (`L_dir ≠ normalizedLaplacian` on directed input, `−1 ≠ −3/2`) and the **PSD refutation**: on `dirB = !![0,4;1,0]` (nonnegative, positive out-degrees, symmetric `L_dir`) `quadForm L_dir 1 = −1/2 < 0` — symmetric does not mean PSD; the positivity layer of the undirected toolkit provably does not transfer, and the directed spectral theory needs Perron–Frobenius (the proposal's Calibration boundary, now witnessed numerically). Records: the proposal (status COMPLETE, Step-2 delivery record), `proposals/README.md` (row, progress paragraph, Delivered table), backlog item 8, the SGT index map, README (1342, proved list, module table), radar (QA count 1295/38 → 1342/38, held 4.0), scoreboard (both Direct rows, `lake build` row, interpretation bullet), the execution plan, and this log. Nothing committed.

**Decisive commands and outcomes:** `lake env lean` on the module and QA — zero errors, zero warnings each (after one rebuild of the module olean; QA elaboration had initially consumed the stale olean); explicit `lake build` targets for both modules ✔; `#print axioms` on the five new public and nineteen headline QA theorems — `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2230 targets, "Build completed successfully", zero errors, detached)**; `lint_axioms` (9), `check_citations`, `check_markdown_links` pass; scoreboard regenerated **1342/9/0**, idempotent under re-run. Pin-specific QA techniques recorded in the proposal for future fixtures: `Real.sqrt_eq_iff_eq_sq` for numerals (`norm_num` alone does not evaluate `Real.sqrt 4`); the entry form's conditional discharges by `if_pos rfl`/`if_neg (by decide : ¬(i = j))` — `Matrix.one_apply_ne (by decide)` elaborates with metavariables and fails; ground `Fin`-index `if`s inside entry computations need full `simp` (`norm_num` leaves residue); `rw` rewrites all occurrences of an instantiated pattern at once, so duplicate lemma mentions in a `rw` list fail.

**Verification:** fully proved hard crust — nothing axiom-backed was added, no `sorry` anywhere; the QA is load-bearing in both directions (the hypothesis-free symmetry instantiated on asymmetric input would fail to elaborate against a definition that secretly needed `IsSymm`; the conjugate's two sides were computed independently and must match; the PSD refutation exercises the shelf's `quadForm` interface against the new operator).

**Remaining risk:** low. The named residual is unchanged and now witnessed: the convention forfeits Chung's directed-Cheeger content, and the PSD refutation shows the undirected positivity layer does not transfer — any directed spectral statement must wait for Perron–Frobenius. The Mathlib coverage map needed no correction.

**Next handoff:** the Medium rows by leverage — **the Perron–Frobenius admission** (`admit-perron-frobenius.md` — decoupled by the Step-0 record; its imprimitive-cycle negative witness is the centerpiece its QA plan mandates; the natural continuation of the directed axis), the **Cheeger hard-direction Step 0 survey** (known-hard), and **approximate spectral projection** (Step 0 first). Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T19:40:20Z — Directed operators Step 2: the symmetrized normalized Laplacian, closing the proposal

**Run:** `20260822T194020Z-run-1`  
**Session:** `ses_fd5032572ffe4qTynTCxjNs6hi`  
**Status:** in-progress  
**Milestone:** `proposals/directed-graph-operators.md` Step 2 (the directed normalized Laplacian `I − ½(SAS + SAᵀS)` at the Step-0-recorded out-degree-symmetrized convention) plus the Step-3 agreement brick (recorded by Step 0 as one line from decision (b)) — on delivery the proposal's Lean content is complete. Top-ranked Medium row, Active table holding no High rows. Zero new axioms.

**Changes:** intent recorded in the execution plan; Lean work pending below (`GraphTheory.Directed` + `Directed_QA.lean`).

**Verification:** pending — module + QA elaboration, `#print axioms`, explicit builds, full `lake build`, lint/citation/link checks, scoreboard regeneration at the milestone boundary.

**Remaining risk:** low — the convention is decided, the consumed shelf lemmas (`degreeSqrt`/`degreeInvSqrt` cancellation pair, `normalizedLaplacian`) were read at their exact signatures during the Step-0 survey and again this run.

**Next handoff:** delivery record, records sync, terminal entry.

## 2026-08-22T18:17:01Z — Directed operators Step 0 + Step 1: convention decisions and the degree layer

**Run:** `20260822T181701Z-run-1`  
**Session:** `ses_fd5521f76ffeRFs1v4dJctUmET`  
**Status:** in-progress  
**Milestone:** `proposals/directed-graph-operators.md` Step 0 (the mandated survey and convention decisions, coordinated with `proposals/admit-perron-frobenius.md` per the scoped-together instruction) + Step 1 (the degree layer `outDeg`/`inDeg`, directed handshaking, and the asymmetric-input certification of the pre-existing walk operators) — the top-ranked Medium program with the Active table holding no High rows. Zero new axioms.

**Changes:** Step 0 record written into the proposal (decisions (a)/(b)/(c) plus the discovery that `deg`/`walkTransitionMatrix`/`walkLaplacian` are already the out-degree walk operators, hypothesis-free); intent recorded in the execution plan. Lean: new `Scaffold/Mathlib/GraphTheory/Directed.lean` and `Scaffold/QA/SpectralGraph/Directed_QA.lean` pending below.

**Verification:** pending — module + QA elaboration, `#print axioms`, oleans, umbrella import, full `lake build`, lint/citation/link checks, scoreboard regeneration at the milestone boundary.

**Remaining risk:** low — every consumed shelf lemma was read at its exact signature during the Step-0 survey; the convention decision (b) decouples rather than couples, so no build-order hazard.

**Next handoff:** delivery record, records sync, terminal entry.

## 2026-08-22T18:39:13Z — Directed operators Step 0 + Step 1 delivered: the directed axis is open, decoupled from Perron–Frobenius

**Run:** `20260822T181701Z-run-1`  
**Session:** `ses_fd5521f76ffeRFs1v4dJctUmET`  
**Status:** completed  
**Milestone:** `proposals/directed-graph-operators.md` Steps 0+1 — the three mandated Step-0 convention decisions recorded before any statement, then Step 1 (the run's one Lean step): the directed degree layer in the new `Scaffold.Mathlib.GraphTheory.Directed` plus the asymmetric-input QA certification of the pre-existing walk operators. Zero new axioms (count stays 9). The Step-0 convention decision **decouples this program from `admit-perron-frobenius.md`** (out-degree-symmetrized normalized Laplacian, not Chung's Perron-vector form, so no admitted axiom becomes a prerequisite of a definition).

**Changes:** new `Scaffold/Mathlib/GraphTheory/Directed.lean` (seven public declarations: `outDeg`, `inDeg`, the two `rfl` identifications with the shelf's `deg` and its transpose, the symmetric-cone agreements, directed handshaking `∑ outDeg = ∑ inDeg`) and new QA `Scaffold/QA/SpectralGraph/Directed_QA.lean` (41 declarations: the genuinely-directed fixture `!![0,3,1;1,0,0;1,0,0]` with a nine-entry `rfl` table, both degree functions pinned raw `outDeg = (4,1,1)` / `inDeg = (2,3,1)`, handshaking `6 = 6` by both routes, the symmetric-edge agreement witness, the load-bearing instantiation of `walkTransitionMatrix_row_sum` and `walkLaplacian_mulVec_one_eq_zero` **on asymmetric input** with a raw cross-check, and the two negative witnesses `outDeg 0 ≠ inDeg 0` and `¬ (walkTransitionMatrix dirA).IsSymm`). Umbrella import added. Records: the proposal (status header, Step-0 record, Step-1 delivery record with the pin-specific QA technique), `proposals/README.md` (Medium row + progress paragraph), backlog item 8, the SGT index map (Directed section), README (1295, proved list, module table), radar (QA axis held at 4.0, count synced 1254/37 → 1295/38), scoreboard (both Direct rows, the `lake build` row, a new interpretation bullet), the execution plan, and this log. Nothing committed; prior-run uncommitted deliveries preserved untouched.

**Decisive commands and outcomes:** `lake env lean` on the module and on the QA file — zero errors, zero warnings each; explicit `lake build` targets for both modules ✔; `#print axioms` on the seven public and twelve headline QA theorems — `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2230 targets, "Build completed successfully", zero errors, detached log + poll)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated **1295/9/0** (`Directed_QA` a new file row at 41). One QA-engineering detour recorded for future fixture work on this pin: `simp only` unfolds of *new* degree defs against matrix literals leave `vecHead/vecTail` residue (while the same list through the shelf's `deg` behaves), and `show` cannot kernel-reduce `Finset.sum` — the deterministic route is a `rfl` entry table plus `Fin.sum_univ_three` splitting with table rewrites, now recorded in the proposal.

**Verification:** the delivery is fully proved hard crust — nothing axiom-backed was added, no `sorry` anywhere, and the QA is load-bearing in both directions: the asymmetric-input instantiations would fail if the pre-existing walk operators had secretly depended on symmetry (that dependence-absence is the certification's whole point), and both negative witnesses refute the hypothesis-free forms (`outDeg = inDeg`; walk-matrix symmetry) that undirected habits would suggest.

**Remaining risk:** low. The named residual is Step 2's to carry: the chosen convention forfeits Chung's directed-Cheeger content (recorded honestly in the Step-0 record); any future directed-isoperimetric work must adopt Chung's convention there or prove its own bounds. The Mathlib coverage map needed no correction — the Step-0 re-survey confirmed its rows.

**Next handoff:** the Medium rows by leverage — **directed operators Step 2** (the normalized Laplacian at the recorded convention; unblocked), **the Perron–Frobenius admission** (decoupled; its imprimitive-cycle negative witness is the centerpiece its QA plan mandates), the **Cheeger hard-direction Step 0 survey** (known-hard), and **approximate spectral projection** (Step 0 first). Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T17:12:56Z — Subgaussian tail bound retired by repair: the Step 0 spike proved the old axiom materially false

**Run:** `20260822T164518Z-run-1`  
**Session:** `ses_fd5aa3374ffeR6W0kz6WrMW4ho`  
**Status:** completed  
**Milestone:** `proposals/prove-subgaussian-tail-bound.md` — the mandated Step 0 spike plus the repair-and-retire in one run: `subgaussian_tail_bound` is a proved theorem, **explicit axioms 10 → 9** (the first measure-theoretic axiom retirement), delivered as the Woodbury-precedent emergency correctness repair after the spike proved the old statement materially false.

**Changes:** `Subgaussian.lean` — `axiom subgaussian_tail_bound` became `theorem` at the same name and conclusion (including the `2K²` constant) with honest hypotheses `(hK : 0 < K)`, MGF integrability at `K`, and the MGF bound at `K`; the `subgaussianNorm` docstring's junk-behavior paragraph corrected with a dated note (unbounded tails make the defining set *full*, not empty — `integral_undef` junk-zero integrals); `hoeffding_lemma`'s stale QA-note (referencing the nonexistent `hoeffding_lemma_zero_QA`) fixed. `Scalar_QA.lean` 6 → 17 declarations: the zero fixture through the new hypotheses, the proposal-mandated nonzero instance (constant-1, `K = 2`, `t = 1` on `dirac 0`; moment `exp (1/4) ≤ 2` via the pinned `Real.log_two_gt_d9`; event and bound sides pinned raw), and the four-piece refutation family (`3 • δ₀` fixture; the empty-set junk mechanism exhibited as a theorem; the old hypotheses proved satisfiable-vacuously; the old conclusion `3 ≤ 2` refuted). Records: both index files, scoreboard (counts, Direct rows, `lake build` row, lint row, interpretation bullet), radar (axiom-minimization synced to 9, trend extended, hold logged; QA count 1254/37, held), README, architecture §12, the proposal (full delivery record with the pin-specific API notes and the adjacent-hazard residual), the execution plan, and this log. The operator-side worktree change (the `proposals/README.md` Low row) preserved untouched; nothing committed.

**Decisive commands and outcomes:** the Step 0 spike (`wip/subgaussian_spike.lean`, git-ignored) elaborated green with `#print axioms subgaussian_tail_bound` reading only `propext, Classical.choice, Quot.sound` — confirming both falsity mechanisms against the pin (`Real.sInf_empty` at Archimedean.lean:190; `integral_undef` at Bochner.lean:743) before the module was touched; `lake env lean` on the module (only the pre-existing `unused variable K` warning, verified identical in HEAD via a HEAD elaboration) and on the QA file (zero errors; nine remaining warnings = the pre-existing set, verified by a stashed-HEAD elaboration); `#print axioms` on the retired theorem and all twelve touched/new QA theorems — three standard axioms only; `lake build` on both targets ✔; **full `lake build` ✔ (2229 targets, "Build completed successfully", detached log + poll)**; `lint_axioms` (**9**), `check_citations`, `check_markdown_links` pass; scoreboard regenerated **1254/9/0**, idempotent.

**Verification:** the delivery is fully proved hard crust at the repaired statement; the QA is load-bearing in both directions — the nonzero instance pins the bound's two sides raw (a wrong `2K²` constant or hypothesis orientation would break it), and the refutation family falsifies the old shape with its hypotheses proved satisfied (the Woodbury/old-Cheeger falsification pattern). One operational lesson re-confirmed: QA files elaborate against built oleans, so the module must be rebuilt before its QA consumer sees a changed interface (the QA's first failure was the stale axiom-shaped olean, not the code).

**Remaining risk:** low for what is delivered. The named residual — the same junk-integral mechanism likely touching `hoeffding_inequality`/`bernstein_inequality`'s mean hypotheses on infinite measures and the `MatrixMDS` set-integrals — is recorded in the proposal and architecture §12 for their own Step 0s. `hoeffding_lemma` remains an admitted axiom (statement unchanged); the repaired theorem no longer consumes it, so its only remaining consumer is the `subgaussian_norm_zero_QA` cross-coherence check.

**Next handoff:** the Medium rows by leverage — **Perron–Frobenius + directed operators** (scoped together, Step 0 first per the convention-choice gate), the **Cheeger hard-direction Step 0 survey** (known-hard working assumption), and **approximate spectral projection** (Step 0 first). Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T16:45:18Z — Subgaussian tail bound: Step 0 spike (and contingent repair-and-retire)

**Run:** `20260822T164518Z-run-1`  
**Session:** `ses_fd5aa3374ffeR6W0kz6WrMW4ho`  
**Status:** superseded (by the completed delivery entry above)  
**Milestone:** `proposals/prove-subgaussian-tail-bound.md` — the proposal's mandated Step 0 (Lean spike against the pinned Mathlib: `Real.sInf_empty`, `integral_undef`, `mul_meas_ge_le_integral_of_nonneg` at exact signatures; the monotone-in-`K` moment transfer; the Markov assembly), with Step 1 (retire `subgaussian_tail_bound`, axioms 10 → 9) to follow in this run if the spike confirms tractability. Pre-edit reading surfaced two junk hazards in the axiom's current shape (empty-`sInf` vacuity on measures of mass > 2; junk-zero Bochner integrals making the defining set full for heavy tails) — if the spike confirms either, the run executes the Woodbury-precedent repair-and-retire with the decision recorded before stating.

**Changes:** intent recorded in the execution plan (hazards, contingent route, next action). No Lean or record edits yet beyond that.

**Verification:** pending — spike elaboration, then module + QA elaboration, `#print axioms`, full `lake build`, lint/citation/link checks, scoreboard regeneration at the milestone boundary.

**Remaining risk:** the falsity hazards, if confirmed, convert this from a proof task to a correctness repair; the repaired statement's shape (moment+integrability hypotheses at `K`, conclusion unchanged) is already drafted in the execution plan.

**Next handoff:** spike results and the go/no-go on the repair route.

## 2026-08-22T14:07:07Z — Relative entropy and Shannon entropy delivered: the finite-distribution program complete

**Run:** `20260822T134800Z-run-1`  
**Session:** `ses_fd64842bdffeLZUnmAoGML8Wh3`  
**Status:** completed  
**Milestone:** `proposals/finite-relative-entropy.md` — both steps in one run per the proposal's own operating instruction: Gibbs' inequality in both directions (`klDiv_nonneg`, `klDiv_eq_zero_iff`), the uniform bridge, and the entropy maximum with its equality case (`shannonEntropy_le_log_card`, `shannonEntropy_eq_log_card_iff`), all pure hard crust in the new `Scaffold.Mathlib.InformationTheory.Entropy` — zero new axioms (count stays 10). Closes the entropy half of backlog item 6 (reversibility half landed earlier the same day).

**Changes:** new public module `Scaffold/Mathlib/InformationTheory/Entropy.lean` (namespace `Scaffold.InformationTheory`; nine public theorems around the scalar `klTerm` carrying the proposal-mandated visible `a = 0 ↦ 0` junk convention) and new QA `Scaffold/QA/InformationTheory/Entropy_QA.lean` (31 declarations, the first InformationTheory-domain QA file). **Route decision recorded before stating:** the mandated Jensen survey found the whole shelf present (`ConcaveOn.le_map_sum`, `StrictConcaveOn.lt_map_sum`/`eq_of_map_sum_eq`/`map_sum_eq_iff'`; `strictConcaveOn_log_Ioi` — stop-and-record clause not triggered), but the delivered proof is the term-wise information inequality (`Real.one_sub_inv_le_log_of_pos` + `Real.log_lt_sub_one_of_pos` at the reciprocal) — the same Cover–Thomas 2.6.3 route with no Finset-`smul` plumbing and no support filtering; the junk case is discharged inside the per-term bound, where its strictness is *stronger* (gap `= b > 0`), so the equality case needs no `∑_{support} q` argument. QA: the biased coin's divergence and entropy hand-computed to closed log-forms (`¼·log(27/16)`, `¼·log(256/27)`) with strict positivity pinned; the equality case exercised in both directions against raw computations; **the uniform bridge numerically cross-checked** at the fair coin (`¼·log(27/16) = log 2 − ¼·log(256/27)`, both sides independently pinned); the maximum attained at uniform two ways and **strictly missed** by the non-uniform `Fin 4` distribution — strictness only through the equality-case iff, the proposal-prescribed load-bearing use; the delta distribution's entropy exactly `0` exhibiting the junk convention. Records: proposal (status header + full delivery record with pin-specific API notes), `proposals/README.md` (Medium row → Delivered; progress paragraph), new `index/map/information_theory.md` + map README row, scoreboard (1243/10/0 regenerated; both Direct rows prepended; a new interpretation bullet), radar (QA axis held at 4.0, count synced 1243/37, sync logged), README (counts, module table, proved list, and the stale conditional-on-Davis–Kahan persistence note corrected), backlog item 6, the umbrella import + docstring, the execution plan, this log.

**Decisive commands and outcomes:** `lake env lean` on `Entropy.lean` and `Entropy_QA.lean` — zero errors, zero warnings each (final re-elaboration after the reachability probe); explicit target builds of both modules ✔; `#print axioms` on the nine public and thirteen headline QA theorems — `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2229 targets, "Build completed successfully", zero errors)**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated idempotently (**1243 QA declarations / 10 explicit axioms / 0 sorries**). **Build-reachability fact recorded (content-change probe: appending a comment to a QA file leaves `lake build` with nothing to do):** the default target is the `Scaffold.lean` umbrella closure — it certifies every public module including the new one but does not itself compile the QA tree; QA modules are certified by direct elaboration and explicit targets, and the scoreboard's `lake build` row now states this scope precisely.

**Verification:** the delivery is fully proved hard crust — nothing axiom-backed was added, no `sorry` anywhere. The QA is load-bearing in both directions: every headline quantity is pinned through the theorems *and* by raw log algebra independent of them (a wrong bridge constant or sign would break the numerical cross-check), and the strictness witness is derivable only through the equality-case iff — exactly the strict-route use the proposal's QA plan demands.

**Remaining risk:** low — the area is self-contained and every consumed Mathlib lemma was verified at its exact signature before stating. Pin-specific API notes for future QA are recorded in the proposal: `Real.log_pow`/`Real.log_inv` take explicit arguments (no hypotheses), `Finset.sum_one` is absent at that name (use `Finset.sum_const` + `Finset.card_univ` + `Nat.smul_one_eq_cast`), coefficient-atom identities need `ring_nf` rather than `norm_num`, and `Finset.sum_sub_distrib` is oriented `∑ (f − g) = ∑ f − ∑ g`.

**Next handoff:** the Medium rows by leverage — **the subgaussian tail bound** (the 2026-08-22 operator-directed addition — run its Step 0 first), **Perron–Frobenius + directed operators** (Step 0 first per the convention-choice gate), the **Cheeger hard-direction Step 0 survey** (known-hard), and **approximate spectral projection** (Step 0 first). Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T13:48:00Z — Relative entropy and Shannon entropy: the finite-distribution program

**Run:** `20260822T134800Z-run-1`  
**Session:** `ses_fd64842bdffeLZUnmAoGML8Wh3`  
**Status:** superseded (by the completed delivery entry above)  
**Milestone:** `proposals/finite-relative-entropy.md` — Step 1 (`klDiv`, Gibbs' inequality `klDiv_nonneg`, the equality case `klDiv_eq_zero_iff`) and Step 2 (`shannonEntropy`, the maximum `shannonEntropy_le_log_card`, its equality case), both in one run per the proposal's own operating instruction. Closes the entropy half of backlog item 6; zero new axioms (pure hard crust from proved Mathlib scalar lemmas).

**Changes:** intent, pre-edit surveys, route decision, statement shapes, and QA plan recorded in the execution plan before any edit. Surveys done: the pinned Jensen shelf is fully present (`ConcaveOn.le_map_sum`, `StrictConcaveOn.lt_map_sum`/`eq_of_map_sum_eq`/`map_sum_eq_iff'` at Jensen.lean:71/145/169/233; `strictConcaveOn_log_Ioi` at SpecificFunctions/Basic.lean:63) — the proposal's stop-and-record clause is not triggered — but the delivered route is the term-wise information inequality (`Real.one_sub_inv_le_log_of_pos`, `Real.log_lt_sub_one_of_pos`), the same Cover–Thomas 2.6.3 proof without the Finset-`smul`/support-filter plumbing. Placement decided: new `Scaffold/Mathlib/InformationTheory/Entropy.lean` + `Scaffold/QA/InformationTheory/Entropy_QA.lean`, namespace `Scaffold.InformationTheory`.

**Verification:** pending — module + QA elaboration, `#print axioms`, full build, lint/citation/link checks, scoreboard regeneration at the milestone boundary.

**Remaining risk:** low — every consumed Mathlib lemma verified present at its exact signature before stating; the QA strictness witness depends on the equality-case iff exactly as designed (that is its point).

**Next handoff:** Lean implementation, QA, verification, records.

## 2026-08-22T12:43:09Z — Mixing-time Step 3, component 2 delivered: the χ² assembly; the mixing-time program is complete

**Run:** `20260822T115239Z-run-1`  
**Session:** `ses_fd6b75575ffejcx9dFsZqxgnLo`  
**Status:** completed  
**Milestone:** `proposals/mixing-time-bound.md` Step 3, component 2 of 2 — the χ² assembly and the program's closing statement `chiSquareDistance_le_of_connected`: `χ²(t, x) ≤ r ^ (2t) · ((π x)⁻¹ − 1)` on connected symmetric-nonnegative positive-degree networks under the rate hypothesis. Pure hard crust, zero new axioms; the proposal's radar axis-5 re-score trigger fired (3.0 → 3.5).

**Changes:** three public modules extended — `GraphTheory.Normalized` (+3: the constant fix `walkTransitionMatrix_mulVec_one`, the `√D`/`1/√D`-action entry lemmas), `GraphTheory.Mixing` (+4: the centered evolution `walkDensity_sub_one`, the mass-conservation pairing, the connectivity mode derivation — the kernel of `L_sym` transferred through the proved congruence `√D L_sym √D = L` to the shelf's combinatorial kernel theorem, then collapsed by mass conservation, the mode hypothesis *derived* rather than assumed — and the headline bound); `Mixing_QA.lean` 67 → 117 declarations: the final statement instantiated on both fixtures (K₃ with the bound attained *exactly* at `t = 1, 2`; P₃ with the rate derived basis-independently from two sum-of-squares certificates pinning every eigenvalue into `[0, 2]`), cross-checks of the centered evolution and the connectivity-derived mode fact against the component-1 hand computations, and the two negative witnesses — connectivity load-bearing on the triangle⊕self-loop `Fin 4` fixture (spectrum `{0, 0, 3/2, 3/2}` derived basis-independently so the rate hypothesis provably holds at `r = 1/2` — the loop's `μ = 0` mode excluded from the rate hypothesis by design, exactly the hole connectivity plugs — while `χ²(3) = 3/8 > 3/64` refutes the conclusion), and the rate load-bearing at `r = 1/4` on K₃ (hypothesis unsatisfiable by the trace, conclusion refuted). Records: proposal (status header COMPLETE, the full component-2 delivery record including two pin-specific API discoveries, open-next-step → none with the three optional items named), `proposals/README.md` (Medium row retired to the Delivered table, progress paragraph rewritten, and the duplicate reversibility row — 2026-08-19 drift — removed), scoreboard (1212/10/0, both Direct rows prepended, the `lake build` row extended, a new interpretation bullet), radar (axis 5 **re-scored 3.0 → 3.5** with the full re-score log entry, the weakest-axes paragraph rewritten, QA count synced 1212/36), README (1212, the proved list gains the closing mixing bound, module table, coverage snapshot axis 5 → 3.5), SGT index map (Mixing program-complete header + 4 rows + entry-lemma note), backlog item 2 (program complete), the execution plan, this log. The worktree's unrelated operator-side changes (the untracked `proposals/prove-subgaussian-tail-bound.md` + its README row) and the uncommitted-but-delivered Step-2/Phase A/component-1 work remain preserved untouched.

**Decisive commands and outcomes:** `lake env lean` on `Normalized.lean` (only the documented pre-existing `congr 1` note), `Mixing.lean`, and `Mixing_QA.lean` — the latter two zero errors, zero warnings; `#print axioms` on the seven new public and twelve headline QA theorems — `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2228 targets, "Build completed successfully", detached log + poll, zero errors)**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1212 QA declarations / 10 explicit axioms / 0 sorries**; `Mixing_QA` a 67 → 117 file row).

**Verification:** the delivery is fully proved hard crust — nothing axiom-backed was added, no `sorry` anywhere. The QA is load-bearing in both directions: the K₃ positive witness pins the final bound's both sides by raw literal arithmetic with the bound attained exactly at two time steps (the engine's Parseval exactness carrying through the χ² identification unchanged), and the disconnected negative witness is the strongest kind this program supports — every hypothesis of the final theorem except connectivity proved to hold on the fixture (including the rate, via a basis-independent spectrum derivation), with the conclusion refuted, demonstrating that the value-based rate exclusion cannot detect the second kernel mode and connectivity genuinely must be assumed.

**Remaining risk:** low — the program is closed and every interface it built is QA'd. Two pin-specific API hazards are recorded in the proposal for future QA work: this snapshot's `Finset.mul_sum`/`Finset.sum_mul` take arguments `(s) (f) (a)` with `mul_sum : a * ∑ f = ∑ (a * f)` (different argument order and orientation than the standard statement; explicit-argument `have`s are the robust route), and the matrix-literal far-corner entry (`!![…; 0,0,0,2]`-shaped) normalizes through the notation's empty default row and defeats both `rfl` inside `fin_cases` and `norm_num` — the robust routes are an `fin_cases + rfl`-proved entry table consumed as a simp lemma, or a scalar-multiple route avoiding entrywise evaluation.

**Next handoff:** the Medium rows by leverage — **Relative Entropy** (Gibbs' inequality and the entropy maximum from Mathlib's proved strict-concavity machinery), **the subgaussian tail bound** (Step 0 first), **Perron–Frobenius + directed operators** (Step 0 first per the convention-choice gate), the **Cheeger hard-direction Step 0 survey** (known-hard), and **approximate spectral projection** (Step 0 first). Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T11:52:39Z — Mixing-time Step 3, component 2: the χ² assembly

**Run:** `20260822T115239Z-run-1`  
**Session:** `ses_fd6b75575ffejcx9dFsZqxgnLo`  
**Status:** superseded (by the completed delivery entry above)  
**Milestone:** `proposals/mixing-time-bound.md` at its recorded open next step — Step 3, component 2 of 2, the χ² assembly and the program's closing statement `χ²(t, x) ≤ (λ*)^{2t} · ((π x)⁻¹ − 1)`: the centered density evolution, the connectivity kernel characterization of `L_sym` (the shelf's `laplacian_kernel_eq_span_onesVec` transferred through the proved congruence), and the gluing into the delivered contraction. Pure gluing plus one real-content piece; zero new axioms; this is the proposal's radar axis-5 re-score trigger.

**Changes:** intent, route, statement-shape decisions, and QA plan recorded in the execution plan before any edit. Pre-edit interface reading done: the contraction's `hmode`/`hrate` shapes, `chiSquareDistance_eq_sum_smul`, `chiSquareDistance_zero`, `exists_const_of_laplacian_mulVec_eq_zero`, and `degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt` all confirmed on the shelf at the exact needed shapes; the QA connectivity technique (`SimpleGraph.connected_iff_exists_forall_reachable` + explicit walks) confirmed from `Connectivity_QA.lean`.

**Verification:** pending — module + QA elaboration, `#print axioms`, full build, lint/citation/link checks, scoreboard regeneration at the milestone boundary.

**Remaining risk:** the P₃ rate derivation needs two SOS certificates with `√2` atoms (the `path_one_add_one_QA` normalization-bridge technique may be needed); the disconnected-fixture spectrum derivation needs the "orthogonal to `e₃`" step through symmetry (`L_sym *ᵥ e₃ = 0` on that fixture) — both planned in the plan's QA section.

**Next handoff:** Lean implementation in `Normalized.lean` (+3 entry lemmas) and `Mixing.lean` (+4 theorems), then QA, verification, records.

## 2026-08-22T10:42:00Z — Mixing-time Step 3, component 1 delivered: the geometric decay engine

**Run:** `20260822T095344Z-run-1`  
**Session:** `ses_fd71c43f4ffeFVBbJiOzNG01En`  
**Status:** completed  
**Milestone:** `proposals/mixing-time-bound.md` Step 3, component 1 of 2 — the geometric decay engine (the authorized sub-decomposition of the program's hardest step): conjugated walk powers through the proved similarity, eigencoordinate evolution via a new generic center lemma, the Parseval-exact decay identity, and the hypothesis-shaped ℓ²(π) contraction under value-based mode exclusion. Pure hard crust, zero new axioms; component 2 (the χ² assembly) is the recorded open next step, all gluing on this delivery.

**Changes:** three public modules extended — `GraphTheory.Spectral` (+1 generic: `eigvecOf_dotProduct_one_sub_mulVec`, the `1 − M` eigenaction), `GraphTheory.Normalized` (+2: the commutation form `√D · P = (1 − L_sym) · √D` and the conjugated-power transfer `√D *ᵥ (Pᵗ *ᵥ g) = (1 − L_sym)ᵗ *ᵥ (√D *ᵥ g)`), `GraphTheory.Mixing` (+5: eigencoordinate evolution, the Parseval-exact identity, the norm-form contraction, the π-norm bridge, and the π-form headline contraction); `Mixing_QA.lean` 33 → 67 declarations (the triangle K₃ with basis-independent eigen-facts and *exact* decay `2 → 1/2 → 1/8` at rate `1/2`; the P₃ λ* = 1 oscillation cross-check tying the engine to the pinned `χ²(2) = 1`; the mode-hypothesis negative witness). Records: proposal (status header, delivery record, open-next-step → numbered component-2 list), `proposals/README.md` (Medium row, progress paragraph, Delivered row), scoreboard (1162/10/0, narrative rows, interpretation bullet), radar (axis-5 hold entry + QA count sync 1162/36, held), README (counts, proved list, module table), SGT index map (+5 rows and supporting-additions note), backlog item 2, the execution plan, this log. The worktree's unrelated operator-side changes (the untracked `proposals/prove-subgaussian-tail-bound.md` + its README row) and the uncommitted-but-delivered Step-2/Phase A work are preserved untouched.

**Decisive commands and outcomes:** `lake env lean` on `Spectral.lean`, `Normalized.lean`, `Mixing.lean`, `Mixing_QA.lean` — zero errors each; `Mixing`/`Mixing_QA` zero warnings, `Spectral`/`Normalized` only their documented pre-existing diagnostics; `#print axioms` on all eight new public theorems and thirteen headline QA theorems — `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2227 targets, "Build completed successfully", detached log, zero errors)**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1162 QA declarations / 10 explicit axioms / 0 sorries**; `Mixing_QA` a 33 → 67 file row).

**Verification:** the delivery is fully proved hard crust — nothing axiom-backed was added, no `sorry` anywhere. The QA is load-bearing in both directions: the K₃ positive witness pins the contraction's both sides by raw literal arithmetic with the bound *attained exactly* at two time steps (the decay is genuinely geometric at rate `1/4` per step-pair), and the negative witness refutes the hypothesis-free form while separately proving the mode hypothesis unsatisfiable at the kernel index. The eigen-facts the instances consume are derived without controlling Mathlib's classical eigenbasis (unit norm + entrywise eigen equation + linear arithmetic; the kernel index's existence from trace vs `9/2`).

**Remaining risk:** low for what is delivered — every interface component 2 consumes is now on the shelf and QA'd. The component-2 risks are named in the proposal's open-next-step list: the kernel characterization `ker L_sym = span{√D·1}` under connectivity (transferring the shelf's `laplacian_kernel_eq_span_onesVec` through the similarity) is the one piece with real content left. One pin-specific API discovery recorded in the plan for future QA: this snapshot's sum-subtraction lemma is `Finset.sum_sub_distrib`, and `linear_combination` takes the exact coefficient expression (sign mattered).

**Next handoff:** mixing-time **Step 3, component 2** — the χ² assembly (centered evolution `h_t − 1 = Pᵗ(h₀ − 1)`; connectivity kernel-orthogonality; the final `χ²(t, x) ≤ (λ*)²ᵗ · ((π x)⁻¹ − 1)` instantiated on the existing K₃/P₃ fixtures) — per the proposal's numbered gluing list. Or the other Medium rows by leverage (Relative Entropy; the subgaussian tail bound Step 0; Perron–Frobenius + directed operators Step 0; the Cheeger hard-direction survey; approximate spectral projection Step 0).

## 2026-08-22T10:02:19Z — Mixing-time Step 3, component 1: the geometric decay engine

**Run:** `20260822T095344Z-run-1`  
**Session:** `unavailable` (to be established before the terminal entry)  
**Status:** in-progress  
**Milestone:** `proposals/mixing-time-bound.md` at its recorded open next step — Step 3, executed as the sub-decomposition the proposal itself licenses ("likely the hardest single step... may need its own sub-decomposition across runs"). Component 1 of 2: the decay engine — conjugated matrix powers through the proved similarity, eigencomponent evolution, the Parseval-exact decay identity, and the hypothesis-shaped ℓ²(π) contraction. Zero new axioms; hard crust load-bearing on the Step-1 transfer, the shelf's eigenbasis layer, and Parseval. Component 2 (the χ² assembly with the connectivity kernel characterization) stays a later dedicated run.

**Changes:** intent and route recorded in the execution plan (statement-shape decisions made before stating: value-based mode exclusion over index-based — it keeps the theorem true unconditionally on degenerate graphs; hypothesis-shaped rate `r`; no decorative sign hypothesis; π-form headline). Pre-edit API survey done: `Matrix.dotProduct_sub`, `pow_le_pow_left`, `sq_le_sq'`, `Matrix.mulVec_mulVec`, `pow_succ'` all present on the pin; the generic `1 − M` eigenaction lemma is absent from the shelf (to be added to `Spectral.lean`).

**Verification:** pending — module + QA elaboration, `#print axioms`, full build, lint/citation/link checks, scoreboard regeneration at the milestone boundary.

**Remaining risk:** the K₃ QA mode/rate derivations go through Mathlib's classically-chosen eigenbasis; the plan avoids naming basis vectors (only unit-norm, the eigen equation, and entrywise linarith), the DavisKahan_QA technique.

**Next handoff:** Lean implementation, then verification and record updates.

## 2026-08-21T22:51:25Z — Davis–Kahan Step 1, component 1 delivered: the equal-rank projector identity

**Run:** `unavailable` (interactive completion; the autonomous continuation run that did the Lean work was `20260821T175629Z-run-1`)  
**Session:** `unavailable`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Davis–Kahan Step 1, component 1 of 2 — the equal-rank projector identity `‖P − Q‖ = ‖(I−Q)P‖` for real symmetric idempotent matrices of equal rank, in the new public module `Analysis/OperatorTheory/Perturbation/ProjectionGap.lean`, zero new axioms, with QA. This closes out the milestone the two prior 2026-08-21 runs (`20260821T133507Z-run-1`, `20260821T175629Z-run-1`) left in progress: both hit their step limit mid-verification — the first left the module drafted but unelaborated, the second elaborated it clean (~1570 lines, all five sections) and wrote QA down to a single remaining `rewrite` failure before running out of steps.

**Changes:** (1) Fixed the one remaining QA error in `ProjectionGap_QA.lean` (`max_form_unequal_rank_QA`, line 585): the rewrite list's final item, `diff_one_opNorm_QA`, was redundant — by that point the goal had already collapsed to the numeric tautology `0 ⊔ 1 = 0 ⊔ 1` via the preceding three rewrites, so the pattern it hunted for no longer existed; dropped it from the list. Also removed a dead `all_goals try norm_num` (line 534, flagged by the linter as never executed). (2) Wired the umbrella: `Scaffold.lean` now imports `Analysis.OperatorTheory.Perturbation.ProjectionGap`. (3) Records: `docs/EXECUTION_PLAN.md` milestone closed (component 1 DELIVERED, component 2 opened as the next milestone), `proposals/discharge-perturbation-axioms.md`'s "Open next step" updated, `proposals/README.md`'s Medium row and progress paragraph updated, `index/map/perturbation.md` gained a new "Equal-Rank Projector Identity" section (4 declarations), `README.md`'s module table and QA count updated, scoreboard regenerated. The SGT Radar was deliberately left unchanged — `davis_kahan_sin_theta` itself is still an admitted axiom (only one of its two required components is delivered), and this repo's convention re-scores an axis only when a capability actually lands, not on partial progress toward it.

**Decisive commands and outcomes:** `lake env lean` on both changed files — zero errors, zero warnings on each; `#print axioms` on every public `ProjectionGap` theorem (from the prior run's record, re-confirmed by the clean compile): `propext, Classical.choice, Quot.sound` only; full `lake build` — **2186/2187 targets, "Build completed successfully"**, only the documented pre-existing `Derived/ProjectorDrift.lean` `hγ` warning; `lint_axioms` (**11**, unchanged), `check_citations`, `check_markdown_links` all pass; scoreboard regeneration — QA declarations **998 → 1035** (37 new: the `ProjectionGap_QA` file), axioms unchanged at 11. The `scaffold-pursue` LaunchAgent was deliberately unloaded (`launchctl bootout`) before this work began, to avoid a collision with the hourly autonomous trigger while editing shared state files, and is to be re-bootstrapped after this entry is committed.

**Verification:** every changed module elaborates directly with zero errors/warnings and is linked into the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added. `#print axioms` confirms no hidden trust boundary. The QA fixture (30°-rotation realized as the 3-4-5 Pythagorean triple, `sin θ = 3/5`) pins the headline identity by two independent routes plus a rank-mismatch guard refuting the hypothesis-free form.

**Remaining risk:** low for what's delivered — the one-line fix was a mechanical redundant-rewrite removal, not a proof-shape change, and the surrounding ~1570/600 lines were already elaborated clean by the prior run. The larger open risk is unchanged from the Step-0 survey: component 2 (the Duhamel/FTC assembly) is the harder, less-predictable half, not yet started.

**Next handoff:** Davis–Kahan Step 1, **component 2** — the Duhamel/FTC assembly consuming this identity plus the spike-verified semigroup primitives (`wip/dk_spike.lean`) — as its own dedicated run, per the proposal's one-step-per-run discipline. Do not bundle it with component 1's cleanup in the same run in the future; today's two runs each hit their step limit on a single component alone.

## 2026-08-21T13:35:07Z — Davis–Kahan Step 1, component 1: the equal-rank projector identity (hard crust)

**Run:** `20260821T133507Z-run-1`  
**Session:** `ses_fdb8aca45ffe3YCyELhEpdARZv`  
**Status:** in-progress  
**Milestone:** `proposals/discharge-perturbation-axioms.md` at its recorded open next step — Davis–Kahan Step 1, executed as the authorized two-component split's first half: the equal-rank projector identity `‖P − Q‖ = ‖(I−Q)P‖` for real symmetric idempotent matrices of equal rank, as its own hard-crust delivery (new public module, zero new axioms, QA). Shrinks the path to the largest remaining axiom retirement; the Duhamel/FTC assembly (component 2) stays a later dedicated run.

**Changes:** intent recorded in the execution plan. Pre-edit shelf survey (read-only): this Mathlib pin has **no** AB/BA characteristic-polynomial lemma (Charpoly files read; `Analysis/Matrix.lean` is sup/Frobenius norms only) — but `Analysis/CStarAlgebra/Matrix.lean` has the whole `Matrix.L2OpNorm` C*-layer (`l2_opNorm_conjTranspose_mul_self`, `l2_opNorm_mul`, `l2_opNorm_mulVec`), and Scaffold's own Courant–Fischer counting lemmas plus Parseval/eigenaction identities (`dotProduct_eigvecOf`, `dotProduct_eigvecOf_mulVec`, `eigvecOf_expansion_apply`, `finrank_span_eigvecOf_finset`, `card_filter_eigvalOf_lt_evals_le`) route the entire proof without charpoly machinery. Route recorded in the plan before any module edit.

## 2026-08-21T07:43:00Z — Davis–Kahan Step 0 survey delivered; citation mislocation repaired; route spike-verified

**Run:** `20260821T072042Z-run-1`  
**Session:** `ses_fdcda3324ffeLkwyWOg7bVGO07`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md` at its recorded open next step — the Davis–Kahan Step 0 survey (top Medium item; no High rows remain). Delivered as a decisive **positive-with-large-cost** record: the YWS paper read in full, the proof route named and its primitives spike-verified proved, the 600–1000-line Step-1 estimate recorded, and the citation mislocation the survey surfaced repaired in four files. No axiom statements changed; explicit axioms stay 11; no `sorry` anywhere.

**Changes:** (1) **Citation repair**: the axiom's provenance note paired "YWS Theorem 2" with "constant 1" — a pairing absent from the paper, whose actual Theorem 2 is population-gap/Frobenius/constant-2 (Weyl + Wielandt–Hoffman + Kronecker Sylvester); the repo's mixed-gap operator-norm constant-1 statement is the paper's **Theorem 1** (classical DK restated, operator-norm variant noted there) at the bottom cluster — single-pair δ equivalence by sortedness re-verified, constant-1 tightness re-verified numerically (2×2 rotation family: sinθ ≈ 0.0985 vs bound ≈ 0.0990, asymptotically attained). Corrected with dated notes: `DavisKahan.lean` docstring, `index/sources/davis_kahan_1970.md`, `index/map/perturbation.md`, `docs/2_ARCHITECTURE.md` §12. (2) **Route record** in the proposal: the entrywise eigenbasis-coordinate identity caps at Frobenius shape (√(k+1) constant — exactly YWS Thm 2's `d^{1/2}` numerator) so it cannot discharge the exact statement; constant-1 operator-norm needs the Duhamel/exponential integral `(I−Q)P = ∫₀^∞ e^{-tÃ}(I−Q)E e^{tA}P dt` (the mixed gap *is* side separation ⇒ `e^{-tδ}` decay; semigroups at vector level, no `Matrix.exp`) plus the equal-rank projector identity `‖P−Q‖ = ‖(I−Q)P‖` (principal angles; required since the reverse cross-gap degrades through Weyl to `δ − 2‖E‖`; the tempting `(P−Q)²` decomposition refuted by a worked 2×2 example). (3) **Spike** `wip/dk_spike.lean` (git-ignored): five primitives PROVED, all `#print axioms`-clean — `heatApply` (damped-eigenbasis semigroup), its adjoint/expansion workhorse, Parseval damping, eigenaction, `HasDerivAt` in `t` (this pin needs explicit `Analysis.Calculus.Deriv.Add` + `Analysis.SpecialFunctions.ExpDeriv` imports — not transitive through `GraphTheory.Spectral`), and the reducing commutation `spectralProjector M hM c * M = M * spectralProjector M hM c` (+`mulVec` form; `Matrix.IsSymm.apply` for entry symmetry). (4) Proposal Status header, per-axiom item 2 closed, Open-next-step → authorized Step 1 as a dedicated run; `proposals/README.md` Medium row + progress paragraph (top next candidate now the Step 1 retirement itself); scoreboard regenerated (idempotent, 998/11/0).

**Decisive commands and outcomes:** `lake env lean` on the changed module and both consumers — `DavisKahan.lean` zero errors/warnings (docstring-only change), `DavisKahan_QA.lean` clean, `Derived/ProjectorDrift.lean` only the documented pre-existing `hγ` warning; the spike elaborates end-to-end with all three `#print axioms` reads = `propext, Classical.choice, Quot.sound`; `lint_axioms` (11), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (998/11/0). Environment healthy at run start (5387 Mathlib oleans at the corrected path; no fetch needed).

**Verification:** the survey gate is satisfied per the proposal's own contingency pattern — findings recorded in the proposal *before* any Step-1 edit, and Step 1 was not started. Nothing axiom-backed was added or altered; the delivery is a survey record plus proved spike primitives (scratch) plus a citation-fidelity repair with no statement changes.

**Remaining risk:** the Step-1 estimate is an estimate — the equal-rank projector identity is the least-predictable component (moderate-large; principal-angles route), and the FTC assembly carries analysis-API friction (scalar `intervalIntegral`, improper limit). The spike covered the semigroup/algebra layer only, not the integration. The citation repair rests on the paper as published at arXiv:1405.0680v1 (Annals of Statistics 43(3):2028–2061); the Davis–Kahan 1970 primary-source §3 locator remains section-level as before.

**Next handoff:** Davis–Kahan **Step 1** — authorized, dedicated run, optionally split (equal-rank lemma first as its own hard-crust delivery, then the Duhamel assembly); or the other Medium rows by leverage (mixing-time Step 1; Reversibility Phase A; Relative Entropy; Perron–Frobenius + directed operators Step 0; Cheeger hard-direction survey under its known-hard assumption; approximate spectral projection Step 0; Fiedler Phase B awaits an operator decision).

## 2026-08-21T07:22:00Z — Davis–Kahan Step 0 survey (sin-Θ tractability)

**Run:** `20260821T072042Z-run-1`  
**Session:** `ses_fdcda3324ffeLkwyWOg7bVGO07`  
**Status:** in-progress  
**Milestone:** `proposals/discharge-perturbation-axioms.md` at its recorded open next step — the Davis–Kahan Step 0 survey (no High rows remain in the Active table; this is the top Medium item by the recorded leverage ranking, shrinking the mushy center). Scope: what a proof at the axiom's exact statement needs vs. the shelf, a scratch spike of the decisive primitive, findings recorded in the proposal before any Step-1 edit, plus the citation repair the survey itself surfaced.

**Changes:** intent recorded in the execution plan. Survey evidence gathered: the YWS paper (arXiv:1405.0680) fetched and read in full — finding: the axiom's provenance note mislocates the statement (the paper's Theorem 2 is population-gap/Frobenius/constant-2; the repo's mixed-gap/operator-norm/constant-1 statement is the paper's Theorem 1 with its noted operator-norm variant, at the bottom cluster — the single-pair-δ equivalence by sortedness still holds). Route analysis: the entrywise eigenbasis-coordinate identity closes only at Frobenius shape (√(k+1) constant); constant-1 operator-norm needs the Duhamel/exponential-integral representation plus the equal-rank projector identity. Spike to follow in `wip/dk_spike.lean` (ignored); then the proposal's Step-0 record, the docstring/index citation fix, and verification.

## 2026-08-21T04:59:08Z — Spectral band projectors, Step 4 delivered (the Hilbert-projection specialization); program complete

**Run:** `20260821T040302Z-run-1`  
**Session:** `ses_fdd8410deffe43MaMPuIN14Gyc`  
**Status:** completed  
**Milestone:** The Active priority table's only High row (`proposals/spectral-band-projectors.md`) at its recorded open next step — Step 4, the program's last — delivered as pure hard crust, **zero new axioms** (count stays 11; `#print axioms` on all three new public theorems reads only `propext, Classical.choice, Quot.sound`). The band-projector program is complete: Steps 1–3 on 2026-08-20, Step 4 on 2026-08-21, one step per run throughout.

**Changes:** `GraphTheory.Band` gained the Step-4 section (with the two Mathlib imports `Analysis.InnerProductSpace.{Projection,PiL2}`): `bandProjector_residual_dotProduct_eq_zero` (the residual-orthogonality engine `(x − B*ᵥx) ⬝ᵥ (B*ᵥz) = 0` — load-bearing on exactly the two Step-1 facts, symmetry and idempotence), `bandProjector_toEuclidean_apply_eq_orthogonalProjection` (the identification: Mathlib's `orthogonalProjection` at `LinearMap.range (toEuclideanLin B)` *is* the band-filtered signal — the SGT center's first consumption of `Analysis/InnerProductSpace/Projection.lean`), and `norm_sub_bandProjector_apply_le` (the closest-point property over the band's fixed space, from `orthogonalProjection_minimal` + the conditionally-complete `ciInf_le`). Statement shapes recorded before stating: at `EuclideanSpace ℝ V` (the bare `V → ℝ` default norm is the sup norm), fixed-point hypothesis form over the membership existential, range form over an eigenspace-span form (coincide for idempotent self-adjoint projectors; span-form agreement is the proposal's named residual). QA `SpectralGraph/Band_QA.lean` +25 (109 in file, 998 total): the identification pinned to the packaged band image; minimality **attained** (distance exactly `4`), **strict over the zero signal** (`4 ≤ 5`, the 3-4-5 triangle), **generic over the whole range line** (`4 ≤ √((3−t)²+16)`) with `band_diag13_hilb_min_line_raw` reproducing the identical inequality from bare square-positivity — an independent hand-check; the high band instantiated; the residual engine by theorem and raw routes; and the **fixed-space guard** refuting the hypothesis-free form at the unfiltered signal (`0 < 4`, not band-fixed). Records: module/QA/umbrella docstrings, scoreboard (998/11/0, both Direct rows + the `lake build` row prepended/extended with the Step-4 slice, new interpretation bullet, provenance run events), radar (**axis 2 re-scored 4.0 → 4.5** — the capability dimension the Step-1/Step-3 records explicitly reserved as the trigger; QA 998/34, QA axis **held at 4.0**; both logged), README (998/11; proved list extended; coverage snapshot's spectral-linear-algebra row synced 3.5 → 4.5, stale since the Tikhonov re-score), SGT index map (Band section header + 3 rows), proposal (program-complete status header, Step-4 delivery record, open-next-step → none), `proposals/README.md` (High row removed, Delivered row added, progress paragraph rewritten — **no High rows remain**), execution plan. The operator's concurrent plist path edit is preserved untouched.

**Decisive commands and outcomes:** `lake env lean` on `Band` and `Band_QA` — zero errors, zero warnings (public module after two argument-shape fixes: this snapshot's `LinearMap.mem_range` has no explicit arguments and `orthogonalProjection_minimal` takes its submodule implicitly; `iInf_le` does not apply over ℝ — `ciInf_le` with a `BddBelow` witness of `0` does; QA after three proof-shape fixes: a simp-closes-goal `norm_num` trap, a symbolic dot-product `ring` residue, and a `rw`-all-occurrences scope trap replaced by `calc`); `#print axioms` on 3 public + 9 headline QA theorems — only `propext, Classical.choice, Quot.sound`; oleans built during iteration (`lake build Scaffold.Mathlib.GraphTheory.Band` / `…Band_QA`); **all thirty-four QA modules batch-elaborated — BATCH-DONE total=34 fail=0** (one mid-batch restart at the 10-minute tool timeout — no state damage, `lake env lean` does not replay traces); **full `lake build` ✔ (2186 targets, "Build completed successfully")**, detached log + poll per the recorded procedure; `lint_axioms` (11), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (**998/11/0**). Environment healthy at run start (correct-path olean check: 5387 present, no fetch).

**Verification:** every changed module elaborated directly with zero errors/warnings and linked in the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional. The identification and minimality are load-bearing on the Step-1 algebra (the residual engine consumes symmetry and idempotence exactly), and the fixed-space hypothesis is refutable-on-omission (the QA guard). The proposal's mandatory signature survey found the entire needed shelf in the pinned Mathlib; the stop-and-record clause was not triggered.

**Remaining risk:** low — Step 4 is one orthogonality computation plus Mathlib's projection API over the already-QA'd band machinery, with an independent raw-arithmetic cross-check and the hypothesis guard. The `a > b` junk region remains documented-not-guarded (no theorem claims anything there). The span-form agreement (range vs. in-band-eigenspace span) is the proposal's named residual, not delivered.

**Next handoff:** with no High rows remaining, the next run selects among the Medium rows by leverage (as ranked in `proposals/README.md`): the Davis–Kahan Step 0 survey (`discharge-perturbation-axioms.md` — shrinking the mushy center, tractability genuinely unknown), mixing-time Step 1, Reversibility Phase A, Relative Entropy, Perron–Frobenius + directed operators (Step 0 first), or approximate spectral projection (Step 0 first). Fiedler Phase B still needs an operator decision.

## 2026-08-21T04:08:11Z — Spectral band projectors, Step 4 (the Hilbert-projection specialization)

**Run:** `20260821T040302Z-run-1`  
**Session:** `ses_fdd8410deffe43MaMPuIN14Gyc`  
**Status:** in-progress  
**Milestone:** The Active priority table's only High row (`proposals/spectral-band-projectors.md`) at its recorded open next step — Step 4, the Hilbert-projection specialization, the program's last step: the band projector's output is the closest point in its range to the input, by instantiating Mathlib's Hilbert projection theorem at the band's range. Pure hard crust, zero new axioms (the proposal forbids them and mandates a recorded obstruction if the shelf lacks needed machinery).

**Changes:** intent + route recorded in the execution plan. The proposal's mandatory pre-step survey ran against the pinned snapshot and found everything needed: `eq_orthogonalProjection_of_mem_of_inner_eq_zero` (the identification lemma), `orthogonalProjection_minimal` + `iInf_le` (minimality), `HasOrthogonalProjection.ofCompleteSpace` (instance), and the `inner_piLp_equiv_symm` (`rfl`) + `toEuclideanCLM_piLp_equiv_symm`/`toLin'_apply` transport spine — the resolvent Step-0 precedent. Route: the residual-orthogonality engine `(x − B*ᵥx) ⬝ᵥ (B*ᵥz) = 0` (symmetry + idempotence, both Step-1 facts) feeding the identification at `K = range (toEuclideanCLM B)`; statements at `EuclideanSpace ℝ V` (the bare `V → ℝ` norm instance is the sup norm — deliberately not used). Planned QA: minimality attained with equality in-band and strict on the 3-4-5 signal (`4 < 5`), identification instantiated, fixed-space guard refuting the hypothesis-free form. Environment healthy at run start (5387 Mathlib oleans; the pruned-oleans state did not recur). Lean work to follow in `GraphTheory/Band.lean` and `QA/SpectralGraph/Band_QA.lean`.

## 2026-08-21T00:51:34Z — Spectral band projectors, Step 3 delivered (completeness under a partition)

**Run:** `20260820T210049Z-run-1`  
**Session:** `ses_fdf0afe0cffeISDycxodu6Lgfc`  
**Status:** completed  
**Milestone:** The Active priority table's only remaining High row (`proposals/spectral-band-projectors.md`) at its recorded open next step — Step 3, completeness under a partition — delivered as pure hard crust, **zero new axioms** (count stays 11; `#print axioms` on all four new public theorems reads only `propext, Classical.choice, Quot.sound`). The proposal's one-step-per-run rule was honored: Step 4 (the Hilbert projection specialization) untouched.

**Changes:** `GraphTheory.Band` gained the Step-3 section: `sum_range_bandProjector_eq_sub` (the **unconditional telescoping law** `∑_{k<n} B(t_k, t_{k+1}) = P_{t_n} − P_{t_0}` for *any* threshold sequence, ordered or not — range-succ induction with an `abel` residue, load-bearing on the band definition's exact difference shape), `sum_range_bandProjector_eq_one` (**completeness**: a family starting strictly below every eigenvalue and ending at-or-above them all resolves the identity — exactly the two endpoint covering hypotheses, both load-bearing), `bandProjector_mul_bandProjector_eq_zero_of_monotone` (distinct members of a **monotone** family compose to zero — the recorded statement-shape decision: monotonicity is deliberately *not* a hypothesis of the sum identity since telescoping does not consume it; it is exactly what this theorem consumes via Step 2's disjointness, making the family a *partition* rather than a sequence), and `sum_range_bandProjector_mulVec_eq_self` (the consumer's form `∑ B_k *ᵥ x = x`, through the inlined `mulVec` analog of `Matrix.sum_mul`). QA `SpectralGraph/Band_QA.lean` +41 (84 in file, 973 total): the covering two-band family summed to the identity through the theorem *and* from independently pinned band values; a three-band partition with an **empty middle band** and its top threshold exactly touching the top eigenvalue (the closed right endpoint); the **two endpoint guards** — a family starting above the lowest mode and a family truncated below the highest each provably fails to sum to the identity, each violated covering hypothesis separately refuted (the design note's "silently ignores modes" failure mode, witnessed in both directions); the **non-monotone telescoping witness** (family `4, 0, 4`: junk band `−1` cancelling covering band `1`, both sides independently `0`); and the vector decomposition on a concrete signal by both routes. Records: module/QA/umbrella docstrings, scoreboard (973/11/0, both Direct rows prepended with the Step-3 slice, the `lake build` row extended, the Step-3 interpretation bullet, the provenance note amended with a **wrong-path olean-presence-check correction** — the layout has no `lean/` level, so the old check pattern returns 0 with the full set present; the correct check is a `find`-based count at the package build root), radar (axis 2 completeness layer, **held at 4.0** per protocol — same-family completion, with Step 4 named the natural re-score trigger as it consumes Mathlib's inner-product-space machinery; QA 973/34, **held at 4.0**; both holds logged), README (973; proved list gains partition completeness), SGT index map (Band section +4 rows, Steps 1–3), proposal (Step-3 delivery record + status header + open-next-step → Step 4), `proposals/README.md` (High row note, Delivered row, progress paragraph — Step 4 now the top of the Active table), execution plan.

**Decisive commands and outcomes:** `lake env lean` on `Band` and `Band_QA` — zero errors, zero warnings (public module first pass; QA after two proof-shape fixes: this snapshot's `Finset.sum_range_succ` appends the new term on the *right* (`f 0 + f 1 + …`, with no `Finset.sum_range_two`/`Nat.cast_mono` available), and the `rw`-closes-`3 ≤ 3`-by-itself linter trap behind one warning); `#print axioms` on 4 public + 13 QA headline theorems — only `propext, Classical.choice, Quot.sound`; oleans produced by the recorded fast `lean -o` path; **all thirty-four QA modules batch-elaborated — BATCH-DONE total=34 fail=0**; **full `lake build` ✔ (2186 targets, "Build completed successfully")**, executed detached (log + poll) after the run's first invocation was killed at its 300 s tool timeout during Mathlib trace replay — the olean set verified intact afterward by the corrected presence check, so no re-fetch was needed (one redundant idempotent re-fetch had already run); `lint_axioms` (11), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (973/11/0).

**Verification:** every changed module elaborated directly with zero errors/warnings and linked in the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional. The completeness statement is load-bearing on the band definition's exact difference shape (the non-monotone QA witness would fail against a sign-flipped or transposed definition), and both covering hypotheses are refutable-on-omission (the two endpoint guards).

**Remaining risk:** low — Step 3 is one induction plus endpoint algebra over the already-QA'd projector machinery, with dual-route summation checks and both endpoint guards. The `a > b` junk region remains documented-not-guarded (no theorem claims anything there). Step 4 of the proposal (the Hilbert projection specialization — survey `Analysis/InnerProductSpace/Projection.lean` signatures first) remains open.

**Next handoff:** the same proposal's Step 4 — the Hilbert-projection-theorem specialization (the program's last step; the `toEuclideanCLM` transport spine from the resolvent Step-0 record is the precedent for the `EuclideanSpace`-to-matrix transport); or the queued Medium rows (Fiedler Phase B — needs an operator decision; mixing-time Step 1; Reversibility A and B; Relative Entropy; Perron–Frobenius + directed operators; discharge-perturbation — the Davis–Kahan Step 0 survey; approximate spectral projection).

## 2026-08-20T21:00:49Z — Spectral band projectors, Step 3 (completeness under a partition)

**Run:** `20260820T210049Z-run-1`  
**Session:** `ses_fdf0afe0cffeISDycxodu6Lgfc`  
**Status:** in-progress  
**Milestone:** The Active priority table's only remaining High row (`proposals/spectral-band-projectors.md`) at its recorded open next step — Step 3, completeness under a partition: for a threshold family covering the spectral range, the sum of the consecutive band projectors is the identity — pure hard crust, zero new axioms (count stays 11; the proposal's one-step-per-run rule keeps Step 4 queued).

**Changes:** intent + route recorded in the execution plan. Route: an *unconditional* telescoping law `∑_{k<n} B(t_k, t_{k+1}) = P_{t_n} − P_{t_0}` (range-succ induction, `abel` residue — load-bearing on the band definition's exact difference shape); completeness from the two endpoint covering hypotheses only; monotone-family orthogonality as its own theorem (where monotonicity is load-bearing, per the no-decorative-hypotheses discipline); consumer vector form `∑ B_k *ᵥ x = x`. Planned QA: partition witness (theorem + independent band-value routes), empty-middle three-band partition touching the closed top endpoint, both endpoint guards (refuting the hypothesis-free form — the design note's "silently ignores modes" failure mode), non-monotone telescoping witness, vector form. Environment: the pruned-oleans state recurred at run start; the recorded interpreted cache fetch restored 5685 ("Unpacked in 22688 ms"). Lean work to follow in `GraphTheory/Band.lean` and `QA/SpectralGraph/Band_QA.lean`.

## 2026-08-20T20:23:00Z — Spectral band projectors, Step 2 delivered (orthogonality of disjoint bands)

**Run:** `20260820T171956Z-run-1`  
**Session:** `ses_fdfd37fa6ffeT8EAoVx1GrUhr4`  
**Status:** completed  
**Milestone:** The Active priority table's only remaining High row (`proposals/spectral-band-projectors.md`) at its recorded open next step — Step 2, orthogonality of disjoint bands — delivered as pure hard crust, **zero new axioms** (count stays 11; `#print axioms` on all four new public theorems reads only `propext, Classical.choice, Quot.sound`). The proposal's one-step-per-run rule was honored: Steps 3–4 untouched. (Count correction: the in-progress entry above said 12 — the verified count has been 11 since the operator-directed `spectral_persistence` removal earlier on 2026-08-20; the scoreboard authority confirms 11.)

**Changes:** `GraphTheory.Band` gained the Step-2 section: `bandProjector_mul_bandProjector_eq_zero` / `_eq_zero'` (bands over disjoint intervals compose to zero in **both orders**, by exactly the paved route — the Step-1 cross-law's ordered forms expand `(P_b − P_a)(P_d − P_c)` to the four-term expression that collapses under the ordering; the flipped theorem is a direct expansion through `_of_le'`, not a transpose wrapper), `bandProjector_inner_eq_zero` (the consumer's form: `(B_{a,b} *ᵥ x) ⬝ᵥ (B_{c,d} *ᵥ y) = 0`, the first band moved across the dot product through `vecMul_transpose`/`dotProduct_mulVec`/`vecMul_vecMul`), and `eq_zero_of_bandProjector_mulVec_eq_self` (the subspace-level reading of the step's "they share no eigenvector": a vector fixed by two disjoint bands is zero). The hypothesis set is folded to `a ≤ b`, `c ≤ d`, `b ≤ c` — `b ≤ c` is exactly interval disjointness and is load-bearing. QA `SpectralGraph/Band_QA.lean` +16 (43 in file, 932 total): composition to zero through the theorem *and* by raw literal multiplication in both orders; image orthogonality by both routes with the **same-band counter-witness** (`1 ≠ 0`, separating disjointness from fixture zeros); the composed action annihilating a filtered signal; and the **overlap guard** — bands `(−1, 3]` and `(1, 4]` sharing the eigenvalue `3` compose to the provably nonzero `diag(0,1)`, refuting the hypothesis-free form. Records: module/QA/umbrella docstrings, scoreboard (932/11/0, both Direct rows prepended with the Step-2 slice, `lake build` row extended, Step-2 interpretation bullet, cache-provenance invocation note, two stale narrative counts fixed — lint row 12 → 11 axioms, QA-definition line 917 → 932), radar (axis 2 orthogonality layer, **held at 4.0** per protocol; QA 932/34, **held at 4.0**; both holds logged), README (status table synced to the scoreboard authority 11/932; proved list extended), SGT index map (Band section +3 rows, Steps 1–2), proposal (Step-2 delivery record + status header + open-next-step → Step 3), `proposals/README.md` (High row note, Delivered row, progress paragraph), execution plan.

**Decisive commands and outcomes:** `lake env lean` on `Band` and `Band_QA` — zero errors, zero warnings (public module first pass; QA needed three small proof-shape fixes, one traced to `rw` closing `3 ≤ 3` unassisted, the cause of the only linter warning seen); `#print axioms` on 4 public + 12 QA headline theorems — only `propext, Classical.choice, Quot.sound`; oleans produced directly during iteration; **all thirty-four QA modules batch-elaborated — BATCH-DONE fail=0**; **full `lake build` ✔ (2186 targets, "Build completed successfully")**, executed detached from the tool timeout (log + poll) with the only diagnostic the documented pre-existing `hγ` warning in `ProjectorDrift.lean`; `lint_axioms` (11), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (932/11/0). Environment: the pruned-oleans state recurred at run start; the interpreted cache fetch restored 5387 ("Unpacked in 21270 ms"); invocation note recorded — under `lake --dir`, the `--run` file argument resolves relative to the cwd, so invoke from the repo root with the full package-relative path.

**Verification:** every changed module elaborated directly with zero errors/warnings and linked in the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional; the orthogonality statements are load-bearing on the Step-1 cross-law (a wrong cross-law would leave a nonzero four-term residue and fail both the theorem route and the raw-literal QA route).

**Remaining risk:** low — Step 2 is four-consequence algebra over the already-QA'd cross-law, with both composition orders dual-route-checked and the overlap guard refuting the hypothesis-free form. The `a > b` junk region remains documented-not-guarded (no theorem claims anything there). Steps 3–4 of the proposal (partition completeness, the Hilbert projection specialization) remain open.

**Next handoff:** the same proposal's Step 3 — completeness under a partition of the spectrum (the two-band covering instance `bandProjector_eq_one` already exists; Step 2 is the pairwise half), then Step 4 (survey `Analysis/InnerProductSpace/Projection.lean` signatures first); or the queued Medium rows.

## 2026-08-20T17:20:30Z — Spectral band projectors, Step 2 (orthogonality of disjoint bands)

**Run:** `20260820T171956Z-run-1`  
**Session:** `ses_fdfd37fa6ffeT8EAoVx1GrUhr4`  
**Status:** in-progress  
**Milestone:** The Active priority table's only remaining High row (`proposals/spectral-band-projectors.md`) at its recorded open next step — Step 2, orthogonality of disjoint bands: for bands `(a, b]` and `(c, d]` with `b ≤ c`, the two band projectors compose to zero in both orders and their images are orthogonal — pure hard crust, zero new axioms (count stays 12; the proposal's one-step-per-run rule keeps Steps 3–4 queued).

**Changes:** intent + route recorded in the execution plan (the Step-1 nestedness cross-law's ordered forms expand the band product to the collapsing four-term expression; `b ≤ c` is exactly interval disjointness, so the hypothesis is load-bearing — the QA plan includes an overlap guard refuting the hypothesis-free form). Environment: the pruned Mathlib-oleans state recurred at run start (0 present); the recorded interpreted cache fetch is running in the background. Lean work to follow in `GraphTheory/Band.lean` and `QA/SpectralGraph/Band_QA.lean`.

## 2026-08-20 — Strip "dynamic spectral persistence" framing from strategy docs (operator-directed, interactive session)

**Run:** `unavailable` (interactive Claude Code session)  
**Session:** `unavailable`  
**Status:** completed  
**Milestone:** Follow-up to the `spectral_persistence` axiom removal above.
The operator asked where else "spectral persistence" appears in the
repository; the answer was that it's a named strategic direction in
`AGENTS.md`'s Mission and Priority-order sections, in
`docs/1_STRATEGY.md`, and in `Azuma.lean`'s docstring — distinct from the
axiom itself, since the underlying proved modules
(`Derived/EventStream.lean`, `Derived/ProjectorDrift.lean`) rest on
legitimate axioms (Davis–Kahan, matrix Azuma-Hoeffding) and were not in
question. Given a choice between leaving it, stripping the framing while
keeping the proved math, or deleting the modules outright, the operator
chose **strip the framing, keep the math** — scoped explicitly to
`AGENTS.md`, `docs/1_STRATEGY.md`, and the `Azuma.lean` docstring; no
other file in the broader "persistence" grep footprint (`docs/2_ARCHITECTURE.md`,
`docs/3_SPECTRAL_THEORY.md`, `Spectral.lean`, the proposals mentioning
it) was touched, since they were outside the selected option.

**Changes:** `AGENTS.md` — the Mission sentence no longer names "dynamic
spectral persistence" and "x90 applications" as a direction to radiate
toward (replaced with a pointer to `docs/3_SPECTRAL_THEORY.md`'s own
retained-example status, which already disclaims itself as a roadmap
goal); Priority order item 6 reworded from "Advance dynamic persistence
and application work" to "Advance application-facing work." This also
fixes a standing internal inconsistency: `AGENTS.md` was telling
autonomous runs to advance toward persistence as a destination, while
`docs/1_STRATEGY.md` and `docs/3_SPECTRAL_THEORY.md` already said the
opposite ("not Scaffold's research goal," "do not extend... merely
because... available"). `docs/1_STRATEGY.md`'s paragraph reworded to
drop "already developed elsewhere" (inaccurate — it was developed in
this repository's own derived layer) while keeping the substantive
disclaimer. `Azuma.lean`'s docstring reworded to introduce matrix
Azuma–Hoeffding on its own terms (a real, independently citable
theorem) rather than via the persistence narrative, with a factual
pointer to its actual consumer (`eventStreamTail`) instead.

**Verification:** `lake env lean` on `Azuma.lean` — zero errors (the
other two edits are prose-only, in `.md` files);
`scripts/check_markdown_links.py` passes.

**Remaining risk:** none identified. This was a framing/wording change
with no effect on any theorem, axiom, or QA declaration; counts are
unchanged from the prior entry (11 axioms, 916 QA declarations).

**Next handoff:** none opened by this change.

## 2026-08-20 — `spectral_persistence` removed (operator-directed, interactive session)

**Run:** `unavailable` (interactive Claude Code session, not an
`opencode-pursue`/OpenCode wrapper invocation)  
**Session:** `unavailable`  
**Status:** completed  
**Milestone:** Remove the `spectral_persistence` axiom
(`Scaffold/Mathlib/GraphTheory/Dynamics.lean`) and its sole QA consumer,
per explicit operator instruction. Editorial removal, not a proof-based
retirement: the operator's stated criterion was that the axiom is not
well-established published math, unlike this repository's other
axioms — distinct from every prior retirement, which discharged a
citation-backed axiom by proof. A broader initial request to also scrub
all mentions from `research/archive/` was raised earlier in the same
session and declined (conflicts with `AGENTS.md`'s archive-immutability
rule and would falsify historical QA-coverage records); this narrower
Lean-source-only removal was carried out instead, at the operator's
explicit re-scoping ("remove the lean").

**Changes:** deleted `axiom spectral_persistence` and its docstring
section from `Dynamics.lean`; deleted its sole consumer
`persistence_zero_perturbation_QA` (and the `set_option
linter.deprecated false in` it required) from `Dynamics_QA.lean`; updated
both files' module docstrings to drop the persistence framing. Fixed a
dangling reference in `Scaffold/Derived/ProjectorDrift.lean`'s docstring
(previously named the axiom as an available-but-unused per-step route).
`TimeVaryingGraph`, `laplacianSequence`, `IsEventDriven`, and
`laplacianSequence_symmetric` are untouched — confirmed still consumed
by `Derived/EventStream.lean` and `Derived/ProjectorDrift.lean`/their QA
files via grep before editing, since those are the load-bearing building
blocks the derived layer's proved two-endpoint persistence chain
(`davisKahanTwoPoint`, `eventStreamProjectorDrift`) actually uses.
Synced: `index/map/spectral_graph.md` (removed the axiom's table row),
`index/map/perturbation.md`, `index/sources/davis_kahan_1970.md`
(removed the axiom's citation-mapping row; the `davis_kahan_sin_theta`
citation itself is untouched, since that axiom still stands),
`docs/2_ARCHITECTURE.md`, `docs/7_SGT_RADAR.md` (axiom-minimization trend
line), `README.md` (status table and trust-surface prose),
`docs/5_QA_SCOREBOARD.md` (regenerated metrics via
`scripts/generate_qa_scoreboard.py`, plus a new dated narrative bullet
and a trimmed now-resolved priority item), `docs/6_SGT_BACKLOG.md`
(appended an update note to the existing entry, not rewritten), and
`docs/EXECUTION_PLAN.md`. `cdx-clean-assess.md` (a dated point-in-time
audit snapshot) and `research/archive/` were deliberately left
untouched — both are historical record, not live documentation.

**Decisive commands and outcomes:** `lake env lean` on the three touched
Lean modules individually — zero errors on all three; one pre-existing,
unrelated `unused variable 'hγ'` warning in `ProjectorDrift.lean`
(confirmed present before this change, in code untouched by this edit —
the only change to that file was a documentation comment).
`scripts/generate_qa_scoreboard.py` regeneration: explicit axioms 12 →
11, QA declarations 917 → 916 (`Dynamics_QA.lean` 6 → 5). A full `lake
build` was not run for this change — not requested, and the edit makes
no signature changes to anything another module imports, so isolated
elaboration of the three touched files is the relevant check.

**Remaining risk:** low for correctness (the removed axiom had zero
non-QA consumers by its own deprecation record, confirmed again here by
grep before deletion). The larger judgment call — whether "not
well-established math" is the right bar for what belongs in this
repository's axiom set, and whether it should be applied to any other
axiom — was not evaluated here; this entry documents one instance
executed on explicit, scoped operator instruction, not a new standing
policy.

**Next handoff:** none opened by this change; the Active priority table
in `proposals/README.md` and the Active milestone in
`docs/EXECUTION_PLAN.md` (Spectral Band Projectors Steps 2–4) are
unaffected.

## 2026-08-20T13:39:48Z — Spectral band projectors, Step 1 (two-sided band projector)

**Run:** `20260820T133553Z-run-1`  
**Session:** `ses_fe0a0f4b6ffeOdvy2Pf5lWRbOv`  
**Status:** in-progress  
**Milestone:** The Active priority table's only remaining High row
(`proposals/spectral-band-projectors.md`) at its recorded open next step —
the two-sided band projector `bandProjector M hM a b := spectralProjector M hM b − spectralProjector M hM a`
with idempotence and self-adjointness, pure hard crust (zero new axioms), the
frequency-selective bandpass object named by the proposal's external consumer.

**Changes:** intent + route recorded in the execution plan (pre-edit survey:
the projector lemma set already has symmetry/idempotence/extremes — the
load-bearing missing piece is the nestedness cross-law
`P_{c₁} * P_{c₂} = P_{min c₁ c₂}`, from which band idempotence and the old
idempotence both derive). Environment: the pruned Mathlib-oleans state
recurred at run start (0 present); the recorded interpreted cache fetch
restored 5685 (`lake --dir=.lake/packages/mathlib env lean --run <pkg>/Cache/Main.lean get`).
Lean work starting in `GraphTheory/Spectral.lean` (cross-law + action pair)
and the new `GraphTheory/Band.lean` + `QA/SpectralGraph/Band_QA.lean`.

## 2026-08-20T16:26:39Z — Spectral band projectors, Step 1 (two-sided band projector)

**Run:** `20260820T133553Z-run-1`  
**Session:** `ses_fe0a0f4b6ffeOdvy2Pf5lWRbOv`  
**Status:** completed  
**Milestone:** The Active priority table's only remaining High row
(`proposals/spectral-band-projectors.md`) at its recorded open next step —
the two-sided `(a, b]` band projector with idempotence and self-adjointness,
pure hard crust (zero new axioms; count stays 12).

**Changes:** the new `Scaffold/Mathlib/GraphTheory/Band.lean`
(`bandProjector M hM a b := spectralProjector M hM b − spectralProjector M hM a`,
parameterized by interval per the design note, total definition with the
`a > b` junk documented; symmetry, idempotence at `a ≤ b`, the mode-selection
action interface — in-band fixed, below-/above-band annihilated — the
below-spectrum special case, the covering band `= 1`); enabling lemmas in
`GraphTheory.Spectral` (the nestedness cross-law
`spectralProjector_mul_spectralProjector` `P_{c₁} * P_{c₂} = P_{min c₁ c₂}`
with ordered forms — the pre-edit survey's route finding: idempotence of a
*difference* needs the cross-law, not just idempotence of the factors; the
old `spectralProjector_idempotent` re-derived from it at unchanged
statement, its 50-line proof now one rewrite; and the complete action
description `spectralProjector_mulVec_eigvecOf` with specializations); the
new `QA/SpectralGraph/Band_QA.lean` (27 declarations); the umbrella import
+ docstring; records (scoreboard, radar, README, SGT index map, proposal
status/delivery record/open-next-step, proposals README High row + Delivered
row + progress note, execution plan).

**Decisive commands and outcomes:** `lake env lean` on `Spectral`,
`Band`, and `Band_QA` — zero errors, zero warnings on the two new modules
(`Spectral`'s only diagnostics are the documented pre-existing
section-variable warnings); `#print axioms` on the seven public and nine
headline QA theorems — only `propext, Classical.choice, Quot.sound`; **all
thirty-four QA modules batch-elaborated, zero errors**; **full `lake build`
✔ — "Build completed successfully", 2186 targets, zero errors** (executed
detached from the tool timeout, log + poll, per the recorded recovery
procedure; the Mathlib residue replay ~2 h); `lint_axioms` (12),
`check_citations`, `check_markdown_links` pass; scoreboard regeneration
idempotent (**917/12/0**; `Band_QA` a new file row at 27). Environment: the
pruned-oleans state recurred at run start; the interpreted cache fetch
restored 5685 before any elaboration (`lake --dir=.lake/packages/mathlib env
lean --run <pkg-path>/Cache/Main.lean get` — `--dir` from the repo root,
since direct `cd` into the package is sandboxed). Implementation notes for
future projector QA: `fin_cases` eta-expanded `Fin` indices defeat
`rw`/`linarith` atom matching (coerce back with defeq-tolerant `have`s or
`show`, the recorded trap); `rw ... at` accepts only local hypotheses, not
theorem names (copy with `have` first); `linear_combination` likewise wants
local fvar atoms; `Finset.sum_ite_eq` matches `if b = x` and `sum_ite_eq'`
matches `if x = b`; `(if P then f else 0) k` distributes via `ite_apply`
(root namespace), not `apply_ite`; un-ascribed `!![..]` literals elaborate
as ℕ — ascribe `(!![..] : Matrix (Fin 2) (Fin 2) ℝ)`; type-ascribed `have`
is the bridge for `eigvecOf`/`eigvalOf` defs versus Mathlib's raw
`WithLp`-coerced spectral-theorem terms (the center's own idiom).

**Verification:** every changed module elaborated directly and built in the
full default build; QA covers both mode-selection directions with the
excluded-mode-not-fixed witness and the between-eigenvalues zero band (the
gapped-definition guard), the band values pinned against hand-computed
outer products on a diagonal fixture whose spectrum is pinned from
trace+determinant independent of the machinery under test.

**Remaining risk:** low — Step 1 is one-consequence algebra over the
already-QA'd projector machinery, with the new cross-law itself numerically
instantiated in both orders. The `a > b` junk region is documented, not
guarded; no theorem claims anything there. Steps 2–4 of the proposal
(orthogonality of disjoint bands, partition completeness, the Hilbert
projection specialization) remain open.

**Next handoff:** the same proposal's Step 2 — orthogonality of disjoint
bands (`a ≤ b ≤ c ≤ d`; the cross-law's ordered forms already expand
`(P_b − P_a)(P_d − P_c)` to the collapsing four-term expression), then
Steps 3–4; or the queued Medium rows.

## 2026-08-17 — SGT center reaches a clean default build

**Status:** completed  
**Milestone:** Restore honest build reachability for the spectral graph theory
(SGT) center, its perturbation bridge, and its dynamic-persistence frontier.

The library target no longer points at the nonexistent `Main.lean`; `lake
build` now compiles the `Scaffold` umbrella successfully. To make that result
meaningful, the SGT surface was rebuilt around real sorted-spectrum,
Laplacian, projector, and update definitions, with proved basic identities
and QA. Classical results not yet formalized remain visible as cited axioms,
rather than hidden placeholders.

The repaired bridge covers Cheeger, Weyl, Davis--Kahan, dynamics, matrix
updates, and norms. QA now has 47 declarations and no live `sorry` or
`admit`; it exposed and corrected a missing no-self-loop hypothesis in the
Laplacian-trace statement. Citation and Markdown checks were repaired so they
respect ordinary source-comment placement and ignore vendored dependencies.

**Verification:** `lake build` completed successfully. Mathlib artifacts were
bootstrapped through the Lean interpreter after the native cache executable
hit a local macOS dyld failure; the workaround and its provenance are recorded
in the QA scoreboard.

**Trust boundary:** the SGT/bridge public API retains explicit cited axioms
for Cauchy interlacing, the variational characterization of `lambda2`,
Cheeger bounds, Weyl, Davis--Kahan, persistence, and matrix-update identities.
Their consequences are checked; the axioms themselves are not claimed as
foundationally proved.

**Next handoff:** repair the excluded probability/concentration modules,
starting with malformed syntax and undefined `RV`/`Independent`, then add the
missing citation for `matrix_azuma_hoeffding`. Separately, review page-level
locators for Horn--Johnson and Chung and reduce the remaining admitted
projector/eigenbasis interfaces.

## 2026-08-17 — Concentration-bridge repair

**Status:** in-progress  
**Milestone:** Recover the probability/concentration bridge (all six
`Probability.Concentration` modules) on real Mathlib probability interfaces,
certify its QA, and restore umbrella reachability.

Direct elaboration confirmed the recorded failures (invalid binder
annotations from undefined `ZeroOmega`, `expected token` parses from the
ill-typed probability side `(ω : Ω) ↦ … ≤ …`, undefined `Independent`, `Prob`,
`Matrix.spectral_norm`, and an `MRV n n` arity mismatch). A scratch
elaboration probe against the pinned Mathlib (v4.14.0, a pruned checkout
without `Filtration`/`Adapted`/`condexp`) validated the replacement
interfaces: plain `Ω → ℝ` / `Ω → Matrix V V ℝ` functions, explicit
`μ : Measure Ω` with `IsProbabilityMeasure`, `ProbabilityTheory.IndepFun`,
a new product-σ-algebra measurable-space instance for `Matrix`, scoped
`Matrix.L2OpNorm` for the spectral norm, `Matrix.PosSemidef` for the
semidefinite order, and an elementary comap-based natural filtration with
set-integral conditional mean zero for matrix Azuma. Next: write modules,
QA, and index updates, then verify each module directly.

## 2026-08-17 — Concentration bridge restored and certified

**Status:** completed  
**Milestone:** Recover the probability/concentration bridge (all
`Probability.Concentration` modules) on real Mathlib probability
interfaces, certify its QA, and restore umbrella reachability.

**Changes:** all three scalar modules and all three matrix modules were
restated over plain `Ω → ℝ` / `Ω → Matrix V V ℝ` functions, an explicit
`Measure` with `IsProbabilityMeasure`, `ProbabilityTheory.IndepFun`,
the spectral norm via scoped `Matrix.L2OpNorm`, `Matrix.PosSemidef` for
the semidefinite order, and a new product-σ-algebra `MeasurableSpace`
instance on real matrices (new `Matrix/Basic.lean`; Mathlib ships none).
`subgaussian_norm` (an axiom-typed hole) became the real definition
`subgaussianNorm`; `hoeffding_iid` and `bernstein_iid` became proved
derived theorems; five unconsumed subgaussian axioms (moment growth,
linear combination, centering, sum bound) were removed from the trust
boundary. Matrix Azuma is stated through a new `MatrixMDS` structure
(comap past σ-algebras plus set-integral conditional means) because the
pinned Mathlib snapshot has no filtration/conditional-expectation API.
Both concentration QA files were rewritten to instantiate each axiom at
degenerate zero sequences (constant independence, `PosSemidef.zero`,
empty-event measures) and to check cross-axiom subgaussian coherence.

**Decisive commands and outcomes:** direct `lake build` of each of the
seven public modules (six repaired plus `Matrix/Basic`) and both QA
targets passed; the full `lake build` umbrella passed after re-adding
the subtree; `generate_qa_scoreboard.py`, `lint_axioms.py`,
`check_citations.py`, and `check_markdown_links.py` all pass.

**Verification:** 59 QA declarations (up from 48) with zero
`sorry`/`admit` anywhere under `Scaffold/`; explicit axiom count reduced
from 26 to 19, all cited and indexed; the long-standing
`matrix_azuma_hoeffding` citation/index warnings are closed.

**Trust boundary:** the concentration tail bounds (Hoeffding, Bernstein,
empirical, subgaussian lemma/tail, matrix Hoeffding/Bernstein/Azuma)
remain explicit cited axioms; QA checks their interfaces and degenerate
consequences, not their truth.

**Remaining risk:** the two-sided (factor-2) spectral-norm forms and the
MGF characterization of `subgaussianNorm` involve documented constant-level
differences from the cited sources; `MatrixMDS` should be restated through
Mathlib filtrations once available. The dynamic frontier still does not
consume the bridge.

**Next handoff:** derive the first `Scaffold/Derived/` theorem — an
event-stream cumulative-perturbation tail for `IsEventDriven` graph
streams from the concentration axioms — then the Horn–Johnson/Chung
page-level citation review.

## 2026-08-17T19:22:51Z — Derived event-stream tail (with inward Azuma repair)

**Run:** `20260817T191152Z-run-2`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Implement `Scaffold/Derived/EventStream.lean`, the first
derived-layer theorem: an Azuma tail bound on the cumulative Laplacian
perturbation `‖L_m - L_0‖` of a random event-driven graph stream.

Preparing the derivation exposed an inner defect: `matrix_azuma_hoeffding`
was stated with denominator `8 R²`, independent of the number of summands
`m`. Tropp's Theorem 7.1 variance statistic accumulates; the uniform-bound
specialization is `σ² = m R²`, and without the `m` factor the statement is
false for `m ≥ 2` (Rademacher sum counterexample). Per the center-out
policy the axiom is repaired before any consumer is built on it. Plan:
repair the axiom and its QA, add the proved telescoping identity plus the
random event-stream model and derived tail theorem, certify with
degenerate-stream QA, then umbrella and hygiene updates.

## 2026-08-17T19:31:02Z — Derived event-stream tail completed

**Run:** `20260817T191152Z-run-2`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** First derived-layer theorem: an Azuma tail bound on the
cumulative Laplacian perturbation of a random event-driven graph stream,
connecting the dynamic frontier to the concentration bridge.

**Changes:** repaired `matrix_azuma_hoeffding` to carry the cumulative
variance factor (`8 m R²` denominator); without it the statement was false
for `m ≥ 2` (Rademacher-sum counterexample) and had no consumers at repair
time. New `Scaffold/Derived/EventStream.lean`: proved telescoping identity
`sum_range_telescope`, the increment process `randomLaplacianIncrement`,
the proved interface lemma
`randomLaplacianIncrement_bounded_iff` (uniform bound ↔ pointwise
`IsEventDriven`), and the axiom-backed derived theorem `eventStreamTail`
bounding `P {‖L_m - L_0‖ ≥ t}`. New `Scaffold/QA/Derived/EventStream_QA.lean`
(seven declarations): telescoping at 0/1, constant-stream interface
coherence, and the derived tail instantiated at a zero-increment stream
with exact empty-event measures. Umbrella, README, architecture, scoreboard,
and the probability-concentration index updated.

**Decisive commands and outcomes:** `lake build` on
`Scaffold.Mathlib.Probability.Concentration.Matrix.Azuma`,
`Scaffold.QA.Concentration.Matrix_QA`, `Scaffold.Derived.EventStream`,
`Scaffold.QA.Derived.EventStream_QA` all pass individually; full `lake
build` passes; `generate_qa_scoreboard.py`, `lint_axioms.py`,
`check_citations.py`, `check_markdown_links.py` all pass.

**Verification:** 66 QA declarations (up from 59), zero `sorry`/`admit`
anywhere under `Scaffold/`, 19 explicit cited axioms; the derived module is
certified through the umbrella.

**Trust boundary:** `eventStreamTail` is a checked deduction conditional
on `matrix_azuma_hoeffding` (Tropp 2012, Thm 7.1, uniform-bound
specialization `σ² = m R²`); it is not a foundationally proved result. The
Azuma repair is documented in the scoreboard interpretation section.

**Remaining risk:** `MatrixMDS` uses the elementary comap filtration; a
future Mathlib filtration API should replace it. The projector-drift
combination may expose interface friction on the perturbation side
(cumulative vs per-step bounds).

**Next handoff:** derived step 2 — high-probability cumulative
projector-drift corollary combining `eventStreamTail` with
`spectral_persistence`/Davis–Kahan under a spectral gap; then the
Horn–Johnson/Chung page-level citation review.

## 2026-08-17T19:26:48Z — Derived projector drift (concentration → DK)

**Run:** `20260817T192354Z-run-3`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Derived step 2: high-probability projector-drift bound
combining `eventStreamTail` (Azuma) with Weyl and Davis–Kahan, completing
the `‖Σₖ Eₖ‖ / γ` chain without adding any new axiom.

Design decision recorded before editing: the honest composition is
two-endpoint. Davis–Kahan is a two-point statement and Azuma controls the
two-endpoint displacement `‖L_m − L_0‖`; the DK separation hypothesis is
discharged pointwise from `weyl_inequality` plus proved `evals_sorted`
monotonicity and a base-gap hypothesis. The derivation exposes one inner
interface need — `initialProjector_congr` (proof-irrelevance transport of
projectors along matrix equalities), which will be added as a proved
theorem in the SGT center `GraphTheory.Spectral`. New modules:
`Scaffold/Derived/ProjectorDrift.lean` (`davisKahanTwoPoint`,
`eventStreamProjectorDrift`) plus `Scaffold/QA/Derived/ProjectorDrift_QA.lean`.

## 2026-08-17T19:36:43Z — Projector drift derived; persistence chain complete

**Run:** `20260817T192354Z-run-3`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Derived step 2: high-probability projector-drift bound,
completing the `‖Σₖ Eₖ‖ / γ` persistence chain end-to-end without adding
any new axiom.

**Changes:** new `Scaffold/Derived/ProjectorDrift.lean` with
`davisKahanTwoPoint` (Davis–Kahan two-point form, separation discharged
from `weyl_inequality` plus proved `evals_sorted` monotonicity under a
base-gap hypothesis `δ ≤ gap_B − ‖C−B‖`) and `eventStreamProjectorDrift`
(`μ{‖P_{L_m} − P_{L_0}‖ ≥ s/(γ−s)} ≤ 2 d exp(−s²/(8 m R²))` for
martingale event streams with base gap ≥ γ and `0 < s < γ`), the latter
combining the wrapper with `eventStreamTail` through an event inclusion.
One proved center theorem added to `GraphTheory.Spectral`:
`initialProjector_congr` (projector transport along matrix equalities by
proof irrelevance), exposed by the derivation and used to restate DK's
`A + E` conclusion at `L_m`. New `Scaffold/QA/Derived/ProjectorDrift_QA.lean`
(four declarations): wrapper at `C = B`, constant-stream instantiation of
the drift theorem, and empty-drift-event tightness. Umbrella, README,
architecture, scoreboard, and index updated. Design decision recorded:
the composition is two-endpoint (DK is a two-point statement and Azuma
controls the two-endpoint displacement), answering the
cumulative-vs-per-step interface question.

**Decisive commands and outcomes:** `lake build` on
`Scaffold.Mathlib.GraphTheory.Spectral`, `Scaffold.Derived.ProjectorDrift`,
`Scaffold.QA.Derived.ProjectorDrift_QA` all pass individually; full `lake
build` passes; `generate_qa_scoreboard.py`, `lint_axioms.py`,
`check_citations.py`, `check_markdown_links.py` all pass.

**Verification:** 70 QA declarations (up from 66), zero `sorry`/`admit`
anywhere under `Scaffold/`, 19 explicit cited axioms (unchanged — the
milestone added hard crust only).

**Trust boundary:** `davisKahanTwoPoint` is conditional on
`davis_kahan_sin_theta` and `weyl_inequality`; `eventStreamProjectorDrift`
additionally on `matrix_azuma_hoeffding` (via `eventStreamTail`). Neither
is foundationally proved.

**Remaining risk:** the drift theorem assumes the spectral gap at the base
`L_0` only; a gap-along-the-path variant would need the per-step
`spectral_persistence` axiom or pathwise Weyl bookkeeping. The eigenbasis
facts behind `spectralProjector` remain unproved in the center.

**Next handoff:** prove spectral-projector idempotence and eigenbasis
orthonormality in the SGT center (projector algebra), then the
Horn–Johnson/Chung page-level citation review; the x90 observable
specification is now unblocked by a credible inner chain.

## 2026-08-17T19:40:12Z — Spectral-projector algebra in the center

**Run:** `20260817T193702Z-run-4`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Prove the projector algebra behind `spectralProjector`
(eigenbasis orthonormality and completeness, projector idempotence, extreme
thresholds) in the SGT center, replacing facts currently consumed through
the admitted perturbation interfaces with hard crust. No new axioms.

Design recorded before editing: pairwise orthonormality and completeness
of `eigvecOf` come from the pinned Mathlib `OrthonormalBasis` API
(`OrthonormalBasis.orthonormal`, `OrthonormalBasis.sum_repr'`, with
`PiLp.inner_apply` reducing inner products to coordinate sums);
idempotence follows entrywise through `Finset.sum_mul_sum`, sum
reordering, and the orthonormality relation; extreme-threshold theorems
are hypothesis-gated (empty/full filter sets). QA composes the extreme
cases with idempotence; thin-QA rationale documented since these are
theorems rather than axioms.

## 2026-08-17T19:59:41Z — Projector algebra proved in the SGT center

**Run:** `20260817T193702Z-run-4`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Prove the spectral-projector algebra behind
`spectralProjector` in the SGT center, replacing structural facts
previously consumed implicitly through the admitted perturbation
interfaces. No new axioms; hard crust only.

**Changes:** in `GraphTheory.Spectral`, proved `eigvecOf_inner`
(eigenbasis orthonormality from `OrthonormalBasis.orthonormal` with
`PiLp.inner_apply`), `eigvecOf_complete` (completeness from
`OrthonormalBasis.sum_repr'` at `EuclideanSpace.single`,
`EuclideanSpace.inner_single_right` for the coefficients),
`spectralProjector_idempotent` (entrywise expansion: `Finset.sum_mul_sum`,
sum reorder, orthonormality collapse via `Finset.sum_eq_single`),
`spectralProjector_eq_zero` / `spectralProjector_eq_one` (hypothesis-gated
extreme thresholds), and `initialProjector_idempotent`. The
`WithLp`/`EuclideanSpace` type-synonym coercions required explicit
Pi-typed ascriptions (`(∑ … : V → ℝ) b`) since the pruned snapshot lacks
direct sum-application lemmas; the delicate proofs were validated in a
scratch elaboration probe before being transplanted. New QA file
`SpectralGraph/Projector_QA.lean` (5 declarations): unit-norm diagonals of
the two basis relations and extreme-threshold compositions with
idempotence. Scoreboard, architecture debt list, README, and the SGT
index map updated. An operator checkpoint (`4181d07`) landed mid-run and
absorbed the earlier uncommitted work; my scratch probe file swept into
it was deleted as intended hygiene.

**Decisive commands and outcomes:** `lake build` on
`Scaffold.Mathlib.GraphTheory.Spectral` and
`Scaffold.QA.SpectralGraph.Projector_QA` pass; every QA module target
(thirteen) rebuilt individually; full `lake build` passes;
`generate_qa_scoreboard.py`, `lint_axioms.py`, `check_citations.py`,
`check_markdown_links.py` all pass.

**Verification:** 75 QA declarations (up from 70), zero `sorry`/`admit`
anywhere under `Scaffold/`, 19 explicit cited axioms (unchanged).

**Trust boundary:** unchanged — the perturbation inequalities
themselves (`weyl_inequality`, `davis_kahan_sin_theta`,
`spectral_persistence`, Cheeger/interlacing/variational axioms) remain
admitted; only the projector algebra around them became hard crust.

**Remaining risk:** the two basis relations are stated through the
repo's `eigvecOf` coercion; if `eigvecOf`'s definition is ever restated
through a different `WithLp` conversion, the `rfl`-steps need revisiting.
Citation page-level locators remain pending.

**Next handoff:** citation hygiene (Horn–Johnson/Chung page locators,
assumption tightening review), then the `spectral_persistence`
fold-or-deprecate decision, then the x90 observable specification.

## 2026-08-17T20:03:37Z — Citation honesty audit + perturbation tightening

**Run:** `20260817T200010Z-run-5`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Citation hygiene with two interface tightenings: fix the
citation-audit findings on the perturbation/SGT axiom surface, and convert
`spectral_gap_stability` from an admitted axiom into a theorem proved from
`weyl_inequality` (axiom count 19 → 18 at zero trust cost).

Audit findings so far: the Chung index's provenance note ("earlier
revisions recorded Theorem 2.1 p. 42, Theorem 2.2 p. 44") is contradicted
by git history — the initial commit cited only "Theorem 2.2" without a
page and no pre-rebuild index file exists; the Weyl axiom lacks a
statement-differences note explaining that its Lean form is the
spectral-norm corollary of the cited general theorem; the Davis–Kahan
separation hypothesis is stated in a pairwise form whose binding instance
(by `evals_sorted`) is the single-pair cluster separation the cited
Yu–Wang–Samworth Theorem 2 actually uses. Plan: replace the false note
with accurate history (no invented page numbers), add the Weyl note,
tighten the DK hypothesis to the single-pair form (updating the derived
wrapper and QA), and prove `spectral_gap_stability` from Weyl.

## 2026-08-17T20:09:50Z — Citation hygiene completed; axioms 19 → 18

**Run:** `20260817T200010Z-run-5`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Citation honesty fixes on the perturbation/SGT axiom
surface, Davis–Kahan hypothesis tightening, and conversion of
`spectral_gap_stability` from an admitted axiom into a theorem proved
from `weyl_inequality`.

**Changes:** (1) Chung index provenance note corrected — git history
shows the claimed earlier page-level locators ("Theorem 2.1 p. 42,
Theorem 2.2 p. 44") were never recorded (initial commit cited
"Theorem 2.2" without a page); theorem/page numbering now explicitly
unconfirmed, no numbers invented. (2) `weyl_inequality` doc now records
that its Lean form is the spectral-norm corollary of the cited general
Weyl inequality. (3) `davis_kahan_sin_theta` separation tightened to the
single-pair two-cluster form `λ_{k+1}(A+E) − λ_k(A) ≥ δ` (the form of
the cited Yu–Wang–Samworth Theorem 2); `davisKahanTwoPoint` simplified
to one Weyl fact at the gap index (sortedness no longer needed);
DavisKahan QA reduces the pairwise hypothesis via `evals_sorted`.
(4) `spectral_gap_stability` proved from `weyl_inequality` (Weyl at both
gap endpoints plus `linarith`) — identical statement shape, explicit
axioms 19 → 18. Perturbation index map updated to distinguish axiom vs
proved declarations.

**Decisive commands and outcomes:** direct builds of
`Perturbation.Weyl`, `Perturbation.DavisKahan`,
`Derived.ProjectorDrift`, and QA modules `Weyl_QA`, `DavisKahan_QA`,
`Derived.{ProjectorDrift,EventStream}_QA` all pass; full `lake build`
passes; all four hygiene scripts pass; scoreboard confirms 18 explicit
axioms.

**Verification:** 75 QA declarations, zero `sorry`/`admit` under
`Scaffold/`; every axiom cited and indexed.

**Trust boundary:** unchanged in substance for the inequalities
themselves — `weyl_inequality` and `davis_kahan_sin_theta` remain the
admitted perturbation boundary; `spectral_gap_stability` is now a
checked consequence of it rather than a parallel admission.

**Remaining risk:** Horn–Johnson/Chung locator confirmation still needs a
physical or publisher copy. Note: the operator reoriented the execution
plan mid-run toward a broad-SGT backlog (persistence retained only as a
compatibility example); this run's edits preserved that concurrent
reorganization and closed the citation-hygiene item within it.

**Next handoff:** first broad-SGT backlog (weighted/normalized Laplacian
interoperability, random-walk/Markov interfaces, expansion/cut
interfaces, spectral algorithms), ranked by concrete reuse.

## 2026-08-17T20:12:04Z — Broad-SGT backlog + random-walk interfaces

**Run:** `20260817T200846Z-run-6`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Deliver the first broad-SGT backlog (ranked by concrete
reuse, center-first) together with its top-ranked item implemented:
random-walk/transition-matrix interfaces for `d`-regular graphs, bridging
the combinatorial Laplacian center to the normalized/Cheeger world and to
future Markov-chain consumers. Pure hard crust, no new axioms.

Design: `transitionMatrix A d := d⁻¹ • A` (real definition); proved
symmetry, row-stochasticity `∑ j P i j = 1` under `deg A i = d` and
`0 < d`; `randomWalkLaplacian A d := 1 - transitionMatrix A d`; proved
identity with `regularNormalizedLaplacian` (interop by theorem, not by
definition-sharing) and the scaling bridge
`randomWalkLaplacian = d⁻¹ • laplacian` for `d`-regular graphs. QA
instantiates everything at a concrete two-vertex graph.

## 2026-08-17T20:17:06Z — Broad-SGT backlog published; random-walk interfaces delivered

**Run:** `20260817T200846Z-run-6`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Deliver the first broad-SGT backlog (ranked by concrete
reuse, center-first) and implement its top-ranked item: random-walk /
Markov interfaces for `d`-regular graphs, bridging the combinatorial
Laplacian center to the normalized/Cheeger world. Pure hard crust, no
new axioms.

**Changes:** new `docs/6_SGT_BACKLOG.md` (six ranked items, each naming
consumers, dependency paths, and gates; standing decisions on
`spectral_persistence` and re-admissions; linked from the README
canonical-docs list). New `Scaffold/Mathlib/GraphTheory/RandomWalk.lean`
(all proved): `transitionMatrix` (`d⁻¹ • A`), `transitionMatrix_symmetric`,
`transitionMatrix_row_sum` (row-stochasticity for `d`-regular graphs —
the interface Markov-chain consumers need),
`randomWalkLaplacian`, `randomWalkLaplacian_symmetric`,
`randomWalkLaplacian_eq_regularNormalizedLaplacian` (interop with the
Cheeger bridge by theorem, not definition-sharing),
`randomWalkLaplacian_eq_smul_laplacian` (bridge to the combinatorial
center: `L_rw = d⁻¹ • L`). New QA
`SpectralGraph/RandomWalk_QA.lean` (7 declarations): a concrete
two-vertex edge graph with fully computed symmetry, degree,
row-stochasticity, transition entries, both bridge identities, and the
Laplacian entries. Umbrella, SGT index map, README maturity list, and
scoreboard updated.

**Decisive commands and outcomes:** `lake build` on
`Scaffold.Mathlib.GraphTheory.RandomWalk` and
`Scaffold.QA.SpectralGraph.RandomWalk_QA` pass; full `lake build`
(including the new umbrella import) passes; all four hygiene scripts
pass.

**Verification:** 82 QA declarations (up from 75), zero `sorry`/`admit`
under `Scaffold/`, 18 explicit cited axioms (unchanged).

**Trust boundary:** unchanged; the increment adds only proved
statements. The Cheeger axioms remain the admitted boundary for the
normalized world.

**Remaining risk:** the bridges are restricted to the `d`-regular cone;
the irregular adapters (backlog item 2) are gated on representing
`D^{-1/2}` without a pinned-Mathlib square root.

**Next handoff:** backlog item 2 — irregular normalized-Laplacian
adapters (walk-form statements plus spectral similarity transfer), then
expansion/cut interfaces as consumers emerge.

## 2026-08-17T20:19:58Z — Irregular normalized-Laplacian adapters

**Run:** `20260817T201730Z-run-7`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Backlog item 2: the general (irregular) symmetric
normalized Laplacian as a real definition, removing the `d`-regular
restriction of the current normalized surface without any matrix square
root.

Key design decision: only a *diagonal* square root is needed
(`√deg A i` per vertex), which `Real.sqrt` supplies directly — the
pinned-Mathlib matrix-square-root gap never applies. New module
`GraphTheory.Normalized`: `degreeSqrt`/`degreeInvSqrt` diagonal matrices,
`normalizedLaplacian A = 1 - S⁻¹ A S⁻¹`, proved symmetry, the congruence
`S * L_sym * S = laplacian A` (square roots cancel), and agreement with
`regularNormalizedLaplacian` on the regular cone. QA at a 3-vertex path
(genuinely irregular, `√2` entries) and the regular edge. Spectral
similarity transfer to the walk view deferred to the next slice.

## 2026-08-17T20:31:08Z — Irregular normalized Laplacian delivered

**Run:** `20260817T201730Z-run-7`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Backlog item 2 (core): the general (irregular) symmetric
normalized Laplacian as a real definition, removing the `d`-regular
restriction of the normalized surface without any matrix square root.
Pure hard crust, no new axioms.

**Changes:** new `Scaffold/Mathlib/GraphTheory/Normalized.lean` (all
proved): `degreeSqrt`/`degreeInvSqrt` — the observation that only a
diagonal square root is needed (`Real.sqrt` per vertex), bypassing the
recorded pinned-Mathlib gap; `normalizedLaplacian A = 1 - (1/√D) A (1/√D)`;
`degreeSqrt_mul_degreeSqrt` (`√D √D = degreeMatrix`); inverse-factor
theorems; `normalizedLaplacian_symmetric` (transpose algebra through
`diagonal_transpose`); the congruence
`degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt`
(`√D L_sym √D = laplacian A`, square roots cancel — the
square-root-free-shaped bridge to the combinatorial center); and
`normalizedLaplacian_eq_regularNormalizedLaplacian` (regular-cone
agreement). New QA `SpectralGraph/Normalized_QA.lean` (11 declarations)
at a concrete 3-vertex path (genuinely irregular: degrees 1, 2, 1; the
`-1/√2` adjacent entries computed symbolically) and the regular
two-vertex edge. Umbrella, backlog item 2 status, SGT index map,
scoreboard, and README updated.

**Decisive commands and outcomes:** direct builds of
`Scaffold.Mathlib.GraphTheory.Normalized` and
`Scaffold.QA.SpectralGraph.Normalized_QA` pass (the diagonal-algebra
proofs were probe-validated before transplantation); full `lake build`
passes; all four hygiene scripts pass.

**Verification:** 93 QA declarations (up from 82), zero `sorry`/`admit`
under `Scaffold/`, 18 explicit cited axioms (unchanged).

**Trust boundary:** unchanged; the increment adds only proved
statements. The Cheeger axioms remain the admitted boundary for the
normalized world.

**Remaining risk:** spectral similarity transfer to the walk form and
irregular row-stochasticity are still open (recorded in backlog item 2);
QA entry computations rely on the pinned snapshot's `!!`-notation
evaluation behavior.

**Next handoff:** finish backlog item 2 (walk-form similarity:
`evals`-invariance interface plus irregular row-stochasticity), then
expansion/cut interfaces as consumers emerge.

## 2026-08-17T20:34:12Z — Irregular walk form: row-stochasticity + similarity

**Run:** `20260817T203130Z-run-8`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Finish backlog item 2's walk half: the general
(irregular) walk transition matrix with proved row-stochasticity (the
named Markov consumer) and the similarity identity
`√D · L_walk · (1/√D) = L_sym` as proved hard crust.

Evidence check recorded before editing: the walk Laplacian `I − D⁻¹A`
is not symmetric for irregular graphs, so Scaffold's `evals` (defined
only for `IsSymm`) does not apply to it; the deferred eigenvalue
transfer needs charpoly-roots machinery for non-symmetric matrices,
absent from the pinned Mathlib. The similarity *identity* is therefore
the honest stopping point, with the transfer documented as a precisely
named gap rather than a vague TODO.

## 2026-08-17T20:43:20Z — Irregular walk form completed (backlog item 2 closed)

**Run:** `20260817T203130Z-run-8`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Close the walk half of backlog item 2: the general
(irregular) walk transition matrix with proved row-stochasticity and the
similarity identity to the symmetric normalized Laplacian. Pure hard
crust, no new axioms.

**Changes:** in `GraphTheory.Normalized`: `walkTransitionMatrix`
(`D⁻¹A`, positive degrees), `walkTransitionMatrix_row_sum`
(row-stochasticity on irregular graphs — removing the `d`-regularity
restriction of the RandomWalk module's version; the named Markov
consumer), `walkLaplacian` (`I − D⁻¹A`, documented as non-symmetric in
general), and `degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt`
(`√D · L_walk · (1/√D) = L_sym`, proved via the diagonal-algebra lemma
`√D · D⁻¹ = 1/√D`). QA extended (96 declarations total): row sums on
the 3-vertex path, computed walk entries (`P 1 0 = 1/2`, `P 0 1 = 1`),
and the similarity identity instantiated entrywise. Backlog item 2
marked closed with the eigenvalue-list transfer recorded as the
precisely named residual gap.

**Decisive commands and outcomes:** direct builds of
`Scaffold.Mathlib.GraphTheory.Normalized` and
`Scaffold.QA.SpectralGraph.Normalized_QA` pass; full `lake build`
passes; all four hygiene scripts pass.

**Verification:** 96 QA declarations (up from 93), zero `sorry`/`admit`
under `Scaffold/`, 18 explicit cited axioms (unchanged).

**Trust boundary:** unchanged; hard crust only.

**Remaining risk:** the eigenvalue-list transfer needs a charpoly-roots
interface for non-symmetric matrices (absent in the pinned Mathlib);
until then, spectral statements about the walk form route through the
similarity identity plus the symmetric `L_sym`.

**Next handoff:** backlog item 3 (expansion/cut interfaces with named
consumers) or the `spectral_persistence` retain-or-deprecate decision.

## 2026-08-17T20:46:15Z — spectral_persistence deprecation decision

**Run:** `20260817T204342Z-run-9`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Close the standing `spectral_persistence`
retain-or-deprecate decision (ready-queue item) from consumer evidence,
per the architecture's upstream-replacement lifecycle.

Evidence: grep shows zero non-QA consumers — the derived layer references
it only in a comment, its only use is the QA deliberately exercising the
compatibility surface, and the derived two-endpoint chain covers the
motivating use. Decision: deprecate with a migration note (axiom retained
through the compatibility window; removal is a later release decision,
not a breaking change now). `@[deprecated]` probe-verified to apply to
`axiom` declarations in this toolchain. Plan: annotate + migration note,
linter-silence the deliberate QA use, update indexes/docs (davis_kahan
source, SGT and perturbation maps, backlog standing decision,
architecture debt, scoreboard).

## 2026-08-17T20:49:57Z — spectral_persistence deprecated (decision closed)

**Run:** `20260817T204342Z-run-9`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Close the standing `spectral_persistence`
retain-or-deprecate decision from consumer evidence, per the
architecture's deprecation lifecycle; no new mathematics.

**Changes:** `spectral_persistence` annotated `@[deprecated (since :=
"2026-08-17")]` with a migration note in its doc (zero non-QA consumers;
derived two-endpoint chain covers the motivating use; migration path:
sum the two-endpoint bound over consecutive times or consume
`davisKahanTwoPoint` directly). The attribute's applicability to `axiom`
declarations was probe-verified first. `Dynamics_QA.lean` continues to
exercise the deprecated compatibility surface with
`set_option linter.deprecated false in` scoped to that one lemma (doc
records why). Updated: davis_kahan source index, SGT and perturbation
map entries, backlog standing decision, architecture §12 debt item,
scoreboard interpretation (axiom count stays 18 until the compatibility
window closes). Bonus hygiene: the derived module's use of Mathlib's
deprecated `div_lt_div_iff` upgraded to `div_lt_div_iff₀`.

**Decisive commands and outcomes:** `lake build` on
`Scaffold.Mathlib.GraphTheory.Dynamics`,
`Scaffold.QA.SpectralGraph.Dynamics_QA`, and
`Scaffold.Derived.ProjectorDrift` pass; full `lake build` passes with
zero deprecation warnings; all four hygiene scripts pass.

**Verification:** 96 QA declarations, zero `sorry`/`admit` under
`Scaffold/`; 18 explicit cited axioms (unchanged — deprecation, not
removal).

**Trust boundary:** effectively reduced by one admitted-but-unconsumed
statement; formally unchanged until the compatibility window closes and
the axiom is removed in a permitted release.

**Remaining risk:** none new; the migration note must be revisited at
the removal release.

**Next handoff:** backlog item 3 — expansion and cut interfaces
(edge-boundary and uniform-weight conductance variants), each admitted
only with a named algorithm consumer.

## 2026-08-17T20:53:04Z — Cut duality (hard crust)

**Run:** `20260817T205021Z-run-10`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Backlog item 3, first slice: the cut-duality structural
facts (volume complementarity, boundary and conductance invariance under
complementation, degenerate-cut guards) as proved statements in the SGT
center. No axioms — the Cheeger inequalities remain the admitted
boundary.

Named consumers: spectral-partitioning sweep cuts and sparsest-cut
statement shapes (backlog items 3–4) both assume cuts are
partition-valued (invariant under choosing the other side); the Cheeger
minimizer canonicalization consumes conductance invariance.

## 2026-08-17T21:01:11Z — Cut duality delivered (backlog item 3, first slice)

**Run:** `20260817T205021Z-run-10`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Backlog item 3, first slice: the cut-duality structural
facts in the SGT center — a cut is a property of the partition, not the
chosen side. Pure hard crust, no new axioms; the Cheeger inequalities
remain the admitted boundary.

**Changes:** in `GraphTheory.Spectral`: `vol_compl` (volume
complementarity via `Finset.sum_add_sum_compl`),
`boundary_compl` (boundary invariance under complementation for
symmetric weights, via `Finset.sum_comm` + `IsSymm`),
`conductance_compl` (conductance invariance — the Cheeger minimizer can
be canonicalized to either side, the interface sweep-cut consumers
require), `boundary_empty` / `boundary_univ` (degenerate-cut guards).
New QA `SpectralGraph/Cuts_QA.lean` (11 declarations) at the 3-vertex
path: degrees (1,2,1), the singleton cut's boundary computing to `1`
via row-sum-minus-diagonal, duality and conductance invariance
instantiated, total volume `4`, guards evaluated. SGT index map,
backlog item 3 "Have" list, scoreboard, and README updated.

**Decisive commands and outcomes:** direct builds of
`Scaffold.Mathlib.GraphTheory.Spectral` and
`Scaffold.QA.SpectralGraph.Cuts_QA` pass; full `lake build` passes with
zero deprecation warnings; all four hygiene scripts pass.

**Verification:** 107 QA declarations (up from 96), zero `sorry`/`admit`
under `Scaffold/`, 18 explicit cited axioms (unchanged).

**Trust boundary:** unchanged; hard crust only.

**Remaining risk:** none new. Backlog item 3's further variants
(edge-boundary and uniform-weight conductance) remain gated on named
algorithm consumers.

**Next handoff:** remaining backlog item 3 variants with named
consumers, or the backlog item 4 gating review (spectral algorithms).

## 2026-08-17T21:09:41Z — SGT coverage radar (operator direction)

**Run:** `20260817T210736Z-run-1`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Deliver the operator-directed coverage assessment from
`cdx-sgt-radar-axes.md`: two radars — eight subject axes and a separate
assurance-quality radar — scored by usable, verified coverage rather
than declaration count, each score justified by named declarations with
their proved/admitted/absent status.

Method: evidence-first scoring against the current tree (18 explicit
axioms, 107 QA declarations, proved/admitted status per module); the
weakest axes feed the backlog (subject axis 6 — combinatorial and
electrical structure — is entirely absent; assurance-side downstream
reuse is weakest since RandomWalk/Normalized lack consumers). Deliverable
`docs/7_SGT_RADAR.md` plus backlog/README integration; no Lean changes,
verification via the doc-hygiene suite.

## 2026-08-17T21:11:09Z — SGT coverage radar delivered

**Run:** `20260817T210736Z-run-1`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Deliver the operator-directed coverage assessment
(`cdx-sgt-radar-axes.md`): two radars — eight subject axes and a
separate assurance-quality radar — scored by usable, verified coverage,
each score justified by named declarations with proved/admitted/absent
status.

**Changes:** new `docs/7_SGT_RADAR.md` (linked from the README
canonical-docs list): subject scores — models 2.5, spectral algebra 3.5,
variational 2.5, cuts/expansion 2.5, walks 2.5, electrical 0.5,
perturbation/randomness 3.0, adjacent systems 1.0; assurance scores —
proved depth 3.5, axiom minimization 3.5 (26 → 19 → 18 trend),
Mathlib interop 3.5, QA 3.0 (skews degenerate-case), citation fidelity
3.5, downstream reuse 2.5 (RandomWalk/Normalized unconsumed). Includes
weakest-axis findings and a re-scoring protocol (scores move only with
usable, verified coverage, recorded with the causing milestone).
Backlog: new gated candidate item 7 (combinatorial/electrical structure
— axis entirely absent, admission deferred until a named consumer
states the identity it needs) and a downstream-reuse standing decision.
No Lean changes.

**Decisive commands and outcomes:** axiom inventory re-verified by grep
(18 explicit, including the deprecated one) before scoring;
`generate_qa_scoreboard.py`, `lint_axioms.py`, `check_citations.py`,
`check_markdown_links.py` all pass; scoreboard metrics unchanged (107
QA declarations, 0 `sorry`/`admit`).

**Verification:** doc-only change; every score's cited declarations
exist in the current tree.

**Trust boundary:** unchanged; the radar explicitly labels which
neighborhoods rest on admitted statements.

**Remaining risk:** scores are judgment calls over cited evidence; the
re-scoring protocol constrains drift, and milestone entries must record
future changes.

**Next handoff:** radar-driven next milestone — the first downstream
consumer for the walk/normalized interfaces (weakest assurance axis),
or remaining backlog item 3 variants with named consumers.

## 2026-08-17T21:13:57Z — Stationary structure (first walk/normalized consumer)

**Run:** `20260817T211135Z-run-2`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Close the radar's weakest assurance axis (downstream
reuse): the first module consuming the `RandomWalk`/`Normalized`
interfaces — the stationary-structure theorems, proved from the bridge
lemmas. No new axioms.

Content: `L_sym *ᵥ √deg = 0` (kernel of the general normalized
Laplacian) and `Pᵀ *ᵥ deg = deg` (the degree measure is stationary for
the walk — `π ∝ deg` is the stationary distribution, the Markov-mixing
consumer interface). Both reduce to the diagonal algebra plus
`A *ᵥ 1 = deg`.

## 2026-08-17T21:16:50Z — Stationary structure delivered (reuse gap closing)

**Run:** `20260817T211135Z-run-2`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Close the radar's weakest assurance axis (downstream
reuse): `Scaffold.Mathlib.GraphTheory.Stationary`, the first module
consuming the walk/normalized interfaces. Pure hard crust, no new
axioms.

**Changes:** new `GraphTheory.Stationary` (imports `Normalized`):
`mulVec_one_eq_deg` (`A *ᵥ 1 = deg`, row sums in vector form),
`normalizedLaplacian_mulVec_sqrtDeg_eq_zero` (kernel of the general
normalized Laplacian is `√deg` — the normalized counterpart of the
combinatorial `laplacian_ones_in_kernel`, proved through the
`degreeInvSqrt` diagonal algebra), and
`walkTransitionMatrix_transpose_mulVec_deg` (`Pᵀ *ᵥ deg = deg`: the
degree measure is stationary for the walk, i.e. `π ∝ deg` — the named
Markov-mixing consumer interface). New QA
`SpectralGraph/Stationary_QA.lean` (6 declarations) at the 3-vertex
path, including a fully computed center kernel entry. Umbrella, SGT
index map, scoreboard, and README updated. SGT radar downstream-reuse
score re-scored 2.5 → 3.0 with the causing milestone recorded per the
radar's protocol; backlog standing decision updated (remaining reuse
gap: `RandomWalk`'s regular-case bridges).

**Decisive commands and outcomes:** direct builds of
`Scaffold.Mathlib.GraphTheory.Stationary` and
`Scaffold.QA.SpectralGraph.Stationary_QA` pass; full `lake build`
passes; all four hygiene scripts pass.

**Verification:** 116 QA declarations (up from 107), zero `sorry`/`admit`
under `Scaffold/`, 18 explicit cited axioms (unchanged).

**Trust boundary:** unchanged; hard crust only.

**Remaining risk:** none new; `RandomWalk`'s regular bridges remain
unconsumed outside QA (noted in backlog standing decisions).

**Next handoff:** a consumer for `RandomWalk`'s regular bridges (e.g. a
regular-graph Cheeger consequence restated through the walk view), or
remaining backlog item 3 variants with named consumers.

## 2026-08-17T21:19:52Z — Walk-Laplacian kernel (RandomWalk consumer)

**Run:** `20260817T211717Z-run-3`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Close the remaining reuse gap: make `Stationary` the
demonstrated consumer of `RandomWalk` as well as `Normalized`, via the
walk-Laplacian kernel facts `(I − P) *ᵥ 1 = 0` (regular and irregular
variants) — conservation of mass, the base statement of diffusion and
mixing arguments.

Scoping evidence: the heavier spectral-transfer consumer
(`evals (c • M) = c • evals M`) requires excavation through Mathlib's
`irreducible_def` eigenspace decomposition; recorded as a named backlog
candidate rather than attempted speculatively.

## 2026-08-17T21:22:27Z — RandomWalk consumer delivered; reuse axis closed

**Run:** `20260817T211717Z-run-3`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Close the remaining downstream-reuse gap:
`GraphTheory.Stationary` extended to consume `RandomWalk` in addition
to `Normalized`, via the walk-Laplacian kernel (conservation-of-mass)
facts. Pure hard crust, no new axioms.

**Changes:** `Stationary` now imports `RandomWalk` and proves
`randomWalkLaplacian_mulVec_one_eq_zero` (regular case; consumes
`RandomWalk.transitionMatrix_row_sum`) and
`walkLaplacian_mulVec_one_eq_zero` (irregular case; consumes
`Normalized.walkTransitionMatrix_row_sum`) — both the statement
`(I − P) *ᵥ 1 = 0`, total probability preserved by each walk step.
QA extended (119 declarations total): the irregular path and the
regular edge instantiate the two variants. Radar: downstream reuse
re-scored 3.0 → 3.5 (recorded per protocol); the weakest assurance
axis is now QA depth (3.0, degenerate-case skew). Backlog records the
named future consumer candidate (`evals (c • M) = c • evals M`,
gated on Mathlib's `irreducible_def` eigenspace excavation). SGT index
map, scoreboard, and README updated.

**Decisive commands and outcomes:** direct builds of
`Scaffold.Mathlib.GraphTheory.Stationary` and
`Scaffold.QA.SpectralGraph.Stationary_QA` pass; full `lake build`
passes; all four hygiene scripts pass.

**Verification:** 119 QA declarations (up from 116), zero `sorry`/`admit`
under `Scaffold/`, 18 explicit cited axioms (unchanged).

**Trust boundary:** unchanged; hard crust only.

**Remaining risk:** `Stationary` is the sole consumer of both interface
modules — breadth of reuse is the new constraint, not existence.

**Next handoff:** breadth consumers (second consuming module, e.g.
variational Rayleigh bounds through the congruence bridge), the QA
assurance lever (property-based/falsification QA), or backlog item 3
variants with named consumers.

## 2026-08-17T21:29:30Z — Exhaustive/falsification QA for the SGT center

**Run:** `20260817T212523Z-run-1`  
**Session:** `ses_fee6294b2ffembnC8DMWLp0fQN`  
**Status:** in-progress  
**Milestone:** Raise the weakest assurance axis (QA 3.0 — degenerate-case
skew, no property-based/negative QA) by delivering exhaustive,
kernel-checked-coverage sweeps over *all* cuts of two fixtures plus
negative witnesses, in a new QA module. Pure hard crust, no axiom
changes.

Scoping evidence: existing QA instantiates theorems at one or two cuts
and mostly applies the general theorem being tested (e.g.
`path_boundary_compl_QA` rewrites with `boundary_compl`), so a
self-consistent mis-definition would pass. Backlog item 3 variants are
gated on named consumers; reuse just re-scored to 3.5 — QA depth is the
named next assurance lever.

## 2026-08-17T21:48:42Z — Exhaustive/falsification QA delivered (QA axis 3.0 → 3.5)

**Run:** `20260817T212523Z-run-1`  
**Session:** `ses_fee6294b2ffembnC8DMWLp0fQN`  
**Status:** completed  
**Milestone:** Raise the weakest assurance axis (QA, 3.0 — degenerate-case
skew) by delivering `Scaffold/QA/SpectralGraph/Exhaustive_QA.lean`:
exhaustive, kernel-checked sweeps over all cuts of two fixtures, computed
from the definitions rather than by applying the general theorems, plus
negative witnesses. Pure hard crust, no axiom changes.

**Changes:** 87 new QA declarations (206 total across 18 modules).
(a) Coverage certificates `cuts3_eq`/`cuts4_eq`: the listed cuts are
exactly `Finset.univ.powerset` on `Fin 3`/`Fin 4`, decided by the kernel —
"exhaustive" is verified, not asserted. (b) Boundary and volume tables
for every cut of the 3-vertex path and the 4-cycle, each entry evaluated
from `boundary`/`vol`/`conductance` on concrete data (`norm_num` on the
unfolded sums; no use of `boundary_compl`/`vol_compl` on the path from
definition to value). (c) Duality recomposed from the independently
computed tables (`exh_boundary_duality_QA`, `cyc_boundary_duality_QA`,
`exh_vol_complementarity_QA`). (d) Negative witnesses: conductance
separates adjacent-pair (`1/2`) from opposite-pair (`1`) cuts on the
cycle; Rayleigh separates `8/3` from `0` on the path; an asymmetric
two-vertex weight (`A 01 = 2`, `A 10 = 1`) shows `boundary_compl`'s
symmetry hypothesis is load-bearing (`2 ≠ 1`). (e) Walk row sums
computed per row, independently of `walkTransitionMatrix_row_sum`.
Radar QA axis re-scored 3.0 → 3.5 per protocol (stale 107/16 evidence
count refreshed to the current tree); execution plan and scoreboard
updated.

**Decisive commands and outcomes:** `lake env lean` on the module
(zero output — clean elaboration); `lake build
Scaffold.QA.SpectralGraph.Exhaustive_QA` ✔; full `lake build` ✔;
`lint_axioms`, `check_citations`, `check_markdown_links` all pass;
`generate_qa_scoreboard` regenerated (206 declarations, 0 placeholders).

**Verification:** all 87 new declarations compile with no
`sorry`/`admit`; 18 explicit cited axioms unchanged; umbrella build
unaffected (QA modules are leaf builds, built directly).

**Trust boundary:** unchanged; hard crust only. Implementation note
recorded: `degreeMatrix`'s diagonal conditional elaborates with a
classical `Decidable` instance (defined at generic `V`), so the Rayleigh
checks compose the proved Dirichlet identity and kernel theorem; the
checked values are still fully computed.

**Remaining risk:** no parametric (randomized) property QA and no
computational eigenvalue checks (Mathlib's spectral-theorem API is not
computable) — both named as the residual QA-depth gap on the radar.

**Next handoff:** breadth consumers (second consuming module for
walk/normalized, e.g. Rayleigh bounds through the congruence bridge),
the gated `evals (c • M) = c • evals M` excavation candidate, or
backlog item 3 variants once an algorithm consumer is named.

## 2026-08-17T21:51:19Z — Variational transfer (second interface consumer)

**Run:** `20260817T214929Z-run-2`  
**Session:** `ses_fee6294b2ffembnC8DMWLp0fQN`  
**Status:** in-progress  
**Milestone:** Deliver the open milestone's named breadth consumer:
`GraphTheory.VariationalTransfer`, the second consuming module for the
`Normalized`/`Spectral` interfaces — quadratic-form and Rayleigh-quotient
transfer through the proved congruence `√D L_sym √D = L`, plus PSD
transfer. Addresses the downstream-reuse axis's stated constraint
(`Stationary` is the sole consumer). Pure hard crust, no new axioms.

Scoping evidence: all required Mathlib pieces exist in the pinned
snapshot (`dotProduct_mulVec`, `mulVec_transpose`, `mulVec_diagonal`,
`mulVec_mulVec`, `one_mulVec`, `diagonal_transpose`); no name
collisions for the planned declarations.

## 2026-08-17T21:56:15Z — Variational transfer delivered (reuse axis 3.5 → 4.0)

**Run:** `20260817T214929Z-run-2`  
**Session:** `ses_fee6294b2ffembnC8DMWLp0fQN`  
**Status:** completed  
**Milestone:** Deliver the open milestone's named breadth consumer:
`Scaffold.Mathlib.GraphTheory.VariationalTransfer` — quadratic-form and
Rayleigh-quotient transfer between the combinatorial and normalized
Laplacians through the proved congruence `√D L_sym √D = L`, plus PSD
transfer. The second consuming module of the `Normalized`/`Spectral`
interfaces, addressing the reuse axis's stated constraint
("`Stationary` is the sole consumer"). Pure hard crust, no new axioms.

**Changes:** public module (7 proved declarations): `quadForm_congr`
(generic symmetric-congruence invariance of quadratic forms),
`degreeSqrt_isSymm`/`degreeSqrt_mulVec` (entrywise stretch),
`quadForm_laplacian_eq_quadForm_normalizedLaplacian` (Dirichlet-form
transfer), `dotProduct_degreeSqrt_mulVec` (degree-weighted
denominator), `degreeSqrt_mulVec_ne_zero`,
`rayleigh_normalizedLaplacian_degreeSqrt` — the headline
irregular-graph normalized Rayleigh quotient
`rayleigh L_sym (√D y) = (yᵀ L y) / ∑ deg i · y i²`, which the
regular-only Cheeger axioms cannot express — and
`normalizedLaplacian_psd` (PSD transferred from `laplacian_psd` by
un-stretching through `1/√D`). QA
`SpectralGraph/VariationalTransfer_QA.lean` (15 declarations at the
3-vertex path): entrywise stretch computes to `-√2`; the denominator
computes to `4` both through the lemma and as a bare sum; the headline
instantiates to the classical value `rayleigh L_sym (√D (1,-1,1)) =
8/4 = 2` — the largest eigenvalue of the normalized path Laplacian,
obtained without any spectral theorem (a defect in the congruence
bridge, stretch, or denominator lemma would move this value). Umbrella
import added; SGT index map gains the module section; radar re-scored
per protocol: downstream reuse 3.5 → 4.0 (two consuming modules),
subject axis 3 (variational) 2.5 → 3.0.

**Decisive commands and outcomes:** `lake env lean` on both files
(zero output after fixes — clean elaboration, zero warnings);
`lake build` of module and QA ✔; full `lake build` ✔ (1997 targets);
`lint_axioms`, `check_citations`, `check_markdown_links` pass;
scoreboard regenerated: 221 QA declarations, 0 placeholders, 18 axioms
unchanged.

**Verification:** all 7 public declarations proved from the center
(consumes `degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt`,
`degreeSqrt_mul_degreeInvSqrt`, `laplacian_psd`); Mathlib pieces used
(`dotProduct_mulVec`, `mulVec_transpose`, `mulVec_diagonal`,
`mulVec_mulVec`, `one_mulVec`, `diagonal_transpose`) all exist in the
pinned v4.14.0 snapshot.

**Trust boundary:** unchanged; hard crust only.

**Remaining risk:** no admitted-axiom consumer yet (Cheeger bounds
still regular-only); the transfer statement shapes are available for a
future irregular Cheeger family. `evals (c • M)` excavation still
gated.

**Next handoff:** the `evals (c • M) = c • evals M` Mathlib-excavation
candidate; an irregular Cheeger statement shape through
`rayleigh_normalizedLaplacian_degreeSqrt` (needs a precise source and
consumer); or backlog item 3 variants once an algorithm consumer is
named.

## 2026-08-18T02:10:53Z — Cheeger axiom statement-shape repair (in progress)

**Run:** `20260818T020953Z-run-1`  
**Session:** `ses_fed696611ffe0yiCxJU9cqgq3S`  
**Status:** in-progress  
**Milestone:** Repair a materially false statement shape at the admitted
boundary: both Cheeger axioms pass `regularNormalizedLaplacian A d` to
`lambda2`, which is `evals (laplacian ·) 1` — so the asserted spectral
quantity is `λ₂(L(L_sym)) = λ₂(-L_sym)`, not `λ₂(L_sym)`. On the
two-vertex edge the lower-bound instance reads `1/2 ≤ 0`, false; the
documented and cited intent is Chung Ch. 2's `φ²/2 ≤ λ₂(L_sym)`. Leverage:
the admitted Cheeger interface is the core of radar axis 4's admitted
half; a false admitted statement is an emergency-repair case
(architecture §9) and the top center-out priority.

Scoping evidence: `lambda2` consumers grep-verified (only `Cheeger.lean`
misuses it; `lambda2_variational` uses it correctly); Mathlib v4.14
provides the repair kit (`Matrix.IsHermitian.eigenvalues_eq` Rayleigh
form for the refutation bound; `det_eq_prod_eigenvalues`,
`Matrix.trace_mul_cycle`, `unitary.coe_star_mul_self`,
`Multiset.sort_eq`, `Finset.sum_eq_multiset_sum` for value pinning).
Plan: `secondEval` + `lambda2_eq_secondEval` + `eigvalOf_sum_eq_trace`
proved in the center; axioms restated at unchanged names/hypotheses with
corrected RHS; QA refutes the old shape, pins the corrected value
`λ₂(L_sym) = 2` on the edge, and re-instantiates coherence; dangling QA
reference `cheegerConstant_le_two_QA` in the upper-bound docstring fixed.

## 2026-08-18T02:54:12Z — Cheeger statement-shape repair delivered (QA 3.5 → 4.0)

**Run:** `20260818T020953Z-run-1`  
**Session:** `ses_fed696611ffe0yiCxJU9cqgq3S`  
**Status:** completed  
**Milestone:** Repair a materially false statement shape at the
admitted boundary: both Cheeger axioms passed
`regularNormalizedLaplacian A d` to `lambda2`, which is
`evals (laplacian ·) 1` — so the asserted spectral quantity was
`λ₂(L(L_sym)) = λ₂(-L_sym)`, not `λ₂(L_sym)`. On the two-vertex edge
the lower-bound instance reads `1/2 ≤ 0`, false; the documented and
cited intent is Chung Ch. 2's `φ²/2 ≤ λ₂(L_sym) ≤ 2φ`. Delivered as an
emergency repair (architecture §9) at unchanged names and hypotheses.

**Changes:** `GraphTheory.Spectral` gains five proved declarations:
`secondEval` (matrix-facing second sorted eigenvalue — the correct
spectral side for operators that are not adjacency matrices),
`lambda2_eq_secondEval` (adjacency-facing bridge),
`evals_mem_eigvalOf` (sorted-spectrum ↔ eigenbasis connection),
`eigvalOf_sum_eq_trace` (trace from the unitary diagonalization), and
`eigvalOf_le_of_quadForm_nonpos` (one-sided Rayleigh eigenvalue
bound). `GraphTheory.Cheeger` restates both axioms at
`secondEval (regularNormalizedLaplacian A d) …` with the correction
recorded in the docstrings. `Cheeger_QA.lean` (26 declarations, +19)
adds the `Fin 2` edge fixture (`edgeAdj`), the **proved refutation**
`old_cheeger_lower_bound_refuted_QA` (old instance on `K₂` implies
`1/2 ≤ 0` via the Rayleigh bound on `L(L_sym) = -L_sym` and
`cheegerConstant = 1`), the **value pinning**
`edge_normLap_secondEval_eq_two_QA` (`λ₂(L_sym) = 2`, computed from
trace + determinant + sortedness through `Multiset.sort_eq` — no
axiom, no spectral-theorem computation), `cheeger_bounds_edge_QA`
(the corrected sandwich on the fixture: `1/2 ≤ 2 ≤ 2`), and the
coherence lemmas at the corrected shape. Scoreboard, radar, SGT index
map, and Chung source index updated with the correction record.

**Decisive commands and outcomes:** `lake env lean` on Spectral,
Cheeger, and Cheeger_QA (zero output — clean elaboration, zero
warnings); `lake build Scaffold.Mathlib.GraphTheory.{Spectral,Cheeger}`
✔; all nineteen QA modules + the changed public modules built directly
✔; full `lake build` ✔ (2161 targets); `lint_axioms`,
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(240 QA declarations, 0 placeholders, 18 axioms unchanged).

**Verification:** the refutation and the value pinning are both proved
statements, conditional on no axiom; the corrected axioms' conclusions
are exercised on a fixture where the old and new shapes separate
numerically (`0` vs `2`). Consumers were grep-audited before the change:
only `Cheeger_QA.lean` used the axioms; `lambda2_variational` and all
other `lambda2` uses are correct and untouched.

**Trust boundary:** unchanged in size (18 explicit cited axioms); both
Cheeger axioms remain admitted and downstream use stays conditional on
them. The repair changes *what* is asserted, aligning the Lean
statement with the cited source; it is not a proof of the axioms.

**Remaining risk:** the corrected axioms are regular-graph statements;
the irregular Cheeger shape (through
`rayleigh_normalizedLaplacian_degreeSqrt`) remains open and needs a
precise source and consumer. Eigenvalue pinning is so far limited to
two-point fixtures; `evals (c • M)` excavation remains gated (though
the new trace/membership tools lower its cost).

**Next handoff:** the `evals (c • M) = c • evals M` excavation; an
irregular Cheeger statement shape with a named consumer; or backlog
item 3 variants with named algorithm consumers.

## 2026-08-18T03:18:31Z — Electrical-crust step 1: connectivity/kernel characterization (in progress)

**Run:** `20260818T031831Z-run-1`  
**Session:** `ses_fed249ea1ffeNPR0xYcQVtoj2z`  
**Status:** in-progress  
**Milestone:** Operator-directed: `proposals/electrical-structure-crust.md`
step 1 ONLY — prove the converse of `laplacian_ones_in_kernel`: for a
connected weighted graph, `ker (laplacian A)` is exactly the constants.
Pure hard crust, no new axioms; obstruction goes to
`docs/6_SGT_BACKLOG.md` if unprovable. Proposal steps 2–5 (effective
resistance, Rayleigh monotonicity, Foster) out of scope.

**Pre-edit decision (recorded in the execution plan):** connectivity is
adopted as Mathlib `SimpleGraph.Connected` via a `WAdj → SimpleGraph`
adapter `supportGraph A hA` (`Adj i j ↔ i ≠ j ∧ 0 < A i j`; looplessness
forces the conjunct, and positive diagonal self-loops cancel in `D − A`).
Rationale: reuses Mathlib's walk induction for propagation, the
`Connected` field `Nonempty` discharges the empty-type case, avoids
duplicating `Walk`/`Reachable`, and creates the first WAdj→SimpleGraph
bridge (the radar's standing interop deviation). Cost: two new Mathlib
imports in `Spectral.lean`, mitigated by the `supportGraph_adj`
interface lemma.

**Planned proof path:** kernel vector ⇒ zero quadratic form ⇒ termwise
`(f i − f j)² = 0` on positive weights (via `laplacian_quadForm` +
nonneg weights) ⇒ `f` constant along support-graph walks ⇒ constant on
`V` by connectivity; then assemble
`ker (mulVecLin (laplacian A)) = span ℝ {onesVec}`. QA with connected
positive witness (3-path) and disconnected negative witness
(two-component `Fin 4` graph: component indicator in kernel, not
constant).

## 2026-08-18T03:38:08Z — Electrical-crust step 1 delivered: kernel = constants on connected graphs (completed)

**Run:** `20260818T031831Z-run-1`  
**Session:** `ses_fed249ea1ffeNPR0xYcQVtoj2z`  
**Status:** completed  
**Milestone:** `proposals/electrical-structure-crust.md` step 1 ONLY —
the converse of `laplacian_ones_in_kernel`: for symmetric nonnegative
weights whose support graph is connected, `ker (laplacian A)` is
exactly the constants. Delivered as pure hard crust; **no new axioms**
(explicit axiom count unchanged at 18). Proposal steps 2–5 untouched.

**Changes:** `GraphTheory.Spectral` (new section 5; sections 5–6
renumbered to 6–7; two Mathlib imports added:
`Combinatorics.SimpleGraph.Path`, `LinearAlgebra.Matrix.ToLin`): the
`supportGraph` adapter (`WAdj → SimpleGraph`, `Adj i j ↔ i ≠ j ∧
0 < A i j`; the `i ≠ j` conjunct is forced by looplessness — positive
diagonal self-loops cancel in `D − A`) with interface lemma
`supportGraph_adj`; `eq_of_laplacian_mulVec_eq_zero_of_pos_weight`
(zero Dirichlet energy ⇒ `(f i − f j)² = 0` termwise on positive
weights, via `laplacian_quadForm` + `Finset.sum_eq_zero_iff_of_nonneg`);
`eq_of_supportGraph_walk` (propagation by induction on
`SimpleGraph.Walk`); `exists_const_of_laplacian_mulVec_eq_zero` (anchor
vertex from `Connected`'s bundled `Nonempty`; value propagated along
walks); `laplacian_mulVec_const`; iff form
`laplacian_mulVec_eq_zero_iff_exists_const`; headline span form
`laplacian_kernel_eq_span_onesVec`
(`ker (mulVecLin (laplacian A)) = span ℝ {onesVec}` — the shape
effective-resistance uniqueness will consume). New QA
`SpectralGraph/Connectivity_QA.lean` (15 declarations): connected
witness at the 3-vertex path (connectivity by explicit walks through
the center; both iff directions; constant recovered and pinned to `5`;
non-constant `![1,0,0]` computed out of the kernel entrywise) and
disconnected negative witness at two disjoint `Fin 4` edges (component
indicator `![1,1,0,0]` computed into the kernel yet not constant;
support graph proved not connected via a walk block invariant) — the
connectivity hypothesis is load-bearing. Docs: backlog item 7 records
step 1 delivered with named step-2 consumers; SGT index map, scoreboard
(static counts + verification record + interpretation bullet) updated;
radar re-scored per protocol (see below).

**Decisive commands and outcomes:** `lake env lean` on
`GraphTheory.Spectral` — zero errors, zero new warnings (six
pre-existing linter notes in untouched code); `lake env lean` on
`QA.SpectralGraph.Connectivity_QA` — zero output; `lake build Scaffold
.QA.SpectralGraph.Connectivity_QA` ✔ (2009 targets); full `lake build`
✔ (2171 targets); `lint_axioms`, `check_citations`,
`check_markdown_links` pass; scoreboard regenerated: 255 QA
declarations (+15), 0 placeholders, 18 axioms unchanged.

**Verification:** every new declaration is a Lean-checked theorem
conditional on no Scaffold axiom; QA includes both the connected
positive witness and the disconnected negative witness the direction
required. Radar re-scored only after proof + QA landed, per protocol:
subject axis 6 (electrical) 0.5 → 1.0 (connectivity hinge proved; no
electrical quantity defined yet), subject axis 1 (models) 2.5 → 3.0
(first `SimpleGraph` adapter), assurance Mathlib interop 3.5 → 4.0
(the matrix-first deviation is bridged one direction and genuinely
consumed by the center theorem). The README coverage snapshot's two
affected cells were synced to the radar (the snapshot was added
concurrently during this run; its other content untouched).

**Trust boundary:** unchanged in size (18 explicit cited axioms); this
slice added no axioms and consumes none.

**Remaining risk:** `supportGraph` is one-directional (`toWAdj` still
open); the span theorem's `hconn` hypothesis is phrased through the
adapter, so future refactors of that definition touch consumers (the
`supportGraph_adj` lemma is the stable interface). Concurrent operator
edits during this run (README snapshot, proposal re-sequencing,
`cdx-sgt-radar-axes.md` deletion) were preserved untouched except the
two README score cells synced above.

**Next handoff:** proposal step 2 — effective resistance by the
potential equation (`IsEffectiveResistance A u v r ↔ ∃ f,
laplacian A *ᵥ f = e u − e v ∧ f u − f v = r`), whose
well-definedness consumes `laplacian_kernel_eq_span_onesVec`; or the
open earlier candidates (`evals (c • M)` excavation; irregular Cheeger
shape; backlog item 3 variants).

## 2026-08-18T04:27:41Z — SimpleGraph→WAdj interoperability adapter (in progress)

**Run:** `20260818T042204Z-run-1`  
**Session:** `ses_fece519a1ffeRIOcnxA00ZWV1f`  
**Status:** in-progress  
**Milestone:** `proposals/electrical-structure-crust.md` step 1 under the
2026-08-18 re-sequenced numbering — deliver `SimpleGraph.toWAdj`, the
`SimpleGraph → WAdj` adapter the proposal calls "the highest compounding
multiplier available". SGT leverage: converts every proved Scaffold
theorem into something callable on Mathlib `SimpleGraph` objects,
completes the two-directional adapter surface begun with `supportGraph`,
and folds in the neutral re-export of Mathlib's unweighted
kernel/component results. Pure hard crust, no new axioms; one step per
run (steps 2–6 untouched).

**Scope note:** the previous run's operator direction predated the
proposal re-sequencing; effective resistance is now step 5 and gated
behind step 4 (solvability), so the plan's earlier "next: effective
resistance" handoff is superseded by this step-1 delivery.

**Planned:** new module `GraphTheory/SimpleGraphAdapter` with
`toWAdj G = G.adjMatrix ℝ`, proved agreement (`toWAdj_symm`,
`toWAdj_nonneg`, `deg_toWAdj`, `vol_toWAdj` + handshake,
`laplacian G.toWAdj = G.lapMatrix ℝ`, boundary as crossing-edge count),
roundtrip `supportGraph (toWAdj G) = G`, connected-`G` kernel corollary,
and the two Mathlib re-exports (kernel/reachable iff, component-count
finrank). QA at the 3-vertex path plus the two-edge `Fin 4` negative
witness (component indicator in kernel but outside `span {onesVec}`).

## 2026-08-18T06:13:31Z — SimpleGraph→WAdj interoperability adapter delivered (completed)

**Run:** `20260818T042204Z-run-1`  
**Session:** `ses_fece519a1ffeRIOcnxA00ZWV1f`  
**Status:** completed  
**Milestone:** `proposals/electrical-structure-crust.md` step 1 under
the 2026-08-18 re-sequenced numbering — `SimpleGraph.toWAdj`, the
`SimpleGraph → WAdj` adapter, completing the two-directional Mathlib
bridge begun with `supportGraph`. Pure hard crust; **no new axioms**
(explicit count unchanged at 18). One step per the proposal's operating
instructions; steps 3–6 untouched.

**Changes:** new `Scaffold/Mathlib/GraphTheory/SimpleGraphAdapter.lean`
(16 declarations, all proved): `SimpleGraph.toWAdj` (deliberately
defined as Mathlib's `adjMatrix ℝ` so no parallel matrix construction
can drift out of agreement) with interface lemma `toWAdj_apply`;
`toWAdj_symm`, `toWAdj_nonneg` (0/1 weights discharge every `hnonneg`
hypothesis of the center); agreement family `deg_toWAdj` (via
`degree_eq_sum_if_adj`), `vol_toWAdj_eq_sum_degrees`, handshake
`vol_toWAdj_univ_eq_two_mul_card_edges` (Mathlib's
`sum_degrees_eq_twice_card_edges` transferred), headline
`laplacian G.toWAdj = G.lapMatrix ℝ`, boundary as the crossing-edge
count (`boundary_toWAdj_eq_sum_neighbors`,
`boundary_toWAdj_eq_sum_card_neighbors` — each crossing edge counted
exactly once); neutral re-exports `laplacian_toWAdj_mulVec_eq_zero_iff_reachable`
and `finrank_ker_laplacian_toWAdj` (Mathlib's unweighted kernel and
component-count results transferred by one-two rewrites); roundtrip
`supportGraph_toWAdj_eq_self`; connected-`G` corollary
`laplacian_toWAdj_kernel_eq_span_ones` (the delivered span theorem
applied to Mathlib graphs through the roundtrip). New QA
`SpectralGraph/SimpleGraphAdapter_QA.lean` (38 declarations): 3-vertex
path `SimpleGraph` fixture with weights, degrees (1,2,1), Laplacian
entries, *both* Laplacian sides, boundary `{1} = 2`, volume `4`,
handshake `4 = 2·2`, kernel span/iff instances, constant-in-kernel
pinned to `5`, and `![1,0,0]` computed out of the kernel entrywise;
disconnected `Fin 4` negative witness with the component indicator
computed into the kernel, not constant, outside `span {onesVec}`, and
the kernel proved ≠ `span {onesVec}` — connectivity load-bearing
through the adapter. Umbrella, SGT index map, scoreboard, backlog
item 7, radar, README updated.

**Decisive commands and outcomes:** environment repair first — the
local `.lake/build` was found pruned (Mathlib oleans 1795/5685, all
modules this slice needs missing); re-ran the recorded interpreter
cache fetch (`lake env lean --run Cache/Main.lean get` from the
mathlib package root: 5685 files, 100% success), then `lake build
Scaffold.Mathlib.GraphTheory.Spectral` recompiled the 2008-target
residue to completion. `lake env lean` on the new public module —
zero errors/warnings after fixes (named-argument forms for
`isSymm_adjMatrix`/`degree_eq_sum_if_adj`, cast bookkeeping in the
card-form boundary, `omit`s for unused section variables); `lake env
lean` on the new QA module — zero output; `lake build` of both targets
✔; full `lake build` ✔ (2177 targets); all 21 QA modules built
directly in one batch (exit 0); `lint_axioms`, `check_citations`,
`check_markdown_links` pass; scoreboard regenerated: 293 QA
declarations (+38), 0 placeholders, 18 axioms unchanged.

**Verification:** every new declaration is a Lean-checked theorem
conditional on no Scaffold axiom; the QA computes adapter values from
the definitions (not by rewriting with the agreement theorems), per
the falsification-QA standard, and includes both the connected
positive witness and the disconnected negative witness the step
required. Radar re-scored only after proof + QA landed, per protocol:
Mathlib interop 4.0 → 4.5 (both directions tied by a proved roundtrip;
Mathlib kernel/component results transferred; remaining deviation only
`MatrixMDS`/filtration), subject axis 1 (models) 3.0 → 3.5; QA axis
text updated to 293 declarations / 21 modules (score unchanged). README
coverage-snapshot cell and maturity bullet synced.

**Trust boundary:** unchanged in size (18 explicit cited axioms); this
slice added no axioms and consumes none.

**Remaining risk:** the component-count transfer covers only 0/1
weights (`finrank_ker_laplacian_toWAdj` is about `toWAdj G`) — the
weighted generalization is exactly proposal step 3
(`ker (laplacian A) = ker ((supportGraph A).lapMatrix ℝ)`); `toWAdj`
QA fixtures are small graphs only (no parametric QA — standing QA-axis
gap). Concurrent operator edits in the tree (AGENTS.md, strategy
revision, new proposals `get-outside-signal.md`,
`prove-lambda2-variational.md`, `sell-the-methodology.md`, untracked
coverage map) were preserved untouched.

**Next handoff:** proposal step 3 — the kernel-equality bridge for
weighted graphs, inheriting Mathlib's `lapMatrix_ker_basis` and
`card_ConnectedComponent_eq_rank_ker_lapMatrix`; then step 4
(potential solvability — the hinge; resistance is forbidden before it
lands). Or the open earlier candidates: `evals (c • M)` excavation;
irregular Cheeger shape with a named consumer; backlog item 3
variants.

## 2026-08-18T06:23:17Z — Electrical-crust step 3: kernel-equality bridge (in progress)

**Run:** `20260818T061620Z-run-1`
**Session:** `ses_fec7cb0f5ffe66xyhhSJgVZ1IY`
**Status:** in-progress
**Milestone:** Operator direction: advance
`proposals/electrical-structure-crust.md` **step 3 only** — prove the
kernel-equality bridge `ker (laplacian A) = ker ((supportGraph
A).lapMatrix ℝ)` and inherit Mathlib's component-indexed kernel facts
(`lapMatrix_ker_basis`, `card_ConnectedComponent_eq_rank_ker_lapMatrix`)
for the weighted Laplacian; one step per run, no new axioms, step 4 out
of scope.

**Pre-implementation survey (recorded):** pinned Mathlib
`LapMatrix.lean` provides the unweighted kernel/rank/basis family;
`Matrix.toLin'_apply'` (ToLin.lean:310) identifies `toLin' M` with
`mulVecLin M`; `Real.decidableLT` (noncomputable, Real/Basic.lean:539)
makes `DecidableRel (supportGraph A hA).Adj` elaborable for free;
`SimpleGraph.Adj.reachable` (Path.lean:664) converts adjacency to
reachability. The bridge's weighted side needs one new center fact —
the no-connectivity characterization `L *ᵥ f = 0 ↔ f constant on
support-graph components` (step 2 delivered only the connected case);
direction "component-constant ⇒ kernel" is new and goes entrywise
through a diffusion-form identity for `(L *ᵥ f) i`.

**Next action:** implement (a) center lemmas in `Spectral.lean`, (b)
bridge + transfers in `SimpleGraphAdapter.lean`, (c) QA
`SpectralGraph/KernelBridge_QA.lean` on the `Connectivity_QA`
fixtures, then verify by direct elaboration and full build.

## 2026-08-18T06:45:01Z — Electrical-crust step 3 delivered: kernel-equality bridge (completed)

**Run:** `20260818T061620Z-run-1`
**Session:** `ses_fec7cb0f5ffe66xyhhSJgVZ1IY`
**Status:** completed
**Milestone:** Operator direction "advance
`proposals/electrical-structure-crust.md`, step 3 only" — the
kernel-equality bridge and the inherited Mathlib component facts for
the weighted Laplacian. One step per run; step 4 (potential
solvability) was not started, per the proposal's scope fence.

**Changes.** Center (`Scaffold/Mathlib/GraphTheory/Spectral.lean`):
`laplacian_mulVec_apply` (diffusion-form entrywise action; self-loops
cancel), `laplacian_mulVec_eq_zero_of_forall_reachable`
(component-constant ⇒ kernel, entrywise, no connectivity hypothesis),
`laplacian_mulVec_eq_zero_iff_forall_reachable` (component-form
characterization — the weighted counterpart of Mathlib's unweighted
iff). Bridge (`GraphTheory/SimpleGraphAdapter.lean`):
`supportGraphAdjDecidable` (decidability prerequisite for Mathlib's
`lapMatrix` API, invisible through the `supportGraph` projection;
`Real.decidableLT`), the headline `ker_laplacian_eq_ker_
supportGraph_lapMatrix` (`ker (laplacian A) = ker ((supportGraph
A).lapMatrix ℝ)`), `finrank_ker_laplacian_eq_card_supportGraph_
components` (kernel dimension = component count for weighted graphs),
and the transported component-indicator basis `laplacian_ker_basis` /
`laplacian_ker_basis_apply`. New QA
`Scaffold/QA/SpectralGraph/KernelBridge_QA.lean` (14 declarations)
reusing the `Connectivity_QA` fixtures. Docs: execution plan, this
journal, backlog item 7, radar (subject axis 6 re-scored 1.0 → 1.5
per protocol; QA-axis counts updated to 307/22), proposal checklist
marked step 3 delivered with a delivery note (including the recorded
decidability prerequisite), scoreboard (regenerated + verification
rows and a dated provenance note), SGT index map.

**Verification.** `lake env lean` zero errors/zero warnings on
`SimpleGraphAdapter` and `KernelBridge_QA`; zero errors on `Spectral`
(no new warnings — the six pre-existing linter notes untouched);
`lake build Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter` ✔; full
`lake build` ✔ (2177 targets); all twenty-two QA modules elaborated
directly in one batch (zero failures); no `sorry`/`admit` under
`Scaffold/`; `lint_axioms`, `check_citations`, `check_markdown_links`
pass; scoreboard regenerated (307 QA declarations, 18 explicit
axioms — unchanged; the slice is pure hard crust).

**Trust boundary:** unchanged (18 explicit cited axioms); this slice
added no axioms and consumes none. The inherited basis/count facts are
Mathlib theorems transferred through a proved bridge, not new trust.

**Remaining risk.** The transported `laplacian_ker_basis` requires a
`DecidableEq ConnectedComponent` instance at use sites (classical
suffices; QA uses it without incident). The QA fixtures are small
graphs only — no parametric property QA (standing QA-axis gap). The
bridge inherits Mathlib's component *count/basis* but not any
electrical quantity: solvability (step 4) is still open, and the
proposal forbids defining effective resistance before it lands.

**Next handoff:** proposal step 4 — potential solvability for
zero-sum demand (`∃ f, L *ᵥ f = b` when `∑ b = 0`; specialize to
`b = e u − e v`), recording the route decision (orthogonality vs
constructive eigenbasis) before stating; then step 5 (resistance
uniqueness, consuming `laplacian_kernel_eq_span_onesVec`). Or the
open earlier candidates: `evals (c • M)` excavation; irregular
Cheeger shape with a named consumer; backlog item 3 variants.

## 2026-08-18T07:01:06Z — Electrical-crust step 4 started: potential solvability

**Run:** `20260818T070106Z-run-1`
**Session:** `ses_fec5a1003ffeuJmMzrd6DtYfoa`
**Status:** in-progress
**Milestone:** Operator direction "advance
`proposals/electrical-structure-crust.md`, step 4 only" — the potential
solvability hinge (`∃ f, laplacian A *ᵥ f = b` for zero-sum `b` on a
connected graph), which the proposal gates ahead of any definition of
effective resistance.

**Pre-implementation survey and route decision (recorded before
stating):** constructive eigenbasis route chosen over the orthogonality
route. The pin has no ready-made `range = (ker)ᗮ` lemma for the
function-type spaces the center uses (targeted search over
`Analysis/InnerProductSpace/` this run; same finding as the proposal's
own survey), while the center already proves orthonormality
(`eigvecOf_inner`), completeness (`eigvecOf_complete`), the eigenvector
equation (`mulVec_eigenvectorBasis`), and the kernel span theorem
(`laplacian_kernel_eq_span_onesVec`, proposal step 2). The witness
`f = ∑_{λᵢ ≠ 0} (vᵢ ⬝ᵥ b / λᵢ) • vᵢ` consumes all of them, making the
solvability theorem load-bearing on the step-2 kernel shape exactly as
the strategy's falsifiability principle asks. Supporting lemma: the
reciprocity identity `w ⬝ᵥ (L *ᵥ f) = (L *ᵥ w) ⬝ᵥ f`
(`Matrix.dotProduct_mulVec` + Laplacian symmetry).

**Next action:** center block in `GraphTheory.Spectral` (reciprocity,
kernel corollary, main existence theorem, unit-demand specialization),
QA `SpectralGraph/PotentialSolvability_QA.lean` with positive and both
negative witnesses (non-zero-sum unsolvable on a connected fixture;
zero-sum unsolvable on the disconnected fixture), then direct
elaboration, target builds, full build, hygiene scripts, scoreboard.

## 2026-08-18T07:27:05Z — Electrical-crust step 4 delivered: potential solvability (completed)

**Run:** `20260818T070106Z-run-1`
**Session:** `ses_fec5a1003ffeuJmMzrd6DtYfoa`
**Status:** completed
**Milestone:** Operator direction "advance
`proposals/electrical-structure-crust.md`, step 4 only" — the potential
solvability hinge: on a connected graph (symmetric, nonnegative
weights), every zero-sum demand `b` admits a potential `f` with
`laplacian A *ᵥ f = b`, specialized to the unit demand `e u − e v`.
One step per run; step 5 (effective resistance) was not started, per
the proposal's scope fence — the proposal forbids defining resistance
before this hinge lands, and it now has.

**Route decision (executed as recorded before stating).** Constructive
eigenbasis: witness `f = ∑_{λᵢ ≠ 0} (vᵢ ⬝ᵥ b / λᵢ) • vᵢ`. The pin
(re-surveyed) still lacks a ready-made `range = (ker)ᗮ` lemma for the
center's function-type spaces, while the route consumes the proved
eigenbasis algebra and the step-2 kernel theorem — load-bearing on
both, per the strategy's falsifiability principle.

**Changes.** Center (`Scaffold/Mathlib/GraphTheory/Spectral.lean`):
`laplacian_dotProduct_mulVec` (reciprocity / discrete Green identity),
`dotProduct_eq_zero_of_laplacian_mulVec_eq_zero` (kernel vectors
certify unsolvability), `mulVec_eigvecOf_sum_apply` (entrywise action
on eigenbasis combinations), `exists_mulVec_eq_of_zero_comp`
(constructive spectral inversion), `exists_laplacian_mulVec_eq_of_sum_
eq_zero` (the hinge), `exists_laplacian_mulVec_eq_single_sub_single`
(unit demand; step 5's defining equation). New QA
`Scaffold/QA/SpectralGraph/PotentialSolvability_QA.lean` (12
declarations): edge fixture + `Connectivity_QA` fixtures; computed
potentials `![1,0]` and `![1,0,−1]`; theorem instantiations; proved
*unsolvability* witnesses for both hypotheses (non-zero-sum `e₀` on
the connected edge via the all-ones certificate; zero-sum
cross-component `e₀ − e₂` on the disconnected fixture via the
component-indicator certificate). Docs: execution plan, this journal,
backlog item 7, radar (subject axis 6 re-scored 1.5 → 2.0 per
protocol — the potential equation is now completely characterized on
connected graphs; QA-axis counts updated to 319/23), scoreboard
(regenerated; verification rows and a solvability interpretation
bullet), SGT index map, README snapshot, proposal checklist marked
step 4 delivered with the route decision and one implementation note
(`rw [Finset.mul_sum]` instance-matching quirk; `simp only` used).

**Verification.** `lake env lean` zero errors/zero new warnings on
`GraphTheory.Spectral` (eight pre-existing linter notes untouched);
zero errors/zero warnings on `PotentialSolvability_QA`; `lake build`
of the QA target and of `SimpleGraphAdapter` (downstream consumer) ✔;
full `lake build` ✔ (2177 targets); all twenty-three QA modules
elaborated directly in one batch (zero failures); no `sorry`/`admit`
under `Scaffold/`; `lint_axioms`, `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (319 QA
declarations, 18 explicit axioms — unchanged; pure hard crust).

**Trust boundary:** unchanged (18 explicit cited axioms); this slice
added no axioms and consumes none. The solvability theorems are
unconditional proved hard crust.

**Remaining risk.** The unsolvability direction is QA-witnessed, not
yet a center theorem (`∃ kernel-certificate ⇔ unsolvable` is the
natural next center statement; reciprocity makes it short). No
parametric property QA (standing QA-axis gap). Environment: ~300
Mathlib oleans pruned at run start (recorded debt); everything this
slice needed was present, so no cache fetch was required — but the
pruning may recur and cost a later run the recorded interpreter fetch.

**Next handoff:** proposal step 5 — define `effectiveResistance` by
the potential equation (`IsEffectiveResistance A u v r ↔ ∃ f, L *ᵥ f
= e u − e v ∧ f u − f v = r`): existence from step 4, uniqueness of
`r` from `laplacian_kernel_eq_span_onesVec`; then symmetry,
nonnegativity, `R u u = 0`, and the energy identity (proposal
authorizes splitting step 5 across two runs if needed). Or the open
earlier candidates: `evals (c • M)` excavation; irregular Cheeger
shape with a named consumer.

## 2026-08-18T11:25:36Z — Electrical-crust step 5 started: effective resistance

**Run:** `20260818T112536Z-run-1`
**Session:** `ses_feb641df5ffenZ7eBJVWZpWAtK`
**Status:** in-progress
**Milestone:** Operator direction "advance
`proposals/electrical-structure-crust.md`, step 5 only" — effective
resistance by the potential equation (`IsEffectiveResistance A u v r ↔
∃ f, laplacian A *ᵥ f = e u − e v ∧ f u − f v = r`), now unlocked by
the delivered step-4 solvability hinge; existence consumes step 4,
uniqueness of `r` consumes the step-2 kernel theorem, making the new
definition load-bearing on both per the falsifiability principle.

**Pre-implementation decisions (to be recorded in the plan):** new
public module `GraphTheory/Electrical.lean` (keeps the 1198-line
`Spectral.lean` from growing; mirrors Mathlib's topic layout), QA
`SpectralGraph/EffectiveResistance_QA.lean` reusing the
`Connectivity_QA`/`PotentialSolvability_QA` fixtures. Mathlib survey
for an existing effective-resistance result runs before writing the
proof, per the proposal's operating instructions.

**Next action:** survey the Mathlib pin (record either way), then the
module (relation, existence, uniqueness of `r`, total
`effectiveResistance` + agreement, energy identity, symmetry,
nonnegativity, `R u u = 0`), QA with positive, fallback-honesty, and
non-unique-potential/unique-`r` witnesses, then direct elaboration,
target builds, full build, hygiene scripts, scoreboard, and doc
updates (backlog item 7, radar subject axis 6, SGT index map, proposal
checklist).

## 2026-08-18T11:38:59Z — Electrical-crust step 5 delivered: effective resistance (completed)

**Run:** `20260818T112536Z-run-1`
**Session:** `ses_feb641df5ffenZ7eBJVWZpWAtK`
**Status:** completed
**Milestone:** Operator direction "advance
`proposals/electrical-structure-crust.md`, step 5 only" — effective
resistance as a defined, well-determined quantity: the
potential-equation relation `IsEffectiveResistance A u v r`, a total
`effectiveResistance` with proved agreement, the energy identity at
solution and function level, symmetry, nonnegativity, and `R u u = 0`.
One step per run; step 6 (the one-sided Dirichlet bound) was not
started. No new axioms (count unchanged at 18) — pure hard crust.

**Mathlib survey (recorded before stating, per the proposal's
operating instructions):** no effective-resistance or "resistance"
declaration anywhere in the pin; no Moore–Penrose pseudoinverse —
the potential-equation definition is the only available route.

**Changes.** New public module
`Scaffold/Mathlib/GraphTheory/Electrical.lean` (17 declarations, all
proved): `IsEffectiveResistance`; hypothesis-free diagonal
characterization `isEffectiveResistance_self_iff`; hypothesis-free
relation symmetry `isEffectiveResistance_symm`; existence
`exists_isEffectiveResistance` (consumes step 4's unit-demand
solvability); uniqueness `isEffectiveResistance_unique_of_reachable` —
stated at reachability-pair strength through step 3's component-form
kernel characterization, so it holds within a component of a
disconnected graph (strictly stronger than the proposal's connected
sketch) — with the connected corollary; the total function
`effectiveResistance` (classical choice; junk fallback `0` **stated,
not hidden** via `effectiveResistance_eq_zero_of_not_exists`);
agreement theorems (`effectiveResistance_eq_of_reachable`,
`effectiveResistance_eq`); the energy identity at solution level
(`quadForm (laplacian A) f = f u − f v` for any solution, no
hypotheses) and function level (`effectiveResistance_eq_quadForm`);
`effectiveResistance_nonneg` (from `laplacian_psd`);
`effectiveResistance_symm`; `effectiveResistance_self`. New QA
`Scaffold/QA/SpectralGraph/EffectiveResistance_QA.lean` (17
declarations, reusing the `Connectivity_QA`/`PotentialSolvability_QA`
fixtures): values computed from the definitions (unit edge `R 0 1 = 1`,
3-path `R 0 2 = 2` — series edges add), the energy identity
cross-checked against an energy computed independently from the raw
definitions, the junk fallback pinned on the disconnected fixture
(cross-component pair: no value exists, proved from the step-4
unsolvability witness, while the function reads `0` — fallback, not
measurement), and same-component witnesses (two distinct potentials
pinning one value `1` through the reachability-form agreement where
the connected theorem's hypothesis fails). Docs: umbrella, execution
plan, this journal, scoreboard (336 QA declarations, 24 modules; new
interpretation bullet; QA-target row updated), SGT index map (new
`Electrical` section), backlog item 7, radar (subject axis 6 re-scored
2.0 → 2.5 per protocol — the first electrical quantity; below 3.0
while the Dirichlet bound, monotonicity, metric inequality, and
Matrix–Tree/Kirchhoff are absent), README snapshot (counts, umbrella,
crust description, axis cell), and the proposal checklist (steps 1–5
of 6 delivered, with the delivery note recording the two strengthening
deviations and the named definiteness residual).

**Verification.** `lake env lean` zero errors/zero warnings on
`GraphTheory.Electrical` and on `EffectiveResistance_QA`; `lake build`
of the QA target and of `SimpleGraphAdapter` (downstream consumer) ✔;
full `lake build` ✔ (2178 targets); all twenty-four QA modules
elaborated directly in one batch (zero failures); no `sorry`/`admit`
under `Scaffold/` (tactic-level scan; textual matches are prose only);
`lint_axioms`, `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (336 QA declarations, 18 explicit axioms —
unchanged).

**Trust boundary:** unchanged (18 explicit cited axioms); this slice
added no axioms and consumes none. The resistance package is
unconditional proved hard crust, load-bearing on the step-2/3 kernel
characterization and the step-4 solvability theorem (a defect in
either would break uniqueness or agreement rather than pass beside
them).

**Remaining risk.** `effectiveResistance` is noncomputable (classical
choice), so QA pins values through the agreement theorems rather than
`decide` on the function itself — the standard trade for totality.
Component-restricted *solvability* is still implicit (agreement needs a
witness in hand; on a disconnected graph, same-component existence is
QA-witnessed but not yet a center theorem). No parametric property QA
(standing QA-axis gap).

**Next handoff:** proposal step 6 — the one-sided Dirichlet bound
`R u v ≥ (f u − f v)² / quadForm (laplacian A) f` (Cauchy–Schwarz
over the energy identity; the direction applications use to
lower-bound resistance), plus the cheap definiteness residual
`R u v = 0 ↔ u = v` (reachable pair). Or the still-open earlier
candidates: `evals (c • M)` excavation; irregular Cheeger shape with
a named consumer.

## 2026-08-18T14:06:54Z — Electrical-crust step 6 started: one-sided Dirichlet bound

**Run:** `20260818T140654Z-run-1`
**Session:** `ses_fead1b54bffecXkdKzAHJaWoVS`
**Status:** in-progress
**Milestone:** Operator direction "advance
`proposals/electrical-structure-crust.md`, step 6 only" — the one-sided
Dirichlet bound `(f u − f v)² / quadForm (laplacian A) f ≤
effectiveResistance A u v` for any test potential `f` with positive
energy. Leverage: it is the direction every application uses to
lower-bound resistance, and its proof is load-bearing on `laplacian_psd`
(polarization of the PSD quadratic form) and on the step-4/step-5
solvability-and-energy chain — per the falsifiability principle, an
error in those would break this proof rather than pass beside it.

**Route (recorded before stating):** expand `quadForm L (f − t • g)`
via the proved reciprocity `laplacian_dotProduct_mulVec`; nonnegativity
for all `t` (from `laplacian_psd`) forces the discriminant bound at
`t = c/E` (degenerate `E = 0` case separately); the cross term is
`f u − f v` through the step-4 potential and the solution-level energy
identity. No attained supremum — the full Dirichlet principle stays
deferred per the proposal.

**Next action:** survey the Mathlib pin for a usable PSD Cauchy–Schwarz
(record either way), implement in `GraphTheory.Electrical`, QA in
`EffectiveResistance_QA.lean` (equality/strict positive witnesses,
reverse-inequality refutation, zero-energy disconnected guard witness),
direct elaboration + target builds + full build + hygiene scripts, then
proposal checklist, backlog item 7, radar, index map, scoreboard, README
snapshot.

## 2026-08-18T14:21:59Z — Electrical-crust step 6 delivered: one-sided Dirichlet bound; program complete (completed)

**Run:** `20260818T140654Z-run-1`
**Session:** `ses_fead1b54bffecXkdKzAHJaWoVS`
**Status:** completed
**Milestone:** Operator direction "advance
`proposals/electrical-structure-crust.md`, step 6 only" — the one-sided
Dirichlet bound `(f u − f v)² / quadForm (laplacian A) f ≤
effectiveResistance A u v`, delivered as the proposal's final step;
steps 1–6 are now all proved hard crust, axiom count 18 throughout.

**Mathlib survey (recorded before proving):** the pin's only
Cauchy–Schwarz is the definite inner-product-space one; the Laplacian
form is semidefinite, unusable without quotienting the kernel; no
`QuadraticForm` C–S at these function types — polarization route taken.

**Changes.** `Scaffold/Mathlib/GraphTheory/Electrical.lean` +4 proved
declarations: `sq_le_mul_of_forall_zero_le_sub` (nonnegative-everywhere
quadratics have nonpositive discriminants), `quadForm_laplacian_sub_smul`
(polarization; mixed terms collapse via the proved reciprocity),
`laplacian_cauchy_schwarz` (`(f ⬝ᵥ L g)² ≤ quadForm L f · quadForm L g`,
no connectivity hypothesis — reusable), and the headline
`effectiveResistance_ge_sq_div_quadForm` (division guarded by
`0 < quadForm`). Load-bearing chain: cross term = `f u − f v` through
the step-4 demand potential, energy = `R u v` through the step-5 energy
identity, C–S through `laplacian_psd`. QA
`SpectralGraph/EffectiveResistance_QA.lean` +9 (345 total): attainment
at both harmonic potentials (edge `1/1 = 1`, path `4/2 = 2`, energies
computed from raw definitions), strictness at a non-harmonic potential
(`1 < 2`), the reverse inequality refuted numerically (`2 ≤ 1` false —
one-sidedness forced), and the `0 <` energy guard witnessed on the
disconnected fixture (zero-energy indicator with voltage difference
`1`). Docs: scoreboard, radar (subject axis 6 re-scored 2.5 → 3.0 per
protocol after proof + QA landed; QA count synced 345/24), backlog item
7 (program complete, definiteness residual named), SGT index map,
README snapshot, proposal checklist (all six steps ✅ with delivery
note).

**Verification.** `lake env lean` on `GraphTheory.Electrical` and
`EffectiveResistance_QA` — zero errors, zero warnings; `lake build` of
the QA target ✔ (2012) and full `lake build` ✔ (2178 targets); all 24
QA modules elaborated directly (zero errors; remaining outputs are
pre-existing `unusedSectionVars` warnings in untouched modules);
345 QA declarations, no `sorry`/`admit` under `Scaffold/` (prose-only
matches); 18 cited axioms unchanged; `lint_axioms`, `check_citations`,
`check_markdown_links`, scoreboard regeneration all pass.

**Concurrent-change note:** `docs/traction-plan.md` was modified
outside this run at 14:21Z (references this milestone's module as the
release-example candidate) and an untracked
`proposals/eng-use-cases.md` present at run start was removed; both
left exactly as found, not authored or reverted by this run.

**Remaining risk.** None new in the delivered slice; the axis-6
residuals stay as recorded (full Rayleigh monotonicity needs the
attained-supremum Dirichlet principle; resistance metric /
definiteness residual `R u v = 0 ↔ u = v`; Matrix–Tree/Kirchhoff
absent).

**Next handoff.** Cheap electrical residual `R u v = 0 ↔ u = v`
(reachable pair, reusing the step-2 zero-energy ⇒ constant argument);
or the standing earlier candidates: `evals (c • M) = c • evals M`
Mathlib excavation, an irregular Cheeger statement shape through
`rayleigh_normalizedLaplacian_degreeSqrt` (needs source + consumer), or
backlog item 3 variants with named consumers.

## 2026-08-18T14:46:27Z — lambda2_variational retirement started: prove in the matrix world; false-shape repair found

**Run:** `20260818T144627Z-run-1`
**Session:** `ses_feaba2b1dffeDvdW2qjgt9LQjm`
**Status:** in-progress
**Milestone:** Operator direction "advance
`proposals/prove-lambda2-variational.md`" — retire the
`lambda2_variational` axiom (18 → 17). Survey finding recorded before
stating anything: the axiom as admitted is materially false — symmetry
alone does not make `onesVec` a bottom eigenvector; on `Fin 2` with
`A = [[0,−1],[−1,0]]` the Laplacian has sorted spectrum `[−2, 0]`, so
`lambda2 = 0` while the Rayleigh sInf side is `−2`. Repair: add
`hnonneg : ∀ i j, 0 ≤ A i j` (matching `laplacian_psd`) at the same
name, then prove it — axiom retirement and emergency statement-shape
repair in one slice. Leverage: closes the radar axis-3 named gap
("λ₂ variational characterization admitted"), removes the stated
blocker of `proposals/prove-cheeger-easy-direction.md`, and every
consumer of the axiom inherits a proved foundation.

**Route (recorded before proving):** matrix-world proof through the
repo's proved eigenbasis machinery (Parseval expansion, spectral
resolution of `quadForm`, eigenvector–`onesVec` orthogonality, two
sorted-multiset counting lemmas via `Multiset.sort_eq` +
`filter_map`), not the proposal's LinearMap bridge — its step-5
multiplicity pin is exactly the counting done here, at lower cost.

**Next action:** implement in `GraphTheory.Spectral` (new proved
section; axiom → theorem), QA in `Variational_QA.lean` (old-shape
refutation on the negative-weight fixture, `K₂` exact instantiation,
disconnected `λ₂ = 0` instantiation), direct elaboration + target
builds + full build + hygiene scripts, then radar/index/source/proposal
and scoreboard updates.

## 2026-08-18T15:54:16Z — lambda2_variational delivered: proved Courant–Fischer, false axiom shape repaired, axioms 18 → 17 (completed)

**Run:** `20260818T144627Z-run-1`
**Session:** `ses_feaba2b1dffeDvdW2qjgt9LQjm`
**Status:** completed
**Milestone:** Operator direction "advance
`proposals/prove-lambda2-variational.md`" — delivered. The
`lambda2_variational` Courant–Fischer characterization of the algebraic
connectivity is now a **proved theorem** (same name, hypothesis
`hnonneg : ∀ i j, 0 ≤ A i j` added); the admitted axiom is retired and
the explicit axiom count drops 18 → 17.

**Falsity finding (recorded before stating):** the pre-repair axiom
assumed only symmetry. On `Fin 2` with `A = [[0,−1],[−1,0]]` it
asserted `0 = −2` (sorted spectrum `[−2, 0]`, every constraint vector a
multiple of `(1,−1)` with Rayleigh quotient `−2`). Same defect class as
the 2026-08-18 Cheeger repair; repaired per architecture §9 at the same
name.

**Route (matrix world; the proposal's LinearMap bridge was never
built):** new proved hard crust in `GraphTheory.Spectral` —
`eigvecOf_expansion_apply`, `dotProduct_eigvecOf` (Parseval),
`dotProduct_eigvecOf_mulVec`, `quadForm_eigvalOf` (spectral
resolution), `quadForm_eigvecOf_self`, `eigvecOf_ortho_onesVec`, the
two multiplicity pins `evals_one_le_max_of_ne` /
`exists_ne_eigvalOf_of_evals_head_eq` (the proposal's step-5
"argument to write", done by `Multiset.sort_eq`-based counting), and
`lambda2_variational`. `exists_mulVec_eq_of_zero_comp` refactored to
consume the extracted expansion lemma.

**Changes.** `Scaffold/Mathlib/GraphTheory/Spectral.lean` (axiom →
theorem + 12 supporting proved declarations; §7 now admits exactly one
statement); `Scaffold/QA/SpectralGraph/Variational_QA.lean` (+26
declarations: old-shape refutation on the negative-weight fixture,
`K₂` exact instantiation with `λ₂ = 2` computed twice independently,
disconnected `λ₂ = 0` on two disjoint edges, path bound `λ₂(P₃) ≤ 1`).
Docs: scoreboard (17/371/0 + retirement note), radar (subject axis 3:
3.0 → 3.5; axiom minimization 3.5 → 4.0, first axiom removed by proof;
proved-depth and QA text/count updated), Chung and Horn–Johnson source
indexes and SGT index map (rows marked theorem), README snapshot, both
proposals' status notes (delivered + normalized-instance scope caveat:
the Cheeger proposal's `secondEval L_sym` intermediate follows from
this plus the proved congruence transfer, but that step is not yet
written).

**Verification.** `lake env lean` on both changed modules — zero
errors, zero new warnings; `lake build` of the QA target ✔; full
`lake build` ✔ (2178 targets); all 24 QA modules elaborated directly
(zero failures); 371 QA declarations, no `sorry`/`admit` under
`Scaffold/` (prose-only matches); 17 cited axioms; `lint_axioms`,
`check_citations`, `check_markdown_links`, scoreboard regeneration all
pass.

**Concurrent-change note:** `proposals/electrical-structure-crust.md`
was re-statused outside this run and three untracked proposals
(`discovery-mcp-server.md`, `fiedler-partitioning.md`,
`mixing-time-bound.md`) appeared at run start (timestamps 07:33–07:42Z,
before this run began at 14:46Z); all left exactly as found, not
authored or reverted by this run.

**Remaining risk.** None new in the delivered slice. Recorded caveats:
the normalized-Laplacian variational instance (`secondEval L_sym`) is
one proved-transfer step away and not delivered; `lambda2_variational`'s
nonnegativity hypothesis means consumers must now supply it (no
in-repository consumers existed at retirement).

**Next handoff.** The normalized-instance transfer (combinatorial λ₂
variational + `rayleigh_normalizedLaplacian_degreeSqrt` → variational
characterization of `secondEval L_sym`), which is exactly the remaining
intermediate for `proposals/prove-cheeger-easy-direction.md`; the cheap
electrical residual `R u v = 0 ↔ u = v` (reachable pair); or the still
open `evals (c • M) = c • evals M` Mathlib excavation.

## 2026-08-18T17:01:01Z — Retire cheeger_upper_bound (Cheeger easy direction)

**Run:** `20260818T170101Z-run-1`
**Session:** `ses_fea3405d0ffeBFONeKeIHb6OtE`
**Status:** in-progress
**Milestone:** Prove the Cheeger easy direction (`λ₂(L_sym) ≤ 2φ`,
repo name `cheeger_upper_bound`) from a generalized Courant–Fischer
(`secondEval_variational` for any symmetric PSD `M` with
`M *ᵥ onesVec = 0`), retiring the axiom 17 → 16. Top High item in
`proposals/README.md`; the proposal's named missing intermediate is
exactly the normalized-Laplacian variational instance.

**Changes (planned):** `GraphTheory/Spectral.lean` (generic
`secondEval_variational` + generic orthogonality twin;
`lambda2_variational` becomes a corollary at unchanged shape),
`GraphTheory/Cheeger.lean` (axiom → theorem at identical
name/hypotheses), QA extension, then scoreboard/index/proposal updates.

## 2026-08-18T17:32:07Z — cheeger_upper_bound retired: easy direction proved

**Run:** `20260818T170101Z-run-1`
**Session:** `ses_fea3405d0ffeBFONeKeIHb6OtE`
**Status:** completed
**Milestone:** The Cheeger easy direction (`λ₂(L_sym) ≤ 2φ`, repo name
`cheeger_upper_bound`) proved and retired from axiom (17 → 16) — the
top High item in `proposals/README.md`, executed per
`prove-cheeger-easy-direction.md`.

**Changes:** `GraphTheory.Spectral`: the `lambda2_variational`
Courant–Fischer argument generalized to any symmetric PSD matrix with
`onesVec` in its kernel (`secondEval_variational`; generic
`eigvecOf_ortho_onesVec_of_mulVec_eq_zero`; `lambda2_variational`
re-proved as a corollary at unchanged shape; new consumer form
`secondEval_le_rayleigh`). `GraphTheory.Cheeger`: regularity scaling
bridges (`d • L_sym = laplacian A`, PSD transfer, row-sum kernel,
vol = d·card), the volume-centered `cutTestVector` interface
(orthogonality; the regularity-free cut energy identity
`xᵀLx = boundary · (vol V)²`; norm and Rayleigh values), and
`cheeger_upper_bound` as a theorem at the axiom's exact
name/hypotheses. QA `Cheeger_QA.lean` +7 (378 total; imports
`Exhaustive_QA` for the `C₄` tables): test vector pinned to `![1,-1]`
on `K₂`, Rayleigh value computed to `2` (= the pinned `λ₂(L_sym)`:
bound attained), theorem instantiated on `K₂` (`λ₂ = 2φ`) and on `C₄`
(`λ₂ ≤ 1` at conductance `1/2`). Docs: scoreboard (16/378/0 + note),
radar (axis 4 re-scored 2.5 → 3.0 per protocol; trend
26 → 19 → 18 → 17 → 16), Cheeger indexes, backlog item 3, README
snapshot, proposal moved to Delivered with named residuals (irregular
generalization needs the congruence-transfer route after all; the two
supporting moves stay live).

**Verification:** `lake env lean` on `Spectral`, `Cheeger`, and
`Cheeger_QA` — zero errors (only pre-existing linter notes in
untouched code); `lake build Scaffold.Mathlib.GraphTheory.Spectral`
and `Scaffold.Mathlib.GraphTheory.Cheeger` ✔; full `lake build` ✔
(2178 targets); all 24 QA modules elaborated directly in one batch
(zero failures); `lint_axioms`, `check_citations`,
`check_markdown_links` pass; scoreboard regenerated. No `sorry`/`admit`
under `Scaffold/` (textual matches are prose).

**Remaining risk:** the hard direction (`cheeger_lower_bound`,
`φ²/2 ≤ λ₂`) remains admitted — the retirement is the easy direction
only, and QA consequences of the lower bound stay conditional on it.
The irregular-graph Cheeger statement remains future work (named
residual: the generalized engine's constraint set is `x ⊥ onesVec`,
not `x ⊥ √deg`).

**Next handoff:** Fiedler Phase A (A1/A2) — the remaining High item in
`proposals/README.md`, scoped as close to free, now composable with
the proved easy direction; or the named residuals; or the
`evals (c • M)` Mathlib-excavation candidate.

## 2026-08-18T18:14:05Z — Audit and finish the uncommitted normalized-Cheeger milestone

**Run:** `20260818T181405Z-run-1`
**Session:** `ses_fe9ed19c5ffedEJXC38yttHzNl`
**Status:** in-progress
**Milestone:** Operator direction (`scripts/finish-cheeger-milestone`):
audit and finish the current uncommitted Cheeger work only — the
`cheeger_upper_bound` retirement on the normalized Laplacian, whose
hard-direction twin `cheeger_lower_bound` correctly remains the sole
admitted Cheeger axiom — preserving unrelated working-tree changes, no
new proposal, no commit. Planned changes: strip the 6
trailing-whitespace metadata lines this milestone's own two newest
entries introduced into this log, then re-verify directly (changed
public modules + Cheeger QA elaboration and target builds, hygiene
scripts, scoreboard drift check, full `lake build`) and record the
outcome.

## 2026-08-18T18:16:54Z — Normalized-Cheeger milestone audited and finished

**Run:** `20260818T181405Z-run-1`
**Session:** `ses_fe9ed19c5ffedEJXC38yttHzNl`
**Status:** completed
**Milestone:** The uncommitted normalized-Cheeger milestone (the
`cheeger_upper_bound` retirement; `cheeger_lower_bound` correctly
remains the sole admitted Cheeger axiom) audited and finished per
operator direction — no new mathematics, no new proposal, no commit.

**Changes:** `docs/AGENT_ACTIVITY.md` only, in two kinds: (a) stripped
the 6 trailing-whitespace metadata lines this milestone's own two
newest entries (17:01/17:32Z) had introduced — the recent-convention
region of the log is now whitespace-free end to end, while older
committed entries and the template's illustrative hard breaks were
left untouched as unrelated records; (b) this run's own entries.
`docs/EXECUTION_PLAN.md` records the audit and its outcome. No Lean,
index, scoreboard, README, or proposal files changed — the audit found
them already consistent.

**Verification:** audit — the uncommitted Lean changes, scoreboard
(16/378/0), README snapshot, radar, indexes, and the proposal's
Delivered row are mutually consistent, and the recorded claims were
re-derived: direct elaboration (`lake env lean`) of
`GraphTheory.Spectral`, `GraphTheory.Cheeger`, and
`QA.SpectralGraph.Cheeger_QA` with zero errors (Cheeger QA zero
warnings; the remaining linter notes were checked to sit in
declarations present unchanged in HEAD, outside the diff hunks);
explicit `lake build` of those three targets ✔; `lint_axioms` (16
axioms covered), `check_citations`, `check_markdown_links` all pass;
scoreboard regeneration byte-identical to the recorded file (no
drift); `grep` confirms the 16 `axiom` declarations and that
`sorry`/`admit` textual matches are prose only; full `lake build` ✔
(2178 targets). Unrelated working-tree changes (`.opencode/`,
`AGENTS.md`, `scripts/opencode-pursue`, `scripts/README.md`,
`scripts/test_opencode_pursue.sh`, `scripts/finish-cheeger-milestone`,
`proposals/sell-the-methodology.md`,
`proposals/retire-the-mushy-center.md`, untracked
`proposals/README.md`) preserved untouched; nothing committed.

**Remaining risk:** none new — no source changed. The standing risk is
unchanged: the hard direction (`cheeger_lower_bound`, `φ²/2 ≤ λ₂`)
remains admitted; QA consequences resting on it stay conditional.

**Next handoff:** Fiedler Phase A (A1/A2) — the remaining High item in
`proposals/README.md`; or the named residuals (irregular Cheeger via
congruence transfer, the electrical definiteness residual); or the
`evals (c • M)` Mathlib excavation.

## 2026-08-18T18:26:12Z — Fiedler Phase A: vector and sign partition

**Run:** `20260818T182612Z-run-1`
**Session:** `ses_fe9e0c143ffexTpz2rHUkp92Bm`
**Status:** in-progress
**Milestone:** Deliver `fiedler-partitioning.md` Phase A (A1/A2) — the
remaining High item in `proposals/README.md` and the plan's open next
milestone: the Fiedler-vector interface (existence + the induced
sign-pattern partition with nonempty/proper sanity), hard crust, no new
axioms. Leverage: backlog item 4's named first application-ring
candidate, and a load-bearing consumer of the electrical program's
kernel characterization.
- *2026-08-18T18:26:12Z entry continues (Fiedler Phase A).* Status
  update: **completed** as of 2026-08-18T19:07:28Z (same run, same
  session).

**Changes:** new `Scaffold/Mathlib/GraphTheory/Fiedler.lean` (18
declarations, all proved, no new axioms — axiom count stays 16):
`fiedlerIndex`/`fiedlerIndex_eigvalOf` (the eigenbasis index carrying
`lambda2`, fixed by classical choice — the proposal's build-order
sketch indexed `eigvecOf` by a sorted-spectrum position, which is not
that function's type; deviation recorded in the module docstring),
`fiedlerVector` with the eigenvector equation `fiedlerVector_eigen`,
unit norm, nonvanishing, `fiedlerVector_quadForm`,
`fiedlerVector_ortho_onesVec`/`_sum_eq_zero`; the algebraic-connectivity
certificate `lambda2_pos_of_connected` (connected ⇒ `0 < lambda2`,
consuming `laplacian_kernel_eq_span_onesVec`, PSD, and both
multiplicity pins — load-bearing on all three); and `fiedlerPartition`
with sanity facts at interface strength (`_nonempty_of_pos`,
`_ne_univ_of_pos`, through the zero-sum identity) and connectivity
corollaries. New QA `Scaffold/QA/SpectralGraph/Fiedler_QA.lean` (57
declarations): `K₂` partition pinned to a singleton half; the `P₄`
barbell (two `K₂` near-cliques joined by a bridge) with `lambda2 ≤ 1`
via the proved Rayleigh engine, `lambda2 ≠ 1` via the eigen equations,
and the partition *derived* to be exactly the known good cut `{0,1}`
(or complement): boundary `1`, volume `3`, conductance `1/3`; the
disconnected negative witness (`lambda2 = 0`; `onesVec` a nonzero
eigenvector there whose sign filter is `univ` — hypothesis
load-bearing). Records updated: umbrella, scoreboard (435/16/0),
radar (subject axis 4 re-scored 3.0 → 3.5 per the proposal's protocol;
QA count 435/25), SGT index map, backlog item 4, README snapshot cell,
proposal delivery record, `proposals/README.md` (Fiedler → Medium).

**Verification:** `lake env lean` on `GraphTheory.Fiedler` and
`QA.SpectralGraph.Fiedler_QA` — zero errors, zero warnings (build
diagnostics filtered to the two new files: none; the remaining build
notes are the documented pre-existing linter notes in untouched
modules, verified present unchanged in HEAD); `lake build` of both
targets ✔; full `lake build` ✔ (2179 targets); all twenty-five QA
modules elaborated directly in one batch (zero failures); 435 QA
declarations, no `sorry`/`admit` anywhere under `Scaffold/` (textual
matches are prose); 16 explicit cited axioms (unchanged); `lint_axioms`,
`check_citations`, `check_markdown_links` all pass; scoreboard
regenerated (435/16/0).

**Remaining risk:** Phase A is existence and sanity, not quality — the
Fiedler partition exists and is a genuine bipartition on connected
graphs, but no conductance guarantee is claimed (Phase B, deliberately
not started; it would be axiom-backed on the still-admitted Cheeger
hard direction). The `fiedlerIndex` choice is classical, so
`fiedlerVector` is fixed only up to the eigenbasis; every theorem is
choice-independent (stated through `fiedlerIndex_eigvalOf`-style
interfaces). Phase B needs the operator decision the proposal names.

**Next handoff:** the new High item
(`proposals/repair-and-retire-woodbury.md`, appeared mid-run from the
operator; preserved untouched) — the admitted Woodbury axiom is
verified false and Mathlib carries the correct proof, so this is a
correctness repair with axiom-count reduction. Then Fiedler Phase B
(Medium, decision-gated), the electrical definiteness residual, or the
`evals (c • M)` excavation.

## 2026-08-18T19:19:06Z — Fiedler Phase A milestone audit and finish

**Run:** `20260818T191906Z-run-1`
**Session:** `ses_fe9b0cceeffev1a5nLrF4bDxcy`
**Status:** in-progress
**Milestone:** Finish the uncommitted Fiedler Phase A milestone only
(operator direction): audit the delivered `GraphTheory.Fiedler` and
`Fiedler_QA.lean` changes, verify them proportionately (direct module
builds, hygiene suite, scoreboard drift check, full `lake build`),
update only the corresponding records, and close the milestone — no
new mathematics, no new proposal, no commit. Unrelated work (the
untracked Woodbury proposal, `scripts/next-steps`, and all other
working-tree changes) preserved untouched.

## 2026-08-18T19:22:00Z — Fiedler Phase A milestone audit and finish

**Run:** `20260818T191906Z-run-1`
**Session:** `ses_fe9b0cceeffev1a5nLrF4bDxcy`
**Status:** completed
**Milestone:** The uncommitted Fiedler Phase A milestone (the new
`GraphTheory.Fiedler` module, `Fiedler_QA.lean`, and their record
updates) audited, verified, and closed per operator direction — no new
mathematics, no new proposal, no commit.

**Changes:** `docs/7_SGT_RADAR.md` only, one cell: the subject-axis-4
score, stale at `3.0`, synced to `3.5` — the value every other record
of the re-score already carried (the radar's own trailing prose, the
README snapshot, the execution plan, the proposal delivery record, the
activity log). Plus this run's own entries in
`docs/AGENT_ACTIVITY.md` and `docs/EXECUTION_PLAN.md`. No Lean, index,
scoreboard, README, or proposal content changed — the audit found them
already mutually consistent (57 Fiedler QA declarations, 16 explicit
axioms, 25 QA modules, re-derived from source).

**Verification:** `lake env lean` on `GraphTheory.Fiedler` and on
`QA.SpectralGraph.Fiedler_QA` — zero errors, zero warnings; `lake
build` of both targets ✔; full `lake build` ✔ ("Build completed
successfully" — the 22 Scaffold-side linter notes are the documented
pre-existing ones in untouched committed modules, none in the two new
Fiedler files; the ~2980 further notes are Mathlib-package `docPrime`
warnings over recompiled Mathlib residue, the recorded pruned-cache
environment debt, not Scaffold code); scoreboard regeneration
byte-identical (435/16/0 re-derived, no drift); `lint_axioms` (16
covered), `check_citations`, `check_markdown_links` all pass.
Unrelated working-tree changes (untracked
`proposals/repair-and-retire-woodbury.md`, `scripts/next-steps`, and
all pre-existing modifications) preserved untouched; nothing
committed.

**Remaining risk:** none new — one stale documentation cell repaired,
no source changed. The standing risks are unchanged: the Cheeger hard
direction (`cheeger_lower_bound`) remains admitted (Phase B of the
Fiedler proposal would rest its lower-bound half on it), and the
Fiedler vector is fixed only up to the classical eigenbasis/index
choice (every theorem is stated through choice-independent
interfaces).

**Next handoff:** the High item — repair and retire the Woodbury
identity axiom (`repair-and-retire-woodbury.md`: the admitted axiom is
verified false; Mathlib's `Matrix.invOf_add_mul_mul` carries the
correct proof). Then Fiedler Phase B (Medium, decision-gated), the
electrical definiteness residual, or the `evals (c • M)` excavation.

## 2026-08-18T19:30:04Z — Repair and retire the false Woodbury identity axiom

**Run:** `20260818T193004Z-run-1`
**Session:** `ses_fe9a84ffbffef90p4oMoglfP5k`
**Status:** in-progress
**Milestone:** Execute the High priority item
(`proposals/repair-and-retire-woodbury.md`): the admitted
`woodbury_identity` axiom is verified false (scalar counterexample
`A=1, U=V=1, C=0`), so repair its statement shape to the standard
middle factor `C⁻¹ + V A⁻¹ U` with the three explicit `IsUnit …det`
hypotheses, then prove it from Mathlib's `Matrix.invOf_add_mul_mul`
plus the `NonsingularInverse` bridges — an emergency trust-base repair
per architecture §9, retiring an axiom (16 → 15). QA: refutation of the
old scalar shape without consuming the axiom, plus positive scalar and
non-scalar instances. Correctness repair outranks consumers here: a
false axiom is dangerous precisely while still unconsumed
(`GraphTheory/Dynamics.lean` names it as its intended future consumer).

## 2026-08-18T19:50:11Z — Woodbury identity repaired and retired (axiom 16 → 15)

**Run:** `20260818T193004Z-run-1`
**Session:** `ses_fe9a84ffbffef90p4oMoglfP5k`
**Status:** completed
**Milestone:** The High priority item delivered: the verified-false
admitted `woodbury_identity` retired to a proved theorem at the same
name (explicit axioms 16 → 15), an emergency correctness repair per
architecture §9, with the false old shape refuted in QA and the
corrected theorem proved from Mathlib.

**Changes:** `Scaffold/Mathlib/Core/MatrixUpdates.lean` — the axiom is
now a theorem with the standard middle factor `(C⁻¹ + V * A⁻¹ * U)⁻¹`
and exactly the three hypotheses `IsUnit A.det`, `IsUnit C.det`,
`IsUnit (C⁻¹ + V * A⁻¹ * U).det`; the old `IsUnit (A + U C V).det`
hypothesis was dropped as *derivable* (Mathlib's
`Matrix.invertibleAddMulMul` constructs the sum's `Invertible`
instance — a strengthening beyond the proposal's three-hypothesis
sketch). Proof is pure upstream reuse: `Matrix.invOf_add_mul_mul` plus
`Matrix.invertibleOfIsUnitDet`/`Matrix.invOf_eq_nonsing_inv`, no new
imports needed. Module and theorem docstrings carry the repair record;
`sherman_morrison` untouched (out of scope by the proposal). New QA
file `Scaffold/QA/Core/MatrixUpdates_QA.lean` (8 declarations, the
first Core-domain QA): `old_woodbury_identity_refuted_QA` negates the
retired axiom's own statement at `Fin 1`/`ℚ` and refutes it *without
consuming any axiom*; `old_woodbury_middle_hyp_holds_QA` /
`old_woodbury_sum_hyp_holds_QA` prove the retired hypotheses *held* at
the counterexample (the refutation is of a genuinely applicable
statement); `corrected_C_hyp_excludes_counterexample_QA` proves the new
`IsUnit C.det` hypothesis excludes it; positive instances at scalars
(`1/5` both sides, right side pinned by consuming the theorem) and at
the non-scalar rank-one update `diag 2 2` + all-ones (both sides
`!![3/8,-1/8;-1/8,3/8]`, middle `(1+1)⁻¹ = 1/2` computed). Records:
both indexes, scoreboard (15/443/0, milestone bullet, verification
rows), radar (axiom-minimization re-scored 4.0 → 4.5 per protocol —
the first retirement motivated by verified falsity; QA 443/26;
proved-depth text), README (15 axioms, 443 QA), the proposal's delivery
record, and `proposals/README.md` (item → Delivered).

**Verification:** `lake env lean` on `Core.MatrixUpdates` and
`QA.Core.MatrixUpdates_QA` — zero errors, zero warnings (the Woodbury
theorem elaborated clean on the first pass; the QA file needed three
iterations — a stale-olean artifact, `Ring.inverse` blocking kernel
`decide` evaluation of `Matrix.inv`, and bare `Fin 2` literals
defaulting to `ℕ`, all resolved: 1×1 inverses via
`Matrix.inv_eq_left_inv` cancellation, 2×2 via the adjugate formula,
literal noise eliminated by fixture definitions); `lake build
Scaffold.Mathlib.Core.MatrixUpdates` ✔; full `lake build` ✔ (2179
targets); all twenty-six QA modules elaborated directly in one batch
(zero errors; only the documented pre-existing `unusedSectionVars`
notes in untouched modules); 443 QA declarations, no `sorry`/`admit`
under `Scaffold/` (textual matches are prose); 15 explicit axioms
(−1); `lint_axioms` (15 covered), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated from source
(15/443/0).

**Remaining risk:** none from the retired axiom — the false statement
is deleted, not deprecated, and had zero consumers (a compatibility
alias would have to restate a falsehood). `sherman_morrison` remains
admitted: the proposal's own text and the priority table note it is
correctly shaped per its statement, but it has not had the full
fidelity review the Woodbury one got before its falsity was found; the
`retire-sherman-morrison.md` proposal (now unblocked) covers it.

**Next handoff:** the operator's new High item
(`proposals/prove-courant-fischer.md`, with four named downstream
consumers), or the Sherman–Morrison retirement (Medium, the cheapest
remaining retirement, QA scaffolding now in place). Fiedler Phase B
stays Medium and decision-gated; the electrical definiteness residual
and the `evals (c • M)` excavation remain open. Concurrent
working-tree changes preserved untouched (the operator's
`proposals/{prove-courant-fischer,retire-sherman-morrison,admit-perron-frobenius}.md`
additions and the `scripts/next-steps` deletion).

## 2026-08-18T21:03:46Z — General Courant–Fischer min–max (proof)

**Run:** `20260818T210346Z-run-1`
**Session:** `ses_fe9562e17ffe4hhby1PpujPSnj`
**Status:** in-progress
**Milestone:** Prove the general Courant–Fischer min–max theorem for the
sorted spectrum of any real symmetric matrix (the High item in
`proposals/README.md`, `proposals/prove-courant-fischer.md`), generalizing
the fixed-k=2 `secondEval_variational` engine to every index. Pure hard
crust — no axiom is retired (general min–max was never admitted), axiom
count stays 15 — but it is the proof substrate the proposal names for four
downstream consumers (interlacing retirement, Rayleigh monotonicity, the
Cheeger hard direction, Fiedler Phase B).

**Plan (recorded before editing):** the proposal's open next step — survey
the pin for the dimension-intersection lemma — is resolved affirmatively
this run: `Submodule.finrank_sup_add_finrank_inf_eq`,
`Finset.exists_smaller_set`, `finrank_span_eq_card` (Fintype-family form),
`Fintype.linearIndependent_iff`, `Module.finrank_pi`, and
`Submodule.ne_bot_iff` are all present in the v4.14.0 pin. Route: two
witness-form theorems (existence of an optimal `(k+1)`-dimensional
subspace; every `(k+1)`-dimensional competitor contains a test vector with
Rayleigh quotient ≥ `evals k`), proved through the existing eigenbasis
algebra (`quadForm_eigvalOf`, `dotProduct_eigvecOf`,
`eigvecOf_inner`), plus the packaged `sInf` equality. New general-k
multiplicity pins (index-filter cardinalities vs `k`) as public center
API. QA: computable fixture `!![2,1;1,2]` (spectrum `[1,3]` pinned by
trace/determinant/sortedness, mirroring `edge_normLap_secondEval_eq_two_QA`),
both directions instantiated, attainment and non-attainment negative
witnesses (wrong subspace refuted; dimension hypothesis witnessed
load-bearing), and a `Fin 3` path-Laplacian instantiation.

## 2026-08-18T21:52:24Z — General Courant–Fischer min–max proved

**Run:** `20260818T210346Z-run-1`
**Session:** `ses_fe9562e17ffe4hhby1PpujPSnj`
**Status:** completed
**Milestone:** The High item `proposals/prove-courant-fischer.md` delivered:
the `k`-th sorted eigenvalue of any real symmetric matrix characterized at
every index — pure hard crust, axiom count unchanged at 15 (general
min–max was never admitted), so this is load-bearing proof growth rather
than trust-surface reduction; it is the named proof substrate for four
follow-ons (interlacing retirement, Rayleigh monotonicity, the Cheeger
hard direction, Fiedler Phase B), none claimed here.

**Changes:** `GraphTheory.Spectral` gained a `CourantFischer` section
(~450 lines): public center API — general-`k` multiplicity pins
(`card_filter_eigvalOf_lt_evals_le`, `succ_le_card_filter_eigvalOf_le`),
orthonormal-family tools (`eigvecOf_dotProduct`,
`linearIndependent_eigvecOf_finset`, `finrank_span_eigvecOf_finset`),
component-form Rayleigh bounds
(`rayleigh_le_evals_of_forall_dotProduct_eq_zero`,
`evals_le_rayleigh_of_forall_dotProduct_eq_zero`), and span-orthogonality
(`dotProduct_eigvecOf_eq_zero_of_mem_span`); plus the three headline
forms — `exists_submodule_forall_rayleigh_le`,
`exists_ne_mem_rayleigh_ge_of_finrank_eq`, `evals_min_max` —
symmetry-only, reusing the proved eigenbasis algebra plus the pin's
`Submodule.finrank_sup_add_finrank_inf_eq` (the proposal's open survey
step, resolved affirmatively before committing). New QA file
`SpectralGraph/CourantFischer_QA.lean` (33 declarations): spectrum `[1,3]`
pinned from trace/determinant/sortedness on `!![2,1;1,2]`; both
directions instantiated, including the derived top-eigenvalue-domination
universal (existence direction + `eq_top_of_finrank_eq`) and exact
attainment of `evals 1` through both directions; negative witnesses —
wrong line refuted (`3 ≤ 1`), dimension hypothesis load-bearing
(conclusion false on a one-dimensional subspace at index `1`), interior
index `k = 1 < n−1` exercised on the path Laplacian (wrong
two-dimensional subspace refuted at `4/3`; cross-check against the older
`secondEval_le_rayleigh` engine). Records: scoreboard (15/476/0,
milestone bullet), radar (subject axis 3 re-scored 3.5 → 4.0 per
protocol; QA count 476/27; proved-depth text), README (axis cell, counts,
maturity), SGT index map, proposal delivery record,
`proposals/README.md` (High item → Delivered; no High remains).

**Verification:** `lake env lean` on `GraphTheory.Spectral` (zero errors;
no new warnings after silencing the one new-code section-variable note
with `omit`) and on `QA.SpectralGraph.CourantFischer_QA` (zero errors,
zero warnings); targeted `lake build` of both targets ✔; full
`lake build` ✔ (2179 targets); all twenty-seven QA modules elaborated
directly in one batch (zero failures); 476 QA declarations (+33), no
`sorry`/`admit` anywhere under `Scaffold/` (textual matches are prose);
15 explicit cited axioms (unchanged); `lint_axioms`, `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (15/476/0) and
re-checked idempotent after the manual prose edits.

**Remaining risk:** none identified in the delivered proof — it is
kernel-checked with no new axioms or admissions, and the QA falsifies
nearby wrong statements rather than merely instantiating the theorem.
The four named consumers are open follow-ons needing their own scoping
(the proposal explicitly forbids claiming them); the packaged
`evals_min_max` expresses the within-subspace maximum as the infimum of
dominating values, an honest but non-standard packaging documented in
its docstring.

**Next handoff:** no High item remains in `proposals/README.md`.
Candidates for the next run: the Sherman–Morrison retirement (Medium,
cheapest remaining); the interlacing retirement through the new min–max
theorem (its first named consumer); full Rayleigh/Dirichlet monotonicity;
Fiedler Phase B (Medium, decision-gated). Unrelated working-tree changes
(the operator's `scripts/opencode-pursue` and
`scripts/test_opencode_pursue.sh` modifications) preserved untouched;
nothing committed.

## 2026-08-18T22:33:14Z — Sherman–Morrison axiom retirement (proof)

**Run:** `20260818T223314Z-run-1`
**Session:** `ses_fe900e85affegpNCBrauKLr1L5`
**Status:** in-progress
**Milestone:** Retire the `sherman_morrison` axiom (the Medium item
`proposals/retire-sherman-morrison.md`, named the cheapest remaining axiom
retirement and unblocked by the Woodbury repair) by specializing the proved
`woodbury_identity` at `k = Fin 1`, at the axiom's current name and
hypotheses — explicit axiom count 15 → 14, pure trust-surface reduction.
Per the proposal's verified finding, this is a proof task, not a
correctness repair: the statement was already checked correct against the
corrected Woodbury shape.

**Plan (recorded before editing):** Mathlib survey done — the pin has
`Matrix.mul_smul`/`Matrix.smul_mul`, `Matrix.det_fin_one`,
`Matrix.inv_eq_left_inv` (`B * A = 1 → A⁻¹ = B`), `Matrix.dotProduct`;
`Matrix.inv_one` does not exist (derived instead). Route: rank-one
packing `u`/`v` into `Fin 1` column/row matrices, 1×1 middle factor with
entry `1 + v ⬝ᵥ (A⁻¹ *ᵥ u)` (`Fin.sum_univ_one` computation), unit
determinant from `hv`, scalar-inverse 1×1 inverse, matrix-level
`mul_smul`/`smul_mul` reshaping to the entrywise statement. QA: positive
instance at the existing `A2 = diag 2 2` rank-one fixture (value
computed independently via the adjugate), negative witness at the
excluded denominator (`v ⬝ᵥ (A⁻¹ *ᵥ u) = -1`, where the update is
singular). Records to follow: module docstring, both indexes, scoreboard,
radar, README, `proposals/README.md`, proposal delivery record. The
operator's concurrent changes (`.gitignore`, clean-room proposals,
`cdx-clean-assess.md`, mushy-center priority row) preserved untouched.

## 2026-08-18T22:44:25Z — Sherman–Morrison axiom retired (proved)

**Run:** `20260818T223314Z-run-1`
**Session:** `ses_fe900e85affegpNCBrauKLr1L5`
**Status:** completed
**Milestone:** `proposals/retire-sherman-morrison.md` delivered — the
`sherman_morrison` axiom retired to a proved theorem at unchanged name,
hypotheses, and statement (explicit axiom count 15 → 14), as the
`k = Fin 1` specialization of the proved `woodbury_identity`. Pure
trust-surface reduction; per the proposal's verified pre-check, a proof
task, not a correctness repair.

**Changes:** `Core.MatrixUpdates` — the axiom replaced by a theorem
proved from the repository's own Woodbury theorem: `Fin 1` column/row
packing (`U * V` equals the entrywise outer product, a
`Fin.sum_univ_one` computation as calibrated), the 1×1 middle factor
identified with the scalar denominator `1 + v ⬝ᵥ (A⁻¹ *ᵥ u)` (via
`Matrix.dotProduct_mulVec`), its unit determinant from `hv` through
`Matrix.det_fin_one`, its inverse as the 1×1 scalar inverse
(`Matrix.inv_eq_left_inv`; `Matrix.inv_one` absent from the pin,
derived instead), and the shape matched by `Matrix.mul_smul` /
`Matrix.smul_mul` algebra. The specialization is load-bearing on the
Woodbury repair. QA `Core/MatrixUpdates_QA.lean` +4 (480 total):
adjugate-independent positive instance at `diag 2 2` + all-ones
(`!![3/8,-1/8;-1/8,3/8]`, denominator computed to `1`), and the
excluded-denominator negative witness (`v ⬝ᵥ (A⁻¹ *ᵥ u) = -1` attained
at a `Fin 1` fixture where the update is the singular zero matrix).
Docs: module docstring, both indexes, scoreboard (14/480/0 + milestone
bullet + verification rows), radar (trend extended to 26 → … → 14; QA
count 480/27), README (14/480), `proposals/README.md` (→ Delivered),
proposal delivery record.

**Verification:** `lake env lean` on both changed modules — zero
errors, zero warnings; targeted `lake build` of both targets ✔ (the QA
file is the module's only direct consumer, verified by import search);
full `lake build` ✔ (2179 targets); 480 QA declarations, no
`sorry`/`admit` anywhere under `Scaffold/`; `lint_axioms` (14 covered)
and `check_citations` pass; `check_markdown_links` reports only the
operator's untracked `cdx-clean-assess.md` links (pre-existing at run
start, outside this milestone); scoreboard regeneration idempotent
after the prose edits.

**Remaining risk:** none identified — the retired statement is
unchanged (it was verified correct before the proof), the theorem is
kernel-checked with no new axioms, and zero consumers existed to
migrate. The singular-witness QA pins that the excluded denominator is
exactly where the update loses invertibility.

**Next handoff:** no High item remains in `proposals/README.md`.
Candidates: Fiedler Phase B (Medium, needs its named operator
decision), the mixing-time program (Medium), the min–max theorem's
named consumers as separately scoped runs (interlacing retirement;
Rayleigh/Dirichlet monotonicity), the electrical definiteness residual,
or the `evals (c • M)` excavation. Unrelated working-tree changes (the
operator's `.gitignore`, clean-room proposal files,
`cdx-clean-assess.md`, and the mushy-center priority row) preserved
untouched; nothing committed.

## 2026-08-18T23:05:12Z — Cauchy interlacing axiom retirement (proof)

**Run:** `20260818T230335Z-run-1`
**Session:** `ses_fe8e869ffffekg9H8jzuweYEGJ`
**Status:** in-progress
**Milestone:** Retire the `eigen_interlacing_principal_submatrix` axiom
(the min–max theorem's first named consumer; explicit axiom count target
14 → 13) by proving Cauchy interlacing from the proved Courant–Fischer
engine. Pure trust-surface reduction and load-bearing growth: the proof
consumes both CF witness directions, so a defect in the new engine would
surface here rather than pass beside it. Pre-check: the admitted
statement is the textbook true window — a proof task, not a repair.

**Plan (recorded before editing):** padding bridge (extend-by-zero,
Rayleigh-preserving), lower bound via CF existence on the submatrix +
competitor on the ambient, upper bound via CF existence on the ambient
at `i + d` + the dimension-intersection count (the same
`finrank_sup_add_finrank_inf_eq` pattern CF used) + basis extraction for
the exact competitor dimension. QA: numeric instantiation at `K₂` with a
singleton submatrix (strict window, both naive one-sided bounds
refuted). Records to follow: module docstring, both index rows,
scoreboard, radar, README, coverage map, Courant–Fischer proposal note,
`proposals/README.md`.

## 2026-08-18T23:43:10Z — Cauchy interlacing axiom retired (proved from Courant–Fischer)

**Run:** `20260818T230335Z-run-1`
**Session:** `ses_fe8e869ffffekg9H8jzuweYEGJ`
**Status:** completed
**Milestone:** `eigen_interlacing_principal_submatrix` retired from
axiom to proved theorem at unchanged name/hypotheses/statement —
explicit axiom count **14 → 13**. A pure proof task per the recorded
pre-check (the admitted statement was the true textbook window
`λᵢ ≤ μᵢ ≤ λᵢ₊ₙ₋ₘ`), and the Courant–Fischer min–max engine's first
named consumer: the proof consumes both witness directions, so a defect
in the new engine would surface here (load-bearing growth).

**Changes:** `GraphTheory.Spectral` — the axiom replaced by a theorem
proved through a new extend-by-zero padding bridge (`padVec`/
`padVecLinear` with `dotProduct_padVec_self`, `quadForm_padVec`,
`rayleigh_padVec` — Rayleigh preservation needs no symmetry) plus
subspace bookkeeping (`finrank_map_eq_of_injective`,
`finrank_comap_eq_of_le_range`, `exists_submodule_finrank_eq_of_le`).
Lower bound: CF-existence on the submatrix, image under padding,
CF-competitor on the ambient. Upper bound: CF-existence on the ambient
at `i + d`, the dimension count `finrank (U ⊓ range pad) ≥ i + 1` (the
proposal's warned subspace-intersection step, via the same
`Submodule.finrank_sup_add_finrank_inf_eq` the min–max proof used),
exact-dimension extraction, comap transfer, back through
`rayleigh_padVec`. One new import (`Mathlib.Algebra.Module.Submodule.Range`).
The module now carries zero `axiom` declarations. QA
`SpectralGraph/Interlacing_QA.lean` (+4 public, 484 total): `K₂`
spectrum `[0,2]` and singleton-submatrix spectrum `[1]` pinned from
trace/determinant/sortedness independent of the theorem; window
instantiated to the strict `0 ≤ 1 ≤ 2`; both collapsed one-sided bounds
refuted in proved form — superseding the axiom-era "no thin QA exists"
note (the machinery did not exist then). Docs: module docstring and
section header, scoreboard (13/484/0 + milestone bullet + verification
rows), radar (axis-2 interlacing proved; axiom-minimization trend → 13;
QA 484/27; proved-depth and reuse text), README (13 axioms, 484 QA),
Horn–Johnson source index and SGT index map, coverage map,
Courant–Fischer proposal delivery note, `proposals/README.md`.

**Verification:** `lake env lean` on both changed modules — zero errors
(new-code section-variable notes silenced with `omit`; remaining notes
are the documented pre-existing ones); targeted `lake build` of both
targets ✔; full `lake build` ✔ (2179 targets); 484 QA declarations, no
`sorry`/`admit` anywhere under `Scaffold/`; 13 explicit cited axioms;
`lint_axioms`, `check_citations`, `check_markdown_links` pass;
scoreboard regenerated and idempotent after the prose edits.

**Remaining risk:** none identified — the retired statement is
unchanged (verified true before the proof), kernel-checked with no new
axioms, and zero consumers existed to migrate. The 1×1/2×2 QA fixtures
pin the window only at small sizes; the interlacing statement's index
arithmetic (`hn`) is exercised at the singleton instance.

**Next handoff:** the operator's new High item
(`proposals/electrical-flow-routing.md`, indexed mid-run — electrical
flows, Thomson's principle, Rayleigh monotonicity; step 0 is its
representation/Mathlib survey) is the next run's milestone per the
operator's own note. Alternatives: mixing-time step 1 (Medium),
Rayleigh/Dirichlet monotonicity (cheaper now through the padding
bridge), Fiedler Phase B (decision-gated). The operator's concurrent
`proposals/electrical-flow-routing.md` and its priority row preserved
untouched; nothing committed.

## 2026-08-19T00:30:01Z — Electrical-flow routing, step 0 (representation survey) + step 1 (Kirchhoff conservation)

**Run:** `20260819T003001Z-run-1`  
**Session:** `ses_fe897785cffejcLqL4bSCUd1j6`  
**Status:** in-progress  
**Milestone:** Open the High item `proposals/electrical-flow-routing.md`: run its step 0 (pin and record the flow representation against a fresh Mathlib survey) and then its step 1 — the smallest independently useful Lean slice (electrical current, divergence, flow predicates, the Kirchhoff bridge from unit-demand potentials to unit flows). Zero new axioms; turns the delivered potential-based resistance API into a routing object. Steps 2–5 are not started this run.

## 2026-08-19T00:41:19Z — Electrical-flow routing steps 0–1 delivered (representation + Kirchhoff conservation)

**Run:** `20260819T003001Z-run-1`  
**Session:** `ses_fe897785cffejcLqL4bSCUd1j6`  
**Status:** completed  
**Milestone:** Open the Active table's High item `proposals/electrical-flow-routing.md`: step 0 (representation survey/decision, recorded before any Lean) and step 1 (the flow interface and Kirchhoff bridge — the resistance API becomes a routing object). Zero new axioms (13 unchanged); steps 2–5 not started.

**Changes:** step 0 recorded in the proposal first — fresh pin survey found no flow/circulation/max-flow API, no graph-native divergence (only continuum divergence theorems), nothing electrical, and no usable oriented-edge API (`SimpleGraph.Dart` is counting machinery), so the matrix representation `EdgeFlow V = Matrix V V ℝ` was pinned with conductance orientation, the zero-conductance support as an explicit `IsFlowOn` conjunct, and the `1/2` ordered-pair factor reserved for step-2 `flowEnergy`; target module the new focused `GraphTheory.ElectricalFlow` (coverage map's electrical row re-surveyed, same absence verdict). Step 1: `electricalCurrent`, `flowDivergence`, `IsFlowOn`, `IsUnitFlow`, `electricalCurrent_antisymm`, `electricalCurrent_eq_zero_of_weight_eq_zero`, the Kirchhoff bridge `flowDivergence_electricalCurrent` (a one-line load-bearing consumer of `laplacian_mulVec_apply`'s exact sign convention), `isFlowOn_electricalCurrent`, and the headline `isUnitFlow_electricalCurrent` (a unit-demand potential induces a valid unit flow). QA `SpectralGraph/ElectricalFlow_QA.lean` (16 declarations): `K₂` and 3-path currents/divergences computed from raw definitions (internal vertex `0`), plus negative witnesses for both proposal-named traps — asymmetric network `!![0,2;1,0]` refutes current antisymmetry (`2 ≠ 1`), and an edgeless-network phantom (antisymmetric, unit divergence) excluded by the support conjunct alone. Umbrella import added; scoreboard (500/13/0), radar (QA 500/28; subject axis 6 evidence extended, score held at 3.0 per protocol and recorded), README, SGT index map, coverage map, proposal, and `proposals/README.md` progress note updated.

**Decisive commands and outcomes:** `lake env lean` on `GraphTheory.ElectricalFlow` and `ElectricalFlow_QA` — both zero errors/warnings (three `omit` clauses for unused section variables); `lake build` of both targets ✔; full `lake build` ✔; all 28 QA modules batch-elaborated with zero failures; `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration byte-idempotent.

**Remaining risk:** the flow interface is plumbing — its mathematical payoff (Thomson, Rayleigh monotonicity) is steps 3–4 and depends on step 2's `flowEnergy` landing with the `1/2` factor QA-witnessed; the zero-edge trap's energy-level refutation is deferred to step 2 by design (no energy definition exists yet to refute with).

**Next handoff:** proposal step 2 — `flowEnergy` (explicit zero branch, mandatory `1/2` factor), the agreement `flowEnergy A (electricalCurrent A f) = quadForm (laplacian A) f`, and the double-counting QA fixture; then steps 3–4 as separate runs. Concurrent operator additions preserved untouched: the uncommitted `proposals/README.md` interlacing-row edit and the new untracked `proposals/decidable-spectral-certificates.md` (a High proposal not yet indexed in the priority table — the next run should treat the table, kept current by the operator, as authoritative). Nothing committed.

## 2026-08-19T01:32:28Z — Electrical-flow routing, step 2 (flow energy and the energy agreement)

**Run:** `20260819T013200Z-run-1`  
**Session:** `ses_fe85dc2beffepvHWCJsEF2D4JJ`  
**Status:** in-progress  
**Milestone:** Continue the Active table's top High item `proposals/electrical-flow-routing.md` at its recorded next step — step 2: `flowEnergy` with the explicit zero branch and the mandatory `1/2` ordered-pair factor, the energy agreement `flowEnergy A (electricalCurrent A f) = quadForm (laplacian A) f`, the unit-demand corollary equating it with `effectiveResistance`, and the QA double-counting/zero-energy-competitor fixtures the proposal mandates. Zero new axioms; steps 3–5 not started this run.

## 2026-08-19T01:46:30Z — Electrical-flow step 2 delivered (flow energy and the energy agreement)

**Run:** `20260819T013200Z-run-1`  
**Session:** `ses_fe85dc2beffepvHWCJsEF2D4JJ`  
**Status:** completed  
**Milestone:** The Active table's top High item `proposals/electrical-flow-routing.md`, step 2: `flowEnergy` with the explicit zero branch and the mandatory `1/2` ordered-pair factor, the energy agreement with the Dirichlet energy, `flowEnergy_nonneg`, and the unit-demand identity equating the current's dissipated energy with the effective resistance it routes. Zero new axioms (13 unchanged); steps 3–5 not started.

**Changes:** `GraphTheory.ElectricalFlow` gained the step-2 section — `flowEnergy` (ordered-pair sum of squared current over conductance, explicit zero branch, halved for double counting), `flowEnergy_electricalCurrent` (agreement `flowEnergy A (electricalCurrent A f) = quadForm (laplacian A) f`: termwise `(c x)²/c = c x²` on the nonzero branch, zero-on-zero on the branch, `laplacian_quadForm` at the end — **symmetry-only**, a recorded statement-shape deviation: nonnegativity is not needed for the agreement, and QA witnesses both sides), `flowEnergy_nonneg` (squares over positive conductances — nonnegativity load-bearing, QA exhibits energy `-1` on a symmetric negative-weight network), and `flowEnergy_electricalCurrent_eq_effectiveResistance` (connected graphs: a unit-demand current dissipates exactly the resistance it routes). QA `ElectricalFlow_QA.lean` (+25, 41 in file): energies `1`/`2` computed from the raw definition on `K₂`/`P₃`, each meeting the independently computed Dirichlet energy and pinned resistance value; the **mandatory double-counting fixture** (raw ordered-pair sum `2 ≠ 1` = Dirichlet energy — omitting the `1/2` factor would numerically break the agreement); the step-1 phantom's deferred zero-energy pinning; and the **zero-energy competitor** — an antisymmetric unit-divergence flow routing through zero-conductance pairs on a real-edge-plus-isolated-vertex network, energy `0 < 1` = the real resistance, excluded by `IsFlowOn`'s support conjunct alone (Thomson's step-3 statement would read `1 ≤ 0` over the support-dropped flow class). Fixture note: all-zero-row matrices defined by the repo's entrywise-`if` pattern (matrix notation's zero-function normalization leaves `vecTail` leftovers). Docs: module/QA docstrings, scoreboard (525/13/0 + milestone bullet + verification rows), radar (QA 525/28; subject axis 6 evidence extended, score held at 3.0 per protocol and recorded — an identity, not a new inequality; proved-depth text), README, SGT index map, proposal step-2 delivery record + deviation, `proposals/README.md` progress note.

**Decisive commands and outcomes:** `lake env lean` on `GraphTheory.ElectricalFlow` and `ElectricalFlow_QA` — both zero errors/warnings; `lake build` of both targets ✔; full `lake build` ✔ (2180 targets); all 28 QA modules batch-elaborated, zero errors (only the documented pre-existing notes in untouched modules); `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (525/13/0).

**Remaining risk:** the energy agreement is plumbing for the variational payoff — Thomson (step 3) and Rayleigh monotonicity (step 4) remain unproved, and the recorded axis hold reflects that; the support conjunct's Thomson-criticality is witnessed at the energy level (the zero-energy competitor) but the inequality itself is not yet stated. The symmetry-only agreement strength is deliberate and QA-pinned; if a later consumer needs the nonnegativity hypothesis present for uniformity, that is a statement-shape decision, not a defect.

**Next handoff:** proposal step 3 — Thomson's principle (`effectiveResistance A u v ≤ flowEnergy A θ` for every valid unit flow; electrical current as minimizer, `flowEnergy_nonneg` on the divergence-free difference, with the discrete integration-by-parts lemma split out if it deserves a reusable interface); then steps 4–5. Alternatives: Foster Phase A (High; needs its pseudoinverse-free statement-shape spike) or decidable-certificates Step 0 (High; convention decision + ℚ-`decide` spike, both scoped in its proposal). The operator's uncommitted `proposals/README.md` sparsification-split rows, untracked `icebox/`, and untracked `proposals/spectral-graph-sparsification.md` preserved untouched; nothing committed.

## 2026-08-19T02:10:23Z — Electrical-flow routing, step 3 (Thomson's principle)

**Run:** `20260819T021023Z-run-1`  
**Session:** `ses_fe838cdecffeVErTeYOC0y9H9f`  
**Status:** in-progress  
**Milestone:** Continue the Active table's top High item `proposals/electrical-flow-routing.md` at its recorded next step — step 3: **Thomson's principle**, `effectiveResistance A u v ≤ flowEnergy A θ` for every valid unit flow `θ` (electrical current as the energy minimizer; discrete integration by parts kills the cross term on the divergence-free difference; `flowEnergy_nonneg` closes). Zero new axioms; steps 4–5 not started this run.

## 2026-08-19T02:59:09Z — Electrical-flow step 3 delivered (Thomson's principle)

**Run:** `20260819T021023Z-run-1`  
**Session:** `ses_fe838cdecffeVErTeYOC0y9H9f`  
**Status:** completed  
**Milestone:** The Active table's top High item `proposals/electrical-flow-routing.md`, step 3: **Thomson's principle** — `effectiveResistance A u v ≤ flowEnergy A θ` for every valid unit flow; the electrical current is the energy minimizer. Zero new axioms (13 unchanged); steps 4–5 (Rayleigh monotonicity, the ICP example) not started.

**Changes:** `GraphTheory.ElectricalFlow` gained the step-3 section — flow-space linearity (`flowDivergence_sub`, `isFlowOn_sub`), the **divergence-free superposition lemma** `flowEnergy_add_of_flowDivergence_eq_zero` (a zero-divergence flow perturbation of a current adds exactly its own energy; the discrete integration-by-parts cross term reduces by Ohm's law to `∑ i j, (f i − f j) * d i j`, whose row sums vanish by zero divergence and whose column sums are the negated row sums by antisymmetry — split out as its own reusable interface per the proposal's suggestion), and the headline `effectiveResistance_le_flowEnergy`. Route exactly as proposed: competitor minus unit-demand current is a divergence-free flow (Kirchhoff bridge + demand equation), superposition adds the difference's energy, `flowEnergy_nonneg` discards it, and the step-2 identity evaluates the current's energy as the resistance — load-bearing on the whole chain. **Statement-shape deviation recorded:** the superposition lemma is stated with **no hypotheses on `A`** (not even the symmetry the proposal's sketch assumed) — only the perturbation's flow properties enter. No `sInf` packaging, per the proposal's instruction. QA `ElectricalFlow_QA.lean` (+18, 59 in file): the new triangle `K₃` fixture (two parallel routes — unit flows non-unique) with resistance `2/3` and the **split current** (`2/3`/`1/3` across the routes) whose energy *attains* `2/3` from the raw definitions; the **detour competitor** (valid `IsUnitFlow`, all conjuncts computed, energy `2`) making Thomson's bound **strict** (`2/3 < 2` — the inequality is not vacuous); and the superposition decomposition composed as `2 = 2/3 + 4/3` with all three energies computed independently of the lemma. Docs: module/QA docstrings, scoreboard (543/13/0, milestone bullet, verification rows), radar (subject axis 6 re-scored **3.0 → 3.5** per protocol — the step-0/2 recorded reservation for Thomson fired; QA count 543/28 with the step-3 kind; proved-depth text; weakest-axes paragraph), README (surgical count/score sync inside the operator's uncommitted rewrite, otherwise untouched), SGT index map (4 new rows), proposal step-3 delivery record + deviation, and `proposals/README.md` progress note.

**Decisive commands and outcomes:** `lake env lean` on `GraphTheory.ElectricalFlow` and `ElectricalFlow_QA` — both zero errors/warnings; `lake build` of both targets ✔; full `lake build` ✔ (2180 targets); all 28 QA modules batch-elaborated, zero errors; `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (543/13/0). Implementation notes: `Finset.mul_sum` rewrote reliably only via expected-type elaboration (`(Finset.mul_sum _ _ _).symm`), not `rw ←`; the triangle/detour fixtures use the entrywise-`if` pattern (the recorded matrix-notation `vecTail` trap).

**Remaining risk:** Thomson's statement requires `supportGraph`-level connectivity because the consumed solvability theorem does; the proof would go through unchanged at reachability strength for same-component pairs of disconnected graphs (the generalization is a statement-shape option, not a defect — the step-2 cheat fixture is excluded by the support conjunct, not by connectivity). Rayleigh monotonicity (step 4) remains unproved; the axis-6 score stays below 4.0 for exactly the recorded reasons (no Rayleigh, resistance metric, or Matrix–Tree/Kirchhoff).

**Next handoff:** proposal step 4 — Rayleigh monotonicity in conductance form (`A ≤ B` entrywise ⇒ `R_B ≤ R_A`, both graphs connected; the `A`-electrical unit flow as competitor on `B` + Thomson on `B`; orientation binding — conductances, not resistances; QA plan item 2, the capacity-increase `1 → 1/2` fixture, belongs there); then step 5 (the ICP capacity-reinforcement example). Alternatives: Foster Phase A (High; needs its statement-shape spike) or decidable-certificates Step 0 (High; convention decision + ℚ-`decide` spike, both scoped in its proposal). The operator's uncommitted README rewrite preserved (only the QA-count and axis-6 score cells synced); nothing committed.

## 2026-08-19T04:08:36Z — Electrical-flow routing, step 4 (Rayleigh monotonicity)

**Run:** `20260819T040836Z-run-1`  
**Session:** `ses_fe7cd9bc4ffeMTQNRZ8PY6Rdff`  
**Status:** in-progress  
**Milestone:** Continue the Active table's top High item `proposals/electrical-flow-routing.md` at its recorded next step — step 4: **Rayleigh monotonicity in conductance form**, entrywise `A ≤ B` ⇒ `effectiveResistance B u v ≤ effectiveResistance A u v` on connected symmetric nonnegative networks (the `A`-electrical unit flow as a competitor on `B`; its `B`-energy is at most its `A`-energy because every conductance increased; Thomson on `B` closes). Orientation binding: weights are conductances, so the inequality direction is `R_B ≤ R_A` — reversing it is a statement bug. Zero new axioms; step 5 (the ICP example) not started this run.

## 2026-08-19T05:44:53Z — Electrical-flow step 4 delivered (Rayleigh monotonicity in conductance form)

**Run:** `20260819T040836Z-run-1`  
**Session:** `ses_fe7cd9bc4ffeMTQNRZ8PY6Rdff`  
**Status:** completed  
**Milestone:** The Active table's top High item `proposals/electrical-flow-routing.md`, step 4: **Rayleigh monotonicity in conductance form** — entrywise `A ≤ B` on connected symmetric nonnegative networks gives `effectiveResistance B u v ≤ effectiveResistance A u v`. Zero new axioms (13 unchanged); step 5 (the ICP example) not started.

**Changes:** `GraphTheory.ElectricalFlow` gained the step-4 section — `isFlowOn_of_le` (**flow-space growth**: a flow supported on `A` is a flow on every entrywise larger `B ≥ A ≥ 0`; support load-bearing — a `B`-zero entry above a nonnegative `A` entry squeezes the latter to zero, so the transferred current carries nothing there), `flowEnergy_le_of_le` (**raising conductances lowers dissipated energy**, termwise `θ²/B ≤ θ²/A` on nonzero branches since every denominator increased; support load-bearing a second time on the `A i j = 0 < B i j` branch, where the `B`-term would otherwise exceed the zeroed `A`-branch — the same zero-conductance trap as steps 2–3, now guarding the comparison), and the headline `effectiveResistance_le_of_le`, proved exactly by the proposed route: the `A`-unit-demand potential's current is a unit flow *on `B`* (growth + the Kirchhoff bridge), Thomson's principle (step 3) on `B` bounds `R_B` by its `B`-energy, the comparison bounds that by its `A`-energy, and the step-2 identity evaluates it as `R_A` — load-bearing on solvability, the Kirchhoff bridge, support, Thomson, and the energy identity. The conductance orientation is as the proposal binds; the optional `supportGraph B`-from-`A` connectivity adapter was deliberately not attempted (non-blocking per the proposal; noted for step 5's packaging if wanted). QA `ElectricalFlow_QA.lean` (+20, 79 in file): the proposal's QA item 2 — conductance `1 → 2` on the unit edge with the resistance decrease `1 → 1/2` certified from an independent potential witness, monotonicity instantiated, the decrease certified strict, and the **orientation guard** refuting the reverse inequality numerically (`1 ≤ 1/2` false — a resistance-direction restatement would be a false statement on this fixture); the competitor transfer instantiated on computed objects (the `edgeAdj`-current a unit flow on `edge2Adj`, cross-network energy `1/2 ≤ 1` from the raw definitions); and a partial increase on the triangle (one edge's conductance doubled: `2/3 → 2/5` strict, the new value pinned by the independent potential `![2/5, 0, 1/5]`). Docs: module/QA docstrings, scoreboard (563/13/0, verification rows, step-4 milestone bullet, cache-provenance note extended), radar (subject axis 6 re-scored **3.5 → 4.0** per the step-3 recorded reservation — Thomson and Rayleigh both landed; QA count 563/28 with the step-4 kind; proved-depth text; weakest-axes paragraph), README (counts, axis-6 cell 4.0, last-assessed date), SGT index map (3 new rows, header to steps 0–4), backlog item 7 (stale "deferred Rayleigh" note corrected — the conductance-form theorem is delivered via the flow route, only the Dirichlet-principle route remains deferred), proposal step-4 delivery record, and `proposals/README.md` progress note.

**Decisive commands and outcomes:** `lake env lean` on `GraphTheory.ElectricalFlow` and `ElectricalFlow_QA` — both zero errors, zero warnings; `lake build` of both targets ✔; full `lake build` ✔ (2180 targets); all 28 QA modules batch-elaborated with zero errors (only the documented pre-existing linter notes in untouched modules); `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (563/13/0). Environment: the pruned Mathlib-oleans state recurred at run start (Mathlib build dir empty; the earlier 10/15-minute elaboration timeouts were the cold import chain, not a defect) — the recorded interpreted cache fetch (`lake env lean --run Cache/Main.lean get` from the mathlib package) restored all 5685 and the builds then elapsed normally (~15 s for the QA module); recorded in the scoreboard's provenance note. Implementation notes: `div_le_div_iff₀` needs the denominators in goal order (B then A); `div_le_div_right` is deprecated for `div_le_div_iff_of_pos_right`; the `B i j = 0` comparison branch must derive `A i j = 0` first (both branches then read `0 ≤ 0`) — `zero_le` on the unresolved `if` fails with a stuck instance.

**Remaining risk:** the headline hypothesizes connectivity of both graphs (the proposal's initial shape); the proof would compose unchanged with a reachability-strength Thomson if that generalization is ever wanted, and the adapter deriving `B`'s connectivity from `A`'s plus `A ≤ B` remains unwritten by design. The orientation guard witnesses the direction on one fixture, not a proof that no restatement could flip it silently — the statement-shape defense is the docstring's explicit conductance note plus the guard. Step 5 is packaging, so the program's mathematical content is now complete; the axis-6 residual gaps (resistance metric, Matrix–Tree, Kirchhoff network theorems) are unchanged.

**Next handoff:** proposal step 5 — the ICP capacity-reinforcement example (`effectiveResistance (increaseConductance A i j δ) u v ≤ effectiveResistance A u v` on a small `SimpleGraph.toWAdj` or weighted fixture, short enough for release documentation), completing the electrical-flow program; or the other High items (Foster Phase A — needs its pseudoinverse-free statement-shape spike; decidable-certificates Step 0 — convention decision + ℚ-`decide` spike, both scoped in its proposal). Concurrent operator additions preserved untouched: the new priority rows in `proposals/README.md` (Reversibility Phase A Medium, Relative Entropy Medium, Weighted Matrix-Tree Low), the untracked proposal files, the `icebox/` additions, and `why-sgt.md`. Nothing committed.

## 2026-08-19T06:01:17Z — Electrical-flow routing, step 5 (the ICP capacity-reinforcement example)

**Run:** `20260819T060117Z-run-1`  
**Session:** `ses_fe767f27affe0rGkDcONmxu57b`  
**Status:** in-progress  
**Milestone:** Complete the Active table's top High item `proposals/electrical-flow-routing.md` at its recorded final step — step 5, the ICP capacity-reinforcement example: `effectiveResistance (increaseConductance A i j δ) u v ≤ effectiveResistance A u v` as a one-hypothesis theorem (only the original network's connectivity is assumed; the increased network's connectivity is derived), plus the release-documentation QA fixture on a `SimpleGraph.toWAdj` path network with the decrease certified numerically. Packaging of step 4, not new mathematics; zero new axioms (13 unchanged). With step 5 the electrical-flow program is complete.

## 2026-08-19T06:17:20Z — Electrical-flow step 5 delivered (ICP capacity reinforcement); program complete

**Run:** `20260819T060117Z-run-1`  
**Session:** `ses_fe767f27affe0rGkDcONmxu57b`  
**Status:** completed  
**Milestone:** The Active table's top High item `proposals/electrical-flow-routing.md`, step 5 — the ICP capacity-reinforcement example: `effectiveResistance (increaseConductance A i j δ) u v ≤ effectiveResistance A u v` as a one-hypothesis theorem (only the original network's connectivity hypothesized; the reinforced network's derived), plus the release-documentation QA fixture on the Mathlib path graph through `toWAdj`. Zero new axioms (13 unchanged); **with this step the electrical-flow program is complete** (all six steps, 0–5, delivered across five runs).

**Changes:** `GraphTheory.ElectricalFlow` gained the step-5 section — `increaseConductance` (raise one undirected pair's conductance by `δ`, both ordered entries together, symmetry/nonnegativity-preserving) with entry interfaces and structural lemmas (`increaseConductance_apply_of_reinforced`/`_of_not_reinforced`, `le_increaseConductance` for `0 ≤ δ`, `increaseConductance_isSymm`, `increaseConductance_nonneg`); the step-4-recorded optional adapter delivered as the packaging companion — `supportGraph_le_of_le` (support graphs grow along entrywise domination, stated with **no nonnegativity hypothesis**: `0 < A i j ≤ B i j`) and `supportGraph_connected_of_le` (capacity growth preserves connectivity, through Mathlib's `SimpleGraph.Connected.mono`, found in the pin — no local walk induction needed); and the one-hypothesis headline `effectiveResistance_le_increaseConductance`, composing step 4's monotonicity with the adapter. QA `ElectricalFlow_QA.lean` (+9, 88 in file) — the release-facing example on the Mathlib `Fin 3` path graph through `SimpleGraph.toWAdj`: adapter weights bridged entrywise to the weighted-fixture world; the reinforcement computed to exactly the concrete doubled-path matrix; the reinforced resistance `3/2` pinned by the independent potential witness `![1/2, 0, −1]` with connectivity from explicit walks (independent of the adapter the theorem consumes); the headline instantiated one-hypothesis; the decrease certified strict `3/2 < 2` against the pinned original `2`. Docs: module/QA docstrings, scoreboard (572/13/0, verification rows, step-5 milestone bullet), radar (QA 572/28; axis-6 evidence extended to program-complete, score **held at 4.0** per protocol — packaging, not new mathematics; step-4's 3.5 → 4.0 re-score added to the re-scoring log for continuity; proved-depth clause; header date), README (572), SGT index map (4 new rows, header to steps 0–5), backlog item 7 (program-complete note), proposal step-5 delivery record + status/open-next-step closure, and `proposals/README.md` (row moved to the Delivered table; progress note rewritten — Foster Phase A is now the top High item). Mid-run repair, recorded: a `True`-placeholder stub inserted by a bad edit was replaced with the real section before any verification ran.

**Decisive commands and outcomes:** `lake env lean` on `GraphTheory.ElectricalFlow` and `ElectricalFlow_QA` — both zero errors/warnings (targeted `omit` clauses on unused section variables; note the QA re-elaboration required `lake build` of the module first — the direct elaboration had loaded the stale olean); `lake build` of both targets ✔; full `lake build` ✔ (2180 targets); all 28 QA modules batch-elaborated, zero errors; `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (572/13/0). Implementation notes: the `WAdj` abbrev accepts only named application (`WAdj (V := V)`), not positional; `omit` must precede the doc comment and cannot drop an instance the `if`-condition's `Decidable` instance actually references (`DecidableEq V` is load-bearing in the entry lemmas); the path fixture's vertex 2 is reached through vertex 1 (no direct 0–2 edge — the triangle pattern does not transfer).

**Remaining risk:** none identified for the delivered statement — it is packaging of the step-4 theorem, whose orientation guard, strictness, and value pinning carry the falsification load, and the QA pins the packaged values (`2 → 3/2`) from independent potential witnesses. The axis-6 residual gaps are unchanged and recorded (resistance metric/triangle inequality, Matrix–Tree, Kirchhoff network theorems); the definiteness residual `R u v = 0 ↔ u = v` remains the family's cheap open item.

**Next handoff:** the Active table's top High item is now **Foster's Theorem Phase A** (`spectral-graph-sparsification.md`) — first run is its recorded pseudoinverse-free statement-shape spike (eigenbasis expansion + the proved one-dimensional kernel characterization); alternative: decidable-certificates Step 0 (convention decision + ℚ-`decide` spike, scoped in its own proposal). Operator's Medium/Low rows and the untracked `why-sgt.md` preserved untouched; nothing committed.

## 2026-08-19T06:35:36Z — Foster's Theorem Phase A (pseudoinverse-free eigenbasis route)

**Run:** `20260819T063536Z-run-1`  
**Session:** `ses_fe74f52a5ffeEdk04vfmw17jU0`  
**Status:** in-progress  
**Milestone:** The Active table's top High item `proposals/spectral-graph-sparsification.md`, **Phase A only**: Foster's theorem `(∑ i, ∑ j, A i j * R i j) / 2 = card V − 1` as pure hard crust via the proposal's pseudoinverse-free route — eigenbasis expansion of the unit-demand potential, summation swap, `quadForm(L, v_k) = λ_k` per unit eigenvector, and the proved one-dimensional kernel characterization for the `n − 1` count. Zero new axioms (13 unchanged); Phase B not started (blocked on the proposal's matrix-Chernoff scope decision). Environment: the pruned Mathlib-oleans state recurred at run start; the recorded interpreted cache fetch restored 5387 oleans before any elaboration.

## 2026-08-19T07:52:00Z — Foster's Theorem Phase A delivered; pure hard crust via the eigenbasis route

**Run:** `20260819T063536Z-run-1`  
**Session:** `ses_fe74f52a5ffeEdk04vfmw17jU0`  
**Status:** completed  
**Milestone:** The Active table's top High item `proposals/spectral-graph-sparsification.md`, **Phase A only**: Foster's theorem `(∑ i, ∑ j, A i j * effectiveResistance A i j)/2 = card V − 1` proved as pure hard crust in the new `GraphTheory.Foster` — zero new axioms (13 unchanged; `#print axioms` confirms only `propext, Classical.choice, Quot.sound`), via the proposal's pseudoinverse-free eigenbasis route. Phase B not started (blocked on the proposal's matrix-Chernoff scope decision).

**Changes:** `GraphTheory.Foster` (5 declarations, all proved): `card_filter_eigvalOf_laplacian_eq_zero` (exactly one eigenbasis index lies in the kernel — at most one by orthonormality against the one-dimensional kernel `laplacian_kernel_eq_span_onesVec`, at least one because `onesVec` is a nonzero kernel vector whose nonzero-eigenvalue components die by self-adjointness), `effectiveResistance_eq_sum_eigbasis` (`R u v = ∑_k (v_k u − v_k v)²/λ_k` over nonzero eigenvalues; energy identity + `quadForm_eigvalOf` + `dotProduct_eigvecOf_mulVec`), `foster_theorem` (stated at full strength — no cardinality hypothesis; the `card V = 1` case degenerates to `0 = 0`), `leverageScore` (the Phase-B-facing importance-sampling object; junk below `2 ≤ card V` documented), and `sum_leverageScore_eq_two` (ordered scores sum to exactly `2`; unordered `1` — the probability-distribution statement, `hcard` as division guard). The proof swaps the double sum, evaluates the per-eigenvector Dirichlet sum to exactly `2 λ_k` (`laplacian_quadForm` + `quadForm_eigvecOf_self`), and counts the nonzero-eigenvalue indices — load-bearing on solvability, the kernel characterization, the spectral resolution, and eigenbasis orthonormality; an error in any breaks the proof. The `electrical-structure-crust.md` removal stands reconciled: it rejected the `L⁺` route, and no pseudoinverse is formed anywhere. QA `Foster_QA.lean` (53 declarations): `K₃`/`K₄`/`P₃`/3-leaf star, every resistance pinned by explicit potential witnesses (`K₄` via the general-pair potential `(e i − e j)/4`, proved to solve the unit demand for *every* pair through the entrywise `L = 4I − J` structure — all twelve ordered terms pinned by one lemma), ordered sums computed independently of the theorem (`4`/`6`/`4`/`6`) and cross-checked against `card V − 1` (`2`/`3`/`2`/`3`), the **double-counting factor refuted-on-omission on both cliques** (`4 ≠ 2`, `6 ≠ 3` — dropping the `/ 2` would falsify either side), non-edge pairs provably absent, leverage pinned (`1/3` edge / total `2` on `K₃`; `1/6` on `K₄`). Docs: module/QA docstrings, umbrella + its docstring, scoreboard (625/13/0, verification rows, milestone bullet), radar (subject axis 6 re-scored **4.0 → 4.5** per protocol — a new theorem family (global network identities), not packaging; QA 625/29; weakest-axes paragraph; re-scoring log), README (625, axis-6 cell 4.5, Foster added to the proved list and module table), SGT index map (5 new rows), backlog item 7, proposal Phase A delivery record + status header, `proposals/README.md` (row moved to Delivered; progress note rewritten — decidable-certificates Step 0 is now the top High item). Implementation notes: `Pi.single` applied at an index leaves its dependent function type unresolved in standalone statements — write function-level `Pi.sub` and distribute with `Pi.sub_apply` (the repo's own demand-equation style); `Finset.sum_div` is stated in the expanding direction, so collapsing sums needs `← Finset.sum_div`; conditional per-pair lemmas do not fire reliably as `simp only` rewrites after a fixture def is unfolded — use a per-term `hpair` case lemma or two-phase simp (`simp only [value lemmas]` before `simp [fixture]`).

**Decisive commands and outcomes:** `lake env lean` on `GraphTheory.Foster` and `Foster_QA` — both zero errors, zero warnings (five QA lemmas carry targeted `set_option linter.unreachableTactic/unusedTactic false in` where `simp` closes some `fin_cases` branches); `#print axioms` on all four public theorems — only the three standard axioms; `lake build Scaffold.Mathlib.GraphTheory.Foster` ✔; full `lake build` ✔ (2181 targets); all 29 QA modules batch-elaborated, zero errors (only the eight documented pre-existing section-variable warnings in untouched modules); `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (625/13/0). Environment: the pruned Mathlib-oleans state recurred at run start; the recorded interpreted cache fetch restored 5387 oleans before any elaboration.

**Remaining risk:** the leverage-score def deliberately omits a cardinality parameter (matching the proposal sketch) — the junk value at `card V ≤ 1` is documented but not hypothesis-guarded; the corollary carries the guard. The axis-6 re-score to 4.5 rests on Foster opening the global-identity family; Matrix–Tree and the Kirchhoff loop/cut-space theorems remain absent, as does the resistance metric (triangle inequality, definiteness residual `R u v = 0 ↔ u = v`). Phase B stays blocked exactly as recorded — the leverage scores define its distribution but nothing probabilistic exists yet.

**Next handoff:** the Active table's top High item is now **decidable spectral certificates Step 0** (`decidable-spectral-certificates.md` — the adjacency-vs-Laplacian eigenvalue convention decision plus the ℚ-`decide` kernel spike, both scoped in the proposal; Step 1 must not begin before both are recorded). Medium alternatives: Fiedler Phase B (needs an operator decision on the admitted hard direction), mixing-time Step 1, Reversibility Phase A, Relative Entropy. The operator's Medium/Low rows and the untracked `why-sgt.md` preserved untouched; nothing committed.

## 2026-08-19T13:24:13Z — Decidable spectral certificates, step 0 (convention decision + ℚ-decide spike)

**Run:** `20260819T132413Z-run-1`  
**Session:** `ses_fe5d101b1ffeAcbY8TX1lYR3o7`  
**Status:** in-progress  
**Milestone:** Open the Active table's top High item `proposals/decidable-spectral-certificates.md` at its recorded gate: **step 0** — decide the adjacency-vs-Laplacian eigenvalue convention for `expander_mixing_lemma` (survey-backed, recorded in the proposal with a restated theorem signature) and spike whether plain kernel `decide` actually verifies a rational spectral certificate on a concrete `Fin n` graph (n = 4 and n = 6), the two unaddressed gaps the proposal itself names as blocking Step 1. If both land cleanly, deliver Step 1's smallest independently useful Lean slice (the `edgeWeight` discrepancy core and the indicator decomposition) in the new `GraphTheory.Expander`, following the electrical-flow steps 0–1 precedent. Zero new axioms (13 unchanged); steps 2–4 not started this run.

## 2026-08-19T14:30:11Z — Decidable-certificates steps 0–1 delivered (convention + decide spike + the Expander discrepancy core)

**Run:** `20260819T132413Z-run-1`  
**Session:** `ses_fe5d101b1ffeAcbY8TX1lYR3o7`  
**Status:** completed  
**Milestone:** The Active table's top High item `proposals/decidable-spectral-certificates.md`, its Step 0 gate (convention decision + ℚ-`decide` spike, both recorded in the proposal) and Step 1 (`GraphTheory.Expander`: `edgeWeight`, the centered-indicator decomposition, and the `d`-regular main-term split — the discrepancy core of the Expander Mixing Lemma). Zero new axioms (13 unchanged); steps 2–4 not started.

**Changes:** **Step 0** — (1) convention decided **Laplacian-first through the `d`-regular bridge**, with the survey evidence recorded (no adjacency-eigenvalue interface exists in the codebase; the certificate half is already Laplacian; the generic symmetric engine applies to adjacency for free, so the bridge `A = d•1 − L` needs no new interface; no named consumer wants adjacency eigenvalues) and the restated `expander_mixing_lemma` signature pinned in Laplacian terms (the `√`-form as the mathematical statement, squaring recorded as a Step-2 implementation option); (2) the ℚ-`decide` spike found a genuine wall, not a slow path: plain kernel `decide` **cannot** verify the proposal's ℚ-arithmetic certificate because `Rat` operations never unfold in elaborator reduction (`((2:ℚ) + 2) = 4` is already stuck at `(Rat.add 2 2).num` — ℚ literals are opaque kernel literals; controls `Nat.gcd`, ℕ-sums over `Fin`, and ℤ arithmetic all decide fine; `#eval` works but is native, not kernel-checked; `native_decide` excluded by the proposal's own rule) — adopted fallback recorded: the **integer cross-multiplied twin** (`rawNumer ≤ 2 * bound * denom`, all data in ℤ), kernel-decided clean on `C₄` (`Fin 4`, attained `λ₂ = 2`, accept + all three reject paths) and `C₆` (`Fin 6`, attained `λ₂ = 1`) plus the fractional-bound clearing form, ~sub-second decide overhead; (3) Ramanujan QA scope resolved to the existing `Kₙ`/`Cₙ` fixtures (both small Ramanujan instances). **Step 1** — the new `GraphTheory.Expander` (all proved): `edgeWeight` with degenerate/degree-sum interfaces, the hypothesis-free matrix form `edgeWeight_eq_dotProduct`, `edgeWeight_symm`; `indicatorVec`/`centeredIndicator` with the decomposition and **unconditional** orthogonality to `onesVec` (empty-type case handled, no `Nonempty` hypothesis); and the headline `edgeWeight_eq_regular_add_centered` (`e(S,T) = d·|S|·|T|/n + centered cross term`), symmetry load-bearing through `Matrix.dotProduct_mulVec`'s transpose and regularity through the `A *ᵥ onesVec = d` evaluation. QA `Expander_QA.lean` (22 declarations, fresh `C₄` fixture): all values from the raw definitions, the decomposition instantiated on adjacent (`1 = 1/2 + 1/2`) and opposite (`0 = 1/2 − 1/2`) cuts with independently computed cross terms, and three negative witnesses (main-term-only refuted `0 ≠ 1/2`; wrong degree `1 ≠ 3/4`; asymmetric weight breaks cut symmetry `2 ≠ 1`). Docs: module/QA docstrings, umbrella, scoreboard (647/13/0, verification rows, milestone bullet), radar (QA 647/30 with the new QA kind; QA axis **held at 4.0** per protocol with the hold recorded — decisions and plumbing, the parametric-QA gap untouched), README (647, cuts-and-expansion row), SGT index map (new `Expander` section), proposal Step-0 record + Step-1 delivery record, `proposals/README.md` progress note.

**Decisive commands and outcomes:** `lake env lean` on `GraphTheory.Expander` and `Expander_QA` — both zero errors, zero warnings; `#print axioms` on all seven public theorems — only `propext, Classical.choice, Quot.sound`; `lake build` of both targets ✔; full `lake build` ✔ (2182 targets); all thirty QA modules batch-elaborated, zero errors; `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (647/13/0). Environment: the pruned-oleans state recurred (mathlib empty; Batteries only partially restored by the cache fetch — an explicit `lake build Batteries` was needed before `Mathlib.Tactic` imports would resolve); the full cold build elapsed ~33 min; recorded in the plan for the next run. Spike implementation notes recorded: `.decide` field notation is invalid on `Prop`-typed expressions (use `decide (...)`); `omit`/`set_option ... in` must precede doc comments.

**Remaining risk:** the integer-twin re-scoping changes Step 3's deliverable shape (ℚ soundness statement + ℤ twin + proved bridge lemma); the twin has been spiked but its soundness bridge is unproved. The Step-2 bridge (eigenvalue hypothesis → Rayleigh-form operator bound on `x ⊥ 1`) is unbuilt and is the next load-bearing dependency; the radar holds reflect that the mixing lemma itself is not yet stated. The restated EML signature is recorded but not yet elaborated.

**Next handoff:** proposal Step 2 — the Expander Mixing Lemma: the bridge layer (eigenvalue hypothesis → `|xᵀAx| ≤ μ xᵀx` on `x ⊥ 1` via the eigenbasis/Courant–Fischer machinery), the centered-cross-term bound by Cauchy–Schwarz, packaged at the restated signature; then Step 3 (certificate module with the ℤ twin + soundness bridge) and Step 4 (QA incl. kernel-`decide` demonstrations). Medium alternatives queued (Fiedler Phase B — decision-gated; mixing-time Step 1; Reversibility Phase A; Relative Entropy). The operator's untracked `adversarial.md`, `sgt-gaps.md`, and `why-sgt.md` preserved untouched; nothing committed.

## 2026-08-19T15:01:42Z — Decidable spectral certificates, Step 2 (Expander Mixing Lemma)

**Run:** `20260819T150142Z-run-1`  
**Session:** `ses_fe57b012dffeLl1r2RrcTtsu8E`  
**Status:** in-progress  
**Milestone:** Deliver Step 2 of `proposals/decidable-spectral-certificates.md` (top High item): the Expander Mixing Lemma as hard crust — the bridge from the Laplacian-form eigenvalue hypothesis to the Rayleigh-form operator bound on `1⊥`, the centered cross-term bound, and the packaged restated `expander_mixing_lemma` signature, with C₄ QA including equality sharpness witnesses. Leverage: the theorem the proposal exists to deliver and the layer Step 3's certificates compose with.

**Changes:** intent recorded; Lean work starting (generic `evals`-last facts in `Spectral.lean`, bridge layer + headline in `GraphTheory/Expander.lean`, QA extension in `SpectralGraph/Expander_QA.lean`).

## 2026-08-19T16:25:49Z — Decidable spectral certificates Step 2 delivered (the Expander Mixing Lemma)

**Run:** `20260819T150142Z-run-1`  
**Session:** `ses_fe57b012dffeLl1r2RrcTtsu8E`  
**Status:** completed  
**Milestone:** Step 2 of `proposals/decidable-spectral-certificates.md` (top High item): the Expander Mixing Lemma proved as hard crust — the classical discrepancy bridge between Laplacian spectral gaps and combinatorial pseudorandomness, and the layer Step 3's certificates compose with.

**Changes:** `GraphTheory.Expander` extended with the Step-2 bridge layer and the headline `expander_mixing_lemma` (at the Step 0 restated `√` signature, minus the found-unnecessary `hloop` hypothesis — deviation recorded in the proposal); `GraphTheory.Spectral` gains the generic `eigvalOf_le_evals_last`, `quadForm_le_evals_last` (top Rayleigh domination, multiplication form), and a public `dotProduct_self_pos`; `Expander_QA.lean` +19 declarations (derived spectral hypothesis, EML instantiations, sharpness witnesses); scoreboard, radar (axis 4 re-scored 3.5 → 4.0, logged; QA held at 4.0 per protocol), README (666 counts, axis-4 cell), SGT index map, umbrella, and both proposal records updated.

**Verification:** `lake env lean` on both changed public modules and the QA module — zero errors, zero warnings; `#print axioms` on the nine new public theorems — only `propext, Classical.choice, Quot.sound` (zero new axioms, count stays 13); full `lake build` ✔ (2182 targets); all thirty QA modules batch-elaborated, zero errors; `lint_axioms`, `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (666/13/0).

**Remaining risk:** the derived-`μ` QA derives `μ = 2` via bounds rather than exact spectrum pinning on `C₄` (exact pins are Step 4's planned route); `Mathlib.cons_val`-style literal evaluation required the pinned simp set (`cons_val_two`, no `vecTail` unfolding) — recorded here for future QA on 4-vertex fixtures.

**Next handoff:** proposal Step 3 — the certificate module (ℚ-facing soundness statement + the kernel-verifiable integer cross-multiplied twin, bridged by a proved cross-multiplication lemma), then Step 4 QA. The operator's concurrent changes (untracked `governance/ADVERSARIAL_REVIEW.md`, six new untracked proposals including `directed-graph-operators.md`, and edits to `1_STRATEGY.md`, `6_SGT_BACKLOG.md`, `CONTRIBUTING.md`, `admit-perron-frobenius.md`, `electrical-flow-routing.md`) were observed mid-run and preserved untouched.

## 2026-08-19T16:55:00Z — Decidable spectral certificates, Step 3 (certificate module)

**Run:** `20260819T164730Z-run-1`  
**Session:** `ses_fe5173fcbffeWuvtINn3O7CbOt`  
**Status:** in-progress  
**Milestone:** Deliver Step 3 of `proposals/decidable-spectral-certificates.md` (top High item): the computable certificate module — the ℚ-facing checker with its soundness theorem `lambda2_le_of_certificate` (a load-bearing consumer of the proved `lambda2_variational`), the kernel-verifiable ℤ cross-multiplied twin, and the proved bridge between them — plus the C₄ kernel-`decide` QA core. Leverage: closes the extraction gap the proposal exists for; first end-to-end proof-carrying-certificate chain (integer arithmetic → kernel `decide` → proved ordered-field bridge → real spectral center).

**Changes:** intent recorded in the execution plan; environment restored (pruned oleans state recurred; interpreted cache fetch re-applied, 5685 files unpacked); Lean work starting in `GraphTheory/SpectralCertificates.lean` and `SpectralGraph/SpectralCertificates_QA.lean`.

## 2026-08-19T17:58:00Z — Decidable spectral certificates Step 3 delivered (the certificate module)

**Run:** `20260819T164730Z-run-1`  
**Session:** `ses_fe5173fcbffeWuvtINn3O7CbOt`  
**Status:** completed  
**Milestone:** Step 3 of `proposals/decidable-spectral-certificates.md` (top High item): the computable certificate module — the ℚ specification checker with its soundness theorem `lambda2_le_of_certificate` (the flagship load-bearing consumer of the proved `lambda2_variational`), the kernel-verifiable ℤ cross-multiplied twin and its fractional variant, and the proved cross-multiplication bridges — plus the C₄ kernel-`decide` QA core. Leverage: closes the proposal's extraction gap inside Lean; first end-to-end proof-carrying-certificate chain (integer arithmetic → kernel `decide` → proved bridge → real spectral bound).

**Changes:** new `GraphTheory.SpectralCertificates` (transport layer with the `rfl` hinge `algebraMap_apply`; `lambda2_le_rayleigh` consumer form; the ℚ checker + soundness; the ℤ twins; sound-and-complete integer bridge + fractional cross-multiplication bridge with the `0 < den` hypothesis external — genuinely needed for the reverse direction; kernel-facing corollaries via the `subst`-based `lambda2_le_of_matrix_eq` transfer); new `SpectralCertificates_QA.lean` (22 declarations); umbrella, SGT index map (new section, 11 rows), scoreboard (688/13/0 + verification rows + milestone bullet), radar (axis 7 re-scored 3.0 → 3.5, logged; QA count 688/31, held at 4.0 per protocol), README, proposal Step-3 delivery record, and `proposals/README.md` (High row → Step 4) updated.

**Verification:** `lake env lean` on both new modules — zero errors, zero warnings; `#print axioms` on the eight headline public theorems and five key QA theorems — only `propext, Classical.choice, Quot.sound` (zero new axioms, count stays 13); all thirty-one QA modules batch-elaborated, zero errors; full `lake build` ✔ (2183 targets, one more than before; 6:27 wall); `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (688/13/0).

**Remaining risk:** the C₄ QA pins the certified bound to the test vector's exact Rayleigh quotient and witnesses accept/reject sharpness, but `lambda2 (C₄) = 2` itself is not pinned (the exact lower bound is Step 4's natural completion, with the `C₆`/Ramanujan fixtures); the fractional bridge's reverse direction needs the external `0 < den` (recorded in the theorem docstring); the ℚ checker remains evaluation-unreachable by the kernel by design — every consumer must go through a bridge, which is the recorded architecture, not a defect. Environment: the pruned-oleans state recurred at run start; the recorded interpreted cache fetch re-applied before elaboration; the full build replayed the trace chain cleanly.

**Next handoff:** proposal Step 4 — QA and extraction demonstration: `C₆` kernel-`decide` demonstrations, the `Kₙ`/`Cₙ` Ramanujan fixture family (drop-if-awkward fallback per the Step 0 scope decision), exact spectrum pins making the certified bounds' sharpness checkable against `lambda2` itself, and the Acceptance-Criterion-4 documentation notes (traction-plan included). The operator's other queued items (the new resolvent-calculus/Tikhonov/band-projector High rows with their Step-0 spikes; Fiedler Phase B still decision-gated) are unchanged; nothing committed.

## 2026-08-19T18:57:27Z — Decidable spectral certificates, Step 4 (QA and extraction demonstration)

**Run:** `20260819T185727Z-run-1`  
**Session:** `ses_fe4a17e43ffeA287ckVygl1V11`  
**Status:** in-progress  
**Milestone:** Deliver Step 4 of `proposals/decidable-spectral-certificates.md` (top High item, the program's final step): QA expansion — the `C₆` kernel-`decide` demonstrations, the `Kₙ`/`Cₙ` Ramanujan fixture family per the Step 0 scope decision, exact spectrum pins (`lambda2 (C₄) = 2` — the C₄ QA pins the quotient, not the value; the exact lower-bound pin via a C₄ Poincaré inequality is this step's named completion), and the Acceptance-Criterion-4 documentation notes (scoreboard/radar/traction-plan). Leverage: makes the Step-3 certificate chain's bounds witnessed-sharp against `lambda2` itself. Zero new axioms (13 unchanged); QA-only changes.

**Changes:** intent recorded; environment verified healthy at run start (5382 Mathlib oleans present — no cache fetch needed this run); Lean QA work starting in `SpectralCertificates_QA.lean` and `Expander_QA.lean`.

## 2026-08-19T19:28:41Z — Decidable spectral certificates Step 4 delivered; program complete (QA and extraction demonstration)

**Run:** `20260819T185727Z-run-1`  
**Session:** `ses_fe4a17e43ffeA287ckVygl1V11`  
**Status:** completed  
**Milestone:** Step 4 of `proposals/decidable-spectral-certificates.md` (top High item, the program's final step): QA and extraction demonstration — the `C₆` kernel-`decide` demonstrations at the second required size, exact spectrum pins making the certified bounds witnessed-sharp against `lambda2` itself (`lambda2 (C₄) = 2` via a Poincaré inequality through the *lower* half of `lambda2_variational`), the `Kₙ`/`Cₙ` Ramanujan fixture family per the Step 0 scope decision, and the Acceptance-Criterion-4 documentation notes (scoreboard/radar/traction-plan). With this step all five steps (0–4) are delivered and the proposal's acceptance criteria 1–4 are met. Zero new axioms (13 unchanged); QA-only changes.

**Changes:** `SpectralCertificates_QA.lean` (+17 declarations, 39 in file): the `C₆` fixture and the whole certificate chain kernel-decided (accept at the attained bound `1`, reject at `0`, fractional `3/2` accepted / `1/2` rejected, arithmetic pinned from the raw definitions — `rawNumer = 8`, `denom = 4`, quotient `8/(2·4) = 1` — the ℚ specification reached only through the proved bridge, end-to-end `lambda2 (C₆) ≤ 1` and `≤ 3/2`); the `C₄` Poincaré inequality (`2‖x‖² ≤ xᵀLx` on `1⊥`, by the Wirtinger identity `E = 2Σx² + 2(x₀+x₂)²` under `Σx = 0`) consumed through `le_csInf` — the proved `lambda2_variational`'s first QA consumer in the `≥` direction — pinning `lambda2 (C₄) = 2` exactly, with `cert4_certificate_exact_QA` stating the chain's exact tightness (the kernel checker accepts precisely at the true `lambda2` and rejects the integer bound `1` below it). `Expander_QA.lean` (+47, 88 in file): the exact `C₄` pins (`λ₂ = 2` Poincaré-below/test-vector-above; `λ_max = 4` by the alternating vector through the generic `quadForm_le_evals_last`), so `μ(C₄) = 2` exactly and the Ramanujan bound `2√(d−1)` is attained with equality; the `K₃` fixture (entry-table + the exact clique energy identity `xᵀLx = 3‖x‖² − (Σx)²`, pinning `λ₂ = λ_max = 3` and `μ(K₃) = 1` — strictly Ramanujan — with the EML attained exactly on both cuts tested, both sides computing to `2/3`); the `C₆` EML with derived `μ ≤ 2` (test vector `λ₂ ≤ 1`, the energy identity `xᵀLx = 4‖x‖² − Σ_edges(xᵢ+xᵢ₊₁)²` for `λ_max ≤ 4`, PSD below), attained exactly on the alternating cut `({0,2,4},{0,2,4})` (both sides compute to `3`). Docs: scoreboard (752/13/0, verification rows + step-4 milestone bullet), radar (QA axis 752/31 with the exact-pin/second-size kinds described; subject axes 4 and 7 evidence extended with scores **held at 4.0/3.5 per protocol** and the holds logged; remaining-gap note updated), traction plan (dated note recording that the extraction-gap revisit precondition it names is now met — planning provenance, respecting the document's clean-room boundary), README (752), proposal Step-4 delivery record + status header (program complete), and `proposals/README.md` (row moved to the Delivered table; progress note rewritten — the three `sgt-gaps`-promoted High rows are now the top of the Active table).

**Decisive commands and outcomes:** `lake env lean` on both changed QA modules — zero errors, zero warnings; `#print axioms` on all 22 new headline theorems — only `propext, Classical.choice, Quot.sound` (zero new axioms, count stays 13); all thirty-one QA modules batch-elaborated, zero errors; full `lake build` ✔ (2183 targets); `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (752/13/0). Environment healthy at run start (full Mathlib oleans present — the pruned-oleans state did not recur).

**Remaining risk:** the `C₆` Ramanujan statement is the inequality (`μ ≤ 2`), not the exact pin `μ = 2` — the exact value needs the `C₆` Wirtinger/Poincaré constant (genuinely nonlinear, not attempted; recorded in the delivery record as the named residual). The exact pins exist only on `C₄`/`K₃`; nothing generalizes the Poincaré inequalities beyond fixtures, and the radar's QA-axis named gap (parametric/randomized QA) is untouched — the QA axis hold reflects that. Implementation note for future 6-vertex QA (recorded in the proposal): the `cons_val` simp family stops at index four — a `rfl`-provable `vecCons_val_five` helper bridges index five when both indices are `OfNat`-literals from sum expansion, but `fin_cases`-produced `Fin.mk` row indices defeat the chain (row sums proved per row by `show` up to defeq instead); ℤ structural facts evaluate by `decide` where ℝ ones cannot.

**Next handoff:** the Active table's top High rows are now the three `sgt-gaps`-promoted items with their recorded entry points — Resolvent Calculus for PSD Matrices (Step 0 first: the unverified `IsSelfAdjoint.spectralRadius_eq_nnnorm` thread for the operator-norm bridge), Tikhonov Regularization in the Laplacian Eigenbasis (no gate), and Spectral Band Projectors (no gate — the difference of two existing `spectralProjector` calls). Medium rows queued behind them (Fiedler Phase B still decision-gated; mixing-time Step 1; Reversibility A/B; Relative Entropy; Perron–Frobenius + directed operators; discharge-perturbation; approximate spectral projection). Nothing committed.

## 2026-08-19T20:32:40Z — Resolvent calculus steps 0–1 (norm-bridge spike + invertibility/resolvent identity)

**Run:** `20260819T203139Z-run-1`  
**Session:** `ses_fe44b2290ffeeaVzXvL7dNQOvY`  
**Status:** in-progress  
**Milestone:** Deliver Steps 0 and 1 of `proposals/resolvent-calculus-psd.md` (top High item). Step 0's spike is already decisive: the C*-algebra thread `IsSelfAdjoint.spectralRadius_eq_nnnorm` is structurally inapplicable to real matrices (`CStarAlgebra` extends `NormedAlgebra ℂ A`; elaboration-verified missing), so the operator-norm bridge falls back to the from-scratch eigenbasis route (Parseval + eigenaction + `l2_opNorm` bookkeeping). Step 1: `A + t•1` invertible for PSD symmetric `A` and `0 < t`, plus the resolvent identity. Leverage: the bridge is a one-time cost shared by the resolvent norm/Lipschitz bounds (items 2/4) and the `discharge-perturbation-axioms.md` Weyl target. Zero new axioms (13 unchanged).

**Changes:** intent recorded in the execution plan; environment restored (pruned oleans recurred — interpreted cache fetch re-applied, 5387 Mathlib oleans); Lean work starting in `Analysis/OperatorTheory/Resolvent.lean` and `QA/OperatorTheory/Resolvent_QA.lean`.

## 2026-08-19T21:46:39Z — Resolvent calculus steps 0–1 delivered (operator-norm bridge + invertibility/resolvent identity)

**Run:** `20260819T203139Z-run-1`  
**Session:** `ses_fe44b2290ffeeaVzXvL7dNQOvY`  
**Status:** completed  
**Milestone:** Steps 0 and 1 of `proposals/resolvent-calculus-psd.md` (top High item). Step 0's spike was decisive: the C*-algebra thread `IsSelfAdjoint.spectralRadius_eq_nnnorm` is structurally inapplicable to real matrices (`CStarAlgebra` extends `NormedAlgebra ℂ A`/`StarModule ℂ A`; `NormedAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℝ)` fails to synthesize — elaboration-verified), so the operator-norm bridge was proved from scratch per the proposal's own contingency: `l2OpNorm_eq_max_abs_evals` (`‖M‖ = max |evals hM 0| |evals hM last|` for every real symmetric matrix) with both directions (`abs_eigvalOf_le_l2OpNorm` via the unit eigenvector through `toEuclideanCLM`; `l2OpNorm_le_of_abs_eigvalOf_le` via Parseval + the eigenaction identity), consuming the new center mirror lemma `evals_first_le_eigvalOf`. Step 1: `M + t•1` invertible for any matrix with nonnegative quadratic form and `t > 0` (kernel-vector route, **no symmetry needed** — a recorded strengthening) plus the `t = 1` instance, and the resolvent identity `(A+1)⁻¹ − (B+1)⁻¹ = (A+1)⁻¹(B−A)(B+1)⁻¹`. The bridge is the shared route for Step 2's bounds and the `discharge-perturbation-axioms.md` Weyl target. Zero new axioms (13 unchanged).

**Changes:** new `Analysis.OperatorTheory.Resolvent` (8 public theorems, all proved; the Step-0 route decision recorded in the module docstring); one generic addition to `GraphTheory.Spectral` (`evals_first_le_eigvalOf`); new `QA/OperatorTheory/Resolvent_QA.lean` (30 declarations: the `!![2,1;1,2]` spectrum pinned from trace/det/sortedness with `‖mat2‖ = 3` pinned by both bridge directions, the `¬(‖mat2‖ ≤ 1)` negative witness, shifted-PSD invertibility cross-checked against computed determinants with the unshifted-Laplacian-determinant-`0` shift guard, and the resolvent identity checked against both-sides-computed literal matrices); umbrella, scoreboard (782/13/0 + verification rows + milestone bullet; `OperatorTheory` a new QA domain), radar (axis 2 evidence extended, score held at 3.5; QA 782/32 held at 4.0; both holds logged), README (782 + proved list), Mathlib coverage map (the operator-norm row's verified finding), perturbation index map (Resolvent section), proposal Step-0 record + Step-1 delivery + status header, and `proposals/README.md` (High row → Step 2). The operator's concurrent edits (`governance/ADVERSARIAL_REVIEW.md`, `proposals/discharge-perturbation-axioms.md`) preserved untouched; nothing committed.

**Decisive commands and outcomes:** `lake env lean` on the three changed Lean modules — zero errors, zero warnings; `#print axioms` on all 8 public theorems + 6 QA headlines — only `propext, Classical.choice, Quot.sound`; all thirty-two QA modules batch-elaborated, zero errors; full `lake build` ✔ (2184 targets, "Build completed successfully"); `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (782/13/0). Environment: the pruned-oleans state recurred at run start (Mathlib build dir empty); the recorded interpreted cache fetch restored 5387 before elaboration; the full build replayed the Mathlib trace residue (~35 min).

**Remaining risk:** the bridge is stated for symmetric matrices through the `L2OpNorm` scoped instance — its consumption by the Weyl-discharge target will need the norm's statement-shape match re-checked when that run starts (the axiom's `‖E‖` was elaborated under the same scoped instance, so they should agree definitionally, but this is asserted, not yet consumed-in-anger); Step 2's eigenvalue transfer for `M + t•1`/`(A+1)⁻¹` (shared eigenvectors, shifted/inverted eigenvalues, and the sorted-spectrum bookkeeping) is unwritten and is the natural next cost; the QA fixtures are 2×2 only (the norm bridge is not exercised on a multi-eigenvalue non-attaining fixture).

**Next handoff:** Resolvent Step 2 — `‖(A+1)⁻¹‖ ≤ 1` and the Lipschitz bound `‖(A+1)⁻¹ − (B+1)⁻¹‖ ≤ ‖A−B‖` (the latter is submultiplicativity `l2_opNorm_mul` + item 2 twice once the norm bound lands), then Step 3's one-line injectivity; or the ungated High rows (Tikhonov, Band Projectors). Medium rows queued behind them. Implementation notes for future L2OpNorm work are recorded in the execution plan (transport spine lemmas, the `rw`-with-bare-`1` trap, entrywise-vs-literal matrix computation, the `(2 : ℝ)` ascription for matrix smul).

## 2026-08-19T22:38:53Z — Resolvent calculus Step 2 (norm bound + Lipschitz bound)

**Run:** `20260819T223853Z-run-1`  
**Session:** `ses_fe3d60017ffeaZgd5m1Hx3kWAu`  
**Status:** in-progress  
**Milestone:** Deliver Step 2 of `proposals/resolvent-calculus-psd.md` (top High item): the norm bound `‖(A+1)⁻¹‖ ≤ 1` and the Lipschitz bound `‖(A+1)⁻¹ − (B+1)⁻¹‖ ≤ ‖A−B‖`, zero new axioms (13 unchanged). Planned route deviation to record at delivery: the energy route (`y = (M+t•1)⁻¹x` gives `t‖y‖² ≤ quadForm M y + t‖y‖² = yᵀx ≤ ‖y‖‖x‖` by dot-product Cauchy–Schwarz, packaged via the Step-0 `opNorm_le_bound` spine) instead of the sketched eigenvalue transfer — strictly stronger (no symmetry hypothesis, general `t`), cheaper; the sorted-eigenvalue transfer stays a named residual. The Lipschitz bound stays load-bearing on Step 1 (invertibility + the resolvent identity).

**Changes:** intent + route decision recorded in the execution plan; environment restore started (the pruned Mathlib-oleans state recurred; the recorded interpreted cache fetch is running in the background). Lean work to follow in `Analysis/OperatorTheory/Resolvent.lean` and `QA/OperatorTheory/Resolvent_QA.lean`.

## 2026-08-19T23:56:55Z — Resolvent calculus Step 2 delivered (norm bound + Lipschitz bound)

**Run:** `20260819T223853Z-run-1`  
**Session:** `ses_fe3d60017ffeaZgd5m1Hx3kWAu`  
**Status:** completed  
**Milestone:** Step 2 of `proposals/resolvent-calculus-psd.md` (top High item) delivered as pure hard crust, zero new axioms (13 unchanged; `#print axioms` on the three new public theorems reads only `propext, Classical.choice, Quot.sound`): the proposal's items 2 and 4. **Recorded route deviation:** the energy route instead of the sketched eigenvalue transfer — for `y = (M+t•1)⁻¹x`, `t‖y‖² ≤ quadForm M y + t‖y‖² = y ⬝ᵥ x ≤ ‖y‖‖x‖` (dot-product Cauchy–Schwarz through the bridge's own `opNorm_le_bound` spine) gives the **strictly stronger general-`t`** `l2OpNorm_inv_add_smul_one_le_inv_of_quadForm_nonneg` (`‖(M+t•1)⁻¹‖ ≤ t⁻¹`, **no symmetry hypothesis**; the energy inequality itself holds for any `t`), the `t=1` instance `l2OpNorm_inv_add_one_le_one_of_quadForm_nonneg`, and the **Lipschitz bound** `l2OpNorm_resolvent_sub_le_of_quadForm_nonneg` (`‖(A+1)⁻¹ − (B+1)⁻¹‖ ≤ ‖A−B‖`) — Step-1 resolvent identity + the scoped `NormedRing` submultiplicativity + the norm bound twice, load-bearing on Step 1's invertibility and identity. The sorted-eigenvalue transfer stays a named residual (mixing-time is the named consumer).

**Changes:** `Analysis.OperatorTheory.Resolvent` extended (3 public theorems + 2 private helpers; docstring to steps 0–2); `QA/OperatorTheory/Resolvent_QA.lean` +45 declarations (75 in file): the norm bound **attained with route agreement** (`‖(L(K₂)+1)⁻¹‖ = 1` exactly — the energy-route theorem and the eigenvalue-bridge route independently meeting at the pinned spectrum `{1/3,1}`; `‖(L+2•1)⁻¹‖ = 1/2` exactly at `{1/4,1/2}`), the Lipschitz instance with both sides independently pinned (`2/3 ≤ 2`), the **shift guard** (invertible PSD `(1/4)I` unshifted has `‖A⁻¹‖ = 4 > 1` — the proposal's QA item 3), and the **hypothesis guard** (`-(3/4)I`'s shift is invertible with inverse norm `4 > 1`, the violated quadForm exhibited at `-3/4 < 0`). Records: scoreboard (827/13/0, verification rows + milestone bullet), radar (axis-2 evidence completed, **held at 3.5** — family completion; QA 827/32 **held at 4.0**; both holds logged; proved-depth extended), README (827, proved list), perturbation index map (+3 rows; deferred narrowed to Step-3 injectivity), proposal Step-2 delivery record + open-next-step (Step 3), `proposals/README.md` (High row → Step 3). The operator's concurrent untracked `governance/mathlib-standards.md` preserved untouched; nothing committed.

**Decisive commands and outcomes:** `lake env lean` on the changed public module and its QA — zero errors, zero warnings; `#print axioms` on 3 public + 8 QA headline theorems — three standard axioms only; all thirty-two QA modules batch-elaborated — zero errors (only the eight documented pre-existing section-variable warnings in untouched modules); **full `lake build` ✔ (2184 targets, exit 0)**; `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (827/13/0). Environment: the pruned-oleans state recurred at run start; the recorded interpreted cache fetch restored 5685 oleans (~4 min) before any elaboration; fast-`lean -o` olean production used during iteration. Implementation notes (coercion/parse traps: `prod_eq_multiset_prod`, `simpa`-only coercion removal in `det_eq_prod_eigenvalues`, `abs_of_nonneg` with explicit side proofs, `-2/3` and `1/4 * 1/2` parse shapes, the generalized two-point pin) recorded in the execution plan.

**Remaining risk:** the QA fixtures are 2×2 (the bounds are not exercised on a larger PSD family — though attainment and both guards are witnessed); the norm bound's `t⁻¹` form assumes exact arithmetic (no rounding model — out of scope); the Weyl-discharge target still needs its own additive-bound spike (the bridge and the now-proved submultiplicativity pattern are available to it).

**Next handoff:** Resolvent Step 3 — injectivity (`A ≠ B → (A+1)⁻¹ ≠ (B+1)⁻¹`, one line from the Step-1 identity), completing the program; or the ungated High rows (Tikhonov Regularization, Spectral Band Projectors). Medium rows queued behind them.

## 2026-08-20T01:02:00Z — Resolvent Step 3: injectivity (program completion)

**Run:** `20260820T010200Z-run-1`  
**Session:** `ses_fe35034fbffezAyn8Uof2QyQBn`  
**Status:** in-progress  
**Milestone:** Resolvent Calculus for PSD Matrices Step 3 — the proposal's item 5, `A ≠ B → (A+1)⁻¹ ≠ (B+1)⁻¹`, the recorded open next step of the Active table's top High item and the program's final step. Zero new axioms; load-bearing on Step 1's resolvent identity and invertibility theorem.

**Changes:** intent recorded in the execution plan; environment restored (pruned-oleans state recurred at run start — the recorded interpreted cache fetch re-applied, 5685 Mathlib oleans unpacked); Lean work starting in `Analysis/OperatorTheory/Resolvent.lean` and `QA/OperatorTheory/Resolvent_QA.lean`.

## 2026-08-20T03:08:46Z — Resolvent Step 3 delivered; program complete

**Run:** `20260820T010200Z-run-1`  
**Session:** `ses_fe35034fbffezAyn8Uof2QyQBn`  
**Status:** completed  
**Milestone:** Resolvent Calculus for PSD Matrices Step 3 — injectivity (`A ≠ B → (A+1)⁻¹ ≠ (B+1)⁻¹`), the recorded open next step of the Active table's top High item and the program's final step; zero new axioms, load-bearing on Step 1's resolvent identity and invertibility theorem.

**Changes:** `Analysis.OperatorTheory.Resolvent` gained the Step-3 section: `eq_of_inv_add_one_eq_inv_add_one` (the core form — equal resolvents of `+1`-invertible matrices force equal matrices, by the proposal's recorded route: the Step-1 identity collapses to `0`, and multiplying through by `A + 1` / `B + 1` cancels both invertible outer factors), `resolvent_map_injective_of_quadForm_nonneg` (the item-5 shape on quadForm-nonneg matrices), and `inv_add_one_eq_inv_add_one_iff_of_quadForm_nonneg` (the certificate iff). QA `OperatorTheory/Resolvent_QA.lean` +19 (94 in file): two distinct PSD pairs instantiated (`lap2` vs `0`; `lap2` vs `mat2` with `mat2`'s PSD proved from `xᵀ(mat2)x = (x₀+x₁)² + x₀² + x₁²`), both resolvents left-inverse-pinned (`(mat2+1)⁻¹ = (1/8)!![3,−1;−1,3]` a new fixture), entry-verified distinctness (`1/3 ≠ 0`, `2/3 ≠ 3/8`), bridge lemmas from the theorem's output to the numeric facts, the iff consumed contrapositively, and the **invertibility guard**: the hypothesis-free implication refuted at `A = −1` vs `−1 + nilpotent` (both `+1` shifts singular — determinant `0` by a zero row — so both resolvents are the junk inverse `0` while the matrices differ).

**Decisive commands and outcomes:** `lake env lean` on the public module and QA module — zero errors, zero warnings; `#print axioms` on the three public and eleven QA theorems — only `propext, Classical.choice, Quot.sound`; all thirty-two QA modules batch-elaborated, zero errors (only the eight documented pre-existing section-variable warnings); **full `lake build` ✔ (2184 targets)**; `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (**846/13/0**).

**Verification:** program complete per the proposal's acceptance shape (all four steps, zero new axioms throughout — count stayed 13). Records updated: module/QA docstrings, scoreboard (verification rows, Step-3 interpretation bullet, provenance note), radar (axis 2 / proved-depth / QA evidence extended, scores **held** with the holds logged — completion within counted interfaces; QA count 846/32), README (846; proved list gains the injectivity), perturbation index map (3 new rows; Deferred Work updated), proposal (Step-3 delivery record, status header: program complete), `proposals/README.md` (row moved to Delivered; **Tikhonov Regularization is now the top High row**), execution plan.

**Remaining risk:** low — the step is one-consequence algebra over already-QA'd Step-1 interfaces, with the hypothesis guard refuted-on-omission. Environment note recorded in the scoreboard's provenance note: two `lake build` invocations killed at tool timeouts left the Mathlib olean dir wiped mid-replay (re-fetch restored; the final uninterrupted build passed), and a macOS case-insensitivity trap was diagnosed — creating `.lake/build/lib/lean/` shadows the toolchain's core `Lean/` tree; this repo's olean layout is `.lake/build/lib/Scaffold/...` directly.

**Next handoff:** the Active table's remaining High rows — Tikhonov Regularization (`tikhonov-shrinkage-filter.md`, no gate) and Spectral Band Projectors (`spectral-band-projectors.md`, no gate); the Medium rows stay queued behind them.

## 2026-08-20T03:39:00Z — Discharge the Weyl axiom: Step 0 spike, then retirement if positive

**Run:** `20260820T033600Z-run-1`  
**Session:** `ses_fe2c2a966ffe71pmKdtv7309zW`  
**Status:** in-progress  
**Milestone:** `proposals/discharge-perturbation-axioms.md` per explicit operator direction — `weyl_inequality` only. Step 0: spike the additive Weyl bound from `evals_min_max` and confirm composition with the proved `l2OpNorm_eq_max_abs_evals`; Step 1 only if positive: retire the axiom at its exact existing statement. `davis_kahan_sin_theta` and `cheeger_lower_bound` untouched. Zero new axioms; expected count 13 → 12.

**Changes:** intent recorded in the execution plan; environment verified healthy at run start (5387 Mathlib oleans present; no cache fetch needed); Lean spike starting in a scratch file against the delivered Courant–Fischer engine.

## 2026-08-20T04:12:00Z — Weyl axiom discharged: proved at its unchanged statement

**Run:** `20260820T033600Z-run-1`  
**Session:** `ses_fe2c2a966ffe71pmKdtv7309zW`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md`, Weyl target only (explicit operator direction). Step 0's additive-bound spike returned a decisive positive; Step 1 retired `weyl_inequality` from admitted axiom to proved theorem at the unchanged name, hypotheses, and conclusion. Explicit axioms **13 → 12**. `davis_kahan_sin_theta` and `cheeger_lower_bound` untouched.

**Changes:** `GraphTheory.Spectral` gained the bottom-Rayleigh-domination mirror `evals_first_mul_dotProduct_le_quadForm` (`λ_min • (x ⬝ᵥ x) ≤ xᵀMx`, the missing lower half of the Rayleigh sandwich). `Perturbation.Weyl` now contains no axiom: the public additive bounds `weyl_additive_upper`/`weyl_additive_lower` (`λᵢ(A) + λ₁(E) ≤ λᵢ(A+E) ≤ λᵢ(A) + λₙ(E)`, proved from the Courant–Fischer engine's two witness forms — upper: the witness subspace for `A` exhibited as a member of the competitor set defining `λᵢ(A+E)` through `evals_min_max`; lower: the competitor direction for `A` run inside the witness subspace for `A+E`), composed into the retired `theorem weyl_inequality` through the proved `l2OpNorm_eq_max_abs_evals` bridge. `spectral_gap_stability` unchanged and now fully hard crust. QA `Weyl_QA.lean` 4 → 18 declarations: nonzero fixture `A = E = !![2,1;1,2]` with both spectra pinned independently (trace/det/sortedness) and `‖E‖ = 3` via the bridge — bound attained exactly at the top index (`|6−3| = 3`), strict at the bottom (`1 < 3`, the proposal's required non-vacuity witness), additive bounds instantiated at both indices, and the window-endpoint guard (`λ₁(E)` for `λₙ(E)` refuted: `6 ≤ 4` false).

**Decisive commands and outcomes:** `lake env lean` on both changed public modules and the QA module — zero errors, zero warnings (oleans produced directly); `#print axioms`: `weyl_inequality`, both additive bounds, `spectral_gap_stability`, and all nine QA theorems read only `propext, Classical.choice, Quot.sound`; derived consumers verified — `davisKahanTwoPoint` now depends on `davis_kahan_sin_theta` only, `eventStreamProjectorDrift` on two axioms instead of three; all thirty-two QA modules batch-elaborated, zero errors; **full `lake build` ✔ twice** (2184 targets; once after the Lean edits, once after the `ProjectorDrift` docstring updates); `lint_axioms` (**12**), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (**860/12/0**).

**Verification:** the Step-0 spike ran first in a scratch file (`wip/weyl_spike.lean`, ignored) and confirmed the proposal's caution — the additive bound is *not* free from the norm bridge (it consumes both witness directions plus both domination bounds, the bottom one newly added) — before any module edit; the cost estimate (~120 lines) was recorded in the proposal, and the spike transferred verbatim. The retirement is at the exact axiom statement, verified by the unchanged downstream code re-linking against the theorem.

**Remaining risk:** low — the proof is the same Courant–Fischer engine shape as the delivered interlacing retirement, with QA pinning both perturbed spectra and the norm independently of the theorem; the derived layer's remaining conditionality (Davis–Kahan, Matrix Azuma) is unchanged and honestly labeled. Davis–Kahan and Cheeger-hard remain unsurveyed — this run's positive outcome does not transfer to them (the proposal's own ranking).

**Next handoff:** the Active table's two ungated High rows (Tikhonov Regularization; Spectral Band Projectors), or the Davis–Kahan Step 0 survey on this proposal's track.

## 2026-08-20T05:11:00Z — Tikhonov regularization in the Laplacian eigenbasis

**Run:** `20260820T051000Z-run-1`  
**Session:** `ses_fe26f8e52ffesMKokGJkYgb5OS`  
**Status:** in-progress  
**Milestone:** Deliver `proposals/tikhonov-shrinkage-filter.md` (the Active priority table's top High row, unblocked, no gate) as pure hard crust in a new `GraphTheory.Tikhonov`: the eigenbasis-defined minimizer, its closed-form eigencoefficient identity, minimality/uniqueness, the shrinkage-factor layer, and the not-a-projection distinction — zero new axioms (12 unchanged). Definition route decided per the proposal's standing rule: the explicit eigenbasis formula over `Classical.choice` strict convexity. Step-3 deviation identified in advance for honest recording: the proposal's "never exactly 1" fails at `λ = 0` (kernel factor is exactly 1 — that is mean preservation); the corrected statements will be delivered instead.

**Changes:** intent recorded in the execution plan; the pruned Mathlib-oleans state recurred at run start and the recorded interpreted cache fetch is running in the background; Lean work to follow in `Scaffold/Mathlib/GraphTheory/Tikhonov.lean` and `Scaffold/QA/SpectralGraph/Tikhonov_QA.lean`.

## 2026-08-20T09:02:00Z — Tikhonov regularization delivered; program complete in one run

**Run:** `20260820T051000Z-run-1`  
**Session:** `ses_fe26f8e52ffesMKokGJkYgb5OS`  
**Status:** completed  
**Milestone:** `proposals/tikhonov-shrinkage-filter.md` (the Active priority table's top High row), all three build steps delivered in one run as pure hard crust — zero new axioms (12 unchanged; `#print axioms` on all 18 public theorems reads only `propext, Classical.choice, Quot.sound`).

**Changes:** new public module `GraphTheory.Tikhonov` + QA `SpectralGraph/Tikhonov_QA.lean` (+30 declarations, 890 total). Definition route decided per the standing rule: the minimizer **defined by the eigenbasis formula** (not `Classical.choice` strict convexity), so the eigencoefficient identity is hypothesis-free orthonormality (via a generic reusable filter workhorse `dotProduct_eigvecOf_filter`), the **normal equation holds both ways** (`(L+π•1) *ᵥ x* = π•y` plus the converse characterization — the QA-pinning interface), and minimality/uniqueness both fall out of the single strict-convexity decomposition `obj(x)−obj(x*) = ∑_k (1+λ_k/π)(d_k−d*_k)²`. Two recorded statement-shape corrections to the proposal's Step 3: the attenuation factor is **exactly 1 at λ = 0** (the kernel mode passes through untouched — that *is* mean preservation, `sum_tikhonovMinimizer_eq_sum`, needing symmetry and `π ≠ 0` only), and "not a projection" is a theorem (idempotence failure `T(T v) ≠ T v`, with the sketch's nonnegativity hypothesis found unnecessary and deleted). QA on `K₂`: minimizer pinned against a **hand-solved 2×2 system** through the converse characterization (spectral construction and Gaussian elimination independently meet at `![2/3,1/3]`), objective pinned exactly (`1/3` vs `1`), exact shrinkage at the pinned spectrum `{0,2}` (factors `1`, `1/3`), `T² ≠ T` numerically, mean preservation twice, and the `hπ` guard refuted-on-omission at `π = 0`. Records: scoreboard (890/12/0 + rows), radar (subject axis 2 re-scored **3.5 → 4.0** — the axis's first constructed application-facing operator family; QA axis held at 4.0 with the hold logged), README (890, proved list), SGT index map (new section, 18 rows), proposal (DELIVERED + delivery record with both deviations), `proposals/README.md` (row moved to Delivered; **Spectral Band Projectors is now the top High row**), umbrella, execution plan.

**Decisive commands and outcomes:** `lake env lean` on the public module and QA — zero errors, zero warnings; `#print axioms` on 18 public + 14 QA headline theorems — three standard axioms only; **all thirty-three QA modules batch-elaborated, zero errors** (only the documented pre-existing section-variable warnings in untouched modules); **full `lake build` ✔ (2185 targets, "Build completed successfully")**; `lint_axioms` (12), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (890/12/0). Environment: the pruned-oleans state recurred at run start; the recorded interpreted cache fetch restored 5387 before elaboration. Operational note recorded in the scoreboard: one `lake build` invocation was killed at its tool timeout mid-replay (the known hazard; Mathlib oleans survived this time — no re-fetch needed) and the build completed on a re-run executed **detached from the tool timeout** (log file + poll), now recorded as the recovery procedure alongside direct `lake env lean`.

**Verification:** every changed module elaborated directly with zero errors/warnings; axiom surface unchanged (12); no `sorry`/`admit` anywhere under `Scaffold/`; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional.

**Remaining risk:** low — the module is eigenbasis algebra over already-QA'd center interfaces, with the minimizer cross-checked against hand computation; `tikhonovMinimizer_eigvecOf` is not numerically instantiated in QA (`eigvecOf` entries are not kernel-computable; its content is covered transitively by the two normal-equation pins) and the Shuman et al. citation remains unverified and out of committed docstrings, as the proposal requires.

**Next handoff:** the Active table's remaining High row — **Spectral Band Projectors** (`spectral-band-projectors.md`, no gate: the two-sided band as the difference of two existing `spectralProjector` calls); the Medium rows stay queued behind it.

## 2026-08-21T23:08:00Z — Davis–Kahan Step 1, component 2: the Duhamel/FTC assembly

**Run:** `20260821T230647Z-run-1`  
**Session:** `ses_fd974e0c2ffef31j2LiAyA9JZx`  
**Status:** in-progress  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Davis–Kahan Step 1, component 2 — the Duhamel/FTC assembly consuming the delivered equal-rank identity plus the spike-verified semigroup primitives, to retire `davis_kahan_sin_theta` at its exact existing statement (explicit axioms 11 → 10; `davisKahanTwoPoint` becomes hard crust, `eventStreamProjectorDrift` conditional on `matrix_azuma_hoeffding` alone). Pre-edit route decision recorded in the execution plan, including the new tie-handling case split (both threshold-tie cases collapse through the proved Weyl bound to `δ ≤ ‖E‖` + `‖P−Q‖ ≤ 1`; Duhamel only needed in the no-tie case where component 1's rank equality holds).

**Changes:** intent recorded in the execution plan and here; environment verified healthy at run start (5382 Mathlib oleans present). Lean work to follow in a new `Analysis/OperatorTheory/Perturbation/Duhamel.lean`, then the `DavisKahan.lean` retirement rewrite and `DavisKahan_QA.lean` extension.

## 2026-08-22T03:17:00Z — Davis–Kahan retired: the Duhamel/FTC assembly delivered; the perturbation-bridge trust surface is empty

**Run:** `20260821T230647Z-run-1`  
**Session:** `ses_fd974e0c2ffef31j2LiAyA9JZx`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Davis–Kahan Step 1, component 2 — the Duhamel/FTC assembly — delivered as the milestone's dedicated run, completing the Davis–Kahan target: `davis_kahan_sin_theta` retired from admitted axiom to proved theorem at the unchanged name, hypotheses, and conclusion. Explicit axioms **11 → 10**; `davisKahanTwoPoint` is now fully hard crust; `eventStreamProjectorDrift` is conditional on `matrix_azuma_hoeffding` alone (both verified by `#print axioms`).

**Changes:** the new public module `Analysis/OperatorTheory/Perturbation/Duhamel.lean` (~900 lines, zero new axioms): the spike's heat-semigroup layer transferred (`heatApply` + expansion/adjoint, Parseval damping, eigenaction, differentiability, and the new `t = 0` eigenbasis-expansion identity `heatApply_zero`), the sorted-spectrum step `evals_succ_le_of_lt` (the interior companion of the two extreme pins), the projector coefficient filter `dotProduct_eigvecOf_spectralProjector_mulVec`, the two cluster-filtered decay bounds, the pairing (duality) norm reduction `l2OpNorm_le_of_abs_dotProduct_le` (self-application: the bound at `y := M *ᵥ x` forces `‖M x‖ ≤ c‖x‖`), the headline `l2OpNorm_one_sub_spectralProjector_mul_spectralProjector_le` (`‖(1 − Q) * P‖ ≤ ‖E‖/(b − a)` — the scalar Duhamel pairing whose derivative is exactly the integrand `−⟨e^{-t(A+E)}z_y, E e^{tA}z_x⟩` by the symmetry shuffle, FTC with the explicit exponential majorant, boundary decay at `T → ∞`), the rank layer, and the `‖P − Q‖ ≤ 1` gap endpoint. `Perturbation/DavisKahan.lean` rewritten: the `axiom` is now a `theorem` proved by the pre-edit-recorded three-way eigenvalue-tie case split — **a route discovery the survey did not need to resolve**: `initialProjector` includes whole tied eigenspaces, so ties make the two projector ranks differ and block the equal-rank identity; both tie cases collapse through the proved `weyl_additive_upper` to `δ ≤ ‖E‖` and finish via `≤ 1`, while the no-tie case consumes the delivered component 1 (`l2OpNorm_sub_eq_of_rank_eq`) and the Duhamel bound. QA `Perturbation/DavisKahan_QA.lean` 3 → 20 declarations: the strict non-vacuity witness (`dkA = diag(0,2)` perturbed by `dkE = [[0,3/4],[3/4,0]]`; both spectra and `‖dkE‖ = 3/4` pinned independently; eigenvector directions pinned from the eigen equations; both projectors pinned to literals `Q = (1/10)!![9,−3;−3,1]`, `P = diag(1,0)`; the bound instance `‖Q − P‖ ≤ 1/3` against the exact pinned distance `1/√10 < 1/3` — strict, and exercising the no-tie branch). Records: the two index files, README (10/1061, proved list, module table), architecture §12, the scoreboard (counts 1061/10/0, the lint/build/Direct rows, an interpretation bullet), radar (axis 7 re-scored **3.5 → 4.0** — the axis's first calculus-based proof technique as a new capability family, logged per protocol; axiom-minimization trend → 10; proved-depth/QA syncs), the proposal (status header, full Step-1 delivery record with the tie-case discovery, open-next-step → the Cheeger hard-direction survey), `proposals/README.md`, the umbrella import, the execution plan, and this log. Nothing committed.

**Decisive commands and outcomes:** `lake env lean` on `Duhamel.lean`, `DavisKahan.lean`, and `DavisKahan_QA.lean` — zero errors, zero warnings on each (Duhamel's headline proof under `set_option maxHeartbeats 2000000`); `#print axioms`: `davis_kahan_sin_theta`, the Duhamel headline, every QA headline — only `propext, Classical.choice, Quot.sound`; derived consumers verified — `davisKahanTwoPoint` three standard axioms only, `eventStreamProjectorDrift` + `matrix_azuma_hoeffding`; `lake build` on the two new modules ✔; **all thirty-five QA modules batch-elaborated, zero errors (BATCH-DONE fail=0)**; **full `lake build` ✔ (2227 targets, "Build completed successfully", detached log + poll)**; `lint_axioms` (no issues), `check_citations`, `check_markdown_links` pass; scoreboard regeneration reflects **1061 QA declarations / 10 explicit axioms / 0 sorries**.

**Verification:** the retirement is at the exact axiom statement (downstream code re-linked with no changes); the delivery is fully proved hard crust — nothing axiom-backed was added. The QA fixture pins every quantity by two independent routes (trace/determinant/sortedness for spectra, the eigen equations for directions, the proved bridge for the norm), so a wrong statement shape would fail its pins.

**Remaining risk:** low for what is delivered. The Cheeger hard-direction Step 0 survey is this proposal's only remaining target and is under a known-hard working assumption — the Weyl and Davis–Kahan outcomes do not transfer to it. The Duhamel bound's `hcl` side condition (every eigenvalue above `c'` is at least `b`) is supplied from `evals_succ_le_of_lt` at the retirement; other consumers with genuinely mixed clusters would need their own sortedness argument.

**Next handoff:** the Medium rows by leverage — mixing-time Step 1, Reversibility Phase A, Relative Entropy, Perron–Frobenius + directed operators (Step 0 first), the Cheeger hard-direction Step 0 survey, approximate spectral projection (Step 0 first); Fiedler Phase B still needs an operator decision.

## 2026-08-22T04:25:00Z — Mixing-time Step 1: eigenpair transfer to the walk matrix

**Run:** `20260822T042339Z-run-1`  
**Session:** `ses_fd84f61efffeGLtzSLjEXLM22W`  
**Status:** in-progress  
**Milestone:** `proposals/mixing-time-bound.md` Step 1 at its recorded open next step (top Medium row; no High rows remain) — transfer eigenpairs between the symmetric normalized Laplacian `L_sym` and the non-symmetric walk form `L_walk = 1 − D⁻¹A` through the already-proved similarity identity `√D · L_walk · (1/√D) = L_sym`, closing `Normalized.lean`'s own named residual gap and building the interface the proposal's Step 3 decay bound consumes. Zero new axioms.

**Changes:** intent + pre-edit survey recorded in the execution plan. Survey outcome: the pinned Mathlib has no general similar-matrices-share-eigenvalues interface (no `IsSimilar`, no charpoly-conjugation invariance under `Mathlib/LinearAlgebra/`), so the direct diagonal-case transfer is the route — both directions via `mulVec` algebra, eigenbasis instantiation via `IsHermitian.mulVec_eigenvectorBasis`, completeness via `eigvecOf_expansion_apply` + the invertibility shuffle. Lean work to follow in `GraphTheory/Normalized.lean` and `SpectralGraph/Normalized_QA.lean` (P₃ fixture, both-direction transfers, raw cross-checks, untransformed-vector guard).

## 2026-08-22T05:39:43Z — Mixing-time Step 1 delivered: eigenpair transfer to the walk matrix

**Run:** `20260822T042339Z-run-1`  
**Session:** `ses_fd84f61efffeGLtzSLjEXLM22W`  
**Status:** completed  
**Milestone:** `proposals/mixing-time-bound.md` Step 1 at its recorded open next step (top Medium row; no High rows remain) — the eigenpair transfer between the symmetric normalized Laplacian `L_sym` and the non-symmetric walk form through the already-proved similarity identity, delivered as pure hard crust in `GraphTheory.Normalized` (its own named residual gap), **zero new axioms** (count stays 10; `#print axioms` on all nine new public theorems reads only `propext, Classical.choice, Quot.sound`). Radar axis 5 re-scored 2.5 → 3.0 per the proposal's own gate.

**Changes:** (1) **Mandatory Mathlib survey, recorded before any edit**: no general similar-matrices-share-eigenvalues interface exists in the pin (no `IsSimilar`, no charpoly-conjugation invariance under `Mathlib/LinearAlgebra/`) — the proposal's anticipated branch, so the direct diagonal-case transfer was the route; the coverage map needed no correction (it already records the upstream absence). (2) **`GraphTheory.Normalized`** gained the eigenpair-transfer section: `walkLaplacian_mulVec_degreeInvSqrt` / `normalizedLaplacian_mulVec_degreeSqrt` (both directions, same eigenvalue, eigenvector conjugated by `1/√D`/`√D` — pure `mulVec` algebra, no characteristic polynomial, dissolving the module docstring's recorded charpoly obstruction), `walkTransitionMatrix_mulVec_degreeInvSqrt` (the `(1 − μ)` transition reflection), the eigenbasis instantiations via `IsHermitian.mulVec_eigenvectorBasis`, `walk_eigvec_expansion` (completeness of the transferred family — the diagonalizability interface Step 3 consumes, from `eigvecOf_expansion_apply` + the invertibility shuffle), `walkEvals` + `exists_eigenvector_walkTransitionMatrix_eq_walkEvals` (every transferred spectrum entry certified a genuine eigenvalue of `P` with an explicit nonzero witness), and the support lemmas `eigvecOf_ne_zero`, `degreeInvSqrt_mulVec_ne_zero`. (3) **QA** `Normalized_QA.lean` 14 → 34 declarations: P₃ hand eigenpairs verified by raw computation, transferred through the theorems, cross-checked by raw arithmetic on the conjugated vectors, both directions; the `walkEvals` existential at every index; a hand-solved spanning witness; and two shortcut guards refuted in proved form (skip-the-conjugation; unreflected eigenvalue). QA-infrastructure note recorded in the proposal: the `√(1+1)`-vs-`√2` simp atom mismatch is bridged by a pinned `1 + 1 = 2` rewrite (`path_one_add_one_QA`), reusable for future `√`-arithmetic QA on this fixture. (4) **Records**: scoreboard (both Direct rows + `lake build` row prepended, new interpretation bullet, counts 1081/10/0), radar (axis 5 evidence row rewritten + re-score 2.5 → 3.0 with the proposal-gate justification; QA axis synced 1081/35, held, both logged in the re-scoring log), README (status table, proved list, coverage snapshot date + axis-5 row), SGT index map (new Normalized transfer section, 9 rows), `docs/6_SGT_BACKLOG.md` (item 2's residual marked closed with the survey re-confirmation), the proposal (status header, full delivery record, open-next-step → Step 2 with its decide-and-record gate named), `proposals/README.md` (Medium row + progress paragraph), the execution plan, and this log. Nothing committed.

**Decisive commands and outcomes:** `lake env lean` on `Normalized.lean` and `Normalized_QA.lean` — zero errors, zero warnings (the module's only diagnostic is the pre-existing `congr 1` linter note on untouched code, identical in HEAD; the QA file reached zero warnings after restructuring the finishers to `all_goals`-style per the linter's own guidance); `#print axioms` on the nine public and seven headline QA theorems — `propext, Classical.choice, Quot.sound` only; oleans built (`lake build` on both targets); **full `lake build` ✔ (2227 targets, "Build completed successfully", executed detached from the tool timeout per the recorded procedure — only the documented pre-existing `hγ` warning in `Derived/ProjectorDrift.lean`)**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1081 QA declarations / 10 explicit axioms / 0 sorries**; `Normalized_QA` 14 → 34).

**Verification:** every changed module elaborates directly with zero errors and zero new warnings and is linked into the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional. The transfer theorems are load-bearing on the proved similarity identity and the diagonal invertibility lemmas (an error in either would make them fail to typecheck), and both QA guards witness that the conjugation and the eigenvalue reflection are not decorative. The prior run's Davis–Kahan delivery was preserved untouched (its uncommitted worktree state is intact; this run's changes are disjoint files except the shared records, which were extended not rewritten).

**Remaining risk:** low for what is delivered. The mixing-time program's hard part remains: Step 3 (the geometric decay of `‖Pᵗ δₓ − π‖`) is rated by the proposal's own calibration as at least as hard as the electrical program's solvability step, and Step 2's ℓ²-proxy scoping decision (ℓ² alone vs. TV conversion) is deliberately left as a recorded decision for the next run, not made here. The transferred expansion is stated over the non-orthogonal transferred family (coefficients carry `√D`); consumers needing orthonormal coordinates must rescale — a named residual, not a defect.

**Next handoff:** the Medium rows by leverage — **mixing-time Step 2** (the ℓ²-mixing proxy; make and record its decide-and-record scoping choice first), **Reversibility Phase A** (cheap, zero new axioms, composes existing `Stationary`/`Normalized` lemmas), **Relative Entropy**, **Perron–Frobenius + directed operators** (Step 0 first per the convention-choice gate), the **Cheeger hard-direction Step 0 survey** (known-hard working assumption), **approximate spectral projection** (Step 0 first). Fiedler Phase B still needs an operator decision.

## 2026-08-22T06:14:00Z — Reversibility Phase A: detailed balance for the weighted-graph walk

**Run:** `20260822T061043Z-run-1`  
**Session:** `ses_fd7ef370fffennYqCBfQGsm4In`  
**Status:** in-progress  
**Milestone:** `proposals/reversibility-and-heat-semigroup.md` Phase A (both steps in one run per its own operating instruction) — prove detailed balance `π i * P i j = π j * P j i` for the simple random walk on a weighted undirected graph with positive degrees, in `GraphTheory.Stationary` (deg form, π/vol form, the symmetrizability matrix form, and the regular-case uniform-measure corollary), zero new axioms, no new definitions. Selected by the inner-dependency test: the higher-ranked mixing-time Step 2's ℓ²(π) proxy consumes exactly this interface, and Phase A is the cheaper strictly-inner dependency (the mixing-time proposal itself defers reversibility to this companion proposal). Closes one of radar axis 5's three named-absent items and one half of backlog item 6's gate.

**Changes:** intent recorded in the execution plan (route + QA plan + a records defect found during pre-edit reading: radar axis 5's table row and "Weakest axes" paragraph were not synced by the 2026-08-22 mixing-time re-score — repair planned alongside the Phase A radar update). Pre-edit survey findings: `transitionMatrix_symmetric` already on the shelf in `RandomWalk.lean` (the regular case's content), `vol` at `Spectral.lean:697`, no detailed-balance/reversibility machinery anywhere in the pinned Mathlib (coverage map already records the absence). Lean work to follow in `Scaffold/Mathlib/GraphTheory/Stationary.lean` and `Scaffold/QA/SpectralGraph/Stationary_QA.lean`.

## 2026-08-22T07:03:21Z — Reversibility Phase A delivered: detailed balance for the weighted-graph walk

**Run:** `20260822T061043Z-run-1`  
**Session:** `ses_fd7ef370fffennYqCBfQGsm4In`  
**Status:** completed  
**Milestone:** `proposals/reversibility-and-heat-semigroup.md` Phase A (both steps in one run per its own operating instruction) — detailed balance `π i * P i j = π j * P j i` for the simple random walk on a weighted undirected graph with positive degrees, delivered as pure hard crust in `GraphTheory.Stationary`, **zero new axioms** (count stays 10; `#print axioms` on all four new public theorems plus the new `Normalized.walkTransitionMatrix_apply` reads only `propext, Classical.choice, Quot.sound`) and **no new definitions** (the proposal's own mandate). Selected by the inner-dependency test: the higher-ranked mixing-time Step 2's ℓ²(π) proxy consumes exactly this interface. Closes one of radar axis 5's three named-absent items (reversibility) and the reversibility half of backlog item 6's gate; radar axis 5 **held at 3.0** per protocol (composed identity within the walk-operator family counted at the same day's mixing-time re-score; hold + triggers logged).

**Changes:** (1) **Pre-edit survey recorded**: no detailed-balance/reversibility machinery anywhere in the pinned Mathlib (coverage map already correct); `transitionMatrix_symmetric` already on the shelf in `RandomWalk.lean` (the regular case's content — so Phase A Step 2 was delivered as the uniform-measure corollary *composed* from it, not a re-proof). (2) **`GraphTheory.Stationary`** gained the detailed-balance section: `walk_detailed_balance` (degree-measure form, both sides exactly `A i j`), `walk_detailed_balance_measure` (the stationary-measure π-form at `π = deg/vol`, by side-condition-free division — **no volume-positivity hypothesis carried**, strictly more general than drafted), `diagonal_deg_mul_walkTransitionMatrix_isSymm` (reversibility *is* symmetrizability: `D * P` symmetric — the self-adjointness interface the mixing program consumes), `transitionMatrix_detailed_balance_uniform`. **`Normalized.lean`** gained the entry lemma `walkTransitionMatrix_apply` (`P i j = (deg A i)⁻¹ * A i j`) and its stale "Named gap (deferred)" similarity docstring was corrected to point at the delivered 2026-08-22 eigenpair transfer. Two Lean findings worth the record: bare `univ` in a statement elaborates as an auto-bound *local* arbitrary finset (not `Finset.univ`) — the explicit house form is now used; and `Finset.sum_pos'` was rendered unnecessary by the division route. (3) **QA** `Stationary_QA.lean` 12 → 26 declarations, the proposal's two prescribed witnesses: positive (P₃, every index pair through the theorems *and* raw literal arithmetic — `1 = 1` degree form, `1/4 = 1/4` π-form with `vol = 4` pinned independently, symmetrized off-diagonal entries both `1`, uniform form at the edge) and negative (the asymmetric `!![0,2;1,0]` with positive degrees: hypothesis-free balance refuted `2 ≠ 1`, symmetry hypothesis provably violated at the same pair — `hA` load-bearing). (4) **Records repaired alongside**: the radar axis-5 *table row* and "Weakest axes" paragraph, which the same day's earlier mixing-time run had left stale at score 2.5 with the closed gap still named, were synced to the recorded 3.0 state. Records updated: proposal (status header, Phase A delivery record with both statement-shape notes, open-next-step → Phase B's operator gate only), `proposals/README.md` (Phase B-only row + Delivered row + progress paragraph), scoreboard (both Direct rows prepended, new interpretation bullet, **1095/10/0**), radar (table row + weakest-axes repair, narrative hold entry), README (1095, proved list), SGT index map (Stationary section, 4 rows + entry-lemma note), backlog item 6 (reversibility half delivered), the execution plan, and this log. An unrelated operator-side worktree change — the new `proposals/prove-subgaussian-tail-bound.md` and its `proposals/README.md` row, appearing mid-run with no second agent process or session in evidence — was preserved untouched and left uncommitted, per the preserve-unrelated-changes rule. Nothing committed.

**Decisive commands and outcomes:** `lake env lean` on `Normalized.lean`, `Stationary.lean`, `Stationary_QA.lean` — zero errors; Stationary's two warnings verified pre-existing in HEAD via `git stash` round-trip; `#print axioms` on the five public and eight headline QA theorems — `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2227 targets, "Build completed successfully", detached log + poll)** — every QA module compiled as a library target; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1095 QA declarations / 10 explicit axioms / 0 sorries**; `Stationary_QA` 12 → 26). One build invocation hit the recorded trace-replay timeout mid-run and was re-executed detached per the recorded procedure; the Mathlib oleans survived (no re-fetch).

**Verification:** every changed module elaborates directly and is linked into the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional. The balance theorems are load-bearing on the exact shapes of `walkTransitionMatrix` (`D⁻¹A`), `deg`, and `hA.apply`; the QA negative witness ties the failed identity to the violated symmetry hypothesis at the same entry pair.

**Remaining risk:** low for what is delivered. Phase B (the heat semigroup) remains gated on the operator decision the proposal itself records — an autonomous run must not start it. The mixing-time program's hard part is untouched: Step 2's ℓ²-proxy scoping decision and Step 3's decay bound (rated at least as hard as the electrical program's solvability step) remain; the delivered interface is their input, not their substitute.

**Next handoff:** the Medium rows by leverage — **mixing-time Step 2** (make and record its decide-and-record scoping choice first; the detailed-balance interface is now available to it), **Relative Entropy**, **the subgaussian tail bound** (the 2026-08-22 operator-directed addition; Step 0 first), **Perron–Frobenius + directed operators** (Step 0 first per the convention-choice gate), the **Cheeger hard-direction Step 0 survey** (known-hard), **approximate spectral projection** (Step 0 first). Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T08:20:00Z — Mixing-time Step 2: the ℓ²-mixing proxy (definitions + evolution interface)

**Run:** `20260822T081458Z-run-1`  
**Session:** `ses_fd7805c03ffeHnziia1UMh3sgq`  
**Status:** in-progress  
**Milestone:** `proposals/mixing-time-bound.md` Step 2 at its recorded open next step — the ℓ²-mixing proxy, with its decide-and-record scoping gate made first (ℓ² alone satisfies the goal, TV stays a separate further step; within ℓ², the weighted χ² form is primary because Step 3's decay bound is Parseval-exact only in the π-weighted inner product where the transferred eigenbasis is orthogonal). New `GraphTheory/Mixing.lean` (`stationaryVec`, `walkDistribution`, `walkDensity`, `chiSquareDistance` + evolution/stationarity/characterization interface, zero new axioms) + `Mixing_QA.lean`. First consumer of the Phase A detailed-balance interface. Lean work to follow.

**Changes:** intent recorded in the execution plan (scoping decision, route, QA plan). Pre-edit Mathlib survey (this run): no chi-square/total-variation/mixing-time/Markov-stationarity objects in the pin — coverage map already records the absence, no correction needed. Worktree inspected: the uncommitted 2026-08-22 Phase A + Step 1 deliveries are prior completed runs' output (terminal entries recorded), preserved untouched and left uncommitted per house rule.

## 2026-08-22T08:52:32Z — Mixing-time Step 2 delivered: the ℓ²-mixing proxy with its evolution interface

**Run:** `20260822T081458Z-run-1`  
**Session:** `ses_fd7805c03ffeHnziia1UMh3sgq`  
**Status:** completed  
**Milestone:** `proposals/mixing-time-bound.md` Step 2 at its recorded open next step — the ℓ²-mixing proxy, delivered as pure hard crust in the new `GraphTheory.Mixing` (**zero new axioms**, count stays 10; `#print axioms` on all fourteen new public theorems reads only `propext, Classical.choice, Quot.sound`). The step's own decide-and-record scoping gate was made *before any statement* (the record the proposal authorizes a run to make): (1) ℓ² alone satisfies the proposal's goal, TV conversion stays a separate further step per the proposal's own Step-4 framing; (2) within ℓ², the *weighted* χ² form `∑ (ν_t − π)²/π` is primary because Step 3's decay bound is Parseval-exact only in the π-weighted inner product where the Step-1 transferred eigenbasis is orthogonal — the plain Euclidean sketch-shape is delivered as the corollary bridge `sum_sub_sq_walkDistribution_le` instead.

**Changes:** (1) New `Scaffold/Mathlib/GraphTheory/Mixing.lean` (14 public theorems + 4 definitions): `stationaryVec` (π = deg/vol; `vol_univ_pos`, `stationaryVec_pos`, `sum_stationaryVec`, the unpacking lemma, and `walk_isStationary` composed from the proved degree-form stationarity), `walkDistribution` (`(Pᵀ)ᵗ *ᵥ δₓ`; `walkDistribution_zero`/`_succ`; `sum_walkDistribution` mass conservation load-bearing on row-stochasticity), `walkDensity` with **`walkDensity_succ`** — the density evolution `h_{t+1} = P *ᵥ h_t`, *the first consumer of the same day's Phase A detailed-balance interface* and the exact coordinate in which the transferred eigenbasis diagonalizes the mixing evolution — and `chiSquareDistance` (nonneg; `= 0 ↔ ν_t = π`; the `t = 0` value `(π x)⁻¹ − 1`, Step 3's normalization; the density-form equivalence; the plain-ℓ² bridge). Two statement-shape notes recorded in the proposal: the adjoint orientation of `walkDistribution` matches the house stationarity theorem's (`Pᵀ *ᵥ deg = deg`), and the χ² junk value at `π i = 0` is documented with every theorem carrying the positivity hypothesis that rules it out. (2) New `Scaffold/QA/SpectralGraph/Mixing_QA.lean` (33 declarations, all proved) at the P₃ fixture. (3) Umbrella import; records: proposal (status header, scoping record, full Step-2 delivery record, open-next-step → Step 3 with the consumed interfaces named), `proposals/README.md` (Medium row, progress paragraph, Delivered row), scoreboard (both Direct rows prepended, `lake build` row, interpretation bullet, lint dates; regenerated **1128/10/0**), radar (axis-5 evidence row + weakest-axes extended, **held at 3.0** per the proposal's own no-re-score-before-Step-3 gate — the mixing *statement* is Step 3's decay bound; hold logged with the QA count synced 1128/36), README (1128, proved list, module table, span list), SGT index map (new Mixing section, 17 rows + status list), backlog item 2 (Step 2 delivered; Step 3 named the remaining piece), the execution plan, and this log. The worktree's unrelated operator-side change (`proposals/prove-subgaussian-tail-bound.md` + its README row, uncommitted) preserved untouched; nothing committed.

**Decisive commands and outcomes:** `lake env lean` on `Mixing.lean` and `Mixing_QA.lean` — zero errors, zero warnings each (six elaboration rounds on the module — orientation quirks of this pin resolved: `pow_succ'` for the adjoint-power recursion, `← Finset.sum_div`/`Finset.sum_mul` orientations, `← mul_div_assoc`, the hypothesis-free `div_eq_zero_iff`, `Finset.not_mem_erase`; one real statement bug caught by the planned numeric check: the first draft of the `walkDensity_succ` termwise identity had the two matrix entries swapped, which the P₃ hand computation `P *ᵥ (4,0,0) = (0,2,0)` refutes); `#print axioms` on the fourteen public and twelve headline QA theorems — `propext, Classical.choice, Quot.sound` only; `lake build Scaffold.Mathlib.GraphTheory.Mixing` and `…Mixing_QA` ✔; **full `lake build` ✔ (2227 targets, "Build completed successfully", detached log + poll)**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regeneration reflects **1128 QA declarations / 10 explicit axioms / 0 sorries** (`Mixing_QA` a new file row at 33).

**Verification:** every changed module elaborates directly with zero errors/warnings and is linked into the full default build (the umbrella now imports `GraphTheory.Mixing`); the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional. The QA pins every headline quantity through the theorems *and* by raw literal arithmetic (π, the t = 0/1/2 laws, the density evolution, both χ² routes, the plain-ℓ² bridge), and the two negative witnesses tie the load-bearing hypotheses to refuted hypothesis-free forms: the asymmetric positive-degree matrix refutes hypothesis-free stationarity at the entry where symmetry provably fails (`1/3 ≠ 2/3`, `hA` load-bearing), and the zero adjacency refutes the hypothesis-free vanishing characterization (`χ² = 0` junk beside `ν₀ ≠ π`, degree positivity load-bearing).

**Remaining risk:** low for what is delivered. Step 3 (the geometric decay bound) is the program's rated-hardest single step and remains open — the delivered interface is its input, not its substitute; the P₃ QA already pins the λ* = 1 bipartite non-decay (`χ²(1) = χ²(2) = 1`) that a correct Step-3 statement must reproduce rather than contradict, and this constraint is now recorded in the proposal's open-next-step. Phase B proposals (reversibility heat semigroup, Fiedler) still await operator decisions.

**Next handoff:** the Medium rows by leverage — **mixing-time Step 3** (the decay bound `χ² ≤ (λ*)²ᵗ · normalization`, consuming `walkDensity_succ` + `chiSquareDistance_eq_sum_smul` + `chiSquareDistance_zero` + the Step-1 transfer theorems; the matrix-power layer is its new work and may need sub-decomposition across runs), **Relative Entropy**, **the subgaussian tail bound** (Step 0 first), **Perron–Frobenius + directed operators** (Step 0 first), the **Cheeger hard-direction Step 0 survey** (known-hard), and **approximate spectral projection** (Step 0 first). Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-23T01:35:00Z — Cheeger hard-direction Step 1b: the co-area core

**Run:** `20260823T013007Z-run-1`  
**Session:** `ses_fd3c2b96dffeJA31TMVEK4VXBm`  
**Status:** in-progress  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Step 1b at its recorded open next step (the top Medium row; no High rows) — the co-area core, the crux of retiring the last perturbation axiom: for `y` whose nonempty superlevel sets `{i : y i² > t}` are all minority-side, `2 * (φ * d * ∑ y i²) ≤ ∑ i j, A i j * |y i² − y j²|`. Zero new axioms. Consuming the Step-1a interfaces at their corrected constant budget; the spike (`wip/cheeger1b_spike.lean`) decides the pin's analysis-API route first (the `Ι = Ioc` right-endpoint indicator-drop trap vs the ae-congruence route, and whether `integral_finset_sum`/`integral_congr_ae` exist at this pin to replace the priced 30-line hand Fubini).

**Changes:** intent recorded in the execution plan and here; no Lean source touched yet. Planned next: spike, then `Cheeger.lean` (co-area section) + `Cheeger_QA.lean` (K₂ equality pin, strict C₄ witness, minority-hypothesis refutation).

## 2026-08-23T02:21:00Z — Cheeger hard-direction Step 1b delivered: the co-area core, with the priced hand Fubini found in the pin

**Run:** `20260823T013007Z-run-1`  
**Session:** `ses_fd3c2b96dffeJA31TMVEK4VXBm`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Step 1b at its recorded open next step (the top Medium row; no High rows) — the co-area core, the crux of the last perturbation axiom's discharge — delivered as pure hard crust in `GraphTheory.Cheeger`, **zero new axioms** (count stays 10; `#print axioms` on all twelve new public theorems and seven QA headlines reads only `propext, Classical.choice, Quot.sound`). QA 1404 → 1423 (`Cheeger_QA` 59 → 78). The hard direction is now reduced to its final component: Step 1c (median + assembly) retires `cheeger_lower_bound` at the unchanged statement.

**Changes:** `GraphTheory.Cheeger` — the closed level step `indicatorLE` (`1_{t ≤ c}`) with the two layer-cake primitives (`integral_indicatorLE`: `∫₀^R 1_{t≤c} = c`; `integral_abs_indicatorLE_sub`: `∫₀^R |1_{t≤c} − 1_{t≤d}| = |c−d|`), integrability helpers, the closed-superlevel cut identity `sum_pairAbs_eq_two_boundary` (`= 2·boundary S_t`), minority conductance `boundary_ge_of_minority`, the indicator↔cardinality dictionary, the per-level bound, and the headline `coarea_core` (`2·(φ·d·∑y i²) ≤ ∑ i j, A i j·|y i² − y j²|` for any `y` whose nonempty closed superlevel sets at positive levels are minority-side). QA: the K₂ **equality** pin (both sides independently `2` — any defective constant in the chain breaks it), the strict multi-level C₄ witness (`20φ ≤ 10 < 16` via the exhaustively computed adjacent-pair conductance), the dictionary's closed-set semantics pinned at a boundary level, and the minority refutation-on-omission (`4 ≤ 0` at `![1,1]`, hypothesis provably unsatisfiable at `t = 1`). Records: the proposal (status header, a second inline dated survey correction at the Fubini note, the full Step-1b delivery record with pin-specific technique notes, open-next-step → 1c), `proposals/README.md` (Medium row + progress paragraph), the SGT index map (Cheeger section +7 rows + program note), README (1423, trust-surface paragraph), the radar (QA axis held 4.0, count synced 1404/39 → 1423/39, hold logged; the row-head count drift left by earlier syncs repaired), the scoreboard (both Direct rows, `lake build` row, lint row, interpretation bullet), the execution plan, this log.

**Decisive commands and outcomes:** `lake env lean Scaffold/Mathlib/GraphTheory/Cheeger.lean` — zero errors (only the documented pre-existing `unusedSectionVars` warning); `lake env lean Scaffold/QA/SpectralGraph/Cheeger_QA.lean` — zero errors, zero warnings; `lake build` on both targets ✔; `#print axioms` via `wip/cheeger1b_axcheck.lean` — twelve public + seven QA declarations each `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2250 targets, "Build completed successfully", detached)**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated **1423/10/0**. Spike discipline followed: the development landed green in `wip/cheeger1b_spike.lean` first (with the API probes against the pin), then transferred.

**Verification:** every changed module elaborates directly and is linked into the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional, and `cheeger_lower_bound` remains admitted, visible, and cited (its retirement is Step 1c's business alone). The chain is load-bearing end to end: the K₂ equality pin ties the FTC constants, the cut identity's factor 2, the conductance step's volume arithmetic, and the assembly's endpoints to independently computed values, and the refutation ties the minority guard to a refuted hypothesis-free form at a fixture satisfying every other hypothesis.

**Remaining risk:** moderate-low for what is delivered. Step 1c is rated moderate by the survey: median existence over the sorted value multiset and the `{u ≥ t} ⊆ {x > m}` inclusion (at `t > 0`) are the two genuinely new pieces, both finite-combinatorial; the constant arithmetic they must reproduce is now machine-checked at both endpoints (1a's normalization cross-checked against `λ₂(L_sym) = 2`; 1b's K₂ equality), so an assembly slip cannot hide. Pin-specific hazards for 1c recorded in the proposal (the `(0:ℝ)..R` Float lexing, the `Set.indicator_of_mem` membership-direction trap, the `IntervalIntegrable.sum` Pi-application whnf loop with its `Finset.sum_apply` route).

**Next handoff:** the Medium rows by leverage — **the Cheeger hard-direction Step 1c** (median + assembly; the final component, retiring the last perturbation axiom, explicit axioms 10 → 9) and **approximate spectral projection** (Step 0 first). The PF consumers (irreducible stationary distributions, PageRank) are unblocked as new-proposal candidates, each needing its own document per the one-step discipline. Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-23T03:25:00Z — Cheeger hard-direction Step 1c: median + assembly (the final component)

**Run:** `20260823T032137Z-run-1`  
**Session:** `ses_fd35d053bffeK4X8H9SR0loehr`  
**Status:** in-progress  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Step 1c at its recorded open next step (the top Medium row; no High rows) — the final component: median existence, the level-set inclusions supplying `coarea_core`'s `hy`, the norm split, and the assembly into the sweep lemma `φ²/2 ≤ R(x)`, retiring `cheeger_lower_bound` at the unchanged statement (explicit axioms 10 → 9). Consumes the delivered 1a/1b interfaces at their corrected constant budget. Zero new axioms.

**Changes:** intent recorded in the execution plan (route + QA plan); no Lean source touched yet. Planned next: develop green in `wip/cheeger1c_spike.lean`, transfer to `Cheeger.lean`, QA (`Cheeger_QA.lean`), then the record sweep (proposal, proposals/README, README, radar, scoreboard, SGT index map, citation index status). The worktree's uncommitted Step-1b delivery (prior run, terminal entry recorded) is preserved untouched.

## 2026-08-23T03:48:30Z — Cheeger hard-direction Step 1c delivered: the axiom retired, the discharge program complete

**Run:** `20260823T032137Z-run-1`  
**Session:** `ses_fd35d053bffeK4X8H9SR0loehr`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Step 1c (median + assembly, the final component) — **`cheeger_lower_bound` retired from admitted axiom to proved theorem at the unchanged name, hypotheses, and conclusion, explicit axioms 10 → 9**, the discharge program COMPLETE (Weyl 2026-08-20, Davis–Kahan 2026-08-21, Cheeger easy 2026-08-18, Cheeger hard 2026-08-23 — all proved hard crust). Pure hard crust in `GraphTheory.Cheeger`'s new Step-1c section; QA 1423 → 1449 (`Cheeger_QA` 78 → 104). Radar axis 4 re-scored 4.0 → 4.5 (both directions of the axis's central isoperimetric–spectral family now proved).

**Changes:** (1) `GraphTheory.Cheeger` — the axiom block replaced by the proved theorem at the identical statement, with a new Step-1c section: median existence `exists_median` by pure Finset arithmetic (*no sorting* — a route simplification over the survey's `Finset.sort`+`get` sketch: the at-most-half set is nonempty at a maximizing vertex, a minimal-value member works, the failure case self-refuting through the lower level set's maximizer lying in `T` below the `T`-minimum; the empty-type case separate), the level-set inclusions `{t ≤ (x−m)⁺²} ⊆ {x > m}` / `{t ≤ (m−x)⁺²} ⊆ {x < m}` at `t > 0` (supplying `coarea_core`'s `hy` in its delivered closed-set form), the per-part bound `hardDirection_perPart` (`φ²·d·∑y² ≤ E'(y)` — the 1b co-area core squared and composed with the 1a Cauchy–Schwarz core, `cheegerConstant_nonneg` for the squaring, zero-norm case by nonnegativity), the norm split `median_parts_norm`, the sweep lemma `cheeger_sweep`, and the retirement through `secondEval_variational` + `le_csInf` at the `Pi.single` witness. (2) `Cheeger_QA.lean` +26 declarations: the median forced into `[−1,1]` on the tie-heavy `![1,1,−1,−1]`, the per-part bound at the 1b K₂ equality data (`1 ≤ 2` both sides raw), the norm split's `+4m²` remainder pinned at two medians, the sweep on K₂ (`1/2 ≤ 2`, against the pinned λ₂) and C₄ at `d = 2` (`φ²/2 ≤ 1/8 < 1 = R`), and the retirement instance `1/2 ≤ λ₂ = 2` through the proved theorem. (3) Records: the proposal (status COMPLETE, Step-1c delivery record with pin-specific technique notes), `proposals/README.md` (Medium row → Delivered table; progress paragraph), the Chung source index (proved-not-axiom row), the SGT index map (+5 rows, program-complete note), README (9 axioms, 1449, both Cheeger inequalities proved), the radar (axis-4 re-score with the log; axiom-minimization trend `... → 9 → 10 → 9` with the row-head count drift from the PF admission repaired; QA sync 1449/39; downstream-reuse gap clause), the scoreboard (both Direct rows, `lake build` row, lint row, retirement bullet — **1449/9/0**), backlog item 4's Phase-B trust note, the execution plan, this log. The prior run's uncommitted Step-1b delivery preserved untouched; nothing committed.

**Decisive commands and outcomes:** `lake env lean` on `Cheeger.lean` (only the documented pre-existing `unusedSectionVars` warning) and `Cheeger_QA.lean` (zero errors, zero warnings); `lake build` on both targets ✔; `#print axioms` via `wip/cheeger1c_axcheck.lean` — the retired theorem, all ten new public theorems, all nine new QA headlines, and the two *pre-existing* axiom-consuming QA theorems (which compiled unchanged and silently shed the dependency) each read only `propext, Classical.choice, Quot.sound`; **full `lake build` ✔ (2250 targets, "Build completed successfully", detached)**; `lint_axioms` (**9**), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1449 QA declarations / 9 explicit axioms / 0 sorries**; `Cheeger_QA` 78 → 104). Spike discipline followed: green in `wip/cheeger1c_spike.lean` first, then transferred.

**Verification:** every changed module elaborates directly and is linked into the full default build; the delivery is fully proved hard crust — the retirement removes an axiom rather than adding trust surface, so nothing new is conditional. The chain is load-bearing end to end: the tie-heavy median pin would fail on any defective counting in `exists_median`; the per-part and sweep instances are computed against independently pinned endpoint values (the 1b K₂ equality data, the pinned `λ₂(L_sym) = 2`, the raw `E' = 8`/`‖x‖² = 2` on C₄); and the retirement instance exercises the exact statement that was previously admitted.

**Remaining risk:** low for what is delivered. The proposal's program is closed; the residual Cheeger-adjacent items are the Fiedler Phase B operator decision (whose composition would now be hard crust if run) and the irregular-graph statement shape (needs a matrix square root absent from the pin). The remaining 9 admitted axioms: the concentration family (with the recorded junk-integral residual on `hoeffding_inequality`/`bernstein_inequality`/`MatrixMDS` mean hypotheses), Perron–Frobenius, and Hoeffding's lemma.

**Next handoff:** the Medium rows by leverage — **approximate spectral projection** (Step 0 first; a negative tractability finding is a valid recorded outcome). The PF consumers (irreducible stationary distributions, PageRank) are unblocked as new-proposal candidates, each needing its own document per the one-step discipline. Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-23T06:15:07Z — Reversibility Phase B Step 0 + Step 1: heat semigroup survey and definition

**Run:** `20260823T061507Z-run-1`  
**Session:** `ses_fd2c33b2dffe5V3NVp8G9iVOA4`  
**Status:** in-progress  
**Milestone:** `proposals/reversibility-and-heat-semigroup.md` Phase B Steps 0–1 — the graph heat semigroup `heatKernel A t := NormedSpace.exp ℝ (-(t • laplacian A))` (the Active priority table's single **High** row: its operator gate was resolved 2026-08-23 by `sgt-gaps.md`, the independent `spectral-proof` rewrite project naming this exact Phase B as its one remaining Scaffold dependency — a real external consumer, so it outranks every Medium row per the priority-0 rule). This run: the Step-0 survey recorded before any statement, then Step 1 — the definition with symmetry (shelf `laplacian_symmetric` through the pin's `Matrix.IsSymm.exp`) and identity at `t = 0` (`NormedSpace.exp_zero`) — plus QA, zero new axioms per the proposal's own mandate. Steps 2–4 (semigroup law, mass conservation, eigenmode decay) follow in later runs.

**Changes:** intent recorded in the execution plan (selection rationale, the Step-0 survey findings — the pin's `MatrixExponential.lean` is purpose-built norm-free, so the proposal's `expSeries_radius_eq_top` worry does not arise; no `Matrix.exp` declaration exists, the function is `NormedSpace.exp` at matrix type — and the naming/instance corrections). No Lean source touched yet. Also repaired in passing: a duplicated line fragment left in the execution plan's Delivered-milestones header by an earlier run's edit. Planned next: spike in `wip/` (git-ignored), then new `GraphTheory/Heat.lean` + `Heat_QA.lean`, then the record sweep.

## 2026-08-23T06:42:15Z — Reversibility Phase B Steps 0+1 delivered: the graph heat semigroup opened, pure hard crust

**Run:** `20260823T061507Z-run-1`  
**Session:** `ses_fd2c33b2dffe5V3NVp8G9iVOA4`  
**Status:** completed  
**Milestone:** `proposals/reversibility-and-heat-semigroup.md` Phase B Steps 0+1 — the graph heat semigroup, delivered as pure hard crust in the new `Scaffold.Mathlib.GraphTheory.Heat` (**zero new axioms**, count stays 9; `#print axioms` on all four public and all ten QA declarations reads only `propext, Classical.choice, Quot.sound`). QA 1457 → 1467 (`Heat_QA` a new file at 10 theorem declarations). The Active priority table's single **High** row (gate resolved by the real external consumer `sgt-gaps.md`, the `spectral-proof` rewrite project) — the first work selected by the priority-0 rule rather than the Medium ranking.

**Changes:** (1) New `GraphTheory/Heat.lean` (namespace `SpectralGraphTheory`): `heatKernel A t := NormedSpace.exp ℝ (-(t • laplacian A))` — the external consumer's first interface item; `heatKernel_isSymm` (`(heatKernel A t).IsSymm` under `A.IsSymm`, every `t`: shelf `laplacian_symmetric` through `Matrix.IsSymm.smul`/`.neg` and the pin's `Matrix.IsSymm.exp`); `heatKernel_zero` (hypothesis-free, via `zero_smul`/`neg_zero`/`NormedSpace.exp_zero`); and the general square-zero exponential collapse `exp_eq_one_add_of_mul_self_eq_zero` (`M * M = 0 → exp ℝ M = 1 + M`, by `NormedSpace.exp_eq_tsum` + `tsum_eq_sum` over `Finset.range 2` with `pow_add`/`pow_two`/`zero_mul`). (2) New `Scaffold/QA/SpectralGraph/Heat_QA.lean`: the time-zero identity computed on both fixtures (hypothesis-free — holds where the symmetry theorem cannot apply); symmetry through the theorem on K₂ with the hypothesis *derived* from the literal; the **exact closed form** `heatKernel asymAdj 1 = !![0, 1; -1, 2]` on the asymmetric fixture `!![0,1;-1,0]` whose Laplacian `!![1,-1;1,-1]` is square-zero; the **symmetry hypothesis refuted-on-omission** (the computed kernel provably asymmetric, `1 ≠ -1`, the fixture's `IsSymm` provably violated at the same pair); and the **sign witness** `heatKernel asymAdj 1 ≠ exp ℝ (1 • laplacian asymAdj)` (`0 ≠ 2` at `(0,0)`). (3) Umbrella import; records: the proposal (status header, the Step-0 survey record with its norm-free finding and naming corrections, the full Steps-0+1 delivery record, open-next-step → Step 2), `proposals/README.md` (High row, progress paragraph, Delivered row), README (1467, proved-list sentence, module-table row), radar (axis 5 **held at 3.5** per protocol — Step 1 is the definition layer, the heat-kernel *statements* are Steps 2–4; QA axis count synced 1457/39 → 1467/40, held at 4.0), scoreboard (both Direct rows, `lake build` row, lint row, interpretation bullet), the SGT index map (new Heat section + status list), the coverage map (the matrix-exponential row: present and purpose-built norm-free — a genuine map correction), backlog item 5 (delivery-opened note), the execution plan (also repairing a duplicated line fragment an earlier run left in its Delivered-milestones header), and this log. Nothing committed.

**Decisive commands and outcomes:** spike first (`wip/heat_spike.lean`: two elaboration rounds to green — the fixes were `zero_mul` vs the mis-guessed `mul_zero`, the `tsum_eq_sum` hypothesis form `∀ b ∉ s` (a `to_additive` of `tprod_eq_prod`, greppable only by its multiplicative name), `Finset.sum_range_succ` twice for the `range 2` sum, and the `Matrix.IsSymm.apply` swapped-argument convention; the spike also caught the first draft's wrong `(1,1)` entry in the closed form — `1 + -(-1) = 2`, not `0` — the exact failure mode numeric QA exists for); `lake env lean Scaffold/Mathlib/GraphTheory/Heat.lean` — zero errors, zero warnings; `lake env lean Scaffold/QA/SpectralGraph/Heat_QA.lean` — zero errors, zero warnings (the transfer fixes: dropping a doubled `Matrix.of` wrapper the house fixture style suggested, and reordering the value theorem before its consumer); `lake build` on both targets ✔; `#print axioms` via `wip/heat_axcheck.lean` on all fourteen declarations — `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2252 targets (+2), "Build completed successfully", detached per the recorded procedure)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1467 QA declarations / 9 explicit axioms / 0 sorries**, idempotent under re-run).

**Verification:** every changed module elaborates directly with zero errors/warnings and is linked into the full default build (the umbrella imports `GraphTheory.Heat`). The delivery is fully proved hard crust — nothing axiom-backed was added, so nothing is conditional. The QA is load-bearing on the definition's exact shape: the closed form pins the exponent's negation, scalar action, and time parameter in one exactly-evaluated matrix (reachable because the fixture's Laplacian is square-zero, so the series collapses); the refutation ties the symmetry hypothesis to a refuted hypothesis-free form at a fixture satisfying every other hypothesis; and the sign witness separates the delivered `e^{-L}` from the concretely computed `e^{+L}`.

**Remaining risk:** low for what is delivered. Phase B is one step in: the semigroup law (Step 2) is one `Matrix.exp_add_of_commute` away at commuting scalar multiples — the survey record shows no ball hypothesis will be needed; mass conservation (Step 3) lifts `laplacian *ᵥ onesVec = 0` through the series (the `tsum` induction is its genuine content); eigenmode decay (Step 4) needs the eigenbasis transfer `exp` ↔ spectral-calculus identity, the step the proposal itself rates hardest (its stop-and-record clause applies if the pin's API falls short). The matrix↔vector bridge to `Perturbation.Duhamel.heatApply` is recorded as Step-4 business, not started.

**Next handoff:** **Reversibility Phase B Step 2** (the semigroup property, per the proposal's one-step-per-run instruction; QA on the square-zero fixture where both sides are exactly evaluable), then Steps 3–4. After Phase B completes, the Medium rows by leverage — approximate spectral projection (Step 0 first; a negative tractability finding is a valid recorded outcome) and the PF consumers (irreducible stationary distributions, PageRank) as new-proposal candidates.

## 2026-08-23T15:33:34Z — Reversibility Phase C Steps 0+1 in delivery: survey + the heat-flow derivative at zero

**Run:** `20260823T153334Z-run-1`  
**Session:** `ses_fd0c25a7effe6yuA5kfIJzIgzR`  
**Status:** in-progress  
**Milestone:** `proposals/reversibility-and-heat-semigroup.md` Phase C, Steps 0+1 — the Active priority table's first High row (all three High rows are new 2026-08-23/24 `sgt-gaps.md` follow-ups; priority-0 rule). Step 0: survey the pin's `Real.exp` remainder/Taylor surface and commit the Step-2 remainder-bound statement shape. Step 1: `heatKernel_mulVec_hasDerivAt_zero` (`HasDerivAt (fun t => heatKernel A t *ᵥ x) (-(laplacian A *ᵥ x)) 0`) by the `Duhamel.lean` termwise-sum technique adapted to `heatKernel_mulVec_eq_sum`; zero new axioms. Pre-edit survey verified: shelf `dotProduct_eigvecOf_mulVec` is the exact pairing transfer needed; pin `HasDerivAt.sum`/`smul_const`/`const_smul` and the `Pi` norm instances all present.

## 2026-08-23T15:54:49Z — Reversibility Phase C Steps 0+1 delivered: the survey + the heat-flow derivative at zero

**Run:** `20260823T153334Z-run-1`  
**Session:** `ses_fd0c25a7effe6yuA5kfIJzIgzR`  
**Status:** completed  
**Milestone:** `proposals/reversibility-and-heat-semigroup.md` Phase C, Steps 0+1 — the Active priority table's first High row (the new 2026-08-23/24 `sgt-gaps.md` wave; priority-0 rule), the second named external-consumer request on the Phase B `heatKernel` interface (the `spectral-proof` rewrite's dissolution-theorem analytic input). Delivered as pure hard crust in `GraphTheory.Heat` (**zero new axioms**, count stays 9; `#print axioms` on both new public and all four new QA declarations reads only `propext, Classical.choice, Quot.sound`). QA 1503 → 1507 (`Heat_QA` 46 → 50). Radar axes 5 and QA **held** at 4.0/4.0 per protocol (the derivative is the infinitesimal-generator packaging of the counted continuous-time family; counts synced 1503/40 → 1507/40).

**Changes:** (1) `GraphTheory/Heat.lean` (+4 Mathlib imports: `Calculus.Deriv.{Add,Mul,Prod}`, `SpecialFunctions.ExpDeriv`): the **Phase C Step-0 survey note** in the module docstring (recorded before any statement was frozen) — the pin's `Real.abs_exp_sub_one_sub_id_le` (`|x| ≤ 1 → |exp x − 1 − x| ≤ x²`) committed as Step 2's termwise remainder engine, the Taylor file rejected as plumbing-heavier, and the **vector-form `whnf` elaboration trap recorded** (a direct vector-valued proof times out on a variable vertex type; the `Fin 2` QA statements elaborating fine is what isolated it to variable-type instance synthesis); the entrywise engine **`heatKernel_mulVec_apply_hasDerivAt_zero`** (Duhamel's `heatApply_hasDerivAt` termwise-sum technique adapted to `heatKernel_mulVec_eq_sum`: per-mode `HasDerivAt.exp`/`.mul_const`, `HasDerivAt.sum`, the derivative-at-zero sum re-expanded to `-(L *ᵥ x)` through `eigvecOf_expansion_apply` + the shelf's self-adjoint pairing transfer `dotProduct_eigvecOf_mulVec` — the pre-edit survey finding that this lemma already exists saved the run its one planned sub-proof); and the headline **`heatKernel_mulVec_hasDerivAt_zero`** (`HasDerivAt (fun t => heatKernel A t *ᵥ x) (-(laplacian A *ᵥ x)) 0`, the infinitesimal generator `d/dt e^{-tL} x |₀ = -L x`), assembled by the pin's `hasDerivAt_pi`; `hA` carried exactly as the expansion lemma already requires. (2) `Heat_QA.lean` +4: the derivative value on K₂ at `![1,3]` pinned to `![2,-2]` by **two independent routes to one statement** (theorem route vs. raw route through the Step-4 closed form `1 + ((e^{-2t}-1)/2) • L` + scalar calculus only — no eigenbasis, no expansion, no `hasDerivAt_pi`), plus the **infinitesimal-conservation cross-check in both directions** (derivative `0` at `onesVec` through the Phase C theorem + `laplacian_ones_in_kernel`, vs. from Step 3's constant-flow conservation alone — Phase C and Phase B Step 3 checking each other). (3) Records: the proposal (status header, the Phase C delivery record with pin-technique notes — the `−t * c` vs `-(t * λ)` parenthesization mismatch, `const_mul`'s left-constant elaboration, `Finset.sum_neg_distrib` as the ungreppable `to_additive` child, the `mul_assoc` residue, the QA `by_cases` t=0 extension — open-next-step → Step 2), `proposals/README.md` (the High row), README (1507, proved-list + module-table rows), the radar (axis-5 + QA-axis hold records, counts synced), the scoreboard (both Direct rows, the `lake build` row, lint row, a new interpretation bullet; regenerated 1507/9/0 idempotent), the SGT index map (Heat +2 declaration rows, Phase C status line), the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/heatC_spike.lean`, eight rounds to green — the fixes became the recorded trap list, the decisive one the entrywise-plus-`hasDerivAt_pi` restructure after the vector-form `whnf` timeout; a `sorry`-probe isolated the timeout to the *proof*, not the statement); `lake build Scaffold.Mathlib.GraphTheory.Heat` ✔ (2044 targets) then `lake env lean Scaffold/QA/SpectralGraph/Heat_QA.lean` — zero errors, zero warnings; `lake build Scaffold.QA.SpectralGraph.Heat_QA` ✔ (2045); `#print axioms` via `wip/heatC_axcheck.lean` on all six new declarations — the standard three only; **full `lake build` ✔ (2252 targets, "Build completed successfully"; no warnings in the changed modules — the log's Scaffold-tree warnings are the documented pre-existing set in untouched modules)**; `lint_axioms` (9, unchanged) — no issues; `check_citations` — pass; `check_markdown_links` — pass; `generate_qa_scoreboard.py` — regenerated idempotent (**1507/9/0**, `Heat_QA` 46 → 50); `git status` — only the intended files changed plus pre-existing/parallel untracked operator files (`docs/scaffold.jpeg`, and `docs/scaffold_map.{html,svg}` + `scripts/generate_scaffold_map_svg.py`, created outside this run's edits and preserved untouched).

**Verification:** every changed module elaborates directly with zero errors/warnings and is linked into the full default build; QA built by explicit target. The delivery is fully proved hard crust — nothing axiom-backed was added, so nothing is conditional. QA is load-bearing through route independence at both new theorem families (the numeric derivative proved by two unrelated chains — eigenbasis-expansion differentiation vs. closed-form-collapse scalar calculus — and infinitesimal conservation cross-checking Phase C against Phase B Step 3 in both directions), so a wrong sign, factor, or eigenvalue anywhere in the delivered chain contradicts an independent computation.

**Remaining risk:** the derivative statement carries `hA : A.IsSymm` because the eigenbasis expansion does (the mathematical statement is hypothesis-free — the asymmetric fixture's derivative also exists — but proving it without the eigenbasis needs the series/semigroup route, deliberately not built); Phase C Step 2 (the remainder bound) is not yet delivered, so the external consumer's dissolution-theorem input is half-discharged (the derivative yes, the quantitative remainder no). The QA fixtures are 2×2; the theorems are size-general. The `spectral-proof` consumer has not been run against the delivered interface — outside this repository's authority.

**Next handoff:** **Phase C Step 2** — the first-order remainder bound on `[0, T]`, termwise through the surveyed `Real.abs_exp_sub_one_sub_id_le` at `|t * λᵢ| ≤ 1` (entrywise form primary, Euclidean via Cauchy–Schwarz if cheap), with the proposal's named QA pair: a concrete-bound witness cross-checked against `heatKernel`'s direct exponential-series value, and a boundary-degradation witness showing the bound worsens as `T` grows. Then the remaining High rows by leverage (Tikhonov Phase 2, discrete affine convergence), per the Active priority table.

## 2026-08-23T17:01:18Z — Reversibility Phase C Step 2 in delivery: the first-order remainder bound

**Run:** `20260823T170118Z-run-1`  
**Session:** `ses_fd0739ccaffeEIV1ltdF9DeEhv`  
**Status:** in-progress  
**Milestone:** `proposals/reversibility-and-heat-semigroup.md` Phase C, Step 2 — the Active priority table's first High row and the recorded open next step of the Steps 0+1 delivery. The first-order remainder bound `|heatKernel A t *ᵥ x a − x a + t (L *ᵥ x) a| ≤ t² · ∑ λᵢ² |vᵢ ⬝ᵥ x| |vᵢ a|` at `|t · λᵢ| ≤ 1`, termwise through the surveyed `Real.abs_exp_sub_one_sub_id_le` per the Step-0 committed shape (entrywise form primary — the boundary-observable coordinate the consumer's dissolution theorem reads), plus the `[0, T]` interval packaging; QA pair per the proposal: concrete-bound witness cross-checked against the closed-form exponential value, boundary-degradation witness. Zero new axioms. Pre-edit survey verified: shelf `eigvecOf_expansion_apply`/`dotProduct_eigvecOf_mulVec`/`eigvecOf_inner` supply the expansion/pairing/unit-norm facts; pin `Real.abs_exp_sub_one_sub_id_le` at `Mathlib/Data/Complex/Exponential.lean:1211`.

## 2026-08-23T17:29:55Z — Reversibility Phase C Step 2 delivered: the first-order remainder bound; the proposal COMPLETE

**Run:** `20260823T170118Z-run-1`  
**Session:** `ses_fd0739ccaffeEIV1ltdF9DeEhv`  
**Status:** completed  
**Milestone:** `proposals/reversibility-and-heat-semigroup.md` Phase C, Step 2 — the Active priority table's first High row and the Steps 0+1 delivery's recorded open next step. Delivered as pure hard crust in `GraphTheory.Heat` (**zero new axioms**, count stays 9; `#print axioms` on both new public and all fifteen new public QA declarations reads only `propext, Classical.choice, Quot.sound`). QA 1507 → 1522 (`Heat_QA` 50 → 66). Radar axes 5 and QA **held** at 4.0/4.0 per protocol (a quantitative refinement within the calculus layer the axis already counts; counts synced 1507/40 → 1522/40). With Step 2, **Phase C is complete in two runs and the proposal is closed end-to-end** (A, B, C; zero axioms throughout) — the external `spectral-proof` consumer's full requested interface discharged: Phase B's four items plus the dissolution-theorem analytic pair (derivative + quantitative remainder).

**Changes:** (1) `GraphTheory/Heat.lean`: `heatKernel_firstOrder_remainder_apply_le` — on the window `∀ i, |t · λᵢ| ≤ 1`, `|(heatKernel A t *ᵥ x) a − x a + t ((laplacian A *ᵥ x) a)| ≤ t² · ∑ᵢ λᵢ² |vᵢ ⬝ᵥ x| |vᵢ a|` at every coordinate `a` (the boundary-observable form), at exactly the Step-0-surveyed committed shape — the flow coordinate through `heatKernel_mulVec_eq_sum`, `x a` through `eigvecOf_expansion_apply`, the generator coordinate through the same expansion + the pairing transfer `dotProduct_eigvecOf_mulVec`, the three sums combined termwise (the pin's to_additive children right-to-left), triangle by `Finset.abs_sum_le_sum_abs`, per mode the surveyed `Real.abs_exp_sub_one_sub_id_le` at `x := −(t·λᵢ)`; **no nonnegativity hypothesis** (per-mode, any symmetric network); plus `heatKernel_firstOrder_remainder_interval` (the uniform `[0, T]` packaging, monotonicity hypothesis-transfer). Euclidean variant deliberately not stated (√n-loss plumbing, no new content; recorded). (2) `Heat_QA.lean` +16 (15 public, 1 private): the K₂ eigenvalue inventory per vertex index (PSD/trace/determinant — `edge_eigvalOf_cases`, `edge_eigvalOf_exists_two`), the eigenmode structure `v = c • ![1,−1]` with `2c² = 1` (`edge_eigvecOf_mode_two`, through the fresh coordinate helper `edgeLaplacian_mulVec_coords` + `eigvecOf_inner`) making the spectral constant **exactly 4** (`edge_remainder_sum_eq`) orientation-sign-independent, the window fact `edge_window` (`[0, 1/2]`), the proposal's named QA pair — the **concrete-bound witness** (theorem at the endpoint `t = 1/2`, RHS evaluated to the concrete `1`; the raw value `1 − 2t − e^{−2t}` pinned at every nonzero time by the closed-form route, no eigenbasis; composite cross-check `e⁻¹ ≤ 1`) and the **boundary-degradation witness** (both times' concrete constants `1/4` at `t = 1/4` via the interval route and `1` at `t = 1/2`, pinning the `t²` scaling — a wrong power of `t` contradicts at least one component) — plus the **fence** (the window hypothesis refuted at `t = 1`: `|1·2| = 2 ≰ 1`; the first-order claim local by construction). (3) Records: the proposal (status header → COMPLETE, the Step-2 delivery record with the run's pin-technique trap list), `proposals/README.md` (the High row → Delivered, the stale Phase-B prose de-staled, the Active table now headed by Tikhonov Phase 2), README (1522; heat-semigroup paragraph + module-table row), the radar (axis-5 + QA-axis hold records, counts synced), the scoreboard (both Direct rows, the `lake build` row, lint row, a new interpretation bullet; regenerated 1522/9/0 idempotent), the SGT index map (+2 declaration rows, Phase C status line), the execution plan, this log.

**Decisive commands and outcomes:** spiked first — `wip/heatC2_spike.lean` (core; two rounds to green: the `set`-vs-`rw` abstraction trap and the sum-distrib direction) then `wip/heatC2_qa_spike.lean` (QA; four rounds: `⟨0,⋯⟩`-literal linarith atoms solved by defeq `have`-ascription, ℕ-numeral `2 • v` smul, `mul_self_abs` absent (→ `← abs_mul` + `mul_self_nonneg`), `if_pos rfl` leaving `if True` (→ `if_true`), and the collapsed-form `rw` order in the degradation composite) — both green before transfer; `lake env lean` on `Scaffold/Mathlib/GraphTheory/Heat.lean` and `Scaffold/QA/SpectralGraph/Heat_QA.lean` — zero errors, zero warnings each; `lake build Scaffold.Mathlib.GraphTheory.Heat` ✔ (2044) and `lake build Scaffold.QA.SpectralGraph.Heat_QA` ✔; `#print axioms` via `wip/heatC2_axcheck.lean` on all seventeen new declarations — the standard three only; **full `lake build` ✔ (2252 targets, "Build completed successfully"; zero warnings in the changed modules — the log's warning mass verified to be entirely the Mathlib-pin doc-string set)**; `lint_axioms` (9, unchanged) — no issues; `check_citations` — pass; `check_markdown_links` — pass (re-run after all record edits); `generate_qa_scoreboard.py` — regenerated, idempotent (**1522/9/0**, `Heat_QA` 50 → 66); `git status` — only the intended files changed plus pre-existing/parallel untracked operator files (`docs/scaffold.jpeg`, `docs/scaffold_map.{html,svg}`, `scripts/generate_scaffold_map_svg.py`, created outside this run and preserved untouched).

**Verification:** every changed module elaborates directly with zero errors/warnings and is linked into the full default build; QA built by explicit target. The delivery is fully proved hard crust — nothing axiom-backed was added, so nothing is conditional. QA is load-bearing through exact numeric evaluation on both sides of the inequality: the theorem's spectral constant is evaluated to *exactly* 4 on K₂ (independent of the spectral-theorem choice's eigenvector orientation, via the `2c² = 1` structure), the raw remainder is pinned by the closed-form route at every time, and the two times' concrete bounds (1/4 and 1) make the t² scaling falsifiable against wrong powers — while the fence witness proves the window hypothesis genuinely cuts at `t = 1/2`, so nothing global is being claimed through a local statement.

**Remaining risk:** low for what is delivered. The remainder bound carries `hA : A.IsSymm` exactly as the eigenbasis expansion requires (as with the derivative); the window is per-eigenvalue `|t · λᵢ| ≤ 1`, the weakest usable form but not the only packaging a consumer might want (a `T ≤ 1/λ_max` sufficient form would need a maximal-eigenvalue interface — not stated, not requested). The `spectral-proof` consumer has not been run against the delivered interface — outside this repository's authority. The Active table's two remaining High rows (Tikhonov Phase 2, discrete affine convergence) are open.

**Next handoff:** **Tikhonov Phase 2** — the hard-filter limit: the positive-eigenvalue limit of `tikhonovShrinkage π λ` plus the finite tail-suppression corollary, stated as suppression per the requester's non-overclaim instruction (continuity-of-division at a nonzero denominator + a finite sum of already-proved bounds; no new axioms); then discrete affine convergence. The Medium rows follow (approximate spectral projection Step 1a next, its Step 0 delivered).

## 2026-08-23T21:58:00Z — Approximate spectral projection Step 1a in delivery: the Krylov/Chebyshev interface layer

**Run:** `20260823T215632Z-run-1`  
**Session:** `ses_fcf5ff831ffe3LgTQYXa9t5h8p`  
**Status:** in-progress  
**Milestone:** `proposals/approximate-spectral-projection.md` Step 1a — the interface layer (the leading Medium row of the Active priority table, which holds no High rows, and the previous run's recorded next handoff): the Step-0 spike's four real lemmas hardened into a new `Scaffold/Mathlib/GraphTheory/Krylov.lean` (a real `krylovSpan` definition, `sum_mulVec`, the Chebyshev band bound, polynomial eigenvector action, Krylov membership, the hypothesis-form `kanielPaigeSkeleton`) plus the two priced shallow gaps (`natDegree (T ℝ n) = n`, the growth lemma `1 ≤ T_m(x)` at `x ≥ 1`), with the module-level survey note. Leverage: the shared Chebyshev layer for both the 1b/1c Kaniel–Paige theorem and the recorded Chebyshev-filter second consumer. QA proportionate to an interface layer; zero new axioms (count stays 9). Spike is already green — this run is the transfer.

## 2026-08-23T22:25:00Z — Approximate spectral projection Step 1a delivered: the Krylov/Chebyshev interface layer

**Run:** `20260823T215632Z-run-1`  
**Session:** `ses_fcf5ff831ffe3LgTQYXa9t5h8p`  
**Status:** completed  
**Milestone:** `proposals/approximate-spectral-projection.md` Step 1a — the interface layer (the leading Medium row of the Active priority table, which holds no High rows, and the previous run's recorded next handoff) — **DELIVERED as pure hard crust, zero new axioms (count stays 9; `#print axioms` via `wip/krylov1a_axcheck.lean` on all 8 public theorems + the `krylovSpan` definition + all 19 QA declarations reads only `propext, Classical.choice, Quot.sound`). QA 1571 → 1590 (`Krylov_QA` a new file at 19).**

**Changes:** (1) the new `Scaffold/Mathlib/GraphTheory/Krylov.lean` (namespace `SpectralGraphTheory`, at the shelf's `V : Type` interface per the Step-0 finding, the umbrella importing it): the scalar Chebyshev layer — `abs_T_eval_le_one` (the spike's proof unchanged), **both Step-0-priced shallow gaps closed** — `natDegree_T` (`(T ℝ (n:ℤ)).natDegree = n` by `Nat.twoStepInduction` at `T_add_two` with `natDegree_sub_eq_left_of_natDegree_lt` doing the degree arithmetic) and `one_le_eval_T_of_one_le` (`1 ≤ T_m(x)` at `x ≥ 1` through the private conjunction engine `eval_T_pair_mono`, ordinary induction sufficing with index-monotonicity as the byproduct); the Krylov layer — `sum_mulVec` (the priced pin-gap push), the real **`krylovSpan`** definition (the hardening over the spike's inlined span), `scalar_mul_eq_smul`, `aeval_mulVec_eq_eval_smul` (through `Heat.pow_mulVec_smul`), `aeval_mulVec_mem_krylovSpan`; and `kanielPaigeSkeleton` at the spike's exact hypothesis form with the five named spectral-layer discharge sites (`hp₁`/`horth`/`horthM`/`hbottom`/`hband`) preserved verbatim as Step 1b's contract. The module docstring carries the survey note; the Saad §6 citation stays with the proposal that owns the statement. (2) `Scaffold/QA/SpectralGraph/Krylov_QA.lean` (+19): raw Chebyshev pins (`T₂(0) = −1`, `T₃(1/2) = −1` interior band equality, `T₂(1/4) = −7/8` strict with the theorem instance composed to `7/8 ≤ 1`), `natDegree` instances, the growth pair two-route (`1 ≤ T₂(2)` theorem vs. `T₂(2) = 7` raw), `sum_mulVec` on concrete matrices, the polynomial action and Krylov membership each by **two independent routes** (transfer theorem vs. hand-computed `aeval diagM (X²+1) = diagM² + 1`; polynomial interface vs. generator-direct), the annihilator `(X − 2)(diagM) *ᵥ e₁ = 0`, the **degree-guard refutation** (`M e₁ = e₂ ∉ krylovSpan M e₁ 1` — the hypothesis-free form false, `hdeg` load-bearing), the **composed-use witness** (`T ℝ 5`'s image in the 6-th Krylov span with `hdeg` from `natDegree_T` alone — 1b's exact consumption pattern), and the **full skeleton instantiation** on the diagonal fixture (all twelve hypotheses hand-discharged, bound constant pinned `= 2` against raw `rayleigh diagM b = 1`, the instantiated bound reading `2 − 1 = 1 ≤ 2` end-to-end). (3) Records: the proposal (status header, the Step-1a delivery record with this run's trap list, open-next-step → 1b), `proposals/README.md` (the Medium row + the progress paragraph), README (1590; module-table row + proved-list sentence), the radar (QA axis synced 1571/41 → 1590/42, held 4.0), the scoreboard (all four verification rows, a new interpretation bullet; regenerated idempotent 1590/9/0), the SGT index map (new Krylov section + 9 declaration rows), the umbrella `Scaffold.lean`, the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/krylov1a_spike.lean`, two rounds to green — the fixes becoming the recorded trap list: `Nat.twoStepInduction`'s `more` case receives `P n` before `P (n+1)`; `Polynomial.leadingCoeff_eq_zero` cannot rewrite a `≠`-goal directly (`rw [Ne, …]` first); `(T ℝ 5)` OfNat and `(T ℝ ↑5)` cast are defeq but rw-incompatible, so composed-use statements must write the cast form; **the numeric-default trap's polynomial face** — an un-ascribed `C 1` or bare `X` in a goal statement elaborates the whole `aeval` at `ℕ[X]` (`pp.all` exposes `aeval ℕ …` after display-identical `rw` failures), and a bare `2 • v` picks the ℕ-smul through ℝ's `AddMonoid` nsmul, which does not unify with the ℝ-smul the theorems conclude — every polynomial in a QA statement now carries `: ℝ[X]` and every smul numeral a `(2 : ℝ)` ascription; matrix-literal tails that `norm_num` leaves as cons-junk close robustly by `funext i; fin_cases i` + `norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]`, and literal `![m₀, m₁] i` selection is a `rfl` fact); `lake env lean` on the module and the QA file — zero errors, zero warnings each; `lake build Scaffold.Mathlib.GraphTheory.Krylov` ✔ then `lake build Scaffold.QA.SpectralGraph.Krylov_QA` ✔; `#print axioms` via `wip/krylov1a_axcheck.lean` — the standard three only, all 28 declarations; **full `lake build` ✔ (2256 targets, +3, "Build completed successfully"; zero warnings in the changed modules — the log's only Scaffold diagnostic the documented pre-existing unused-variable note in untouched `Derived/ProjectorDrift.lean`)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1590/9/0**, idempotent).

**Verification:** every changed module elaborates directly with zero errors/warnings and both new modules build as explicit targets; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing is conditional. QA is load-bearing at the interface level: the polynomial action and Krylov membership are each reached by two independent API paths (a wrong transfer constant contradicts the hand-computed `aeval` route; membership by polynomial vs. generator routes), the degree hypothesis is *refuted in proved form* where dropped (the hypothesis-free membership false on the line `ℝ·e₁`), the composed-use witness exercises exactly the `natDegree_T`-discharges-`hdeg` pattern Step 1b will scale, and the skeleton instantiation checks that the full hypothesis contract is satisfiable on concrete data with its conclusion numerically non-vacuous.

**Remaining risk:** the skeleton is hypothesis-form by design — its five spectral-layer sites are discharged in QA only on a diagonal fixture, not from the eigenbasis machinery; that is Step 1b's scope, and until it lands the Kaniel–Paige bound itself is not yet stated at the proposal's final shape (no overclaim: the module carries interface pieces and the skeleton, not the theorem). The Chebyshev layer is shared with the recorded Chebyshev-filter second consumer, which remains unattempted per the one-shape-per-run rule. QA breadth is `Fin 2`-only, appropriate for an interface layer whose consumers' fixtures (the 1c diagonal 3×3) are still ahead.

**Next handoff:** **Step 1b — the spectral discharge** (`proposals/approximate-spectral-projection.md` at its updated open-next-step: the eigenbasis-expansion layer discharging the skeleton's five named sites, with `natDegree_T` + `Polynomial.natDegree_comp` supplying `hdeg` for the affine band map), then 1c (statement + QA retiring the milestone). The PF consumers (irreducible stationary distributions, PageRank) remain new-proposal candidates per the one-step discipline.

## 2026-08-23T23:29:53Z — Approximate spectral projection Step 1b in delivery: the spectral discharge

**Run:** `20260823T232953Z-run-1`  
**Session:** `ses_fcf0e856dffe6j2B1fa0YEBjvx`  
**Status:** in-progress  
**Milestone:** `proposals/approximate-spectral-projection.md` Step 1b — the spectral discharge (the leading Medium row of the Active priority table, which holds no High rows, and the Step-1a run's recorded next handoff): the eigenbasis-expansion layer discharging the skeleton's five named spectral sites (`hp₁`/`horth`/`horthM`/`hbottom`/`hband`) on the shelf's own machinery — the general-eigenvector self-adjointness transfer (eigenvOf-free, so any unit eigenvector qualifies), the component form `(v i) ⬝ᵥ (p(M) y) = p(μ i) ((v i) ⬝ᵥ y)` with Parseval/`quadForm_eigvalOf`, the band/parallel dichotomy, the affine band map `w(λ) = (2λ − Ltwo − Lbot)/(Ltwo − Lbot)` composed with `T_{k−1}` supplying `hp₁`/`hdeg`/`hTv`, b's unit decomposition, and the composite `kanielPaigeChebyshev` capstone. Zero new axioms (count stays 9). Spike first in `wip/krylov1b_spike.lean`, transfer on green, QA proportionate (two-route engine checks, `bandMap` pins, the composite on `diag(3,1,0)` cross-checked raw).

## 2026-08-24T00:13:07Z — Approximate spectral projection Step 1b delivered: the spectral discharge

**Run:** `20260823T232953Z-run-1`  
**Session:** `ses_fcf0e856dffe6j2B1fa0YEBjvx`  
**Status:** completed  
**Milestone:** `proposals/approximate-spectral-projection.md` Step 1b — the spectral discharge (the leading Medium row of the Active priority table, which holds no High rows, and the Step-1a run's recorded next handoff) — **DELIVERED as pure hard crust, zero new axioms (count stays 9; `#print axioms` via `wip/krylov1b_axcheck.lean` on all 14 new public theorems + the `bandMap` definition + all 16 new QA declarations reads only `propext, Classical.choice, Quot.sound`). QA 1590 → 1606 (`Krylov_QA` 19 → 35).** Radar QA axis **held at 4.0** per protocol (a discharge layer within the Kaniel–Paige family the axis already counts; counts synced 1590/42 → 1606/42).

**Changes:** (1) `Scaffold/Mathlib/GraphTheory/Krylov.lean` gained the `KrylovDischarge` section: the **general-eigenvector transfer layer** (`eigvec_dotProduct_mulVec` — self-adjointness in coordinates at any eigenvector; `_pow_mulVec` through `transpose_pow` + `Heat.pow_mulVec_smul`; `_aeval_mulVec` — the `horth` engine, `u ⬝ᵥ (p(M) g) = (u ⬝ᵥ g) · p(μ)`), the **eigenbasis component layer** (`eigvecOf_dotProduct_aeval_mulVec` + the Parseval and quadratic-form resolution identities `dotProduct_aeval_mulVec_self`/`quadForm_aeval_mulVec` — the `hband`/`hbottom` engines), the **affine band map** (`bandMap` with the closed-form eval, endpoint pins, band range, growth, and degree `1` — the `hp₁`/`hdeg`/`hTv` supply at `T_{k−1} ∘ w`), `exists_unit_decomposition` (unit `b` along unit `u`, `c² + s² = 1` with `1 − c²` realized as the residual's own squared norm — no Cauchy–Schwarz), and the capstone **`kanielPaigeChebyshev`** — the full skeleton conclusion with every spectral site discharged from the eigenbasis-level band hypothesis (`hpar`: out-of-band eigenvectors parallel to `u`; the multiplicity-2 shape `u = (v₁+v₂)/√2` recorded as the reason weaker hypothesis forms fail). (2) `Krylov_QA.lean` +16: the band-map pins two routes (theorems vs. the hand closed form `w(μ) = 2μ − 1`; the composed growth pair `1 ≤ w(3) = 5`), the transfer engines two routes each at a non-basis eigenvector, and the centerpiece on the new 3×3 fixture `diag(3,1,0)` (entrywise-encoded per the recorded `Fin 3` cons-literal trap): `diag310_hpar_QA` deriving the band hypothesis from the eigen-equation alone, the composite instantiated end-to-end with its bound pinned `= 16/75` (`T₁(w(3)) = 5`), and the independent raw route — the actual Krylov witness `(3, 4/5, 0)` exhibited as the generator combination `2(Mb) − b` with its Rayleigh value computed raw to `691/241`, the true gap `32/241` proved strictly inside the delivered `16/75`; plus the unit-decomposition instantiation with both content pins forced (`c = 3/5`, `s² = 16/25`). (3) Records: the proposal (status header, the Step-1b delivery record with this run's pin-technique trap list, open-next-step → 1c), `proposals/README.md` (the Medium row + the progress paragraph de-staled), README (1606; proved-list sentence + module-table row), the radar (QA-axis sync + hold), the scoreboard (all four verification rows, a new interpretation bullet; regenerated 1606/9/0 idempotent), the SGT index map (+13 declaration rows, section status note), the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/krylov1b_spike.lean`, several rounds to green, plus the `wip/krylov1b_iso.lean` isolation that debugged the decomposition's `ring`-vs-`linarith` closers — the fixes became the recorded trap list: **`Polynomial.Chebyshev.T` must be written in full — `open Polynomial` does not reach it, and an unresolved `T` in a statement silently auto-bounds a universe variable named `T`**, surfacing as "function expected at T"; `.comp` binds tighter than application, so `T ℝ (x).comp q` parses as `T ℝ (x.comp q)`; `Matrix.dotProduct_sum` absent at the pin; `⟨n,⋯⟩`-form `fin_cases` indices resist `rfl` (the recorded Heat trap re-hit) while `norm_num` strands `¬⟨2,⋯⟩ = 0` conditions that plain `simp` decides — on `Fin 3` the robust encoding is entrywise fixtures closed by `simp [...] <;> norm_num`; `C_ne_zero` is an iff; `pow_le_pow_left₀`; `X_comp` not `comp_X`; `omit ... in` must precede the docstring and is rejected where the proof legitimately reaches `DecidableEq`); `lake build Scaffold.Mathlib.GraphTheory.Krylov` ✔ (2047 targets) then `lake env lean Scaffold/QA/SpectralGraph/Krylov_QA.lean` — zero errors, zero warnings; `lake build Scaffold.QA.SpectralGraph.Krylov_QA` ✔ (2048); `#print axioms` via `wip/krylov1b_axcheck.lean` on all 31 declarations — the standard three only; **full `lake build` ✔ (2256 targets, "Build completed successfully"; zero warnings in the changed modules — the log's Scaffold-tree warnings are the documented pre-existing set in untouched modules)**; `lint_axioms` (9, unchanged) — no issues; `check_citations` — pass; `check_markdown_links` — pass (re-run after all record edits); `generate_qa_scoreboard.py` — regenerated idempotent (**1606/9/0**); `git status` — only this run's intended files changed (the two Lean modules plus the eight records), **plus one parallel operator change observed and preserved untouched**: the working-tree deletion of `sgt-gaps.md` (tracked at HEAD through the operator's `5dbb21c` "complete sgt-gaps.md" commit; not touched by any command of this run — all three of its items were delivered by prior runs, so the deletion reads as the operator retiring the completed demand file; left exactly as found, neither restored nor committed). The previously-untracked operator files `docs/scaffold.jpeg`/`scaffold_map.{html,svg}` had already been committed by the operator before this run started.

**Verification:** every changed module elaborates directly with zero errors/warnings and both build as explicit targets; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing is conditional. QA is load-bearing at two levels: the transfer engines and band-map pins are each reached by two independent API paths (a wrong transfer constant contradicts the hand computations), and the composite's numerical content is verified against an independent raw route that uses no polynomial interface at all — the actual Krylov witness is exhibited as a generator combination and its Rayleigh gap `32/241` proved strictly inside the delivered `16/75`, so an error in the band map, the Chebyshev evaluation, the dichotomy, or the skeleton assembly contradicts a hand computation.

**Remaining risk:** the composite carries the band hypothesis at the eigenbasis level (`hpar`), which 1c's final statement must connect to its Step-0-recorded hypothesis form ("`λ₂` bounds every non-top eigenvalue + simple top") — on concrete fixtures the QA derives it from the eigen-equation, and 1c must decide whether the final statement instantiates `hpar` directly (honest, interface-level) or derives it from a sorted-spectrum form (heavier, consumer-side; the Step-0 decision says hypotheses, not indexed `evals`). The `b = u` degenerate case reaches the composite only through `hc : c ≠ 0` — 1c's tightness witness must handle it (the skeleton requires `c ≠ 0`, and at `b = u` the bound reads `0 ≤ 0`, exactable directly). QA fixtures are `Fin 2`/`Fin 3`; the theorems are size-general.

**Next handoff:** **Step 1c — the final `kanielPaige` statement + QA retiring the milestone** (`(λ₁ − λₙ) tan²φ / T_{k−1}(1 + 2γ)²` at unit `b` with `u ⬝ᵥ b ≠ 0`, composed from `kanielPaigeChebyshev` + `exists_unit_decomposition`; QA: the `k = 1` degenerate case, the `b = u` tightness witness, the `λ₁ = λ₂` guard refutation). After 1c the milestone closes: the Chebyshev-filter second consumer and the PF consumers (irreducible stationary distributions, PageRank) are new-proposal candidates per the one-step discipline.

## 2026-08-24T01:21:30Z — Approximate spectral projection Step 1c in delivery: the final kanielPaige statement + QA

**Run:** `20260824T012049Z-run-1`  
**Session:** `ses_fceaa390effeA3g0wrKxf8Dkoj`  
**Status:** in-progress  
**Milestone:** `proposals/approximate-spectral-projection.md` Step 1c (the leading Medium row of the Active priority table — no High rows — the Step-1b run's recorded next handoff, and the proposal's recorded open next step): the final `kanielPaige` theorem at the Step-0 recorded shape — unit `b` with `u ⬝ᵥ b ≠ 0`, the decomposition supplied internally by the delivered `exists_unit_decomposition`, the bound as `(Ltop − Lbot)·tan²φ/T_{k−1}(1 + 2γ)²` at `γ = (Ltop − Ltwo)/(Ltwo − Lbot)` — composed from the delivered `kanielPaigeChebyshev` via the identifications `c = u ⬝ᵥ b`, `s² = 1 − c²`, `w(Ltop) = 1 + 2γ`. QA: the final-form `diag(3,1,0)` instantiation (bound = `16/75`, matched against 1b's composite and the raw `32/241` gap strictly inside), the `k = 1` degenerate case (`T₀ ≡ 1` → the plain Rayleigh-gap value `16/3`), the `b = u` tightness witness (bound `0`, attained), and the `λ₁ = λ₂` guard refutation on a `diag(3,3,0)` top-multiplicity fixture. Zero new axioms; spike first, then transfer. Prior runs' uncommitted deliveries preserved untouched.

## 2026-08-24T01:47:12Z — Approximate spectral projection Step 1c delivered: the final kanielPaige statement + QA; the proposal COMPLETE

**Run:** `20260824T012049Z-run-1`  
**Session:** `ses_fceaa390effeA3g0wrKxf8Dkoj`  
**Status:** completed  
**Milestone:** `proposals/approximate-spectral-projection.md` Step 1c (the leading Medium row of the Active priority table — no High rows — the Step-1b run's recorded next handoff, and the proposal's recorded open next step): the final `kanielPaige` theorem + the four proposal-mandated QA witnesses, delivered as pure hard crust (**zero new axioms**, count stays 9; `#print axioms` on all 16 new declarations — 1 public + 15 QA — reads only `propext, Classical.choice, Quot.sound`). QA 1606 → 1621 (`Krylov_QA` 35 → 50). **The proposal is COMPLETE** — Steps 0/1a/1b/1c across four runs, all zero-axiom.

**Changes:** (1) `GraphTheory/Krylov.lean`'s new Step-1c section: **`kanielPaige`** at the Step-0 recorded shape — unit `b` with `u ⬝ᵥ b ≠ 0` the only starting-vector hypothesis (the decomposition internal via 1b's `exists_unit_decomposition`), the bound in the classical `tan²φ`/γ form `(Ltop − Lbot)·(1 − (u ⬝ᵥ b)²)/(u ⬝ᵥ b)²/T_{k−1}(1+2γ)²` at `γ = (Ltop−Ltwo)/(Ltwo−Lbot)`, composed from `kanielPaigeChebyshev` by three short identifications (`c = u ⬝ᵥ b`, `s² = 1 − c²`, `w(Ltop) = 1 + 2γ`); the Saad §6 locator attached to the statement's docstring with the clean-room verify-against-the-physical-copy caveat (proved, not admitted). (2) `Krylov_QA.lean` +15 in the Step-1c section: the final-form instantiation with the bound **proved expression-equal** to the 1b composite's `16/75` (γ-value two-route: `T₁(5) = 5` raw via `T_one` vs the composed `(T₁∘w)(3)`), the raw gap `32/241` strictly inside; the `k = 1` degenerate case (`T₀ ≡ 1`, bound = the plain Rayleigh-gap value `16/3`, raw `R(b) = 43/25`, gap `32/25`); the `b = u` tightness (bound `= 0`, the witness pinned to Rayleigh value exactly `Ltop` from both sides); and the `λ₁ = λ₂` guard **refuted in proved form** on the top-multiplicity `diag(3,3,0)` fixture — `hpar` itself false (eigenvalue dichotomy from the eigen-equation, then orthonormality: `t₀t₁ = 0` against `t₀² = t₁² = 1`), and the hypothesis-free conclusion refuted with every other hypothesis verified (the `k = 1` Krylov line's Rayleigh value `8/3` computed by smul-linearity, true gap `1/3 > 1/4` = bound). (3) Records: the proposal (status header COMPLETE, the Step-1c record with pin-technique notes, open-next-step closed with the named follow-ons — the Chebyshev-filter second consumer, the cosh non-vacuity corollary, the Rayleigh–Ritz sup form), `proposals/README.md` (the Medium row retired to the Delivered table; the progress paragraph rewritten; **plus two de-stalings: the pre-existing `-**PLACEHOLDER**-` artifact in the scoreboard's interpretation section repaired, and the stale directed-graph-operators Medium row — its own Why column already read "PROGRAM COMPLETE", full record in the Delivered table — removed per the file's own proposal-boundary rule, so the Active table now holds only Low rows**), README (1621; proved-list sentence + module-table row), radar (QA axis 1606/42 → 1621/42 held 4.0), scoreboard (four verification rows, interpretation bullet, artifact repair), SGT index map (+`kanielPaige` row, section note → program COMPLETE), the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/krylov1c_spike.lean`, several rounds to green, every `#print axioms` the standard three — the fixes becoming the 1c pin-technique record: `mul_div_cancel_left₀` strands on a `MulDivCancelClass` metavariable inside `rw` → `rw [div_eq_iff h]; ring` on a standalone `have`; `zero_smul` not `smul_zero`; `simp [huu, hgu]` where explicit dotProduct-smul chains strand on simp's own normalization; the `Fin 3` nested-if trap re-hit — `simp [defs, Matrix.dotProduct, Fin.sum_univ_three]; norm_num` the robust closure, plain `simp` deciding the index equalities; the refutation's Rayleigh value by smul-linearity rewrites (`rw [← hr, smul_dotProduct, mulVec_smul, …]`) rather than entrywise sums); `lake env lean` on the module and the QA file — zero errors, zero warnings each; `lake build Scaffold.Mathlib.GraphTheory.Krylov` ✔ then `lake build Scaffold.QA.SpectralGraph.Krylov_QA` ✔; `#print axioms` via `wip/krylov1c_axcheck.lean` on all 16 new declarations — the standard three only; **full `lake build` ✔ (2256 targets, "Build completed successfully"; zero warnings in the changed modules — the log's only Scaffold diagnostic the documented pre-existing unused-variable note in untouched `Derived/ProjectorDrift.lean`)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1621/9/0**, idempotent).

**Verification:** every changed module elaborates directly with zero errors/warnings and is linked into the full default build; QA certified by direct elaboration plus its explicit build target. The delivery is fully proved hard crust — nothing axiom-backed was added, so nothing is conditional. QA is load-bearing at every level the proposal names: the final-form bound is proved *equal as an expression* to the 1b composite's (a wrong γ-form or inverted tan²φ in the restatement contradicts the equality), the degenerate and tightness witnesses pin the two endpoint behaviors (`T₀ ≡ 1` reducing to the plain Rayleigh gap; bound `0` attained at `b = u`), and the guard refutation is two-level — `hpar` proved false on the fixture *and* the hypothesis-free conclusion refuted with every other hypothesis verified true, so the simple-top hypothesis is exercised as a fence, not decoration.

**Remaining risk:** the Saad §6 locator remains section-level with the clean-room caveat (to be confirmed against the physical copy before any committed external use — no axiom involved, so nothing conditional). QA fixtures are 3×3 diagonal; the theorems are size-general, so the risk is to QA breadth, not correctness. The recorded follow-ons (Chebyshev-filter second consumer, cosh non-vacuity corollary, Rayleigh–Ritz sup form) are intentionally not started — each needs its own document per the one-step discipline.

**Next handoff:** the Active priority table holds no High and no Medium rows — every remaining row is a Low blocked on a human/technical decision an autonomous run cannot make. Next run falls through to the center-out SGT policy: the Chebyshev-filter shape (the same proposal's recorded second consumer — own document first), a PF-consumer proposal (irreducible stationary distributions, PageRank), or a backlog-gated item.

## 2026-08-24T02:48:31Z — Irreducible stationary distributions in delivery: the first Perron–Frobenius theorem consumer

**Run:** `20260824T024831Z-run-1`  
**Session:** `ses_fce55f957ffe5RyAw4FqyasReu`  
**Status:** in-progress  
**Milestone:** `proposals/irreducible-stationary-distributions.md` (new this run, added to the Active priority table as its only High row) — the first *theorem* consumer of the `perron_frobenius` axiom: existence, uniqueness up to positive scale, and the `∃!` packaging of a stationary distribution for the irreducible nonnegative walk, plus the full-support corollary. Leverage: load-bearing on the axiom's clause 5 (any nonnegative eigenvector's eigenvalue is the Perron root — pinned to `r = 1` via the shelf's row-stochasticity at `onesVec`) and clause 6 (uniqueness up to positive scalars) exactly; the directed axis' first theorem; zero new axioms (count stays 9). Route surveyed pre-edit: the transposed application's root falls to the bilinear pairing through the pin's `Matrix.dotProduct_mulVec` + `Matrix.mulVec_transpose` — no charpoly or complexification needed.

**Changes (intended):** the proposal document (Step 0 survey + statement shapes + QA obligations); the new `Scaffold/Mathlib/GraphTheory/IrreducibleStationary.lean`; the new `Scaffold/QA/SpectralGraph/IrreducibleStationary_QA.lean`; record updates.

**Next handoff:** spike first in `wip/`; deliver module + QA in this run if the spike holds (the directed-operators Steps 0+1 one-run precedent).

## 2026-08-24T03:53:52Z — Irreducible stationary distributions delivered: the first Perron–Frobenius consumer; the proposal COMPLETE

**Run:** `20260824T024831Z-run-1`  
**Session:** `ses_fce55f957ffe5RyAw4FqyasReu`  
**Status:** completed  
**Milestone:** `proposals/irreducible-stationary-distributions.md` (new this run, Steps 0+1 delivered in one run per the directed-operators precedent — the empty High/Medium queue's recorded handoff and backlog item 8's own note named exactly this PF consumer) — **zero new axioms (count stays 9), QA 1621 → 1715 (`IrreducibleStationary_QA` a new file at 94), the directed axis' first theorem and the `perron_frobenius` axiom's first theorem consumer, conditional on that axiom exactly as specified (`#print axioms` split-verified: the 5 axiom-consuming public theorems and 4 axiom-route QA theorems list `perron_frobenius` + the standard three; the two transfer lemmas and every raw QA lemma only the standard three).**

**Changes:** (1) the proposal document (Step-0 survey: the route runs entirely through the axiom's clauses 5 and 6 — the eigenvalue-identification clause pins the walk's Perron root to `1` at `onesVec` via the shelf's row-stochasticity; the transposed root falls to the bilinear pairing `v ⬝ᵥ (P *ᵥ u) = (Pᵀ *ᵥ v) ⬝ᵥ u` through the pin's `Matrix.dotProduct_mulVec`/`Matrix.mulVec_transpose` — no charpoly, no complex domination; statement shapes recorded before stating; three mandated QA witnesses). (2) The new `Scaffold/Mathlib/GraphTheory/IrreducibleStationary.lean` (namespace `SpectralGraphTheory`; the umbrella importing it): the unconditional transfer lemmas `isIrreducible_transpose` and `walkTransitionMatrix_isIrreducible` (two private `ReflTransGen` support lemmas — a congruence and a flip, both absent from the pin), and the axiom-conditional `exists_walkPerronVector` (the transposed Perron engine, unique-up-to-positive-scale among nonnegative fixed vectors), `exists_stationaryVec_of_irreducible` (existence, full support, normalization), `stationaryVec_smul_of_irreducible`, `existsUnique_stationaryVec_of_irreducible` (the textbook `∃!`), `stationaryVec_pos_of_irreducible`. (3) The new `Scaffold/QA/SpectralGraph/IrreducibleStationary_QA.lean` (+94): the asymmetric directed star with the hand value `(1/2, 1/4, 1/4)` verified completely raw and *identified through* the `∃!` (every stationary distribution of the fixture equals it); the symmetric-cone `K₂` agreement pinning the PF-unique distribution equal to `stationaryVec` through the shelf's detailed-balance chain — two independent API paths to one value; and the reducibility fence on two disjoint `Fin 4` edges refuting the hypothesis-free `∃!` and scale-uniqueness conclusions in proved form with `hnn`/`hdeg` verified intact. (4) Records: the proposal (COMPLETE + delivery record with the pin-technique list), `proposals/README.md` (High row → Delivered; progress paragraph rewritten, the Active table empty again), README (1715; conditional-marked first-consumer sentence; module-table row), the radar (QA axis 1621/42 → 1715/43 held 4.0), the scoreboard (all four verification rows + interpretation bullet; regenerated idempotent 1715/9/0), the SGT index map (new section + 7 declaration rows), backlog item 8 (fourth update), the umbrella `Scaffold.lean`, the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/pfc_spike.lean`, four rounds to green — the surveyed route held verbatim; the fixes became the proposal's trap list: `first | exact` alternatives commit before embedded `by`-blocks are checked, so the irreducibility proofs use arc-`have`s + named `exact`s; the scoreboard's declaration counter is ASCII-only, so unicode QA identifiers were silently uncounted — renamed `π3`/`π4₁`/`π4₂` → `pi3`/`pi4a`/`pi4b`, moving the file's counted declarations 63 → 94; literal-index entry lemmas match `rw`/`simp only` freely but under `fin_cases` only `simp [lemma]` at predicate level — finite sums evaluated through literal component lemmas assembled by `funext` + `fin_cases` + `exact`; `Relation.ReflTransGen.head hstep ih` builds the flipped closure goal-directed where `single`/`trans` combinations cannot; `Finset.mul_sum` at this pin has the factored form on the left; `inv_mul_cancel₀` after `← Finset.mul_sum` needs `exact` for alpha-equivalent binders; `div_mul_cancel₀` takes its value argument first — the recorded Heat trap re-hit); `lake env lean` on the module and QA — zero errors, zero warnings each; `lake build Scaffold.Mathlib.GraphTheory.IrreducibleStationary` ✔ then `lake build Scaffold.QA.SpectralGraph.IrreducibleStationary_QA` ✔; `#print axioms` via `wip/is_axcheck.lean` — the split exactly as specified; **full `lake build` ✔ (2257 targets, +1, "Build completed successfully"; zero warnings in the changed modules — the log's only Scaffold diagnostic the documented pre-existing unused-variable note in untouched `Derived/ProjectorDrift.lean`)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1715/9/0**, idempotent).

**Verification:** every changed module elaborates directly with zero errors/warnings and the new public module is linked into the full default build; the QA module is certified by direct elaboration plus its explicit build target. **The five stationary-distribution theorems are conditional on `perron_frobenius` — Lean-checked deductions, not foundationally proved, and nowhere described as such** (module header, docstrings, README, index map, scoreboard all carry the conditional status; the `#print axioms` audit is the machine check). QA is load-bearing at all three levels the proposal names: the raw route independently proves the stationary predicate satisfiable while the theorem route proves uniqueness, the join pinning the value exactly (a wrong uniqueness clause or a wrong hand value contradicts the other); the symmetric-cone agreement is a two-API cross-validation (axiom route vs. combinatorial deg/vol route — a disagreement falsifies one); and the reducibility fence refutes both hypothesis-free conclusions with the other hypotheses verified, so irreducibility is exercised as a fence, not decoration.

**Remaining risk:** the axiom-conditional theorems inherit the `perron_frobenius` trust cost (Horn & Johnson 8.4.4 at the irreducible-case qualification; the locator still section-level pending physical-copy review — an admission-time fact, unchanged by this delivery). QA breadth: fixtures are `Fin 3`/`Fin 4`; the theorems are size-general. The `hdeg` hypothesis is implied by `hnn + hirr + 2 ≤ card V` (noted in the proposal, not derived — plumbing over interface). The recorded follow-ons are intentionally not started: PageRank (its own document), the symmetric-connected→irreducible bridge, directed mixing (gated on primitivity).

**Next handoff:** the Active priority table is empty again (no High, no Medium). Next run falls through to the center-out SGT policy: the PageRank consumer (own document first), the Chebyshev-filter second consumer of the Krylov layer (own document), or a backlog-gated item.

## 2026-08-24T21:01:06Z — Sweep-cut extraction in delivery: the explicit Fiedler level-set cut

**Run:** `20260824T210106Z-run-1`  
**Session:** `ses_fca77b8daffeqM3rST7EB5sZ1t`  
**Status:** in-progress  
**Milestone:** `proposals/sweep-cut-extraction.md` (new this run) — the swept-level-set extraction, backlog item 4's named strengthening follow-on and the Fiedler module header's own recorded follow-on: replace `cheeger_cut_existence`'s non-constructive conductance-minimizer certificate with an *explicit swept Fiedler level set* (the classical spectral-partitioning sweep step). Three layers: (L1) per-part level extraction at exactly `coarea_core`'s minority hypothesis (min-attainment over the finitely many positive values of `y²` + the covering fact + a non-strict layer-cake integration cloned from `coarea_core`); (L2) the median assembly at any `x ⊥ 1 ≠ 0` giving a closed super/sublevel set of `x` with `conductance² ≤ 2 · rayleigh` — the same constant as `cheeger_sweep` with an explicit witness; (L3) `fiedler_sweep_cut` at `2 · lambda2 / d` on connected `d`-regular graphs. Zero new axioms (count stays 9); load-bearing on the whole Step-1a/1b/1c chain. Plan: spike in `wip/sweep_spike.lean`, then Cheeger.lean + Fiedler.lean sections + QA in `Cheeger_QA`/`Fiedler_QA` (C₄ `cycSweepX`/`cycX2` witnesses, the `onesVec` orthogonality fence, `K₂` Fiedler identification), then the record sweep.

## 2026-08-24T21:42:21Z — Sweep-cut extraction delivered: the explicit Fiedler level-set cut; the proposal COMPLETE

**Run:** `20260824T210106Z-run-1`  
**Session:** `ses_fca77b8daffeqM3rST7EB5sZ1t`  
**Status:** completed  
**Milestone:** `proposals/sweep-cut-extraction.md` (new this run, Steps 0+1 delivered in one run) — the swept-level-set extraction, backlog item 4's named strengthening follow-on and the Fiedler module header's own recorded follow-on — **DELIVERED as pure hard crust, zero new axioms (count stays 9; `#print axioms` via `wip/sweep_axcheck.lean` on all 5 public + 22 QA declarations: `propext, Classical.choice, Quot.sound` only, every one). QA 1999 → 2021 (+22 across `Cheeger_QA`/`Fiedler_QA`). The certified Cheeger cut is now an explicit closed superlevel or sublevel set of the Fiedler vector — the object the spectral-partitioning sweep actually returns — at the same `2 λ₂ / d` constant as Phase B's existential certificate over the non-constructive conductance minimizer.**

**Changes:** (1) `GraphTheory/Cheeger.lean`'s new `SweepExtraction` section (no new imports): `mem_of_posPart_sq`/`mem_of_negPart_sq` (the level-set conversions at `m ± √t`), **`sweep_level_extract`** (per part: for any `y` with minority closed superlevel sets — exactly `coarea_core`'s hypothesis — some level set `S = {i : t ≤ y i²}` at a positive `t` attains `conductance S² ≤ E'(y)/(d·M)`, by attainment over the finitely many positive values of `y²`, the covering fact via `Finset.min'`, and a non-strict layer-cake integration cloned from `coarea_core`'s own proof, closed by Component A), and **`cheeger_sweep_cut`** (the median assembly: any `x ⊥ 1 ≠ 0` has a closed super-/sublevel set with `conductance S² ≤ 2·R_{L_sym}(x)` — the same constant as `cheeger_sweep` with the witness explicit; the product test picks the part uniformly in the degenerate cases). (2) `GraphTheory/Fiedler.lean`'s Phase C: **`fiedler_sweep_cut`** (the `2·lambda2/d` statement on connected `d`-regular graphs through the Phase B Rayleigh bridge); the module header's follow-on sentence updated. (3) QA (+22): the L1 extracted set forced to `{0}` on `C₄` through its level-membership iff (conductance `1` vs bound `4/2`); the L2 family characterized at `cycSweepX` (best swept cut `1`, honestly inside bound `2`, not the global optimum) and at `cycX2` (family = the two dominant halves, swept cut **tying the global optimum `1/2`** — the fixtures marking both ends of the sweep's quality range); the **orthogonality fence refuted in proved form** on the constant vector (empty sweep family — the hypothesis-free conclusion false for every candidate); and on `K₂` the swept cut identified, the family characterized through the Fiedler antisymmetry pins (an equal-entries eigenvector would make the family empty), and the optimality tie `conductance S = cheegerConstant = 1`. (4) Records: the proposal (COMPLETE + delivery record with the pin-technique list and priced follow-ons), `proposals/README.md` (Delivered row; progress paragraph), README (2021; status clause; module-table row), the radar (QA axis 1999/51 → 2021/51 and the axis-4 Phase C sentence, both held), the scoreboard (four verification rows + interpretation bullet; regenerated 2021/9/0 idempotent), `index/map/spectral_graph.md` (3 rows + Phase A–C header), backlog item 4 (Phase C), the Fiedler module header, the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/sweep_spike.lean`, several rounds to green — L1 and L2 each green as units before transfer; the recurring traps recorded in the proposal's pin-technique list: `Finset.exists_min'` absent at the pin (use `min'`/`min'_le`/`min'_mem`); the two-step filtered-image destructuring (`(Finset.mem_filter.1 h).1` then `rw [Finset.mem_image]` at the projection — a one-shot `rw` chain mangles the nested conjunction); `Fintype.sum_prod_type'` at a hypothesis in the ← direction only; `sq_le_sq` in abs form with `abs_le_abs` a two-arg implication (nested `|·|` breaks the parser — write `abs (...)`); `min`-stranded `norm_num` divisions (`2 / min 2 6 = 1` strands `2*2 = 4` — resolve the min by `min_eq_left/right` then `div_self`); literal membership facts cannot serve `simp` at a variable index — use `Finset.eq_univ_iff_forall`/`eq_empty_iff_forall_not_mem`/`subset_singleton_iff` with `fin_cases`; `add_pos`/`add_pos'` both take strict both sides; `hS.elim` on `∅.Nonempty` mis-elaborates — `simp at hS`); `lake env lean` on all four changed modules — zero errors, zero warnings each (the Cheeger module's single line-44 linter note verified pre-existing at HEAD by a stash-roundtrip); explicit `lake build` targets all ✔ (2189/2189, 2194/2194, 2196/2196); `#print axioms` via `wip/sweep_axcheck.lean` on all 27 accessible declarations — the standard three only; **full `lake build` ✔ (2261 targets, "Build completed successfully")**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**2021/9/0**, idempotent).

**Verification:** every changed module elaborates directly with zero errors/warnings and all four are linked into the full default build; the QA modules additionally certified by explicit build targets. The delivery is unconditional hard crust — no axiom is consumed anywhere (`#print axioms`-verified), so there is no conditional-status caveat to carry. QA is load-bearing at every level the proposal names: the per-part witness forces the theorem's *returned set* through its level-membership iff (a wrong family shape or extraction level contradicts the identification); the two C₄ family characterizations exercise the sweep family constraint itself at both quality extremes (optimal and non-optimal, against independently computed conductances); the fence refutes the hypothesis-free conclusion with the hypothesis exactly isolated (orthogonality); and the K₂ family characterization shows the constraint is non-vacuous in the strongest sense — on an eigenvector with equal entries the family would be empty and no theorem of this shape could hold.

**Remaining risk:** the statements are `d`-regular (the Rayleigh/conductance conversion is degree-based); the irregular shape is a priced follow-on gated on a consumer. The sweep is ∃-form (the theorem exhibits a level set, not a procedure enumerating them); the computable-sweep packaging is gated the same way. QA fixtures are `Fin 4`/`Fin 2`; the theorems are size- and weight-general.

**Next handoff:** the Active priority table is empty again (no High, no Medium — every remaining row a Low blocked on a human/technical decision). Next run falls through to the center-out SGT policy: the standing gated candidates (primitivity-shaped admission for directed mixing; the honestly-blocked pairwise set shape; a named consumer pricing the wide-band minimax filter designs), the sweep-cut proposal's priced follow-ons, or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-24T22:48:13Z — Primitive power convergence in delivery: the directed mixing gate opened by admission

**Run:** `20260824T224813Z-run-1`  
**Session:** `ses_fca0f47e8ffeHHShe9rLRQ8BoK`  
**Status:** in-progress  
**Milestone:** `proposals/primitive-power-convergence.md` (new this run) — the primitivity-shaped admission the standing handoff names as the directed-mixing gate, plus its first consumer: powers of a primitive row-stochastic matrix converge to `(π ⬝ᵥ x) • 1` at the stationary distribution (Horn & Johnson §8.5, one new axiom, count 9 → 10), and the Google matrix's teleportation floor makes it primitive on every nonneg input at `0 ≤ α < 1` — so the PageRank power iteration converges (the loop with the delivered existence/`∃!` layer closed: the distribution is computable). Corollaries: entrywise column convergence `Pᵗ i j → π j` and the walk-evolution form `ν ᵥ* Gᵗ → π`. QA headlined by the proved periodicity refutation (the directed 2-cycle: irreducible, stochastic, powers provably oscillate — the fence documenting that primitivity is load-bearing and that the `perron_frobenius` no-dominance honesty was correct). Route surveyed pre-edit: the axiom at the given-π form (no `∃` — consumers hold the delivered unique vector), `Matrix.IsPrimitive` as H&J's positive-power definition, `isIrreducible_of_isPrimitive` by entry-of-power path decomposition, the row-sum carrier matching `walkTransitionMatrix_eq_of_row_sum_one`. Spike first in `wip/ppc_spike.lean`; prior runs' uncommitted deliveries preserved untouched.

## 2026-08-24T23:09:16Z — Primitive power convergence delivered: the directed mixing gate opened; the PageRank power iteration; the proposal COMPLETE

**Run:** `20260824T224813Z-run-1`  
**Session:** `ses_fca0f47e8ffeHHShe9rLRQ8BoK`  
**Status:** completed  
**Milestone:** `proposals/primitive-power-convergence.md` (new this run, Steps 0+1 delivered in one run) — the primitivity-shaped admission the standing handoff named as the directed-mixing gate, plus its first consumer — **DELIVERED: one new axiom (count 9 → 10, the first *convergence* axiom — Horn & Johnson §8.5 at the row-stochastic specialization, given-π form, no rate; `#print axioms` via `wip/ppc_axcheck.lean` on all 13 public + 22 QA declarations: the unconditional ones the standard three only, the six convergence theorems `primitive_power_tendsto` + the standard three, and **no `perron_frobenius` anywhere** — the two directed-axis axioms' trust costs machine-verified independent). QA 2021 → 2051 (`DirectedMixing_QA` a new file at 30).** The directed axis' first convergence theorem, and the loop with the delivered PageRank layer closed: the distribution is unique (conditional on `perron_frobenius`) *and computable* — `pageRank_powerIteration` is the classical algorithm as a theorem.

**Changes:** (1) the new `Scaffold/Mathlib/LinearAlgebra/PrimitiveConvergence.lean`: `Matrix.IsPrimitive` (H&J's positive-power definition verbatim), the admitted `primitive_power_tendsto` (`(P ^ t) *ᵥ x → (π ⬝ᵥ x) • 1` at any nonnegative mass-one stationary `π ᵥ* P = π`; row-stochastic carrier matching the shelf's bridge convention; statement differences and honest scope — no rate, Π topology, `hrow`'s no-fence-possible status — in the module documentation and the source index), and the unconditional transfer layer: `isPrimitive_of_pos`, `reachable_of_pow_pos` + `isIrreducible_of_isPrimitive` (an entry of a positive power is a sum over walks — load-bearing on `Matrix.IsIrreducible`'s exact combinatorial shape), `pow_mulVec_one`, and the generic conditional corollaries `primitive_entrywise_tendsto` / `primitive_vecMul_tendsto` (the private finite-sum tendsto induction, the pin having no tendsto-sum lemma). (2) The new `Scaffold/Mathlib/GraphTheory/DirectedMixing.lean` (minimal imports PageRank + PrimitiveConvergence; the umbrella importing both new modules): `googleMatrix_isPrimitive` (the teleportation floor is primitivity — *aperiodicity* derived, strictly stronger than the delivered irreducibility), **`pageRank_powerIteration`**, `pageRank_entrywise_tendsto`, `pageRank_walk_tendsto`, `googleMatrix_pow_mulVec_onesVec`. (3) `DirectedMixing_QA.lean` (+30 on the reused `PageRank_QA` fixtures): Section A the positive witness (primitivity theorem route + raw floor spot-check; the limit coefficient pinned raw to the uniform `1/4`; the second iterate computed completely raw at `3/16 < 1/4`; the entrywise and non-uniform-start walk forms), Section B the **periodicity refutation** (`P₂ = !![0,1;1,0]`: nonnegative, row-stochastic, *and irreducible* with the uniform stationary verified raw; `P2_not_primitive` — every power is `1` or `P₂`; `P2_no_limit` — the even/odd subsequences are constantly `e₀`/`e₁` through `Tendsto.comp`, so no limit exists for any candidate; `P2_fence_isolation` collecting every other axiom hypothesis as verified — exactly `hprim` isolated, the convergence-form mirror of `strict_dominance_refuted_QA`), Section C the coherence join (the unconditional `onesVec`-fixing against the axiom's limit *derives* `π ⬝ᵥ 1 = 1`, cross-checked against the raw sum). One drafted QA declaration removed as inert (an equality-of-proofs join — rfl by proof irrelevance; the strategy's load-bearing principle's exact warning case, documented in-file). (4) Records: the proposal (status header COMPLETE + the delivery record with the pin-technique list and priced follow-ons), `proposals/README.md` (the Delivered row; the progress paragraph — the natural-candidates note updated: the convergence layer is delivered, what remains is rates), README (2051; the status paragraph's convergence-layer clause; two module-table rows), the coverage map (the PF row's primitive-limit sentence), the radar (QA axis synced 2021/51 → 2051/52, held 4.0), the scoreboard (four verification rows + the interpretation bullet; regenerated 2051/10/0 idempotent), `index/sources/horn_johnson_matrix_analysis.md` (§8.5 row + notes), `index/map/linear_algebra.md` (status + 8 declaration rows + consumers de-staled), `index/map/spectral_graph.md` (the DirectedMixing section), backlog item 8 (the sixth update), the umbrella `Scaffold.lean`, the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/ppc_spike.lean`, several rounds to green — the recurring fixes recorded in the proposal's pin-technique list: `tendsto_nhds_unique`'s argument order; `tendsto_const` being `tendsto_const_nhds` at this pin; `Finset.sum_pos'`'s wrong shape here (the positive-term extraction by `by_contra` + `Finset.sum_nonneg` at the negated sum); both `mul_nonpos` mirrors; `Matrix.mulVec_mulVec`'s right-associativity; `Finset.induction_on`'s `@insert m s hm ih` arity; `Finset.sum_insert`'s shadowed-binder partial rewrites; `Matrix.one_apply` in `Data/Matrix/Diagonal.lean`; ℝ-literal fixtures as `noncomputable def`s; `open scoped Topology` for `𝓝`; `Fin.sum_univ_four` not `Finset`; `Nat.even_or_odd`'s `m + m` form); `lake env lean` on both public modules and the QA file — zero errors, zero warnings each; `lake build` on all three explicit targets ✔ (1736/1736, 2195/2195, 2201/2201); `#print axioms` via `wip/ppc_axcheck.lean` — the split exactly as specified, no `perron_frobenius` anywhere; **full `lake build` ✔ (2263 targets, +2, "Build completed successfully"; zero warnings in the changed modules)**; `lint_axioms` (**10** — the new axiom mapped in the indices, no warnings), `check_citations` — pass; `check_markdown_links` — pass (re-run after all record edits); scoreboard regenerated idempotent (**2051/10/0**); `git status` — only this run's intended files (three new Lean modules, the proposal, and the twelve record files).

**Verification:** every changed module elaborates directly with zero errors/warnings and all three build as explicit targets and are linked into the full default build. **The six convergence theorems are conditional on `primitive_power_tendsto` — Lean-checked deductions, never foundationally proved, and nowhere described as such** (both module headers, the docstrings, README, the index maps, and the scoreboard carry the conditional status; the `#print axioms` audit is the machine check, and it additionally verifies the axioms' trust-cost independence — zero `perron_frobenius` contact). QA is load-bearing at all three mandated levels: the positive witness joins the axiom-route limit with the raw-verified uniform stationary value and exhibits the sequence in motion toward it (a wrong limit shape contradicts the pinned iterate); the fence refutes the hypothesis-free conclusion *in proved form* on a fixture satisfying every other hypothesis, with primitivity separately proved to fail — the hypothesis is exercised, not decorated; and the coherence join *derives* a checkable mass fact from the axiom against an independent raw route.

**Remaining risk:** the new axiom's trust cost is the Horn–Johnson §8.5 locator at section level pending physical-copy review (an admission-time fact, unchanged by QA; the LPW Theorem 4.9 cross-reference likewise). The convergence statements carry no rate — the geometric-rate layer needs the complex spectral theory of non-symmetric matrices and is recorded as a separate future admission gated on a named consumer. QA fixtures are `Fin 4`/`Fin 2`; the theorems are size- and weight-general. The entrywise/Π-topology form is the only limit shape claimed (no operator-norm statement).

**Next handoff:** the Active priority table is empty again (no High, no Medium — every remaining row a Low blocked on a human or technical decision). Next run falls through to the center-out SGT policy: the directed-axis *rate* layer (gated on a separate admission + a named consumer), the magnetic-Laplacian slice, a named consumer pricing the wide-band minimax filter designs, the sweep-cut priced follow-ons, or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-25T03:24:00Z — Build-completeness verification in delivery: the reconciliation script

**Run:** `20260825T032035Z-run-1`  
**Session:** `ses_fc911fcf1ffeM2oSlu263hogtl`  
**Status:** in-progress  
**Milestone:** `proposals/verify-build-completeness.md` (found untracked and unindexed this run, priority **High** in its own header — indexed into the Active priority table at this boundary): `scripts/check_build_completeness.py`, a filesystem-level reconciliation making "lake build completed successfully" falsifiable — every `Scaffold/**/*.lean` source must have a fresh (not mtime-stale, not missing) `.olean` artifact or the check fails nonzero with the offending files listed. Responds to the documented incident (an interrupted run's three-error `Magnetic_QA.lean` passed a full `lake build` silently; only the explicit per-file target failed). Leverage: priority-order item 1, honest build reachability — the most-repeated verification step in every delivery entry currently rests on an assumption the incident proved false. Deliverable is the script + wiring into the documented verification ladder (AGENTS.md, `opencode-pursue`'s `verify_for_commit`, `scripts/README.md`, architecture §10, this log's format block) + the proposal's retirement record. No Lean, no axioms, no QA declarations.

**Next:** implement, regression-test against reconstructed missing/stale artifact states (temp scratch, not the real tree), run the full ladder, update records.

## 2026-08-25T03:45:00Z — Build-completeness verification delivered: the reconciliation fence, 8 live findings remediated; the proposal COMPLETE

**Run:** `20260825T032035Z-run-1`  
**Session:** `ses_fc911fcf1ffeM2oSlu263hogtl`  
**Status:** completed  
**Milestone:** `proposals/verify-build-completeness.md` (found untracked and unindexed at run start, priority **High** in its own header — indexed into the Active priority table at that boundary and pursued per priority item 0; priority-order item 1, honest build reachability) — **DELIVERED: `scripts/check_build_completeness.py` wired into all five documented verification-ladder locations; no Lean, no axioms, no QA declarations. And the fence caught real defects on its first run against the live tree: 8 findings, every one remediated by real elaboration — the tree now reconciles 103/103 fresh, 0 stale, 0 missing, exit 0, immediately after a full `lake build`.**

**Changes:** (1) The new `scripts/check_build_completeness.py`: enumerates the root umbrella `Scaffold.lean` plus every `Scaffold/**/*.lean` (ignored scratch excluded), requires a fresh `.lake/build/lib/<module>.olean` per source, fails nonzero listing every MISSING (never elaborated by any invocation) and STALE (artifact mtime strictly older than source, nanosecond compare) file with a summary line; exits 0/1/2; `--root` for arbitrary trees; no Lean invocation, no lakefile parsing, no Lake-internals re-implementation. (2) **Live findings, run 1:** MISSING — `ProjectionGap_QA.lean` (586 lines) and `Expander_QA.lean` (1,181 lines), both artifact-less and both elaborating clean once built, plus `Mathlib/Core.lean` (an unimported 2-line legacy re-export shim from the initial commit); STALE — `Dynamics_QA.lean` (**a genuine never-rebuilt content edit**: source 08-20, artifact 08-18 — the incident class caught live, not reconstructed), `Mixing_QA.lean`, `SpectralCertificates_QA.lean` (same class, rebuilt), and `Subgaussian.lean`/`Entropy_QA.lean` (benign byte-identical roundtrips, remediated by the documented artifact-removal route forcing re-elaboration). (3) Ladder wiring: `AGENTS.md` § Verification, `scripts/opencode-pursue`'s `verify_for_commit` (immediately after `lake build`, so `--commit` fails closed), `scripts/README.md`, `docs/2_ARCHITECTURE.md` §10, and this log's format block (entries claiming a verified full build must record the check passing right after the build they cite). (4) Records: the proposal (COMPLETE + full delivery record), `proposals/README.md` (the High row added at the boundary then retired to Delivered; the progress paragraph), the execution plan, this log.

**Decisive commands and outcomes:** two calibration experiments on the pinned toolchain — `lake build Scaffold.QA.SpectralGraph.Dynamics_QA` on a stale-mtime source **rewrote the olean** (content-changed ⇒ rebuild), while `touch` + `lake build` on an up-to-date source left the olean untouched (Lake's up-to-date check is content-hash based) — so STALE necessarily fails closed with the always-terminating remediation recorded in the docstring (direct rebuild; else remove the gitignored derived artifact and rebuild once); the trace files were inspected and hold only a Lake-internal UInt64 `depHash`, confirming a filesystem-only check cannot and should not re-derive content currency. Regression suite (acceptance bar) in a synthetic `--root` mini-tree: the incident reconstruction — a three-error `Magnetic_QA.lean` with no artifact — flagged MISSING at exit 1; explicit-mtime STALE flagged with both timestamps; the umbrella and fresh module counted; `wip/Scratch.lean` excluded (5 counted, not 6); usage/bad-root exit 2; the healed tree exits 0. Full ladder on the real tree in the mandated order: `lake build` ✔ ("Build completed successfully") → `check_build_completeness.py` **103/103 fresh, 0 stale, 0 missing, exit 0** → `lint_axioms` (10 axioms, no issues), `check_citations`, `check_markdown_links` pass, scoreboard regeneration idempotent (md5-stable).

**Verification:** the seven remediated modules were elaborated (`lake env lean`, all exit 0 — one pre-existing unused-variable linter note in `Subgaussian.lean`) before being rebuilt, so the green state is by real elaboration, not timestamp cosmetics. The regression suite exercises both failure tiers, the exclusion rule, the umbrella coverage, and all three exit codes. The ladder wiring is itself verified by this entry: it records the completeness check passing immediately after the full `lake build` it cites, per the new format-block rule.

**Remaining risk:** the STALE tier is deliberately conservative — byte-identical roundtrips (git stash/checkout, editor saves) fail until the documented force-re-elaboration runs; rare, and this run itself induced and closed one live (its own `touch` experiment flagged `Mixing_QA`, remediated the same way). mtime comparison cannot see content-hash currency (Lake's ground truth); same-tick edit-build sequences are theoretically maskable, unlikely at nanosecond resolution. `Mathlib/Core.lean` is now built but still imported by nothing — an orphan shim left in place (deletion is a separate operator decision). No pre-commit hook added, per the proposal's explicit choice.

**Next handoff:** the Active priority table is empty again (no High, no Medium — every remaining row a Low blocked on a human or technical decision). Next run falls through to the center-out SGT policy: the directed-axis *rate* layer (gated on a separate admission + a named consumer), the magnetic *spectral* layer (eigenvalues of `M`, magnetic Cheeger — gated on a consumer naming a bound), a named consumer pricing the wide-band minimax filter designs, the sweep-cut priced follow-ons, or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md` — recording the completeness check after its full build.

## 2026-08-25T04:52:22Z — Irregular Cheeger (easy direction) in delivery: general-kernel variational + the degree-stretched cut test vector

**Run:** `20260825T045222Z-run-1`  
**Session:** `ses_fc8c3072dffeOftJ4F8FHrRfPg`  
**Status:** in-progress  
**Milestone:** `proposals/irregular-cheeger-variational-transfer.md` (found committed-but-unindexed — the same gap class this table's history documents twice; indexed into the Active priority table this run and pursued per priority item 0) — Step 0 (the mandatory survey) + Step 1 (the easy/upper-bound direction on arbitrary positive-degree graphs, the hard direction priced and deferred exactly as the proposal authorizes). Leverage: `GraphTheory.VariationalTransfer`'s first theorem consumer (its own docstring names this exact follow-on; zero theorem consumers to date) and the removal of the standing "regular graphs only" caveat from the Cheeger upper bound. Step-0 findings recorded in the execution plan: definitions already volume-general; the irregular test vector is the degree-stretched cut indicator `√D · cutTestVector A S` (degree-weighted orthogonality holds *without* regularity by the volume identity `vol S · vol Sᶜ − vol Sᶜ · vol S = 0`); one new engine lemma (the general-kernel `secondEval_le_rayleigh`) because the normalized Laplacian's kernel vector is `√D · onesVec`, not `onesVec`. Zero new axioms planned. Spike first in `wip/icv_spike.lean`; the previous runs' uncommitted deliveries preserved untouched.

## 2026-08-25T05:46:12Z — Irregular Cheeger easy direction delivered: the volume-weighted upper bound, VariationalTransfer's first theorem consumers; the proposal COMPLETE (easy half)

**Run:** `20260825T045222Z-run-1`  
**Session:** `ses_fc8c3072dffeOftJ4F8FHrRfPg`  
**Status:** completed  
**Milestone:** `proposals/irregular-cheeger-variational-transfer.md` — **Steps 0+1 delivered in one run, pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/icv_axcheck.lean` on all 36 new declarations — 10 public + 26 QA headline: exactly `propext, Classical.choice, Quot.sound`, every one). QA 2067 → 2152 (`IrregularCheeger_QA` a new file at 85 by the generator metric). The standing "regular graphs only" caveat on the Cheeger upper bound is removed, and `GraphTheory.VariationalTransfer` — built for exactly this consumer, zero theorem consumers until today — now carries three.**

**Changes:** (1) `GraphTheory/Spectral.lean`: `eigvecOf_ortho_of_mulVec_eq_zero` (the general-`w` parent of the onesVec orthogonality engine), `secondEval_le_rayleigh_of_ker` (the general-kernel Rayleigh domination — `secondEval ≤ R(x)` for every nonzero `x ⊥ w` at a nonzero kernel vector `w` of a PSD symmetric matrix), `vol_pos_of_pos_deg`. (2) `GraphTheory/Normalized.lean`: `normalizedLaplacian_mul_degreeSqrt` (the left-multiplied congruence) and `normalizedLaplacian_mulVec_degreeSqrt_onesVec` — **the kernel vector is `√D · onesVec`, not `onesVec`**, the structural fact that separates the irregular variational picture. (3) `GraphTheory/VariationalTransfer.lean` (no new modules, no umbrella change): the irregular section — the volume identity `dotProduct_degreeSqrt_mulVec_cutTestVector` (hypothesis-free: `vol S · vol Sᶜ − vol Sᶜ · vol S = 0`, the orthogonality the regular proof needed `vol_eq_of_regular` for), the weighted norm, the nonzero lemma, the Rayleigh quotient (the *same* value as the regular family), and the headline `cheeger_upper_bound_normalized`: `secondEval (normalizedLaplacian A) ≤ 2 * cheegerConstant A` for symmetric nonnegative positive-degree `A` with `2 ≤ card V` — no regularity, no connectivity. (4) The new `Scaffold/QA/SpectralGraph/IrregularCheeger_QA.lean` (+85). (5) Records: the proposal (status header + Step-0 record with the four deliverables + delivery record with the pin-technique list), `proposals/README.md` (the High row retired to Delivered; the progress paragraph), README (2152; the status-paragraph clause; the module-table row), the radar (QA axis 2152/54 held 4.0; axis-4's irregular-easy clause, held 4.5 — the hard direction keeps half the statement regular-only), the scoreboard (two verification rows; regenerated idempotent 2152/10/0), `index/map/spectral_graph.md` (the VT section's second table + the Spectral/Normalized engine rows), backlog item 3, the execution plan, this log.

**Decisive commands and outcomes:** the Step-0 survey read directly from source — `vol`/`boundary`/`conductance`/`cheegerConstant` already volume-general, `cutTestVector`'s energy identity already regularity-free, so only the inequality was new; the decisive finding is that the degree-weighted sum of the *existing* cut indicator vanishes without regularity, making the degree-stretched `√D *ᵥ cutTestVector A S` the correct irregular test object and the general-kernel engine lemma the only genuinely new mathematics on the route. Spike (`wip/icv_spike.lean`) — the whole route green in three elaboration rounds before any module was touched. The QA's recurring traps (recorded in the proposal's pin-technique list): `simp only` with a def-unfold in the same list as a lemma stated over that def — the def wins the rewrite race (durable fix: staged simp onlys, standalone value-pin lemmas, a `hdeglit` copy at the unfolded literal); `obtain` clears its source hypothesis; `Matrix.mulVec_mulVec` stated nested-left at this pin; `rw [secondEval]` fails (use the rfl-equation have); numeric closers flip between rw-closes and needing `norm_num` (`try norm_num` after long chains); `Pi.single` needs its index type ascribed. `lake env lean` — zero errors/warnings on all three public modules and the QA file (QA warning-clean); `lake build` explicit targets ✔ (Spectral/Normalized/VariationalTransfer; IrregularCheeger_QA 2193/2193); `#print axioms` — the standard three only, all 36; **full `lake build` ✔ (2264 targets, "Build completed successfully") immediately followed by `check_build_completeness.py` — 104/104 fresh, 0 stale, 0 missing, exit 0** (the mandatory post-build fence); `lint_axioms` (10), `check_citations`, `check_markdown_links` pass; scoreboard regenerated idempotent (md5-stable); `git status` — only this milestone's intended files plus the prior runs' preserved uncommitted deliveries.

**Verification:** all changed modules elaborate directly with zero errors/warnings and sit in the default build; the QA module is additionally certified by its explicit build target. The delivery is unconditional hard crust — no axiom consumed anywhere (`#print axioms`-verified). QA is load-bearing at every mandated level: the conductance side computed by hand on genuinely irregular input (all six cuts of `P₃`, degrees 1, 2, 1); the test-vector layer pinned entrywise with the energy `16` reached by three independent routes (raw combinatorial arithmetic, the congruence engine, the delivered cut energy identity — a misstated congruence or wrong stretched vector breaks exactly one); the spectral side bounded *independently of the theorem* through the eigenpair witness `![1, 0, -1]` (`λ₂ ≤ 1` vs the theorem's `≤ 2` — non-circular coherence); the discrimination witness (`2 − √2 ≠ 0`) proving the onesVec engine cannot consume this test object, so the new lemma is genuinely more expressive; the `K₂` tight regular recovery; and two proved-form fences isolating exactly `hpsd` (engine) and `hd` (headline) with every other hypothesis verified on the fixture.

**Remaining risk:** route provenance for the classical statement is Chung Ch. 2 (a proof citation, not an admission — section-level locator, the standing verify-against-physical-copy caveat; `check_citations` passes). The irregular *hard* direction (`φ²/2 ≤ λ₂` in the volume-weighted measure) is deliberately not delivered — priced as its own multi-step volume-weighted coarea/median program per the proposal's own authorization; the radar's axis 4 holds 4.5 for exactly that reason. QA fixtures are `Fin 2`/`Fin 3`; the theorems are size- and weight-general.

**Next handoff:** the Active priority table is empty again (no High, no Medium). Candidates on record: the irregular-Cheeger hard direction (the delivery's own priced follow-on), **triaging the untracked `proposals/expander-independence-number-bound.md`** (header Medium-High, "a real consumer for the Expander Mixing Lemma" — appeared in the worktree during this run, not present at run start, left untouched and unindexed by this run since it is not this run's artifact; the next run should read it and apply the unindexed-proposal precedent), the standing gated candidates (directed-axis rate; magnetic spectral; a consumer pricing the wide-band minimax filter designs), or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-25T13:00:43Z — Hermitian functional-calculus bridge in delivery: triage of the untracked proposals, the Step-0 verdict, the thin wrapper

**Run:** `20260825T125600Z-run-1`  
**Session:** `ses_fc702c53affe3TJ8Ik4tkxE7GY`  
**Status:** in-progress  
**Milestone:** `proposals/hermitian-functional-calculus-bridge.md` — the previous run's standing handoff directed triage of the three untracked Hermitian-calculus proposals; triaged: the two consumer documents are gated stubs (blocked on this bridge's Steps 1–3), the bridge itself is Medium-priority with its own gating condition (an Active table empty of higher rows) now satisfied — indexed into the Active table this run and pursued. Deliverable: Steps 1–3 — a thin Scaffold wrapper `spectralCalc M hM f := (isHermitian_of_isSymm hM).cfc f` exposing Mathlib's proved continuous functional calculus at the shelf's real-symmetric convention, the eigenvector action, the equality with the shelf's own filter-sum expansion (`dotProduct_eigvecOf_filter`'s operator), the `spectralProjector` recovery at indicator functions (the proposal's "one existing definition recovered as a calculus instance" clause), and `spectralCalc_id`; plus the three mandated QA sections. Pure hard crust, zero new axioms planned (the proposal's acceptance bar explicitly forbids describing this as addressing any of the ten axioms, replacing Krylov/Chebyshev, or as a universal bridge). Step 0 verdict recorded in the execution plan before any shelf Lean is written (the proposal's hard acceptance-bar order): one `cfc` for both real and complex via `RCLike`; no continuity hypothesis on the bare-function wrapper; eigenbasis reconciliation free (`eigvecOf` IS `eigenvectorBasis`). Spike first in `wip/hfc_spike.lean`; the previous runs' uncommitted deliveries preserved untouched.

## 2026-08-25T13:50:02Z — Hermitian functional-calculus bridge delivered: the Scaffold–Mathlib consolidation layer; the proposal COMPLETE

**Run:** `20260825T125600Z-run-1`  
**Session:** `ses_fc702c53affe3TJ8Ik4tkxE7GY`  
**Status:** completed  
**Milestone:** `proposals/hermitian-functional-calculus-bridge.md` (one of the three untracked Hermitian-calculus proposals the previous run's standing handoff directed this run to triage; triaged: the two consumer documents are gated stubs blocked on this bridge's Steps 1–3 and stayed out of scope, the bridge itself Medium-priority with its own gating condition — an Active table empty of higher rows — then satisfied, indexed and pursued) — **Steps 0+1 delivered in one run, pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/hfc_axcheck.lean` on all 25 audited declarations — 7 public + 18 QA: exactly `propext, Classical.choice, Quot.sound`, every one; zero contact with any of the ten admitted axioms, machine-checked, as the proposal's acceptance bar demands). QA 2173 → 2189 (`FunctionalCalculus_QA` a new file at 16 by the generator metric). The SGT center's spectral machinery now has one shared calculus: the four hand-built "function of a symmetric matrix" notions (`spectralProjector`/`bandProjector`, the PolyFilter layer, `heatKernel`, `tikhonovShrinkage`) are all calculus instances or filter-sum operators the bridge proved equal to `cfc`.**

**Changes:** (1) **Step 0 verdict recorded before any shelf Lean** (the proposal's hard acceptance-bar order): one `RCLike`-generic `cfc` covers real and complex (no API split; one thin real wrapper, complex consumers use `cfc` at `𝕜 = ℂ` directly); no continuity hypothesis on the bare-function form (finite spectrum — discontinuous-at-a-point filters cannot collide); eigenbasis reconciliation free (`eigvecOf` IS `eigenvectorBasis` coerced). One provenance repair: the proposal placed `dotProduct_eigvecOf_filter` in `Spectral.lean`; it lives in `Tikhonov.lean:194`. (2) The new `Scaffold/Mathlib/GraphTheory/FunctionalCalculus.lean` (namespace `SpectralGraphTheory`; imports Spectral + Tikhonov + Mathlib's `HermitianFunctionalCalculus`; the umbrella importing it): `spectralCalc` (the thin wrapper), `spectralCalc_apply` (the entry form — the falsifiability anchor, proved from the `cfc` triple-product definition by controlled rewrites), `spectralCalc_mulVec_apply` (the action form = the shelf's filter-sum vector), `spectralCalc_mulVec_eigvecOf` (the hypothesis-free eigenvector action), `dotProduct_eigvecOf_spectralCalc_mulVec` (the coefficient bridge consuming the Tikhonov workhorse **verbatim** — Step 3's literal statement), `spectralCalc_indicator_eq_spectralProjector` (the recovery of the hand-built projector as the calculus at indicator functions — the "real rather than decorative" clause), `spectralCalc_id`. The module docstring carries the proposal's three mandated NOT-clauses. (3) The new `Scaffold/QA/SpectralGraph/FunctionalCalculus_QA.lean` (+16): all three mandated obligations — two API paths to one value on the reused `diag13` fixture (arbitrary-`f` entry-form computation from the Band_QA pins, sign-free summands; the projector route through the recovery theorem; both pinned to `!![1,0;0,0]`; the f-dependence fence `3 ≠ 9` refuting any `f`-independent implementation), the non-basis eigenvector action (generic `v_i + v_j` linearity + the `![1,1]` action by two independent routes: pinned matrix raw vs the expansion theorem with sign-cancelling coefficients), the repeated-eigenvalue boundary on `2 • 1` (two genuinely independent routes: entry form + completeness with no basis choice anywhere; raw unitary conjugation with no completeness anywhere, the eigenvalue listing derived from the spectral theorem's conjugation identity) — plus the complex-half elaboration witness `fcM2c_cfc_id` (`cfc` at `𝕜 = ℂ` on `[[0,i],[-i,0]]` through the generic `cfc_id'`), discharging the gated magnetic consumer's Step-0 precondition with an artifact. (4) Records: the proposal (COMPLETE header + Step-0 verdict + delivery record with the pin-technique list and priced follow-ons), `proposals/README.md` (the Medium row retired to Delivered; the progress paragraph), README (2189; the status-paragraph bridge clause; the module-table row), the radar (QA axis synced 2173/54 → 2189/55, held 4.0), the scoreboard (the verification row; regenerated 2189/10/0 idempotent), `index/map/spectral_graph.md` (the FunctionalCalculus section + 7 declaration rows), the coverage map (the cross-reference sentence — the correction cross-referenced, not re-litigated, per the acceptance bar), the umbrella `Scaffold.lean`, the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/hfc_spike.lean`, several rounds to green before any module touched; the complex witness spiked separately in `wip/hfc_cx.lean` — `cfc_id' ℝ` at `𝕜 = ℂ` with the `IsHermitian`-to-`IsSelfAdjoint` defeq); the recurring traps recorded in the proposal's pin-technique list — the sharpest being the **two coe forms of `eigenvectorBasis` application** (Mathlib's `eigenvectorUnitary_apply` produces the `WithLp.equiv` form, the shelf's `eigvecOf` type-ascription the bare form — defeq but invisible to `ring`'s atom abstraction; the durable fix is per-atom `have h : LHS = RHS := rfl` bridges, never `simp only [eigvecOf]` + `ring`), `Matrix.mul_apply` must not be simp-cascaded with `mul_diagonal` (double sum), `linear_combination`'s failure printout shows the *residual* after subtracting the claim, the `show … from rfl` unification trap, `fin_cases`-on-ext-binder beta-redexes closed by per-branch definitional `show`, and `Matrix.diagonal_apply_ne _ h`'s explicit `d` slot; `lake env lean` — zero errors/warnings on the module and the QA file; `lake build` explicit targets ✔ (2301/2301, 2304/2304); `#print axioms` via `wip/hfc_axcheck.lean` — the standard three only, all 25; **full `lake build` ✔ (2385 targets, "Build completed successfully"; the +~120-target jump over the previous 2264 is the previously-unbuilt Mathlib CFC closure pulled by the new import, not new Scaffold surface) immediately followed by `check_build_completeness.py` — 106/106 fresh, 0 stale, 0 missing, exit 0** (the mandatory post-build fence); `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass (re-run after the full record sweep); scoreboard regenerated idempotent (md5-stable); `git status` — only this milestone's intended files plus the prior runs' preserved uncommitted deliveries.

**Verification:** every changed module elaborates directly with zero errors/warnings and both sit in the default build; the QA module is additionally certified by its explicit build target. The delivery is unconditional hard crust — no axiom consumed anywhere (`#print axioms`-verified), so there is no conditional-status caveat to carry. QA is load-bearing at every mandated level: the two-path discipline means a wrong calculus specialization or a mismatched eigenbasis convention breaks one path's pinned value against the other's (the entry-form route and the projector route are genuinely independent computations of `!![1,0;0,0]`); the f-dependence fence refutes the degenerate-implementation failure mode in proved form; the repeated-eigenvalue fixture's two routes share *no* proof ingredient (completeness vs unitarity), so a basis-dependence bug breaks exactly one; and the complex witness elaborates the `RCLike`-genericity the Step-0 verdict claims, on genuinely complex input.

**Remaining risk:** the bridge is a consolidation layer, not new SGT theorem content — its value is realized only through the consumers (the two now-unblocked gated stubs). The `RCLike.ofReal = id` over ℝ is used as `rfl` (defeq, kernel-checked, not a simp-lemma rewrite) — safe but worth knowing if the Mathlib pin changes. The QA fixtures are `Fin 2`; the public theorems are size- and weight-general. The Mathlib CFC closure added ~120 build targets (import cost already paid; future consumers add nothing).

**Next handoff:** the Active priority table is empty again (no High, no Medium — every remaining row a Low blocked on a human/technical decision). Next run falls through to the center-out SGT policy: the two now-unblocked bridge consumer stubs (`hermitian-calculus-consumer-tikhonov-heat.md` — Tikhonov *or* Heat as a calculus instance, the smaller reconciliation gap Tikhonov's per the delivery's priced follow-on; `hermitian-calculus-consumer-magnetic.md` — the magnetic heat propagator, its complex-half precondition discharged by this delivery's QA witness), the irregular-Cheeger *hard* direction, the standing gated candidates (directed-axis rate; magnetic spectral; a consumer pricing the wide-band minimax filter designs), or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-26T04:57:52Z — The volume-weighted sweep-cut extraction (in delivery)

**Run:** `20260826T045752Z-run-1`  
**Session:** (recorded at terminal entry)  
**Status:** in-progress  
**Milestone:** the irregular-Cheeger family's top remaining priced follow-on — the regular family's sweep-cut extraction ported to the volume-weighted world, selected per the empty High/Medium Active table by the center-out policy. Delivering `sweep_level_extract_vol` (per-part, `Cheeger.lean`: the attained-minimal-`boundary/vol`-ratio route over the positive values of `y²`, the layer-cake at volume strength, `conductance A S² ≤ E'(y)/∑ deg y²` with the witness level set explicit) and `cheeger_sweep_cut_normalized` (median assembly, `VariationalTransfer.lean`: every nonzero degree-weighted zero-sum `f` has a swept nonempty proper cut at `conductance² ≤ 2·R_{L_sym}(√D f)`, through the volume median, the delivered fused contraction, and the weighted norm split). Load-bearing on the whole delivered `VolumeHardDirection` layer plus the regular family's attainment template; zero new axioms planned; QA extension of `IrregularCheeger_QA.lean` with the forced extraction witness, the pair's shared cut test vector instances, the K₂ regular recovery, and hypothesis fences. Spike first in `wip/`; prior runs' uncommitted deliveries preserved untouched.

## 2026-08-26T05:33:53Z — The volume-weighted sweep-cut extraction delivered: the irregular pair's explicit witness level set (completed)

**Run:** `20260826T045752Z-run-1`  
**Session:** `ses_fc394225bffe195OGNEi37FwTJ`  
**Status:** completed  
**Milestone:** the irregular-Cheeger family's next priced follow-on — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/vsc_axcheck.lean` on all 13 audited declarations — 2 public + 11 QA: exactly `propext, Classical.choice, Quot.sound`, every one, re-run after the final source state). QA 2330 → 2340 (+10 in `IrregularCheeger_QA.lean`, the file 166 → 176).** The irregular Cheeger pair now returns *the cut the spectral-partitioning sweep returns*, not just a bound on the conductance infimum, on every symmetric nonnegative positive-degree graph: `sweep_level_extract_vol` (per part, `Cheeger.lean`'s new `VolumeSweepExtraction` section — the regular family's 2026-08-24 attainment route at the `boundary / vol` ratio, the degree-weighted layer-cake cloned from `coarea_core_vol`'s own proof, Component A already degree-weighted, the minority-volume conversion by pure `vol_compl` arithmetic, no `2 ≤ card V` hypothesis) and `cheeger_sweep_cut_normalized` (the median assembly, `VariationalTransfer.lean` — every nonzero degree-weighted zero-sum `f` carries a swept nonempty proper cut at `conductance² ≤ 2 · R_{L_sym}(√D f)`, exactly the hard direction's constraint shape).

**Changes:** (1) `Cheeger.lean` — the `VolumeSweepExtraction` section (the module docstring extended to name it). (2) `VariationalTransfer.lean` — the irregular-sweep-cut section, placed with the family; the whole delivered `VolumeHardDirection` layer consumed a second time (volume median, volume-minority parts, fused contraction verbatim, weighted norm split) so it now carries weight from two theorem families. (3) QA +10: the extraction witness *forced* to `{0}` on the irregular `P₃` fixture through its level-membership iff (conductance `1` from the file's exhaustive-cut pin, the bound `1 ≤ 2/1` both sides raw); the sweep instances on the pair's shared cut test vector (family characterized in-instance, `1 ≤ 8/3` at the independently pinned `R = 4/3` — one test object now consumed by both Cheeger directions *and* the sweep) and on `K₂` (`1 ≤ 4` at the pinned `R = 2`); the degree-weighted zero-sum fence in proved form (`f = ![1,2]` on `K₂`: `∑ deg · f = 3 ≠ 0`, exactly two nonempty proper swept members each of conductance `1`, demanded `1 ≤ 2/5` with `R = 1/5` computed raw — refuted for *every* candidate, `horth` isolated exactly). (4) Records: the proposal (follow-on delivered + the sweep-extraction delivery record with technique findings), `proposals/README.md` (the Delivered row; the natural-candidates paragraph re-ranked — multiway expansion now the family's last priced follow-on), README (2340; the status-paragraph sweep clause; the module-table clause), the radar (QA axis synced 2330 → 2340; the axis-4 sweep-extraction clause, held 4.5 with the protocol reason), the scoreboard (two verification rows + the interpretation bullet), `index/map/spectral_graph.md` (the VT table row + the extraction section), backlog item 3, the execution plan, this log.

**Decisive commands and outcomes:** spike first — `lake env lean wip/vsc_spike.lean` green before any module touched (the per-part extraction after one tactic trim; the median assembly after four: a malformed positivity step, a spurious calc step, an `rw`-direction fix at the `hWf` transport, and `mul_le_mul_of_nonneg_left` at the `^2`-form norm split). Then `lake env lean` zero errors/zero warnings on both changed public modules and the QA file (the QA pass took the recorded pin-technique iterations: entry-fact lemmas replacing depth-2 matrix-literal `simp only` reductions inside inline `linarith` blocks, the `Fin.exists_eq_zero_or_eq_one_or_eq_two` name gap closed by a local `fin_cases` clone, `▸`-direction transports at Fin cases, `obtain` inside `by` blocks preserving outer hypotheses, and `laplacian_quadForm` needing its proof argument explicit in `rw`); explicit `lake build` targets ✔ (module 2190/2190, QA 2193/2193); `#print axioms` on all 13 — the standard three only. **Full `lake build` ✔ (2384/2385, "Build completed successfully") immediately followed by `check_build_completeness.py` — the fence caught the QA docstring edit's stale artifact under a passing build (the documented incident class), remediated by the documented route (the explicit QA target's real re-elaboration, then a fresh full build): 107/107 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass after the record sweep; scoreboard regenerated idempotent (md5-stable; **2340/10/0**).

**Verification:** every changed module elaborates directly and sits fresh-certified by the completeness reconciliation; the delivery is unconditional hard crust (`#print axioms`-verified after the final source state). QA is load-bearing at three levels: the extracted set is *forced* by the level-membership iff on genuinely irregular input (a mis-shaped extraction hypothesis breaks the forcing); the sweep instances join to *independently produced* Rayleigh pins (the shared `P₃` cut test vector's `R = 4/3` and the `K₂` `R = 2` predate the sweep family — non-circular); and the fence isolates `horth` in proved form on a fixture satisfying every other hypothesis, refuting the conclusion for *every* swept candidate.

**Remaining risk:** route provenance is the regular family's (`proposals/sweep-cut-extraction.md`, Chung Ch. 2 at the volume-weighted measure; section-level locator, the standing physical-copy caveat; the statements are proved, so no axiom citation applies). The `Fintype`-classical `Finset.filter` decidability appears as `Classical.choice` in the audit as expected. QA fixtures are `Fin 2`/`Fin 3`; the theorems are size- and weight-general. The Fiedler-vector instantiation at the normalized Laplacian's second eigenvector (the irregular `fiedler_sweep_cut`, which needs the connectivity transfer's kernel characterization to place `√D·1` in the kernel) is the natural next consumer of this interface — recorded, not started.

**Next handoff:** the Active priority table remains empty (no High, no Medium). Next run falls through to the center-out SGT policy with the re-ranked named candidates: the irregular family's last priced follow-on (multiway expansion — radar axis 4's remaining absent category), the irregular Fiedler instantiation just recorded, the standing gated candidates (directed-axis rate; magnetic spectral, each gated on a named consumer; a consumer pricing the wide-band minimax filter designs), or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-26T08:38:58Z — Multiway expansion in delivery: the Step-0 verdict and the every-family easy direction

**Run:** `20260826T083858Z-run-1`  
**Session:** `ses_fc2d9d8a8ffehWSiHYDHKAqik8`  
**Status:** in-progress  
**Milestone:** `proposals/multiway-expansion.md` (new this run) — the execution plan's named top candidate (the irregular family's last priced follow-on, radar axis 4's remaining absent category), priced as a multi-run program whose dedicated run starts with the Step-0 survey; this is that run. The Step-0 verdict is recorded in the proposal before any shelf Lean: both priced obstructions dissolve at the **every-family statement form** — no partition-space attainment needed (any disjoint family certifies; ρ_k packaging stays a follow-on), and cross-part energy is absorbed pointwise by `(a−b)² ≤ 2a² + 2b²` at constant exactly 2 (the classical Lee–Gharan–Trevisan subspace route at plain uncentered part indicators — the pricing's "centered indicators" concern was an artifact of reusing the k = 2 kernel-based engine). Deliverables: the order-statistics↔counting bridge `evals_le_of_card_eigvalOf_le` (shelf has only the two endpoint instances) + the general-k subspace Rayleigh–Ritz engine `evals_le_of_linearIndependent` (both k-general, both reusable) in `Spectral.lean`; the indicator energy identity + the absorption lemma + the headline `cheeger_upper_bound_multiway` (volume-weighted measure, `L_sym`'s sorted spectrum) in `Cheeger.lean`/`VariationalTransfer.lean`; QA on the P₃/K₂ pins plus a new all-rational C₄ fixture with the overlap fence. Zero new axioms planned. Spike first in `wip/mw_spike.lean`; prior runs' uncommitted deliveries preserved untouched.

## 2026-08-26T17:00:00Z — Multiway expansion verification and record closure (continuation 2): completing the interrupted delivery

**Run:** `20260826T165654Z-run-1`  
**Session:** (recorded at terminal entry)  
**Status:** in-progress  
**Milestone:** closing out the active multiway-expansion milestone (Step 0 + Step 1 — the higher-order Cheeger easy direction's every-family form). The continuation run `20260826T133118Z-run-1` landed the full Lean (the `Spectral.lean` engine — `evals_le_of_card_eigvalOf_le`, `evals_le_of_linearIndependent`, plus the spin-offs `evals_sum_eq_trace`, `exists_eigvalOf_eq_of_mulVec_eq_smul`; the application layer and headlines `cheeger_upper_bound_multiway`/`_conductance` in the new `Multiway.lean`; the QA file at the proposal's six obligations, 73 counted declarations) and regenerated the scoreboard (2349 → 2422), but its session ended before verification and the record sweep. This run re-verifies the whole delivery from scratch — direct elaboration of every changed module, the explicit build targets, the `wip/mw_axcheck.lean` axiom audit, full `lake build` + `check_build_completeness.py`, the three linters, scoreboard idempotence — then completes every record: the proposal's delivery record, the Delivered row + natural-candidates re-rank, README (count + module table + status clause), the index map section, backlog item 3, radar axis 4 (multiway was its absent category — the score decision follows the radar's own protocol), scoreboard verification rows, plan retirement, and the terminal entries (this run's and the continuation run's, left unwritten). Zero new axioms planned; the prior runs' uncommitted deliveries preserved untouched.

## 2026-08-26T16:12:00Z — Multiway expansion landed (continuation run, closed by the next): the Lean complete, session ended pre-verification

**Run:** `20260826T133118Z-run-1`  
**Session:** `ses_fc1bdd405ffegvU5gnobbUx5RF`  
**Status:** completed  
**Milestone:** the multiway-expansion milestone's middle session — **the full Lean landed: the k-general engine in `Spectral.lean` (`evals_le_of_card_eigvalOf_le`, `evals_le_of_linearIndependent`, plus the spin-offs `evals_sum_eq_trace`/`exists_eigvalOf_eq_of_mulVec_eq_smul`), the application layer and headlines `cheeger_upper_bound_multiway`/`_conductance` in the new `Multiway.lean` (umbrella import), the QA file at the proposal's six obligations (73 counted declarations), and the scoreboard regeneration (2349 → 2422).** Spikes first (`wip/mw_spike.lean`, `wip/mw_spin2/3.lean`), the modules elaborated and built (artifacts fresh at close), the axcheck drafted (`wip/mw_axcheck.lean`). The session ended before the from-scratch verification pass and before every record beyond the scoreboard and this log's in-progress entry — the proposal's status header, the Delivered row, README/index/backlog/radar updates, and both terminal entries were unwritten. Zero new axioms; every prior uncommitted delivery preserved untouched. Terminal entry and the closing verification recorded by the next run, `20260826T165654Z-run-1`, on the evidence it re-established itself (its entry below) — the same records-gap mechanism as the 2026-08-25 magnetic delivery.

## 2026-08-26T17:07:49Z — Multiway expansion verified and closed: the higher-order Cheeger easy direction delivered end to end (completed)

**Run:** `20260826T165654Z-run-1`  
**Session:** `ses_fc0ff37b5ffeo4Eqo3ZC4hIfYh`  
**Status:** completed  
**Milestone:** the active multiway-expansion milestone closed — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/mw_axcheck.lean` on all 33 audited declarations — 15 public + 18 QA: exactly `propext, Classical.choice, Quot.sound`, every one, re-run by this run after the final source state). QA 2349 → 2422 (+73, `MultiwayCheeger_QA` a new file).** `cheeger_upper_bound_multiway`: on every symmetric nonnegative positive-degree graph, every disjoint nonempty k-family certifies `evals (L_sym) ⟨k−1⟩ ≤ 2 · maxᵢ boundary(Sᵢ)/vol(Sᵢ)` (conductance form at `2 ≤ k`) — the every-family form, no partition-space minimum, the delivered irregular pair as its k = 2 instance; through the k-general engine (`evals_le_of_card_eigvalOf_le`, `evals_le_of_linearIndependent`, plus the spin-offs `evals_sum_eq_trace`/`exists_eigvalOf_eq_of_mulVec_eq_smul`) and the pointwise cross-part absorption lemma at the theorem's constant exactly 2.

**Changes (this run — verification and records only; the Lean itself is the continuation run's, untouched):** every record completed — the proposal (COMPLETE header + the full delivery record with technique notes: the `sup'` nonemptiness-witness discipline at `Fin 2/3/4`, entry-fact lemmas over depth-2 matrix-literal simp cascades, and the trace + raw-eigenvector + PSD recipe for λ₃/λ₄ pins), `proposals/README.md` (the Delivered row; the natural-candidates paragraph re-ranked — the ρ_k packaging and the multiway hard direction the family's priced follow-ons), README (2422; the status-paragraph clause; the module-table clause), the radar (QA axis synced 2349 → 2422 across 57 modules; axis 4's multiway clause — **held 4.5 per protocol with the explicit reason: the higher-order easy half is a genuinely new theorem family, but the raise is bounded by the family's other half — the structural mirror of the 2-way family's pre-2026-08-23 state, with the named 5.0 trigger the multiway hard direction or the ρ_k packaging**), the scoreboard (two verification rows + the interpretation bullet), the index map (the `Multiway` section + 4 engine rows in the `Spectral` section + the status line), backlog item 3 (the delivery update + the re-priced residue), the execution plan (retired to the Delivered block, Active emptied with the next-candidates pointer), the continuation run's terminal entry above, and this entry.

**Decisive commands and outcomes (all run by this run, from scratch):** `lake env lean` on `Spectral.lean` (zero errors; 8 warnings, all pre-existing in HEAD at lines 78/163/253/716/1104/3154/3176 — the new engine block at 3008–3160 adds none), `Multiway.lean` (zero errors/warnings), and `MultiwayCheeger_QA.lean` (zero errors/warnings); explicit `lake build` on the three changed targets ✔; `lake env lean wip/mw_axcheck.lean` — all 33 declarations the standard three only; **full `lake build` ✔ ("Build completed successfully") immediately followed by `check_build_completeness.py` — 109 source files, 109 fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass (re-run after the full record sweep); scoreboard regenerated idempotent (md5-stable at 2b7052b1, **2422/10/0**); `git status` — only the milestone's intended files plus the prior runs' preserved uncommitted deliveries.

**Verification:** the delivery is unconditional hard crust — no axiom consumed anywhere (`#print axioms`-verified on every public and QA declaration listed in the audit file). QA is load-bearing at every level the proposal mandated: the k = n equality instances are *tight* (a degraded constant or engine misshape breaks the pin), the spectral sides are pinned by independent routes (trace arithmetic + raw eigenvectors through the new spin-off bridges — never by the theorem being instantiated), the non-covering family exercises the every-family scope, and the overlap fence refutes the hypothesis-dropped conclusion on a fixture satisfying every other hypothesis — disjointness exercised, not decorated.

**Remaining risk:** route provenance is Lee–Gharan–Trevisan (STOC 2012 / JAMS 2014, §2) — provenance only, every statement proved; the section-level locator carries the standing physical-copy caveat. QA fixtures are `Fin 2`/`Fin 3`/`Fin 4`; the theorems are size- and weight-general. The ρ_k partition-minimum packaging and the multiway hard direction remain priced follow-ons (the former a pure finite-attainment task at the delivered form; the latter multi-run, gated on a named consumer). The whole irregular-Cheeger/multiway stack remains uncommitted (five deliveries' worth, per the wrapper's no-commit rule for this run — the operator's standing arrangement).

**Next handoff:** the Active priority table remains empty (no High, no Medium — every remaining row a Low blocked on a human or technical decision). Next run falls through to the center-out SGT policy with the re-ranked named candidates: the multiway family's own priced follow-ons (ρ_k packaging first — bounded and unblocked; the hard direction gated), the standing gated candidates (directed-axis rate; magnetic spectral, each gated on a named consumer; a consumer pricing the wide-band minimax filter designs), or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

## 2026-08-26T18:14:45Z — The ρ_k partition-minimum packaging in delivery: the classical minimum over the delivered every-family certificate

**Run:** `20260826T181445Z-run-1`  
**Session:** (recorded at terminal entry)  
**Status:** in-progress  
**Milestone:** the multiway delivery's top priced follow-on, selected per the empty High/Medium Active table by the center-out policy as the standing handoff's named top candidate. Delivering in `GraphTheory/Multiway.lean` (a new "the ρ_k packaging" section; no new imports, no umbrella change): `IsMultiwayPartition` (nonempty, pairwise disjoint, covering), `maxPartConductance`, `multiwayExpansion A k := sInf` over k-way partitions, the `sInf_le` bound, attainment over the finite partition space (`Set.Finite.csInf_mem` at the image of the Fintype of families — the every-family form makes this a pure attainment task), the `k ≤ card V` existence supplier, and the headline `cheeger_upper_bound_multiway_rhoK : evals (L_sym) ⟨k−1⟩ ≤ 2 * multiwayExpansion A k` (the every-family conductance theorem consumed at the attained minimizer — no new engine content). QA extends `MultiwayCheeger_QA.lean`: `ρ₂(C₄) = 1/2` exact (adjacent-pair witness below, the headline joined to an independently pinned `λ₂ = 1` above — `≤ 1` by the counting bridge at two raw eigenvectors, `≥ 1` by the `(x₀+x₂)²` sum-of-squares through `secondEval_variational_of_ker`; the minimum provably beats the diagonal partition's `1`), `ρ₂(K₂) = ρ₃(P₃) = 1` at the pinned top eigenvalues, and the ρ₃-on-K₂ empty-set junk fence (`sInf ∅ = 0`, partition-existence load-bearing). Zero new axioms; spike first in `wip/`; prior runs' uncommitted deliveries preserved untouched.

## 2026-08-26T18:41:42Z — The ρ_k partition-minimum packaging delivered: the classical λ_k ≤ 2ρ_k statement form; attainment falsifiable (completed)

**Run:** `20260826T181445Z-run-1`  
**Session:** `ses_fc0bdbc28ffe7prAyWxWDZl8nt`  
**Status:** completed  
**Milestone:** the multiway delivery's top priced follow-on, selected per the empty High/Medium Active table by the center-out policy as the standing handoff's named top candidate — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/rho_axcheck.lean` on all 34 audited declarations — 9 public + 25 QA: exactly `propext, Classical.choice, Quot.sound`, every one). QA 2422 → 2444 (+22 in `MultiwayCheeger_QA.lean`, the file 73 → 95 by the generator metric). Radar axis 4 raised 4.5 → 5.0 at the pre-recorded trigger.** The higher-order Cheeger easy direction now stands in its full classical statement form: `cheeger_upper_bound_multiway_rhoK` — `evals (L_sym) ⟨k−1⟩ ≤ 2 · multiwayExpansion A k` at the minimum over k-way partitions.

**Changes:** (1) `Multiway.lean`'s new "The ρ_k packaging: the partition minimum" section (no new imports, no umbrella change) — `IsMultiwayPartition`, `maxPartConductance` (`sSup` of range — ℝ's conditional completeness rules out `iSup` syntax; the `sup'`↔`sSup` bridge proved once as `finset_univ_sup'_eq_sSup_range`), `multiwayExpansion A k := sInf` over the k-way partitions (the `k > card V` `sInf ∅ = 0` junk documented, hypothesis-gated), `multiwayExpansion_le`, **attainment** `exists_isMultiwayPartition_eq_multiwayExpansion` (`Set.Nonempty.csInf_mem` at the value set's finiteness — a subset of the range over the Fintype of families; attainment is the packaging's only new content, exactly as priced), the headline `cheeger_upper_bound_multiway_rhoK` (the every-family conductance theorem consumed at the attained minimizer, no new engine), and the `k ≤ card V` existence supplier (injection + complement-absorbing last part). (2) QA +22 — the C₄ second-eigenvalue pin `λ₂ (L_sym C₄) = 1` with both sides independent (the counting bridge at the kernel witness `√D·1` and the raw-entrywise mode `![1,0,−1,0]` for `≤ 1`; the `(x₀+x₂)²` sum-of-squares through `secondEval_variational_of_ker` for `≥ 1`); the star instance `ρ₂(C₄) = 1/2` exact (adjacent-pair witness above, the headline joined to the pinned λ₂ below); the minimum provably beating the diagonal partition's `1` (attainment exercised, not decorated); `ρ₂(K₂) = ρ₃(P₃) = 1` at pre-existing independent pins; the empty-set junk fence `ρ₃(K₂) = sInf ∅ = 0` (no 3-partition of two vertices — partition-existence load-bearing); the supplier instance. (3) Records: the proposal (the follow-on delivery record with technique findings + the status header), `proposals/README.md` (the Delivered row; the candidates paragraph), README (2444; the status clause; the module-table clause; the radar snapshot synced), the radar (QA axis synced; axis 4 → 5.0 with the pre-recorded trigger met and the reason amended in place), the scoreboard (four verification rows + the interpretation bullet), the index map (six new rows + the section intro), backlog item 3 (the residue narrowed to the hard direction alone), both docstrings, the execution plan, this log.

**Decisive commands and outcomes:** spike first — `lake env lean wip/rho_spike.lean` green (module side + QA side, zero errors/warnings) before any module touched; the recorded catches: `csInf_le` needs `BddBelow` (supplied by the value set's finiteness), `le_csInf` takes nonemptiness, `Set.Nonempty.csInf_mem` for attainment, `Function.Embedding.nonempty_of_card_le` for the supplier, `Finset.disjoint_insert_{left,right}` vs `Finset.disjoint_singleton_{left,right}` argument orders, the namespace-reopening trap (a second `namespace SpectralGraphTheory.MultiwayQA` inside a still-open `SpectralGraphTheory` lands declarations in the *doubled* namespace and silently unresolves imported names), and `sup'`-H-witnesses blocking `rw` across statements from different theorem statements (bounds derived by `le_trans` at one's own H instead). Then `lake env lean` — zero errors/zero warnings on both changed modules; explicit `lake build` targets ✔ (2191/2191, 2192/2192 — the axcheck hit the stale-olean trap once, remediated by the documented explicit QA-target rebuild); `#print axioms` via `wip/rho_axcheck.lean` — the standard three only, all 34; **full `lake build` ✔ (2385/2386, "Build completed successfully") immediately followed by `python3 scripts/check_build_completeness.py` — 109/109 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass after the record sweep; scoreboard regenerated idempotent (md5-stable; **2444/10/0**).

**Verification:** every changed module elaborates directly and sits fresh-certified by the completeness reconciliation. The delivery is unconditional hard crust — no admitted-axiom contact anywhere (`#print axioms`-verified after the final source state). QA is load-bearing at three levels: the exact spectral pin produced by genuinely independent routes on both sides (never by the theorem family it feeds); the forced-equality instances (ρ₂(C₄) = 1/2, ρ₂(K₂) = ρ₃(P₃) = 1) where the theorem itself bounds the minimum below the exhibited witness — a broken attainment or wrong constant breaks the equality; and the empty-set fence isolating exactly where partition-existence enters, at the definition (the junk `sInf ∅ = 0` value the gated statements never read).

**Remaining risk:** `multiwayExpansion` is classical-choice-adjacent through `sInf` on a classical set (the standard treatment the shelf's other infimum-defined constants — `cheegerConstant` included — receive); every consumer statement is hypothesis-gated on partition existence, and the junk convention is documented at the definition and fenced in QA. Route provenance for the classical statement is Lee–Gharan–Trevisan §1 (the λ_k ≤ 2ρ_k statement form; the statement is proved, so no axiom citation applies). QA fixtures are `Fin 2`/`Fin 3`/`Fin 4`; the theorems are size- and weight-general. The radar's axis-4 raise consumed the pre-recorded trigger; the multiway hard direction is now the axis's one remaining named extension, still gated on a named consumer.

**Next handoff:** the Active priority table remains empty (no High, no Medium — every remaining row a Low blocked on a human or technical decision). Next run falls through to the center-out SGT policy with the re-ranked named candidates: the multiway hard direction (multi-run, gated on a named consumer), the standing gated candidates (directed-axis rate; magnetic spectral, each gated on a consumer; a consumer pricing the wide-band minimax filter designs), or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md` (radar axis 4 now at 5.0; the adjacent-systems axis at 1.0 and the graph-model axis at 3.5 are the lowest-scored frontiers).

## 2026-08-27T10:55:01Z — Alon–Boppana Step 5 in delivery: the diameter-dependent capstone

**Run:** `20260827T105501Z-run-1`  
**Session:** `ses_fbd2b26c7ffezD9nHoTlGzJh6S`  
**Status:** in-progress  
**Milestone:** the Active table's adopted High row's named next action — Step 5, the program's last step: the far-apart-to-diameter bridge (`distEdge ≤ diam` via `exists_edist_eq_ediam_of_finite` + `edist_ne_top_iff_reachable` supplying the `ediam ≠ ⊤` that Step 2 priced as the blocker), the `√` packaging (Nilli's `secondEval (d•1 − A) ≤ d − (1 + 2k√(d−1))/(k+1)` at `ρ := √((d−1)⁻¹)`, plus the classical `d − 2√(d−1) + 2√(d−1)/(k+1)` error shape), the diameter bookkeeping `2(k+1)+1 ≤ diam` (the honest hypothesis-side reading of the `O(1/⌊diam/2⌋)` error), and the two priced Step-4 QA residuals (the P₃ loop-pair orthogonality fence at `(0,1)`/`(2,2)`; the independent engine route at the integer witness `![1,1,0,−1,−1,−1,0,1]`, `R = 8/6`, to `secondEval (2•1 − C₈) ≤ 2/3` — strictly stronger than the radial route's `≤ 1`). Zero new axioms; spike first (`wip/ab5_spike.lean`).

## 2026-08-27T11:31:54Z — Alon–Boppana Step 5 delivered: the diameter-dependent statement — the program COMPLETE (terminal)

**Run:** `20260827T105501Z-run-1`  
**Session:** `ses_fbd2b26c7ffezD9nHoTlGzJh6S`  
**Status:** completed  
**Milestone (delivered):** the Active table's adopted High row's named next action — Step 5, the program's last step, plus both QA residuals the Step-4 delivery priced for this run: **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/ab5_axcheck.lean` on all 13 audited declarations — 5 public module + 8 public QA: exactly `propext, Classical.choice, Quot.sound`, every one). QA 2576 → 2585 (+9, the Step-5 section of `AlonBoppana_QA.lean`). The Alon–Boppana program (Steps 0–5) is COMPLETE, conditional on nothing.**

**Changes:** (1) `GraphTheory/AlonBoppana.lean`'s new `Packaging` section (one import added — `Mathlib.Combinatorics.SimpleGraph.Diam`, not reached transitively by `Metric`): the `√` plumbing `mul_sqrt_inv_eq_sqrt` (`x·√(x⁻¹) = √x` hypothesis-free), the far-apart-to-diameter bridge `distEdge_le_diam` (the Step-2 priced `ediam ≠ ⊤` blocker dissolved in six lines: `exists_edist_eq_ediam_of_finite` exhibits the supremum at a vertex pair, `edist_ne_top_iff_reachable` + connectivity close it, four `dist_le_diam` applications + `omega`), the honest diameter bookkeeping `alonBoppana_diam_ge` (`2(k+1)+1 ≤ diam`, i.e. `k+1 ≤ ⌊diam/2⌋` — hypothesis-side only; the tree-ball hypothesis is never derived from the diameter, per the proposal's qualification-trap warning), the capstone **`alonBoppana_nilli`** — `secondEval (d•1 − A) ≤ d − (1 + 2k√(d−1))/(k+1)` at `ρ = √((d−1)⁻¹)`, consuming `twoEdgeVec_secondEval_le` verbatim — and the classical error shape `alonBoppana_nilli_classical` (`≤ d − 2√(d−1) + 2√(d−1)/(k+1)`). (2) QA +9: the C₈ capstone instance (`≤ 2 − 1 = 1` through the packaging), the classical instance documenting the error term swallowing the content at `k = 0` (`≤ 2`), the diameter instance `3 ≤ diam (supportGraph C₈)`, the **loop-pair fence** (residual 1, on the new `abP3L` fixture whose support graph provably equals `abP3`'s: the loop's level-0 class is `{2}` of card `1 ≠ 2`, and the orthogonality conclusion fails at `⟨![1,1,−1], 1⟩ = 1 ≠ 0` — `IsTreeBall` isolated exactly where the equal-mass lemma consumes it), and the **independent engine route at the integer witness** (residual 2: `secondEval_le_rayleigh` at `![1,1,0,−1,−1,−1,0,1]` gives `secondEval (2•1 − C₈) ≤ (2·6 − 8)/6 = 2/3` — strictly stronger than both theorem routes' `≤ 1` — with orthogonality, squared norm `6`, and quadratic form `8` all computed raw, the form by the support-`{0,1,3,4,5,7}`²-filtered double sum with all 36 `abC8` entries by `rfl`). (3) Records: the proposal (status header COMPLETE, Step-5 delivery record with technique findings, open-next-step → none), `proposals/README.md` (the High row retired to Delivered with the program-level row; the sparsification High row promoted to the table's top row with its named Step-0 next action; the stale "Active table remains empty" snapshot annotated as historical), README (2585; the status paragraph's Steps-4–5 clauses — repairing the Step-4 clause that run had left only in the module table; the module-table row reading program COMPLETE), the radar (QA axis 2576 → 2585; axis 4's evidence gains the Alon–Boppana clause now that the theorem has landed), the scoreboard (two verification rows, the interpretation bullet, the header date), backlog item 3 (program closure), the index map (the Packaging section + 5 rows), both docstrings, this plan, and this log.

**Decisive commands and outcomes:** spike first — `lake env lean wip/ab5_spike.lean` green (module side and QA side, zero errors/warnings) before any shelf Lean; the recorded catches now in the proposal's delivery record: `Real.sqrt_inv`/`Real.div_sqrt` are hypothesis-free (no positivity split needed at `x·√(x⁻¹) = √x`), the finite-attainment supplier for `dist_le_diam`'s `ediam ≠ ⊤`, `simp` on a `dist`-shaped goal rewriting it into the reachability disjunction and stalling (close by `subst` + `SimpleGraph.dist_self`), `min_self` not `min_id`, the filter-shaped if-table requirement for `Fin 8` vector values with per-case kernel-`rfl` proofs, kernel `rfl` NOT evaluating ℝ arithmetic (why the entry-have + `norm_num` recipe exists at all), `norm_num at h ⊢` + `exact h` to close goals whose proof arguments differ (proof irrelevance absorbs them; `linarith` cannot), and the type-ascribed-`have` requirement for `Finset.sum_subset`-shaped outer filters. Then `lake env lean` — zero errors/zero warnings on both changed files; explicit `lake build` targets ✔ (2011/2011 module; QA after the module rebuild — the stale-olean remediation applied once); `#print axioms` via `wip/ab5_axcheck.lean` — the standard three only, all 13; **full `lake build` ✔ (2389/2390, "Build completed successfully") immediately followed by `python3 scripts/check_build_completeness.py` — 113 source files, 113 fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass after the record sweep; scoreboard regenerated idempotent (**2585/10/0**, md5-stable across double regeneration).

**Verification:** the delivery is unconditional hard crust — no axiom contact anywhere (`#print axioms`-verified on every public declaration after the final source state). QA is falsification-oriented at three levels: the capstone instance exercises the full `√` conversion on a real graph at the same number Step 4's independent instantiation produced; the loop-pair fence proves `IsTreeBall` load-bearing exactly where the equal-mass lemma consumes it; and the integer-witness route reaches the theorem's conclusion — strictly better, `2/3` vs `1` — through a structurally different vector with fully raw arithmetic, so a wrong engine, PSD supplier, or kernel fact would break exactly that route.

**Remaining risk:** none for this program — all five steps are shelf facts, zero axioms, and the proposal records COMPLETE with its deferred items (the asymptotic family corollary needing a named graph family; Route B) explicitly still deferred. One cosmetic residue recorded in the plan: C₈'s exact diameter `= 4` stays unformalized (only `≥ 3` was needed and delivered).

**Next handoff:** per priority item 0 — the sparsification High row's **Step-0 survey** (verify `matrix_bernstein`'s exact clause set supports the leverage-score sampling argument; "not tractable at reasonable cost" is a valid recorded outcome); otherwise the Medium-High/Medium rows (empirical-stationary-distribution Step 0; the sampled-Laplacian quadratic-form consumer; the Fiedler-subspace Davis–Kahan Step-0 check against the delivered Band family).

## 2026-08-27T12:37:51Z — Sparsification Step 0 in delivery: the matrix-Bernstein clause-set survey

**Run:** `20260827T123751Z-run-1`  
**Session:** `ses_fbcca90ecffe5JdpFhOMlS0Fob`  
**Status:** in-progress  
**Milestone:** the Active priority table's top High row's named next action — the Step-0 survey for `proposals/spectral-sparsification-via-leverage-scores.md`: verify that `matrix_bernstein`'s exact clause set (Hermitian, pairwise `IndepFun`, Bochner centering `∫ X i ω ∂μ = 0`, the uniform `∀ i ω` spectral-norm bound, the integral-form variance statistic) actually supports the Spielman–Srivastava leverage-score sampling argument, checking the proposal's three named items against shelf and pinned-Mathlib evidence, with a `wip/` spike pricing the riskiest plumbing (the independent-Bernoulli product space). No shelf Lean until the verdict lands; "not tractable at reasonable cost" a valid outcome. SGT leverage: the gate on giving `matrix_bernstein` (one of 7 zero-consumer axioms) its first structural consumer.

## 2026-08-27T13:20:34Z — Sparsification Step 0 delivered: the matrix-Bernstein clause-set survey — verdict tractable (terminal)

**Run:** `20260827T123751Z-run-1`  
**Session:** `ses_fbcca90ecffe5JdpFhOMlS0Fob`  
**Status:** completed  
**Milestone (delivered):** the Active priority table's top High row's named next action — the Step-0 survey for `proposals/spectral-sparsification-via-leverage-scores.md`: **DELIVERED, verdict tractable — zero shelf Lean touched** (QA 2585 and axiom count 10 unchanged; the evidence artifact is the survey spike `wip/ss0_spike.lean`, 316 lines, `lake env lean` zero errors/zero warnings, exit 0).

**Changes:** the verdict record in the proposal (status header + a full Step-0 delivery section): every clause of `matrix_bernstein` has a discharge route at the classical Spielman–Srivastava design. (1) Centering spike-proved end to end (`integral_delta : ∫ δ_e ∂μ = p e` via `PMF.integral_eq_sum`, the one-coordinate marginal, the `≠ ⊤`-guarded `← ENNReal.toReal_sum`); boundedness at the classical `R = 1/q` with two named shelf routes for its rank-one input — plus two interface findings: the uniform `∀ ω` in `h_bound` forces a saturation guard into the Step-1 summand design, and the `Fin n` indexing needs an edge enumeration. (2) Foster's `(∑ᵢ∑ⱼ A i j · R i j)/2 = card V − 1` is exactly the unordered-pair budget identity; only a thin `(n−1)` rescaling of `leverageScore` is prerequisite. (3) The sampling-space infrastructure did not exist (no concrete measure in the shelf, no coordinate-independence lemma in the pin) — the spike builds and proves it: `bernPMF` via `PMF.ofFinset` + the `Finset.sum_prod_piFinset` swap, the marginals `sum_coord_mul`/`sum_coord2_mul`, cylinder measures, and **`indepFun_coord`** (pairwise `IndepFun` of coordinate projections — `h_indep`'s exact shape). A three-slice Step-1+ decomposition and a technique-findings record (the free-`p` autoBound trap behind every stuck-`Fintype ?m` failure; `rw` not going under `∑` binders; HO-pattern metavar failures at lambda arguments; `Finset.mul_prod_erase` naming; `PMF.toMeasure_apply`'s explicit args; the `toReal_sum` side condition) are recorded in the proposal. Records sweep: the proposal, `proposals/README.md` (High row → Step-1 next action), the old `spectral-graph-sparsification.md` Phase-B blocker note corrected per the acceptance bar, this plan, this log.

**Decisive commands and outcomes:** `lake env lean wip/ss0_spike.lean` — **zero errors / zero warnings, exit 0** (iterated to green through the session; every catch is in the technique-findings paragraph); `rg` surveys of the pinned Mathlib (Independence/Basic π-system-only, no `Measure.pi` independence route; `PMF.integral_eq_sum`, `PMF.bernoulli`, `SimpleFunc.ofFinite`, `SimpleFunc.stronglyMeasurable` topology-only, `Bool.instMeasurableSingletonClass`) and of the shelf (`Foster.lean`'s budget identity; the Resolvent/BandDavisKahan `l2OpNorm` routes; the constant-only QA measure usage). No shelf module changed, so the build surface is untouched and no full build was warranted by this run's diff; the records-only sweep was checked with `python3 scripts/lint_axioms.py` (10, no issues), `python3 scripts/check_citations.py`, `python3 scripts/check_markdown_links.py` — all pass.

**Verification:** the verdict's claims are spike-proved where the proposal's checks demanded proof (centering, independence, construction) and source-verified-confirmed-route where priced as Step-1 work (matrix-codomain measurability layer, rank-one norm bound, variance statistic). The proposal honestly marks the classical constants (`R = 1/q`, `‖Σ‖ ≤ 1/q`) as asserted-not-spiked — Slice 2 owns them.

**Remaining risk:** Slice 1 (the sampling-space module) is blueprint-priced but unbuilt; Finding A's guard decision shapes its statement; the matrix layer is confirmed-route but untried.

**Next handoff:** per priority item 0 — sparsification **Step 1, Slice 1** (the sampling-space module; the spike is its blueprint); otherwise the Medium-High/Medium rows — the empirical-stationary-distribution Step 0 is now cheaper (its i.i.d.-space prerequisite is spike-priced), the sampled-Laplacian quadratic-form consumer, the Fiedler-subspace Davis–Kahan Step-0 check.

## 2026-08-27T14:26:00Z — Sparsification Step 1 Slice 1 in delivery: the sampling-space module

**Run:** `20260827T142209Z-run-1`  
**Session:** `ses_fbc6677b5ffeF975gaauEKkOM5`  
**Status:** in-progress  
**Milestone:** the Active priority table's top High row's named next action — **Step 1, Slice 1: the sampling-space module** (`proposals/spectral-sparsification-via-leverage-scores.md`): promote the Step-0 spike's proved blueprint (`bernPMF`, the one-/two-coordinate marginals, `indepFun_coord`, `toMeasure_cyl`, `integral_delta`) into shelf Lean at `Scaffold/Mathlib/Probability/BernoulliProduct.lean`, and build the Lean-untried matrix-codomain transfer layer the Step-0 verdict left as named residual risk (`StronglyMeasurable` at the L2OpNorm topology via the `SimpleFunc.ofFinite` route, `Measurable` at the shelf's matrix pi σ-algebra via `measurable_pi_iff`, the `IndepFun.comp` transfer, the matrix centering integral) — plus a QA file with concrete-instance pins and hypothesis fences. Zero new axioms; spike the matrix layer first (`wip/ss1_spike.lean`). SGT leverage: the shelf's first concrete probability space, cross-listed for the empirical-stationary-distribution Medium-High row's identical i.i.d.-sampling prerequisite, and the gate on `matrix_bernstein`'s first structural consumer (Slice 3).

## 2026-08-27T15:08:00Z — Sparsification Step 1 Slice 1 delivered: the sampling-space module — the shelf's first concrete probability space (terminal)

**Run:** `20260827T142209Z-run-1`  
**Session:** `ses_fbc6677b5ffeF975gaauEKkOM5`  
**Status:** completed  
**Milestone (delivered):** the Active priority table's top High row's named next action — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/ss1_axcheck.lean` on all 42 audited declarations — 18 public module + 24 public QA: exactly `propext, Classical.choice, Quot.sound`, every one). QA 2585 → 2609 (+24, the new `Scaffold/QA/Probability/BernoulliProduct_QA.lean`, the `Probability` QA domain's first file).**

**Changes:** the new `Scaffold/Mathlib/Probability/BernoulliProduct.lean` (umbrella import added): the Step-0 spike's blueprint promoted — `bernPMF` (the product-Bernoulli PMF on `ι → Bool`), the marginals `sum_coord_mul`/`sum_coord2_mul`, the cylinder measures, **`indepFun_coord`** (pairwise `IndepFun` of coordinate projections), **`integral_delta`** (`∫ δ_e ∂μ = p e`) — **plus the Step-0 record's named residual risk retired: the matrix-codomain transfer layer, Lean-untried until this run, proved** (`stronglyMeasurable_coord_matrix` by Mathlib's `StronglyMeasurable.of_finite` — the topology-only `h_meas` route at the shelf's hand-rolled matrix σ-algebra; `measurable_coord_matrix`; the `IndepFun.comp` transfer `indepFun_coord_matrix`; and the centering integrals `integral_coord_smul` and **`integral_coord_center_smul`** — the exact `h_mean` clause shape `∫ ((δ_e/p_e) − 1) • M ∂μ = 0` at `p e ≠ 0`). Cross-leverage on record: the empirical-stationary-distribution Medium-High row names the same i.i.d.-sampling prerequisite, now delivered. QA: the `Fin 2 → Bool` four-atom fixture at `p = ![1/2, 1/3]` — joint masses raw, total mass by two independent routes, three cylinder pins, **independence pinned numerically** (`1/2 · 2/3 = 1/3` through `indepFun_coord`), `∫ δ_1 = 1/3` by two routes, the matrix-layer clause instances, and two proved fences (the `[0,1]` bounds load-bearing at `p = ![2]`; the `p e ≠ 0` centering hypothesis refuted at the junk `0/0` value — the integral is `−M ≠ 0`). Records: the proposal (status header + Slice-1 delivery record with technique findings + next action → Slice 2), `proposals/README.md` (High row next action → Slice 2), README (2609 + module-table row), radar (QA axis synced across 60 modules; axis 7 clause, score held at 4.0 per protocol), scoreboard (two verification rows), backlog item 7, the index map's Sampling Spaces section, this plan, this log.

**Decisive commands and outcomes:** spike first — `lake env lean wip/ss1_spike.lean` (the full module + QA section) iterated to **zero errors/zero warnings** before any shelf Lean; the iteration's catches are the proposal's technique-findings paragraph (`ENNReal.ofReal_mul` takes ONE side condition where `ofReal_add` takes two — the root of the "function expected at `ENNReal.ofReal_mul ?m`" failures; `ofReal`-equalities close by `congr 1; norm_num`, and the merge lemmas must be applied in rw position with the pattern present; `CompleteSpace (Matrix V V ℝ)` resolves at the L2OpNorm scoped instance — probe-verified before `integral_smul_const`; `MeasurableSpace.pi` is already global in Mathlib, so the spike's local instance was dropped; `omit [...] in` must precede the docstring; no pi `DecidableEq` in the pin — atom-disequality side conditions via `congrFun`-at-index witnesses; scalar ascription required in `(1/2) • M` statements or the smul elaborates at `ℕ`). Then `lake env lean` — zero errors/zero warnings on both new shelf files; explicit `lake build` targets ✔ (2042/2042 module, 2043/2043 QA); `lake env lean wip/ss1_axcheck.lean` — all 42 declarations exactly the standard three (output aggregated: 34+8 line-prefix matches, every one `propext, Classical.choice, Quot.sound`); **full `lake build` ✔ (2398/2399, "Build completed successfully") immediately followed by `python3 scripts/check_build_completeness.py` — 115 source files, 115 fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**2609/10/0**).

**Verification:** the delivery is unconditional hard crust — no axiom contact anywhere (`#print axioms`-verified on every public declaration). QA is load-bearing at two levels: the two-route pins (the ∑-∏ theorem vs the raw atom enumeration share no mechanism — a wrong `bernPMF` construction or marginal breaks exactly one route), and the junk-value fence (the `p e ≠ 0` hypothesis of the centering lemma is isolated by *refuting its conclusion* at `p e = 0`, where the junk `0/0 = 0` makes the "centered" integrand identically `−M`). One inherited records repair: the scoreboard's generated-metrics block had been left at the committed 2549/2026-08-26 by the prior uncommitted deliveries (verification rows swept, block not re-run); this run's regeneration brought it to the truthful 2609 — the same staleness class the Step-3b closing run documented.

**Remaining risk:** Slices 2–3 of the sparsification program remain (the deterministic SS algebra with Finding A's saturation-guard statement decision and the `R = 1/q` / `‖Σ‖ ≤ 1/q` constants; then the assembly with Finding B's `Fin n` edge transport and the three proposal QA obligations). The matrix-codomain layer is now proved, so Slice 2's remaining risk is purely the deterministic bounds.

**Next handoff:** per priority item 0 — sparsification **Step 1, Slice 2** (the deterministic SS algebra); otherwise the Medium-High/Medium rows — the empirical-stationary-distribution Step 0 is now cheaper again (its i.i.d.-space prerequisite is *delivered*, `bernPMF` + `indepFun_coord` being exactly its sampling object), the sampled-Laplacian quadratic-form consumer, the Fiedler-subspace Davis–Kahan Step-0 check.

## 2026-08-27T16:19:58Z — Sparsification Step 1 Slice 2 in delivery: the deterministic SS algebra

**Run:** `20260827T161958Z-run-1`  
**Session:** `ses_fbc04c987fferE0kJOYsJY7C3A`  
**Status:** in-progress  
**Milestone:** the Active priority table's top High row's named next action — **Step 1, Slice 2: the deterministic SS algebra** (`proposals/spectral-sparsification-via-leverage-scores.md`): the rank-one norm bound `‖v ⊗ v‖ ≤ v ⬝ v`, the Finding-A-guarded sampling matrices on the delivered Bernoulli space, the variance statistic, and the projector identity `∑_e v_e ⊗ v_e = Π_{im L}` (eigen-coordinate form), retiring the Step-0 record's named residual risk (the `R = 1/q` / `‖Σ‖ ≤ 1/q` classical constants, proved rather than asserted) and the headline `‖Σ‖ ≤ 1/q`. Design: ordered-pair indexing with `1/√2` normalization (the delivered `bernPMF` at `ι = V × V` is the sampling space verbatim; `∑ v_e ⊗ v_e = Π` exactly), zero new axioms, spike first (`wip/ss2_spike.lean`). SGT leverage: the deterministic core `matrix_bernstein`'s first structural consumer (Slice 3) assembles from exactly these pieces.

## 2026-08-27T19:34:53Z — Records repair + Sparsification Step 1 Slice 3 in delivery: the assembly + QA

**Run:** `20260827T193452Z-run-1`  
**Session:** (to be recorded at the terminal entry)  
**Status:** in-progress  
**Milestone:** two parts. (1) **Records repair:** the committed Slice-2 delivery (`d6e62a9`, verified by its own run with the full ladder including `check_build_completeness.py` 117/117) exited post-commit before its terminal activity entry and the execution-plan retirement — the recurring records-gap pattern, fifth instance; this run re-verifies from scratch (direct elaboration of both Slice-2 files, the axcheck re-read against the committed state; this run's end-of-run full build + completeness cover the rest) and closes both records. (2) **The Active table's top High row's named next action — Step 1, Slice 3: assembly + QA** (`proposals/spectral-sparsification-via-leverage-scores.md`): `matrix_bernstein`'s first real consumer. Priced design: the Bool-valued summand shape `ssSummand e ω = F_e (ω e)` closes `h_meas`/`h_indep` through the delivered Slice-1 transfer layer verbatim; Finding B's `Fin n` transport is `Fintype.equivFin` + `Equiv.sum_comp`; the tail substitutes the *proved* `R = 1/q` and `‖Σ‖ ≤ 1/q` into the axiom's exact exponential; `ssSampled` carries the saturation guard deterministically so `ssSampled ω − Π_{im L} = ∑_e X_e ω` holds for every outcome; the norm→quadratic-form transfer (`‖M‖ ≤ t → |xᵀMx| ≤ t·xᵀx`) is Cauchy–Schwarz + the shelf's `l2OpNorm_mulVec_le`. Zero new axioms — the delivery consumes `matrix_bernstein` and must report it honestly in `#print axioms`; spike first (`wip/ss3_spike.lean`). SGT leverage: the payoff slice of the program's strategic aim (a first theorem consumer for one of the seven zero-consumer concentration axioms, exercising its exact hypothesis shape).

## 2026-08-27T20:05:00Z — Sparsification Step 1 Slice 2 delivered: the deterministic SS algebra (terminal; records closed by the next run)

**Run:** `20260827T161958Z-run-1`  
**Session:** `ses_fbc04c987fferE0kJOYsJY7C3A`  
**Status:** completed  
**Milestone (delivered):** the Active priority table's top High row's named next action — **DELIVERED as pure hard crust, zero new axioms** (count stays 10; `#print axioms` via `wip/ss2_axcheck.lean` on all 72 audited declarations — 48 public module + 24 public QA: exactly `propext, Classical.choice, Quot.sound`, every one). QA 2609 → **2632** (+23, the new `Scaffold/QA/SpectralGraph/Sparsification_QA.lean`). The full delivery record (design decisions, statement shapes, technique findings, verification) lives in the proposal's Slice-2 section; the delivery was committed by the operator as part of `d6e62a9` with the full verification ladder recorded in the commit message (full `lake build` ✔ 2400 targets, `check_build_completeness.py` 117/117 fresh / 0 stale / 0 missing, `lint_axioms` 10, zero errors).

**Terminal-entry note (closing run `20260827T193452Z-run-1`):** the delivery session exited post-commit before this terminal entry and the execution-plan Active-block retirement — the recurring records-gap pattern, fifth instance. The closing run re-verified the delivery from scratch against the committed state before writing this entry: `lake env lean Scaffold/Mathlib/GraphTheory/Sparsification.lean` — zero errors / zero warnings; `lake env lean Scaffold/QA/SpectralGraph/Sparsification_QA.lean` — zero errors / zero warnings; the 72-declaration axcheck re-read line by line — every one exactly the standard three, zero non-standard; this run's end-of-run full build + completeness cover the remainder of the ladder.

**Remaining risk:** Slice 3 (assembly + the proposal's three QA obligations) — Finding B's `Fin n` edge-enumeration transport, the norm-event → quadratic-form transfer, the `q`-budget error-shape calculus, and the recorded set-aside (`ssVariance K₂ 1 = rankOne v_(0,1)` exact matrix value).

**Next handoff:** per priority item 0 — sparsification **Step 1, Slice 3** (assembly + QA), pursued by the closing run itself; otherwise the Ramanujan High row (a light composition) or the Medium-High/Medium rows.

## 2026-08-27T20:54:00Z — Records repair + Sparsification Step 1 Slice 3 delivered: the assembly — `matrix_bernstein`'s first real theorem consumer, Step 1 COMPLETE (terminal)

**Run:** `20260827T193452Z-run-1`  
**Session:** `ses_fbb63032affeEN6aEn0jj4u01v`  
**Status:** completed  
**Milestone (delivered):** two parts, both complete. (1) **Records repair:** the committed Slice-2 delivery (`d6e62a9`, verified by its own run) had exited post-commit before its terminal entry and the plan retirement (the records-gap pattern, fifth instance) — re-verified from scratch (`lake env lean` zero errors/zero warnings on both Slice-2 files against the committed state; the 72-declaration axcheck re-read — every one exactly the standard three), terminal entry appended, stale Active block retired, delivered-milestone record written. (2) **The Active table's then-top High row's named next action — Step 1, Slice 3: assembly + QA — DELIVERED, Step 1 COMPLETE and the program's strategic aim met:** zero new axioms (count stays 10); of the 43 audited declarations (`wip/ss3_axcheck.lean`), 39 (the 14 new module declarations and 25 of 27 QA) read exactly `propext, Classical.choice, Quot.sound`, and exactly the two Derived tails plus their two QA interface pins read `…, matrix_bernstein` — the conditional structure honestly reported, never disguised. QA 2632 → **2659** (+27, the new `Scaffold/QA/Derived/SparsificationTail_QA.lean`).

**Changes:** (a) `GraphTheory/Sparsification.lean`'s two new sections — the transfer helpers (`quadForm_add`/`quadForm_sub_matrix`/`quadForm_smul`), the action bound `l2OpNorm_mulVec_dotProduct_le` (a local dot-product route to the C*-norm spine), the symmetry-free norm→form transfer `abs_quadForm_le_of_l2OpNorm_le` (`‖M‖ ≤ t → |xᵀMx| ≤ t (x⬝ᵥx)`), the sampled design `ssWeight`/`ssSampled` with the **exact pointwise deviation identity** `ssSampled ω − Π_{im L} = ∑_e X_e ω` (the saturation guard mirrored as a deterministic weight — no null-event caveats), and the Bool-valued summand shape closing `h_meas`/`h_indep` through the Slice-1 transfer layer verbatim; (b) the new `Scaffold/Derived/SparsificationTail.lean` (umbrella import added) — **`sparsification_norm_tail`** (`μ {‖S(ω) − Π‖ ≥ t} ≤ 2 d exp(−t²/(2/q + 2t/(3q)))` at the proved constants `R = 1/q`, `‖Σ‖ ≤ 1/q`; Finding B's `Fintype.equivFin` + `Equiv.sum_comp` transport; no connectivity hypothesis) and **`sparsification_quadForm_tail`** (the additive eigen-coordinate pullback `|xᵀSx − xᵀΠx| ≤ t(x⬝x)` for every vector outside the bounded-measure set) — conditional on `matrix_bernstein`; (c) the QA (K₂ + zero-graph fixtures): the deviation identity pinned with every piece visible (`0 + (v_e v_eᵀ) + (v_e v_eᵀ) + 0`), **the deviation norm `= 1 = 1/q` tight both sides**, the transfer bound attained with equality, `quadForm_imageProjector_eq`'s first consumer (`qF(Π)v = 1/2`), both tails' interface instances, the nonempty-event witness, and the two-sided connectivity content (the disconnected budget fence `0 ≠ card − 1` beside the connectivity-free identically-zero positive). One mid-run build repair: `quadForm_sub` already declared in AlonBoppana (a different notion) — renamed `quadForm_sub_matrix` with all consumers updated. Records swept: the proposal (status header Step 1 COMPLETE + priced follow-ons + the Slice-3 delivery record with technique findings), `proposals/README.md` (the High row → Medium-follow-ons with the delivery clause; the Ramanujan row now the only High), README (2659; the module rows), the radar (QA axis synced, 62 modules), the scoreboard (two verification rows + the interpretation bullet; metrics regenerated 2659/10/0), the backlog (the Slice-3 clause), the index map (the Sparsification + SparsificationTail sections, 21 rows — also closing the inherited gap that Slice 2's declarations had never been indexed), this plan, and this log.

**Decisive commands and outcomes:** spike first — `lake env lean wip/ss3_spike.lean` iterated to zero errors/zero warnings before any shelf Lean (catches recorded in the proposal: beta-redex spelling mirroring for rewrites against the axiom-instantiated conclusion; `Equiv.sum_comp`'s direction; `Real.exp_le_exp` as iff; `Π` a reserved identifier character; explicit nonneg certificates for nlinarith squaring; the stale-olean recurrence at the module-target boundary). Then `lake env lean` — zero errors/zero warnings on all three changed/new files; explicit `lake build` targets ✔ (2159/2159 module, 2165/2165 derived, 2166/2166 QA); `#print axioms` via `wip/ss3_axcheck.lean` — 39/43 at the standard three, the four bernstein-bearing declarations exactly the two tails and their two QA pins; **full `lake build` ✔ (2400/2401, "Build completed successfully") immediately followed by `python3 scripts/check_build_completeness.py` — 119 source files, 119 fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass after the record sweep; scoreboard regenerated idempotent (**2659/10/0**).

**Verification:** the deterministic core is unconditional hard crust (no axiom contact anywhere, machine-checked); the two tails are axiom-conditional by design and labeled so in their docstrings, the module docstring, the proposal, and this record — QA never proves the axiom, and its interface pins honestly inherit the dependency. QA is falsification-oriented: the deviation norm's tight two-sided pin at the classical constant would break under any wrong constant in the Slice-2 chain; the transfer lemma's bound is attained with equality at the fixture; the connectivity content is proved on both sides of the hypothesis (fence + positive on one fixture).

**Remaining risk:** none blocking. Priced follow-ons recorded in the proposal: the multiplicative `(1±ε)` refinement on `im Π`-coordinate vectors, the `q ~ log n/ε²` budget corollary, the graph-vector Laplacian form (the draft statement's own packaging), and the Slice-2 set-aside (`ssVariance K₂ 1 = rankOne v_(0,1)` exact matrix value).

**Next handoff:** per priority item 0 — the **Ramanujan Expansion Ceiling** High row (a light composition giving `AlonBoppana.lean` its first theorem consumer); otherwise the Medium-High/Medium rows (empirical-stationary-distribution Step 0 — its i.i.d.-sampling prerequisite is delivered; the sampled-Laplacian quadratic-form consumer; the Fiedler-subspace Davis–Kahan Step-0 check) or the sparsification follow-ons.

## 2026-08-27T22:02:30Z — Ramanujan Expansion Ceiling in delivery: the Alon–Boppana × Cheeger composition

**Run:** `20260827T220230Z-run-1`  
**Session:** (to be recorded at the terminal entry)  
**Status:** in-progress  
**Milestone:** the Active priority table's only High row (`proposals/ramanujan-expansion-ceiling.md`), the standing handoff's named next target — the light composition `cheegerConstant A ≤ √(2 (1 − 2√(d−1)/d + 2√(d−1)/(d (k+1))))` pairing `alonBoppana_nilli_classical` with `cheeger_lower_bound` through one new engine piece (`secondEval_smul_of_pos`, the positive-scaling lemma absent from shelf and pin) and one operator identity (`d•1 − A = d • regularNormalizedLaplacian A d` under regularity). `AlonBoppana.lean`'s first theorem consumer; zero new axioms; obstruction/ceiling scope only, no tightness claim (hard acceptance-bar item). Step 0's three checks answered from source evidence and recorded in the proposal before any shelf Lean: `IsDRegular` is definitionally Cheeger's `hd`; the scaling lemma's cheapest route is the variational one (both sides through `secondEval_variational`, sInf-image ping-pong); `h01 → hnonneg` by `Or.elim`. QA plan: the K₂ two-route scaling pin at `c = 3` + the negative-`c` fence (`Variational_QA.lean`); the C₈ `k = 0` ceiling instance joined to a raw `φ ≤ 1/4` cut pin and the two-`k` arithmetic improvement pin (`AlonBoppana_QA.lean`), with the honest note that C₈ hosts only `k = 0` (the on-file `abC8_far_fence`). Spike first (`wip/ram_spike.lean`).

## 2026-08-27T22:37:30Z — Ramanujan Expansion Ceiling delivered: `AlonBoppana.lean`'s first theorem consumer, the Alon–Boppana × Cheeger composition (terminal)

**Run:** `20260827T220230Z-run-1`  
**Session:** `ses_fbac7fa02ffeAog959v6yItlQf`  
**Status:** completed  
**Milestone (delivered):** the Active priority table's only High row (`proposals/ramanujan-expansion-ceiling.md`), the standing handoff's named next target — **DELIVERED as pure hard crust, zero new axioms (count stays 10; `#print axioms` via `wip/ram_axcheck.lean` on all 13 audited declarations — 5 module + 8 QA — reads exactly `propext, Classical.choice, Quot.sound`, every one; the ceiling consumes two *proved* theorems, so the whole chain is unconditional). QA 2659 → 2666 (+7 theorem declarations).**

**Changes:** (a) `Spectral.lean`'s `Lambda2Variational` section — **`secondEval_smul_of_pos`** (exact positive scaling by the variational route: both sides through `secondEval_variational`, the constraint set of `c • M` as the positive-scaled image, `sInf` commuting at `0 < c` by the two-direction ping-pong; PSD + kernel hypotheses exactly what both shelf Laplacians carry — the hypothesis-free generalization stays priced, the pin having no `eigenvalues_smul`/`charpoly_smul`), `smul_isSymm` (public, cross-module), and **`secondEval_congr`** (proof irrelevance across equal operator spellings); (b) `AlonBoppana.lean`'s new `ExpansionCeiling` section (the file gains the `Cheeger` import — no cycle): the operator identity `smul_one_sub_eq_smul_regularNormalizedLaplacian` (`d • 1 − A = d • L_sym` under regularity, the missing `degreeMatrix = d • 1` half) and the headline **`ramanujan_expansion_ceiling`** — `cheegerConstant A ≤ √(2 (1 − 2√(d−1)/d + 2√(d−1)/(d (k+1))))` at exactly `alonBoppana_nilli_classical`'s hypothesis stack, both source theorems consumed verbatim (`h01 → hnonneg` by cases the only bridge) — the first shelf statement connecting the "how good can expansion be" upper-limit direction to the delivered lower-bound machinery. Obstruction scope only, per the proposal's hard acceptance-bar item: no tightness or attainment claim anywhere in the delivery records. (c) QA: `Variational_QA.lean`'s `ScalingK2` section — the K₂ two-route scaling pin (`secondEval (3 • L) = 6`: raw trace/determinant/sortedness `[0, 6]` vs the lemma joined to the on-file `λ₂ = 2`; a wrong scaling constant breaks exactly one route) and the negative-`c` fence (sorted spectrum `[-2, 0]`, `0 ≠ -2`: the `0 < c` hypothesis load-bearing); `AlonBoppana_QA.lean`'s Step 6 — the C₈ ceiling instance (numerically `√2` at `k = 0`, the honest weak-at-small-`k` reading), the non-vacuity join (`φ ≤ 1/4` by the exhibited half-set cut, boundary `2`, volumes `8 = 8` — strict slack `1/4 < √2`, never tight), and the two-`k` improvement pin (arithmetic on the statement's own constants at `d = 2`, with the honest note that C₈ hosts only `k = 0` per the on-file far fence). Records swept: the proposal (Step-0 verdict + COMPLETE header + delivery record with technique findings), `proposals/README.md` (the High row retired to the Delivered table — the Active table now has no High rows), README (2666; the module-table clause), the radar (axis 4's evidence clause, score held at 5.0 per protocol; the QA axis synced 2659 → 2666), the scoreboard (a verification row + the interpretation bullet; regenerated idempotent at 2666/10/0), backlog item 3 (the ceiling clause), the index map (the ExpansionCeiling + scaling-engine sections), this plan, and this log. Nothing committed; the prior runs' uncommitted Slice-3 delivery preserved untouched.

**Decisive commands and outcomes:** spike first — `lake env lean wip/ram_spike.lean` iterated to zero errors/warnings before any shelf Lean (catches recorded in the proposal: `λ` is the `fun` keyword and breaks identifiers like `h2λ`; rewriting a matrix equality under a proof-carrying `secondEval M hM hcard` application fails on the motive — dissolved by stating `secondEval_congr` at hypothesis level and rewriting the whole application; `Matrix.smul_mulVec_assoc`'s direction; `mem_lowerBounds.1` for `BddBelow` destructuring; def-rewrites needing the `show … from rfl` equation form; the `Real.sqrt_lt_sqrt (0 ≤ x) (x < y)` argument order; `norm_num` evaluating inside `√` at `d = 2` and leaving `1 < √2`, closed by rewriting `1 = √1` backwards; Finset-literal sums behaving at width 8 where matrix literals hit the vecCons trap; the stale-olen recurrence at the Spectral → AlonBoppana import boundary). Then `lake env lean` — zero errors on all four touched files, warnings exactly at the pre-existing baselines (Spectral's 8, Variational_QA's 7); explicit `lake build` targets ✔ (all four modules, 2193/2193 among them); `lake env lean wip/ram_axcheck.lean` — all 13 declarations exactly the standard three; **full `lake build` ✔ (2400/2401, "Build completed successfully") immediately followed by `python3 scripts/check_build_completeness.py` — 119 source files, 119 fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass after the record sweep; scoreboard regenerated idempotent (**2666/10/0**).

**Verification:** the delivery is unconditional hard crust — no axiom contact anywhere (machine-checked on every public declaration). The composition is load-bearing on both source theorems' exact shapes: the operator identity's `d ≠ 0` and regularity feed the scaling; a wrong scaling constant, a wrong identity, or a wrong Cheeger/Alon–Boppana statement breaks the ceiling's type or its QA instances. The scaling engine is falsified-against twice (two-route pin; negative-`c` fence), and the ceiling's numeric content is checked on the C₈ fixture against an independent cut-level route (strict slack, honestly non-tight).

**Remaining risk:** none blocking. Priced follow-ons recorded in the proposal: the hypothesis-free general scaling lemma (eigenvalue-multiset machinery the pin lacks; no named consumer), a `k = 1`-hosting fixture (C₁₂) for instance-level two-`k` QA, and the asymptotic family corollary (a named d-regular family with `diam → ∞`).

**Next handoff:** the Active table has no High rows — per priority item 0, fall through to the Medium-High/Medium rows: empirical-stationary-distribution Step 0 (its i.i.d.-sampling prerequisite is delivered), the sampled-Laplacian quadratic-form consumer, the Fiedler-subspace Davis–Kahan Step-0 check, or the sparsification follow-ons.

## 2026-08-28T05:29:30Z — Transit-map freshness reconciliation in delivery: the High row

**Run:** `20260828T052502Z-run-1`  
**Session:** `ses_fb92bda48ffeA3QDR4b37n04l4`  
**Status:** in-progress  
**Milestone:** the Active priority table's only High row (`proposals/verify-scaffold-map-freshness.md`), selected per priority item 0 — the transit map (the operator-facing rendering of the SGT delivery record) drifted from ground truth for days while the pre-commit hook re-rendered it every commit; the fix pattern is the `verify-build-completeness.md` one, a mandatory reconciliation script rather than a process reminder. Deliverable: `scripts/check_scaffold_map_freshness.py` (Tier 1 scoreboard-number + station-parity checks, hard-fail; Tier 2 per-station `source` → proposal-status keyword buckets, fail-loud-not-auto-edit), the `source` schema in both map files, ladder wiring at the five `check_build_completeness.py` locations plus report-only in the hook, and the acceptance-bar fixtures. No Lean, no axioms.

## 2026-08-28T05:46:29Z — Transit-map freshness reconciliation delivered: the check, the source schema, and the ladder wiring (terminal)

**Run:** `20260828T052502Z-run-1`  
**Session:** `ses_fb92bda48ffeA3QDR4b37n04l4`  
**Status:** completed  
**Milestone (delivered):** the Active priority table's only High row (`proposals/verify-scaffold-map-freshness.md`), selected per priority item 0 — **DELIVERED in full; no Lean, no axioms, no QA change (counts stay 2731/10/0, scoreboard regeneration idempotent).**

**Changes:** (1) `scripts/check_scaffold_map_freshness.py` — Tier 1: the scoreboard's generated metrics table is parsed (never re-hardcoded) and every `Repo-wide: N explicit axioms · M QA declarations · K sorries` stamp in either map file must match it (a deleted stamp is its own finding); station parity between the SVG generator's data (parsed via `ast.literal_eval`) and the HTML's data tables (a string-literal-aware recursive brace scanner — a station note embeds `{2t}` inside a quoted string, which ate both a naive `[^0-9]*` regex — HTML entities carry digits — and a first-draft scanner that grabbed spoke objects instead of station objects), pairwise by name on status AND `source`, single-file presence a failure. Tier 2: each cited proposal's first `**Status:**` paragraph (both `**Status:** X` and `**Status: X**` marker spellings accepted — the corpus is not uniform, `alon-boppana-bound.md` uses the second) is keyword-bucketed with **gated-words precedence** (a partly-blocked proposal is not cleanly delivered — and this is exactly what keeps the mixed-phase `spectral-graph-sparsification.md` consistent for the gated Spielman–Srivastava station), then `COMPLETE`/`DELIVERED` → {proved, axiom} (axiom stations with delivered admission proposals are sound), then bare `Proposed` → {open, gated} (the proposal's own sanctioned narrowing: authorized-vs-gated lives in the priority table, not status prose); a station tier outside the bucket fails with the proposal's own status text quoted. (2) The `source` schema in both map files — 32 of 36 stations linked; the four unlinked (Cauchy Interlacing, Foster's Theorem — mixed-phase source; Matrix Concentration — admission predates delivery records; Consensus & Sync.) printed on every run as visible coverage gaps, reasons recorded in the data tables. (3) Ladder wiring at all five `check_build_completeness.py` locations (`scripts/opencode-pursue`'s `verify_for_commit`, `AGENTS.md` § Verification, `docs/2_ARCHITECTURE.md` §10, `scripts/README.md`, this file's format block) plus `.git/hooks/pre-commit` report-only — findings to stderr, never blocking. (4) The proposal's status header → COMPLETE + the delivery record (classifier decisions, the dissolved repair, residuals); `proposals/README.md`'s High row retired + the Delivered-table row (a mid-edit row-clobber of the Fiedler Delivered row was caught by count-check and fully restored — net diff verified as exactly one row modified, one added).

**Decisive commands and outcomes:** `python3 scripts/check_scaffold_map_freshness.py` — **exit 0 on the post-fix tree** (36 stations checked; 32 with a source, 4 without, listed; scoreboard 10 axioms · 2731 QA · 0 sorries); the acceptance-bar fixtures, each a reconstructed pre-fix root in gitignored scratch (removed after): historical stats drift `9 explicit axioms · 1503 QA` in both stamps → **exit 1** with both findings naming the scoreboard's real numbers; a synthetic station in the SVG data only → **exit 1** parity failure; the Alon–Boppana regression (station flipped back to `gated` against its COMPLETE proposal) → **exit 1** with the finding quoting the proposal's own status line; the deleted HTML stamp → **exit 1**; `bash .git/hooks/pre-commit` end-to-end → **exit 0** (SVG regenerated byte-identical — the `source` fields do not render — nothing staged, findings channelled to stderr); `check_markdown_links` / `check_citations` / `lint_axioms` pass after the records sweep; `generate_qa_scoreboard` idempotent (no diff). No Lean source changed, so no `lake build` this run — the Lean tree's last verified state remains the prior run's full build + 123/123 `check_build_completeness`.

**Verification:** the check is falsification-oriented by construction — every tier was demonstrated failing on a reconstructed instance of the exact historical incident it exists to catch, and the fixtures live in the delivery record. Tier 2's honest limits are recorded rather than hidden: it is a forcing function (keyword buckets with named precedence), never an auto-editor, and the note-text-contradiction case stays a documented manual example. One anticipated records repair dissolved under inspection: `decidable-spectral-certificates.md`'s header was read as stale "Proposed" from a truncated preview, but its status paragraph already records "The program is COMPLETE" a sentence later — the classifier reads it correctly, and the misread is recorded in the delivery record as the same preview-truncation error class the check itself guards against.

**Remaining risk:** the stamps' hand-maintained commit-SHA/date text stays unchecked (reconciling it against git state is out of scope for a text ladder step); missing stations for recent deliveries (Ramanujan ceiling, Fiedler Davis–Kahan, empirical-stationary, Multiway, Signed graphs) remain a completeness gap for a human placement decision, per the proposal's Non-goals — flagged, not resolved.

**Next handoff:** the Active table has no High rows — per priority item 0 fall through to the Medium-High/Medium rows (the sampled-Laplacian quadratic-form consumer for `matrix_hoeffding`; the sparsification follow-ons; the empirical-stationary Step 2 once a consumer prices the bias-term shape), or the concentration → subspace-stability pipeline named in the Fiedler program's handoff.

## 2026-08-28T13:25:41Z — Concentration → subspace-stability pipeline in delivery: composing fiedlerLine_stability with edgePerturbation_norm_tail

**Run:** `20260828T132541Z-run-1`  
**Session:** `ses_fb778a266ffekfoYNH33LtGgB9`  
**Status:** in-progress  
**Milestone:** the standing handoff's named next candidate (priority item 0 fall-through — no High rows, only priced follow-ons open): **the concentration → subspace-stability pipeline**, the first join of the two most recent center deliveries. Deliverable: `Derived/EdgePerturbationDrift.lean` — `edgePerturbation_fiedlerSubspace_drift` and `edgePerturbation_fiedlerLine_drift` (high-probability Fiedler rotation under the centered Bernoulli edge design, the `eventStreamProjectorDrift` inclusion idiom at the new design, separation discharged from the base graph's spectral gap via the proved Weyl on the tail event's complement), plus the priced engine follow-on `laplacian_smul`/`laplacian_sum` (Spectral.lean) and the design layer `perturbWeight` with the packaging identity `laplacian (perturbWeight A p ω) = ∑ₑ perturbSummand A p e ω` (EdgePerturbation.lean — the sampled-graph packaging identity's named prerequisite), and the QA section (the identity pinned at the K₂ concrete outcome; the P₃ full-hypothesis line-drift instance with the closed-form bound). Conditional on `matrix_hoeffding` via the tail alone — zero new axioms; the stability side (Davis–Kahan, kernel identification) is proved. SGT leverage: the Fiedler program's payoff statement exercised under a *random* perturbation for the first time, making the kernel-characterization ecosystem load-bearing inside a probability bound.


## 2026-08-28T14:41:02Z — Concentration → subspace-stability pipeline delivered: high-probability Fiedler drift under random edge resampling (terminal)

**Run:** `20260828T132541Z-run-1`  
**Session:** `ses_fb778a266ffekfoYNH33LtGgB9`  
**Status:** completed  
**Milestone (delivered):** the standing handoff's named next candidate (priority item 0 fall-through — no High rows) — **DELIVERED: `Derived/EdgePerturbationDrift.lean`'s `edgePerturbation_fiedlerSubspace_drift` and `edgePerturbation_fiedlerLine_drift`** (`μ{‖Fiedler rotation at ω‖ ≥ t/δ} ≤ 2 d exp(−t²/(2‖∑ₑ L_e²‖))` at the centered Bernoulli edge design whenever the base gap satisfies `t + δ ≤ λ₃ − λ₂`), the first join of the two most recent center deliveries — **zero new axioms (count stays 10; `#print axioms` via `wip/csd_axcheck.lean` on all 29 audited declarations: 27 exactly `propext, Classical.choice, Quot.sound`; exactly the two Derived drift theorems and the drift-QA instance honestly carrying `matrix_hoeffding` alone). QA 2765 → 2785 (+20, `EdgePerturbation_QA.lean`'s drift section).**

**Changes:** (a) the deterministic hinge — `Spectral.lean`'s linearity package `deg_smul`/`laplacian_smul`/`laplacian_sum` (retiring the sparsification program's recorded engine prerequisite) and `EdgePerturbation.lean`'s weight-space layer (`perturbAdj`/`perturbWeight`, symmetric every outcome; entry formulas off-diagonal and diagonal, no double count; the **packaging identity** `laplacian (perturbWeight A p ω) = ∑ₑ perturbSummand A p e ω`); (b) the two drift theorems, in the `eventStreamProjectorDrift` inclusion idiom with one interface improvement — the separation discharged per-outcome from the *deterministic base gap* by the proved Weyl on the tail event's complement, so **no per-outcome spectral hypothesis** remains (the precedent's `hgap` was per-outcome); (c) the QA — the packaging identity by **two independent routes** on K₂ (raw weight-space vs the design route; a wrong `laplacian_sum`/`laplacian_smul` breaks exactly one), the three-path variance statistic exact (`∑ₑ L_e² = 4 • L(P₃)`, `‖·‖ = 12` through the pinned λ₃ = 3), the per-outcome stack at p ≡ ¼ (**support-graph equality**: every edge survives in every outcome), and the closed-form instance `μ{‖rotation‖ ≥ 1} ≤ 6 exp(−1/24)`. Records: the matrix-Hoeffding proposal (follow-on struck + delivery record with technique findings), the Fiedler proposal (companion-consumer note), README (2785 + module row), radar (QA axis synced; score held at 4.0 per protocol — a composition of counted families plus engine, not a new theorem family), scoreboard (verification row + interpretation bullet), backlog (item 4's pipeline clause), index map (weight-space rows + the Drift section), this plan, this log.

**Decisive commands and outcomes:** spike first — `lake env lean wip/csd_spike.lean` iterated to **zero errors/zero warnings** before any shelf edit (the catch record is the proposal's technique findings: `fin_cases`-produced `⟨k, ⋯⟩` literals block rw matching and simp's `Fin.val`-cast evaluation — replaced by the disjunction-substitution idiom `rcases hfin i with rfl | … | rfl` at genuine numerals; implicit-`{i}{j}`-binder lemmas need `(hij := …)` named arguments or the proof lands in the first explicit slot; a missing numeric binder between proofs produces the misleading "numerals are data" error; `simp (config := {decide := true})` for product-numeral if-conditions plain simp leaves half-normalized; `Matrix.transpose_smul` (not `smul_transpose`); `lt_of_le_of_lt` for `≤`-hypotheses; `Fin.ext (by simp)` for the top-index conversion; the stale-olen recurrence at every import boundary). Then `lake env lean` — zero errors on all four touched files, Spectral at exactly its pre-existing 8-warning baseline; explicit `lake build` targets ✔ (Spectral, EdgePerturbation, EdgePerturbationDrift, the QA module — 2165/2165, 2230/2230, 2233/2233 among them); `lake env lean wip/csd_axcheck.lean` — the honest split above; **full `lake build` ✔ (2405/2406) immediately followed by `python3 scripts/check_build_completeness.py` — after the documented single-module mtime remediation (a mid-run `touch` during the baseline check), 127 source files, 127 fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`, `check_markdown_links` pass; scoreboard regenerated idempotent (**2785/10/0**); **map freshness exit 0** after the stats-stamp sync (the check caught the 2765 → 2785 drift on first run, as designed).

**Verification:** the two Derived theorems are conditional on `matrix_hoeffding` via the tail alone and are labeled so in their docstrings, the module docstring, the proposals, the scoreboard, and this record — QA never proves the axiom, and `#print axioms` is the honest record. The deterministic chain is unconditional hard crust and load-bearing on three delivered layers at once: the packaging identity consumes the new linearity package and the single-edge join (a wrong `laplacian_smul` coefficient or `laplacian_sum` base case breaks the QA's two-route pin on exactly one side); the drift consumes `fiedlerLine_stability`'s kernel identification under a *random* perturbation for the first time; and the P₃ instance's closed form would catch any wrong constant in the design, the variance statistic, or the gap discharge.

**Remaining risk:** none blocking. Priced follow-ons recorded in the proposal: the uniform/existential-x quadratic-form packaging, the `s/(γ−s)`-shaped interface consuming the gap inline (mirroring `eventStreamProjectorDrift` exactly), and the matrix-martingale golden-factor question (source-level).

**Next handoff:** **mid-run commit notice — the operator landed `c9b730d` (2026-08-28T13:59:57Z, ~35 minutes into this run), committing the prior runs' deliveries and adding two new Active-table rows: a HIGH row ("Lint Every Axiom Signature for a Missing Degenerate-Corner Guard", `proposals/lint-axiom-degenerate-corner-guards.md`) and a Medium row ("Audit `perron_frobenius` and `primitive_power_tendsto` for the Degenerate-Cardinality Hazard").** This run selected its milestone at 13:25Z when the table verifiably had no High rows (the selection is recorded above); the next run MUST pursue the High linter row per priority item 0 — same tooling profile as the delivered `verify-build-completeness`/`verify-scaffold-map-freshness` ladder steps. After it: the Medium Perron–Frobenius audit, then the priced follow-ons (empirical-stationary Step 2's bias-term shape, the sparsification `(1±ε)`/budget corollaries, a third concentration-axiom consumer).

## 2026-08-28T15:49:30Z — Axiom degenerate-corner guard linter (in progress)

**Run:** `20260828T154318Z-run-1`  
**Session:** `ses_fb6f5cdd9ffejS258jmMlGeAk9`  
**Status:** in-progress  
**Milestone:** `proposals/lint-axiom-degenerate-corner-guards.md` — the
Active priority table's only **High** row (added by the operator mid-run
at 13:59Z, recorded in the prior run's mid-run notice; pursued per
priority item 0). Deliverable: a degenerate-corner guard check in
`scripts/lint_axioms.py` that flags every axiom whose signature carries
a `Fintype`-carried matrix/vector index type with no visible `Nonempty`
guard, or a `Measure` argument with no visible
`IsProbabilityMeasure`/`IsFiniteMeasure`/total-mass guard, with a
per-(axiom, kind) allowlist that records *why* each flagged axiom is
accepted — the loud state, never silence. Both of this week's axiom
repairs had exactly this gap visible in the signature with zero proof
effort needed to see it. Leverage: priority-order items 3/4 (trust
surface) at the admission boundary itself; same tooling profile as the
delivered `check_build_completeness.py` / `check_scaffold_map_freshness.py`
ladder steps. No Lean, no axioms, no QA declarations.

**Next action:** implement the signature parser (multi-line `axiom`
declarations; namespace-scoped `variable` tracking, since six of the ten
axioms carry their measure guard in a `variable` line — Lean includes it
only when the declaration mentions `μ`), the two finding kinds, the
provisional allowlist entries for the anticipated `perron_frobenius` /
`primitive_power_tendsto` findings (Lean-confirmed verdicts are the
Medium companion audit's job), the acceptance-bar fixtures against the
`a1e59ac~1` pre-repair signatures, and the ladder wiring at the five
documented locations.

## 2026-08-28T15:56:54Z — Axiom degenerate-corner guard linter delivered (terminal)

**Run:** `20260828T154318Z-run-1`  
**Session:** `ses_fb6f5cdd9ffejS258jmMlGeAk9`  
**Status:** completed  
**Milestone (delivered):** `proposals/lint-axiom-degenerate-corner-guards.md`
(the Active priority table's only **High** row) — the degenerate-corner
guard check in `scripts/lint_axioms.py`, its per-(axiom, kind)
allowlist, the acceptance-bar fixtures, and the ladder wiring. **No
Lean, no axioms, no QA declarations; counts stay 2785/10/0.**

**Changes:** `check_degenerate_corner_guards` folded into
`lint_axioms.py`'s `main()` (every existing ladder invocation runs it —
no new command to forget) with the two finding kinds the incidents
dictated: a `Fintype`-carried index type (`Matrix V …`/`V →`/
`Fintype.card V`) with no visible `Nonempty` guard, and a `Measure`
argument with no `IsProbabilityMeasure`/`IsFiniteMeasure`/total-mass
guard. The signature model approximates the elaborator as little as
possible: bracket-matched binder parsing (multi-name and anonymous
groups), namespace-scoped `variable` tracking with Lean's name-mention
inclusion semantics (six of the ten axioms carry their measure guard in
a `variable` line, not in the declaration), transitive inclusion
through included binders' types, and Unicode-aware identifiers — the
acceptance bar's own first fixture run caught the scanner blind to
Greek identifiers (`μ`, `Ω`: the measure check could not see `μ` at
all, i.e. exactly the weighted false-silence failure mode) before
delivery. The allowlist landed with provisional entries for exactly
the two anticipated findings (`perron_frobenius`'s `hex` argument,
`primitive_power_tendsto`'s `hπsum` empty-sum argument), each naming
its reasoning as docstring-level and pointing at the companion audit
for the Lean-confirmed verdict; entries are load-bearing (removal
re-flags, fenced) and are to be removed when an axiom acquires a real
guard. The literal `Fin n` sample-index scoping decision is recorded in
the tool's docstring, not silent. Ladder wiring at all five
`check_build_completeness.py` locations plus the admission-time rules:
`AGENTS.md` § Verification, `scripts/opencode-pursue`'s
`verify_for_commit`, `scripts/README.md`, `docs/2_ARCHITECTURE.md` §10
(its paragraph) and §5 (the hazard checklist's mechanical-nudge
sentence), `governance/CONTRIBUTING.md`'s Axiom Addition checklist, and
this log's format block (a new rule: any entry reporting a new axiom
admission must record the check passing with the admission's allowlist
decision).

**Decisive commands and outcomes:** `python3 wip/axlint_fixtures.py` —
all fixtures pass, after the Greek-identifier repair; the fixture set:
pre-repair `matrix_hoeffding` and `hoeffding_lemma` reconstructed
verbatim from `a1e59ac~1` both flag (the historical incidents
reproduced); guard-recognition fences (inline `[Nonempty W]`, hypothesis
`(hW : Nonempty W)`, `[IsFiniteMeasure m]`, `m Set.univ = 1` all
silence; `Matrix W W ℂ` and a `Fintype.card`-prefactor axiom with no
guard both flag; an unused measure variable does not falsely trigger);
the namespace-scope fence (a guard inside a closed namespace cannot
leak past its `end` — the under-flag direction); the allowlist-expiry
fence (removing `perron_frobenius`'s entry re-flags exactly it); and
`wip/axlint_probe.py`'s transitive-inclusion probe (an index type
entering only via `variable {B : Matrix V V ℝ}` still triggers). Real
tree: `python3 scripts/lint_axioms.py` exit 0, deterministic, with
exactly the two `Allowlisted:` notes; all ten axioms verified scanned
at their correct `file:line` positions (`wip/axlint_dump.py`);
`check_citations`, `check_markdown_links` pass; scoreboard regeneration
idempotent (**2785/10/0** — no Lean source touched, so no `lake build`
was run this run; the Lean tree's last verified state remains the prior
run's full build + 127/127 build-completeness); **map freshness exit 0**
(mandatory — this delivery changes a proposal's status header; the
linter proposal is not a map station source, and the check confirmed no
drift); `bash .git/hooks/pre-commit` exit 0 (nothing staged, freshness
report-only channel green); `git status` — exactly the milestone's ten
intended files.

**Remaining risk:** none blocking on the check. The two allowlist
entries are provisional by design — upgrading them to Lean-confirmed
verdicts (or repairs) is the companion audit's scope items 1–3 — and
the `Fin n` scoping decision is the known, recorded under-flag edge
(one documented regex away if a future `n`-prefactor axiom breaks at
`n = 0`).

**Next handoff:** per priority item 0 — the Active table's **Medium**
row: `proposals/audit-perron-frobenius-family-degenerate-corner.md`
(Lean-verified Step-0 verdicts for `perron_frobenius` and
`primitive_power_tendsto` at `card V = 0`, the `card V = 1`
spot-checks, then upgrading this delivery's two provisional allowlist
entries per its scope item 3); then the priced follow-ons
(empirical-stationary Step 2, the sparsification `(1±ε)`/budget
corollaries, a third concentration-axiom consumer, the
uniform/existential-x quadratic-form packaging, the `t/δ`-sharpened
drift interface).

## 2026-08-28T17:03:58Z — PF-family degenerate-corner audit started

**Run:** `20260828T165900Z-run-1`  
**Session:** `ses_fb6b1c779ffetwkHLQEEvU7yYe`  
**Status:** in-progress  
**Milestone:** `proposals/audit-perron-frobenius-family-degenerate-corner.md`
(the Active table's only open Medium row, the delivered linter run's
named next handoff) — Lean-verify the degenerate-cardinality safety of
`perron_frobenius` and `primitive_power_tendsto` (Step 0: derive
`False` from `hex` / `hπsum` alone at `Fintype.card V = 0`; spot-check
`card V = 1`), then upgrade the two provisional linter allowlist
entries to Lean-confirmed verdicts. Trust-surface repair, no new
breadth; zero axioms expected to change.

## 2026-08-28T17:21:58Z — PF-family degenerate-corner audit delivered: both axioms safe by Lean-verified unsatisfiability (terminal)

**Run:** `20260828T165900Z-run-1`  
**Session:** `ses_fb6b1c779ffetwkHLQEEvU7yYe`  
**Status:** completed  
**Milestone (delivered):**
`proposals/audit-perron-frobenius-family-degenerate-corner.md` (the
Active table's only open Medium row, the delivered linter run's named
next handoff) — **COMPLETE with zero axiom changes (count stays 10;
neither `perron_frobenius` nor `primitive_power_tendsto` moved — the
proposal's repair branch never opened). QA 2785 → 2800 (+15).**

**Changes:** (1) **Step 0 verdicts, proved unconditionally in QA** —
`perron_frobenius_hex_unsat_card_zero_QA` (new audit section of
`PerronFrobenius_QA.lean`: at `Fintype.card V = 0`, `False` from
`hex` alone — `Fintype.card_eq_zero_iff` → `IsEmpty V` →
`isEmptyElim` on the witness; an empty index type supplies no `i`)
and `mass_one_unsat_card_zero_QA` (new Section D of
`DirectedMixing_QA.lean`: `False` from `hπsum : ∑ i, π i = 1` alone —
the empty sum is `0`). Each axiom's hypothesis set has *no
instantiation* at the degenerate dimension: safe by unsatisfiability,
structurally unlike the matrix trio (whose hypotheses all stayed
satisfiable while the conclusion's prefactor collapsed) — and now
kernel-checked rather than docstring-asserted, which was the entire
point of the audit: the same shape of prose reasoning is what let the
matrix trio's bug sit. (2) **The `card V = 1` adjacent corners**
(scope item 2): at `Fin 1`/`!![1]`, `perron_frobenius_S1_QA` pins the
axiom instance to the hand Perron data (root exactly `1` from the
eigen-equation on the unknown witness; the simplicity clause — the one
the scope item named as the risk — exactly the hand
`rootMultiplicity 1 = 1` via `S1_charpoly_QA`/
`S1_rootMultiplicity_QA`), and `P1_singleton_hand_QA` proves the
primitive limit shape *without* the axiom (constant sequence) beside
the non-vacuous instance `P1_singleton_axiom_QA`. (3) **The allowlist
upgrade** (scope item 3): both provisional `lint_axioms.py` entries
replaced with Lean-confirmed entries citing the theorem names; the
linter proposal's residual struck through as resolved. (4) **Records**:
the proposal (COMPLETE header, verdict section with the exact Lean
arguments, technique findings, delivery record), `proposals/README.md`
(row retired + Delivered-table row), the index map's corner note,
README (2800), the radar QA axis (score held 4.0 — audit records, not
a new theorem family), the scoreboard (verification rows +
interpretation bullet), the map stamps, the execution plan, this log.

**Verification:** spike first (`wip/pfa_spike.lean`, zero
errors/warnings before any shelf edit; the unsatisfiability arguments
elaborated live against the actual axioms); `lake env lean` zero
errors/zero warnings on both touched QA modules; explicit `lake
build` targets ✔ (2202/2202); `#print axioms` via `wip/pfa_axcheck.lean`
on all seven new declarations — the two verdict lemmas and three hand
pins exactly `propext, Classical.choice, Quot.sound`, the two
singleton instances carrying exactly their named axiom; **full `lake
build` ✔ immediately followed by `check_build_completeness.py` —
127/127 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` exit 0 (10
axioms, both findings allowlisted-confirmed, none provisional);
`check_citations`, `check_markdown_links` pass; scoreboard
regenerated idempotent (**2800/10/0**); **map freshness exit 0**
(mandatory — this delivery changes a proposal's status header; stamps
synced 2785 → 2800 before the check, which then confirmed no drift).
Nothing committed; prior runs' uncommitted deliveries preserved
untouched.

**Remaining risk:** none owed by the proposal. Its honesty note
stands as the recorded residual: the audit cleared the
degenerate-cardinality mechanism only, not either axiom's mathematical
content — a wrong constant or strictness mismatch elsewhere would need
its own Step 0 if ever suspected (none is). The
signature-visible half of the hazard class stays mechanically enforced
by `lint_axioms.py` on every admission.

**Next handoff:** the Active table has no High rows and no open
Medium rows — fall through to the center-out policy: the priced
follow-ons on record (empirical-stationary Step 2 gated on a consumer
pricing the bias-term shape; the sparsification `(1±ε)`/budget
corollaries; a third concentration-axiom consumer; the
uniform/existential-x quadratic-form packaging; the `t/δ`-sharpened
drift interface), or the next load-bearing gap
`docs/6_SGT_BACKLOG.md` names.

## 2026-08-28T18:30:01Z — Sparsification `(1±ε)` multiplicative refinement + budget corollary in delivery

**Run:** `20260828T183001Z-run-1`  
**Session:** `ses_fb663c26affeivsby4ztzWdpk3`  
**Status:** in-progress  
**Milestone:** the sparsification proposal's two priced one-slice
follow-ons (`proposals/spectral-sparsification-via-leverage-scores.md`,
follow-on delivery record): the multiplicative `(1±ε)` quadratic-form
tail on `im Π`-coordinate vectors (the field-standard "S is a
(1±ε)-sparsifier" sentence) and the `q ≥ (8/3)·log(2d/δ)/ε²` budget
corollary — both on the delivered `sparsification_quadForm_tail` base,
so zero new axioms (conditional on `matrix_bernstein` alone). Selected
per the standing handoff's fall-through: no High/open-Medium rows; the
empirical-stationary Step 2 stays consumer-gated and the uniform-x
edge-perturbation packaging is a re-packaging, while this is the
program's payoff statement shape. Engine piece:
`quadForm_imageProjector_eq_of_mulVec_eq` (the projector's `im Π`-cone
identity). QA plan: order-independent im-Π membership at the K₂ edge
vector, the tight ε = 1 two-sided instance, failure-event nonemptiness
at ε = 1/2 with hand values, and the un-guarded pointwise refutation
at the all-false outcome fencing the cone hypothesis.

## 2026-08-28T18:48:43Z — Sparsification `(1±ε)` refinement + budget corollary delivered: the SS program's payoff sentence (terminal)

**Run:** `20260828T183001Z-run-1`  
**Session:** `ses_fb663c26affeivsby4ztzWdpk3`  
**Status:** completed  
**Milestone (delivered):**
`proposals/spectral-sparsification-via-leverage-scores.md` (the
proposal's two priced one-slice follow-ons, the standing handoff's
named fall-through candidate — the Active table has no High rows and
no open Medium rows) — **both DELIVERED as zero new axioms (count
stays 10; `#print axioms` via `wip/ssmult_axcheck.lean`: the engine
lemma and six hard-crust QA lemmas exactly `propext,
Classical.choice, Quot.sound`; the two Derived theorems and their two
QA interface pins honestly carrying `matrix_bernstein` alone). QA
2800 → 2808 (+8).**

**Changes:** (1) **The engine piece** —
`quadForm_imageProjector_eq_of_mulVec_eq` in `Sparsification.lean`:
at every `im Π`-coordinate vector the projector's quadratic form is
exactly the squared norm, the identity that makes the multiplicative
reading legitimate (off the cone the zero-eigenvalue mass is dropped
and the conversion is unsound — fenced, below). (2) **The two Derived
theorems**: `sparsification_multiplicative_tail` — the field-standard
"S is a (1±ε)-sparsifier" shape, the failure of the two-sided
quadratic-form bound over vectors the image projector fixes obeying
the same exponential tail (a `measure_mono` from the delivered
additive tail at `t = ε`, any `0 < ε`) — and
`sparsification_multiplicative_budget`: at `0 < ε ≤ 1`, budget
`q ≥ (8/3)·log(2d/δ)/ε²` drives the failure measure below `δ`, the
`8/3` exact (the Tropp exponent rewritten as `qε²/(2+2ε/3)`, the
denominator at most `8/3`, closed through `Real.exp_log`; holds at
every `δ > 0`, `δ > 2d` included — no case split). (3) **QA (+8)**:
the edge vector's order-independent im-Π membership (at a
zero-eigenvalue basis index the edge vector's own definition vanishes
— no `eigvalOf` ordering assumption anywhere), the engine identity's
first instance, the tight `ε = 1` two-sided instance (upper bound
attained with equality, consistent with the deviation norm `= 1/q`),
failure-event nonemptiness at hand values (`1 > 3/4`), the **cone
fence** (at the all-false outcome `S = 0` is proved — both cross-pair
weights `δ/p = 0`, loops' rank-one factors zero — and the un-guarded
pointwise claim is *refuted* at `onesVec`: `(1/2)·2 = 1 > 0`), and
both interface pins (the budget's `(8/3)·log 8/(1/4) ≤ 100`
discharged by `log 8 ≤ 300/32` from `Real.add_one_le_exp`). (4)
**Records**: the proposal (status header + full follow-on delivery
record with technique findings — the `Real.log`-argument numeral/cast
rewrite trap, the explicit `field_simp; ring` prefactor normalization
before `linarith`, `log_le_iff_le_exp` as this pin's spelling,
forward-only `exp_neg`, `positivity`'s blindness to variable
hypotheses), `proposals/README.md` (the Active row retired to the
Delivered table at the proposal-boundary rule; the superseded Phase-B
row's stale "see the High row above" pointer fixed), README (2808;
one module-table clause), the radar (QA axis synced, score held 4.0
per protocol — a packaging of the counted sparsification family, not
a new theorem family), the scoreboard (verification row +
interpretation bullet), the backlog (item 7's follow-on clause), the
index map (three new rows + the module blurb), the map stamps, this
plan, and this log.

**Verification:** spike first (`wip/ssmult_spike.lean`, all pieces to
zero errors/warnings before any shelf edit); `lake env lean` zero
errors/zero warnings on all three touched modules; explicit `lake
build` targets ✔; `#print axioms` exactly as designed; **full `lake
build` ✔ (2405/2406) immediately followed by
`check_build_completeness.py` — 127/127 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10, both findings allowlisted-confirmed),
`check_citations`, `check_markdown_links` pass; scoreboard
regenerated idempotent (**2808/10/0**); **map freshness exit 0**
(mandatory — this delivery changes a proposal's status header; the
stamps were synced 2800 → 2808 and the check confirmed no drift) and
the pre-commit hook end-to-end exit 0. Nothing committed; the prior
runs' uncommitted deliveries preserved untouched.

**Remaining risk:** none owed by the proposal. Its one remaining
priced follow-on (not started): the graph-vector multiplicative form
(`xᵀL̃x` vs `xᵀLx` — needs the sampled-Laplacian object), recorded so
no run mistakes the delivered eigen-coordinate form for it.

**Next handoff:** the Active table's only actionable row is the
empirical-stationary Step 2, still gated on a consumer pricing the
bias-term shape; otherwise the priced follow-ons on record (a third
concentration-axiom consumer — e.g. the uniform/existential-x
quadratic-form packaging of the edge-perturbation tail, or the
`t/δ`-sharpened drift interface), or the next load-bearing gap
`docs/6_SGT_BACKLOG.md` names.

## 2026-08-28T20:06:03Z — Graph-vector sparsification form in delivery: the sampled Laplacian's (1±ε) tail

**Run:** `20260828T200603Z-run-1`  
**Session:** `ses_fb6147a1effen0Rpy6ibuaLYsN`  
**Status:** in-progress  
**Milestone:** the sparsification proposal's last priced follow-on
(`proposals/spectral-sparsification-via-leverage-scores.md`): the
*graph-vector* multiplicative form — `xᵀL̃(ω)x` vs `xᵀLx` on the
sampled Laplacian for every graph vector, no `im Π` cone restriction,
at the same exponential tail plus the budget corollary. Selected per
the standing handoff's fall-through: no High/open-Medium rows; the
empirical-stationary Step 2 stays consumer-gated. Zero new axioms
expected (conditional on `matrix_bernstein` alone via the delivered
additive tail). Engine pieces: the transport `ssTransport` (eigen
coordinates × `√λ`, automatically on-cone — the mechanism that removes
the cone hypothesis), the isometry through `quadForm_eigvalOf`, claim A
at positive pairs through `eq_of_laplacian_mulVec_eq_zero_of_pos_weight`,
and the sampled-Laplacian object with its form-level correspondence.
QA plan: K₂ raw pins + two-route correspondence join + tight `ε = 1`
instance + the signed-fixture fences refuting both new engines'
nonnegativity hypothesis (junk-zero transport vs `√(1/2) ≠ 0`; `−36 < 0`).

## 2026-08-28T20:38:38Z — Graph-vector sparsification form delivered: the sampled Laplacian's (1±ε) tail, no cone restriction (terminal)

**Run:** `20260828T200603Z-run-1`  
**Session:** `ses_fb6147a1effen0Rpy6ibuaLYsN`  
**Status:** completed  
**Milestone (delivered):**
`proposals/spectral-sparsification-via-leverage-scores.md` (the
proposal's last priced follow-on, the standing handoff's named item —
the Active table has no High rows and no open Medium rows) — **the
graph-vector multiplicative form DELIVERED as zero new axioms (count
stays 10; `#print axioms` via `wip/ssgv_axcheck.lean` on all 28 audited
declarations: the 11 shelf declarations and all hard-crust QA exactly
`propext, Classical.choice, Quot.sound`; the two Derived theorems and
their two QA interface pins honestly carrying `matrix_bernstein`
alone). QA 2808 → 2830 (+22).**

**Changes:** (1) **The engine layer** — `GraphTheory/Sparsification.lean`'s
new `Transport` section: the transport `ssTransport` (`c(x)_k = √λ_k
(x ⬝ᵥ q_k)` — on the `im Π` cone *by construction*, which is exactly
why the graph-vector statement needs no cone hypothesis: the
restriction moved from the theorem's hypotheses into the definition),
the isometry `quadForm_laplacian_eq_ssTransport` (`xᵀLx = ‖c(x)‖²`
through `quadForm_eigvalOf`), claim A `ssTransport_dot_ssEdgeVec`
(`c ⬝ᵥ v_e = √(w_e/2)(x u − x v)` at positive pairs, the kernel
constancy `eq_of_laplacian_mulVec_eq_zero_of_pos_weight` load-bearing),
the sampled Laplacian `ssLaplacian` (symmetric, PSD), and the
form-level correspondence `quadForm_ssLaplacian_eq` (`xᵀL̃(ω)x =
c(x)ᵀ S(ω) c(x)` for every vector and every outcome — claim A squared
at positive pairs; at nonpositive weights a junk-zero corner analysis:
the edge vector vanishes through `√`, forcing the probability to `0`
and the weight to `δ/0 = 0`, so both per-pair terms die). (2) **The
Derived theorems** — `Derived/SparsificationTail.lean`:
`sparsification_graph_tail` — the textbook sentence `(1−ε)xᵀLx ≤
xᵀL̃(ω)x ≤ (1+ε)xᵀLx` failing only on a set of the delivered
exponential bound's measure, for *every* graph vector (a `measure_mono`
from the delivered additive tail at `y := c(x)`: the isometry
identifies the denominators, the correspondence the numerators) — and
`sparsification_graph_budget` (the same `q ≥ (8/3)·log(2d/δ)/ε²`
sentence, numeric chain factored as a private `sparsification_budget_core`;
the delivered budget proof untouched). (3) **QA (+22)** — the raw pins
`xᵀLx = 4` (Dirichlet identity) and `xᵀL̃x = 8` (per-pair evaluation of
the definition), the isometry instance joined to the raw `4`, the
correspondence joined by **two independent routes** (the raw `8`
against the sampled operator's own evaluation through the claim-A dot
values — a wrong weight, edge difference, claim A, or correspondence
breaks exactly one side), the tight `ε = 1` instance (`8 = 2·4`
attained, a pure-data join), failure-event nonemptiness, both interface
pins, and the **signed-fixture fences**: at one fixture
(`A = !![0,−2,1; −2,0,−2; 1,−2,0]`, `L = −rankOne ![1,−2,1]` — all
eigenvalues nonpositive, kernel two-dimensional and non-constant) the
transport is *provably junk-zero* (`√λ_k = 0` for every `k`) while
`xᵀLx = −36` and `√(A₀₂/2)·(x₀−x₂) = √(1/2) ≠ 0`: the isometry and
claim A both *refuted* in proved form without `hnn` — nonnegativity
load-bearing on both new engines, fenced exactly as the delivered
family's signed fences fence theirs. (4) **Records**: the proposal
(status header + the second follow-on delivery record with technique
findings — `λ` is a reserved token so `hλ` does not parse, `mul_sub`
not `sub_mul`, `Real.sqrt_eq_zero_of_nonpos`'s name, `Real.sqrt_div`'s
positional signature, the calc-terminal-form trap with pre-normalized
`pow_two`, parenthesized lambdas inside `rw`, ∀-equation `simp only`
for under-binder coefficient rewrites, the stale-olen recurrence at
the Derived import boundary — and the residual struck through: the
proposal now has no open follow-ons), `proposals/README.md` (the
Delivered-table row completed — "program COMPLETE"; the superseded
Phase-B row's pointer), README (2830; one module-table clause), the
radar (QA axis synced, score held at 4.0 per protocol — the textbook
statement shape of the already-counted sparsification family, not a
new theorem family), the scoreboard (verification row + interpretation
bullet), the backlog (item 7's follow-on clause), the index map (five
engine rows + the two Derived rows + the module blurb), the map
stamps, this plan, and this log.

**Verification:** spike first (`wip/ssgv_spike.lean`, every piece
iterated to zero errors/warnings before any shelf edit — the module
part, the Derived theorems, and the full QA section including the
fences); `lake env lean` zero errors/zero warnings on all three touched
modules; explicit `lake build` targets ✔ (2159/2159, 2165/2165,
2166/2166); `#print axioms` exactly as designed; **full `lake build` ✔
(2405/2406, "Build completed successfully") immediately followed by
`check_build_completeness.py` — 127/127 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10, both findings allowlisted-confirmed),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
idempotent (**2830/10/0**); **map freshness exit 0** after the
stats-stamp sync 2808 → 2830 (mandatory — this delivery changes the
proposal's status header). Nothing committed; the prior runs'
deliveries are committed at `760526e` and preserved untouched.

**Remaining risk:** none owed by the proposal — it now has no open
priced follow-ons. The two graph-vector theorems remain conditional on
`matrix_bernstein` and must never be described as foundationally
proved.

**Next handoff:** the Active table's only actionable row is the
empirical-stationary Step 2, still gated on a consumer pricing the
bias-term shape; otherwise the priced follow-ons on record (a third
concentration-axiom consumer — e.g. the uniform/existential-x
quadratic-form packaging of the edge-perturbation tail, or the
`t/δ`-sharpened drift interface), or the next load-bearing gap
`docs/6_SGT_BACKLOG.md` names.

## 2026-08-29T04:37:41Z — Irregular Cheeger window assembly (in-progress)

**Run:** `20260829T043741Z-run-1`  
**Session:** `ses_fb43760f1ffeHJ6dyaqJCwOvH5`  
**Status:** in-progress  
**Milestone:** the degree sandwich's own named consumer — the irregular
(normalized) Cheeger window under random edge resampling, composing the
delivered λ₂ tail, the 2026-08-29 degree sandwich, and the irregular
Cheeger pair; the first three-way composition across those three
families. Step-0 design verdicts settled: admissibility window
event-internal (no design restriction preserves the centered design, and
the norm tail carries zero degree information since `L(E_ω)·1 = 0`
identically); floor consumes the sandwich lower side at the perturbed
degree ceiling, ceiling the upper side at the degree floor; new engine
pair `dmin·φ²/2 ≤ λ₂(L A) ≤ 2·dmax·φ(A)`. Spiking in `wip/` before any
shelf edit.

## 2026-08-29T05:02:14Z — Irregular (normalized) Cheeger window delivered: the degree sandwich's consumer, the λ₂ tail × sandwich × irregular-Cheeger three-way composition (terminal)

**Run:** `20260829T043741Z-run-1`  
**Session:** `ses_fb43760f1ffeHJ6dyaqJCwOvH5`  
**Status:** completed  
**Milestone (delivered):** the degree sandwich's own named priced
follow-on (and the execution plan's top open candidate) — the
high-probability **normalized**-connectivity window under random edge
resampling, on arbitrary symmetric nonnegative positive-degree base
graphs with no regularity — **DELIVERED as zero new axioms (count
stays 10; `#print axioms` via `wip/irrwin_axcheck.lean` on all 14
audited declarations: the engine pair and ten hard-crust QA lemmas
exactly `propext, Classical.choice, Quot.sound`; the two Derived
window theorems and the two closed-form QA instances honestly carrying
`matrix_hoeffding` alone). QA 2902 → 2918 (+16,
`EdgePerturbation_QA.lean`'s normWindow section).**

**Changes:** (1) **The engine pair** —
`GraphTheory/VariationalTransfer.lean` beside the sandwich's
interfaces: `cheeger_lower_bound_laplacian_of_degree_window`
(`dmin·φ²/2 ≤ λ₂(L)`, the irregular hard direction ×
`mul_degMin_le_lambda2`) and
`cheeger_upper_bound_laplacian_of_degree_window` (`λ₂(L) ≤ 2·dmax·φ`,
via `lambda2_le_mul_degMax`) — the degree-window generalizations of
the regular pair, reducing to it at `dmin = dmax = d`. (2) **The
window** — `Derived/EdgePerturbationTail.lean`'s NormalizedCheegerWindow
section: `perturbAdmissible` (the event-internal admissibility window),
`edgePerturbation_normalized_cheeger_floor`, and
`edgePerturbation_normalized_connectivity_bracket`. Both Step-0 design
verdicts settled as the sandwich proposal predicted: the per-outcome
degree bound is event-internal (no design restriction preserves the
centered tail; the norm tail carries zero degree information since
`L(E_ω)·1 = 0` identically), and the floor consumes the sandwich's
lower side at the perturbed degree *ceiling* while the ceiling consumes
the upper side at the degree *floor*. (3) **QA (+16)** — the engine
ceiling attained with equality on `K₂`, the genuinely irregular `P₃`
instances (φ(P₃) = 1 transferred entrywise), the scale-invariance raw
computation with `λ₂(L_sym) = 2` at the all-true outcome, the
admissibility witnesses on **both** window sides (all-false excluded by
the degree floor; `P₃` all-true by the degree ceiling `5 > 3` with
nonnegative entries), the complement witness (`2` strictly inside the
window at `t = 1/2`), and the two closed-form instances
(`4 exp(−1/64)`). (4) **Records** — the matrix-Hoeffding proposal (the
follow-on delivery record with the Step-0 verdicts, the honesty note,
and technique findings), the sandwich proposal (status header + the
residual struck through), `proposals/README.md` (both Delivered rows),
README (2918; one module-table clause), the radar (QA axis synced,
score held at 4.0 per protocol), the scoreboard (verification row +
interpretation bullet), the backlog (the follow-on clause closed), both
index maps, the map stamps + regenerated SVG, the execution plan, and
this log.

**Verification:** spike first (`wip/irrwin_spike.lean`, every piece to
zero errors/warnings before any shelf edit; one statement-direction
slip caught by elaboration and recorded in the proposal);
`lake env lean` zero errors/zero warnings on all three touched modules
(the QA module at its pre-existing `Try this: ring_nf` baseline,
verified present on the HEAD version of the file); explicit `lake
build` targets ✔ (`VariationalTransfer`, `EdgePerturbationTail`,
`EdgePerturbation_QA` — each "Build completed successfully");
`#print axioms` exactly as designed (14 declarations); **full `lake
build` ✔ (2405/2406) immediately followed by
`check_build_completeness.py` — 128 source files, 128 fresh artifacts,
0 stale, 0 missing, exit 0**; `lint_axioms` (10, both findings
allowlisted-confirmed), `check_citations`, `check_markdown_links`
pass; scoreboard regenerated idempotent (**2918/10/0**); **map
freshness exit 0** after the stats-stamp sync (mandatory — this
delivery changes the sandwich proposal's status header).

**Remaining risk:** none owed — the window family's priced follow-on
list is empty on both spelling sides. The two new Derived theorems are
conditional on `matrix_hoeffding` and must never be described as
foundationally proved. The honesty note stands: the admissibility
window is proof-load-bearing with no dropped-window refutation fixture
at fixture scale — the normalized Laplacian's junk value at
zero-degree corners is the *identity's* spectrum (`λ₂ = 1`), not the
zero matrix's (a spike-level finding recorded for the next corner
audit).

**Next handoff:** the Active table's only actionable row remains the
empirical-stationary Step 2, still gated on a consumer pricing the
bias-term shape; otherwise the next load-bearing gap
`docs/6_SGT_BACKLOG.md` names, or a new composition the now-complete
window/sandwich/tail triangle unlocks (e.g. the volume-weighted sweep
extraction joined to the normalized window's floor — priced, not
owed).

## 2026-08-29T06:06:01Z — Sweep-cut consumer of the normalized window (in-progress)

**Run:** `20260829T060601Z-run-1`  
**Session:** `ses_fb3e2e4d4ffeAL7MrTS8ProaBm`  
**Status:** in-progress  
**Milestone:** the standing handoff's named composition — the
volume-weighted sweep extraction joined to the normalized connectivity
window: `edgePerturbation_fiedler_sweep_cut_tail`, a high-probability
*certified swept Fiedler cut of the resampled graph* (connected ∧ an
explicit swept level set at `conductance² ≤ 2·(2·dmax·φ + t)/dmin`)
under random edge resampling, on the admissible outcomes, at the new
floor-positivity hypothesis `0 < dmin·φ²/2 − t` (the floor's positivity
is what the connectivity transfer consumes: `λ₂ > 0 ↔ connected`). A
pure `measure_mono` into the delivered bracket, load-bearing on three
delivered families (bracket, connectivity transfer,
`fiedler_sweep_cut_normalized`). QA: closed-form K₂/P₃ tail instances
plus the good-outcome witness at the all-true outcome. Spiking in
`wip/sweepwin_spike.lean` before any shelf edit.

## 2026-08-29T06:17:46Z — Swept-Fiedler-cut consumer of the normalized window delivered: the window family's algorithm-facing capstone (terminal)

**Run:** `20260829T060601Z-run-1`  
**Session:** `ses_fb3e2e4d4ffeAL7MrTS8ProaBm`  
**Status:** completed  
**Milestone (delivered):** the standing handoff's named composition —
the volume-weighted sweep extraction joined to the normalized
connectivity window — **DELIVERED as zero new axioms (count stays 10;
`#print axioms` via `wip/sweepwin_axcheck.lean` on all five audited
declarations: the connectivity pin and the good-outcome witness exactly
`propext, Classical.choice, Quot.sound`; the Derived theorem and the
two closed-form QA instances honestly carrying `matrix_hoeffding`
alone). QA 2918 → 2922 (+4, `EdgePerturbation_QA.lean`'s sweepWindow
section).**

**Changes:** (1) **The theorem**
(`Derived/EdgePerturbationTail.lean`'s NormalizedCheegerWindow
section): `edgePerturbation_fiedler_sweep_cut_tail` — at the bracket's
hypothesis stack plus the new floor-positivity guard
`0 < dmin·φ²/2 − t`, `μ {ω admissible ∧ ¬(connected G_ω ∧ ∃ swept S,
conductance² ≤ 2·(2·dmax·φ + t)/dmin)} ≤ 2 d exp(−t²/(2‖∑ₑ L_e²‖))`,
the swept existential exactly `fiedler_sweep_cut_normalized`'s return
shape on the resampled graph — the chain concentration → eigenvalue
window → connectivity → the spectral-partitioning sweep's cut, closed
under one statement, with three delivered families load-bearing (the
floor's positivity is the connectivity transfer's exact input, the
ceiling caps the sweep extraction, the bracket is the measure bound).
(2) **QA (+4)**: the raw-walk connectivity pin at the all-true `K₂`
outcome, the good-outcome witness (that outcome provably *not* in the
measured event — its swept cut from the deterministic theorem at the
pinned `λ₂(L_sym) = 2`, `conductance² ≤ 4` inside the window bound
`16.25`), and the closed-form K₂/P₃ tail instances at `t = 1/16`
(`4 exp(−1/4096)`, `6 exp(−1/6144)`). (3) **Records** — the
matrix-Hoeffding proposal (the sweep-cut follow-on delivery record with
the guard's design verdict and technique findings: the
positional-application trap with a trailing `Prop` argument after
postponed `(by norm_num)` slots — the named-argument form the fix —
and the stale-olen recurrence), `proposals/README.md` (the Delivered
row's sweep-cut clause), README (2922; one module-table clause), the
radar (QA axis synced, score held at 4.0 per protocol), the scoreboard
(verification row + interpretation bullet), the backlog (item 3's
capstone clause), the probability-concentration index map (the
theorem's row), the map stamps + regenerated SVG, the execution plan,
and this log.

**Verification:** spike first (`wip/sweepwin_spike.lean`, every piece
to zero errors/warnings before any shelf edit, the spike's own
`#print axioms` confirming the conditional structure pre-shelf);
`lake env lean` zero errors/zero warnings on both touched modules (the
QA module at its recorded pre-existing `Try this: ring_nf` baseline);
explicit `lake build` targets ✔ on `EdgePerturbationTail` (2227/2227)
and `EdgePerturbation_QA`; `#print axioms` exactly as designed (5
declarations); **full `lake build` ✔ (2405/2406) immediately followed
by `check_build_completeness.py` — 128 source files, 128 fresh
artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, both
findings allowlisted-confirmed), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated idempotent
(**2922/10/0**); **map freshness exit 0** after the stats-stamp sync
(2918 → 2922 in both map files; no proposal status header changed).

**Remaining risk:** none owed — the theorem is conditional on
`matrix_hoeffding` and must never be described as foundationally
proved. The guard's honesty note stands: the floor-positivity
hypothesis is proof-load-bearing (the connectivity transfer's input)
with no dropped-guard refutation fixture possible at fixture scale —
the recorded junk-measure obstruction, not an unexamined corner.

**Next handoff:** the Active table's only actionable row remains the
empirical-stationary Step 2, still gated on a consumer pricing the
bias-term shape; otherwise the next load-bearing gap
`docs/6_SGT_BACKLOG.md` names (all remaining items consumer-gated), or
a consumer that prices the swept cut's quality (none named yet).

## 2026-08-29T07:33:31Z — C₄ dropped-guard refutation of the sweep-cut tail's floor-positivity hypothesis in delivery

**Run:** `20260829T073300Z-run-1`  
**Session:** `ses_fb39dd959ffeDpxm8dikAP5jZR`  
**Status:** in-progress  
**Milestone:** the falsification-discipline milestone named by the
previous run's own honesty note ("no dropped-guard refutation fixture
exists at fixture scale … recorded for the next corner audit"):
delivery analysis found the note over-narrow — on C₄ at window `[1, 2]`
the perfect-matching outcomes are admissible-but-disconnected, and
their bad-set membership is t-invariant, so at large `t` the collapsed
tail bound drops below the atom mass and the un-guarded
`edgePerturbation_fiedler_sweep_cut_tail` statement is refuted in
proved arithmetic. Pure QA hard crust, zero new axioms.

**Changes (planned):** a new guard-fence section in
`Scaffold/QA/Derived/EdgePerturbation_QA.lean`: the C₄ fixture and its
hypothesis stack (symmetric, nonneg, degrees `2`), the matching
outcome's rescaled adjacency (two weight-`2` edges), admissibility at
`[1, 2]`, disconnectedness by the kernel route
(`exists_const_of_laplacian_mulVec_eq_zero` contrapositive at the
non-constant kernel vector `![1,1,0,0]`), the variance-norm bound
`‖∑ L_e²‖ ≤ 64` plus its positivity (the `(0,0)` entry pinned `= 4`),
the singleton atom mass `2⁻¹⁶`, and the headline negation at `t` large.
Records to follow: the proposal's honesty-note correction, README QA
count, radar QA axis, scoreboard, this plan, and the activity log.

**Verification (planned):** spike to zero errors/warnings before the
shelf edit; `lake env lean` on the QA module; explicit `lake build`
target; `#print axioms` on the new declarations (expect exactly
`propext, Classical.choice, Quot.sound` — the refutation proves a
negation and cannot consume the axiom-conditional theorem); full
`lake build` + `check_build_completeness.py`; `lint_axioms`,
`check_citations`, `check_markdown_links`; scoreboard regeneration and
map-freshness sync.

## 2026-08-29T08:11:22Z — C₄ dropped-guard refutation of the sweep-cut tail's floor-positivity guard delivered: the honesty note corrected on the record (terminal)

**Run:** `20260829T073300Z-run-1`  
**Session:** `ses_fb39dd959ffeDpxm8dikAP5jZR`  
**Status:** completed  
**Milestone (delivered):** the falsification-discipline milestone named
by the previous run's own honesty note ("no dropped-guard refutation
fixture exists at fixture scale … recorded for the next corner audit")
— **DELIVERED as zero new axioms (count stays 10; `#print axioms` on
all eight audited new declarations: exactly `propext,
Classical.choice, Quot.sound` — a refutation proves a negation and
cannot consume the axiom-conditional theorem). QA 2922 → 2951 (+29,
`EdgePerturbation_QA.lean`'s new guard-fence section).**

**Changes:** the headline `epC4_sweepWindow_unguarded_refuted_QA` —
the un-guarded conclusion of `edgePerturbation_fiedler_sweep_cut_tail`
refuted in proved arithmetic — plus its support stack: the C₄ fixture
(`epC4`, symmetric nonnegative, degrees all `2`), the matching outcome
`epC4ω` (edges `{0,1}`, `{2,3}` kept) with its rescaled adjacency
pinned entrywise through the design's off-diagonal formula
(`epC4_perturbed_eq`), admissibility at the hypothesis-loosened window
`[1, 2]` (`epC4ω_admissible`), disconnectedness by the kernel route
(`epC4ω_supportGraph_not_connected`: the component indicator
`![1,1,0,0]` a non-constant Laplacian-kernel vector — raw `epC4M_lap_mulVec`
against the contrapositive of `exists_const_of_laplacian_mulVec_eq_zero`),
the atom mass exactly `2⁻¹⁶` (`epC4ω_mass`), the variance statistic
bounded `‖∑ L_e²‖ ≤ 64` (`epC4_varNorm_le`: triangle +
submultiplicativity + `l2OpNorm_rankOne_le`) and pinned positive
(`epC4_varNorm_pos`: the `(0,0)` entry `= 8` by sixteen-way literal
enumeration). **The corrected claim**: the recorded obstruction
("at 2–3 vertices the tail bound exceeds `1`") had anchored on the
eigenvalue-floor membership route — t-monotone, evasive — and on
fixtures without admissible-disconnected outcomes; the
disconnectedness route is t-invariant, so at `t = 9000` the collapsed
bound `8/(1 + 9000²/128)` sits strictly below the atom mass
`1/65536`. The Derived theorem's docstring honesty note corrected in
place; the proposal carries the full record with the two technique
lessons (enumerate t-invariant structural membership routes; compare
against atom masses, not `1`) and the honest residue (the bracket's
un-windowed statement genuinely shrinks with `t` and remains
unfalsified; the normalized-Laplacian zero-degree junk-spectrum finding
stays parked).

**Verification:** spike first (`wip/c4fence_spike.lean`, iterated to
zero errors/warnings before any shelf edit, with the spike's own
`#print axioms` confirming the unconditional structure pre-shelf);
`lake env lean` zero errors/zero warnings on the QA module (its lone
`Try this: ring_nf` note verified pre-existing on the stashed
unmodified tree); explicit `lake build` targets ✔ on
`EdgePerturbation_QA` (2238/2238) and `EdgePerturbationTail`
(2227/2227, after the docstring-only correction); **full `lake build` ✔
immediately followed by `check_build_completeness.py` — after the
documented single-module mtime remediation (remove + rebuild once),
128 source files, 128 fresh artifacts, 0 stale, 0 missing, exit 0**;
`lint_axioms` (10, both findings allowlisted-confirmed),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(**2951/10/0**); **map freshness exit 0** after the stats-stamp sync
(2922 → 2951 in both map files, SVG regenerated; no proposal status
header changed).

**Remaining risk:** none owed by the delivery — the fence is
unconditional hard crust. The window family's conditional theorems
remain conditional on `matrix_hoeffding` and must never be described as
foundationally proved.

**Next handoff:** the Active table's only actionable row remains the
empirical-stationary Step 2, gated on a consumer pricing the bias-term
shape; otherwise the next load-bearing gap `docs/6_SGT_BACKLOG.md`
names (all consumer-gated), a consumer that prices the swept cut's
quality (none named), or the next falsification target the shelf's
honesty notes name — the audit pattern this run executed once.

## 2026-08-29T09:53:40Z — Degenerate-degree corner audit delivered: the parked junk-spectrum finding settled in proved form; both attacked honesty notes stand (terminal)

**Run:** `20260829T092750Z-run-1`  
**Session:** `ses_fb3359cafffedSVqHfQWT6erXC`  
**Status:** completed  
**Milestone (delivered):** the corner audit the standing handoff named
as its falsification-frontier residue ("the normalized Laplacian's
zero-degree junk spectrum (the identity's, not the zero matrix's)
remains recorded for a future corner audit if one is ever priced") —
**DELIVERED as zero new axioms (count stays 10; `#print axioms` via
`wip/degcorner_axcheck.lean` on all 15 audited declarations: exactly
`propext, Classical.choice, Quot.sound`). QA 2951 → 2963 (+12,
`EdgePerturbation_QA.lean`'s new cornerAudit section).**

**Changes:** the shelf lemmas — `Normalized.lean`'s new
degenerate-degree-corners section (`degreeInvSqrt_apply_eq_zero_iff`:
the reciprocal factor vanishes exactly at nonpositive degrees, both the
zero corner and the *negative* corner — the hitherto-unrecorded `p ≠ ½`
outcomes route; `normalizedLaplacian_eq_one_of_forall_deg_nonpos`: the
identity degeneration) — plus `Spectral.lean`'s `eigvalOf_one`/`evals_one`
(the sorted spectrum of the identity is `1` at every index, via the
eigenaction `1 *ᵥ v = v` against `eigvecOf_inner` and
`evals_mem_eigvalOf`). The QA audit: the all-false `p ≡ ½` outcome's
degrees `0` and normalized Laplacian `1` pinned, **the parked finding
pinned** (`λ₂(L_sym) = 1`), the easy misprediction refuted
(`λ₂ ≠ 0`), the spectral contrast as one proved statement
(`λ₂(L) = 0 ∧ λ₂(L_sym) = 1` at the same outcome), the honesty note's
floor-condition mechanism proved as a fixture instance (`1 ≤ 1/2`
fails), the negative corner at `p ≡ 1` (resampled adjacency
`= (-1) • K₂`, degrees `-1 < 0`, the same identity junk), and the
vanishing iff exercised on both sides. The Derived bracket's docstring
honesty note updated to point at the proved lemmas. The proposal
carries the full record including the two adversarial analyses the run
performed *before* selecting: the sharpened drift's `s = γ` corner
attacked (small-`p` variance collapse fails — the stated variance
proxy is the deterministic `‖∑ L_e²‖`, p-independent; weight scaling
fails — the exponent is scale-invariant and mixed weights only lower
it, capped ≈ 2/3 on hand fixtures vs. the needed `ln(2d)`) and the
window's dropped admissibility attacked (negative-adjacency outcomes
at legal `p ≠ ½` design points exist, but congruence inertia forces
`λ₂(L_sym) ≥ 1 > floor` at every outcome with at most one positive
resampled-adjacency eigendirection) — **both honesty notes survived
with their structural reasons now on record**, and those analyses
consumed the junk-prediction fact three times over, which is what
priced the audit.

**Verification:** spike first (`wip/degcorner_spike.lean`, iterated to
zero errors/warnings before any shelf edit, the spike's own
`#print axioms` at the standard three on all 16 declarations pre-shelf);
`lake env lean` zero errors on all touched modules
(`Spectral.lean`/`Normalized.lean` at warning sets verified identical
to the stashed unmodified tree — only line shifts; the QA module at its
recorded pre-existing `Try this: ring_nf` baseline; the Derived Tail
module re-elaborated after its docstring-only edit, exit 0); explicit
`lake build` targets ✔ on `Spectral`, `Normalized`,
`EdgePerturbationTail`, and `EdgePerturbation_QA`; `#print axioms`
exactly as designed (15 declarations); **full `lake build` ✔ (2405/2406)
immediately followed by `check_build_completeness.py` — 128 source
files, 128 fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms`
(10, both findings allowlisted-confirmed), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**2963/10/0**);
**map freshness exit 0** after the stats-stamp sync (2951 → 2963 in
both map files, SVG regenerated; no proposal status header changed).

**Remaining risk:** none owed by the delivery — the audit is
unconditional hard crust. The conditional theorems of the window
family remain conditional on `matrix_hoeffding` and must never be
described as foundationally proved.

**Next handoff:** the Active table's only actionable row remains the
empirical-stationary Step 2, still gated on a consumer pricing the
bias-term shape; otherwise the next load-bearing gap
`docs/6_SGT_BACKLOG.md` names (all remaining items consumer-gated), a
consumer that prices the swept cut's quality (none named), or a
genuinely new falsification target — the named fixture-scale targets
have now all been attacked, with their structural survival reasons on
record.

## 2026-08-29T11:07:30Z — hoeffding_inequality's first theorem consumer: vertex-degree concentration under edge resampling

**Run:** `20260829T110514Z-run-1`  
**Session:** `ses_fb2d80ab4ffeXYtA83FfUv8jRA`  
**Status:** in-progress  
**Milestone:** the scalar Hoeffding axiom's first theorem consumer —
the per-vertex degree-deviation tail
`μ {|deg (A + perturbWeight A p ω) v − deg A v| ≥ t}
≤ 2 exp(−t²/(2 ∑ₑ w_v(e)²))`
plus the all-vertices union bound, at the same centered Bernoulli
edge-resampling design the delivered window family lives on.
Selection context: no High rows; the Medium-High empirical-stationary
Step 2 row stays consumer-gated; backlog items all consumer-gated;
the previous run recorded the fixture-scale falsification frontier as
exhausted. Of the ten admitted axioms, four still have zero theorem
consumers outside their own files (`hoeffding_inequality`,
`bernstein_inequality`, `bernstein_bounded_variance`,
`hoeffding_lemma` — audited safe 2026-08-28 but never load-borne).
SGT leverage: the window family's honesty notes record that the λ₂
tail carries zero degree information (`L(E_ω)·1 = 0` identically) and
`perturbAdmissible`'s degree clauses are event-internal; the degree
tail is the missing complementary concentration, making
`hoeffding_inequality`'s exact clause structure load-bearing on a
graph-theoretic statement for the first time.

## 2026-08-29T11:53:00Z — Degree-concentration milestone delivered: hoeffding_inequality's first theorem consumer (terminal)

**Run:** `20260829T110514Z-run-1`  
**Session:** `ses_fb2d80ab4ffeXYtA83FfUv8jRA`  
**Status:** completed  
**Milestone (delivered):** the scalar Hoeffding axiom's first theorem
consumer — the per-vertex degree-deviation tail
`μ {|deg (A + perturbWeight A p ω) v − deg A v| ≥ t}
≤ 2 exp(−t²/(2 ∑ₑ w_v(e)²))`
plus the all-vertices union bound, at the same centered Bernoulli
edge-resampling design the delivered window family lives on —
**DELIVERED as zero new axioms (count stays 10; `#print axioms` via
`wip/degconc_axcheck.lean` on all 23 audited declarations: the seven
engine lemmas and twelve hard-crust QA lemmas exactly `propext,
Classical.choice, Quot.sound`; the two Derived tails and two
axiom-instantiating QA pins honestly carrying `hoeffding_inequality`
alone). QA 2963 → 2977 (+14, `EdgePerturbation_QA.lean`'s degreeTail
section).**

**Changes:** selection first audited the ten admitted axioms' consumer
landscape — four have zero theorem consumers outside their own files
(`hoeffding_inequality`, `bernstein_inequality`,
`bernstein_bounded_variance`, `hoeffding_lemma`; audited safe
2026-08-28 but never load-bearing) — and picked the first, at the
design where the shelf's newest family (the irregular Cheeger window)
records its own missing half: the honesty notes say the λ₂/norm tails
carry zero degree information (`L(E_ω)·1 = 0` identically) and
`perturbAdmissible`'s degree clauses are event-internal hypotheses.
The delivery: `Spectral.lean`'s degree-linearity package
(`deg_add`/`deg_sum`), `EdgePerturbation.lean`'s section 5 (the
`degPerturbWeight`/`degPerturbSummand` design, the deviation identity
`deg_resampled`, and all four `hoeffding_inequality` clauses proved at
the design — sign-free, no hypothesis on the weight matrix; the
centering through `integral_delta` with no `p ≠ 0` guard),
`Derived/EdgePerturbationTail.lean`'s degreeTail section (the
per-vertex tail with the established `Fin n` transport, and the union
bound at the exact per-vertex sum), and the QA section (variance
statistic exact with the single-counted value refuted; the identity by
two independent routes at all-true and joined to the corner audit at
all-false; closed-form instances `2 exp(−1/4)` / union `4 exp(−1/4)`;
and the **exact event measure `1/2`** computed through the design's own
independence machinery, `indepFun_coord` + `toMeasure_cyl`,
independently of the tail theorem — the bound's fixture-scale slack on
the record, the same junk-measure obstruction the window family
records). New proposal
`proposals/hoeffding-inequality-degree-concentration.md` created and
delivered in one run, with the technique findings (`simp only` for
∀-hypothesis rewrites under binders; explicit `(f := …) (g := …)` for
`integral_sub`; the `smul`-spelling route around the pin's missing real
`integral_mul_const`; the `((0, 1) : Fin 2 × Fin 2)` parenthesization
trap) and two priced follow-ons: the admissibility dissolution (union
with the window bracket + the `p e + p eᵀ ≤ 1` nonnegativity design
condition) and the Bernstein twin (the variance-adaptive degree tail,
the second zero-consumer scalar axiom's consumer).

**Verification:** spike first (`wip/degconc_spike.lean`, every piece —
design, clause set, both tails, the full QA section — at zero errors
before any shelf edit); `lake env lean` zero errors on all four touched
modules (the QA module at three `Try this: ring_nf` notes: one
pre-existing baseline plus two cosmetic additions, recorded);
explicit `lake build` targets ✔ on `Spectral`, `EdgePerturbation`,
`EdgePerturbationTail`, `EdgePerturbation_QA`; `#print axioms` exactly
as designed (23 declarations); **full `lake build` ✔ (2405/2406)
immediately followed by `check_build_completeness.py` — after the
documented single-module mtime remediation (remove + rebuild once)
for the Derived module, whose header docstring was edited after the
full build, with the full ladder re-run green at the final tree —
128 source files, 128 fresh artifacts, 0 stale, 0 missing, exit 0**;
`lint_axioms` (10, both findings allowlisted-confirmed),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(**2977/10/0**); **map freshness exit 0** after the stats-stamp sync
(2963 → 2977 in both map files, SVG regenerated; no proposal status
header changed).

**Remaining risk:** none owed by the delivery — the engine and QA are
unconditional hard crust. The two new Derived tails are conditional on
`hoeffding_inequality` and must never be described as foundationally
proved. The three sibling axioms (`bernstein_inequality`,
`bernstein_bounded_variance`, `hoeffding_lemma`) remain zero-consumer;
the Bernstein twin follow-on would close the second.

**Next handoff:** the Active table's only actionable row remains the
empirical-stationary Step 2, gated on a consumer pricing the bias-term
shape; otherwise the admissibility dissolution or the Bernstein twin
(both priced, both now unblocked by this delivery's clause machinery),
or the next load-bearing gap `docs/6_SGT_BACKLOG.md` names (all
remaining items consumer-gated).

## 2026-08-29T12:58:27Z — The Bernstein twin: the variance-adaptive degree tail (two more zero-consumer axioms made load-bearing)

**Run:** `20260829T125827Z-run-1`  
**Session:** `ses_fb268ccb1ffeFUBGi00H8luzlR`  
**Status:** in-progress  
**Milestone:** Deliver `bernstein_inequality`'s first theorem consumer (and `bernstein_bounded_variance`'s, by a budget corollary): the per-vertex degree-deviation tail with the variance-adaptive denominator `2σ²_v + 2Mt/3` at `σ²_v = ∑ₑ w_v(e)² p_e(1−p_e)`, on the same centered Bernoulli edge-resampling design as the delivered Hoeffding twin — the standing handoff's top priced follow-on, unblocked by that delivery's clause machinery, closing the zero-consumer gap for two of the three remaining axioms.

**Changes (planned):** `BernoulliProduct.lean`'s second-moment companion of `integral_delta` (`∫ (δ_e − p_e)² = p_e(1 − p_e)`); `EdgePerturbation.lean`'s design instantiation (`∫ X_e² = w_v(e)² p_e(1−p_e)`); `EdgePerturbationTail.lean`'s bernsteinTwin section (the exact-statistic tail via `bernstein_inequality`, the budget tail via `bernstein_bounded_variance`); QA pins (the statistic exactly `1/2` on K₂ at the fair coin with the Poisson-shaped `1` refuted; the strict Bernstein-beats-Hoeffding improvement `2 exp(−3/5) < 2 exp(−1/4)`; closed-form conditional instances). Spike first in `wip/`; degenerate-corner analysis recorded pre-statement (prefactor constant `2`, `t = 0` safe through `zero_div`, empty-`V` vacuous).

## 2026-08-29T13:21:18Z — The Bernstein twin delivered: two more zero-consumer axioms made load-bearing, with the variance-adaptivity improvement itself a proved theorem

**Run:** `20260829T125827Z-run-1`  
**Session:** `ses_fb268ccb1ffeFUBGi00H8luzlR`  
**Status:** completed  
**Milestone:** `bernstein_inequality`'s and `bernstein_bounded_variance`'s first theorem consumers — the variance-adaptive per-vertex degree tails at the same centered Bernoulli edge-resampling design — the standing handoff's top priced follow-on, closing the zero-consumer gap for two of the three remaining axioms.

**Changes:** `BernoulliProduct.lean`: the second-moment companion `integral_sq_delta_sub` (`∫ (δ_e − p_e)² = p e (1 − p e)`, beside `integral_delta`). `EdgePerturbation.lean` section 5: the design instantiation `integral_sq_degPerturbSummand` (`∫ X_e² = w_v(e)² p e (1 − p e)`) plus module-docstring updates. `Derived/EdgePerturbationTail.lean`: the new bernsteinTwin section — `edgePerturbation_degree_tail_bernstein` (`μ {|deg dev| ≥ t} ≤ 2 exp(−t²/(2 σ²_v + 2Mt/3))` at the true variance statistic `σ²_v = ∑ₑ w_v(e)² p e (1 − p e)`, magnitude budget `M ≥ |w_v(e)|`, `0 ≤ M` derived at the incident pair) and `edgePerturbation_degree_tail_bernstein_budget` (any `σ²_v ≤ Vbud`), each conditional on its own axiom alone. QA +10 (2977 → 2987, the bernsteinTwin section): the true statistic pinned (`σ²₀ = ½` on K₂ at the fair coin) with the Poisson-trial shape (`∑ w² p = 1`) refuted; the fourfold variance reduction as an equation (`σ²₀ = S₀/4`); the engine integral at an incident pair (`¼`); `M = 1` at the fixture; the **strict variance-adaptivity improvement proved** (`epK2_bernstein_beats_hoeffding`: `2 exp(−3/5) < 2 exp(−1/4)`, hard crust — the cross-axiom coherence check); the budget relaxation pinned honest; the two closed-form conditional instances. Degenerate-corner analysis recorded pre-statement (prefactor constant `2`; `t = 0` safe through `zero_div`; empty `V` vacuous in `v`). Records: the proposal's follow-on delivery record (with technique findings), `proposals/README.md`'s Delivered-row clause, README (2987; highlights; module table), the radar (QA axis synced, 4.0 held per protocol), the scoreboard (verification rows + interpretation bullet), both index maps, both map stamps + regenerated SVG, the execution plan, this entry.

**Verification:** spike first (`wip/berntwin_spike.lean`, everything to zero errors/warnings pre-shelf); `lake env lean` zero errors on all four touched modules (QA at its recorded three-note `ring_nf` baseline — this delivery's `norm_num` calls add none, verified against the stashed pre-delivery tree); explicit `lake build` targets ✔ on `BernoulliProduct`, `EdgePerturbation`, `EdgePerturbationTail`, `EdgePerturbation_QA`; `#print axioms` via `wip/berntwin_axcheck.lean` exactly as designed (14 declarations: engine + hard-crust QA at the standard three; each tail/pin on its own axiom alone); **full `lake build` ✔ (2403/2406) immediately followed by `check_build_completeness.py` — after the documented mtime remediation (a stash-cycle touched five source mtimes; remove artifact + rebuild once), 128 sources, 128 fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, both findings allowlisted-confirmed, exit 0), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**2987/10/0**, idempotent); **map freshness exit 0** after the stats-stamp sync (no proposal status header changed).

**Remaining risk:** none owed — engine and QA are unconditional hard crust; the two Derived tails are conditional on their own axiom and must never be described as foundationally proved. Only `hoeffding_lemma` remains zero-consumer (its natural consumer is `bernstein_inequality`'s own proof — upstream work). The sole priced follow-on: the admissibility dissolution, now with both degree tails as candidate engines (the Bernstein one strictly sharper at interior `p`).

**Next handoff:** the Active table's only actionable row remains the empirical-stationary Step 2, gated on a consumer pricing the bias-term shape; otherwise the admissibility dissolution (priced, unblocked), or the next load-bearing gap `docs/6_SGT_BACKLOG.md` names (all remaining items consumer-gated).

## 2026-08-29T17:33:40Z — The pairwise-independence audit: six concentration axioms carry a false hypothesis shape

**Run:** `20260829T173340Z-run-1`  
**Session:** `ses_fb17db359ffe9YX8gfLEglYVtE`  
**Status:** in-progress  
**Milestone:** priority item 4 (reduce the explicit trust surface), selected
per priority item 0 (no High rows; the Medium-High empirical-stationary
Step 2 row consumer-gated; all Low rows human-decision-gated): a Step-0
audit found that all six independence-carrying concentration axioms
(`hoeffding_inequality`, `hoeffding_empirical`, `bernstein_inequality`,
`bernstein_bounded_variance`, `matrix_hoeffding`, `matrix_bernstein`;
Azuma's `MatrixMDS` is a genuine martingale shape, unaffected)
hypothesize only pairwise `IndepFun` — and pairwise independence does
not suffice for Hoeffding/Chernoff: the 15 Walsh characters of the fair
BernoulliProduct on `Fin 4 → Bool` are pairwise independent with sum 15
on the all-false atom (mass 1/16) and −1 elsewhere, refuting each
axiom's tail bound at `t = 15` by a factor ≫ 1 with numerics needing
only `e ≥ 2`. Deliverable: the refutation fixtures in QA, the in-place
repair (pairwise clause → `iIndepFun`), the `iIndepFun_coord` /
`iIndepFun_coord_matrix` engine in BernoullilliProduct (cylinder-mass
generalization of the delivered `sum_coord2_mul` route), full consumer
threading (designs are genuinely mutually independent — public Derived
statements unchanged), and records. Zero new axioms (count stays 10;
six repaired in place).

**Changes (planned):** `Scaffold/Mathlib/Probability/BernoulliProduct.lean`
(iIndep machinery), `IIDProduct.lean`, the four Scalar + two Matrix
concentration axiom files, `EdgePerturbation.lean`,
`EdgePerturbationTail.lean`, `SparsificationTail.lean`,
QA files (`Scalar_QA.lean` refutation family + re-instantiations,
`Matrix_QA.lean`, `EmpiricalStationary_QA.lean`,
`SparsificationTail_QA.lean`, `EdgePerturbation_QA.lean` pins), a new
proposal, and the status records.

**Verification (planned):** spike to zero errors before any shelf edit;
`lake env lean` on all touched modules; explicit `lake build` targets;
`#print axioms` on the repaired axioms' consumers; full `lake build` +
`check_build_completeness.py`; `lint_axioms` (allowlist decisions for
any new axiom signature shapes — repairs keep existing guards),
`check_citations`, `check_markdown_links`; scoreboard regeneration;
map-freshness sync if any proposal status header changes.

## 2026-08-29T19:56:11Z — Continuing the pairwise-independence repair: threading the remaining consumers and building the refutation fixtures

**Run:** `20260829T195611Z-run-1`  
**Session:** `ses_fb0f2f880ffe4AHeHedI2WzxDA`  
**Status:** in-progress  
**Milestone:** continuation of the active pairwise-independence audit
and repair (run `20260829T173340Z-run-1` repaired the six axiom
signatures in place and threaded the BernoulliProduct and
EdgePerturbation chains; the tree does not build as it stands). This
run: (1) restore build reachability — IIDProduct's `iIndepFun`
coordinate machinery (the `iidPMF` analogue of the delivered
BernoulliProduct engine), EmpiricalStationary + Sparsification
consumer threading, and the zero-family QA re-instantiations
(Scalar_QA, Matrix_QA, EmpiricalStationary_QA) that still pass the
dead pairwise clause; (2) the Walsh-family refutation fixtures in QA
(the falsification content justifying the repair): the 15 nontrivial
characters of the fair BernoulliProduct on `Fin 4 → Bool`, their
pairwise independence and zero means (flip-involution), the sum value
15/−1, and the six hypothesis-form refutations of the pre-repair
shapes; (3) the proposal and status records. Zero new axioms (count
stays 10; six repaired in place, consumers' public statements
unchanged).

**Changes (planned):** `Scaffold/Mathlib/Probability/IIDProduct.lean`
(iIndep engine), `Scaffold/Derived/EmpiricalStationary.lean`,
`Scaffold/Mathlib/GraphTheory/Sparsification.lean`
(`iIndepFun_ssSummand`), `Scaffold/Derived/SparsificationTail.lean`,
QA re-instantiations, a new
`Scaffold/QA/Concentration/PairwiseIndependence_QA.lean`, a new
proposal, and the status records.

**Verification (planned):** spike to zero errors before shelf edits;
`lake env lean` on touched modules; explicit `lake build` targets;
`#print axioms` on the repaired axioms' consumers; full `lake build` +
`check_build_completeness.py`; `lint_axioms`, `check_citations`,
`check_markdown_links`; scoreboard regeneration; map-freshness sync.

## 2026-08-29T22:24:14Z — Completing the pairwise-independence repair: verification restored, records closed

**Run:** `20260829T222414Z-run-1`  
**Session:** `ses_fb06adbf6ffeS2fmzA1T2Vw5Iu`  
**Status:** in-progress  
**Milestone:** completion of the active pairwise-independence repair (runs `20260829T173340Z-run-1`, `20260829T195611Z-run-1`): the interrupted prior run left the tree mid-threading with the records claiming more than the tree delivered. This run: (1) re-verify every claim independently — the six repaired axioms, the BernoulliProduct/IIDProduct `iIndepFun` engines, all consumer threadings, and the Walsh refutation family; (2) finish what the interruption left open — the new QA file carried linter warnings/deprecation notes (cleaned to zero output), the map stats stamps were still 3008 (synced to 3099, SVG regenerated), Errata §6 still recorded the repair as open/in-progress; (3) close every record: Errata §6, the `proposals/README.md` Delivered row, README/radar counts, the execution plan, and the terminal activity entry.

**Changes (planned):** `Scaffold/QA/Concentration/PairwiseIndependence_QA.lean` (warning cleanup only — six linter notes, one deprecation pair, one positionless `Try this: ring_nf` traced by bisection to a `ring` call and replaced by `ring_nf`), `docs/9_ERRATA.md` (§6 closed), `proposals/README.md` (Delivered row), `README.md`, `docs/7_SGT_RADAR.md` (count syncs), `scripts/generate_scaffold_map_svg.py` + `docs/scaffold_map.html` (stats stamps), `docs/EXECUTION_PLAN.md`, this file.

**Verification (planned):** full `lake build` + `check_build_completeness.py` (129/129); `#print axioms` on the six refutations, the nine engines, and the eight Derived consumers (each on its own axiom alone); `lint_axioms`, `check_citations`, `check_markdown_links`; scoreboard idempotence; map freshness exit 0.

## 2026-08-29T22:27:50Z — Pairwise-independence repair completed and verified

**Run:** `20260829T222414Z-run-1`  
**Session:** `ses_fb06adbf6ffeS2fmzA1T2Vw5Iu`  
**Status:** completed  
**Milestone:** the active pairwise-independence repair (runs `20260829T173340Z-run-1`, `20260829T195611Z-run-1`) — six of the ten admitted concentration axioms had pairwise-only `IndepFun` hypothesis clauses, materially false per the Walsh-character counterexample (Errata §6) — brought to a fully verified, fully recorded close.

**Changes:** `Scaffold/QA/Concentration/PairwiseIndependence_QA.lean` (linter cleanup only: six unused-binder notes, two deprecated `div_lt_iff`/`lt_div_iff` → `…₀`, one unnecessary-seq-focus pair, one positionless `Try this: ring_nf` located by bisection — a `ring` call in `ofReal_le_refl` — and replaced by `ring_nf`; the file now elaborates with zero output); `wip/pairwise3_axcheck.lean` (the consumer/engine axiom audit, extending the interrupted run's refutation audit); records — `docs/9_ERRATA.md` §6 resolved, `proposals/README.md`'s Delivered row, the proposal's status header (third-run clause), `README.md` (3099), `docs/7_SGT_RADAR.md` (QA axis 3099/67 modules; axis 7's second axiom-consistency-repair clause), `docs/5_QA_SCOREBOARD.md` (verification row), `index/map/probability_concentration.md` (repair annotations on all six axiom rows + the new `iIndepFun` engine rows), `scripts/generate_scaffold_map_svg.py` + `docs/scaffold_map.html` (stats stamps 3008 → 3099, SVG regenerated), `docs/EXECUTION_PLAN.md` (queue emptied, delivered record).

**Verification:** every interrupted-run claim re-checked independently before any record edit: explicit `lake build` targets ✔ on all touched modules; `#print axioms` via `wip/pairwise2_axcheck.lean` (six refutations: exactly `propext, Classical.choice, Quot.sound`) and `wip/pairwise3_axcheck.lean` (nine engines hard-crust; the eight Derived consumers each conditional on its own axiom alone — `matrix_hoeffding` ×2, `hoeffding_inequality`, `bernstein_inequality`, `matrix_bernstein` ×2, `hoeffding_empirical` ×2); **full `lake build` ✔ immediately followed by `check_build_completeness.py` — first pass flagged the QA file's own stale artifact after the linter cleanup (my edit), remediated by the documented remove-and-rebuild, final 129 source files, 129 fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, both findings allowlisted-confirmed), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**3099/10/0**, idempotent across two runs, hand verification row preserved); **map freshness exit 0** (45 stations, no proposal status header changed).

**Remaining risk:** the six axioms remain admitted — the repair fixes the hypothesis *shape*; truth stays with the cited literature, and the Derived tails remain conditional on their own axioms. The whole delivery (this milestone's three runs) sits uncommitted in the worktree; the Errata §6 commit reference lands with the operator's commit per `docs/arch/commit-steward-protocol.md`.

**Next handoff:** the queue is empty — check `proposals/README.md`'s Active table first (no High rows; the Medium-High empirical-stationary Step 2 is consumer-gated on the bias-term shape); otherwise the center-out policy. `hoeffding_lemma` remains the one zero-consumer axiom (its natural consumer is `bernstein_inequality`'s own proof — upstream work).
