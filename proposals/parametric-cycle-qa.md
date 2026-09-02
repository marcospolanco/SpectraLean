# Proposal: Parametric (Arbitrary-Scale) QA for the Cycle Family

**Status:** COMPLETE — proposed and delivered in the same run
(`20260902T161908Z-run-1`, session
`ses_f9d153357ffe8wg52HLdL6e7ge`). QA-only, zero axiom contact:
`#print axioms` via `wip/paramqa_axcheck.lean` on all 17 audited
declarations (the 10 public pins + the 7 consumed shelf theorems
re-checked; the 4 private calculators audited transitively — every
public pin reads exactly the standard three, which subsumes them)
reads exactly `[propext, Classical.choice, Quot.sound]`. QA
3738 → 3748 (+10; the scoreboard counts public declarations, so the
4 private calculators are not in the count). Radar QA axis re-scored
4.0 → 4.5 per the "named absent category gains its first occupant"
protocol — the parametric half of the axis's named gap closed, the
randomized half recorded as still absent. See the delivery record at
the end of this file.

Companion to [Strategy](../docs/1_STRATEGY.md) (the
load-bearing-growth principle this applies), to
[cycle-family-alon-boppana-asymptotic.md](cycle-family-alon-boppana-asymptotic.md)
(the delivery whose own record concedes the gap this closes), and to
the radar's QA axis (`docs/7_SGT_RADAR.md` — the named remainder
"parametric property QA" that every score-hold since 2026-08-22
cites).

---

## Clean-room boundary

This planning document is internal prioritization and analysis. If
counsel approves a public repository export, restate the technical
specifications independently from standard textbook sources (cycle
distances, BFS level classes, and tree-ball cardinalities on cycles
are elementary; see Sources below). Do not copy this proposal
verbatim.

## The obligation this discharges

The QA axis's score has been held at 4.0 through every sync since
2026-08-22 with the same recorded reason: the named gap
"parametric property QA" (originally "parametric property QA and
eigenvalue pinning beyond two-point fixtures"; the eigenvalue half
closed with the C₄–C₁₂ spectral pins, the parametric half never).
The cycle-family delivery (`20260902T021120Z-run-1`) made the
*theorems* parametric — `cycleAdj_dist_eq`, `cycle_levE_eq`,
`cycle_levClass_eq`, `isTreeBall_cycle`, `cycleAdj_distEdge_gt`,
`alonBoppana_cycle`, `alonBoppana_cycle_asymptotic` all quantify over
the scale — but its own delivery record states the residual plainly:
*"these QA witnesses themselves remain fixed-`n`, so the axis's full
parametric-QA gap is narrowed, not closed."*

This proposal closes the parametric half: a QA section whose lemmas
are themselves `∀ n`/`∀ k`/`∀ m`, consuming the shelf theorems at
symbolic scale.

## Why this is load-bearing (the falsifiability case)

Every existing QA pin in the repository instantiates a theorem at a
*literal* fixture. A parametric statement with a scale-dependent
error — an off-by-one that only bites when the antipodal tie `2m = n`
occurs, a level-class boundary mishandled exactly at `2(j+1) = n`, a
wraparound branch wrong only for offsets past the midpoint — passes
every fixed fixture up to some size and fails beyond it. The largest
cycle fixture ever pinned is `C₁₂`; nothing in the repository would
notice if `cycleAdj_dist_eq` were wrong on `C₁₄` and up. Symbolic-QA
lemmas fail at *every* scale at once: they are the only QA shape
whose success is contingent on the parametric statement being exactly
right at arbitrary `n`, which is `1_STRATEGY.md`'s
load-bearing-growth principle applied to the QA layer itself.

## The witnesses (statement design, recorded before stating)

All consume the shelf theorems (never re-derive what the shelf
proves); arithmetic is `omega`-level after the theorem rewrite.

1. **The translate-invariant edge pin, every scale:**
   `∀ n ≥ 2, ∀ a : Fin n, dist a (a+1) = 1`. Consumes
   `cycleAdj_dist_eq` at the offset-1 branch. A wrong min-branch or
   wraparound term fails at every scale simultaneously.

2. **The short-branch pin with the antipodal tie included, symbolic
   base and scale:** `∀ n ≥ 2, ∀ m, 2m ≤ n → ∀ a,
   dist a (a + ⟨m⟩) = m`. Both branches of the min agree at the tie
   `2m = n` — the tie is *in* the hypothesis set, so a
   strict-inequality error in the formula's branch selection fails
   here.

3. **The family's own antipode at the exact tie:**
   `∀ k, dist (0 : Fin (4k+8)) ⟨2k+4⟩ = 2k+4` — the `C_{4k+8}`
   family's antipode is exactly the tie case, symbolic `k`.

4. **The exact far-apart value:**
   `∀ k, distEdge (C_{4k+8}) 0 1 (2k+4) (2k+5) = 2k+3`. The shelf
   theorem `cycleAdj_distEdge_gt` certifies only `2k+2 < distEdge`;
   this pins the exact value — the strictness slack is exactly `1`,
   witnessed at every scale (the same slack class as the display-form
   witnesses of recent QA).

5. **The tree-ball truth boundary, bracketed at every scale (the
   section's centerpiece):**
   - `∀ m ≥ 2, IsTreeBall (cycleAdj (2m)) 0 1 2 m` — the tree-ball
     predicate *holds* at radius `n/2`, **one past the radius the
     shelf theorem certifies** (`isTreeBall_cycle` needs
     `2(k+1) < n`, which maxes out at radius `n/2 − 1` on even
     cycles). The boundary level class is computed raw from
     `cycle_levE_eq` — exactly where `cycle_levClass_eq`'s strict
     hypothesis `2(j+1) < n` refuses to apply. This witnesses that
     the shelf's strictness is proof-forced, not truth-forced: the
     honest-scope pin.
   - `∀ m ≥ 2, ¬ IsTreeBall (cycleAdj (2m)) 0 1 2 (m+1)` — one past
     the truth: the level-`m` class is empty at every scale (the two
     offset branches overshoot each other). Together the pair
     brackets the truth (`radius ≤ n/2` on the even family) at
     arbitrary scale.
   - **The even-boundary class itself pinned:**
     `∀ j ≥ 1, levClass (cycleAdj (2(j+1))) 0 1 j = {⟨j+1⟩, ⟨j+2⟩}` —
     card `2`, the *adjacent antipodal pair*, not a singleton. This
     corrects the cycle-family delivery record's boundary note, which
     described the level-`k` class at `n = 2(k+1)` as "the single
     antipodal vertex": on the *even* boundary the class keeps two
     (adjacent) vertices; the singleton is the *odd* boundary —
   - **The odd-cycle singleton boundary:**
     `∀ j ≥ 1, levClass (cycleAdj (2j+1)) 0 1 j = {⟨j+1⟩}` and
     `¬ IsTreeBall (cycleAdj (2j+1)) 0 1 2 (j+1)` — where the two
     offset branches genuinely merge (`j+1 = n−j` iff `n = 2j+1`),
     card drops to `1 < 2`, and the tree-ball predicate fails: the
     genuine strictness bite, at every scale.

6. **The asymptotic witness pinned explicitly, symbolic `ε`:**
   `∀ ε > 0, λ₂(L(C_{4⌈1/ε⌉+8})) ≤ ε`. The shelf corollary's `∃ k`
   is opaque; this pins the witness the shelf proof actually
   produces (`k = ⌈1/ε⌉`) and re-certifies the ceiling arithmetic
   (`1/(k+1) ≤ ε`) at symbolic `ε` — the parametric consumption of
   `alonBoppana_cycle_laplacian`.

### Corner analysis (Step-0 discipline, per §5 of the architecture)

- `n = 2` corners are excluded where `cycleGraph 2` semantics could
  intrude (`2 ≤ n` kept where the shelf theorems carry it; the
  boundary lemmas require `j ≥ 1`, i.e. `n ≥ 4` even / `n ≥ 3`
  odd).
- Truncated subtraction: the boundary class is stated at `2(j+1)`
  and `2j+1` spellings to avoid `m − 1` corners.
- Witness 6 at large `ε` (`ε ≥ 1`): `⌈1/ε⌉ ≥ 1`, the bound
  `1/(k+1) ≤ 1 ≤ ε` still holds — no corner.
- No `Measure`, no `Fintype`-carried axiom hypothesis set, no
  `sorry`/`admit` (QA contract); no `-- @refutes` tags (nothing
  refutes an axiom here).

## Scope and non-goals

- QA-only: no shelf declaration changes; the shelf's strict
  hypotheses stay exactly as delivered (the boundary pins witness
  their slack honestly rather than tightening them — tightening
  `isTreeBall_cycle` to `2(k+1) ≤ n` would be a real shelf change
  with real consumers to re-verify, deliberately not bundled here).
- The *randomized* half of the QA axis's named gap
  ("parametric/randomized QA") remains absent and is recorded as
  such — no randomization machinery for QA exists in the repository.
- The exact `C_n` spectrum pins stay consumer-gated follow-ons, as
  the cycle-family delivery recorded.

## QA plan (this *is* the QA)

One section, `Step 8`, appended to
`Scaffold/QA/SpectralGraph/AlonBoppana_QA.lean`: the seven witness
groups above (≈ 10 public lemmas plus private symbolic-offset
helpers in the file's established `dist12`-calculator idiom).
Expected count +10–14 QA declarations.

## Sources

The witnesses pin the repository's own delivered theorems
(`Scaffold/Mathlib/GraphTheory/AlonBoppana.lean`, the CycleFamily
section) against elementary cycle geometry: graph distance on the
cycle `C_n` is `min(δ, n − δ)` at cyclic offset `δ`; BFS levels
around an edge; the two-branch structure of level classes. Standard
references for the underlying Alon–Boppana program are recorded on
the shelf declarations (`proposals/alon-boppana-bound.md`).

---

## Delivery record (2026-09-02, `20260902T161908Z-run-1`)

DELIVERED as proposed — QA-only, no shelf changes, all eight witness
groups landed as `AlonBoppana_QA.lean`'s `Step8` section (10 public
pins + 4 private symbolic-offset calculators; the scoreboard metric
counts the 10).

The witnesses, as landed:

1. `cycn_dist_short_QA` — `dist a (a + ⟨m⟩) = m` at `2m ≤ n`,
   symbolic in scale, offset, and translate; the antipodal tie `2m = n`
   inside the hypothesis set.
2. `cycn_dist_edge_QA` — `dist a (a + 1) = 1` at every scale ≥ 2 and
   every translate.
3. `cycfam_antipode_dist_QA` — the `C_{4k+8}` family's own antipode at
   the exact tie, every scale `k`.
4. `cycfam_distEdge_exact_QA` — `distEdge = 2k+3` exactly at every
   scale (the shelf's `cycleAdj_distEdge_gt` certifies only
   `2k+2 <`; the strictness slack is exactly `1`, witnessed at every
   scale).
5. `cycn_levClass_half_boundary_QA` — the even boundary class is the
   adjacent antipodal pair `{m, m+1}`, card `2`, computed raw from
   `cycle_levE_eq` at exactly the radius where `cycle_levClass_eq`'s
   hypothesis `2(j+1) < n` reads `2m < 2m` and refuses.
6. `cycn_isTreeBall_half_QA` — `IsTreeBall` **holds** at radius
   `n/2`, one past the shelf theorem's certified radius (which maxes
   at `n/2 − 1` on even cycles): the strictness is proof-forced, not
   truth-forced.
7. `cycn_not_isTreeBall_half_succ_QA` — fails one past the truth
   (the empty boundary class); with 6 this brackets
   `radius ≤ n/2` at arbitrary scale.
8. `cycn_levClass_odd_singleton_QA` + `cycn_not_isTreeBall_odd_QA` —
   the odd boundary `n = 2j+1` where the two offset branches merge,
   card drops to `1`, the predicate fails: the genuine strictness
   bite.
9. `cycfam_asymptotic_witness_QA` — the asymptotic corollary's
   witness pinned explicitly at symbolic `ε` (`k = ⌈1/ε⌉` certifies
   `λ₂ ≤ ε` through `alonBoppana_cycle_laplacian`).

The boundary correction this establishes: the cycle-family delivery
record described the level-`k` class at `n = 2(k+1)` as "the single
antipodal vertex" — on the *even* boundary the class is a pair
(witness 5, `C₄`: `{2, 3}`); the singleton is the *odd* boundary
(witness 8). The shelf theorems are untouched — their strict
hypotheses stay as delivered, now with their exact truth boundary
witnessed at every scale instead of guessed at one.

### Verification

Spiked in `wip/paramqa_spike.lean` to zero errors/zero warnings
before any shelf edit (including the `#print axioms` audit); the
landed `AlonBoppana_QA.lean` elaborates directly with zero errors/
zero warnings; explicit `lake build` target ✔; `#print axioms` via
`wip/paramqa_axcheck.lean` on 17 audited declarations — every one
exactly `propext, Classical.choice, Quot.sound`; full `lake build` ✔
immediately followed by `check_build_completeness.py` (133 source
files, 133 fresh artifacts, 0 stale, 0 missing, exit 0);
`lint_axioms` exit 0 (4 current axioms, unchanged);
`check_refutation_independence` (9-tag clean — no tags touched);
`check_public_reachability` clean (63 repo modules); `check_citations`,
`check_markdown_links`, `check_backlog_freshness` pass; scoreboard
regenerated (3748/4/0); map-freshness exit 0 after the 3738 → 3748
stats sync in both map files and SVG regeneration.

### Technique findings (recorded for future runs)

- **The `rcases` second-branch identifier trap** (the spike's only
  real logic bug, silent until elaboration): after
  `rcases Nat.eq_zero_or_pos z.val with h0 | hpos`, the second branch
  must use `if_neg (by omega : ¬(z.val = 0))` — writing
  `if_neg h0` references the *first* branch's binder and elaborates
  as "unknown identifier" only at the use site, since `h0` is not in
  the second branch's context. The shelf's own `if_neg (by omega …)`
  idiom (`cycle_levE_eq`'s proof) is load-bearing style, not
  verbosity; "simplifying" it is a bug.
- **`Fin` numeral instances in statements**: `(⟨0, _⟩ + 1 : Fin n)`
  needs `[NeZero n]` *in the signature* — a `haveI` inside the proof
  is too late for statement elaboration. The pins that state the base
  edge as `+ 1` carry the instance binder (the same convention as
  the shelf's `cycle_levE_eq`).
- **`Fin.val_one` is not a reliable `rw` on OfNat-shaped terms**: on
  `(1 : Fin n).val` as it appears after `Fin.add_def` unfolding, the
  lemma does not fire (the term is `Fin.val ⟨1 % n, _⟩`-shaped after
  instance unfolding). The robust route is a `show`-defeq to
  `1 % n` (`Fin.val_one'` is `rfl`) plus `Nat.mod_eq_of_lt`.
- **Symbolic-modulus arithmetic**: `omega` cannot evaluate `%` with a
  symbolic modulus; the offset calculators need explicit
  `Nat.mod_add_mod` / `Nat.add_comm` / `Nat.add_mod_right` /
  `Nat.mod_eq_of_lt` chains (four lemmas per calculator, then
  `omega` finishes the linear residue).
- **Rewriting a `+ 1` numeral through a large goal can time out at
  default heartbeats** (`isDefEq` on the instance path); the fix that
  worked is rewriting through a small dedicated bridge lemma
  (`pqa_add_one : ⟨0⟩ + 1 = ⟨1⟩`) applied at a small goal, plus
  `set_option maxHeartbeats 4000000 in` on the one theorem that
  needed it (the shelf's `alonBoppana_cycle` carries the same bump).
- **The scoreboard's declaration metric counts public declarations
  only** — private helpers (`pqa_*`) do not appear in the count; the
  delivery is +10, not +14.
