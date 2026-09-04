# The Effective-Resistance Core Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-04 by run `20260904T095642Z-run-1`,
session `ses_f942c6402fferk1SnBIjy3mNzf`; see the delivery record).

## Scope

The prior terminal handoff's named continuation class: "the audit
method's natural next targets are the remaining pre-discipline QA
families outside the mixing cascade in consumption order — the
electrical cluster (`EffectiveResistance_QA`/`ElectricalFlow_QA`/
`ResistanceMetric_QA`/`Foster_QA`/`KernelBridge_QA`, feeding the
sparsification program) is the next-highest-consumed unaudited cluster."
This run audits the cluster's **root family**: the whole of
`Scaffold/Mathlib/GraphTheory/Electrical.lean` — the
potential-equation definition layer (`IsEffectiveResistance`,
`effectiveResistance`, existence/uniqueness/agreement, the energy
identity), the one-sided Dirichlet bound and its engines
(`sq_le_mul_of_forall_zero_le_sub`, `quadForm_laplacian_sub_smul`,
`laplacian_cauchy_schwarz`), the confinement pair (the maximum
principle), and the resistance-metric residual trio (`pos_of_ne`,
`eq_zero_iff`, `le_add`) — together with its two QA files
(`EffectiveResistance_QA.lean`, delivered 2026-08-18/24;
`ResistanceMetric_QA.lean`, delivered 2026-08-24). The remaining four
electrical QA files (`ElectricalFlow`, `Foster`, `KernelBridge`, and
the `ResistanceMetric` consumers) build on this substrate and are the
natural next audits in the same order.

Method: `governance/ADVERSARIAL_REVIEW.md`'s hypothesis-necessity pass
(seven precedents: TV/Dobrushin, lazy, entropy, Poisson-bridge,
primitivity-supplier (+ its consumer follow-on), irregular Cheeger,
regular Cheeger) — re-read every theorem's hypothesis clauses, identify
those with no negative witness anywhere in the repository, and close
each with a hypothesis-form fence (the dropped-hypothesis statement
refuted at a fixture where every other hypothesis is genuine, certified
by an isolation companion), or record a non-fenceable with its
mechanism.

## Step-0 findings: the priced fence list

Sixteen genuinely new fences at three new fixtures plus the
disconnected fixture, six clauses screened as already fenced by
delivered witnesses.

### The rank-1 signed 4-cycle `sgnK4Adj` (new fixture)

Positive edges `(0,1), (0,2), (1,3), (2,3)` — the support, a connected
4-cycle `1—0—2—3—1`; negative edges `(0,3), (1,2)`; every degree
exactly `1`. The decisive structural finding: its Laplacian has **rank
1** — the kernel is three-dimensional (spanned by `1`,
`![1,1,-1,-1]`, `![1,-1,1,-1]`; every row of `L` is the single linear
constraint `f 0 + f 3 = f 1 + f 2`). Consequently the demand
`e 0 − e 2` is unsolvable (the kernel vector `![1,1,-1,-1]` pairs with
it to `2 ≠ 0`, certified through the shelf's
`dotProduct_eq_zero_of_laplacian_mulVec_eq_zero`), while the support
graph is connected and the weights symmetric. **Connected support does
not imply demand solvability once signs enter.**

- **Fence (`exists_isEffectiveResistance`, `hnn`)**: `sgnK4F_exists_hnn_fence_QA`
  — no resistance value exists between `0` and `2`; the junk fallback
  pinned (`sgnK4_fallback_zero_QA`).
- **Fence (`effectiveResistance_eq_quadForm`, `hnn`)**:
  `sgnK4F_energy_hnn_fence_QA` — no potential solves the demand, so the
  energy-identity existence statement fails outright.
- Isolation: `sgnK4_fence_isolation_QA` (symmetric ∧ connected support ∧
  ¬nonnegative).

### The signed overshoot fixture `sgnOverAdj` (new fixture)

Positive edges `(0,1), (1,3), (2,3)` (support: the path `0—1—3—2`), one
negative edge `(0,2)`, degrees `(0, 2, 0, 2)`. The kernel is exactly the
constants, so every demand is solvable — this fixture supplies genuine
solutions, unlike `sgnK4Adj`.

- **Fence (`laplacian_mulVec_eq_single_sub_single_le_max`, `hnn`)**:
  `soF_confinement_max_hnn_fence_QA` — the `e 0 − e 1` solution
  `![1/2, 0, 1, 1/2]` takes vertex `2` to `1 > max(1/2, 0)`: the
  negative edge is an anti-restoring force that pushes a non-boundary
  vertex strictly above both boundary values.

  **Pricing finding:** no three-vertex signed fixture can kill the max
  half. On three vertices the interior vertex `x`'s diffusion row reads
  `deg x · f x = ∑_j A x j · f j` with every neighbor on the boundary
  pair — i.e. `f x` is a weighted average of `f u` and `f v` whenever
  `deg x = ∑_j A x j` (no self-loop), always confined. This is why the
  delivered 2026-08-24 signed fence (`signed_confine_refuted_QA`, on
  `signedAdj`) killed only the **min** half: its overshoot goes below,
  and the fixture's interior vertex is pinned to the boundary average
  from above. The max half needed the fourth vertex.
- Isolation: `soF_isolation_QA`.

### The disconnected fixture's `hconn` fences (existing `connDiscAdj`)

The **free-constant-on-a-foreign-component** mechanism: a same-component
demand leaves every other component's potential free at an arbitrary
constant, and that constant escapes confinement.

- **Fence (`…_le_max`, `hconn`)**: `discF_confinement_max_hconn_fence_QA`
  at `![1, 0, 7, 7]` (`7 > max 1 0`).
- **Fence (`…_min_le`, `hconn`)**: `discF_confinement_min_hconn_fence_QA`
  at `![1, 0, -7, -7]` (`min 1 0 = 0 > -7`).
- **Fence (`effectiveResistance_ge_sq_div_quadForm`, `hconn`)**:
  `discF_dirichlet_hconn_fence_QA` — the indicator `e 0` has genuine
  energy `1` (`disc_energy_e0_four_QA`), so the dropped bound reads
  `1 ≤ R 0 2 = 0`: the junk fallback cannot bound a genuine Dirichlet
  ratio. (Distinct from the delivered `disc_zero_energy_guard_QA`, which
  fences the `hpos` *guard* on a zero-energy vector.)
- **Fence (`effectiveResistance_le_add`, `hconn`)**:
  `discF_triangle_hconn_fence_QA` — routing the edge `0—1` through a
  foreign middle vertex reads `1 ≤ R 0 2 + R 2 1 = 0 + 0` (the mirrored
  demand `e 2 − e 1` unsolvable: `disc_no_resistance_21_QA`, pinned
  `disc_fallback_21_zero_QA`).
- **Fence (`effectiveResistance_pos_of_ne`, `hconn`)**:
  `discF_pos_hconn_fence_QA` (`0 < R 0 2 = 0` false).
- **Fence (`effectiveResistance_eq_zero_iff`, `hconn`)**:
  `discF_definiteness_hconn_fence_QA` (the iff identifies `0` and `2`).

### The asymmetric fixture `ecAsymAdj = !![0,2;1,0]]` (new fixture)

The Cauchy–Schwarz and polarization engines' statements never mention
`supportGraph`, so their `hA` is genuinely fenceable (unlike every
theorem whose `hconn` clause syntactically consumes the symmetry proof).

- **Fence (`laplacian_cauchy_schwarz`, `hA`)**:
  `ecF_cauchy_schwarz_hA_fence_QA` — row sums `(2, 1)`, Laplacian
  `!![2,-2;-1,1]`, at `f = ![5,6]`, `g = ![1,0]`: cross term `4`,
  squared `16`, against `quadForm f · quadForm g = (-4) · 2 = -8`.
- **Fence (`quadForm_laplacian_sub_smul`, `hA`)**:
  `ecF_polarization_hA_fence_QA` — at `f = ![1,0]`, `g = ![5,6]`,
  `t = 1`: the perturbed energy `-4` against the expanded `2`.
- Isolation: `ecF_cauchy_schwarz_hA_isolation_QA` (nonnegative ∧
  ¬symmetric).

### The signed fixture's engine fences (existing `signedAdj`)

- **Fence (`laplacian_cauchy_schwarz`, `hnn`)**:
  `sgF_cauchy_schwarz_hnn_fence_QA` — at `f = ![0,1,-1]` (energy `-2`),
  `g = ![0,1,0]` (energy `0`): cross term `-1`, squared `1`, against
  `(-2) · 0 = 0`. The discriminant extraction needs the nonnegative PSD
  hypothesis, not symmetry alone.
- **Fence (`effectiveResistance_ge_sq_div_quadForm`, `hnn`)**:
  `sgF_dirichlet_hnn_fence_QA` — the indicator `e 0`'s genuine ratio
  `(1-0)²/2 = 1/2` against the pinned `R 0 1 = 0`.
- **Fence (`effectiveResistance_nonneg`, `hnn`)**:
  `sgF_nonneg_hnn_fence_QA` — `0 ≤ R 2 1 = -2` false (explicit; the pin
  `signed_R21_QA` predates this audit).
- **Fence (`effectiveResistance_eq_zero_iff`, `hnn`)**:
  `sgF_definiteness_hnn_fence_QA` — `R 0 1 = 0` at `0 ≠ 1`.
- Isolation: `sgF_cauchy_schwarz_hnn_isolation_QA`.

### Screened clauses (already fenced by delivered witnesses)

- The min half's `hnn` — `signed_confine_refuted_QA` (2026-08-24).
- `exists_isEffectiveResistance`'s `hconn` — `disc_no_resistance_QA`
  (2026-08-18; the header's named connectivity negative witness).
- The Dirichlet bound's `hpos` guard — `disc_zero_energy_guard_QA`
  (2026-08-18; the zero-energy component indicator).
- `effectiveResistance_le_add`'s `hnn` — `signed_triangle_refuted_QA`
  (2026-08-24).
- `effectiveResistance_pos_of_ne`'s `hnn` — `signed_pos_refuted_QA`
  (2026-08-24).
- The reverse (upper-bound) direction of the Dirichlet inequality as a
  *statement shape* — `path_bound_reverse_refuted_QA` (2026-08-18).

## Recorded non-fenceables (with mechanisms)

- **The structural `hA`s.** Every theorem whose statement contains
  `supportGraph A hA` consumes the symmetry proof in the statement
  itself: `exists_isEffectiveResistance`, `…_unique_of_reachable`,
  `…_unique`, `…_eq_of_reachable`, `…_eq`, `…_eq_quadForm`,
  `…_nonneg`, `…_symm`, `…_pos_of_ne`, `…_eq_zero_iff`, `…_le_add`,
  and both confinement halves. The dropped-`hA` statement is unstatable
  at an asymmetric fixture — the reachability/connectivity hypothesis
  cannot be formed. (The engines fenced above are exactly the two
  exceptions whose statements are `supportGraph`-free.)
- **The uniqueness/agreement `hnn`** (`isEffectiveResistance_unique_of_reachable`,
  `isEffectiveResistance_unique`, `effectiveResistance_eq_of_reachable`,
  `effectiveResistance_eq`): for **symmetric** `A` (of any sign
  pattern), solvability of the demand `L *ᵥ f = e u − e v` forces
  `e u − e v ⊥ ker L` (range ⊆ kernel-orthogonal), and any kernel
  direction `k` then satisfies `k u = k v` (pair `k` with the demand);
  adding `k` to a solution changes `f u − f v` by `k u − k v = 0`. So
  whenever a witness exists, the value is unique — the dropped-`hnn`
  statement is provable for all symmetric `A`, and the reachability
  clause needs `hA` structurally. The signed fixtures cannot refute it:
  `signedAdj`'s demands are all solvable with unique values.
- **`effectiveResistance_symm`'s `hnn` and `hconn`**: the relation-level
  symmetry `isEffectiveResistance_symm` is hypothesis-free, and by the
  same orthogonality mechanism the two orientations' value sets are
  singletons-or-empty (for symmetric `A`) — so the function-level
  symmetry holds without nonnegativity and without connectivity. The
  dropped-hypothesis statement is provable; only the asymmetric corner
  could in principle break it (two `Classical.choose`s from
  propositionally-distinct-but-equivalent existentials), and `hA` is
  structural here anyway.
- **`effectiveResistance_nonneg`'s `hconn`**: within a component the
  value is a genuine resistance with the energy identity and
  `laplacian_psd` available; across components the function takes the
  junk `0`. Both cases give `0 ≤ R u v` — the dropped-connectivity
  statement is provable on all symmetric nonnegative graphs.
- **`sq_le_mul_of_forall_zero_le_sub`'s `hE`**: a real quadratic
  `Q − 2tc + t²E` nonnegative for every `t` forces `E ≥ 0` (else it
  diverges to `-∞`), so `hE` is implied by `h` — removable, not
  fenceable.
- **Hypothesis-free lemmas** (`isEffectiveResistance_self_iff`,
  `isEffectiveResistance_symm`, `effectiveResistance_self`,
  `effectiveResistance_eq_zero_of_not_exists`,
  `quadForm_laplacian_eq_sub_of_mulVec_eq_single_sub_single`): no
  clauses to fence.

## Discipline

QA-only: no axiom contact (count stays 4; `#print axioms` via
`wip/ecfences_axcheck.lean` on all 50 new declarations — every one
exactly `propext, Classical.choice, Quot.sound`); no `-- @refutes` tags
(these refute *theorem* instantiations; nothing admitted is consumed).
Spiked first in `wip/ecfences_spike.lean` to zero errors/zero warnings;
landed as pure insertions (`AdversarialFences` sections in
`EffectiveResistance_QA.lean` and `ResistanceMetric_QA.lean`, plus one
header sentence each). The prior runs' uncommitted deliveries preserved;
nothing committed.

## Delivery record (2026-09-04, run `20260904T095642Z-run-1`)

All 16 priced fences closed with isolation companions as planned; no
scope revision. QA 4648 → 4695 (+47 by the generator metric, which
counts theorems/lemmas only — the 50 declarations include the 3 fixture
`def`s). Verification: spike → `lake env lean` on both landed modules
(zero errors/zero warnings) → explicit `lake build` targets → the
50-declaration axiom audit → full `lake build` ✔ + completeness 133/133
fresh/0 stale/0 missing → `lint_axioms` (4 unchanged) →
`check_refutation_independence` (9-tag) → `check_public_reachability`
(63) → `check_citations` → `check_markdown_links` →
`check_backlog_freshness` → scoreboard regenerated with the
verification row → map-freshness after the stats sync + SVG regen.

Technique findings:

1. **`degreeMatrix`'s dependent `if` does not decide under a bound
   variable.** Every entrywise Laplacian computation that unfolds
   `degreeMatrix` inside `∑ j` stalls on `dite (i = j)` with `j`
   generic — `simp` cannot decide it and `norm_num` cannot either. The
   robust route for *all* fixture arithmetic is the shelf's
   `laplacian_mulVec_apply` (the diffusion form `∑ j, A i j * (f i − f
   j)`), which never mentions `degreeMatrix`. Delivered as the two
   generic helpers `ecf_quadForm_lap`/`ecf_dot_lap` so future QA never
   re-derives this.
2. **`simp only` does not run `reduceIte`.** Residual `if (2 : Fin 4) =
   1 then …` conditions survive `simp only [...]` + `norm_num` but are
   decided by plain `simp` — the pins that stalled under `simp only`
   close under `simp` once the sums are unrolled by `Fin.sum_univ_n`
   first. Conversely plain `simp` sometimes closes the whole arithmetic
   goal, leaving a trailing `norm_num` to error with "no goals" — the
   robust shape is `simp [sum-unroll, fixture, cons lemmas]` then
   `norm_num` only where the display still shows arithmetic.
3. **`Matrix.dotProduct_single` is the clean route for demand-vs-kernel
   pairings.** Rewriting `k ⬝ᵥ (single u 1 − single v 1)` with
   `Matrix.dotProduct_sub` + `Matrix.dotProduct_single` (twice) reduces
   to two vector-literal lookups — avoiding the `Pi.single_apply`-under-
   sum path that `simp` turns into `Finset.filter`-card goals it cannot
   close.
4. **`lake env lean` reads built oleans, not fresh sources.** A QA file
   importing new declarations from another QA file fails on "unknown
   identifier" until the dependency is rebuilt (`lake build
   Scaffold.QA.SpectralGraph.EffectiveResistance_QA` first); the error
   message names the helper, not the staleness, which misleads.

Remaining priced follow-ons: none in this family — the four sibling
electrical QA families (`ElectricalFlow_QA`, `Foster_QA`,
`KernelBridge_QA`, and the `ResistanceMetric` consumer set) are the
audit method's next targets in the consumption order the handoff named.
