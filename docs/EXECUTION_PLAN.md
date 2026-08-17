# Execution plan

This is the compact, current-state ledger for sustained autonomous work. It is
updated at milestone boundaries; [`AGENT_ACTIVITY.md`](AGENT_ACTIVITY.md)
holds the append-only narrative.

## Active milestone

**Citation hygiene and broad-SGT reorientation.** The projector algebra is
proved in the center. The persistence package is retained as an existing
compatibility/example result, not a roadmap goal. The citation-hygiene
audit items below were completed on 2026-08-17 (see Last verified state):

1. **False provenance note (found by audit):** the Chung index claimed
   earlier revisions recorded page-level locators "Theorem 2.1 p. 42,
   Theorem 2.2 p. 44". Git history contradicted this: the initial commit
   cited only "Theorem 2.2" without a page, and no pre-rebuild index file
   exists. The note now records the accurate history; theorem and page
   numbering stay explicitly unconfirmed against the printed text (no
   local copy; page numbers were not invented).
2. **Weyl citation fidelity:** `weyl_inequality`'s doc now records that
   its Lean form is the spectral-norm corollary of the cited general Weyl
   inequality (obtained by combining the additive bound with
   `λ₁(E) ≤ ‖E‖` and `λₙ(E) ≥ -‖E‖`).
3. **Davis–Kahan hypothesis tightening:** the separation hypothesis is
   now the binding single-pair two-cluster form
   `λ_{k+1}(A+E) - λ_k(A) ≥ δ` (the form used by the cited
   Yu–Wang–Samworth Theorem 2); the derived wrapper simplified to one
   Weyl fact at the gap index, and the QA reduces the pairwise form via
   `evals_sorted`.

**Hard-crust conversion (same module):** `spectral_gap_stability` is now
a theorem proved from `weyl_inequality` (Weyl at both gap endpoints plus
arithmetic), reducing the explicit axiom count 19 → 18 with identical
statement shape (no consumer changes).

**Leverage delivered:** a false provenance claim removed from the
human-review surface; two axiom statements aligned with their sources;
the mushy center shrunk at zero trust cost.

**Next action:** with citation hygiene closed, the next milestone is the
broad-SGT backlog (ready queue item 1) — **delivered on 2026-08-17**:
(a) `docs/6_SGT_BACKLOG.md`, the bounded center-first backlog ranked by
concrete reuse (random-walk/Markov interfaces; irregular normalized
adapters; expansion/cut interfaces; spectral algorithms; conditional
dynamics and statistical-mechanics items), each naming consumers and
dependency paths, linked from the README canonical-docs list; and (b) its
top-ranked item implemented: `Scaffold.Mathlib.GraphTheory.RandomWalk`
— `transitionMatrix`, proved row-stochasticity for `d`-regular graphs,
`randomWalkLaplacian`, and proved bridges to both existing worlds
(`= regularNormalizedLaplacian`; `= d⁻¹ • laplacian`). Pure hard crust,
no new axioms; QA `SpectralGraph/RandomWalk_QA.lean` with a concrete
two-vertex instantiation. Umbrella, scoreboard, and SGT index map
updated.

**Next milestone:** backlog item 2, remainder — the irregular walk form —
**delivered on 2026-08-17 (run 8)**. Evidence check first: the walk
Laplacian `I − D⁻¹A` is *not symmetric* for irregular graphs, so
Scaffold's `evals` does not apply to it, and the deferred eigenvalue
transfer would need a charpoly-roots interface absent from the pinned
Mathlib. Delivered in `GraphTheory.Normalized` (all proved): general
`walkTransitionMatrix` (`D⁻¹A`) with `walkTransitionMatrix_row_sum`
(row-stochasticity under positive degrees — the named Markov consumer),
`walkLaplacian`, and the similarity identity
`degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt`
(`√D · L_walk · (1/√D) = L_sym`), with the eigenvalue-list transfer
recorded as the precisely named residual gap in the backlog. QA extended
at the 3-vertex path (row distributions, walk entries `1/2`/`1`, and the
similarity identity instantiated entrywise).

**Next milestone (open):** backlog item 3 — expansion and cut interfaces
(edge-boundary and uniform-weight conductance variants), each admitted
only with a named algorithm consumer.

**Active slice (run 10, 2026-08-17): cut duality — delivered.** The
existing cut surface (`vol`, `boundary`, `conductance`,
`cheegerConstant`) had nonnegativity but not the duality facts that
every cut-consuming algorithm assumes. Delivered in
`GraphTheory.Spectral` (all proved, no axioms): `vol_compl`
(`vol S + vol Sᶜ = vol univ`), `boundary_compl` (`boundary S =
boundary Sᶜ` for symmetric `A`, via `Finset.sum_comm` + symmetry),
`conductance_compl` (`conductance S = conductance Sᶜ` — Cheeger
minimizer canonicalization; the sweep-cut consumer interface),
`boundary_empty`/`boundary_univ` (degenerate-cut guards). QA at the
3-vertex path (`SpectralGraph/Cuts_QA.lean`, 11 declarations):
singleton boundary computes to `1`, duality and conductance invariance
instantiate, volume complementarity totals `4`, guards evaluate.
Backlog item 3's "Have" list updated.

**Next slice (open):** remaining backlog item 3 variants — edge-boundary
and uniform-weight conductance — each to be admitted only with a named
algorithm consumer; or backlog item 4 gating review.

**Active milestone (run 1, 2026-08-17): SGT coverage radar (operator
direction) — delivered.** `docs/7_SGT_RADAR.md` published with both
radars scored strictly from repository evidence (every score cites
declarations with proved/admitted/absent status): subject — models 2.5,
spectral algebra 3.5, variational 2.5, cuts/expansion 2.5, walks 2.5,
electrical **0.5** (entirely absent), perturbation/randomness 3.0,
adjacent systems 1.0; assurance — proved depth 3.5, axiom minimization
3.5, Mathlib interop 3.5, QA 3.0, citation fidelity 3.5, downstream
reuse **2.5** (RandomWalk/Normalized unconsumed). Includes a
re-scoring protocol (scores move only with usable, verified coverage,
recorded with the causing milestone). Backlog gains the radar-driven
gated candidate (item 7, electrical structure) and a downstream-reuse
standing decision; README canonical-docs list links the radar. No Lean
changes; hygiene suite passes.

**Next milestone (radar-driven): first downstream consumer for the
walk/normalized interfaces — delivered (run 2, 2026-08-17).** New
`Scaffold.Mathlib.GraphTheory.Stationary` (imports `Normalized`; all
proved, no axioms): `mulVec_one_eq_deg` (`A *ᵥ 1 = deg`),
`normalizedLaplacian_mulVec_sqrtDeg_eq_zero` (kernel of `L_sym` is
`√deg` — the normalized counterpart of `laplacian_ones_in_kernel`),
and `walkTransitionMatrix_transpose_mulVec_deg` (`Pᵀ *ᵥ deg = deg`:
the degree measure is stationary for the walk, `π ∝ deg` — the named
Markov-mixing consumer interface). QA
`SpectralGraph/Stationary_QA.lean` (6 declarations) at the 3-vertex
path. Radar: downstream reuse re-scored 2.5 → 3.0 with this milestone
recorded (protocol followed); remaining reuse gap: `RandomWalk`'s
regular-case bridges.

**Next milestone (open):** a consumer for `RandomWalk`'s regular
bridges — **delivered (run 3, 2026-08-17).** Evidence-based scoping:
the λ-transfer consumer needs `evals (c • M) = c • evals M`, but
Mathlib's `eigenvalues` is `irreducible_def` behind the eigenspace
decomposition — recorded as a named backlog candidate rather than
attempted. Delivered instead: `GraphTheory.Stationary` extended with
the walk-Laplacian kernel facts —
`randomWalkLaplacian_mulVec_one_eq_zero` (regular; consumes
`RandomWalk.transitionMatrix_row_sum`) and
`walkLaplacian_mulVec_one_eq_zero` (irregular; consumes
`Normalized.walkTransitionMatrix_row_sum`) — conservation of mass,
`(I − P) *ᵥ 1 = 0`, the base statement of diffusion/mixing arguments.
`Stationary` is now the demonstrated consumer of *both* interface
modules. QA at the regular edge and the irregular path. Radar: reuse
re-scored 3.0 → 3.5 (recorded); the constraint is now breadth of
reuse, and QA (3.0, degenerate-case skew) is the weakest assurance
axis.

**Next milestone (open):** breadth consumers for the walk/normalized
interfaces (second consuming module — e.g. variational Rayleigh bounds
through the congruence bridge), or the QA-assurance lever
(property-based/falsification QA), or remaining backlog item 3
variants with named consumers.

**Decision milestone (run 9, 2026-08-17): `spectral_persistence`
deprecated — decision closed.** Consumer inventory (grep evidence): the
axiom had zero non-QA consumers — the derived layer mentioned it only in
a comment; its only use was the QA deliberately exercising the
compatibility surface; the derived two-endpoint chain
(`eventStreamProjectorDrift`/`davisKahanTwoPoint`) covers the motivating
persistence use. Per the architecture §9 lifecycle: `@[deprecated]` with
a migration note (probe-verified to apply to `axiom` declarations),
retained through the compatibility window — removal is a later release
decision, so the explicit axiom count remains 18 until then. The QA
exercises the deprecated surface with the linter silenced for that use
only. Indexes/docs updated (davis_kahan source, SGT/perturbation maps,
backlog standing decision, architecture debt, scoreboard). Bonus hygiene
in the same run: the derived module's use of Mathlib's deprecated
`div_lt_div_iff` upgraded to `div_lt_div_iff₀`; the full build now
carries zero deprecation warnings.

## Ready queue

1. Citation hygiene — completed 2026-08-17 (see Active milestone and Last
   verified state); Chung provenance corrected, Weyl/Davis–Kahan fidelity
   notes added, DK hypothesis tightened, `spectral_gap_stability` proved
   from Weyl (axioms 19 → 18).
2. Establish the first broad-SGT backlog — delivered 2026-08-17 as
   `docs/6_SGT_BACKLOG.md` with its top item implemented
   (`GraphTheory.RandomWalk`); next backlog item: irregular normalized
   adapters.
3. Do not let retained applications or compatibility packages determine the
   next SGT milestone.
4. `spectral_persistence` retain-or-deprecate — decided 2026-08-17:
   deprecated with a migration note (zero non-QA consumers; derived
   chain covers the motivating use), retained through the compatibility
   window; removal is a later release decision. Do not extend its
   theorem family.
5. Re-admit removed subgaussian statements (moment growth, linear
   combinations, centering, sums) only when a consumer names them.

## Last verified state

- 2026-08-17 (walk-Laplacian kernel / RandomWalk consumer): `lake
  build` passes; 119 QA declarations, no `sorry`/`admit`; 18 explicit
  cited axioms (unchanged); `Stationary` consumes both interface
  modules; radar reuse 3.0 → 3.5 recorded; all hygiene scripts pass.
- 2026-08-17 (stationary structure): `lake build` passes with
  `GraphTheory.Stationary` in the umbrella; twenty public modules and
  seventeen QA modules (116 declarations) compile directly with no
  `sorry`/`admit`; 18 explicit cited axioms (unchanged); downstream
  reuse radar score 2.5 → 3.0 recorded; all hygiene scripts pass.
- 2026-08-17 (cut duality): `lake build` passes; 107 QA declarations
  (new `SpectralGraph/Cuts_QA.lean`), no `sorry`/`admit`; 18 explicit
  cited axioms (unchanged); cut duality proved in the center
  (`vol_compl`, `boundary_compl`, `conductance_compl`,
  `boundary_empty`, `boundary_univ`); all hygiene scripts pass.
- 2026-08-17 (irregular walk form): `lake build` passes; 96 QA
  declarations, no `sorry`/`admit`; 18 explicit cited axioms (unchanged);
  general `walkTransitionMatrix` with row-stochasticity, `walkLaplacian`,
  and the similarity identity `√D · L_walk · (1/√D) = L_sym` proved;
  all hygiene scripts pass.
- 2026-08-17 (irregular normalized Laplacian): `lake build` passes with
  `GraphTheory.Normalized` in the umbrella; nineteen public modules and
  fifteen QA modules (93 declarations) compile directly with no
  `sorry`/`admit`; 18 explicit cited axioms (unchanged — pure hard
  crust); `lint_axioms`, `check_citations`, `check_markdown_links` all
  pass.
- 2026-08-17 (broad-SGT backlog + random-walk interfaces): `lake build`
  passes with `GraphTheory.RandomWalk` in the umbrella; eighteen public
  modules and fourteen QA modules (82 declarations) compile directly
  with no `sorry`/`admit`; 18 explicit cited axioms (unchanged — the
  increment is pure hard crust); `lint_axioms`, `check_citations`,
  `check_markdown_links` all pass; `docs/6_SGT_BACKLOG.md` published and
  linked.
- 2026-08-17 (citation hygiene + tightening): `lake build` passes;
  explicit axioms reduced 19 → 18 (`spectral_gap_stability` now proved
  from `weyl_inequality`); `davis_kahan_sin_theta` separation tightened
  to the single-pair two-cluster form (derived wrapper simplified to one
  Weyl fact; QA reduces the pairwise form via `evals_sorted`); Chung
  index provenance note corrected against git history; Weyl doc records
  the norm-corollary relation; `lint_axioms`, `check_citations`,
  `check_markdown_links` all pass; 75 QA declarations, no `sorry`/`admit`.
- 2026-08-17 (projector algebra): `lake build` passes; all seventeen
  public modules and all thirteen QA modules (75 declarations) compile
  directly with no `sorry`/`admit`; eigenbasis orthonormality
  (`eigvecOf_inner`) and completeness (`eigvecOf_complete`) proved from
  the Mathlib spectral-theorem API; `spectralProjector_idempotent`,
  `initialProjector_idempotent`, `spectralProjector_eq_zero`,
  `spectralProjector_eq_one` proved; new QA
  file `SpectralGraph/Projector_QA.lean` (5 declarations).

## Blockers

- The native Mathlib cache executable fails on this macOS environment with a
  dyld segment error. Cached artifacts were obtained through the recorded Lean
  interpreter workaround; this is environment debt, not an SGT source failure.
