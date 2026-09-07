# Proposal: The Signed Switching Layer's Positive Pins

**Status:** COMPLETE. Delivered 2026-09-07 (run `20260907T060831Z-run-3`,
session `ses_f85b4c94affebxh9q9Bec73k5W`); QA-only, zero axiom contact.
The delivery record is at the file's end.

## The census finding this closes

`scripts/consumption_survey.py`'s census (`wip/census_20260907_post6.txt`)
names Signed as the largest remaining never-touched cluster (4 theorems):
`signedAdj_symmetric`, `signedLaplacian_symmetric`, `switchVec_ne_zero`,
and `laplacian_mulVec_switchVec` — the backward eigenpair transfer, the
spectral bridge of Harary balance (the forward twin
`signedLaplacian_mulVec_switchVec` is already consumed; the backward
direction never was). The existing QA had pinned the balance/kernel/
energy facts *beside* these four: `sgPath_switch_ne_zero_QA` proves
nonvanishing raw rather than through `switchVec_ne_zero`, and no QA
statement had ever instantiated either symmetry theorem or the backward
transfer. Signed and EdgePerturbation tied at four; Signed wins on
content centrality — the four are the balance theory's engine, not
design plumbing.

## What was delivered

Ten QA theorems in `Signed_QA.lean`'s new `StructuralPins` section
(QA 6635 → 6645), the first genuine consumption of all four:

- **The symmetry two** (`sgp_adjSymm_path`, `sgp_lapSymm_path`) — the
  theorem instances at the balanced path fixture, both hypotheses
  genuine; the entry-level reads (`sgp_adjSymm_entry_pin`,
  `sgp_lapSymm_entry_pin`) derive the `(1, 0)` entries THROUGH the
  theorems' `IsSymm.apply` from the raw `(0, 1)` entries (`−1` for the
  signed adjacency, `+1` for the signed Laplacian — the sign-flipped
  edge `−(−1)`), exactly what a transposed convention would break.
- **The scope witness** (`sgp_lapSymm_tri`): the frustrated triangle —
  symmetric but NOT balanced (`sgTri_not_isBalanced_QA`) — still gets a
  symmetric signed Laplacian: the theorem's hypothesis set is symmetry,
  not balance, pinned at the boundary.
- **The switching nonvanishing** (`sgp_switchVec_val` +
  `sgp_switchVec_ne_zero_pin`): the switched value `diag(g)·(2,3,5) =
  (2,−3,−5)` pinned raw (three genuinely nonzero entries, so the
  nonvanishing is not carried by one coordinate), the nonzeroness
  THROUGH the theorem.
- **The headline round-trip** (`sgp_unsigned_eigenpair_raw`,
  `sgp_signed_eigenpair_raw`, `sgp_backward_transfer_pin`): the
  unsigned mode `L·(1,0,−1) = 1·(1,0,−1)` computed RAW (route A, the
  diffusion-form action `laplacian_mulVec_apply` at the adjacency
  entries); its switching `L_σ·(1,0,1) = 1·(1,0,1)` computed RAW; and
  the SAME unsigned eigenpair equation re-derived through
  `laplacian_mulVec_switchVec` at the signed eigenpair, composed with
  the switching involutivity identifying the switched-back vector as
  exactly `![1,0,−1]`. Two routes, one value; they agree only if the
  raw computations AND the bridge are right.

## Technique findings (Lean 4.14 / this Mathlib pin)

- `Matrix.IsSymm.apply h i j : A j i = A i j` — the REVERSED direction
  from the natural reading; the entry reads go through
  `hsym.symm.trans hraw`.
- Fin-literal `if`s from `Matrix.diagonal_apply` do not resolve under
  `norm_num` (`if ⟨2, ⋯⟩ = 1 then …` stuck; `¬0 = 2` side goals) — the
  private helper `sgp_diagonal_mulVec_apply` routes through
  `Finset.sum_eq_single` + `Matrix.diagonal_apply_eq` with the
  off-diagonal bullet closed by `simp [Matrix.diagonal_apply, hj.symm]`
  (the `diagonal_apply_ne` signature takes its arguments in an order
  that made the direct `rw` call mis-elaborate).
- Entry lemmas at `Fin 3` literals (`sgPathL00`-style) do not
  `simp only`-match post-`fin_cases` goals (the `⟨2, ⋯⟩`-vs-`2`
  surface-syntax gap); the raw eigenpair computation routes through
  the diffusion form `laplacian_mulVec_apply` instead, mirroring
  `sgPath_kernel_QA`'s working idiom.

## Verification

Spike-first (`wip/sgpins_spike.lean` — green after three fix rounds);
the landed module elaborates with zero errors/warnings; explicit build
✔; the 10-declaration axiom audit (`wip/sgpins_axcheck.lean`) — every
one exactly `propext, Classical.choice, Quot.sound`; full `lake build`
+ `check_build_completeness.py` (135/135 fresh); `lint_axioms` exit 0;
`check_refutation_independence` (24-tag clean);
`check_public_reachability` (63 modules); `check_citations`;
`check_markdown_links`; `check_qa_name_uniqueness` (`sgp_*`
collision-free); `check_backlog_freshness` clean; scoreboard
regenerated (1369 / 6645 / 4 / 0); map freshness exit 0 after the
stats sync; the census re-run (`wip/census_20260907_post7.txt`)
verifying exactly the four targeted theorems leaving the inert set.

## Honest scope

Positive pins only — no hypothesis-necessity fences (the four
theorems' hypothesis surfaces are structural: symmetry and
`{±1}`-valuedness; a necessity fence for `hsymm` would need a
signing whose asymmetry breaks the conclusion, priced but not owed
under the pins pattern). The fixtures are the module's own path and
triangle; the eigenpair round-trip is at the eigenvalue `1` only.
