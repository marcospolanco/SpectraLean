# Proposal: Signed Graphs — the Balance Theorem via the Magnetic π-Flux Bridge

**Status:** COMPLETE — Step 0 (the design decisions below, recorded
before any shelf Lean) + Step 1 (the delivery) both delivered
2026-08-26 by run `20260826T194844Z-run-1`. Selected per the empty
High/Medium Active table by the center-out policy as a fresh
graph-model-axis candidate — radar axis 1 named signed-graph theory an
absent category, and the standing handoff named the graph-model axis
among the lowest-scored frontiers. Zero axioms admitted (count stays
10; `#print axioms` via `wip/sg_axcheck.lean` on all 93 audited
declarations — 32 public + 61 QA — reads exactly
`propext, Classical.choice, Quot.sound`, every one). Nothing
committed, nothing published. Priced follow-ons (not gated, one
delivered): the multiset-level spectrum equality `evals L_σ = evals L`,
Zaslavsky counting theory, signed Cheeger, the frustration-index
variational layer (gated on the magnetic program's consumer rule).

## The obligation this discharges

`docs/7_SGT_RADAR.md` axis 1 (graph and Laplacian models, 3.5) lists
signed-graph theory as an absent category. The `docs/1_STRATEGY.md`
load-bearing-growth principle names the mechanism this proposal
executes: make a delivered-but-only-QA-consumed layer carry weight from
a second theorem family. The magnetic Laplacian
(`GraphTheory/Magnetic.lean`, delivered 2026-08-25) has its energy
identity and gauge characterization exercised only by QA pins; a
signing is exactly a magnetic potential at the π-flux, so the magnetic
machinery becomes the engine of the classical signed-graph balance
theory — and a defect in it would break the signed theorems below
loudly.

## Classical background (route provenance only — statements are proved)

- F. Harary, *On the notion of balance of a signed graph*, Michigan
  Math. J. 2 (1953): a signed graph is balanced exactly when its edges
  admit a vertex "switching" `g : V → {±1}` with `σ_uv = g_u g_v` on
  every edge (equivalently, every cycle has positive sign product).
- T. Zaslavsky, *Signed graphs*, Discrete Appl. Math. 4 (1982) and
  *Matroid applications* (1993) ch. 9: the signed Laplacian and the
  switching/spectrum theory. The `D − A_σ` Laplacian convention used
  here is the matrix version used by Kunegis et al., *The
  diagonalization method for signed graph embedding* (2010) §2 — the
  same convention the shelf's `laplacian A = D − A` reduces to at
  `σ ≡ +1`.
- The magnetic view of signings (π-flux potentials) is the
  Crucini–Pérez–Bungert–Van Mieghem convention already on the shelf at
  `GraphTheory/Magnetic.lean`.

## Step 0 — the design decisions (recorded before any shelf Lean)

1. **Carrier:** a signing is a plain function `s : V → V → ℝ` with
   explicit hypotheses `∀ u v, s u v = 1 ∨ s u v = -1` (the ±1
   constraint), symmetry `s u v = s v u`, and **loops unsigned**
   `s u u = 1` (the classical convention: loop signs do not enter
   balance, and the unsigned loop keeps the row-sum identity exact).
   Matrix-first, no new type — the same representation decision as
   `WAdj` itself.
2. **The objects:** `signedAdj A s := fun u v => A u v * s u v`
   (entrywise), `signedLaplacian A s := degreeMatrix A − signedAdj A s`
   — `laplacian A` at `s ≡ 1`, symmetric by the same one-liner.
3. **The π-flux join:** `signFlux s u v := if s u v = -1 then π else
   0` gives `e^{i·flux} = s u v` entrywise, so
   `magneticLaplacian A (signFlux s) = (signedLaplacian A s) : Matrix
   V V ℂ` entrywise on symmetric `A` and symmetric `s` (the symmetrized
   degree collapses to `deg` on the symmetric cone). The signed energy
   identity is then **derived from the delivered `magnetic_energy`**
   (the load-bearing join), not re-proved from scratch: `xᵀL_σ x = ½
   ∑ A_uv (x_u − s_uv x_v)²` for real `x`.
4. **The kernel characterization route:** the shelf's form-level gauge
   iff (`magneticQuadForm_eq_zero_iff`) becomes an *action-level*
   kernel characterization — the new `Magnetic.lean` section supplies
   the missing row algebra (`aligned → M *ᵥ x = 0`, unit modulus doing
   the cancellation), composed with the form-level iff. On the signed
   side: `L_σ *ᵥ x = 0 ↔ x_u = s_uv x_v` on every positive edge.
5. **Balance:** `IsBalanced A s := ∃ g : V → ℝ, (∀ v, g v = ±1) ∧ ∀ u
   v, A u v ≠ 0 → s u v = g u * g v`. The **headline** is the Harary
   kernel form: on connected symmetric nonnegative input,
   `IsBalanced A s ↔ ∃ x ≠ 0, L_σ *ᵥ x = 0`. Forward: a direct
   row-sum computation at `g` (no connectivity, no nonnegativity
   needed). Backward: kernel → alignment (Step 0.4) → the walk
   collapse (supportGraph `Walk` induction, the electrical program's
   `exists_const_of_laplacian_mulVec_eq_zero` pattern with the
   accumulated sign product in place of the constant) → `g := x / x_{u₀}`
   is a ±1 switching. The frustrated side: `¬IsBalanced` forces the
   form positive definite on connected input.
6. **The switching similarity:** at a balanced signing with switching
   `g`, `Matrix.diagonal g * L_σ * Matrix.diagonal g = laplacian A`
   (g² = 1 entrywise; off-diagonal `g_u σ_uv g_v A_uv = A_uv`), and
   eigenpairs transfer at switched vectors `g ⊙ v` in both directions —
   the classical "balanced ⟹ spectrally unsigned" fact, stated in the
   `Normalized` eigenpair-transfer pattern (∃-witness form; the
   sorted-spectrum multiset equality is a priced follow-on, not this
   slice).

**Priced follow-ons (not this slice):** the multiset-level spectrum
equality `evals L_σ = evals L` (needs an eigenvalue-counting argument
beyond the ∃-witness transfer); Zaslavsky's chromatic/counting theory;
the signed Cheeger regime; the frustration-index variational theory
(the magnetic program's gated synchronization layer).

## Step 1 — delivery plan

A new section of `GraphTheory/Magnetic.lean` (the kernel at the action
level), the new focused module `GraphTheory/Signed.lean`, QA in a new
`Signed_QA.lean`, and the record sweep (radar axis 1 — including the
repair of its stale "absent: directed graphs" clause, delivered
2026-08-22/25 under backlog item 8; README; scoreboard; index map).
Verification per the ladder: spike first in `wip/sg_spike.lean`,
direct elaboration of both changed modules and the QA file, explicit
`lake build` targets, `#print axioms` audit of every new declaration,
the full build + completeness fence, the script battery, the
scoreboard regeneration.

## Delivery record

**Delivered 2026-08-26 by run `20260826T194844Z-run-1`** — the
Step-0 design held unchanged (including the loop-sign analysis: the
planned `hsloop` hypothesis was *dropped* at implementation time when
the delivery noticed balance itself forces loops unsigned on positive
self-weights — `s u u = g u * g u = 1` — so the theorems are cleaner
than the Step-0 sketch, and QA witnesses the boundary: a negative loop
on a positive self-weight auto-frustrates, `¬IsBalanced` with trivial
kernel).

**Public surface (28 declarations).** A new section of
`GraphTheory/Magnetic.lean` — the kernel at action level:
`hermQuadForm_eq_zero_of_mulVec_eq_zero` (hypothesis-free),
`conj_exp_I_mul_exp_I` (unit-modulus pairing, cloned from the energy
identity's own proof), `magneticLaplacian_mulVec_eq_zero_of_forall_
exp_mul_eq` (the row algebra: alignment cancels the phase through
`exp ≠ 0`, the conjugate transposed term through the unit-modulus
pairing), and **`magneticLaplacian_mulVec_eq_zero_iff`** (the delivered
form-level gauge iff promoted to the kernel — the magnetic module's
own strengthening, at nonnegative weights). The new
`GraphTheory/Signed.lean`: the objects (`signedAdj`,
`signedLaplacian`, `IsBalanced`), the bridge (`signFlux`,
`complex_exp_I_mul_signFlux` at `e^{iπ} = -1`, `symDeg_eq_deg`,
**`magneticLaplacian_signFlux_apply`** — the join, entrywise),
`hermQuadForm_map_ofReal` (the coercion bridge),
**`hermQuadForm_signedLaplacian`** (the complex energy identity,
derived from `magnetic_energy` through the join — the load-bearing
consumption), `signedLaplacian_quadForm` (the real identity, derived
from the complex one), `signedLaplacian_mulVec_apply` (the row-sum,
hypothesis-free), **`signedLaplacian_mulVec_eq_zero_iff_aligned`**
(kernel ↔ edge alignment), `walk_sign` + `exists_switching_of_aligned`
(the walk collapse — the electrical program's pattern with the
accumulated sign product in place of the constant),
`exists_mulVec_eq_zero_of_isBalanced` (row-sum at the switching,
no connectivity/nonnegativity needed, `[Nonempty V]` only),
`isBalanced_of_mulVec_eq_zero` (kernel → alignment → collapse, scale
cancelled against the nonzero anchor), the headline
**`isBalanced_iff_exists_ne_zero_mulVec_eq_zero`**,
`quadForm_pos_of_ne_zero_of_not_isBalanced` (frustration is positive
definiteness), and the switching layer
(`diagonal_mul_signedLaplacian_mul_diagonal`,
`diagonal_mul_diagonal_of_sign`, `switchVec_apply`,
`switchVec_mulVec_switchVec`, `switchVec_ne_zero`,
`signedLaplacian_eq_diagonal_mul_laplacian_mul_diagonal`,
`signedLaplacian_mulVec_switchVec`, `laplacian_mulVec_switchVec` —
two-way eigenpair transfer, the `Normalized` pattern at the
involutive diagonal gauge).

**QA (+62, `Signed_QA` a new file):** the balanced one-negative-edge
path (kernel pinned raw to the switching `![1,−1,−1]`, the iff both
directions — forward from the raw balance witness, backward through
the walk collapse so the join is non-circular, the real energy `10`
and the complex energy `4` at hand-computed test vectors — the latter
exercising the magnetic-join derivation at complex input — and the
π-flux join pinned at the flipped entry `+1`); the frustrated
one-negative-edge triangle (`¬IsBalanced` *proved* from the switching
equations' cyclic contradiction `−1 = (g₀g₁)(g₁g₂)(g₀g₂)·(g₂²)⁻¹·… =
+1`, kernel trivial by the alignment chase, positive definiteness at
`![1,0,0]`); the **disconnected conclusion-level fence** (Fin 5:
balanced edge ⊕ frustrated triangle — the switching extended by zero
is a genuine kernel vector while the signing is globally unbalanced;
the headline's iff cannot even be instantiated, so `hconn` is
load-bearing at the conclusion, exactly as designed); the
**negative-loop boundary** (Fin 2: `s 0 0 = −1` on a positive
self-weight — `¬IsBalanced` since the loop equation needs `g² = −1`,
kernel trivial: both iff sides read "no", consistently, documenting
why no loop-sign hypothesis is carried); the **`hnn` mechanism fence**
(Fin 3 with a `−2` weight: `![0,−2,−1]` a genuine kernel vector with
alignment refuted at the `(0,1)` equation `0 ≠ −2` — the
characterization's hnn is load-bearing at the termwise-vanishing step
of the energy identity, where the fence lives); and the switching
layer (the similarity at concrete witnesses; the independently
verified path eigenpair `![1,0,−1] @ 1` transferring to the switched
`![1,0,1]`, nonzero).

**Technique findings (for future QA at `Fin n` fixtures):**

- The **`fin_cases` id-literal trap**: after `funext i; fin_cases i`,
  the goal's indices carry an `(fun i => i) ⟨k, ⋯⟩` wrapper whose
  proof term differs from the elaborated numeral's — `simp only`
  (instances transparency) and even `rw` fail to match entry-table
  lemmas against it. Remedies that work: per-component `have`s stated
  at literal indices with the whole equation reassembled by `exact`
  (defeq closes the wrapper), and row-sum-identity routes
  (`signedLaplacian_mulVec_apply`) where `norm_num [matrix-defs]`
  evaluates entries without literal matching.
- The **`−1`-entry simp trap**: matrix literals whose entries include
  `-1` defeat simp's numeral unification when `simp [def]` unfolds
  them (0/1-only literals evaluate fine) — the fix is the shelf's
  rfl entry-table discipline (`sgPaths_00 … sgPaths_22 := rfl`) fed to
  `rw`, never `simp`, and `norm_num` only after the table.
- `linear_combination` certificates for `t = t * (unit-product)` goals
  need the **negative** orientation: `linear_combination (-(t)) * h`
  where `h : unit * unit = 1` (the residual is `t·(1 − u²)`).
- `Matrix.mulVec_diagonal (d w i) : (diagonal d *ᵥ w) i = d i * w i`
  exists and takes all three arguments explicitly.
- The stale-olean trap hit once at the QA file's first elaboration
  (unknown identifiers until `lake build Scaffold.QA.SpectralGraph.
  Signed_QA`); the documented remediation applied.

**Verification:** spike first (`wip/sg_spike.lean` + `wip/sg_spike2.lean`,
the flux/join/coercion/row-algebra/walk/switching routes green before
any module touched; the complex-real coercion bridge needed all-forward
`simp only [Complex.ofReal_sum, Complex.ofReal_mul]` normalization —
the `←` rewrites fail on product summands); `lake env lean` — zero
errors/zero warnings on both changed modules and the QA file; explicit
`lake build` targets ✔ (module 2192/2192, QA 2193/2193);
`#print axioms` via `wip/sg_axcheck.lean` — the standard three only,
all 93; **full `lake build` ✔ (2386/2387, "Build completed
successfully") immediately followed by `check_build_completeness.py` —
111/111 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no
issues), `check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**2506/10/0**). Records updated: this proposal,
`proposals/README.md` (the Delivered row; the natural-candidates
paragraph), README (2506; the status-paragraph clause; the module-table
row; the radar snapshot synced), the radar (axis 1 re-scored 3.5 → 4.0
with the stale directed-absent clause repaired; QA axis synced 2444 →
2506 across 58 modules), the scoreboard (two verification rows + the
interpretation bullet), the index map (the Signed section + the
Magnetic kernel rows), backlog item 8's magnetic note, the module and
QA docstrings, the umbrella, the execution plan, and the activity log.
Nothing committed; the prior runs' uncommitted deliveries preserved
untouched.
