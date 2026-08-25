# The Magnetic Laplacian: the Directed-Native Hermitian Operator

**Status:** COMPLETE (run `20260825T001310Z-run-1` drafted module+QA
and recorded Step 0; interrupted before verification; completed by run
`20260825T021040Z-run-1`, which verified both modules — catching and
fixing the draft's three first-pass errors — wired the umbrella, ran
the full check battery, and finished the record sweep)

**Axis:** backlog item 8's reserved "further, separate slice"
(`docs/6_SGT_BACKLOG.md`: "Magnetic Laplacians and Hermitian embeddings
of directed graphs are a further, separate slice — real, but do not
fold into the first proposal under this item by default"), named as a
legitimate SGT-center extension by the strategy's 2026-08-19 scope
decision (`docs/1_STRATEGY.md`), and listed as an open (ungated)
standing candidate in the execution plan's handoff after the
primitive-power-convergence delivery. Selected per the empty
High/Medium Active priority table by the center-out policy: every
alternative standing candidate is gated — the directed *rate* layer on
a separate admission plus a named consumer, the wide-band minimax
filter designs on a named consumer, the computable sweep enumeration on
a consumer, Matrix–Tree/Kirchhoff on a named consumer — while this
slice's named external consumer already exists in backlog item 8's own
text ("directed community detection via the magnetic Laplacian — an
active area with no route into this backlog" before the scope
decision).

## Why this slice, and why now

The directed axis currently has two spectral toolkits, both real: the
symmetrized `directedNormalizedLaplacian` (structurally symmetric, but
QA-refuted PSD on directed input — the delivered calibration witness),
and the admitted Perron–Frobenius family (irreducible/primitive
nonnegative-matrix theory, no sign of *phase* structure). What neither
provides is the object the community-detection literature actually
consumes: a **Hermitian operator whose quadratic form measures phase
frustration** — how well a vertex phase assignment `x` can align with
edge fluxes `e^{iΘ_uv}` around cycles. That is the magnetic Laplacian
(Fanuel–Bolla–Alfaro; Crucoli–Pérez–Bungert–Van Mieghem for the
directed convention adopted here), and it is the shelf's first
complex-valued object.

The mathematical content of the first slice is deliberately the layer
every consumer needs and nothing beyond it:

1. the **operator** (Hermitian *by construction*, hypothesis-free);
2. the **magnetic energy identity** `x*Mx = ½ ∑ A_uv |x_u − e^{iΘ_uv} x_v|²`
   (the finite-algebra Dirichlet principle — hypothesis-free);
3. **PSD** on nonnegative weights (a corollary of 2);
4. the **gauge characterization** `x*Mx = 0 ↔ x_u = e^{iΘ_uv} x_v` on
   every positive edge (the balanced-potential condition; a frustrated
   cycle forces the kernel trivial — *spectral localization of flux*,
   delivered at form level with no complex spectral theorem);
5. the **cone agreements**: at Θ = 0 the complexified classical
   Laplacian (the join with the real shelf, through the symmetrized
   weights on asymmetric input), and on the symmetric/antisymmetric
   cone the single-W classical form `D − A∘e^{iΘ}`.

## Step 0: scope decisions (recorded before stating)

- **Convention (the Hermitian part).** With real weights `A` (possibly
  asymmetric — directed-native) and a real phase matrix `Θ` (arbitrary
  in the definitions; antisymmetry enters only through cone lemmas),
  define `W := A ∘ e^{iΘ}` entrywise and
  `M := D_sym − ½(W + Wᴴ)` with `D_sym := ½(diag(outDeg + inDeg))`.
  This is the Crucoli–Pérez–Bungert–Van Mieghem directed convention
  (off-diagonal `−½(A_uv e^{iΘ_uv} + A_vu e^{−iΘ_vu})`) and matches
  the fan-in/fan-out degree split the energy identity's diagonal
  demands. The alternative — the single-W form as the *definition* —
  would carry `A.IsSymm ∧ Θ = -Θᵀ` as definitional hypotheses;
  rejected for the same reason `directedNormalizedLaplacian` was: the
  Hermitian-part convention makes Hermitian-ness structural
  (`Matrix.IsHermitian` hypothesis-free) and puts the directed case at
  the center rather than the periphery.
- **Phases on the raw matrix.** `Θ` is any `Matrix V V ℝ`; the
  definition takes `e^{iΘ u v}` per entry. Antisymmetry is *not*
  assumed in the definitions — on the cone `(A.IsSymm ∧ Θᵀ = −Θ)` the
  single-W classical magnetic Laplacian is *derived*
  (`magneticLaplacian_eq_single`), mirroring how the directed
  normalized Laplacian derives its symmetric-cone agreement.
- **The sesquilinear form.** `hermQuadForm M x := ∑ i, conj (x i) *
  (M *ᵥ x) i : ℂ`, with realness on Hermitian `M` proved once
  (`hermQuadForm_im_eq_zero`). Mathlib's `Matrix.dotProduct` is
  bilinear, so the complex form needs its own one-line carrier; this
  is the shelf's `quadForm` analogue, not a reuse.
- **What is deliberately out of scope.** No eigenvalues of `M`, no
  complex spectral theorem, no magnetic Cheeger or synchronization
  bounds, no Heat-semigroup analogue. The pin *has*
  `Matrix.IsHermitian` spectral theory (`LinearAlgebra/Matrix/`
  `Spectrum.lean`, per the coverage map), so those are priced
  follow-ons, not obstructions.
- **Mathlib re-survey (pre-edit).** `Matrix.IsHermitian`
  (`Mathlib/LinearAlgebra/Matrix/Hermitian.lean:41`),
  `Complex.exp_mul_I` (`Mathlib/Data/Complex/Exponential.lean:643`),
  `Complex.normSq`/`normSq_nonneg`/`normSq_eq_zero`
  (`Mathlib/Data/Complex/Basic.lean:527,591,594`), and the
  `conjTranspose` algebra family
  (`Mathlib/Data/Matrix/ConjTranspose.lean`) all verified present in
  the pin. No magnetic/Hermitian-graph-laplacian content anywhere in
  the pin (the coverage map's Hermitian row is matrix-spectral-theory
  only).

## Step 1: the Lean content

New `Scaffold/Mathlib/GraphTheory/Magnetic.lean` (namespace
`SpectralGraphTheory`; minimal imports `GraphTheory.Spectral` +
`GraphTheory.Directed`; the umbrella importing it), all proved, zero
axioms:

- `magneticMatrix A Θ` — `W`, entrywise `A u v * exp (I * Θ u v) : ℂ`;
- `magneticLaplacian A Θ` — entrywise: `½ (outDeg A u + inDeg A u)` on
  the diagonal, `−½ (W u v + Wᴴ u v)` off;
- `magneticLaplacian_isHermitian` — **hypothesis-free**;
- `hermQuadForm` + `hermQuadForm_im_eq_zero` (realness on Hermitian
  input) + `hermQuadForm_conjTranspose` (the reflection identity the
  realness proof consumes);
- `magnetic_energy` — **hypothesis-free**:
  `hermQuadForm (magneticLaplacian A Θ) x = ½ • ∑ u v, (A u v : ℂ) *
  Complex.normSq (x u − exp (I * Θ u v) * x v)`;
- `magneticQuadForm_nonneg` — PSD at form level under `0 ≤ A`
  entrywise (stated on `.re`);
- `magneticQuadForm_eq_zero_iff` — the gauge characterization under
  `0 ≤ A`;
- `magneticLaplacian_zero_phase_eq_map` — Θ = 0: the complexified
  Laplacian of the symmetrized weights (on symmetric `A`, of
  `laplacian A` itself — the real-shelf join);
- `magneticLaplacian_eq_single` — on the `A.IsSymm ∧ Θᵀ = −Θ` cone,
  `M = D_ℂ − W` (the classical single-W magnetic Laplacian).

## QA plan (`Scaffold/QA/SpectralGraph/Magnetic_QA.lean`)

Four sections, exact arithmetic only (phases from `{0, π/2, π}` so
`e^{iθ} ∈ {1, I, −1}` by `exp_mul_I` + the `cos/sin` `π` lemmas):

1. **Positive/asymmetric witnesses** (the hypothesis-free content):
   the energy identity pinned numerically on the asymmetric directed
   star at a genuinely complex vector; Hermitian verified entrywise on
   asymmetric input with nonzero phases; the Θ = 0 agreement entrywise
   against the mapped `laplacian` (symmetric fixture) and the
   symmetrized-weights form (asymmetric fixture).
2. **Frustration vs consistency** (the gauge characterization's
   content): the triangle with one π-phase edge — the gauge condition
   forces `x = 0`, so the form is *positive definite* (the frustrated
   cycle is spectrally localized at form level, no eigenvalue
   machinery); against `K₂` with the same π flux — an antipodal kernel
   vector survives (consistent flux is free), the pair together
   exhibiting that the characterization discriminates.
3. **The classical bridge**: on the connected triangle at Θ = 0 the
   gauge `iff` holds exactly at the constant vectors (the complexified
   kernel of the classical Laplacian), cross-checked against the
   energy identity evaluated at a constant vector (zero).
4. **The nonnegativity fence**: symmetric *signed* input (one negative
   edge) with the gauge-vanishing test vector — PSD refuted in proved
   form (`¬ 0 ≤ re`), `hA : 0 ≤ A` isolated (the hypothesis-free form
   false, every other hypothesis of the PSD theorem vacuous), the
   signed-graph surface the fence marks.

## Pricing and follow-ons (priced, not gaps)

- The **complex spectral layer** (eigenvalues of `M`, magnetic
  Cheeger/λ₂-gap statements) consumes the pin's Hermitian spectral
  theorem and the energy identity — its own proposal when a consumer
  names a bound.
- The **gauge→component-constant** transport at Θ = 0 (walk induction
  over the support graph, the `Electrical` max-principle pattern) —
  QA here instantiates it on fixtures; the module-level general form
  is one walk-induction away if a consumer needs it.
- **Synchronization/frustration functionals** (`inf` over unit-modulus
  vectors of the energy) — the community-detection consumer itself.

## Delivery record

**Delivered 2026-08-25 (runs `20260825T001310Z-run-1` +
`20260825T021040Z-run-1`), zero new axioms (count stays 10; `#print
axioms` via `wip/mag_axcheck.lean` on all 39 accessible declarations —
14 public module, 8 QA fixture defs, 16 public QA theorems, plus the
two module-private helpers covered by the module building green:
`propext, Classical.choice, Quot.sound` only, every one). QA
2051 → 2067 (`Magnetic_QA` a new file at 16 by the generator metric,
30 declarations total).**

**Module** (`Scaffold/Mathlib/GraphTheory/Magnetic.lean`, namespace
`SpectralGraphTheory`, minimal imports `GraphTheory.Directed` +
`GraphTheory.Spectral`, the umbrella importing it): exactly the Step-1
list — `symDeg`, `magneticMatrix`, `magneticLaplacian`, `hermQuadForm`;
`magneticMatrix_isHermitian` (the cone lemma), **hypothesis-free**
`magneticLaplacian_isHermitian`, `magneticLaplacian_mulVec_apply` (the
action interface and energy engine), the two private expansion lemmas
(`normSq_sub_exp` — the per-edge `|z − e·w|²` split with the
conjugate-pair cross terms; `hermQuadForm_expansion`), **the energy
identity** `magnetic_energy` (hypothesis-free; the diagonal split into
out-/in-degree halves, the first cross sum matched termwise, the second
swapped and conjugated), `magnetic_energy_real` /
`magneticQuadForm_im_eq_zero` (realness), **PSD**
`magneticQuadForm_re_nonneg`, **the gauge characterization**
`magneticQuadForm_eq_zero_iff` (the `Finset.sum_eq_zero_iff_of_nonneg`
extraction both directions), and the cone agreements
`magneticLaplacian_zero_phase_apply`,
`magneticLaplacian_zero_phase_apply_of_isSymm`,
`magneticLaplacian_eq_single`.

**QA** (all four mandated sections): (A) the asymmetric fixture
(`magA = !![0,2;1,0]`, `Θ = π/π₂` mixed): `W`'s raw entries `−2`/`I`,
the operator's conjugate-pair off-diagonals `1 ± I/2`, Hermitian by
theorem on directed input, the energy identity pinned at `5` at
`![1,1]`, the zero-phase agreement entrywise against the mapped
`laplacian`, and the cone single-`W` form at the `π`-flux pair;
(B) **frustration vs consistency**: the one-`π`-edge triangle forces
`x = 0` through the gauge conditions (`magTri_frustrated`, with the
positive-definiteness corollary `magTri_frustrated_posdef`) while
`K₂` at the same flux keeps the antipodal potential `![1,−1]` in the
kernel (the iff's reverse direction, cross-checked by the raw
vanishing energy — every edge energy `e^{iπ}·(−1) = 1` cancelling
exactly); (C) **the classical bridge**: constants in the zero-phase
kernel, the antipodal vector outside it at energy exactly `4` — the
flux is what moved the kernel, joining sections B and C; (D) **the
nonnegativity fence**: the symmetric signed fixture `!![0,−1;−1,0]`
refutes PSD in proved form at `−1 < 0` with the PSD theorem's only
hypothesis — exactly the fence.

**Verification (continuation run):** `lake env lean` on the module
(zero diagnostics on the draft as left) and on the QA file after
fixing its three first-pass errors; `lake build` explicit targets ✔
(module; QA 2192/2192); the root `lake build` ✔ (2264 targets, "Build
completed successfully"; zero warnings in the changed modules — the
log's only Scaffold diagnostics the documented pre-existing set);
`lint_axioms` (**10**, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**2067/10/0**,
idempotent).

**Pin-technique list (QA, from the verification pass):**

- the `Fin 2`/`Fin 3` `match u, v with` exhaustion needs each diagonal
  alternative exactly once — a copy-pasted duplicate is a *redundant
  alternative error*, not a warning (delete it; the `absurd rfl huv`
  arms for the zero-weight diagonals stay);
- the recurring false-numeric-pin mode, caught exactly as numeric QA
  exists to catch: the drafted zero-phase energy of `![1,−1]` on `K₂`
  said `2` (a docstring arithmetic slip `½[|1−1|² + |−1−1|²]` that
  drops a sign inside the first absolute value); `norm_num` evaluated
  the double sum to `4` and reduced the goal to `False` — the fix is
  the statement (`= 4`), not the proof;
- phases from `{0, π/2, π}` evaluate via a private `magExp_eq`
  (`exp_mul_I` + `ofReal_cos/sin` rewrites) and its four evaluated
  corollaries, with the `/2`-inside-`ofReal` pushed by
  `push_cast [Complex.ofReal_div]` before `rfl` — writing
  `((Real.pi : ℂ) / 2)` directly in the lemma avoids the push at the
  use sites;
- the `hermQuadForm`-at-`![1,1]` energy pins evaluate by
  `norm_num [fixture, Matrix.cons_val_*, Matrix.head_cons, magExp_*,
  Complex.normSq_apply]` in one shot once every phase is an evaluated
  constant.

**Priced follow-ons (recorded, not started):** the complex spectral
layer (eigenvalues of `M` through the pin's Hermitian spectral
theorem, magnetic Cheeger, `λ₂`-gap statements) — its own proposal when
a consumer names a bound; the gauge→component-constant transport at
`Θ = 0` as a module-level walk induction (QA here instantiates it on
fixtures); synchronization/frustration functionals (`inf` over
unit-modulus vectors) — the community-detection consumer itself.
