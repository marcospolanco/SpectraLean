# Proposal: Discharge Davis–Kahan / Weyl / Cheeger Hard Direction

**Status:** Weyl **delivered** (2026-08-20) and **Davis–Kahan
delivered** (2026-08-21 — Step 0 surveyed, then both Step-1 components
executed as the recorded two-component split, with the retirement at
the unchanged statement; explicit axioms 11 → 10). The Cheeger hard
direction **Step 0 survey landed 2026-08-22: positive-with-large-cost**
— the standard co-area/Cauchy–Schwarz route closes with exactly the
axiom's constants, the assembly skeleton and the pure-algebra component
are spike-verified green, and the remaining content decomposes into
three bounded components (recorded below). **Step 1a delivered
2026-08-23** (the pure-algebra component — Component A, the fused
median-part contraction, the normalization — zero new axioms, plus a
recorded constant-budget correction to the survey's step-5/6 route; see
the delivery record below the Open next step). Step 1b (the co-area
crux) is the next dedicated run per the Davis–Kahan precedent. Priority
**Medium**. Authorizes no axiom admissions or external publication.

Companion to `docs/2_ARCHITECTURE.md` §9 (upstream-replacement lifecycle)
and this session's precedent of axiom retirements (Courant–Fischer,
Cauchy interlacing, Cheeger easy direction, Sherman–Morrison, Woodbury) —
this is the same category of work, shrinking the mushy center rather than
growing the hard crust into new territory.

## Clean-room boundary

Internal prioritization and analysis. If counsel approves a public
repository export, restate from the standard operator-perturbation-theory
literature (Davis & Kahan; Bhatia). Do not copy this proposal verbatim.

Assessed from `Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/
{Weyl,DavisKahan}.lean` and `Scaffold/Mathlib/GraphTheory/Cheeger.lean`
(all three axioms confirmed present, exact statements read directly,
2026-08-19), `Spectral.lean`'s `evals_min_max` (the general Courant–Fischer
engine, proved 2026-08-18), and a 2026-08-19 spot-check into
`.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/{Spectrum,
ContinuousFunctionalCalculus/Order}.lean`.

## External consumer

The single most load-bearing classical result among this repository's
admitted axioms: Davis–Kahan sin-Θ is the standard eigenvector
perturbation bound behind spectral clustering stability arguments and PCA
robustness theory generally; Weyl's inequality is used anywhere
eigenvalues need to be bounded under perturbation, in numerical linear
algebra broadly.

## The ask, precisely

Not "add an axiom" — **discharge one already admitted.** Three separate
targets, not one bundled effort:

1. `weyl_inequality` (`Weyl.lean:60`): for symmetric `A, E` and every
   sorted index `i`, `|evals (hA.add hE) i − evals hA i| ≤ ‖E‖` (ℓ²
   operator norm).
2. `davis_kahan_sin_theta` (`DavisKahan.lean:64`): the sin-Θ eigenvector
   perturbation bound.
3. `cheeger_lower_bound` (`Cheeger.lean:88`): the hard direction of
   Cheeger's inequality (regular graphs).

If any turns out to be out of reach, **the axiom stays, and stays
visible** — per the original assessment's own honesty, this is an
improvement attempt, not a correction owed. Do not weaken this into
admitting a restated or narrower version to claim partial credit.

## Why the three are not equally tractable — do not treat them as one problem

**Update (2026-08-19): the norm bridge Weyl needs is now proved — this
section originally flagged a lead, `resolvent-calculus-psd.md`'s own
Step 0 has since resolved it, both ways.** That proposal's Step 0 spiked
the exact C*-algebra thread named below and found it **structurally
inapplicable** to real matrices, elaboration-verified: `CStarAlgebra`
requires `NormedAlgebra ℂ A`, and real matrices are not a complex
algebra — not an instance-search gap a different search could close.
The two proposals were right to expect they'd need the same bridge; they
were wrong to expect the C*-algebra route would supply it.

**But that proposal's own contingency fired, and the fallback is exactly
what this proposal needs.** `resolvent-calculus-psd.md` delivered a
from-scratch finite-dimensional bridge instead, in the new module
`Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent`:
`l2OpNorm_eq_max_abs_evals` — `‖M‖ = max |evals hM 0| |evals hM last|`
for symmetric `M` — proved from the already-shelf eigenbasis machinery
(`toEuclideanCLM`, Parseval, `ContinuousLinearMap.opNorm_le_bound`), no
axioms. This is precisely `λ₁(E) ≤ ‖E‖` / `λₙ(E) ≥ −‖E‖` in one packaged
identity — the operator-norm-to-eigenvalue bridge Weyl's admitted axiom's
own docstring says it's built from. **Weyl's Step 0 is now mostly done as
a side effect of a sibling proposal, not something to re-spike from
scratch.** What remains is composing `l2OpNorm_eq_max_abs_evals` with
the *additive* Weyl bound from `evals_min_max` (a subspace-intersection
argument, likely nearly identical in shape to the already-delivered
Cauchy-interlacing proof) — genuinely closer to Step 1 than Step 0 now.

**Davis–Kahan is genuinely unclear.** Nothing surveyed so far suggests a
comparable shortcut; treat it as "large" as originally rated, with its
own from-scratch tractability question, not assumed to ride along with
Weyl's finding.

**The Cheeger hard direction is known-hard, not merely unexplored.** This
is textbook-established: unlike the easy direction (already proved this
session via a variational argument), the hard direction requires a
genuinely different constructive/combinatorial argument (a sweep-cut or
similar), not a Courant–Fischer corollary. Do not expect this proposal's
Weyl-side optimism to transfer here.

## Build order

### Step 0: Tractability survey (mandatory; the whole gate)

**Weyl — surveyed 2026-08-20, decisive positive.** The additive bound
was spiked exactly as this section directs, before any Step 1 edit, and
the proposal's caution was vindicated in both directions:

- The additive bound is **not** a free corollary of the norm bridge. It
  consumes *both* Courant–Fischer witness directions
  (`exists_submodule_forall_rayleigh_le` for the upper bound — the
  witness subspace for `A` is exhibited as a member of the competitor
  set defining `λᵢ(A+E)` through `evals_min_max`;
  `exists_ne_mem_rayleigh_ge_of_finrank_eq` for the lower — the
  competitor direction for `A` run inside the witness subspace for
  `A+E`), plus *both* Rayleigh domination bounds: the top half from the
  EML step's `quadForm_le_evals_last` and the bottom half from the new
  mirror `evals_first_mul_dotProduct_le_quadForm` (added to
  `GraphTheory.Spectral` with this delivery — it did not exist).
- Composition with `l2OpNorm_eq_max_abs_evals` is then exactly as
  predicted: `‖E‖ = max |λ₁(E)| |λₙ(E)|` turns the additive window into
  the spectral-norm statement in two `linarith` steps, with the bridge's
  `1 ≤ card V` hypothesis covered by vacuity (`Fin 0` has no index).
- **Cost estimate for the full statement (the recording this section
  requires):** ~120 lines of Lean — three private translation lemmas
  (Rayleigh↔multiplication form both directions; a local
  `quadForm_add'` copy, since the generic one lives in the outer
  `GraphTheory.Expander` module this perturbation module must not
  import), two public additive-bound theorems, and the composed
  retirement theorem. Verified end-to-end in a scratch spike before any
  module was edited; the spike then transferred to
  `Perturbation/Weyl.lean` essentially verbatim.

**Davis–Kahan — surveyed 2026-08-21, decisive positive-with-large-cost;
the route is named and its primitives are spike-verified.** The paper was
read in full (arXiv:1405.0680, YWS "A useful variant of the Davis–Kahan
theorem for statisticians"); findings, all recorded before any Step-1
edit:

- **Citation mislocation found and repaired.** The axiom's provenance
  note cited "YWS Theorem 2 (two-sided separation, projector form,
  constant 1)" — a locator/constant pairing that does not exist in the
  paper. YWS's actual Theorem 2 is a *population-gap* result with
  constant 2 (`‖sinΘ‖_F ≤ 2 min(d^{1/2}‖E‖_op, ‖E‖_F)/min(gap)`, proved
  via Weyl + Wielandt–Hoffman + a Kronecker/vec Sylvester separation).
  The repo's statement — mixed cross-gap `λ_{k+1}(A+E) − λ_k(A)`,
  operator norm on the projector difference, constant 1 — is YWS
  **Theorem 1** (the classical Davis–Kahan restatement; the paper notes
  the operator-norm variant) specialized to the bottom cluster, the
  single-pair δ reduction by sortedness still valid. Docstring,
  `index/sources/davis_kahan_1970.md`, `index/map/perturbation.md`, and
  `docs/2_ARCHITECTURE.md` §12 corrected 2026-08-21; the axiom statement
  itself is unchanged and remains true (constant-1 tightness was
  re-verified numerically at the 2×2 rotation family during the survey:
  sinθ ≈ 0.0985 vs bound ≈ 0.0990 at t = 0.1, asymptotically attained).
- **Why the cheap route cannot discharge the exact statement.** The
  entrywise eigenbasis-coordinate identity
  `(λ̂ᵢ − λⱼ)·⟨vⱼ, ûᵢ⟩ = −⟨ûᵢ, E vⱼ⟩` (from `M *ᵥ vⱼ = λⱼ vⱼ` and
  symmetry — both sides shelf-provable today) is available over the
  cleanly side-separated pairing (A's lower cluster vs (A+E)'s upper
  cluster, gap exactly δ, no Weyl loss), but summing it gives only the
  Frobenius shape with constant √(k+1) — exactly the `d^{1/2}` numerator
  of YWS Theorem 2. The operator-norm constant-1 statement additionally
  requires either the Schur/Sylvester operator-norm bound (false in
  general) or an integral representation.
- **The route that works: Duhamel/exponential integral.**
  `(I−Q)P = ∫₀^∞ e^{-tÃ}(I−Q) E e^{tA} P dt`, where `P` is A's
  lower-cluster projector, `Q` the same for `Ã = A+E`. The mixed gap is
  *side separation* (Ã's upper cluster `≥ b = λ_{k+1}(Ã)`, A's lower
  cluster `≤ a = λ_k(A)`, `b − a ≥ δ`), which makes the integrand decay
  at rate `e^{-tδ}` and the integral converge to the boundary value
  `(I−Q)P` at `t = 0`. Norm: `‖(I−Q)P‖ ≤ ∫₀^∞ e^{-tδ}‖E‖ dt =
  ‖E‖/δ` — **constant 1, operator norm.** No `Matrix.exp` needed: the
  semigroups live at vector level as damped eigenbasis expansions.
- **A cheaper algebraic technique exists for a related but distinct
  statement — checked against this axiom's exact hypothesis and found
  NOT to substitute for the Duhamel route; recorded so no future run
  re-derives this.** A standard textbook packaging (Vershynin,
  *High-Dimensional Probability*, 2018, Thm 4.1.15–4.1.16 —
  `index/sources/vershynin_hdp.md`) proves the product-projector bound
  `‖QP‖ ≤ ‖A−B‖/δ` by a purely algebraic commutator/shift argument: no
  integral, no `HasDerivAt`, no differentiability API — only that a
  self-adjoint operator commutes with its own spectral projections and
  that spectral projections are contractive. Center both spectra at a
  point `c`; if `P`'s selected eigenvalues lie within `r` of `c` and
  `Q`'s selected eigenvalues lie at least `r+δ` from `c`, two one-line
  norm inequalities combine to `δ‖QP‖ ≤ ‖A−B‖` — and `r` cancels out of
  the *final* bound algebraically, which is what makes the technique look
  free. **The catch, worked through by hand before writing this down:**
  `r` cancelling in the final step does not mean `r` is unconstrained —
  a *single* finite `r` must satisfy both containment conditions
  simultaneously, and `davis_kahan_sin_theta`'s `P` (`initialProjector`)
  selects the entire half-line `(−∞, evals hA k]`, not a bounded window.
  That forces `r` up to the *full spread* of `A`'s lower cluster
  (`evals hA k − evals hA 0`, a number the spectrum determines and the
  axiom's hypothesis does not bound), while the separation condition
  needs `r ≤ (evals hAE ⟨k+1⟩ − evals hA k) − δ`. Satisfying both requires
  the actual gap to exceed `δ` by the *entire lower-cluster spread* — a
  strictly stronger hypothesis than `hsep : δ ≤ evals hAE ⟨k+1⟩ −
  evals hA k`, which bounds nothing about the spread below the threshold.
  Duhamel does not have this limitation because it uses the *local*
  decay rate `e^{-tδ}` rather than a fixed global containment radius —
  which is presumably why it, not the shift trick, is the route that
  closes the exact half-line statement.
  **Do not substitute this technique into Step 1** — doing so would
  require either weakening `davis_kahan_sin_theta`'s hypothesis (Step 1's
  own contract below forbids restating the axiom more narrowly to make it
  easier) or changing the conclusion to a bounded spectral window instead
  of a half-line threshold, neither of which is a valid discharge of the
  existing axiom.
  **What it is genuinely good for, as separate future work (not part of
  Step 1 or Step 2):** a *bounded-window* ("band") Davis–Kahan theorem —
  both `P` and `Q` are finite spectral windows, `δ`-separated — is a
  different, new, axiom-free statement this technique proves cheaply with
  no calculus at all, and it would compose naturally with the just-delivered
  `GraphTheory.Band` program (Steps 1–4, 2026-08-20/21). Recorded as
  backlog item 9 in `docs/6_SGT_BACKLOG.md`; it needs its own proposal
  entry and Step-0 survey before any Lean is written, and is not
  authorized inside a Davis–Kahan Step-1/2 run.
- **Spike-verified primitives** (`wip/dk_spike.lean`, all proved with
  only `propext, Classical.choice, Quot.sound`): the vector-level heat
  semigroup `heatApply t x = ∑ i e^{-tλᵢ}(vᵢ ⬝ᵥ x) vᵢ`; its expansion/
  adjoint workhorse and **Parseval damping**
  (`‖heatApply t x‖² = ∑ e^{-2tλᵢ}(vᵢ⬝ᵥx)²`); its **eigenaction**
  (`M *ᵥ heatApply t x` through the shelf's
  `mulVec_eigvecOf_sum_apply`); **differentiability in `t`** under the
  finite sum (`HasDerivAt`, this pin's `HasDerivAt.sum`/`HasDerivAt.exp`
  from `Analysis.Calculus.Deriv.Add`/`Analysis.SpecialFunctions.ExpDeriv`);
  and the **reducing commutation** `spectralProjector M hM c * M =
  M * spectralProjector M hM c` (entrywise double-sum through
  `Matrix.IsSymm.apply` + the eigenvector action) plus its `mulVec`
  form. Cost for these: ~250 spike lines, essentially transferable.
- **The two genuinely new components, with cost estimates:** (1) the
  **equal-rank projector identity** `‖P − Q‖ = ‖(I−Q)P‖` for orthogonal
  projectors of equal rank (principal angles) — REQUIRED for constant 1:
  Duhamel directly bounds `‖(I−Q)P‖`, and the alternative (bounding
  `‖(I−P)Q‖` by the reverse cross-gap) degrades through Weyl to
  `δ − 2‖E‖`. Naive `(P−Q)²` decompositions were checked by hand and
  fail (a 2×2 counterexample to the tempting
  `(P−Q)² = P(I−Q)P + Q(I−P)Q` identity was worked out); the
  principal-angles/CS route is the honest one — moderate-large, the
  least-predictable piece. (2) the **FTC assembly** — scalar pairing
  `⟨y, e^{-tÃ}(I−Q)E e^{tA}P x⟩`, derivative via the spike's
  differentiability + commutation, improper integral over `[0,∞)` with
  the `e^{-δt}` decay bound (cluster-filtered Parseval damping; scalar
  `intervalIntegral` FTC) — moderate, mostly analysis-API friction.
- **Step-1 cost estimate (the recording this section requires):**
  600–1000 lines over 2–3 runs — spike transfer (~250), the two new
  components above, the cluster-filtered norm corollaries, and QA. This
  is the largest single retirement this proposal contemplates; it should
  be a dedicated run (or a two-component split: the equal-rank lemma
  first as its own hard-crust delivery, then the Duhamel assembly),
  not bundled with survey work.

**Cheeger hard direction — surveyed 2026-08-22, decisive
positive-with-large-cost; the route is reconstructed with tight
constants and its load-bearing components are spike-verified green.**
Findings, all recorded before any Step-1 edit (the survey was run under
the known-hard working assumption as instructed; the positive verdict
is a finding, not an assumption — every assembly dependency below was
read at its exact statement and the cheap components were proved, not
sketched, in the git-ignored spike `wip/cheeger_spike.lean`):

- **The reduction that makes it tractable: no eigenvector, no
  spectral-side work at all.** The shelf's proved
  `secondEval_variational` (`Spectral.lean:1745`) states
  `λ₂(M) = sInf {R_M(x) | x ≠ 0, x ⊥ 1}` for PSD `M` with `M *ᵥ 1 = 0`
  — and *both* of `M = regularNormalizedLaplacian A d`'s side
  conditions are already proved in `Cheeger.lean`
  (`regularNormalizedLaplacian_psd`,
  `regularNormalizedLaplacian_mulVec_onesVec`). So the theorem reduces,
  via `le_csInf` (`ConditionallyCompleteLattice/Basic.lean:187`, the
  same call shape `cheegerConstant`'s own proof uses), to one **sweep
  lemma**: for every `x` with `x ≠ 0` and `x ⬝ᵥ 1 = 0`,
  `φ²/2 ≤ R_{L_sym}(x)`. The whole assembly skeleton is spike-verified
  end-to-end in hypothesis form (`CheegerSpike.assembly_skeleton`,
  `#print axioms`: the standard three only) — including the sInf-set
  nonemptiness witness (the `Pi.single u 1 − Pi.single v 1` vector the
  variational proof itself uses, `hcard` supplying the two distinct
  vertices).
- **The sweep lemma's proof, with the constant budget verified by hand
  twice.** Let `E'(y) := ∑ i j, A i j (y i − y j)²` (so
  `E' = quadForm (laplacian A)` by the proved `laplacian_quadForm`,
  and `R_{L_sym}(x) = E'(x) / (d · ‖x‖²)` for `x ≠ 0` via the proved
  `quadForm_regularNormalizedLaplacian`). Take a median `m` of the
  values of `x` (exists on the finite value multiset: `|{x > m}| ≤ n/2`
  and `|{x < m}| ≤ n/2`) and split `x − m·1 = u − v` into
  `u := (x − m)⁺`, `v := (m − x)⁺`. Then:
  1. *Level sets are minority-side by construction:* every nonempty
     level set of `u` sits inside `{x > m}` and every nonempty level
     set of `v` inside `{x < m}`, so each has cardinality `≤ n/2 =`
     volume-minority under `d`-regularity (`vol_eq_of_regular`,
     proved); both complements are nonempty (each side of the median
     holds `< n` vertices, `n ≥ 2`), so every level set is a
     nonempty proper subset and `conductance_ge_cheegerConstant`
     (proved) applies: `boundary ≥ φ · d · |level set|`.
  2. *Co-area core (the one genuinely new component):* weighted
     layer-cake against the FTC identity
     `∫_{a}^{b} 2t dt = b² − a²` gives, for each part `y ∈ {u, v}`:
     `½ ∑_{i j} A i j |y i² − y j²| ≥ φ · d · ∑ i y i ²` — each
     crossing pair `(i, j)` contributes its exact squared-value gap,
     and the per-level conductance bound converts crossing weight into
     minority-side mass.
  3. *Cauchy–Schwarz core (spike-proved at final shape,
     `CheegerSpike.core_sum_abs_sq_sub_sq`, axiom-clean):*
     `(∑_{i j} A i j |y i² − y j²|)² ≤ E'(y) · (4 ∑ i deg i · y i²)`
     — via `Finset.sum_mul_sq_le_sq_mul_sq` over the product type
     `V × V` with the pointwise factorization
     `|a² − b²| = |a − b| · |a + b|` (needs `0 ≤ A` for the
     `√A · √A = A` regrouping; the `(a+b)² ≤ 2a² + 2b²` side needs
     `IsSymm` — the cross double sum's column sums must match `deg`'s
     row sums. Recorded as a statement guard for Step 1: Component A
     carries `hA`, not just `hnonneg`).
  4. *Combine per part:* `φ² · d · ‖y‖² ≤ E'(y)` for each of `u`, `v`.
  5. *Contraction (pointwise lemma spike-proved, `abs_posPart_sub`,
     axiom-clean):* `|max (a − m) 0 − max (b − m) 0| ≤ |a − b|`, so
     `E'(u) ≤ E'(x − m·1) = E'(x)` (translation invariance is a
     `ring`-level summand identity) and likewise `E'(v) ≤ E'(x)`.
  6. *Norm split — the step that makes the constants tight:* `u v = 0`
      pointwise gives `‖u‖² + ‖v‖² = ‖x − m·1‖² = ‖x‖² + n m² ≥ ‖x‖²`
      (the cross term dies by `x ⊥ 1`). Summing 4 over both parts:
      `φ² d (‖u‖² + ‖v‖²) ≤ E'(u) + E'(v) ≤ 2 E'(x)`, hence
      `φ² d ‖x‖² ≤ 2 E'(x) = 2 d R ‖x‖²`, i.e. **`φ²/2 ≤ R`** — the
      factor 2 from carrying *both* median parts is exactly the
      statement's `/2`; nothing is lost anywhere in the chain.
      **[Correction, 2026-08-23, found by the Step-1a run's pre-edit
      re-derivation: steps 5–6 as written here are NOT the tight route.**
      Step 5's summation `E'(u), E'(v) ≤ E'(x)` summed to `2 E'(x)` is
      loose by exactly the factor `2` the conclusion spends, and step
      6's normalization `E'(x) = d R ‖x‖²` omits the `/2` of
      `laplacian_quadForm` (`E'` = the ordered double sum = twice
      `quadForm (laplacian A)`); as written the two errors cancel,
      which is why this writeup passed two hand checks. The tight route
      — delivered 2026-08-23 as Step 1a — takes step 5 as the *fused
      pair-summed* pointwise contraction
      `(max (a−m) 0 − max (b−m) 0)² + (max (m−a) 0 − max (m−b) 0)² ≤
      (a−b)²`, whose cross-edge slack `(u+v)² ≥ u²+v²` pays for
      carrying both parts (giving `E'(u) + E'(v) ≤ E'(x)` directly, not
      `≤ 2 E'(x)`), and states the normalization honestly as
      `R = E'/(2 d ‖x‖²)`; then `φ² d ‖x‖² ≤ E'(x) = 2 d R ‖x‖²`
      exactly. Steps 1b/1c must use these shapes — see the Step-1a
      delivery record below the Open next step.]
- **Why no cheaper route exists (recorded so no future run re-derives
  it).** The half-volume obstruction is real: for `x ⊥ 1` the
  positive part `x⁺` can have majority support with majority norm
  (e.g. `x = (2,2,2,2,2,−1,−1,−1)` on 9 vertices), and for such
  level sets `min(vol S, vol Sᶜ)` counts the *complement* — the naive
  "integrate `|S_t|` over all `t`" bound is false there. The median
  split is precisely what routes both parts to their own minority
  side; and the norm split shows the two parts jointly carry the full
  norm (plus `n m²`), which is why splitting loses nothing. The
  eigenvector-based variants of the proof (sweep of the λ₂-eigenfunction
  directly) are strictly harder here: they additionally need an
  eigenvector-existence and `-⊥-1` interface the sInf reduction makes
  unnecessary.
- **Spike-verified pin facts** (`wip/cheeger_spike.lean`, all
  declarations `#print axioms`-clean at `propext, Classical.choice,
  Quot.sound`): `Finset.sum_mul_sq_le_sq_mul_sq`
  (`Algebra/Order/BigOperators/Ring/Finset.lean:197`) applies directly
  over the product Fintype; `Fintype.sum_prod_type'`
  (`Data/Fintype/BigOperators/BigOperators`-family) is the double-sum
  ↔ product-sum bridge (direction trap: the `'` variant runs
  `∑ i ∑ j → ∑ p`); the interval-integral FTC primitive
  `∫ t in a..b, 2t = b² − a²` is provable from
  `integral_congr` + `integral_smul` + `integral_id`
  (`Analysis/SpecialFunctions/Integrals.lean:406`) — with two pin
  traps recorded: `integral_congr` takes `Set.EqOn f g (Set.uIcc a b)`
  (not the ∀-membership form), and the `intervalIntegral.*` dotted
  names race against the root-level *function* `intervalIntegral`
  (the exported integral), so `open intervalIntegral` with bare names
  is the robust form. `Real.mul_self_sqrt` (`√x * √x = x`) is the
  regrouping lemma; `Real.sqrt_mul_self` at this pin is the *different*
  statement `√(x * x) = x`. `Matrix.IsSymm.apply hA j i : A i j = A j i`
  (argument convention swapped relative to expectation).
- **The missing pin lemma, found and priced:** this Mathlib snapshot
  has **no finite-sum/interval-integral interchange** (no
  `intervalIntegral.integral_sum`; the `Bochner.lean` `integral_sum`
  is measure-valued). The co-area Fubini step therefore needs a hand
  Finset induction over `integral_add` with `IntervalIntegrable` side
  conditions (bounded indicator functions on bounded intervals —
  each summand is integrable, so `intervalIntegrable` follows). ~30
  lines of friction, priced into Step 1b below.
- **Step-1 cost estimate (the recording this section requires):
  550–900 lines over 2–3 dedicated runs**, the largest single
  retirement remaining in this proposal, decomposed as:
  - **Step 1a (pure algebra, low risk — entirely spike-verified
    already):** Component A at its final public shape, the
    contraction lemma summed to `E'`, translation invariance, the
    `R = E'/(d‖x‖²)` normalization. ~150–250 lines + QA (the K₂
    equality pin `φ = d = P₂ = 1` and a strict case).
  - **Step 1b (the crux, moderate-high risk):** the co-area core —
    for `y ≥ 0` whose nonempty level sets are all minority-side,
    `½ ∑ A |y i² − y j²| ≥ φ d ∑ y i²` — by the interval-integral
    encoding (per-pair FTC + Fubini + per-level conductance;
    level sets as `Finset.filter`). ~250–400 lines + QA. This is
    the least-predictable piece, the analogue of Davis–Kahan's
    equal-rank lemma.
  - **Step 1c (median + assembly, moderate risk):** median existence
    over the value multiset (`Finset.sort` + `get`), the level-set
    cardinality facts, the degenerate cases (`m = max` or `m = min`
    making one part identically zero), the norm split, and the final
    arithmetic composing with the Step-0 skeleton. ~150–250 lines +
    QA.
  Constant-checking discipline carried forward: before Step 1's
  statements are frozen, pin the chain numerically on a hand example
  (the K₂ edge at equality and a strict C₄/P₃ case) — this repository
  has been burned by a false Cheeger shape before
  (`old_cheeger_lower_bound_refuted_QA`), and the survey's hand
  verification, however careful, is not a proof until Lean checks it.

Per-axiom order as originally written:

1. **Weyl.** ~~The norm bridge is delivered — reuse
    `l2OpNorm_eq_max_abs_evals` from `Analysis.OperatorTheory.Resolvent`
    directly; do not re-spike the C*-algebra route (confirmed dead above).
    What remains: spike the *additive* Weyl bound from `evals_min_max`
    (do not assume the norm bridge makes the additive bound free too —
    check it on its own), then compose the two. Record a real cost
    estimate for the full statement once the additive spike is done.~~
    **Done — see above and the delivery record below.**
2. **Davis–Kahan.** ~~Survey what the sin-Θ bound's standard proof actually
    needs (typically: the norm bridge above, plus a resolvent-based or
    variational argument relating the perturbed and unperturbed
    eigenspaces) against what's on the shelf. Record findings even if
    negative. Note added 2026-08-20: the shelf gained since the original
    writing — the resolvent identity, the norm/Lipschitz resolvent
    bounds, and the resolvent-map injectivity are all proved in
    `Analysis.OperatorTheory.Resolvent`, and Weyl itself is now proved —
    but no survey of what a sin-Θ proof needs has been run, so "large"
    stands.~~ **Done 2026-08-21 — see the survey record above:
    positive-with-large-cost; the Duhamel route's primitives are
    spike-verified; Step 1 estimated at 600–1000 lines over 2–3 runs,
    with the equal-rank projector identity and the FTC assembly as the
    two new components.**
3. **Cheeger hard direction.** ~~Survey the standard sweep-cut argument's
    Lean cost specifically — this is the one where "known-hard" should be
    treated as the working assumption unless the survey finds otherwise,
    not spiked with the same optimism as Weyl.~~ **Done 2026-08-22 — see
    the survey record above: positive-with-large-cost (550–900 lines over
    2–3 runs, the co-area core as the crux); the assembly skeleton and
    the pure-algebra component are spike-verified green with the exact
    statement constants reconstructed and checked.**

Record all three findings in this document before any Step 1 begins on
any of the three axioms — they may be pursued independently once
surveyed (this is not a single bundled effort).

### Step 1 (per axiom, only after that axiom's Step 0 survey is positive)

Prove the axiom's exact existing statement — same name, same hypotheses,
same conclusion — via whichever route Step 0 found. Do not restate the
theorem more narrowly to make it easier; a narrower proved theorem is not
a valid discharge of the existing axiom (the `sherman_morrison`/
`woodbury_identity` retirements are the precedent for "same shape,
now proved").

**Weyl Step 1 — DELIVERED 2026-08-20.** `weyl_inequality` retired from
admitted axiom to proved theorem in `Perturbation/Weyl.lean` at the
unchanged name, hypotheses, and conclusion (explicit axioms 13 → 12),
exactly along the surveyed route:

- the two public additive bounds `weyl_additive_upper` /
  `weyl_additive_lower` (`λᵢ(A) + λ₁(E) ≤ λᵢ(A+E) ≤ λᵢ(A) + λₙ(E)`,
  symmetry-only, every sorted index) — reusable hard-crust interfaces in
  their own right;
- the composed retirement `theorem weyl_inequality` (additive window →
  norm bridge), `#print axioms` reading only `propext,
  Classical.choice, Quot.sound`;
- `spectral_gap_stability` is unchanged code and now fully hard crust;
- the derived consumers shed the axiom dependency without recompilation
  changes: `davisKahanTwoPoint` is conditional on
  `davis_kahan_sin_theta` alone, `eventStreamProjectorDrift` on two
  axioms instead of three (both verified by `#print axioms`);
- QA per this proposal's plan: the existing `Weyl_QA` fixtures kept
  (zero-perturbation instances), plus the required non-vacuity witness
  and more — the nonzero fixture `A = E = !![2,1;1,2]` with both spectra
  pinned independently (trace/determinant/sortedness) and `‖E‖ = 3`
  through the proved bridge: the bound **attained exactly** at the top
  index (`|6−3| = 3 = ‖E‖`), **strict** at the bottom (`1 < 3`), both
  additive bounds instantiated at both indices, and the
  **window-endpoint guard** — the upper additive bound with `λ₁(E)` in
  place of `λₙ(E)` refuted (`6 ≤ 4` is false), so the window's
  endpoints are load-bearing and not interchangeable.

## QA plan

Per discharged axiom: reuse the existing QA file's fixtures (`Weyl_QA.lean`
etc. — survey what already exists before adding new ones), plus at least
one negative witness confirming the bound is not vacuously true (e.g., a
nonzero perturbation where the bound is strict, not just satisfied at
equality trivially).

## Operating instructions for an autonomous run

- Step 0 is mandatory and per-axiom; do not begin Step 1 on any axiom
  before that axiom's own survey is recorded.
- **No new axioms, and no restated/narrower replacement axioms.** If a
  survey finds an axiom out of reach, record the precise obstruction in
  `docs/6_SGT_BACKLOG.md` and leave the existing axiom exactly as is —
  visible, cited, unchanged.
- Pursue the three axioms independently; a positive finding on Weyl does
  not authorize assuming Davis–Kahan or the Cheeger hard direction are
  similarly reachable.
- Survey Mathlib precisely (exact instance and lemma signatures, not just
  names) before writing any Scaffold statement — the C*-algebra thread
  above is a lead, not a confirmed asset.

## Open next step

**Cheeger hard-direction Step 1b** (the co-area core — the crux, its own
dedicated run per the Davis–Kahan precedent): for `y ≥ 0` whose
nonempty level sets are all minority-side,
`½ ∑ i j, A i j * |y i² − y j²| ≥ φ * d * ∑ i, y i²`, by the
interval-integral encoding (per-pair FTC + the hand Finset-induction
Fubini, since this pin has no finite-sum/interval-integral interchange —
the ~30-line friction priced in the survey) + per-level conductance
(level sets as `Finset.filter`). Its composition with the delivered
Component A is the per-part bound `φ² * d * ‖y‖² ≤ E'(y)` (ordered
convention) — Step 1c consumes it through the delivered *fused*
contraction and normalization, per the corrected constant budget
recorded in the Step-1a delivery note below (do **not** follow the
survey's original step-5/6 summation route — it is loose by exactly the
factor `2` the statement spends; the 1a correction record has the
tight shapes). Then Step 1c (median + assembly) retires
`cheeger_lower_bound` at the unchanged statement.

**Cheeger hard-direction Step 1a — DELIVERED 2026-08-23** (the
pure-algebra component, zero new axioms, count stays 10; `#print
axioms` on every new public theorem and QA headline reads only
`propext, Classical.choice, Quot.sound`):

- `GraphTheory.Cheeger` gained, in a new "hard direction Step 1a"
  section: **Component A** `core_sum_abs_sq_sub_sq` (transferred
  verbatim from the survey spike — the Cauchy–Schwarz core at final
  shape with the `IsSymm` statement guard), the scalar **fused
  median-part contraction** `sq_posPart_sub_add_sq_negPart_sub_le`
  (`(max (a−m) 0 − max (b−m) 0)² + (max (m−a) 0 − max (m−b) 0)² ≤
  (a−b)²`) with its summed form `sum_edgeWeight_sq_posPart_add_sq_
  negPart_le` (`E'((x−m)⁺) + E'((x−m)⁻) ≤ E'(x)`, nonneg weights only,
  no symmetry), the regularity bridge `sum_deg_mul_eq_of_regular`
  (`∑ deg·f² = d·∑f²`), and the **normalization**
  `rayleigh_regularNormalizedLaplacian_eq`
  (`R(x) = E'(x) / (2·d·‖x‖²)` for `x ≠ 0`).
- **Route correction over the survey record, found before any statement
  was frozen (the run's pre-edit constant re-derivation):** the survey's
  step 5 as written — contract each part separately to `E'(x)` and sum
  to `2E'(x)` — loses exactly the factor `2` that the statement's `/2`
  consumes, and its step-6 normalization `R = E'/(d‖x‖²)` omits the `/2`
  of `laplacian_quadForm` (`E'` is the *ordered* double sum, twice
  `quadForm (laplacian A)`); as literally recorded the two errors
  cancel, which is why the twice-hand-checked writeup looked exact. The
  tight route, delivered here: the contraction as the *pair-summed
  pointwise identity* — cross edges contribute `(u_i + v_j)² ≥
  u_i² + v_j²`, exactly paying for carrying both median parts — with
  translation invariance absorbed into the pointwise RHS being
  `(a−b)²` itself (the separate translation-invariance lemma the 1a
  sketch named is therefore inert and was *not* added), and the
  normalization carrying the explicit `2`. With these shapes the chain
  is exact: per-part `φ²·d·‖y‖² ≤ E'(y)` (1b composed with Component A)
  sums through the fused contraction to `φ²·d·‖x‖² ≤ E'(x) =
  2·d·R·‖x‖²`, i.e. `φ²/2 ≤ R`. The spike's hypothesis-form
  `assembly_skeleton` verified the *composition*, not the constants —
  the exact failure mode the survey's own QA-discipline note
  anticipated.
- **QA** (`Cheeger_QA.lean` 33 → 59 declarations): Component A on `K₂`
  at `![1,0]` with all three quantities computed independently
  (total-variation `2`, energy `2`, degree sum `1` — the last through
  the new regularity bridge, making it load-bearing), the instance
  `4 ≤ 8` and the strict gap pinned; the contraction on `C₄` in an
  **equality case** (`![1,0,-1,0]` at `m = 0`: `4 + 4 = 8`) and a
  **strict case** (`![1,1,-1,-1]`: `4 + 4 < 16`); the normalization on
  `K₂` at `![1,-1]` evaluated through the theorem to `2` and
  cross-checked against the independently pinned `λ₂(L_sym) = 2`
  (`rayleigh_edge_attains_secondEval_QA` — a defective denominator
  constant would fail this check); and **two guard refutations**:
  Component A's `IsSymm` hypothesis refuted-on-omission at the
  nonnegative asymmetric `!![0, 1/10; 1, 0]` (vertex `0`'s column sum
  `1` vs row sum `1/10` — the exact mismatch symmetry rules out;
  instance reads `121/100 ≤ 44/100`, false; nonnegativity proved to
  *hold* on the fixture), and the contraction's nonnegativity
  hypothesis refuted-on-omission at the symmetric negative-weight
  `!![0, -1; -1, 0]` with `x = ![2,1]`, `m = 3/2` (`-1/2 + -1/2 = -1
  ≤ -2`, false; symmetry proved to *hold* there).

Weyl is delivered and closed (2026-08-20). Davis–Kahan is delivered and
closed (2026-08-21; records below). The Cheeger Step 0 survey is
delivered (2026-08-22, this document's survey record above).

## Davis–Kahan Step 1 — DELIVERED 2026-08-21 (both components; explicit axioms 11 → 10)

`davis_kahan_sin_theta` retired from admitted axiom to proved theorem
at the **unchanged name, hypotheses, and conclusion** in
`Perturbation/DavisKahan.lean`, by the recorded two-component split,
executed as two runs the same day:

- **Component 1** — the equal-rank projector identity `‖P − Q‖ =
  ‖(I−Q)P‖` for real symmetric idempotent matrices of equal rank,
  `Analysis/OperatorTheory/Perturbation/ProjectionGap.lean` (~1570
  lines), zero new axioms, QA'd (`ProjectionGap_QA.lean`, 37
  declarations; the 30° Pythagorean rotation fixture by two routes plus
  the unequal-rank guard).
- **Component 2** — the Duhamel/FTC assembly,
  `Analysis/OperatorTheory/Perturbation/Duhamel.lean` (~900 lines),
  zero new axioms (`#print axioms` on every public theorem: `propext,
  Classical.choice, Quot.sound` only): the spike's semigroup primitives
  transferred (`heatApply` with expansion/adjoint, Parseval damping,
  eigenaction, differentiability, and the `t = 0` eigenbasis expansion),
  the sorted-spectrum step `evals_succ_le_of_lt`, the projector
  coefficient filter, the two cluster-filtered decay bounds, the
  pairing (duality) norm reduction `l2OpNorm_le_of_abs_dotProduct_le`
  (self-application route), and the headline
  `l2OpNorm_one_sub_spectralProjector_mul_spectralProjector_le`
  (`‖(1 − Q) * P‖ ≤ ‖E‖ / (b − a)`) — the scalar Duhamel pairing
  `⟨e^{-t(A+E)} z_y, e^{tA} z_x⟩` whose derivative is exactly the
  integrand `−⟨e^{-t(A+E)} z_y, E e^{tA} z_x⟩` (the two semigroup
  derivatives cancel through the symmetry shuffle, leaving the defect
  `E`), FTC on `[0, T]` with the explicit exponential majorant
  `‖E‖ e^{-(b-a)t}`, and the boundary term killed by `T → ∞`. Plus
  the rank layer (`rank_spectralProjector_eq_card_filter`, the no-tie
  pin `rank_spectralProjector_evals_of_lt`) and the `≤ 1` gap-metric
  endpoint.

**A route discovery the survey did not need to resolve, recorded at
delivery:** `initialProjector` includes whole tied eigenspaces, so under
eigenvalue ties at a threshold the two projector ranks differ and the
equal-rank identity does not apply directly. The retirement proof is a
three-way case split: **no tie at either `k`-th threshold** → both
ranks `k+1` → the equal-rank identity converts the goal to `‖(I−Q)P‖` →
the Duhamel bound → `‖E‖/(b−a) ≤ ‖E‖/δ`; **tie at `(A+E)`'s threshold**
(`λ_k = λ_{k+1}` there) → separation plus the proved
`weyl_additive_upper` at index `k` force `δ ≤ ‖E‖`; **tie at `A`'s
threshold** → the same through Weyl at index `k+1`; in both tie cases
the unconditional `‖P − Q‖ ≤ 1` finishes `‖P − Q‖ ≤ 1 ≤ ‖E‖/δ`. (A
2×2 hand example confirms the tie case is real, not vacuous: `A =
diag(0,0,3)`, `Ã = diag(0,2,3)` has ranks 2 vs 1 at `k = 0` with the
separation holding and the bound attained at equality.)

**QA** (`DavisKahan_QA.lean`, extended to 20 declarations): the retained
zero-perturbation instance, plus the proposal-required **strict
non-vacuity witness** — `dkA = diag(0,2)` perturbed by
`dkE = [[0,3/4],[3/4,0]]`, both spectra and `‖dkE‖ = 3/4` pinned
independently (trace/determinant/sortedness + the proved bridge), the
eigenvector directions pinned from the eigen equations (one-dimensional
eigenspaces; no control over Mathlib's classical eigenbasis needed), so
both projectors are pinned to explicit literals (`Q = (1/10)·[[9,−3],
[−3,1]]`, `P = diag(1,0)`), the bound instance reads `‖Q − P‖ ≤ 1/3`,
and the difference's own pinned spectrum gives the exact distance
`1/√10 < 1/3` — strict, and the fixture exercises the no-tie (Duhamel)
branch of the proof.

**Downstream effect (verified by `#print axioms`):**
`davisKahanTwoPoint` is **fully hard crust**; `eventStreamProjectorDrift`
is conditional on `matrix_azuma_hoeffding` alone.
