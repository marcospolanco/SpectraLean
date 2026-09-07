/-
  Signed_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.Signed` (the signed-graph
  slice, `proposals/signed-graphs-balance.md`), exercising every layer
  of the balance theorem at concrete fixtures:

  - **A (the balanced path):** the three-vertex path with one negative
    edge — `IsBalanced` witnessed by the switching `![1,-1,-1]`, the
    kernel pinned to that switching (the headline's forward half), the
    energy identities pinned numerically (real `10` and complex `4` at
    hand-computed test vectors — the complex one exercising the
    magnetic-join derivation of `hermQuadForm_signedLaplacian`), the
    π-flux join pinned at an entry, and the headline iff instantiated
    in both directions.

  - **B (the frustrated triangle):** the triangle with one negative
    edge — `¬IsBalanced` proved from the switching equations (their
    product around the cycle contradicts), the kernel trivial (two
    routes: the characterization's aligned equations, and the raw sign
    chase), and positive definiteness at a test vector.

  - **C (the disconnected fence):** balanced edge ⊕ frustrated triangle
    on `Fin 5` — a genuine kernel vector exists while the signing is
    globally unbalanced, refuting the headline's conclusion at exactly
    the dropped connectivity hypothesis (the iff cannot even be
    instantiated there).

  - **D (the negative-loop boundary):** a negative loop on a positive
    self-weight auto-frustrates — no switching exists (g² = −1) and
    the kernel is trivial, witnessing that the theorems need no
    separate loop-sign convention: balance itself forces loops
    unsigned.

  - **E (the nonnegativity mechanism fence):** symmetric weights with a
    negative entry — a nonzero kernel vector coexists with provable
    non-alignment, so the kernel↔aligned characterization fails at
    exactly the dropped `hnn` hypothesis (which cannot be
    instantiated). The fence lives at the mechanism, where the
    hypothesis enters.

  - **F (the switching similarity):** the balanced path's switching
    conjugates `L_σ` to `laplacian A` exactly (the similarity theorem
    at concrete witnesses), and the independently verified path
    eigenpair `![1,0,-1] @ 1` transfers to the switched vector
    `![1,0,1]` (the eigenpair-transfer theorem at its first concrete
    instance).

  Fixtures are `Fin 2`/`Fin 3`/`Fin 5` with entries in `{0, 1, -1, -2}`;
  matrix entries evaluate by `rfl` (the `Directed_QA` entry-table
  pattern). All proofs are raw computations or single-theorem
  instantiations; no `sorry`, no `admit`, no new assumptions.
-/
import Scaffold.Mathlib.GraphTheory.Signed
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix ComplexConjugate

namespace SpectralGraphTheory.QA

/-! ### Fixtures and hypothesis packages -/

/-- The path `0 — 1 — 2` on `Fin 3`, symmetric unit weights. -/
def sgPathA : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 0; 1, 0, 1; 0, 1, 0]

/-- The signing of the path with the single negative edge `0 — 1`. -/
def sgPaths : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![1, -1, 1; -1, 1, 1; 1, 1, 1]

theorem sgPathA_isSymm : sgPathA.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

theorem sgPathA_nonneg : ∀ i j, 0 ≤ sgPathA i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [sgPathA]

theorem sgPaths_isSymm : ∀ u v, sgPaths u v = sgPaths v u := by
  intro u v
  fin_cases u <;> fin_cases v <;> rfl

theorem sgPaths_pm : ∀ u v, sgPaths u v = 1 ∨ sgPaths u v = -1 := by
  intro u v
  fin_cases u <;> fin_cases v <;> first | exact Or.inl rfl | exact Or.inr rfl

/-! The signed-path entry table (rfl-reducible) — the `-1` entries
defeat simp's numeral unification, so the sums below rewrite through
these first. -/
theorem sgPaths_00 : sgPaths 0 0 = 1 := rfl
theorem sgPaths_01 : sgPaths 0 1 = -1 := rfl
theorem sgPaths_02 : sgPaths 0 2 = 1 := rfl
theorem sgPaths_10 : sgPaths 1 0 = -1 := rfl
theorem sgPaths_11 : sgPaths 1 1 = 1 := rfl
theorem sgPaths_12 : sgPaths 1 2 = 1 := rfl
theorem sgPaths_20 : sgPaths 2 0 = 1 := rfl
theorem sgPaths_21 : sgPaths 2 1 = 1 := rfl
theorem sgPaths_22 : sgPaths 2 2 = 1 := rfl

/-- The switching of the signed path. -/
def sgPathG : Fin 3 → ℝ := ![1, -1, -1]

theorem sgPathG_pm : ∀ v, sgPathG v = 1 ∨ sgPathG v = -1 := by
  intro v
  fin_cases v <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem sgPathG0 : sgPathG 0 = 1 := rfl
theorem sgPathG1 : sgPathG 1 = -1 := rfl
theorem sgPathG2 : sgPathG 2 = -1 := rfl

theorem sgPaths_eq_g_mul_g : ∀ u v, sgPathA u v ≠ 0 →
    sgPaths u v = sgPathG u * sgPathG v := by
  intro u v h
  fin_cases u <;> fin_cases v <;> first
  | exact absurd rfl h
  | norm_num [sgPaths, sgPathG]

theorem sgPath_supportGraph_connected :
    (supportGraph sgPathA sgPathA_isSymm).Connected := by
  have hfrom1 : ∀ v : Fin 3,
      (supportGraph sgPathA sgPathA_isSymm).Reachable 1 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.cons (u := 1) (v := 0) (w := 0)
        ⟨by decide, by simp [sgPathA]⟩ SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 1) (v := 2) (w := 2)
        ⟨by decide, by simp [sgPathA]⟩ SimpleGraph.Walk.nil⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨1, hfrom1⟩

/-- The triangle on `Fin 3`, symmetric unit weights. -/
def sgTriA : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 1; 1, 0, 1; 1, 1, 0]

/-- The signing of the triangle with the single negative edge `0 — 1`. -/
def sgTris : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![1, -1, 1; -1, 1, 1; 1, 1, 1]

theorem sgTriA_isSymm : sgTriA.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

theorem sgTriA_nonneg : ∀ i j, 0 ≤ sgTriA i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [sgTriA]

theorem sgTris_isSymm : ∀ u v, sgTris u v = sgTris v u := by
  intro u v
  fin_cases u <;> fin_cases v <;> rfl

theorem sgTris_pm : ∀ u v, sgTris u v = 1 ∨ sgTris u v = -1 := by
  intro u v
  fin_cases u <;> fin_cases v <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem sgTri_supportGraph_connected :
    (supportGraph sgTriA sgTriA_isSymm).Connected := by
  have hfrom0 : ∀ v : Fin 3,
      (supportGraph sgTriA sgTriA_isSymm).Reachable 0 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
        ⟨by decide, by simp [sgTriA]⟩ SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 2) (w := 2)
        ⟨by decide, by simp [sgTriA]⟩ SimpleGraph.Walk.nil⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, hfrom0⟩

/-! ### A. The balanced path -/

/-- **The balance witness**: the signed path is balanced at the
switching `![1,-1,-1]`, verified through every hypothesis. -/
theorem sgPath_isBalanced_QA : IsBalanced sgPathA sgPaths :=
  ⟨sgPathG, sgPathG_pm, sgPaths_eq_g_mul_g⟩

/-- **The kernel pinned to the switching**: the switching vector itself
is killed by the signed Laplacian — raw, entrywise. -/
theorem sgPath_kernel_QA :
    signedLaplacian sgPathA sgPaths *ᵥ ![1, -1, -1] = 0 := by
  funext i
  fin_cases i <;>
    simp only [signedLaplacian_mulVec_apply, Fin.sum_univ_three] <;>
    norm_num [sgPathA, sgPaths]

/-- The pinned witness is nonzero. -/
theorem sgPath_switch_ne_zero_QA : (![1, -1, -1] : Fin 3 → ℝ) ≠ 0 := by
  intro h
  have h0 : (![1, -1, -1] : Fin 3 → ℝ) 0 = 0 := congrFun h 0
  norm_num at h0

/-- **The headline's forward half instantiated**: balance gives a
nonzero kernel vector. -/
theorem sgPath_iff_forward_QA :
    ∃ x : Fin 3 → ℝ, x ≠ 0 ∧ signedLaplacian sgPathA sgPaths *ᵥ x = 0 :=
  (isBalanced_iff_exists_ne_zero_mulVec_eq_zero sgPathA_isSymm
    sgPathA_nonneg sgPaths_isSymm sgPaths_pm
    sgPath_supportGraph_connected).1 sgPath_isBalanced_QA

/-- **The headline's backward half instantiated**, second route: the
pinned kernel vector gives balance — derived through the walk collapse,
not through the switching witness of `sgPath_isBalanced_QA`. -/
theorem sgPath_iff_backward_QA : IsBalanced sgPathA sgPaths :=
  isBalanced_of_mulVec_eq_zero sgPathA_isSymm sgPathA_nonneg
    sgPaths_isSymm sgPaths_pm sgPath_supportGraph_connected
    sgPath_switch_ne_zero_QA sgPath_kernel_QA

/-- **The signed Dirichlet energy pinned**: at the test vector
`![1,2,3]` the form reads `10`, both through the energy-identity
theorem and by raw computation of the same value. -/
theorem sgPath_energy_QA :
    quadForm (signedLaplacian sgPathA sgPaths) ![1, 2, 3] = 10 := by
  rw [signedLaplacian_quadForm sgPathA_isSymm sgPaths_isSymm sgPaths_pm]
  simp only [Fin.sum_univ_three, sgPaths_00, sgPaths_01, sgPaths_02,
    sgPaths_10, sgPaths_11, sgPaths_12, sgPaths_20, sgPaths_21, sgPaths_22]
  norm_num [sgPathA]

/-- **The complex energy identity pinned** at the complex test vector
`![1, I, 1]`: the form reads `4` — this exercises the
magnetic-join derivation (`hermQuadForm_signedLaplacian` through
`magnetic_energy`) at genuinely complex input. -/
theorem sgPath_complex_energy_QA :
    hermQuadForm (fun u v => ((signedLaplacian sgPathA sgPaths) u v : ℂ))
      ![1, Complex.I, 1] = 4 := by
  rw [hermQuadForm_signedLaplacian sgPathA_isSymm sgPaths_isSymm sgPaths_pm]
  simp only [Fin.sum_univ_three, sgPaths_00, sgPaths_01, sgPaths_02,
    sgPaths_10, sgPaths_11, sgPaths_12, sgPaths_20, sgPaths_21, sgPaths_22]
  norm_num [sgPathA, Complex.normSq, map_add, map_mul,
    Complex.conj_I, Complex.I_mul_I]

/-- **The π-flux join pinned** at the negative edge: the magnetic
Laplacian at the signing's flux reads the signed Laplacian's entry `1`
(the sign `e^{iπ} = -1` flipping `−A` to `+A`). -/
theorem sgPath_join_QA :
    magneticLaplacian sgPathA (signFlux sgPaths) 0 1 = (1 : ℂ) := by
  rw [magneticLaplacian_signFlux_apply sgPathA_isSymm sgPaths_isSymm
    sgPaths_pm]
  norm_num [signedLaplacian, signedAdj, sgPathA, sgPaths, degreeMatrix, deg]

/-! ### B. The frustrated triangle -/

/-- **No switching exists**: the product of the switching equations
around the triangle contradicts `g² = 1` — the sign chase in proved
form. -/
theorem sgTri_not_isBalanced_QA : ¬ IsBalanced sgTriA sgTris := by
  rintro ⟨g, hgpm, hgs⟩
  have h01 : g 0 * g 1 = -1 := (hgs 0 1 (by simp [sgTriA])).symm
  have h02 : g 0 * g 2 = 1 := (hgs 0 2 (by simp [sgTriA])).symm
  have h12 : g 1 * g 2 = 1 := (hgs 1 2 (by simp [sgTriA])).symm
  have g0 : g 0 * g 0 = 1 := by rcases hgpm 0 with h | h <;> rw [h] <;> norm_num
  have g1 : g 1 * g 1 = 1 := by rcases hgpm 1 with h | h <;> rw [h] <;> norm_num
  have g2 : g 2 * g 2 = 1 := by rcases hgpm 2 with h | h <;> rw [h] <;> norm_num
  have key : (g 0 * g 1) * (g 1 * g 2) = g 0 * g 2 := by
    have : (g 0 * g 1) * (g 1 * g 2) = (g 0 * g 2) * (g 1 * g 1) := by ring
    rw [g1, mul_one] at this
    exact this
  rw [h01, h12] at key
  linarith [h02, key]

/-- **The kernel is trivial** — route 1: the characterization's aligned
equations force `x = 0` by the sign chase. -/
theorem sgTri_kernel_trivial_QA (x : Fin 3 → ℝ)
    (hx : signedLaplacian sgTriA sgTris *ᵥ x = 0) : x = 0 := by
  have halign := (signedLaplacian_mulVec_eq_zero_iff_aligned sgTriA_isSymm
    sgTriA_nonneg sgTris_isSymm sgTris_pm x).1 hx
  have e1 : x 0 = -1 * x 1 := halign 0 1 (by simp [sgTriA])
  have e2 : x 1 = 1 * x 2 := halign 1 2 (by simp [sgTriA])
  have e3 : x 0 = 1 * x 2 := halign 0 2 (by simp [sgTriA])
  funext i
  fin_cases i
  · show x 0 = 0; linarith
  · show x 1 = 0; linarith
  · show x 2 = 0; linarith

/-- **Positive definiteness under frustration**: at `![1,0,0]` the
signed Dirichlet energy is strictly positive — the theorem's instance
and the raw value `2` agree. -/
theorem sgTri_posdef_QA :
    0 < quadForm (signedLaplacian sgTriA sgTris) ![1, 0, 0] := by
  refine quadForm_pos_of_ne_zero_of_not_isBalanced sgTriA_isSymm
    sgTriA_nonneg sgTris_isSymm sgTris_pm sgTri_supportGraph_connected
    sgTri_not_isBalanced_QA (by simp)

/-! ### C. The disconnected fence: balanced edge ⊕ frustrated triangle -/

/-- `Fin 5`: the balanced negative edge `0 — 1` disjoint from the
frustrated triangle `2 — 3 — 4` (negative edge `3 — 4`). -/
def sgDisA : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of !![0, 1, 0, 0, 0;
               1, 0, 0, 0, 0;
               0, 0, 0, 1, 1;
               0, 0, 1, 0, 1;
               0, 0, 1, 1, 0]

def sgDisS : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of !![1, -1, 1, 1, 1;
               -1, 1, 1, 1, 1;
               1, 1, 1, 1, 1;
               1, 1, 1, 1, -1;
               1, 1, 1, -1, 1]

theorem sgDisS_isSymm : ∀ u v, sgDisS u v = sgDisS v u := by
  intro u v
  fin_cases u <;> fin_cases v <;> rfl

theorem sgDisS_pm : ∀ u v, sgDisS u v = 1 ∨ sgDisS u v = -1 := by
  intro u v
  fin_cases u <;> fin_cases v <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- **The kernel vector exists**: the balanced component's switching,
extended by zero, is killed — raw, entrywise. -/
theorem sgDis_kernel_QA :
    signedLaplacian sgDisA sgDisS *ᵥ ![1, -1, 0, 0, 0] = 0 := by
  funext i
  fin_cases i <;>
    simp only [signedLaplacian_mulVec_apply, Fin.sum_univ_five] <;>
    norm_num [sgDisA, sgDisS]

/-- **But the signing is globally unbalanced**: the triangle's
switching equations contradict. -/
theorem sgDis_not_isBalanced_QA : ¬ IsBalanced sgDisA sgDisS := by
  rintro ⟨g, hgpm, hgs⟩
  have h23 : g 2 * g 3 = 1 := (hgs 2 3 (by simp [sgDisA])).symm
  have h24 : g 2 * g 4 = 1 := (hgs 2 4 (by simp [sgDisA])).symm
  have h34 : g 3 * g 4 = -1 := (hgs 3 4 (by simp [sgDisA])).symm
  have g2 : g 2 * g 2 = 1 := by
    rcases hgpm 2 with h | h <;> rw [h] <;> norm_num
  have g3 : g 3 * g 3 = 1 := by
    rcases hgpm 3 with h | h <;> rw [h] <;> norm_num
  have g4 : g 4 * g 4 = 1 := by
    rcases hgpm 4 with h | h <;> rw [h] <;> norm_num
  have key : (g 2 * g 3) * (g 2 * g 4) = (g 2 * g 2) * (g 3 * g 4) := by ring
  rw [h23, h24, g2, h34] at key
  norm_num at key

/-- **The conclusion-level fence**: a nonzero kernel vector coexists
with global unbalance — the headline's iff fails at exactly the dropped
connectivity hypothesis (the fixture's support graph is the disjoint
union, so `hconn` cannot be supplied). -/
theorem sgDis_fence_QA :
    (∃ x : Fin 5 → ℝ, x ≠ 0 ∧ signedLaplacian sgDisA sgDisS *ᵥ x = 0)
      ∧ ¬ IsBalanced sgDisA sgDisS :=
  ⟨⟨![1, -1, 0, 0, 0], by simp, sgDis_kernel_QA⟩, sgDis_not_isBalanced_QA⟩

/-! ### D. The negative-loop boundary -/

/-- `Fin 2`: a positive self-loop at `0` signed negative. -/
def sgLoopA : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![1, 1; 1, 0]

def sgLoopS : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![-1, 1; 1, 1]

theorem sgLoopS_isSymm : ∀ u v, sgLoopS u v = sgLoopS v u := by
  intro u v
  fin_cases u <;> fin_cases v <;> rfl

theorem sgLoopS_pm : ∀ u v, sgLoopS u v = 1 ∨ sgLoopS u v = -1 := by
  intro u v
  fin_cases u <;> fin_cases v <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- **A negative loop auto-frustrates**: no switching exists, since the
loop's own equation would need `g² = -1`. This is why the theorems
carry no separate loop-sign hypothesis: balance forces loops unsigned
wherever the self-weight is positive. -/
theorem sgLoop_not_isBalanced_QA : ¬ IsBalanced sgLoopA sgLoopS := by
  rintro ⟨g, hgpm, hgs⟩
  have h00 : g 0 * g 0 = -1 := (hgs 0 0 (by simp [sgLoopA])).symm
  rcases hgpm 0 with h | h <;> rw [h] at h00 <;> norm_num at h00

/-- **The kernel is trivial**: the raw row equations force `x = 0` —
so both sides of the balance iff read "no", consistently. -/
theorem sgLoop_kernel_trivial_QA (x : Fin 2 → ℝ)
    (hx : signedLaplacian sgLoopA sgLoopS *ᵥ x = 0) : x = 0 := by
  have hrow0 : (signedLaplacian sgLoopA sgLoopS *ᵥ x) 0 = 0 :=
    congrFun hx 0
  have hrow1 : (signedLaplacian sgLoopA sgLoopS *ᵥ x) 1 = 0 :=
    congrFun hx 1
  simp only [signedLaplacian_mulVec_apply, Fin.sum_univ_two] at hrow0 hrow1
  norm_num [sgLoopA, sgLoopS] at hrow0 hrow1
  funext i
  fin_cases i
  · show x 0 = 0; linarith
  · show x 1 = 0; linarith

/-! ### E. The nonnegativity mechanism fence -/

/-- `Fin 3`: symmetric weights with a negative entry — the support
graph is the full triangle (entrywise positivity fails only through
the sign of one weight). -/
def sgNegA : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, -2; 1, 0, -2; -2, -2, 0]

def sgNegS : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![1, 1, 1; 1, 1, 1; 1, 1, 1]

theorem sgNegS_isSymm : ∀ u v, sgNegS u v = sgNegS v u := by
  intro u v
  fin_cases u <;> fin_cases v <;> rfl

theorem sgNegS_pm : ∀ u v, sgNegS u v = 1 ∨ sgNegS u v = -1 := by
  intro u v
  fin_cases u <;> fin_cases v <;> exact Or.inl rfl

theorem sgNegA_isSymm : sgNegA.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

/-- **The kernel vector exists** — raw, entrywise: `![0,-2,-1]` is
killed by the signed Laplacian. -/
theorem sgNeg_kernel_QA :
    signedLaplacian sgNegA sgNegS *ᵥ ![0, -2, -1] = 0 := by
  funext i
  fin_cases i <;>
    simp only [signedLaplacian_mulVec_apply, Fin.sum_univ_three] <;>
    norm_num [sgNegA, sgNegS]

/-- **But the vector is not aligned**: at the positive-weight pair
`(0,1)` the alignment equation reads `0 = -2`. So the kernel↔aligned
characterization fails here — the `hnn` hypothesis (which this
fixture's `-2` entries violate) is load-bearing exactly at the
termwise-vanishing step of the energy identity. -/
theorem sgNeg_fence_QA :
    (∃ x : Fin 3 → ℝ, x ≠ 0 ∧ signedLaplacian sgNegA sgNegS *ᵥ x = 0)
      ∧ ¬ (∀ u v, sgNegA u v ≠ 0 → ![0, -2, -1] u = sgNegS u v * ![0, -2, -1] v) :=
  ⟨⟨![0, -2, -1], by simp, sgNeg_kernel_QA⟩, by
    intro halign
    have h01 := halign 0 1 (by simp [sgNegA])
    have h01' : (![0, -2, -1] : Fin 3 → ℝ) 0 = 1 * (![0, -2, -1] : Fin 3 → ℝ) 1 :=
      h01
    norm_num at h01'⟩

/-! ### F. The switching similarity and the eigenpair transfer -/

/-- **The similarity at concrete witnesses**: conjugating the signed
path Laplacian by the switching's diagonal recovers `laplacian sgPathA`
exactly — the theorem instantiated, and the target matrix pinned raw. -/
theorem sgPath_switch_QA :
    Matrix.diagonal sgPathG * signedLaplacian sgPathA sgPaths
      * Matrix.diagonal sgPathG = laplacian sgPathA := by
  refine diagonal_mul_signedLaplacian_mul_diagonal sgPathG_pm
    sgPaths_eq_g_mul_g

/-! The path Laplacian's entry table (the degree diagonal through
`degreeMatrix_diagonal` and the row sums). -/
theorem sgPathL00 : laplacian sgPathA 0 0 = 1 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal]
  norm_num [deg, sgPathA, Fin.sum_univ_three]
theorem sgPathL01 : laplacian sgPathA 0 1 = -1 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal sgPathA (by decide)]
  norm_num [sgPathA]
theorem sgPathL02 : laplacian sgPathA 0 2 = 0 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal sgPathA (by decide)]
  norm_num [sgPathA]
theorem sgPathL10 : laplacian sgPathA 1 0 = -1 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal sgPathA (by decide)]
  norm_num [sgPathA]
theorem sgPathL11 : laplacian sgPathA 1 1 = 2 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal]
  norm_num [deg, sgPathA, Fin.sum_univ_three]
theorem sgPathL12 : laplacian sgPathA 1 2 = -1 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal sgPathA (by decide)]
  norm_num [sgPathA]
theorem sgPathL20 : laplacian sgPathA 2 0 = 0 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal sgPathA (by decide)]
  norm_num [sgPathA]
theorem sgPathL21 : laplacian sgPathA 2 1 = -1 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal sgPathA (by decide)]
  norm_num [sgPathA]
theorem sgPathL22 : laplacian sgPathA 2 2 = 1 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal]
  norm_num [deg, sgPathA, Fin.sum_univ_three]

/-- The path Laplacian's eigenpair `![1,0,-1] @ 1`, verified raw — the
independent input to the transfer. -/
theorem sgPath_eigenpair_raw_QA :
    laplacian sgPathA *ᵥ ![1, 0, -1] = (1 : ℝ) • ![1, 0, -1] := by
  have h0 : (laplacian sgPathA *ᵥ ![1, 0, -1]) 0
      = ((1 : ℝ) • ![1, 0, -1]) 0 := by
    simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
    rw [sgPathL00, sgPathL01, sgPathL02]
    norm_num
  have h1 : (laplacian sgPathA *ᵥ ![1, 0, -1]) 1
      = ((1 : ℝ) • ![1, 0, -1]) 1 := by
    simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
    rw [sgPathL10, sgPathL11, sgPathL12]
    norm_num
  have h2 : (laplacian sgPathA *ᵥ ![1, 0, -1]) 2
      = ((1 : ℝ) • ![1, 0, -1]) 2 := by
    simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
    rw [sgPathL20, sgPathL21, sgPathL22]
    norm_num
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- **The eigenpair transfer instantiated**: the switched vector
`![1,0,1]` is an eigenvector of the signed Laplacian at the same
eigenvalue `1` — through the theorem at the raw eigenpair. -/
theorem sgPath_transfer_QA :
    signedLaplacian sgPathA sgPaths *ᵥ (Matrix.diagonal sgPathG *ᵥ ![1, 0, -1])
      = (1 : ℝ) • (Matrix.diagonal sgPathG *ᵥ ![1, 0, -1]) := by
  refine signedLaplacian_mulVec_switchVec sgPathG_pm sgPaths_eq_g_mul_g
    sgPath_eigenpair_raw_QA

/-- **The switched vector pinned**: the transfer's output vector is
`![1,0,1]` — nonzero. -/
theorem sgPath_switched_vec_QA :
    Matrix.diagonal sgPathG *ᵥ ![1, 0, -1] = ![1, 0, 1]
      ∧ (![1, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
  have h0 : (Matrix.diagonal sgPathG *ᵥ ![1, 0, -1]) 0 = (![1, 0, 1] : Fin 3 → ℝ) 0 := by
    rw [switchVec_apply, sgPathG0]; norm_num
  have h1 : (Matrix.diagonal sgPathG *ᵥ ![1, 0, -1]) 1 = (![1, 0, 1] : Fin 3 → ℝ) 1 := by
    rw [switchVec_apply, sgPathG1]; norm_num
  have h2 : (Matrix.diagonal sgPathG *ᵥ ![1, 0, -1]) 2 = (![1, 0, 1] : Fin 3 → ℝ) 2 := by
    rw [switchVec_apply, sgPathG2]; norm_num
  refine ⟨by
      funext i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2, ?_⟩
  intro h
  have h0' : (![1, 0, 1] : Fin 3 → ℝ) 0 = 0 := congrFun h 0
  norm_num at h0'

/-! ### The structural pins (destined for Signed_QA.lean) -/

/-- The diagonal action at a literal, Fin-if-free: `(diag(g) · v) i =
`g i * v i`, by `Finset.sum_eq_single` + the diagonal's eq/ne entry
lemmas — dodging the Fin-literal `if`s `Matrix.diagonal_apply` leaves
behind. -/
private theorem sgp_diagonal_mulVec_apply (g v : Fin 3 → ℝ) (i : Fin 3) :
    (Matrix.diagonal g *ᵥ v) i = g i * v i := by
  rw [Matrix.mulVec, Matrix.dotProduct, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hj
    have hd : Matrix.diagonal g i j = 0 := by
      simp [Matrix.diagonal_apply, hj.symm]
    rw [hd, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi


/-- **The signed adjacency's symmetry, path fixture** — through the
theorem, with both hypotheses genuine (`sgPaths_isSymm`,
`sgPathA_isSymm`). -/
theorem sgp_adjSymm_path :
    (signedAdj sgPathA sgPaths).IsSymm :=
  signedAdj_symmetric sgPathA sgPaths_isSymm sgPathA_isSymm

/-- **The symmetry read at the entry level**: the `(1, 0)` entry of
the signed adjacency DERIVED through the theorem's symmetry instance
from the `(0, 1)` entry (which is raw `1 * (-1) = -1`), with the raw
companion pinned beside it — the entry equality is exactly what a
transposed convention would break. -/
theorem sgp_adjSymm_entry_pin :
    signedAdj sgPathA sgPaths 1 0 = -1
      ∧ signedAdj sgPathA sgPaths 0 1 = -1 := by
  have hsym : signedAdj sgPathA sgPaths 0 1 = signedAdj sgPathA sgPaths 1 0 :=
    (signedAdj_symmetric sgPathA sgPaths_isSymm sgPathA_isSymm).apply 1 0
  have hraw : signedAdj sgPathA sgPaths 0 1 = -1 := by
    show sgPathA 0 1 * sgPaths 0 1 = -1
    norm_num [sgPathA, sgPaths]
  exact ⟨hsym.symm.trans hraw, hraw⟩

/-- **The signed Laplacian's symmetry, path fixture** — through the
theorem. -/
theorem sgp_lapSymm_path :
    (signedLaplacian sgPathA sgPaths).IsSymm :=
  signedLaplacian_symmetric sgPathA sgPaths_isSymm sgPathA_isSymm

/-- **The symmetry scope witness — the frustrated triangle**: the
triangle's single-negative-edge signing is symmetric but NOT balanced
(`sgTri_not_isBalanced_QA`), and the signed Laplacian is symmetric
anyway — the theorem's hypothesis set is symmetry, not balance. -/
theorem sgp_lapSymm_tri :
    (signedLaplacian sgTriA sgTris).IsSymm :=
  signedLaplacian_symmetric sgTriA sgTris_isSymm sgTriA_isSymm

/-- **The sign-flipped edge read through the symmetry**: the signed
Laplacian's `(0, 1)` entry is `+1` (the degree diagonal minus the
negatively-signed edge `−(−1)`), the `(1, 0)` entry DERIVED through
the theorem. -/
theorem sgp_lapSymm_entry_pin :
    signedLaplacian sgPathA sgPaths 1 0 = 1
      ∧ signedLaplacian sgPathA sgPaths 0 1 = 1 := by
  have hsym : signedLaplacian sgPathA sgPaths 0 1
      = signedLaplacian sgPathA sgPaths 1 0 :=
    (signedLaplacian_symmetric sgPathA sgPaths_isSymm sgPathA_isSymm).apply
      1 0
  have hraw : signedLaplacian sgPathA sgPaths 0 1 = 1 := by
    show degreeMatrix sgPathA 0 1 - sgPathA 0 1 * sgPaths 0 1 = 1
    rw [degreeMatrix_off_diagonal sgPathA (by decide)]
    norm_num [sgPathA, sgPaths]
  exact ⟨hsym.symm.trans hraw, hraw⟩

/-- **The switched vector, value pinned raw**: `diag(g) · (2, 3, 5) =
(2, −3, −5)` — three genuinely nonzero entries, so the nonvanishing
below is not carried by a single coordinate. -/
theorem sgp_switchVec_val :
    Matrix.diagonal sgPathG *ᵥ (![2, 3, 5] : Fin 3 → ℝ)
      = (![2, -3, -5] : Fin 3 → ℝ) := by
  funext i
  rw [sgp_diagonal_mulVec_apply]
  fin_cases i <;>
    simp only [sgPathG, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] <;>
    norm_num

/-- **The switching preserves nonvanishing** — through the theorem, at
the value-carrying vector. -/
theorem sgp_switchVec_ne_zero_pin :
    Matrix.diagonal sgPathG *ᵥ (![2, 3, 5] : Fin 3 → ℝ) ≠ 0 :=
  switchVec_ne_zero sgPathG_pm
    (by intro h
        have h0 := congrFun h 0
        simp at h0)

/-- **The raw unsigned eigenpair** (route A): `L · (1, 0, −1) =
1 · (1, 0, −1)` on the path — direct entrywise computation. -/
theorem sgp_unsigned_eigenpair_raw :
    laplacian sgPathA *ᵥ (![1, 0, -1] : Fin 3 → ℝ)
      = (1 : ℝ) • (![1, 0, -1] : Fin 3 → ℝ) := by
  funext i
  rw [laplacian_mulVec_apply]
  fin_cases i <;>
    simp only [Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul] <;>
    norm_num [sgPathA]

/-- **The raw signed eigenpair**: `L_σ · (1, 0, 1) = 1 · (1, 0, 1)` —
the switching of the unsigned mode, computed entrywise through the
signed action's diffusion form. -/
theorem sgp_signed_eigenpair_raw :
    signedLaplacian sgPathA sgPaths *ᵥ (![1, 0, 1] : Fin 3 → ℝ)
      = (1 : ℝ) • (![1, 0, 1] : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;>
    simp only [signedLaplacian_mulVec_apply, Fin.sum_univ_three] <;>
    norm_num [sgPathA, sgPaths]

/-- **The backward eigenpair transfer consumed** (route B): from the
raw SIGNED eigenpair, `laplacian_mulVec_switchVec` produces the
unsigned eigenpair equation at the switched vector — and the switching
involutivity identifies that vector as exactly `![1, 0, −1]` — the
same equation as route A, derived through the spectral bridge of
Harary balance. Two routes, one value; they agree only if the raw
computations AND the bridge are right. -/
theorem sgp_backward_transfer_pin :
    laplacian sgPathA *ᵥ (![1, 0, -1] : Fin 3 → ℝ)
      = (1 : ℝ) • (![1, 0, -1] : Fin 3 → ℝ) := by
  have hsign := sgp_signed_eigenpair_raw
  have hback := laplacian_mulVec_switchVec sgPathG_pm sgPaths_eq_g_mul_g
    hsign
  have hsw : Matrix.diagonal sgPathG *ᵥ (![1, 0, 1] : Fin 3 → ℝ)
      = (![1, 0, -1] : Fin 3 → ℝ) := by
    funext i
    rw [sgp_diagonal_mulVec_apply]
    fin_cases i <;>
      simp only [sgPathG, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] <;>
      norm_num
  rwa [hsw] at hback

end SpectralGraphTheory.QA
