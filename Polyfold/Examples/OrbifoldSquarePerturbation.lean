import Polyfold.Examples.OrbifoldSquareOrientation
import Polyfold.Chapter16.IndexZeroNormOneWitness

/-!
# The orbifold `ℂ/ℤ₅` and the section `z ↦ z²`: the auxiliary norm and the multisection

A worked example for Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021),
Theorem 16.6.6, 2021 p. 739.

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquare`)

* `N5`, `isAuxNorm_N5`: the auxiliary norm `N(z, w) = |w|` (Euclidean; invariant under the
  morphisms); `n5`, `isAuxNorm_n5`: the auxiliary norm on the strong polyfold bundle
  (Definition 16.3.9).
* `controlsCompactness_sqSection_univ`, `controlsCompactness_n5`: `(n, Z)` controls the
  compactness of `f` (`|z²| ≤ 1` forces `|z| ≤ 1`); `hasCompactSolutionSet_sqFredholmSection`.
* `branch c j`, `Λ5 c`: the multisection with the five constant branches `z ↦ (z, ζ^{2j} c)`,
  weight `1/5` each; `isWFunctor_Λ5`, `isScPlusMultisection_Λ5` (Definition 13.2.1).
* `Λ5_sqSection_pos_iff`: `Λ(f(z)) > 0` iff `z² = ζ^{2j} c` for some `j`.
* **`isInGeneralPosition_Λ5`** (Definition 15.3.5), for `c ≠ 0`: at a solution `z ≠ 0`, and
  `(f − s_j)'(z) = 2z` is onto.
* `t5 c`, `isControlledBy_t5` (for `|c| ≤ 1`), `isInGeneralPositionWith_t5`: the sc⁺-multisection
  `λ` of the strong polyfold bundle is controlled by `(n, Z)`, and `(f, λ)` is in general
  position.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.OrbifoldSquare

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure StrongBundleEquivalenceExamples
  StrongBundleLocalizationExamples SBLocalization StrongRetr Linearization15

/-! ### The auxiliary norm -/

/-- **The auxiliary norm** `N(z, w) = |w|` (the Euclidean norm of `ℂ`). -/
def N5 : (bundle 2 2).One → ℝ := fun w => ‖cE ((bundle 2 2).oneVal w).2‖

theorem N5_oneMk (w : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hw : w ∈ (bundle 2 2).oneSet) :
    N5 ((bundle 2 2).oneMk w hw) = ‖cE w.2‖ := by
  unfold N5
  rw [oneVal_oneMk]

/-- **`N` is an auxiliary norm** (Definition 5.1.1). -/
theorem isAuxNorm_N5_bundle : (bundle 2 2).IsAuxNorm N5 where
  continuous := (continuous_norm.comp (cE.continuous.comp continuous_snd)).comp
    (bundle 2 2).continuous_oneVal
  fiber x :=
    { eq_zero := fun v hv => by
        have h0 : ((v : proj 2 2 ⁻¹' {x}) : (Fin 2 → ℝ) × (Fin 2 → ℝ)).2 = 0 :=
          cE.map_eq_zero_iff.1 (norm_eq_zero.1 hv)
        refine Subtype.ext ((fibEquiv x).injective ?_)
        change ((v : proj 2 2 ⁻¹' {x}) : (Fin 2 → ℝ) × (Fin 2 → ℝ)).2 =
          ((0 : proj 2 2 ⁻¹' {x}) : (Fin 2 → ℝ) × (Fin 2 → ℝ)).2
        rw [h0, snd_zero]
      smul := fun t v => by
        change ‖cE ((t • (v : proj 2 2 ⁻¹' {x}) : proj 2 2 ⁻¹' {x}) :
          (Fin 2 → ℝ) × (Fin 2 → ℝ)).2‖ = |t| * ‖cE ((v : proj 2 2 ⁻¹' {x}) :
            (Fin 2 → ℝ) × (Fin 2 → ℝ)).2‖
        rw [snd_smul, map_smul, norm_smul, Real.norm_eq_abs]
      add_le := fun v w => by
        change ‖cE (((v : proj 2 2 ⁻¹' {x}) + (w : proj 2 2 ⁻¹' {x}) : proj 2 2 ⁻¹' {x}) :
          (Fin 2 → ℝ) × (Fin 2 → ℝ)).2‖ ≤ ‖cE ((v : proj 2 2 ⁻¹' {x}) :
            (Fin 2 → ℝ) × (Fin 2 → ℝ)).2‖ + ‖cE ((w : proj 2 2 ⁻¹' {x}) :
              (Fin 2 → ℝ) × (Fin 2 → ℝ)).2‖
        rw [snd_add, map_add]; exact norm_add_le _ _
      complete := fun u hu => by
        set a : ℕ → ℂ := fun j => cE ((u j : proj 2 2 ⁻¹' {x}) :
          (Fin 2 → ℝ) × (Fin 2 → ℝ)).2 with ha
        have hsub : ∀ i j, N5 ((bundle 2 2).toOne (u i - u j)) = ‖a i - a j‖ := fun i j => by
          change ‖cE (((u i : proj 2 2 ⁻¹' {x}) - (u j : proj 2 2 ⁻¹' {x}) : proj 2 2 ⁻¹' {x}) :
            (Fin 2 → ℝ) × (Fin 2 → ℝ)).2‖ = _
          rw [snd_sub, map_sub]
        have hc : CauchySeq a := by
          refine Metric.cauchySeq_iff.2 fun ε hε => ?_
          obtain ⟨N₀, hN₀⟩ := hu ε hε
          exact ⟨N₀, fun i hi j hj => by rw [dist_eq_norm, ← hsub]; exact hN₀ i hi j hj⟩
        obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hc
        let v₀ : proj 2 2 ⁻¹' {x} := ⟨(x, cE.symm b), rfl⟩
        have hv₀ : v₀ ∈ (bundle 2 2).oneFiber x := by
          change ((v₀ : proj 2 2 ⁻¹' {x}) : (Fin 2 → ℝ) × (Fin 2 → ℝ)) ∈ (bundle 2 2).oneSet
          rw [oneSet_eq]; exact mem_univ _
        refine ⟨⟨v₀, hv₀⟩, ?_⟩
        have e : ∀ j, N5 ((bundle 2 2).toOne (u j - ⟨v₀, hv₀⟩)) = ‖a j - b‖ := fun j => by
          change ‖cE (((u j : proj 2 2 ⁻¹' {x}) - v₀ : proj 2 2 ⁻¹' {x}) :
            (Fin 2 → ℝ) × (Fin 2 → ℝ)).2‖ = _
          rw [snd_sub, map_sub]
          change ‖cE _ - cE (cE.symm b)‖ = _
          rw [ContinuousLinearEquiv.apply_symm_apply]
        simp only [e]
        exact tendsto_iff_norm_sub_tendsto_zero.1 hb }
  tendsto_zeroOne := fun w x hP hN => by
    refine TopologicalSpace.tendsto_nhds_generateFrom_iff.2 ?_
    rintro s ⟨c, ⟨a, rfl⟩, W, hW, rfl⟩ ⟨-, hz⟩
    have hlift : ∀ y : (Fin 2 → ℝ) × (Fin 2 → ℝ),
        (chart (k := 2) a).liftOne y = (y.1 - a, y.2) :=
      fun y => Prod.ext rfl (invFun_toBase_one _)
    have hz' : ((x - a, 0) : (Fin 2 → ℝ) × (Fin 2 → ℝ)) ∈ W := by
      have := hz
      change (chart (k := 2) a).liftOne (fiberZero (proj 2 2) x) ∈ W at this
      rwa [hlift] at this
    have h2 : Tendsto (fun j => ((bundle 2 2).oneVal (w j)).2) atTop (𝓝 0) := by
      have h3 : Tendsto (fun j => cE ((bundle 2 2).oneVal (w j)).2) atTop (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.2 hN
      have h4 := (cE.symm.continuous.tendsto 0).comp h3
      rw [map_zero] at h4
      refine h4.congr fun j => ?_
      exact cE.symm_apply_apply _
    have h1 : Tendsto (fun j => (((bundle 2 2).oneVal (w j)).1 - a, ((bundle 2 2).oneVal (w j)).2))
        atTop (𝓝 ((x - a, 0) : (Fin 2 → ℝ) × (Fin 2 → ℝ))) :=
      (hP.sub_const a).prodMk_nhds h2
    filter_upwards [h1 (hW.mem_nhds hz')] with j hj
    refine ⟨mem_univ _, ?_⟩
    change (chart (k := 2) a).liftOne ((bundle 2 2).oneVal (w j)) ∈ W
    rw [hlift]; exact hj

/-- **`N` is an auxiliary norm of the bundle over `ℤ/5 ⋉ ℂ`** (Definition 12.2.1): the
morphisms act on the fibres by `ζ^{2g}`, of modulus `1`. -/
theorem isAuxNorm_N5 : A5.E.IsAuxNorm N5 :=
  ⟨isAuxNorm_N5_bundle, fun h k φ _ e => by
    have e' : (bundle 2 2).oneVal h = actW φ.1 ((bundle 2 2).oneVal k) := e
    unfold N5
    rw [e', actW_apply, cE_rot, norm_mul, norm_pow, norm_χ, one_pow, one_mul]⟩

/-- **The auxiliary norm `n` of the strong polyfold bundle** (Definition 16.3.9). -/
def n5 : A5.E.toEpGroupoid.OrbitSpace → ℝ := sqStructure.descend N5

theorem isAuxNorm_n5 : sqBundle.IsAuxNorm n5 := isAuxNorm_descend rfl isAuxNorm_N5

theorem normOf_n5 : sqStructure.normOf n5 = N5 :=
  sqStructure.normOf_descend isAuxNorm_N5.isOneInvariant

/-! ### `(n, Z)` controls compactness -/

/-- **`(N, ℂ)` controls the compactness of `f`** (Definition 15.3.1): `N(f(z)) ≤ 1` means
`|z|² ≤ 1`. -/
theorem controlsCompactness_sqSection_univ : ControlsCompactness A5 sqSection N5 univ := by
  refine ⟨isAuxNorm_N5, isOpen_univ, GroupoidStr.isSaturated_univ _, subset_univ _, ?_⟩
  let K : Set (Fin 2 → ℝ) := cE.symm '' Metric.closedBall 0 1
  have hK : IsCompact K := (isCompact_closedBall 0 1).image cE.symm.continuous
  have hsub : {x ∈ (univ : Set A5.Obj) | A5.B.AuxLe N5 (sqSection x) 1} ⊆ (K : Set A5.Obj) := by
    rintro (x : Fin 2 → ℝ) ⟨-, hw, hle⟩
    have hle' : ‖cE (sq x)‖ ≤ 1 := (N5_oneMk _ hw).symm.trans_le hle
    rw [cE_sq, norm_pow] at hle'
    have h1 : ‖cE x‖ ≤ 1 := by
      by_contra h
      have h' : 1 < ‖cE x‖ := lt_of_not_ge h
      nlinarith
    exact ⟨cE x, by rw [Metric.mem_closedBall, dist_zero_right]; exact h1,
      cE.symm_apply_apply x⟩
  exact (hK.image A5.X.continuous_π).closure_of_subset (image_mono hsub)

/-- **`(n, Z)` controls the compactness of the section `|z| ↦ |(z, z²)|`** (Definition 16.6.3,
with `U = Z = ℂ/ℤ₅`). -/
theorem controlsCompactness_n5 :
    sqFredholmSection.1.ControlsCompactness n5 (univ : Set A5.X.OrbitSpace) := by
  refine (sqRep.controlsCompactness_iff isAuxNorm_n5 isOpen_univ).2 ?_
  rw [preimage_univ]
  change ControlsCompactness A5 sqSection (sqStructure.normOf n5) univ
  rw [normOf_n5]
  exact controlsCompactness_sqSection_univ

/-- **The solution set is compact**: it is the point `|0|`. -/
theorem hasCompactSolutionSet_sqFredholmSection : sqFredholmSection.1.HasCompactSolutionSet := by
  refine sqRep.hasCompactSolutionSet_iff.2 ?_
  have h : solutionSet A5.P sqSection = {(0 : Fin 2 → ℝ)} := by
    ext x
    exact isZeroAt_sqSection_iff
  change IsCompact (A5.X.π '' solutionSet A5.P sqSection)
  rw [h]
  exact (isCompact_singleton (x := (0 : Fin 2 → ℝ))).image A5.X.continuous_π

/-! ### The multisection with five branches -/

/-- `ζ^{2j} c ∈ ℂ = ℝ²`. -/
def branchVal (c : ℂ) (j : ZMod 5) : Fin 2 → ℝ :=
  cE.symm (χ (Multiplicative.ofAdd j) ^ 2 * c)

theorem cE_branchVal (c : ℂ) (j : ZMod 5) :
    cE (branchVal c j) = χ (Multiplicative.ofAdd j) ^ 2 * c := cE.apply_symm_apply _

theorem rot_branchVal (c : ℂ) (g : G5) (j : ZMod 5) :
    rot (χ g ^ 2) (branchVal c j) = branchVal c (Multiplicative.toAdd g + j) := by
  rw [rot_apply, cE_branchVal, branchVal]
  congr 1
  have h : Multiplicative.ofAdd (Multiplicative.toAdd g + j) = g * Multiplicative.ofAdd j := rfl
  rw [h, χ_mul, mul_pow, mul_assoc]

theorem branchVal_ne_zero {c : ℂ} (hc : c ≠ 0) (j : ZMod 5) : branchVal c j ≠ 0 := fun h => by
  have h1 : cE (branchVal c j) = 0 := by rw [h, map_zero]
  rw [cE_branchVal] at h1
  exact mul_ne_zero (pow_ne_zero 2 (χ_ne_zero _)) hc h1

theorem norm_cE_branchVal (c : ℂ) (j : ZMod 5) : ‖cE (branchVal c j)‖ = ‖c‖ := by
  rw [cE_branchVal, norm_mul, norm_pow, norm_χ, one_pow, one_mul]

theorem branchVal_injective {c : ℂ} (hc : c ≠ 0) : Injective (branchVal c) := by
  intro i j h
  have h1 := congrArg cE h
  rw [cE_branchVal, cE_branchVal] at h1
  have h2 : χ (Multiplicative.ofAdd i) ^ 2 = χ (Multiplicative.ofAdd j) ^ 2 :=
    mul_right_cancel₀ hc h1
  have h3 : χ (Multiplicative.ofAdd i * (Multiplicative.ofAdd j)⁻¹) ^ 2 = 1 := by
    have h4 : χ (Multiplicative.ofAdd i * (Multiplicative.ofAdd j)⁻¹) ^ 2 *
        χ (Multiplicative.ofAdd j) ^ 2 = 1 * χ (Multiplicative.ofAdd j) ^ 2 := by
      rw [← mul_pow, ← χ_mul, inv_mul_cancel_right, one_mul, h2]
    exact mul_right_cancel₀ (pow_ne_zero 2 (χ_ne_zero _)) h4
  have h5 := (χ_sq_eq_one_iff _).1 h3
  have h6 : Multiplicative.ofAdd i = Multiplicative.ofAdd j := mul_inv_eq_one.1 h5
  exact Multiplicative.ofAdd.injective h6

/-- The constant branch `s_j(z) = (z, ζ^{2j} c)`. -/
def branch (c : ℂ) (j : ZMod 5) : A5.Obj → A5.W := graphSection fun _ => branchVal c j

theorem branch_apply (c : ℂ) (j : ZMod 5) (x : Fin 2 → ℝ) :
    branch c j x = (x, branchVal c j) := rfl

theorem isScPlusSection_branch (c : ℂ) (j : ZMod 5) : A5.B.IsScPlusSection (branch c j) :=
  isScPlusSection_graphSection contDiff_const

/-- The morphisms permute the branches: `g · s_j(z) = s_{j+g}(g · z)`. -/
theorem actW_branch (c : ℂ) (g : G5) (j : ZMod 5) (x : Fin 2 → ℝ) :
    actW g (branch c j x) = branch c (Multiplicative.toAdd g + j) (g • x) := by
  rw [branch_apply, branch_apply, actW_apply, rot_branchVal]

open scoped Classical in
/-- **The multisection `Λ`** with the five branches `s_j`, `j ∈ ℤ/5`, of weight `1/5` each. -/
def Λ5 (c : ℂ) : A5.W → ℚ≥0 := fun w =>
  ∑ j : ZMod 5, if w = branch c j (A5.P w) then (1 / 5 : ℚ≥0) else 0

theorem Λ5_pos_iff (c : ℂ) (w : A5.W) : 0 < Λ5 c w ↔ ∃ j : ZMod 5, w = branch c j (A5.P w) := by
  classical
  unfold Λ5
  rw [Finset.sum_pos_iff]
  constructor
  · rintro ⟨j, -, hj⟩
    by_cases h : w = branch c j (A5.P w)
    · exact ⟨j, h⟩
    · rw [if_neg h] at hj
      exact absurd hj (lt_irrefl _)
  · rintro ⟨j, hj⟩
    refine ⟨j, Finset.mem_univ _, ?_⟩
    rw [if_pos hj]
    norm_num

theorem eq_branch_actW_iff (c : ℂ) (g : G5) (j : ZMod 5) (w : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    actW g w = branch c j (g • w.1) ↔ w = branch c (j - Multiplicative.toAdd g) w.1 := by
  constructor
  · intro h
    have h1 := congrArg (actW g⁻¹) h
    rw [actW_inv_actW, actW_branch, inv_smul_smul] at h1
    rw [h1]
    congr 1
    change -Multiplicative.toAdd g + j = j - Multiplicative.toAdd g
    ring
  · intro h
    conv_lhs => rw [h]
    rw [actW_branch]
    congr 1
    ring

/-- **`Λ` is a functor** `W → ℚ⁺` (Definition 13.2.1): the morphisms permute the branches. -/
theorem isWFunctor_Λ5 (c : ℂ) : IsWFunctor A5 (Λ5 c) := by
  classical
  rintro ⟨⟨⟨g, o⟩, w⟩, hq⟩
  change Λ5 c (actW g w) = Λ5 c w
  unfold Λ5
  refine Fintype.sum_equiv (Equiv.subRight (Multiplicative.toAdd g)) _ _ fun j => ?_
  exact if_congr (eq_branch_actW_iff c g j w) rfl rfl

/-- The five branches with weight `1/5` are a local representation of `Λ` on `ℂ`. -/
theorem isLocalRepOn_Λ5 (c : ℂ) :
    IsLocalRepOn A5 (Λ5 c) univ (k := 5) (fun j : Fin 5 => branch c j)
      (fun _ => (1 / 5 : ℚ≥0)) := by
  classical
  refine ⟨fun _ => by norm_num,
    fun j => IsScPlusSectionOn.of_isScPlusSection (isScPlusSection_branch c j) isOpen_univ,
    ?_, fun w _ => rfl⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- **`Λ` is an sc⁺-multisection** (Definition 13.2.1). -/
theorem isScPlusMultisection_Λ5 (c : ℂ) : IsScPlusMultisection A5 (Λ5 c) :=
  ⟨isWFunctor_Λ5 c, fun x₀ => hasLocalSectionStructure_of_isLocalRepOn isOpen_univ
    (mem_univ x₀) (isLocalRepOn_Λ5 c)⟩

/-- `f(z) = s_j(z)` iff `z² = ζ^{2j} c`. -/
theorem sqSection_eq_branch_iff (c : ℂ) (j : ZMod 5) (x : Fin 2 → ℝ) :
    sqSection x = branch c j x ↔ sq x = branchVal c j :=
  ⟨fun h => congrArg Prod.snd h, fun h => Prod.ext rfl h⟩

/-- `Λ(f(z)) > 0` iff `z² = ζ^{2j} c` for some `j`. -/
theorem Λ5_sqSection_pos_iff (c : ℂ) (x : Fin 2 → ℝ) :
    0 < Λ5 c (sqSection x) ↔ ∃ j : ZMod 5, sq x = branchVal c j :=
  (Λ5_pos_iff c _).trans (exists_congr fun j => sqSection_eq_branch_iff c j x)

/-! ### General position -/

/-- In a chart of `ℂ` (model `C` the whole space) the reduced tangent space is the tangent
space. -/
theorem mem_reducedTangentFiber_of_univ {φ : MChart A5.Obj} (hφ : A5.X.PObj.IsChart φ)
    {x : A5.X.PObj.Level 1} (hx : A5.X.PObj.levelVal 1 x ∈ φ.source) {k : ℕ} {V : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin k → ℝ)).prod V))
    (hT : φ.model.C = T 0 ⁻¹' quadrant k V 0) (hC : φ.model.C = univ)
    (α : A5.X.PObj.tangentFiber x) : α ∈ reducedTangentFiber hφ hx T := by
  have h0 : ∀ (v : φ.model.E 0) (i : Fin k), (T 0 v).1 i = 0 := by
    intro v i
    have h1 : ∀ u : φ.model.E 0, 0 ≤ (T 0 u).1 i := fun u => by
      have hu : u ∈ T 0 ⁻¹' quadrant k V 0 := by rw [← hT, hC]; exact mem_univ u
      exact hu i
    have h2 := h1 v
    have h3 := h1 (-v)
    rw [map_neg] at h3
    have h4 : (-(T 0 v)).1 i = -((T 0 v).1 i) := rfl
    rw [h4] at h3
    linarith
  exact Submodule.mem_comap.2 ((mem_minimalSubspaceWith T).2 fun i _ => h0 _ i)

/-- `D(sq − const)(z) = 2z` is onto for `z ≠ 0`. -/
theorem surjective_fderiv_sq_sub_const {x : Fin 2 → ℝ} (hx : x ≠ 0) (b : Fin 2 → ℝ) :
    Surjective (fderiv ℝ (sq - fun _ => b) x) := by
  have hd : HasFDerivAt (sq - fun _ => b) (rot (2 * cE x)) x := (hasFDerivAt_sq x).sub_const b
  rw [hd.fderiv]
  exact surjective_rot (mul_ne_zero two_ne_zero (fun h => hx (cE.map_eq_zero_iff.1 h)))

/-- **`(f, Λ)` is in general position** (Definition 15.3.5), for `c ≠ 0`: at a solution `z` of
`z² = ζ^{2j} c`, in the chart centred at `z`, `(f − s_j)'(z) = 2z` is onto `ℂ`, and `ℂ` has no
boundary. -/
theorem isInGeneralPosition_Λ5 {c : ℂ} (hc : c ≠ 0) :
    IsInGeneralPosition A5 sqSection (Λ5 c) := by
  classical
  have hf := isScFredholmSectionFunctor_sqSection
  refine isInGeneralPosition_iff_exists.2 fun x hpos => ?_
  set x₀ : Fin 2 → ℝ := A5.X.PObj.levelVal 1 x with hx₀
  obtain ⟨j₀, hj₀⟩ := (Λ5_sqSection_pos_iff c x₀).1 hpos
  have hne : x₀ ≠ 0 := fun h =>
    branchVal_ne_zero hc j₀ (by rw [← hj₀, h]; exact (sq_eq_zero_iff 0).2 rfl)
  let ch : StrongBundleChart A5.X.PObj A5.P := chart (k := 2) x₀
  have hch : A5.B.IsChart ch := isChart_chart x₀
  have hx : A5.X.PObj.levelVal 1 x ∈ ch.φ.source := mem_univ _
  obtain ⟨k, V, T, hT⟩ := ch.φ.model.isPartialQuadrant
  refine ⟨ch.φ, ch.isChart, hx, k, V, T, hT, fun L hL => ?_⟩
  have hsurj : Surjective L := by
    let d : LocalLinData A5 (Λ5 c) x :=
      ⟨univ, isOpen_univ, 5, fun j : Fin 5 => branch c j, fun _ => (1 / 5 : ℚ≥0),
        isLocalRepOn_Λ5 c, ch, hch, subset_univ _, hx⟩
    rw [linearization_eq hf d] at hL
    obtain ⟨i, hi, hLi⟩ := (mem_support_linSumIntr_iff (k := 5)
      (s := fun j : Fin 5 => branch c j) (σ := fun _ => (1 / 5 : ℚ≥0)) hf.1.1.1
      (fun _ => by norm_num) (fun _ z _ => rfl) (subset_univ _) hx L).1 hL
    rw [← hLi]
    refine (surjective_toIntr_subDeriv_iff hf.1.1 (IsScPlusSectionOn.of_isScPlusSection
      (isScPlusSection_branch c i) isOpen_univ) hch (subset_univ _) hx hi.symm).2 ?_
    set z := levelLift ch.φ 1 (A5.X.PObj.levelVal 1 x) with hzdef
    have hz : z = 0 := by
      have h1 : ch.φ.model.E.toBase 1 z = ch.φ (A5.X.PObj.levelVal 1 x) :=
        A5.X.PObj.toBase_levelLift ch.isChart hx (A5.X.PObj.levelVal_mem x)
      have h2 : ch.φ x₀ = (0 : Fin 2 → ℝ) := sub_self (show Fin 2 → ℝ from x₀)
      exact h1.trans h2
    have he : ((fun y => ch.principal sqSection y - ch.principal (branch c i) y) ∘ r ch.R) =
        loc (sq - fun _ => branchVal c i) x₀ := by
      funext u
      rfl
    intro w _
    obtain ⟨v, hv⟩ := surjective_fderiv_sq_sub_const hne (branchVal c i) w
    refine ⟨v, ⟨v, ?_⟩, ?_⟩
    · rw [hz]
      exact congrArg (fun S : (rnSc 2) 0 →L[ℝ] (rnSc 2) 0 => S v) (scDeriv_r (k := 2) x₀)
    · change scDeriv ch.U ((fun y => ch.principal sqSection y -
        ch.principal (branch c i) y) ∘ r ch.R) z v = w
      rw [he, hz]
      exact (congrArg (fun S : (rnSc 2) 0 →L[ℝ] (rnSc 2) 0 => S v)
        (scDeriv_loc (contDiff_sq.sub contDiff_const) x₀)).trans hv
  intro w
  obtain ⟨α, hα⟩ := hsurj w
  exact ⟨⟨α, mem_reducedTangentFiber_of_univ ch.isChart hx T hT rfl α⟩, hα⟩

/-! ### The sc⁺-multisection of the strong polyfold bundle -/

/-- **The sc⁺-multisection `λ`** of the strong polyfold bundle `|ℂ × ℂ| → ℂ/ℤ₅`, the class of
`Λ` (Definition 16.5.1). -/
def t5 (c : ℂ) : ScPlusMultisection sqBundle :=
  ⟦ofFunctor sqStructure rfl (Λ5 c) (isScPlusMultisection_Λ5 c)⟧

/-- `N(Λ)(z) = |c|`. -/
theorem pointwiseNorm_Λ5_le {c : ℂ} (hc : ‖c‖ ≤ 1) (x : A5.Obj) :
    pointwiseNorm N5 (Λ5 c) x ≤ 1 := by
  have hmem : ∀ w : A5.W, w ∈ A5.B.oneSet := fun w => by
    have h : (bundle 2 2).oneSet = univ := oneSet_eq
    exact h ▸ mem_univ w
  refine csSup_le ⟨_, mem_image_of_mem _ (⟨rfl, (Λ5_pos_iff c _).2 ⟨0, rfl⟩⟩ :
    branch c 0 x ∈ suppAt (Λ5 c) x)⟩ ?_
  rintro _ ⟨w, ⟨-, hw⟩, rfl⟩
  obtain ⟨j, hj⟩ := (Λ5_pos_iff c w).1 hw
  rw [normW_of_mem N5 (hmem w)]
  refine (N5_oneMk w (hmem w)).trans_le ?_
  rw [hj]
  change ‖cE (branchVal c j)‖ ≤ 1
  rw [norm_cE_branchVal]
  exact hc

/-- **`λ` is controlled by `(n, Z)`** (Definition 16.5.4), for `|c| ≤ 1`. -/
theorem isControlledBy_t5 {c : ℂ} (hc : ‖c‖ ≤ 1) :
    (t5 c).IsControlledBy n5 (univ : Set A5.X.OrbitSpace) := by
  refine ⟨fun z => ?_, subset_univ _⟩
  obtain ⟨x, rfl⟩ := sqStructure.surjective_γπ z
  set b := ofFunctor sqStructure rfl (Λ5 c) (isScPlusMultisection_Λ5 c)
  have h := normLam_eq (c := sqBundle) (S := sqStructure) rfl n5 (Λ5 c) b.lam x
    fun w _ => b.comm w
  rw [normOf_n5] at h
  exact h.le.trans (pointwiseNorm_Λ5_le hc x)

/-- **`(f, λ)` is in general position** (Definition 16.6.4), for `c ≠ 0`. -/
theorem isInGeneralPositionWith_t5 {c : ℂ} (hc : c ≠ 0) :
    sqFredholmSection.1.IsInGeneralPositionWith (t5 c) :=
  ⟨sqRep, Λ5 c, isScPlusMultisection_Λ5 c, rfl, rfl, isInGeneralPosition_Λ5 hc⟩

end Polyfold.Examples.OrbifoldSquare
