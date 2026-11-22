import Polyfold.Chapter17.BranchedTangent
import Polyfold.Chapter17.ModelPropertiesExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.5 "Branched Ep⁺-Subcategories" (pp. 812–817): witnesses for **Definition 17.5.1**,
**Definition 17.5.4**, **Proposition 17.5.5**, **Definition 17.5.6** and **Proposition 17.5.7**.
Numbers and pages are the 2021 text's.

# Branched ep⁺-subcategories: witnesses

## What is formalized

* **Orbifold type with non-trivial isotropy**: on the reflection polyfold `ℤ/2 ⋉ ℝ`
  (`reflectionConstruction`), `Θ₀ = 1_{0}` (Chapter 11's `reflectionTheta`) is a branched
  ep⁺-subcategory (`isBranchedSubcategory_reflectionThetaC`) with `Θ₀(0) = 1`, of orbifold type
  (`isOrbifoldTypeBranched_reflectionThetaC`) and not of manifold type
  (`not_isManifoldTypeBranched_reflectionThetaC`: `0` has the two automorphisms `±1`); `0` is in
  `C¹` (`tangentObj_reflection_zero`), so the formulas of Proposition 17.5.7 apply at `0`.
* **Manifold type**: on `{1} ⋉ ℝ` (`unitTautConstruction`), `1_{0}` is a branched
  ep⁺-subcategory of manifold type (`isBranchedSubcategory_unitThetaC`,
  `isManifoldTypeBranched_unitThetaC`), so Proposition 17.5.5 (1) has a witness with non-empty
  support.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

namespace GCT.PolyfoldConstruction

open EpGroupoid.Examples

/-! ### `Θ₀ = 1_{0}` on `ℤ/2 ⋉ ℝ` -/

/-- `Θ₀ = 1_{0}` as a function on the objects of the reflection GCT `ℤ/2 ⋉ ℝ`. -/
abbrev reflectionThetaC : GCT.reflection.Obj → ℚ := reflectionTheta

/-- **Definition 17.5.1, non-degenerate witness**: `Θ₀` is a branched ep⁺-subcategory of the
reflection polyfold (`F(x) = {Ψ₀}`, `Θ₀ ∘ Ψ₀ = Θ₀`, Chapter 11's
`isBranchedEpSubgroupoid_reflectionTheta`). -/
theorem isBranchedSubcategory_reflectionThetaC :
    reflectionConstruction.IsBranchedSubcategory reflectionThetaC where
  nonneg := isBranchedEpSubgroupoid_reflectionTheta.nonneg
  isFunctorial := isBranchedEpSubgroupoid_reflectionTheta.isFunctorial
  isBranched α Ψ hΨ := by
    obtain rfl := Set.mem_singleton_iff.1 hΨ
    exact isBranchedEpSubgroupoid_reflectionTheta

/-- The support is non-empty: `Θ₀(0) = 1`. -/
theorem reflectionThetaC_zero : reflectionThetaC 0 = 1 := by
  simp [reflectionThetaC, reflectionTheta_apply]

/-- `Θ₀` is of orbifold type (Definition 17.5.4 (2)). -/
theorem isOrbifoldTypeBranched_reflectionThetaC :
    GCT.reflection.IsOrbifoldTypeBranched reflectionThetaC := fun α => by
  change reflectionTheta α = 0 ∨ reflectionTheta α = 1
  rw [reflectionTheta_apply]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- `Θ₀` is not of manifold type: `±1 : 0 → 0` are two different morphisms in `supp(Θ₀)`. -/
theorem not_isManifoldTypeBranched_reflectionThetaC :
    ¬ GCT.reflection.IsManifoldTypeBranched reflectionThetaC := by
  rintro ⟨-, h⟩
  have h1 := h ((1 : ℤˣ), (0 : Fin 1 → ℝ)) ((-1 : ℤˣ), (0 : Fin 1 → ℝ))
    (by change 0 < reflectionTheta 0; rw [reflectionTheta_apply, if_pos rfl]; norm_num)
    (by change 0 < reflectionTheta ((1 : ℤˣ) • 0); rw [smul_zero, reflectionTheta_apply,
      if_pos rfl]; norm_num)
    rfl (by change (1 : ℤˣ) • (0 : Fin 1 → ℝ) = (-1 : ℤˣ) • 0; rw [smul_zero, smul_zero])
  have h2 := congrArg Prod.fst h1
  exact absurd h2 (by decide)

/-- `0 ∈ C¹` with `F(0) ≠ ∅`. -/
theorem tangentObj_reflection_zero : reflectionConstruction.TangentObj (0 : Fin 1 → ℝ) :=
  ⟨⟨reflectionUnif, 0, GroupoidStr.isomorphic_refl _ _, by
      change (0 : Fin 1 → ℝ) ∈ (rnPolyfold 1).levelSet 1
      rw [rnPolyfold_levelSet]; exact mem_univ _⟩,
    reflectionConstruction_hasUniformizers _⟩

/-! ### `1_{0}` on `{1} ⋉ ℝ`: manifold type -/

/-- `1_{0}` as a function on the objects of `{1} ⋉ ℝ`. -/
abbrev unitThetaC : (GCT.translation (Multiplicative (ZMod 1)) (Fin 1 → ℝ)
    isScSmoothMap_z1_smul).Obj → ℚ :=
  ({0} : Set (Fin 1 → ℝ)).indicator 1

open scoped Classical in
/-- The local branching structure of `1_{0}` at `0`: `U = ℝ`, `M = {0}`, weight `1`. -/
def localBranchingStructure_unitTheta :
    (actionEpGroupoid isScSmoothMap_z1_smul).LocalBranchingStructure unitThetaC 0 where
  U := univ
  isOpen_U := isOpen_univ
  mem_U := mem_univ _
  ι := Unit
  M _ := {0}
  subset_U _ := subset_univ _
  isSmoothSubmanifold _ := rnPolyfold_isSmoothSubmanifold_singleton 1 0
  mem_M _ := rfl
  isProperMap _ := (continuous_inclusion _).isProperMap
  σ _ := 1
  σ_pos _ := one_pos
  eq_sum y _ := by
    by_cases hy : y = 0
    · subst hy; simp [unitThetaC]
    · simp [unitThetaC, hy]

theorem isBranchedEpSubgroupoid_unitTheta :
    (actionEpGroupoid isScSmoothMap_z1_smul).IsBranchedEpSubgroupoid unitThetaC where
  nonneg z := by
    by_cases h : z = 0
    · subst h; simp [unitThetaC]
    · simp [unitThetaC, h]
  isFunctorial _ := rfl
  support_subset z _ := by
    change z ∈ (rnPolyfold 1).smoothSet
    rw [TrivialBundle.rnPolyfold_smoothSet]; exact mem_univ z
  paracompactSpace_orbitSupp := by
    have hs : EpGroupoid.supp unitThetaC = {0} := by
      ext z
      by_cases h : z = 0 <;> simp [EpGroupoid.supp, unitThetaC, h]
    have hc : IsCompact ((actionEpGroupoid isScSmoothMap_z1_smul).orbitSupp unitThetaC) := by
      unfold EpGroupoid.orbitSupp
      rw [hs, image_singleton]
      exact isCompact_singleton
    have := isCompact_iff_compactSpace.1 hc
    infer_instance
  localBranching z hz := by
    have hz0 : z = 0 := by
      by_contra h
      have : ¬ (0 < unitThetaC z) := by simp [unitThetaC, h]
      exact this hz
    subst hz0
    exact ⟨localBranchingStructure_unitTheta⟩

/-- **Definition 17.5.1, witness of manifold type**: `1_{0}` is a branched ep⁺-subcategory of
`{1} ⋉ ℝ`. -/
theorem isBranchedSubcategory_unitThetaC :
    unitTautConstruction.IsBranchedSubcategory unitThetaC where
  nonneg := isBranchedEpSubgroupoid_unitTheta.nonneg
  isFunctorial := isBranchedEpSubgroupoid_unitTheta.isFunctorial
  isBranched α Ψ hΨ := by
    obtain rfl := Set.mem_singleton_iff.1 hΨ
    exact isBranchedEpSubgroupoid_unitTheta

theorem unitThetaC_zero : unitThetaC 0 = 1 := by simp [unitThetaC]

/-- **Definition 17.5.4 (1), witness**: `1_{0}` is of manifold type (`{1}` acts trivially, so
between two objects there is at most one morphism). -/
theorem isManifoldTypeBranched_unitThetaC :
    (GCT.translation (Multiplicative (ZMod 1)) (Fin 1 → ℝ)
      isScSmoothMap_z1_smul).IsManifoldTypeBranched unitThetaC := by
  refine ⟨fun α => ?_, fun φ ψ _ _ hs _ => ?_⟩
  · by_cases h : α = 0
    · subst h; exact Or.inr (by simp [unitThetaC])
    · exact Or.inl (by simp [unitThetaC, h])
  · exact Prod.ext (Subsingleton.elim _ _) hs

end GCT.PolyfoldConstruction

end Polyfold
