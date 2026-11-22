import Polyfold.Chapter17.BranchedOrientation
import Polyfold.Chapter17.BranchedSubcategoryExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.5 "Branched Ep⁺-Subcategories" (p. 817): witnesses for **Definition 17.5.8** (orientations)
with non-empty support.  Numbers and pages are the 2021 text's.

# Orientations of branched ep⁺-subcategories: witnesses

## What is formalized

* On `K ⋉ ℝ` with the tautological polyfold structure (`tautConstruction`), `K` a finite group
  with `k ∗ 0 = 0`, and `Θ₀ = 1_{0}` a branched ep⁺-subcategory: the oriented subspace
  `pointTangentC b = (TΨ₀(T_0{0}), ±)` of `T_0C` and the section `pointOrientationC b`
  (`T̂_±(0) = 1 · (TΨ₀(T_0{0}), ±)`, `0` elsewhere).
* The conditions of Definition 17.5.8 on `C`: `pointOrientationC_mem`, `pointOrientationC_natural`
  (`move_pointTangentC`: the morphisms `(k, 0)` fix `(TΨ₀(T_0{0}), ±)`), `pointOrientationC_lifts`
  (`f ∘ T̂_± = TΘ₀`, through `branchedTangentSection_eq_unif`).
* `isOrientation_unifSectionPull_pointOrientationC` (`TΨ₀^*T̂_±` is an orientation of `Θ₀ ∘ Ψ₀`,
  the point `{0}` with orientation `±` as oriented local branching structure,
  `pointOrientedBranching`), and **`isOrientationC_pointOrientationC`** (Definition 17.5.8, via
  Remark 17.5.9 "⇐", `isOrientationC_of_unif`).
* `pointOrientationC_ne`: `T̂_+ ≠ T̂_-`, and `T̂_±(0) ≠ 0` at `0 ∈ supp(Θ₀)`.
* Instances: `isOrientationC_reflection` (`ℤ/2 ⋉ ℝ`, `Θ₀(0) = 1`, `0` with isotropy `ℤ/2`) and
  `isOrientationC_unitTaut` (`{1} ⋉ ℝ`).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

namespace GCT.PolyfoldConstruction

open EpGroupoid.Examples

section PointOrientation

variable {K : Type} [Group K] [Finite K] [TopologicalSpace K] [DiscreteTopology K]
  [MulAction K (Fin 1 → ℝ)]
  (hP : ∀ k : K, (rnPolyfold 1).IsScSmoothMap (rnPolyfold 1) fun y : Fin 1 → ℝ => k • y)

theorem tautConstruction_hasUniformizers : (tautConstruction hP).HasUniformizers :=
  twistConstruction_hasUniformizers _ _

theorem zero_mem_smoothSet_rnPolyfold : (0 : Fin 1 → ℝ) ∈ (rnPolyfold 1).smoothSet := by
  rw [TrivialBundle.rnPolyfold_smoothSet]; exact mem_univ _

/-- `T_0C ⊃ TΨ₀(T_0{0})` with the orientation `+` (for `b = true`; `−` otherwise) of the point:
the oriented `0`-dimensional subspace of Definition 17.5.8 (frames `Fin 0 → T_0C`). -/
def pointTangentC (b : Bool) : (tautConstruction hP).OrTC :=
  ⟨0, (tautConstruction hP).tangentUnifObj (tautConstruction_hasUniformizers hP)
      (tautUnif hP _ 0) '' (rnPolyfold 1).submanifoldTangent {0} 0,
    if b then univ else ∅⟩

open scoped Classical in
/-- **`T̂_± = 1 · (T_0{0}, ±)` at `0` and `0` elsewhere**, a section of `Gr̂(C) → C_∞` over
`K ⋉ ℝ`. -/
def pointOrientationC (b : Bool) : (Fin 1 → ℝ) → (tautConstruction hP).OrTC →₀ ℚ :=
  fun α => if α = 0 then Finsupp.single (pointTangentC hP b) 1 else 0

/-- Every set of (empty) frames orients `T_0{0}` (the two orientations `±` of a point,
Chapter 9's `exists_two_orientations_point`). -/
theorem isOrientedAt_zero (O : Set (Fin 0 → (rnPolyfold 1).TangentSpace)) :
    (rnPolyfold 1).IsOrientedAt 0 ⟨0, (rnPolyfold 1).submanifoldTangent {0} 0, O⟩ := by
  obtain ⟨O₁, O₂, hne, h₁, h₂⟩ := EpGroupoid.exists_two_orientations_point (0 : Fin 1 → ℝ)
  have key : ∀ O' : Set (Fin 0 → (rnPolyfold 1).TangentSpace), O' = ∅ ∨ O' = univ := fun O' =>
    (Set.eq_empty_or_nonempty O').imp id Set.Nonempty.eq_univ
  rcases key O with rfl | rfl <;> rcases key O₁ with rfl | rfl <;>
    rcases key O₂ with rfl | rfl <;> first | exact absurd rfl hne | assumption

/-- The orientation `+` (for `b = true`; `−` otherwise) of the point `{0}`. -/
def pointOrientationRn (b : Bool) : (rnPolyfold 1).SubmanifoldOrientation {0} 0 :=
  MPolyfold.SubmanifoldOrientation.ofPoint (if b then univ else ∅) (isOrientedAt_zero _)

open scoped Classical in
/-- The local branching structure of `1_{0}` at `0` on `K ⋉ ℝ`: `U = ℝ`, `M = {0}`, weight `1`. -/
def pointLocalBranching :
    (actionEpGroupoid hP).LocalBranchingStructure reflectionTheta 0 where
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
    · subst hy; simp [reflectionTheta]
    · simp [reflectionTheta, hy]

instance : Unique (pointLocalBranching hP).ι := inferInstanceAs (Unique Unit)

/-- The oriented local branching structure: the point `{0}` with orientation `±`
(Chapter 9's `pointOrientation`). -/
def pointOrientedBranching (b : Bool) :
    (actionEpGroupoid hP).OrientedBranchingStructure reflectionTheta 0 where
  toLocalBranchingStructure := pointLocalBranching hP
  dim _ := 0
  isSubmanifoldOfDim _ := EpGroupoid.rnPolyfold_isSubmanifoldOfDim_singleton 0
  orient _ := pointOrientationRn b

variable {hP}

theorem orientedSum_pointOrientedBranching (b : Bool) (y : Fin 1 → ℝ) :
    (pointOrientedBranching hP b).orientedSum y = if y = 0 then
      Finsupp.single (((pointOrientedBranching hP b).orient ()).tangent 0) 1 else 0 := by
  classical
  unfold EpGroupoid.OrientedBranchingStructure.orientedSum
  by_cases hy : y = 0
  · subst hy
    rw [if_pos rfl]
    exact Finset.sum_eq_single_of_mem () (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
      fun i _ h => absurd (Subsingleton.elim i ()) h
  · rw [if_neg hy]
    exact Finset.sum_eq_zero fun i hi => absurd (Finset.mem_filter.1 hi).2 hy

theorem base_of_mem_pointTangentC {b : Bool} {e : (tautConstruction hP).TangentCatObj}
    (he : e ∈ (pointTangentC hP b).carrier) : e.base = 0 := by
  obtain ⟨k, hk, rfl⟩ := he
  exact (tangentUnifObj_base _ _ k).trans hk.1

theorem mem_levelSet_zero (k : K) :
    (k, (0 : Fin 1 → ℝ)) ∈ (actionEpGroupoid hP).PMor.levelSet 1 :=
  ((actionEpGroupoid hP).mem_levelSet_src_iff (k, 0) 1).1
    (mem_iInter.1 zero_mem_smoothSet_rnPolyfold 1)

/-- `T(k ∗ ·)(T_0{0}) = T_0{0}` for `k ∗ 0 = 0`. -/
theorem image_tangentMor_submanifoldTangent (hfix : ∀ k : K, k • (0 : Fin 1 → ℝ) = 0) (k : K) :
    (actionEpGroupoid hP).tangentMor (k, 0) '' (rnPolyfold 1).submanifoldTangent {0} 0 =
      (rnPolyfold 1).submanifoldTangent {0} 0 := by
  have hd : (rnPolyfold 1).IsScDiffeoOn (rnPolyfold 1) (fun y => k • y) (fun y => k⁻¹ • y)
      univ univ :=
    ⟨hP k, hP k⁻¹, mapsTo_univ _ _, mapsTo_univ _ _, fun y _ => inv_smul_smul k y,
      fun y _ => smul_inv_smul k y⟩
  have h1 := MPolyfold.submanifoldTangent_image hd (rnPolyfold_isSmoothSubmanifold_singleton 1 0)
    (subset_univ _) (mem_singleton 0)
  simp only [image_singleton, hfix] at h1
  refine (image_congr fun a ha => tangentMor_actionEpGroupoid hP (mem_levelSet_zero k) ha.1).trans
    ?_
  rw [← MPolyfold.tangentMapOn_univ (hP k)]
  exact h1.symm

/-- **`Tχ(T̂_±(0)) = T̂_±(0)`** for the morphisms `χ = (k, 0) : 0 → 0` (`TΨ₀` is `K`-equivariant,
`Ψ̂₀` being continuous). -/
theorem move_pointTangentC (hfix : ∀ k : K, k • (0 : Fin 1 → ℝ) = 0) (b : Bool) (k : K) :
    OrTC.move (tautConstruction hP) (k, 0) (pointTangentC hP b) = pointTangentC hP b := by
  have hc := twist_continuous_hat hP (TranslationTwist.refl K (Fin 1 → ℝ)) 0 continuous_id
  have hU := tautConstruction_hasUniformizers hP
  simp only [OrTC.move, pointTangentC]
  congr 1
  · rw [image_image]
    have h : ∀ a ∈ (rnPolyfold 1).submanifoldTangent {0} 0,
        (tautConstruction hP).tcMove (k, 0)
          ((tautConstruction hP).tangentUnifObj hU (tautUnif hP _ 0) a) =
        (tautConstruction hP).tangentUnifObj hU (tautUnif hP _ 0)
          ((actionEpGroupoid hP).tangentMor (k, 0) a) := fun a ha =>
      (tangentUnifObj_tangentMor hU hc (mem_levelSet_zero k) ha.1).symm
    rw [image_congr h]
    exact (image_image _ _ _).symm.trans
      (congrArg (image _) (image_tangentMor_submanifoldTangent hfix k))
  · cases b
    · exact image_empty _
    · exact eq_univ_of_forall fun v => ⟨v, mem_univ _, Subsingleton.elim _ _⟩

/-! #### The conditions of Definition 17.5.8 on `C` -/

theorem pointOrientationC_mem (b : Bool) (α : Fin 1 → ℝ) :
    pointOrientationC hP b α ∈ (tautConstruction hP).GrHatC α := by
  classical
  unfold pointOrientationC
  split_ifs with hα
  · subst hα
    refine ⟨fun g => ?_, fun g hg => ?_⟩
    · rw [Finsupp.single_apply]; split_ifs <;> norm_num
    · obtain rfl : g = pointTangentC hP b :=
        Finset.mem_singleton.1 (Finsupp.support_single_subset hg)
      exact ⟨fun e he => base_of_mem_pointTangentC he, fun _ _ i => i.elim0⟩
  · exact ⟨fun _ => le_rfl, fun g hg => by simp at hg⟩

theorem pointOrientationC_natural (hfix : ∀ k : K, k • (0 : Fin 1 → ℝ) = 0) (b : Bool)
    (χ : K × (Fin 1 → ℝ)) :
    pointOrientationC hP b ((GCT.translation K (Fin 1 → ℝ) hP).toGroupoidStr.tgt χ) =
      (tautConstruction hP).grHatPushC χ (pointOrientationC hP b
        ((GCT.translation K (Fin 1 → ℝ) hP).toGroupoidStr.src χ)) := by
  classical
  obtain ⟨k, x⟩ := χ
  change pointOrientationC hP b (k • x) =
    (tautConstruction hP).grHatPushC (k, x) (pointOrientationC hP b x)
  by_cases hx : x = 0
  · subst hx
    rw [hfix]
    unfold pointOrientationC
    rw [if_pos rfl, grHatPushC, Finsupp.mapDomain_single, move_pointTangentC hfix]
  · have hkx : k • x ≠ 0 := fun h => hx (by rw [← inv_smul_smul k x, h, hfix])
    unfold pointOrientationC
    rw [if_neg hx, if_neg hkx, grHatPushC, Finsupp.mapDomain_zero]

/-- **`f ∘ T̂_± = TΘ₀`**: `TΘ₀(0) = 1 · TΨ₀(T_0{0})` (Proposition 17.5.7 through the covering family
`{Ψ₀}`), and `TΘ₀ = 0` off `0`. -/
theorem pointOrientationC_lifts (hΘ : (tautConstruction hP).IsBranchedSubcategory reflectionTheta)
    (b : Bool) (α : Fin 1 → ℝ) :
    (tautConstruction hP).grForgetC (pointOrientationC hP b α) =
      (tautConstruction hP).branchedTangentSection (tautConstruction_hasUniformizers hP)
        reflectionTheta α := by
  classical
  have hU := tautConstruction_hasUniformizers hP
  have hα : (tautConstruction hP).IsSmoothObj α :=
    (isSmoothObj_obj_iff (tautUnif hP _ 0) α).2 (by
      change α ∈ (rnPolyfold 1).smoothSet
      rw [TrivialBundle.rnPolyfold_smoothSet]; exact mem_univ _)
  by_cases h0 : α = 0
  · subst h0
    have htv : (tautUnif hP (TranslationTwist.refl K (Fin 1 → ℝ)) 0).1.ep.tangentValue
        (reflectionTheta ∘ (tautUnif hP (TranslationTwist.refl K (Fin 1 → ℝ)) 0).1.obj) 0 =
        Finsupp.single ((rnPolyfold 1).submanifoldTangent {0} 0) 1 :=
      ((tautUnif hP (TranslationTwist.refl K (Fin 1 → ℝ)) 0).1.ep.tangentValue_eq
        ((tautUnif hP _ 0).1.ep.hasIndependentTangentSums _) (pointLocalBranching hP)).trans
        (Fintype.sum_unique _)
    rw [pointOrientationC, if_pos rfl, grForgetC, Finsupp.mapDomain_single]
    refine Eq.symm ((branchedTangentSection_eq_unif hU hΘ (tautUnif hP _ 0) 0
      (tangentObj_of_isSmoothObj hU hα)
      (φ := (GCT.translation K (Fin 1 → ℝ) hP).toGroupoidStr.unit 0) rfl
      ((GCT.translation K (Fin 1 → ℝ) hP).toGroupoidStr.tgt_unit 0)).trans ?_)
    refine (congrArg (Finsupp.mapDomain _) htv).trans
      (Finsupp.mapDomain_single.trans (congrArg (Finsupp.single · 1) ?_))
    refine image_congr fun a ha => ?_
    have hb : ((tautConstruction hP).tangentUnifObj hU (tautUnif hP _ 0) a).base = 0 :=
      (tangentUnifObj_base _ _ a).trans ha.1
    have h := tcMove_unit ((tautConstruction hP).tangentUnifObj hU (tautUnif hP _ 0) a)
    rw [hb] at h
    exact h
  · rw [pointOrientationC, if_neg h0, grForgetC, Finsupp.mapDomain_zero,
      branchedTangentSection_eq_zero hU hΘ (tangentObj_of_isSmoothObj hU hα)
        (by rw [reflectionTheta_apply, if_neg h0]; exact lt_irrefl 0)]

/-! #### The uniformizer `Ψ₀` -/

/-- `TΨ₀(0)⁻¹(T̂_±(0)) = T_0({0}, ±)`. -/
theorem unifOrPull_pointTangentC (b : Bool) :
    (tautConstruction hP).unifOrPull (tautConstruction_hasUniformizers hP) (tautUnif hP _ 0) 0
      (pointTangentC hP b) =
      ⟨0, (rnPolyfold 1).submanifoldTangent {0} 0, if b then univ else ∅⟩ := by
  have hinj := injective_tangentUnifObj (tautConstruction_hasUniformizers hP) (tautUnif hP _ 0)
  simp only [unifOrPull, pointTangentC]
  congr 1
  · ext k
    constructor
    · rintro ⟨-, k', hk', h⟩
      exact hinj h ▸ hk'
    · intro hk
      exact ⟨hk.1, k, hk, rfl⟩
  · cases b
    · ext v
      simp only [IsEmpty.forall_iff, Bool.false_eq_true, ↓reduceIte, true_and, mem_ofPred_eq,
        mem_empty_iff_false, iff_false]
      exact Set.notMem_empty _
    · refine eq_univ_of_forall fun v => ?_
      exact ⟨fun i => i.elim0, mem_univ _⟩

/-- **`TΨ₀^*T̂_±` is an orientation of `Θ₀ ∘ Ψ₀`** on `K ⋉ ℝ` (Definition 9.3.2): naturality from
the continuity of `Ψ̂₀`, and the point `{0}` with orientation `±` as oriented local
representation at `0`. -/
theorem isOrientation_unifSectionPull_pointOrientationC
    (hfix : ∀ k : K, k • (0 : Fin 1 → ℝ) = 0) (b : Bool) :
    (tautUnif hP (TranslationTwist.refl K (Fin 1 → ℝ)) 0).1.ep.IsOrientation
      (reflectionTheta ∘ (tautUnif hP (TranslationTwist.refl K (Fin 1 → ℝ)) 0).1.obj)
      ((tautConstruction hP).unifSectionPull (tautConstruction_hasUniformizers hP)
        (tautUnif hP _ 0) (pointOrientationC hP b)) := by
  classical
  have hU := tautConstruction_hasUniformizers hP
  have hc := twist_continuous_hat hP (TranslationTwist.refl K (Fin 1 → ℝ)) 0 continuous_id
  refine EpGroupoid.isOrientation_of_hasOrientedRepAt
    (grHatPush_unifSectionPull hU hc (fun α _ => pointOrientationC_mem b α)
      (fun χ _ => pointOrientationC_natural hfix b χ)) (fun q _ hq => ?_) (fun q hq => ?_)
  · have hq0 : q ≠ 0 := fun h => hq (by
      change 0 < reflectionTheta q
      rw [reflectionTheta_apply, if_pos h]; exact one_pos)
    change ((pointOrientationC hP b q).mapDomain _) = 0
    rw [pointOrientationC, if_neg hq0, Finsupp.mapDomain_zero]
  · have hq0 : q = 0 := by
      by_contra h
      have : ¬ 0 < reflectionTheta q := by rw [reflectionTheta_apply, if_neg h]; exact lt_irrefl 0
      exact this hq
    subst hq0
    refine ⟨pointOrientedBranching hP b, fun y _ _ => ?_⟩
    refine Eq.trans ?_ (orientedSum_pointOrientedBranching b y).symm
    change ((pointOrientationC hP b y).mapDomain _) = _
    by_cases hy : y = 0
    · subst hy
      rw [pointOrientationC, if_pos rfl, if_pos rfl, Finsupp.mapDomain_single,
        unifOrPull_pointTangentC]
      rfl
    · rw [pointOrientationC, if_neg hy, if_neg hy, Finsupp.mapDomain_zero]
      rfl

/-- **Definition 17.5.8, witness with non-empty support**: on `K ⋉ ℝ` with the tautological
polyfold structure, for a finite group `K` fixing `0`, `T̂_±` is an orientation of the branched
ep⁺-subcategory `Θ₀ = 1_{0}` (through Remark 17.5.9, `isOrientationC_of_unif`). -/
theorem isOrientationC_pointOrientationC
    (hΘ : (tautConstruction hP).IsBranchedSubcategory reflectionTheta)
    (hfix : ∀ k : K, k • (0 : Fin 1 → ℝ) = 0) (b : Bool) :
    (tautConstruction hP).IsOrientationC (tautConstruction_hasUniformizers hP) reflectionTheta
      (pointOrientationC hP b) :=
  isOrientationC_of_unif _ hΘ (fun α _ => pointOrientationC_mem b α)
    (fun χ _ => pointOrientationC_natural hfix b χ) (fun α _ => pointOrientationC_lifts hΘ b α)
    fun α _ Ψ hΨ => by
      obtain rfl := mem_singleton_iff.1 hΨ
      exact isOrientation_unifSectionPull_pointOrientationC hfix b

/-- **The two orientations are different** and do not vanish at `0 ∈ supp(Θ₀)`. -/
theorem pointOrientationC_ne :
    pointOrientationC hP true ≠ pointOrientationC hP false ∧
      ∀ b, pointOrientationC hP b 0 ≠ 0 := by
  classical
  refine ⟨fun h => ?_, fun b h => ?_⟩
  · have h1 := congrFun h 0
    rw [pointOrientationC, pointOrientationC, if_pos rfl, if_pos rfl] at h1
    have h2 := Finsupp.single_left_injective (one_ne_zero (α := ℚ)) h1
    have h3 := congrArg (fun g : (tautConstruction hP).OrTC => g.frames.Nonempty) h2
    simp [pointTangentC] at h3
  · rw [pointOrientationC, if_pos rfl] at h
    exact one_ne_zero (Finsupp.single_eq_zero.1 h)

end PointOrientation

/-! ### `ℤ/2 ⋉ ℝ` and `{1} ⋉ ℝ` -/

/-- **Definition 17.5.8 on the reflection polyfold `ℤ/2 ⋉ ℝ`**: `T̂_±` are two different
orientations of `Θ₀ = 1_{0}` (`Θ₀(0) = 1`, `0` with isotropy `ℤ/2`). -/
theorem isOrientationC_reflection (b : Bool) :
    reflectionConstruction.IsOrientationC reflectionConstruction_hasUniformizers
      reflectionThetaC (pointOrientationC isScSmoothMap_units_smul b) :=
  isOrientationC_pointOrientationC isBranchedSubcategory_reflectionThetaC
    (fun k => smul_zero k) b

/-- **Definition 17.5.8 on `{1} ⋉ ℝ`**: `T̂_±` are two different orientations of `1_{0}`. -/
theorem isOrientationC_unitTaut (b : Bool) :
    unitTautConstruction.IsOrientationC (tautConstruction_hasUniformizers isScSmoothMap_z1_smul)
      unitThetaC (pointOrientationC isScSmoothMap_z1_smul b) :=
  isOrientationC_pointOrientationC isBranchedSubcategory_unitThetaC (fun _ => rfl) b

end GCT.PolyfoldConstruction

end Polyfold
