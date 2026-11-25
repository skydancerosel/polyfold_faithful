import Polyfold.Chapter6.IntervalEndInclusion
import Polyfold.Chapter10.WeakFibredProductTheorem
import Polyfold.Chapter11.BranchedEquivalenceLocalization
import Polyfold.Chapter11.BranchedEquivalenceTangentOrientation

/-!
# Examples for Chapters 10 and 11: weak fibred products, push-forward and pull-back

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Theorem 10.2.2 (p. 477),
the push-forward and pull-back of branched ep⁺-subgroupoids along generalized maps (p. 536) and
Theorem 11.3.5 (p. 539).

## What is formalized (namespace `Polyfold.Examples.Path`)

* `reflIncl`: the inclusion of the trivial ep-groupoid `ℝ` into `ℤ/2 ⋉ ℝ`, the identity on
  objects.  It is a local sc-diffeomorphism on objects but not an equivalence
  (`not_isEquivalence_reflIncl`); the pair `(reflIncl, reflIncl)` is admissible
  (`admissible_reflIncl`), and the objects of `ℝ ×_{ℤ/2 ⋉ ℝ} ℝ` lie over the two lines `z = ±x`
  (`exists_obj_reflIncl_iff`).
* `reflConst`: the constant functor of `ℤ/2 ⋉ ℝ` at `0`; it is not a local sc-diffeomorphism on
  objects, so `(reflConst, reflConst)` is not admissible (`not_admissible_reflConst`).
* `constDiagram`: the generalized map `[ℤ/2 ⋉ ℝ ←1 ℤ/2 ⋉ ℝ →reflConst ℤ/2 ⋉ ℝ]`, which is not a
  generalized isomorphism (`not_isGeneralizedIso_constDiagram`); the pull-back of `Θ₀ = 1_{0}`
  along it is the constant function `1` (`pullTheta_constDiagram`).
* `example935Oriented_pull_push`: `f^* f_* Θ̂ = Θ̂` for Example 9.3.5 and the identity class.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold.Examples.Path

open Polyfold Polyfold.EpGroupoid.Examples Polyfold.EPLocalization Polyfold.EPLocalization.EPLoc
  Polyfold.WeakFibredProduct

/-! ### Theorem 10.2.2: admissible pairs -/

/-- Every point of `ℝ` is smooth. -/
theorem mem_smoothSet_rn1 (y : Fin 1 → ℝ) : y ∈ (rnPolyfold 1).smoothSet := by
  rw [TrivialBundle.rnPolyfold_smoothSet]; exact mem_univ y

/-- Row V10.18, Theorem 10.2.2 (p. 477): the inclusion of the trivial ep-groupoid `ℝ` into
`ℤ/2 ⋉ ℝ`, `y ↦ y` on objects and `y ↦ (1, y)` on morphisms. -/
def reflIncl : EpFunctor (EpGroupoid.trivial (rnPolyfold 1)) reflectionEpGroupoid where
  obj := id
  mor := reflectionEpGroupoid.unit
  src_mor := reflectionEpGroupoid.src_unit
  tgt_mor := reflectionEpGroupoid.tgt_unit
  mor_comp φ ψ h := by
    change ((1 : ℤˣ), φ) = ((1 : ℤˣ) * 1, ψ)
    rw [mul_one]
    exact Prod.ext rfl h
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor := reflectionEpGroupoid.isScSmoothMap_unit

/-- Row V10.18, Theorem 10.2.2 (p. 477): `reflIncl` is not an equivalence, since `1` and `-1`
lie in one orbit of `ℤ/2 ⋉ ℝ` but in two orbits of the trivial ep-groupoid. -/
theorem not_isEquivalence_reflIncl : ¬ reflIncl.IsEquivalence := fun h => by
  have e : reflIncl.orbitMap ((EpGroupoid.trivial (rnPolyfold 1)).π fun _ => (1 : ℝ)) =
      reflIncl.orbitMap ((EpGroupoid.trivial (rnPolyfold 1)).π fun _ => (-1 : ℝ)) := by
    change reflectionEpGroupoid.π (fun _ => (1 : ℝ)) = reflectionEpGroupoid.π fun _ => (-1 : ℝ)
    refine (action_π_eq_π_iff isScSmoothMap_units_smul).2 ⟨-1, ?_⟩
    rw [units_smul_rn_neg_one]
    funext; simp
  obtain ⟨φ, h₁, h₂⟩ :=
    (EpGroupoid.trivial (rnPolyfold 1)).π_eq_π_iff.1 (h.isHomeomorph_orbitMap.injective e)
  have h₃ := congrFun (h₁.symm.trans h₂) 0
  norm_num at h₃

/-- Row V10.18, Theorem 10.2.2 (p. 477): the pair `(reflIncl, reflIncl)` is admissible (`reflIncl`
is a local sc-diffeomorphism on objects), although neither functor is an equivalence. -/
theorem admissible_reflIncl : Admissible reflIncl reflIncl ∧ ¬ reflIncl.IsEquivalence :=
  ⟨Or.inl MPolyfold.isLocalScDiffeo_id, not_isEquivalence_reflIncl⟩

/-- Row V10.18, Theorem 10.2.2 (p. 477): the ep-groupoid `ℝ ×_{ℤ/2 ⋉ ℝ} ℝ`. -/
def reflInclProduct : EpGroupoid (Obj reflIncl reflIncl) (Mor reflIncl reflIncl) :=
  epGroupoid reflIncl reflIncl admissible_reflIncl.1

/-- Row V10.18, Theorem 10.2.2 (p. 477): an object `(x, φ, z)` of `ℝ ×_{ℤ/2 ⋉ ℝ} ℝ` over `(x, z)`
exists iff `z = x` or `z = -x`. -/
theorem exists_obj_reflIncl_iff (x z : Fin 1 → ℝ) :
    (∃ p : Obj reflIncl reflIncl, p.x = x ∧ p.z = z) ↔ z = x ∨ z = -x := by
  constructor
  · rintro ⟨p, rfl, rfl⟩
    have hs := p.src_φ
    have ht := p.tgt_φ
    change p.φ.2 = p.x at hs
    change p.φ.1 • p.φ.2 = p.z at ht
    rw [hs] at ht
    rcases Int.units_eq_one_or p.φ.1 with hg | hg
    · rw [hg, one_smul] at ht; exact Or.inl ht.symm
    · rw [hg, units_smul_rn_neg_one] at ht; exact Or.inr ht.symm
  · rintro (rfl | rfl)
    · exact ⟨Obj.mk reflIncl reflIncl z (1, z) z rfl (one_smul _ _), rfl, rfl⟩
    · exact ⟨Obj.mk reflIncl reflIncl x (-1, x) (-x) rfl (units_smul_rn_neg_one x), rfl, rfl⟩

/-- Row V10.18, Theorem 10.2.2 (p. 477): the constant functor of `ℤ/2 ⋉ ℝ` at `0`. -/
def reflConst : EpFunctor reflectionEpGroupoid reflectionEpGroupoid where
  obj _ := 0
  mor _ := reflectionEpGroupoid.unit 0
  src_mor _ := reflectionEpGroupoid.src_unit 0
  tgt_mor _ := reflectionEpGroupoid.tgt_unit 0
  mor_comp _ _ _ := by
    change ((1 : ℤˣ), (0 : Fin 1 → ℝ)) = ((1 : ℤˣ) * 1, 0)
    rw [mul_one]
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_const (mem_smoothSet_rn1 0)
  isScSmoothMap_mor :=
    reflectionEpGroupoid.isScSmoothMap_unit.comp (MPolyfold.isScSmoothMap_const (mem_smoothSet_rn1 0))

/-- Row V10.18, Theorem 10.2.2 (p. 477): the constant map `ℝ → ℝ` is not a local
sc-diffeomorphism (its image `{0}` is not open). -/
theorem not_isLocalScDiffeo_reflConst :
    ¬ reflectionEpGroupoid.PObj.IsLocalScDiffeo reflectionEpGroupoid.PObj reflConst.obj :=
  fun h => by
    have ho := h.isOpenMap univ isOpen_univ
    have e : reflConst.obj '' univ = {0} := univ_nonempty.image_const 0
    rw [e] at ho
    exact not_isOpen_singleton (0 : Fin 1 → ℝ) ho

/-- Row V10.18, Theorem 10.2.2 (p. 477): the pair `(reflConst, reflConst)` is not admissible. -/
theorem not_admissible_reflConst : ¬ Admissible reflConst reflConst := fun h =>
  h.elim not_isLocalScDiffeo_reflConst not_isLocalScDiffeo_reflConst

/-! ### Push-forward and pull-back along generalized maps -/

/-- Row V11.16, push-forward and pull-back along generalized maps (p. 536): the generalized map
`[ℤ/2 ⋉ ℝ ←1 ℤ/2 ⋉ ℝ →reflConst ℤ/2 ⋉ ℝ]`. -/
def constDiagram : Diagram reflectionEP reflectionEP :=
  ⟨reflectionEP, EpFunctor.id _, EpFunctor.IsEquivalence.id _, reflConst⟩

/-- Row V11.16, push-forward and pull-back along generalized maps (p. 536): `[constDiagram]` is
not a generalized isomorphism (Theorem 10.3.10). -/
theorem not_isGeneralizedIso_constDiagram : ¬ IsGeneralizedIso (homMk constDiagram) := fun h =>
  not_isLocalScDiffeo_reflConst ((theorem_10_3_10 constDiagram).1.1 h).isLocalScDiffeo_obj

/-- Row V11.16, push-forward and pull-back along generalized maps (p. 536): the pull-back of
`Θ₀ = 1_{0}` along the generalized map `[constDiagram]`, which is not a generalized isomorphism,
is the constant function `1`. -/
theorem pullTheta_constDiagram :
    pullTheta (homMk constDiagram) reflectionTheta = fun _ => 1 := by
  have hΘ := isBranchedEpSubgroupoid_reflectionTheta.isFunctorial
  rw [pullTheta_homMk _ hΘ]
  change (EpFunctor.id reflectionEpGroupoid).pushforwardTheta (reflConst.pullbackTheta reflectionTheta) = _
  rw [EpFunctor.pushforwardTheta_id (reflConst.isFunctorial_pullbackTheta hΘ)]
  funext x
  rw [EpFunctor.pullbackTheta_apply, reflectionTheta_apply]
  exact if_pos rfl

/-! ### Theorem 11.3.5 -/

/-- Row V11.21, Theorem 11.3.5 (p. 539): pulling back the push-forward of the oriented branched
ep⁺-subgroupoid of Example 9.3.5 along the identity class returns it. -/
theorem example935Oriented_pull_push :
    (example935Oriented.push isGeneralizedIso_id_rn2EP).pull isGeneralizedIso_id_rn2EP =
      example935Oriented :=
  OrientedBranched.pull_push _ _ fun x hx =>
    absurd (show x ∈ (rnPolyfold 2).smoothSet by
      rw [TrivialBundle.rnPolyfold_smoothSet]; exact mem_univ x) hx

end Polyfold.Examples.Path

