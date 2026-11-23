import Polyfold.Chapter15.CylinderOrientationLocalConj
import Polyfold.Chapter12.RestrictionLocalIso
import Polyfold.Chapter8.NonVacuityBundle
import Polyfold.Chapter15.ProductEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276
(Remark 6.6.19), and §15.4, p. 703.

# The pull-back to `[0, 1] × V` of the restriction of a strong bundle to an open set `V`

For a strong bundle `P : Y → X` and an open `V ⊆ X`, the pull-back of `P|V` to `[0, 1] × V` is
the part over `[0, 1] × V` of the pull-back of `P` to `[0, 1] × X`.

* `StrongBundle.isStrongBundleMap_restrictOpen`: the inclusion `Y|V → Y` is a strong bundle map
  covering the inclusion `V → X`.
* `StrongBundle.ivRestrictIso`: the inclusion of the pull-back of `P|V` to `[0, 1] × V` into
  the pull-back of `P` to `[0, 1] × X`, as a local strong bundle isomorphism onto the part over
  `[0, 1] × V`.
* `StrongBundle.isIntervalProductAt₂_ivRestrictIso`: it is `id × (the inclusion Y|V → Y)`.
* `StrongBundle.cubeLift_eqOn_ivRestrictIso`: the section `(t, x) ↦ f(x)` over `[0, 1] × V` is
  carried to the one over `[0, 1] × X`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

open StrongRetr UnitCube

universe u v

section IvRestrict

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)
  {V : Set X} [Nonempty V] [ParacompactSpace V]
  [ParacompactSpace (pullbackSpace P (Subtype.val : V → X))] (hV : IsOpen V)
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))]
  [ParacompactSpace ((Fin 1 → unitInterval) × V)]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Subtype.val : V → X))
    (Prod.snd : (Fin 1 → unitInterval) × V → V))]

namespace StrongBundle

/-- **The inclusion `Y|V → Y` is a strong bundle map** covering the inclusion `V → X`. -/
theorem isStrongBundleMap_restrictOpen :
    (B.restrictOpen hV).IsStrongBundleMap B (Subtype.val : V → X)
      (fun q : pullbackSpace P (Subtype.val : V → X) => q.1.2) where
  covers q := q.2
  fiber_linear v :=
    (pullbackFiberCLE (P := P) (f := (Subtype.val : V → X)) v).toLinearMap.isLinear
  isScSmoothMap := B.isScSmoothMap_restrictIso_zero hV
  mapsTo_oneSet q hq := (B.mem_oneSet_restrictOpen_iff hV q).1 hq
  isScSmoothMap_one := B.isScSmoothMap_restrictIsoOne hV

/-- The inclusion `[0, 1] × V → [0, 1] × X` is sc-smooth. -/
theorem isScSmoothMap_ivIncl :
    ((cubePolyfold 1).prod (PX.restrictOpen hV)).IsScSmoothMap ((cubePolyfold 1).prod PX)
      (Prod.map id (Subtype.val : V → X)) := by
  have h := MPolyfold.IsScSmoothOn.prodMap
    (MPolyfold.isScSmoothMap_id (P := cubePolyfold 1))
    (MPolyfold.isScSmoothMap_subtypeVal (P := PX) hV)
  rwa [univ_prod_univ] at h

/-- **The inclusion of the pull-back of `P|V` to `[0, 1] × V` into the pull-back of `P` to
`[0, 1] × X`**: `((t, v), (v, y)) ↦ ((t, v), y)`. -/
def ivRestrictMap : pullbackSpace (pullbackProj P (Subtype.val : V → X))
      (Prod.snd : (Fin 1 → unitInterval) × V → V) →
    pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X) :=
  pullbackMap (pullbackProj P (Subtype.val : V → X)) Prod.snd P Prod.snd (h := Subtype.val)
    (Φ := fun q : pullbackSpace P (Subtype.val : V → X) => q.1.2)
    (g := Prod.map id Subtype.val) (fun q => q.2) (fun _ => rfl)

/-- The inclusion is a strong bundle map covering `[0, 1] × V → [0, 1] × X`. -/
theorem isStrongBundleMap_ivRestrictMap :
    (ivBundle (B.restrictOpen hV)).IsStrongBundleMap (ivBundle B)
      (Prod.map id (Subtype.val : V → X)) (ivRestrictMap (P := P) (V := V)) :=
  isStrongBundleMap_pullbackMap (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) (PX.restrictOpen hV))
    (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX) (B.isStrongBundleMap_restrictOpen hV)
    (isScSmoothMap_ivIncl hV) fun _ => rfl

/-- The inverse of the inclusion over `[0, 1] × V`: `((t, x), y) ↦ ((t, x), (x, y))`. -/
def ivRestrictInv (q : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)) :
    pullbackSpace (pullbackProj P (Subtype.val : V → X))
      (Prod.snd : (Fin 1 → unitInterval) × V → V) :=
  ⟨((q.1.1.1, pullbackProj P Subtype.val (B.restrictIsoInv V q.1.2)), B.restrictIsoInv V q.1.2),
    rfl⟩

/-- The inverse of the inclusion on level `[1]`. -/
def ivRestrictInvOne (w : (ivBundle B).One) : (ivBundle (B.restrictOpen hV)).One :=
  (ivBundle (B.restrictOpen hV)).oneMk
    ⟨((((ivBundle B).oneVal w).1.1.1, pullbackProj P Subtype.val ((B.restrictOpen hV).oneVal
      (B.restrictIsoInvOne hV (B.pullbackProj'One
        (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX) w)))),
      (B.restrictOpen hV).oneVal (B.restrictIsoInvOne hV (B.pullbackProj'One
        (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX) w))), rfl⟩
    (((B.restrictOpen hV).mem_oneSet_pullback_iff
      (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) (PX.restrictOpen hV)) _).2
      ((B.restrictOpen hV).oneVal_mem _))

theorem ivRestrictInv_ivRestrictMap (q : pullbackSpace (pullbackProj P (Subtype.val : V → X))
    (Prod.snd : (Fin 1 → unitInterval) × V → V)) :
    B.ivRestrictInv (ivRestrictMap q) = q := by
  have h : B.restrictIsoInv V q.1.2.1.2 = q.1.2 := B.restrictIsoInv_snd_self q.1.2
  apply Subtype.ext
  change ((q.1.1.1, pullbackProj P Subtype.val (B.restrictIsoInv V q.1.2.1.2)),
    B.restrictIsoInv V q.1.2.1.2) = q.1
  rw [h]
  exact Prod.ext (Prod.ext rfl q.2) rfl

theorem ivRestrictMap_ivRestrictInv
    {q : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)} (hq : q.1.1.2 ∈ V) :
    ivRestrictMap (B.ivRestrictInv (V := V) q) = q := by
  have hP : P q.1.2 ∈ V := by rw [q.2]; exact hq
  apply Subtype.ext
  change ((q.1.1.1, (pullbackProj P Subtype.val (B.restrictIsoInv V q.1.2)).1),
    (B.restrictIsoInv V q.1.2).1.2) = q.1
  rw [B.restrictIsoInv_of_mem hP]
  exact Prod.ext (Prod.ext rfl q.2) rfl

/-- The inverse of the inclusion is sc-smooth over `[0, 1] × V`, on level `[0]`. -/
theorem isScSmoothOn_ivRestrictInv :
    (ivBundle B).toMPolyfold0.IsScSmoothOn (ivBundle (B.restrictOpen hV)).toMPolyfold0
      (B.ivRestrictInv (V := V))
      (pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X) ⁻¹' (Prod.snd ⁻¹' V)) := by
  have hWo : IsOpen (pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X) ⁻¹'
      (Prod.snd ⁻¹' V)) :=
    (hV.preimage continuous_snd).preimage (ivBundle B).continuous
  have hb : (ivBundle B).toMPolyfold0.IsScSmoothOn (B.restrictOpen hV).toMPolyfold0
      (fun q : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X) =>
        B.restrictIsoInv V q.1.2)
      (pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X) ⁻¹' (Prod.snd ⁻¹' V)) :=
    MPolyfold.IsScSmoothOn.comp (B.isScSmoothOn_restrictIsoInv_zero hV)
      ((B.isScSmoothMap_pullbackProj' (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX)).mono hWo
        (subset_univ _)) fun q hq => by
        change P q.1.2 ∈ V
        rw [q.2]; exact hq
  have ha1 : (ivBundle B).toMPolyfold0.IsScSmoothOn (cubePolyfold 1)
      (fun q : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X) => q.1.1.1)
      (pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X) ⁻¹' (Prod.snd ⁻¹' V)) :=
    ((MPolyfold.isScSmoothMap_fst (cubePolyfold 1) PX).comp
      (B.isScSmoothMap_pullbackProj (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX))).mono hWo
      (subset_univ _)
  have ha2 := MPolyfold.IsScSmoothOn.comp (B.restrictOpen hV).isScSmoothMap_proj hb
    (mapsTo_univ _ _)
  exact (B.restrictOpen hV).isScSmoothOn_to_pullback_of_eqOn
    (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) (PX.restrictOpen hV)) (ha1.prodMk ha2) hb
    fun _ _ => rfl

theorem oneVal_ivRestrictInvOne (w : (ivBundle B).One) :
    (ivBundle (B.restrictOpen hV)).oneVal (B.ivRestrictInvOne hV w) =
      ⟨((((ivBundle B).oneVal w).1.1.1, pullbackProj P Subtype.val ((B.restrictOpen hV).oneVal
        (B.restrictIsoInvOne hV (B.pullbackProj'One
          (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX) w)))),
        (B.restrictOpen hV).oneVal (B.restrictIsoInvOne hV (B.pullbackProj'One
          (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX) w))), rfl⟩ :=
  rfl

/-- On level `[1]` the inverse of the inclusion has the values of the inverse on level `[0]`,
over `[0, 1] × V`. -/
theorem oneVal_ivRestrictInvOne_of_mem {w : (ivBundle B).One}
    (hw : ((ivBundle B).oneVal w).1.1.2 ∈ V) :
    (ivBundle (B.restrictOpen hV)).oneVal (B.ivRestrictInvOne hV w) =
      B.ivRestrictInv (V := V) ((ivBundle B).oneVal w) := by
  have hP : P ((ivBundle B).oneVal w).1.2 ∈ V := by
    rw [((ivBundle B).oneVal w).2]; exact hw
  have e1 : (B.restrictOpen hV).oneVal (B.restrictIsoInvOne hV (B.pullbackProj'One
      (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX) w)) =
      B.restrictIsoInv V ((ivBundle B).oneVal w).1.2 :=
    (B.oneVal_restrictIsoInvOne hV (w := B.pullbackProj'One
      (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX) w) hP).trans
      (B.restrictIsoInv_of_mem hP).symm
  rw [oneVal_ivRestrictInvOne]
  apply Subtype.ext
  change ((_, pullbackProj P Subtype.val _), _) = ((_, pullbackProj P Subtype.val _), _)
  rw [e1]

/-- The inverse of the inclusion is sc-smooth over `[0, 1] × V`, on level `[1]`. -/
theorem isScSmoothOn_ivRestrictInvOne :
    (ivBundle B).toMPolyfold1.IsScSmoothOn (ivBundle (B.restrictOpen hV)).toMPolyfold1
      (B.ivRestrictInvOne hV)
      ((pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X) ∘ (ivBundle B).oneVal) ⁻¹'
        (Prod.snd ⁻¹' V)) := by
  have hWo : IsOpen ((pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X) ∘
      (ivBundle B).oneVal) ⁻¹' (Prod.snd ⁻¹' V)) :=
    (hV.preimage continuous_snd).preimage
      ((ivBundle B).continuous.comp (ivBundle B).continuous_oneVal)
  have hr : (ivBundle B).toMPolyfold1.IsScSmoothOn (B.restrictOpen hV).toMPolyfold1
      (fun w => B.restrictIsoInvOne hV (B.pullbackProj'One
        (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX) w))
      ((pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X) ∘ (ivBundle B).oneVal) ⁻¹'
        (Prod.snd ⁻¹' V)) :=
    MPolyfold.IsScSmoothOn.comp (B.isScSmoothOn_restrictIsoInvOne hV)
      ((B.isScSmoothMap_one_pullbackProj'
        (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX)).mono hWo (subset_univ _))
      fun w hw => by
        change P ((ivBundle B).oneVal w).1.2 ∈ V
        rw [((ivBundle B).oneVal w).2]; exact hw
  have ha1 : (ivBundle B).toMPolyfold1.IsScSmoothOn (cubePolyfold 1)
      (fun w => ((ivBundle B).oneVal w).1.1.1)
      ((pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X) ∘ (ivBundle B).oneVal) ⁻¹'
        (Prod.snd ⁻¹' V)) :=
    ((MPolyfold.isScSmoothMap_fst (cubePolyfold 1) PX).comp
      (ivBundle B).isScSmoothMap_proj1).mono hWo (subset_univ _)
  have ha2 := MPolyfold.IsScSmoothOn.comp (B.restrictOpen hV).isScSmoothMap_proj1 hr
    (mapsTo_univ _ _)
  refine (B.restrictOpen hV).isScSmoothOn_to_pullback_one
    (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) (PX.restrictOpen hV)) ?_ ?_
  · exact (ha1.prodMk ha2).congr fun _ _ => rfl
  · exact hr.congr fun _ _ => (B.restrictOpen hV).oneVal_injective rfl

/-- **The inclusion of the pull-back of `P|V` to `[0, 1] × V` into the pull-back of `P` to
`[0, 1] × X`, as a local strong bundle isomorphism** onto the part over `[0, 1] × V`. -/
def ivRestrictIso :
    LocalIso (ivBundle (B.restrictOpen hV)) (ivBundle B) univ
      (Prod.snd ⁻¹' V : Set ((Fin 1 → unitInterval) × X)) where
  ϕ := Prod.map id Subtype.val
  g := Prod.map id (MPolyfold.openRetraction V)
  Φ := ivRestrictMap
  Ψ := B.ivRestrictInv
  Φ₁ := oneRestrict (ivBundle (B.restrictOpen hV)) (ivBundle B) ivRestrictMap
    (B.isStrongBundleMap_ivRestrictMap hV).mapsTo_oneSet
  Ψ₁ := B.ivRestrictInvOne hV
  base := by
    have h := MPolyfold.IsScDiffeoOn.prodMap
      (MPolyfold.isScDiffeoOn_id (P := cubePolyfold 1) isOpen_univ)
      (MPolyfold.isScDiffeoOn_subtypeVal (P := PX) hV)
    rwa [univ_prod_univ, univ_prod] at h
  zero := by
    rw [preimage_univ]
    exact ⟨(B.isStrongBundleMap_ivRestrictMap hV).isScSmoothMap, B.isScSmoothOn_ivRestrictInv hV,
      fun q _ => q.1.1.2.2, fun _ _ => mem_univ _, fun q _ => B.ivRestrictInv_ivRestrictMap q,
      fun q hq => B.ivRestrictMap_ivRestrictInv hq⟩
  one := by
    rw [preimage_univ]
    exact ⟨(B.isStrongBundleMap_ivRestrictMap hV).isScSmoothMap_one,
      B.isScSmoothOn_ivRestrictInvOne hV,
      fun w _ => ((ivBundle (B.restrictOpen hV)).oneVal w).1.1.2.2, fun _ _ => mem_univ _,
      fun w _ => (ivBundle (B.restrictOpen hV)).oneVal_injective
        ((B.oneVal_ivRestrictInvOne_of_mem hV
          (w := oneRestrict (ivBundle (B.restrictOpen hV)) (ivBundle B) ivRestrictMap
            (B.isStrongBundleMap_ivRestrictMap hV).mapsTo_oneSet w)
          ((ivBundle (B.restrictOpen hV)).oneVal w).1.1.2.2).trans
          (B.ivRestrictInv_ivRestrictMap _)),
      fun w hw => (ivBundle B).oneVal_injective
        ((congrArg ivRestrictMap (B.oneVal_ivRestrictInvOne_of_mem hV hw)).trans
          (B.ivRestrictMap_ivRestrictInv hw))⟩
  covers _ _ := rfl
  oneVal_Φ₁ _ _ := rfl
  fiber_linear x x' _ hx' := by
    subst hx'
    exact (B.isStrongBundleMap_ivRestrictMap hV).fiber_linear x

@[simp] theorem ivRestrictIso_ϕ (z : (Fin 1 → unitInterval) × V) :
    (B.ivRestrictIso hV).ϕ z = (z.1, z.2.1) := rfl

theorem ivRestrictIso_Φ_val (w : pullbackSpace (pullbackProj P (Subtype.val : V → X))
    (Prod.snd : (Fin 1 → unitInterval) × V → V)) :
    ((B.ivRestrictIso hV).Φ w).1.2 = w.1.2.1.2 := rfl

/-- **The inclusion over `[0, 1] × V` is `id ×` (the inclusion `Y|V → Y`)**, at every point. -/
theorem isIntervalProductAt₂_ivRestrictIso (z : (Fin 1 → unitInterval) × V) :
    LocalIso.IsIntervalProductAt₂ (B.ivRestrictIso hV) (B.restrictIso hV) z :=
  ⟨⟨univ, isOpen_univ, mem_univ z, subset_rfl, fun _ _ => mem_univ _, fun _ _ => rfl⟩,
    fun _ _ => rfl⟩

/-- **The section `(t, x) ↦ f(x)` over `[0, 1] × V` is the one over `[0, 1] × X` carried by the
inclusion.** -/
theorem cubeLift_eqOn_ivRestrictIso {f : X → Y} (hf : IsSection P f) :
    EqOn (cubeLift (n := 1) (restrictSection P V f hf)
        (fun v => (rfl : pullbackProj P Subtype.val (restrictSection P V f hf v) = v)))
      ((B.ivRestrictIso hV).Ψ ∘ cubeLift (n := 1) f hf ∘ (B.ivRestrictIso hV).ϕ) univ :=
  fun z _ => ((B.ivRestrictIso hV).zero.left_inv
    (cubeLift (n := 1) (restrictSection P V f hf) (fun _ => rfl) z) (mem_univ _)).symm

end StrongBundle

end IvRestrict

end Polyfold
