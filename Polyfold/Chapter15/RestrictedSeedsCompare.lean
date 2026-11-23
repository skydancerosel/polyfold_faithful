import Polyfold.Chapter15.CylinderOrientationLocalIso
import Polyfold.Chapter15.RestrictedBundleGeneralPosition
import Polyfold.Chapter15.CylinderCollarNorm
import Polyfold.Chapter15.RelativeStepFamilies

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Corollary 15.3.10 (2), (3)
(pp. 699–700) on the restriction of a strong bundle over an ep-groupoid to a saturated open
subset of the object space (Proposition 7.1.22, p. 250).

# The cylinder of the restriction `W|V` and the cylinder of `W`

For `A : SEP` and an open ep-subgroupoid `V` of the base, the strong bundle
`[0, 1] × (W|V) → [0, 1] × (X|V)` is the part over `[0, 1] × V` of `[0, 1] × W → [0, 1] × X`.

* `StrongBundle.cubePullbackIso`: for a local strong bundle isomorphism `R` from a pull-back
  `f*Y` (over all of its base) onto `Y|V` whose total map is the projection `f*Y → Y`, the
  map `id × R` from the pull-back of `f*Y` to `[0, 1] × Z` onto the part over `[0, 1] × V` of
  the pull-back of `Y` to `[0, 1] × X`.
* `cubeRestrBase`, `cubeRestrFib`: the maps `(t, a) ↦ (t, a)` and `((t, a), h) ↦ ((t, a), h)`.
* `cubeRestrIso`: the two maps as a local strong bundle isomorphism.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v w

section CubePullback

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {f : Z → X} [ParacompactSpace (pullbackSpace P f)] (hf : PZ.IsScSmoothMap PX f)
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))]
  [ParacompactSpace ((Fin 1 → unitInterval) × Z)]
  [ParacompactSpace (pullbackSpace (pullbackProj P f)
    (Prod.snd : (Fin 1 → unitInterval) × Z → Z))]
  {V : Set X} (R : StrongBundle.LocalIso (B.pullback hf) B univ V)

namespace StrongBundle

omit [ParacompactSpace (pullbackSpace P f)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P f)
    (Prod.snd : (Fin 1 → unitInterval) × Z → Z))] in
include hf in
/-- The map `id × f : [0, 1] × Z → [0, 1] × X` is sc-smooth. -/
theorem isScSmoothMap_cubeMap :
    ((cubePolyfold 1).prod PZ).IsScSmoothMap ((cubePolyfold 1).prod PX) (Prod.map id f) := by
  have h := MPolyfold.IsScSmoothOn.prodMap (MPolyfold.isScSmoothMap_id (P := cubePolyfold 1)) hf
  rwa [univ_prod_univ] at h

variable (P f) in
/-- **The map from the pull-back of `f*Y` to `[0, 1] × Z` into the pull-back of `Y` to
`[0, 1] × X`**: `((t, z), (z, y)) ↦ ((t, f z), y)`. -/
def cubePullbackMap : pullbackSpace (pullbackProj P f)
      (Prod.snd : (Fin 1 → unitInterval) × Z → Z) →
    pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X) :=
  pullbackMap (pullbackProj P f) Prod.snd P Prod.snd (h := f)
    (Φ := pullbackProj' P f) (g := Prod.map id f) (fun q => q.2) (fun _ => rfl)

/-- The map is a strong bundle map covering `id × f`. -/
theorem isStrongBundleMap_cubePullbackMap :
    (ivBundle (B.pullback hf)).IsStrongBundleMap (ivBundle B) (Prod.map id f)
      (cubePullbackMap P f) :=
  isStrongBundleMap_pullbackMap (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PZ)
    (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX) (B.isStrongBundleMap_pullbackProj' hf)
    (isScSmoothMap_cubeMap hf) fun _ => rfl

/-- The inverse over `[0, 1] × V`: `((t, x), y) ↦ ((t, z), (z, y))` for `(z, y) = R⁻¹(y)`. -/
def cubePullbackInv (q : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)) :
    pullbackSpace (pullbackProj P f) (Prod.snd : (Fin 1 → unitInterval) × Z → Z) :=
  ⟨((q.1.1.1, pullbackProj P f (R.Ψ q.1.2)), R.Ψ q.1.2), rfl⟩

/-- The inverse on level `[1]`. -/
def cubePullbackInvOne (w : (ivBundle B).One) : (ivBundle (B.pullback hf)).One :=
  (ivBundle (B.pullback hf)).oneMk
    ⟨((((ivBundle B).oneVal w).1.1.1, pullbackProj P f ((B.pullback hf).oneVal
      (R.Ψ₁ (B.pullbackProj'One (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX) w)))),
      (B.pullback hf).oneVal
        (R.Ψ₁ (B.pullbackProj'One (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX) w))), rfl⟩
    (((B.pullback hf).mem_oneSet_pullback_iff
      (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PZ) _).2 ((B.pullback hf).oneVal_mem _))

variable {B hf}

theorem cubePullbackInv_cubePullbackMap (hΦ : ∀ y, R.Φ y = pullbackProj' P f y)
    (q : pullbackSpace (pullbackProj P f) (Prod.snd : (Fin 1 → unitInterval) × Z → Z)) :
    cubePullbackInv B hf R (cubePullbackMap P f q) = q := by
  have h : R.Ψ (pullbackProj' P f q.1.2) = q.1.2 := by
    rw [← hΦ]; exact R.zero.left_inv q.1.2 (mem_univ _)
  apply Subtype.ext
  change ((q.1.1.1, pullbackProj P f (R.Ψ (pullbackProj' P f q.1.2))),
    R.Ψ (pullbackProj' P f q.1.2)) = q.1
  rw [h]
  exact Prod.ext (Prod.ext rfl q.2) rfl

theorem cubePullbackMap_cubePullbackInv (hΦ : ∀ y, R.Φ y = pullbackProj' P f y)
    {q : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)} (hq : q.1.1.2 ∈ V) :
    cubePullbackMap P f (cubePullbackInv B hf R q) = q := by
  have hP : P q.1.2 ∈ V := by rw [q.2]; exact hq
  have h : pullbackProj' P f (R.Ψ q.1.2) = q.1.2 := by
    rw [← hΦ]; exact R.zero.right_inv q.1.2 hP
  apply Subtype.ext
  change ((q.1.1.1, f (pullbackProj P f (R.Ψ q.1.2))), pullbackProj' P f (R.Ψ q.1.2)) = q.1
  have h2 : f (pullbackProj P f (R.Ψ q.1.2)) = q.1.1.2 := by
    have h3 : P (pullbackProj' P f (R.Ψ q.1.2)) = f (pullbackProj P f (R.Ψ q.1.2)) :=
      (R.Ψ q.1.2).2
    rw [← h3, h]; exact q.2
  rw [h, h2]

/-- The inverse is sc-smooth over `[0, 1] × V`, on level `[0]`. -/
theorem isScSmoothOn_cubePullbackInv :
    (ivBundle B).toMPolyfold0.IsScSmoothOn (ivBundle (B.pullback hf)).toMPolyfold0
      (cubePullbackInv B hf R)
      (pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X) ⁻¹' (Prod.snd ⁻¹' V)) := by
  have hV : IsOpen V := R.isOpen_U'
  have hWo : IsOpen (pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X) ⁻¹'
      (Prod.snd ⁻¹' V)) :=
    (hV.preimage continuous_snd).preimage (ivBundle B).continuous
  have hb : (ivBundle B).toMPolyfold0.IsScSmoothOn (B.pullback hf).toMPolyfold0
      (fun q : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X) => R.Ψ q.1.2)
      (pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X) ⁻¹' (Prod.snd ⁻¹' V)) :=
    MPolyfold.IsScSmoothOn.comp R.zero.isScSmoothOn_inv
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
  have ha2 := MPolyfold.IsScSmoothOn.comp (B.pullback hf).isScSmoothMap_proj hb
    (mapsTo_univ _ _)
  exact (B.pullback hf).isScSmoothOn_to_pullback_of_eqOn
    (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PZ) (ha1.prodMk ha2) hb
    fun _ _ => rfl

/-- On level `[1]` the inverse has the values of the inverse on level `[0]`, over
`[0, 1] × V`. -/
theorem oneVal_cubePullbackInvOne_of_mem {w : (ivBundle B).One}
    (hw : ((ivBundle B).oneVal w).1.1.2 ∈ V) :
    (ivBundle (B.pullback hf)).oneVal (cubePullbackInvOne B hf R w) =
      cubePullbackInv B hf R ((ivBundle B).oneVal w) := by
  have hP : P ((ivBundle B).oneVal w).1.2 ∈ V := by
    rw [((ivBundle B).oneVal w).2]; exact hw
  have e1 : (B.pullback hf).oneVal (R.Ψ₁ (B.pullbackProj'One
      (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX) w)) =
      R.Ψ ((ivBundle B).oneVal w).1.2 :=
    R.oneVal_Ψ₁ (B.pullbackProj'One (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX) w) hP
  apply Subtype.ext
  change ((_, pullbackProj P f _), _) = ((_, pullbackProj P f _), _)
  rw [e1]

/-- The inverse is sc-smooth over `[0, 1] × V`, on level `[1]`. -/
theorem isScSmoothOn_cubePullbackInvOne :
    (ivBundle B).toMPolyfold1.IsScSmoothOn (ivBundle (B.pullback hf)).toMPolyfold1
      (cubePullbackInvOne B hf R)
      ((pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X) ∘ (ivBundle B).oneVal) ⁻¹'
        (Prod.snd ⁻¹' V)) := by
  have hV : IsOpen V := R.isOpen_U'
  have hWo : IsOpen ((pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X) ∘
      (ivBundle B).oneVal) ⁻¹' (Prod.snd ⁻¹' V)) :=
    (hV.preimage continuous_snd).preimage
      ((ivBundle B).continuous.comp (ivBundle B).continuous_oneVal)
  have hr : (ivBundle B).toMPolyfold1.IsScSmoothOn (B.pullback hf).toMPolyfold1
      (fun w => R.Ψ₁ (B.pullbackProj'One
        (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX) w))
      ((pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X) ∘ (ivBundle B).oneVal) ⁻¹'
        (Prod.snd ⁻¹' V)) :=
    MPolyfold.IsScSmoothOn.comp R.one.isScSmoothOn_inv
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
  have ha2 := MPolyfold.IsScSmoothOn.comp (B.pullback hf).isScSmoothMap_proj1 hr
    (mapsTo_univ _ _)
  refine (B.pullback hf).isScSmoothOn_to_pullback_one
    (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PZ) ?_ ?_
  · exact (ha1.prodMk ha2).congr fun _ _ => rfl
  · exact hr.congr fun _ _ => (B.pullback hf).oneVal_injective rfl

variable (B hf)

/-- **The pull-back of `f*Y` to `[0, 1] × Z` is the part over `[0, 1] × V` of the pull-back of
`Y` to `[0, 1] × X`**, when `f*Y → Y` is a local strong bundle isomorphism `R` onto `Y|V`:
the map `((t, z), (z, y)) ↦ ((t, f z), y)` as a local strong bundle isomorphism. -/
def cubePullbackIso (hϕ : ∀ z, R.ϕ z = f z) (hΦ : ∀ y, R.Φ y = pullbackProj' P f y) :
    LocalIso (ivBundle (B.pullback hf)) (ivBundle B) univ
      (Prod.snd ⁻¹' V : Set ((Fin 1 → unitInterval) × X)) where
  ϕ := Prod.map id f
  g := Prod.map id R.g
  Φ := cubePullbackMap P f
  Ψ := cubePullbackInv B hf R
  Φ₁ := oneRestrict (ivBundle (B.pullback hf)) (ivBundle B) (cubePullbackMap P f)
    (B.isStrongBundleMap_cubePullbackMap hf).mapsTo_oneSet
  Ψ₁ := cubePullbackInvOne B hf R
  base := by
    have h := MPolyfold.IsScDiffeoOn.prodMap
      (MPolyfold.isScDiffeoOn_id (P := cubePolyfold 1) isOpen_univ) R.base
    rw [univ_prod_univ, univ_prod] at h
    have e : (Prod.map id R.ϕ : (Fin 1 → unitInterval) × Z → _) = Prod.map id f := by
      funext z; exact Prod.ext rfl (hϕ z.2)
    rwa [e] at h
  zero := by
    rw [preimage_univ]
    have hmem : ∀ z, f z ∈ V := fun z => by rw [← hϕ]; exact R.base.mapsTo (mem_univ z)
    exact ⟨(B.isStrongBundleMap_cubePullbackMap hf).isScSmoothMap,
      isScSmoothOn_cubePullbackInv R,
      fun q _ => hmem q.1.1.2, fun _ _ => mem_univ _,
      fun q _ => cubePullbackInv_cubePullbackMap R hΦ q,
      fun q hq => cubePullbackMap_cubePullbackInv R hΦ hq⟩
  one := by
    rw [preimage_univ]
    have hmem : ∀ z, f z ∈ V := fun z => by rw [← hϕ]; exact R.base.mapsTo (mem_univ z)
    exact ⟨(B.isStrongBundleMap_cubePullbackMap hf).isScSmoothMap_one,
      isScSmoothOn_cubePullbackInvOne R,
      fun w _ => hmem ((ivBundle (B.pullback hf)).oneVal w).1.1.2, fun _ _ => mem_univ _,
      fun w _ => (ivBundle (B.pullback hf)).oneVal_injective
        ((oneVal_cubePullbackInvOne_of_mem R
          (w := oneRestrict (ivBundle (B.pullback hf)) (ivBundle B) (cubePullbackMap P f)
            (B.isStrongBundleMap_cubePullbackMap hf).mapsTo_oneSet w)
          (hmem ((ivBundle (B.pullback hf)).oneVal w).1.1.2)).trans
          (cubePullbackInv_cubePullbackMap R hΦ _)),
      fun w hw => (ivBundle B).oneVal_injective
        ((congrArg (cubePullbackMap P f) (oneVal_cubePullbackInvOne_of_mem R hw)).trans
          (cubePullbackMap_cubePullbackInv R hΦ hw))⟩
  covers _ _ := rfl
  oneVal_Φ₁ _ _ := rfl
  fiber_linear x x' _ hx' := by
    subst hx'
    exact (B.isStrongBundleMap_cubePullbackMap hf).fiber_linear x

end StrongBundle

end CubePullback

namespace SBLocalization

open StrongBundle MPolyfold SEP EpGroupoid

variable {A : SEP.{u}} {V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V)

/-! ### The two maps -/

/-- **`ϕ : [0, 1] × (X|V) → [0, 1] × X`**, `(t, a) ↦ (t, a)`. -/
def cubeRestrBase (z : ((A.restr hV).cubeSEP 1).Obj) : (A.cubeSEP 1).Obj :=
  ((show (Fin 1 → unitInterval) × (A.restr hV).Obj from z).1,
    restrBase hV (show (Fin 1 → unitInterval) × (A.restr hV).Obj from z).2)

/-- **`Φ : [0, 1] × (W|V) → [0, 1] × W`**, `((t, a), (a, h)) ↦ ((t, a), h)`. -/
def cubeRestrFib (w : ((A.restr hV).cubeSEP 1).W) : (A.cubeSEP 1).W :=
  StrongBundle.cubePullbackMap A.P (A.baseEP.subFunctor hV).obj w

theorem cubeRestrBase_apply (z : ((A.restr hV).cubeSEP 1).Obj) :
    cubeRestrBase hV z = ((show (Fin 1 → unitInterval) × (A.restr hV).Obj from z).1,
      restrBase hV (show (Fin 1 → unitInterval) × (A.restr hV).Obj from z).2) := rfl

/-- `Φ` covers `ϕ`. -/
theorem P_cubeRestrFib (w : ((A.restr hV).cubeSEP 1).W) :
    (A.cubeSEP 1).P (cubeRestrFib hV w) = cubeRestrBase hV (((A.restr hV).cubeSEP 1).P w) := rfl

/-- The components of `Φ(w)`. -/
theorem cubeVal_cubeRestrFib (w : ((A.restr hV).cubeSEP 1).W) :
    cubeVal (cubeRestrFib hV w) =
      (cubeRestrBase hV (((A.restr hV).cubeSEP 1).P w), restrFib hV (cubeVal w).2) := rfl

/-- A point of `[0, 1] × (W|V)` is determined by its base point and its image under `Φ`. -/
theorem cubeRestrFib_injective : Injective (cubeRestrFib hV) := by
  intro w w' h
  have h1 : cubeVal (cubeRestrFib hV w) = cubeVal (cubeRestrFib hV w') := congrArg _ h
  rw [cubeVal_cubeRestrFib, cubeVal_cubeRestrFib] at h1
  have hb : cubeRestrBase hV (((A.restr hV).cubeSEP 1).P w) =
      cubeRestrBase hV (((A.restr hV).cubeSEP 1).P w') := congrArg Prod.fst h1
  have hb1 := congrArg Prod.fst hb
  have hb2 := congrArg Prod.snd hb
  have hP : ((A.restr hV).cubeSEP 1).P w = ((A.restr hV).cubeSEP 1).P w' :=
    Prod.ext hb1 (restrBase_injective hV hb2)
  have h2 := congrArg Prod.snd h1
  have hP2 : (A.restr hV).P (cubeVal w).2 = (A.restr hV).P (cubeVal w').2 := by
    have e : ∀ v : ((A.restr hV).cubeSEP 1).W,
        (A.restr hV).P (cubeVal v).2 = (((A.restr hV).cubeSEP 1).P v).2 := fun v =>
      (show pullbackSpace (A.restr hV).P
        (Prod.snd : (Fin 1 → unitInterval) × (A.restr hV).Obj → (A.restr hV).Obj) from v).2
    rw [e, e, hP]
  exact Subtype.ext (Prod.ext hP (restr_ext hV hP2 h2))

variable (hVo : IsOpen V)

/-! ### The local strong bundle isomorphism -/

/-- **The cylinder of the restriction is the part over `[0, 1] × V` of the cylinder**
(Corollary 15.3.10 (2), p. 699, for `W|V`): `(ϕ, Φ)` as a local strong bundle isomorphism from
`[0, 1] × (W|V)` (over all of `[0, 1] × (X|V)`) onto `[0, 1] × W` over `[0, 1] × V`.  The point
`z` only provides the values of the inverse off `[0, 1] × V`. -/
def cubeRestrIso (z : ((A.restr hV).cubeSEP 1).Obj) :
    StrongBundle.LocalIso ((A.restr hV).cubeSEP 1).B (A.cubeSEP 1).B univ
      (Prod.snd ⁻¹' V : Set ((Fin 1 → unitInterval) × A.Obj)) :=
  haveI := A.B.paracompactSpace_pullback (A.baseEP.sub hV).X.PObj (A.baseEP.subFunctor hV).obj
  haveI := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  haveI := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
    (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)
  haveI := MPolyfold.paracompactSpace_prod (cubePolyfold 1) (A.baseEP.sub hV).X.PObj
  haveI := (A.B.pullback (A.baseEP.subFunctor hV).isScSmoothMap_obj).paracompactSpace_pullback
    ((cubePolyfold 1).prod (A.baseEP.sub hV).X.PObj)
    (Prod.snd : (Fin 1 → unitInterval) × (A.baseEP.sub hV).Obj → (A.baseEP.sub hV).Obj)
  StrongBundle.cubePullbackIso A.B (A.baseEP.subFunctor hV).isScSmoothMap_obj
    (restrIso hV hVo (show (Fin 1 → unitInterval) × (A.restr hV).Obj from z).2)
    (fun _ => rfl) (fun _ => rfl)

@[simp] theorem cubeRestrIso_ϕ (z : ((A.restr hV).cubeSEP 1).Obj) :
    (cubeRestrIso hV hVo z).ϕ = cubeRestrBase hV := rfl

@[simp] theorem cubeRestrIso_Φ (z : ((A.restr hV).cubeSEP 1).Obj) :
    (cubeRestrIso hV hVo z).Φ = cubeRestrFib hV := rfl

/-- The components of `Φ(w)`, for the local strong bundle isomorphism. -/
theorem cubeVal_cubeRestrIso_Φ (z : ((A.restr hV).cubeSEP 1).Obj)
    (w : ((A.restr hV).cubeSEP 1).W) :
    cubeVal ((cubeRestrIso hV hVo z).Φ w) =
      ((cubeRestrIso hV hVo z).ϕ (((A.restr hV).cubeSEP 1).P w), restrFib hV (cubeVal w).2) :=
  rfl

/-! ### The sections `f̃` -/

/-- **`Φ ∘ (f|V)~ = f̃ ∘ ϕ`.** -/
theorem cubeRestrFib_cubeLiftEp {f : A.Obj → A.W} (hf : IsSection A.P f)
    (z : ((A.restr hV).cubeSEP 1).Obj) :
    cubeRestrFib hV (cubeLiftEp (n := 1) (restrSec hV f hf) (isSection_restrSec hV hf) z) =
      cubeLiftEp (n := 1) f hf (cubeRestrBase hV z) := rfl

/-- `Φ ∘ (f|V)~ = f̃ ∘ ϕ`, for the local strong bundle isomorphism. -/
theorem cubeRestrIso_Φ_cubeLiftEp {f : A.Obj → A.W} (hf : IsSection A.P f)
    (z₀ z : ((A.restr hV).cubeSEP 1).Obj) :
    (cubeRestrIso hV hVo z₀).Φ
        (cubeLiftEp (n := 1) (restrSec hV f hf) (isSection_restrSec hV hf) z) =
      cubeLiftEp (n := 1) f hf ((cubeRestrIso hV hVo z₀).ϕ z) := rfl

/-- **`(f|V)~ = Ψ ∘ f̃ ∘ ϕ`** for the inclusion `(ϕ, Φ)` with inverse `Ψ`. -/
theorem eqOn_cubeLiftEp_restrSec {f : A.Obj → A.W} (hf : IsSection A.P f)
    (z₀ : ((A.restr hV).cubeSEP 1).Obj) :
    EqOn (cubeLiftEp (n := 1) (restrSec hV f hf) (isSection_restrSec hV hf))
      ((cubeRestrIso hV hVo z₀).Ψ ∘ cubeLiftEp (n := 1) f hf ∘ (cubeRestrIso hV hVo z₀).ϕ)
      univ :=
  fun z _ => ((cubeRestrIso hV hVo z₀).zero.left_inv
    (cubeLiftEp (n := 1) (restrSec hV f hf) (isSection_restrSec hV hf) z) (mem_univ _)).symm

/-! ### The base map -/

/-- The time coordinate is kept by `ϕ`. -/
theorem cubeT_cubeRestrBase (z : ((A.restr hV).cubeSEP 1).Obj) :
    cubeT (cubeRestrBase hV z) = cubeT z := rfl

theorem continuous_cubeRestrBase : Continuous (cubeRestrBase hV) :=
  continuous_fst.prodMk ((continuous_restrBase hV).comp continuous_snd)

theorem cubeRestrBase_injective : Injective (cubeRestrBase hV) := by
  intro z z' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext h1 (restrBase_injective hV h2)

/-- `ϕ` maps into `[0, 1] × V`. -/
theorem cubeRestrBase_mem (z : ((A.restr hV).cubeSEP 1).Obj) :
    cubeRestrBase hV z ∈ (Prod.snd ⁻¹' V : Set ((Fin 1 → unitInterval) × A.Obj)) :=
  restrBase_mem hV _

/-- **The image of `ϕ` is `[0, 1] × V`.** -/
theorem range_cubeRestrBase :
    range (cubeRestrBase hV) = (Prod.snd ⁻¹' V : Set ((Fin 1 → unitInterval) × A.Obj)) := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact cubeRestrBase_mem hV z
  · intro hp
    exact ⟨(p.1, (⟨p.2, hp⟩ : V)), rfl⟩

include hVo in
/-- **`ϕ` is a local sc-diffeomorphism.** -/
theorem isLocalScDiffeo_cubeRestrBase :
    ((A.restr hV).cubeSEP 1).X.PObj.IsLocalScDiffeo (A.cubeSEP 1).X.PObj (cubeRestrBase hV) :=
  fun z => ⟨univ, _, (cubeRestrIso hV hVo z).g, mem_univ z, (cubeRestrIso hV hVo z).base⟩

/-- `ϕ` is sc-smooth. -/
theorem isScSmoothMap_cubeRestrBase :
    ((A.restr hV).cubeSEP 1).X.PObj.IsScSmoothMap (A.cubeSEP 1).X.PObj (cubeRestrBase hV) :=
  haveI := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  haveI := MPolyfold.paracompactSpace_prod (cubePolyfold 1) (A.baseEP.sub hV).X.PObj
  StrongBundle.isScSmoothMap_cubeMap (A.baseEP.subFunctor hV).isScSmoothMap_obj

include hVo in
/-- **`ϕ` is an open map.** -/
theorem isOpenMap_cubeRestrBase : IsOpenMap (cubeRestrBase hV) := by
  intro S hS
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  have hd := (cubeRestrIso hV hVo z).base
  have hVo' : IsOpen (Prod.snd ⁻¹' V : Set ((Fin 1 → unitInterval) × A.Obj)) :=
    hVo.preimage continuous_snd
  have hpre : IsOpen ((Prod.snd ⁻¹' V : Set ((Fin 1 → unitInterval) × A.Obj)) ∩
      (cubeRestrIso hV hVo z).g ⁻¹' S) :=
    hd.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hVo' hS
  refine Filter.mem_of_superset (hpre.mem_nhds ⟨cubeRestrBase_mem hV z, ?_⟩) ?_
  · change (cubeRestrIso hV hVo z).g (cubeRestrBase hV z) ∈ S
    rw [show (cubeRestrIso hV hVo z).g (cubeRestrBase hV z) = z from hd.left_inv z (mem_univ z)]
    exact hz
  · rintro p ⟨hpV, hpS⟩
    exact ⟨_, hpS, hd.right_inv p hpV⟩

include hVo in
/-- **`∂([0, 1] × (X|V)) = ϕ⁻¹(∂([0, 1] × X))`.** -/
theorem mem_boundary_cubeRestr_iff (z : ((A.restr hV).cubeSEP 1).Obj) :
    z ∈ ((A.restr hV).cubeSEP 1).X.PObj.boundary ↔
      cubeRestrBase hV z ∈ (A.cubeSEP 1).X.PObj.boundary :=
  ((isLocalScDiffeo_cubeRestrBase hV hVo).mem_boundary_iff z).symm

include hVo in
/-- `ϕ` keeps the degeneracy index. -/
theorem degIndex_cubeRestrBase (z : ((A.restr hV).cubeSEP 1).Obj) :
    (A.cubeSEP 1).X.PObj.degIndex (cubeRestrBase hV z) =
      ((A.restr hV).cubeSEP 1).X.PObj.degIndex z :=
  (isLocalScDiffeo_cubeRestrBase hV hVo).degIndex_eq z

include hVo in
/-- **`ϕ` keeps the levels.** -/
theorem mem_levelSet_cubeRestr_iff (z : ((A.restr hV).cubeSEP 1).Obj) (m : ℕ) :
    z ∈ ((A.restr hV).cubeSEP 1).X.PObj.levelSet m ↔
      cubeRestrBase hV z ∈ (A.cubeSEP 1).X.PObj.levelSet m :=
  ((cubeRestrIso hV hVo z).base.mem_levelSet_iff (mem_univ z) m).symm

/-- **The interpolated set of the restriction is the preimage of the interpolated set.** -/
theorem mem_interpSet_cubeRestr_iff (U₀ U₁ : Set A.Obj) (z : ((A.restr hV).cubeSEP 1).Obj) :
    z ∈ interpSet (A.restr hV) (restrBase hV ⁻¹' U₀) (restrBase hV ⁻¹' U₁) ↔
      cubeRestrBase hV z ∈ interpSet A U₀ U₁ := Iff.rfl

/-! ### Orbits -/

/-- Two objects of `X|V` are isomorphic iff they are isomorphic in `X`. -/
theorem restr_π_eq_π_iff (a a' : (A.restr hV).Obj) :
    (A.restr hV).X.π a = (A.restr hV).X.π a' ↔
      A.X.π (restrBase hV a) = A.X.π (restrBase hV a') :=
  ⟨fun h => congrArg (A.baseEP.subFunctor hV).orbitMap h,
    fun h => injective_orbitMap_restr hV h⟩

/-- **Two points of `[0, 1] × (X|V)` are isomorphic iff their images in `[0, 1] × X` are.** -/
theorem cubeRestr_π_eq_π_iff (z z' : ((A.restr hV).cubeSEP 1).Obj) :
    ((A.restr hV).cubeSEP 1).X.π z = ((A.restr hV).cubeSEP 1).X.π z' ↔
      (A.cubeSEP 1).X.π (cubeRestrBase hV z) = (A.cubeSEP 1).X.π (cubeRestrBase hV z') := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) (A.restr hV).X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) (A.restr hV).X.PMor
  have h1 := (A.restr hV).X.cubeProd_π_eq_π_iff 1 z z'
  have h2 := A.X.cubeProd_π_eq_π_iff 1 (cubeRestrBase hV z) (cubeRestrBase hV z')
  exact h1.trans ((and_congr_right fun _ => restr_π_eq_π_iff hV _ _).trans h2.symm)

/-- **The preimage under `ϕ` of a saturated set is saturated.** -/
theorem isSaturated_preimage_cubeRestrBase {S : Set (A.cubeSEP 1).Obj}
    (hS : (A.cubeSEP 1).X.IsSaturated S) :
    ((A.restr hV).cubeSEP 1).X.IsSaturated (cubeRestrBase hV ⁻¹' S) := by
  refine subset_antisymm ?_ (subset_preimage_image _ _)
  rintro z ⟨z', hz', hzz'⟩
  change cubeRestrBase hV z ∈ S
  rw [← hS]
  exact ⟨cubeRestrBase hV z', hz', (cubeRestr_π_eq_π_iff hV z' z).1 hzz'⟩

/-! ### Sections and functions -/

/-- **A global sc⁺-section of `[0, 1] × W` restricts to a global sc⁺-section of
`[0, 1] × (W|V)`**: `z ↦ Ψ(S(ϕ z))`. -/
theorem isScPlusSection_isoSec_cubeRestrIso (z₀ : ((A.restr hV).cubeSEP 1).Obj)
    {S : (A.cubeSEP 1).Obj → (A.cubeSEP 1).W} (hS : (A.cubeSEP 1).B.IsScPlusSection S) :
    ((A.restr hV).cubeSEP 1).B.IsScPlusSection (isoSec (cubeRestrIso hV hVo z₀) S) := by
  set L := cubeRestrIso hV hVo z₀
  have hVo' : IsOpen (Prod.snd ⁻¹' V : Set ((Fin 1 → unitInterval) × A.Obj)) :=
    hVo.preimage continuous_snd
  have hon := isScPlusSectionOn_isoSec L hVo' subset_rfl
    (IsScPlusSectionOn.of_isScPlusSection hS hVo')
  obtain ⟨hP, G, hG, hGs⟩ := hon
  have huniv : ∀ y : ((A.restr hV).cubeSEP 1).Obj,
      y ∈ isoSet L (Prod.snd ⁻¹' V : Set ((Fin 1 → unitInterval) × A.Obj)) :=
    fun y => ⟨mem_univ _, cubeRestrBase_mem hV y⟩
  exact StrongBundle.isScPlusSection_of_locally (fun p => hP p (huniv p)) fun y₀ =>
    ⟨_, isOpen_isoSet L hVo', huniv y₀, G, hGs, fun y hy => hG y hy⟩

/-- `Φ(Ψ(S(ϕ z))) = S(ϕ z)` for a section `S` of `[0, 1] × W`. -/
theorem cubeRestrFib_isoSec (z₀ : ((A.restr hV).cubeSEP 1).Obj)
    {S : (A.cubeSEP 1).Obj → (A.cubeSEP 1).W} (hS : IsSection (A.cubeSEP 1).P S)
    (z : ((A.restr hV).cubeSEP 1).Obj) :
    cubeRestrFib hV (isoSec (cubeRestrIso hV hVo z₀) S z) = S (cubeRestrBase hV z) :=
  (cubeRestrIso hV hVo z₀).zero.right_inv (S (cubeRestrBase hV z)) (by
    change (A.cubeSEP 1).P (S (cubeRestrBase hV z)) ∈
      (Prod.snd ⁻¹' V : Set ((Fin 1 → unitInterval) × A.Obj))
    rw [hS]; exact cubeRestrBase_mem hV z)

/-- **A function on `[0, 1] × X` that is sc-smooth on `[0, 1] × V` restricts to an sc-smooth
function on `[0, 1] × (X|V)`.** -/
theorem isScSmoothMap_comp_cubeRestrBase {β : (A.cubeSEP 1).Obj → ℝ}
    (hβ : (A.cubeSEP 1).X.PObj.IsScSmoothOn realPolyfold β
      ((univ : Set (Fin 1 → unitInterval)) ×ˢ V)) :
    ((A.restr hV).cubeSEP 1).X.PObj.IsScSmoothMap realPolyfold (β ∘ cubeRestrBase hV) :=
  MPolyfold.IsScSmoothOn.comp hβ (isScSmoothMap_cubeRestrBase hV)
    fun _ _ => ⟨mem_univ _, restrBase_mem hV _⟩

end SBLocalization

end Polyfold
