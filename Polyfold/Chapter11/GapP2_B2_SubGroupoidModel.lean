import Polyfold.Chapter11.GapP2_B2_TranslationAverage
import Polyfold.Chapter7.SubGroupoid
import Polyfold.Chapter9.SolutionFaceForms2021
import Polyfold.Chapter10.Equivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §8.2, p. 374:
the saturated neighbourhoods in the proof of **Proposition 8.2.3** (2017: Proposition 8.1)
(gap G.87); see also Proposition 7.1.22 and Theorem 7.1.13.  Numbers and pages are the 2021
text's.

# Restrictions to saturated open sets and the local model `G_x ⋉ U(x) → X|π⁻¹(π(U(x)))`

## The text, paraphrased

For a natural representation of `G_x` on `U(x)`, the saturation `π⁻¹(π(U(x)))` consists of the
points `y` with a morphism `ψ : x' → y`, `x' ∈ U(x)`; forms on `U(x)` invariant under `G_x` are
extended to it by `σ(y) = ψ^*τ'(x')`.

## What is formalized

* `MPolyfold.isLocalScDiffeo_val_subPolyfold_of_isOpen`: the inclusion of an open subset, with
  its structure of a sub-M-polyfold, is a local sc-diffeomorphism.
* `EpFunctor.codRestrict`: an sc-smooth functor `F : S → X` with values in an ep-subgroupoid
  `A` (Definition 7.1.21), as an sc-smooth functor `S → X|A`.
* `EP.sub A hU`: **the restriction `X|U`** (Proposition 7.1.22, `subEpGroupoid`) as an object of
  `EP`; `EP.subFunctor` (the inclusion `X|U → X`), `EP.codRestrict`, and
  **`EP.subIncl : X|V → X|U`** for `V ⊆ U`.
* For a natural representation `R` of `G_x` on `U(x)` in `X|U` (`U` open and saturated):
  `EP.modelSet = π⁻¹(π(U(x)))`, saturated and open in `X` and contained in `U`
  (`isEpSubgroupoid_modelSet`, `modelSet_subset`), the functor
  **`EP.modelFunctor : G_x ⋉ U(x) → X|π⁻¹(π(U(x)))`** and
  **`EP.isEquivalence_modelFunctor`: it is an equivalence** (full and faithful by the
  uniqueness property of `Γ`, essentially surjective by the definition of the saturation, a
  local sc-diffeomorphism on objects); `EP.subIncl_comp_modelFunctor`: composed with
  `X|π⁻¹(π(U(x))) → X|U` it is Chapter 7's functor `Γ : G_x ⋉ U(x) → X|U`.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u v

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

open scoped Classical in
/-- **The inclusion of an open subset `A`, with its structure of a sub-M-polyfold, is a local
sc-diffeomorphism.** -/
theorem isLocalScDiffeo_val_subPolyfold_of_isOpen {A : Set X} (hA : P.IsSubMPolyfold A)
    (hAo : IsOpen A) [ParacompactSpace A] :
    (subPolyfold hA).IsLocalScDiffeo P (Subtype.val : A → X) := fun a => by
  refine ⟨univ, A, fun x => if h : x ∈ A then ⟨x, h⟩ else a, mem_univ _, ?_⟩
  exact
    { isScSmoothOn := subPolyfold_inclusion_isScSmooth hA
      isScSmoothOn_inv := isScSmoothOn_subPolyfold_of_val hA
        ((isScSmoothMap_id.mono hAo (subset_univ _)).congr fun x hx => by
          simp only [dif_pos (show x ∈ A from hx)]; rfl)
      mapsTo := fun b _ => b.2
      mapsTo_inv := fun _ _ => mem_univ _
      left_inv := fun b _ => by simp only [dif_pos b.2]
      right_inv := fun y hy => by simp only [dif_pos (show y ∈ A from hy)] }

end MPolyfold

open scoped EpGroupoid EpGroupoid.NaturalRep

namespace EpFunctor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- **An sc-smooth functor with values in an ep-subgroupoid `A ⊆ Y`**, as an sc-smooth functor
into the restriction `Y|A` (Proposition 7.1.22). -/
def codRestrict (F : EpFunctor X Y) {A : Set Obj'} (hA : Y.IsEpSubgroupoid A)
    [ParacompactSpace A] (h : ∀ x, F.obj x ∈ A) : EpFunctor X (EpGroupoid.subEpGroupoid hA) where
  obj x := ⟨F.obj x, h x⟩
  mor φ := ⟨F.mor φ, by rw [F.src_mor]; exact h _, by rw [F.tgt_mor]; exact h _⟩
  src_mor φ := Subtype.ext (F.src_mor φ)
  tgt_mor φ := Subtype.ext (F.tgt_mor φ)
  mor_comp φ ψ hc := Subtype.ext (by
    rw [EpGroupoid.subEpGroupoid_comp_val hA (Subtype.ext (by
      change Y.src (F.mor φ) = Y.tgt (F.mor ψ)
      rw [F.src_mor, F.tgt_mor, hc])), ]
    exact F.mor_comp φ ψ hc)
  mor_unit x := Subtype.ext (F.mor_unit x)
  isScSmoothMap_obj := MPolyfold.isScSmoothOn_subPolyfold_of_val _ F.isScSmoothMap_obj
  isScSmoothMap_mor := MPolyfold.isScSmoothOn_subPolyfold_of_val _ F.isScSmoothMap_mor

@[simp] theorem codRestrict_obj_val (F : EpFunctor X Y) {A : Set Obj'}
    (hA : Y.IsEpSubgroupoid A) [ParacompactSpace A] (h : ∀ x, F.obj x ∈ A) (x : Obj) :
    ((F.codRestrict hA h).obj x : Obj') = F.obj x := rfl

@[simp] theorem codRestrict_mor_val (F : EpFunctor X Y) {A : Set Obj'}
    (hA : Y.IsEpSubgroupoid A) [ParacompactSpace A] (h : ∀ x, F.obj x ∈ A) (φ : Mor) :
    ((F.codRestrict hA h).mor φ : Mor') = F.mor φ := rfl

end EpFunctor

namespace EP

variable (A : EP.{u})

/-- **The restriction `X|U`** of an ep-groupoid to an ep-subgroupoid `U` (Definition 7.1.21,
Proposition 7.1.22; e.g. a saturated open set, `EpGroupoid.isEpSubgroupoid_of_isOpen`), as an
object of `EP`. -/
def sub {U : Set A.Obj} (hU : A.X.IsEpSubgroupoid U) : EP.{u} :=
  haveI : ParacompactSpace U := A.X.PObj.paracompactSpace_subtype U
  EP.mk U (A.X.morOn U) (EpGroupoid.subEpGroupoid hU)

/-- The inclusion `X|U → X`. -/
def subFunctor {U : Set A.Obj} (hU : A.X.IsEpSubgroupoid U) : EpFunctor (A.sub hU).X A.X :=
  haveI : ParacompactSpace U := A.X.PObj.paracompactSpace_subtype U
  EpGroupoid.subEpFunctor hU

theorem subFunctor_obj_mem {U : Set A.Obj} (hU : A.X.IsEpSubgroupoid U) (y : (A.sub hU).Obj) :
    (A.subFunctor hU).obj y ∈ U := (show U from y).2

theorem subFunctor_full {U : Set A.Obj} (hU : A.X.IsEpSubgroupoid U) :
    (A.subFunctor hU).toFunctor.Full :=
  haveI : ParacompactSpace U := A.X.PObj.paracompactSpace_subtype U
  EpGroupoid.subEpFunctor_full hU

theorem subFunctor_obj_injective {U : Set A.Obj} (hU : A.X.IsEpSubgroupoid U) :
    Injective (A.subFunctor hU).obj := fun _ _ h => Subtype.ext h

theorem subFunctor_mor_injective {U : Set A.Obj} (hU : A.X.IsEpSubgroupoid U) :
    Injective (A.subFunctor hU).mor := fun _ _ h => Subtype.ext h

/-- The inclusion `X|U → X` of an open ep-subgroupoid is a local sc-diffeomorphism on
objects. -/
theorem isLocalScDiffeo_subFunctor_obj {U : Set A.Obj} (hU : A.X.IsEpSubgroupoid U)
    (hUo : IsOpen U) :
    (A.sub hU).X.PObj.IsLocalScDiffeo A.X.PObj (A.subFunctor hU).obj :=
  haveI : ParacompactSpace U := A.X.PObj.paracompactSpace_subtype U
  MPolyfold.isLocalScDiffeo_val_subPolyfold_of_isOpen hU.isSubMPolyfold hUo

variable {A}

/-- An sc-smooth functor `F : S → X` with values in `U`, as a functor `S → X|U`. -/
def codRestrict {S : EP.{v}} (F : EpFunctor S.X A.X) {U : Set A.Obj}
    (hU : A.X.IsEpSubgroupoid U) (h : ∀ s, F.obj s ∈ U) : EpFunctor S.X (A.sub hU).X :=
  haveI : ParacompactSpace U := A.X.PObj.paracompactSpace_subtype U
  F.codRestrict hU h

theorem subFunctor_comp_codRestrict {S : EP.{v}} (F : EpFunctor S.X A.X) {U : Set A.Obj}
    (hU : A.X.IsEpSubgroupoid U) (h : ∀ s, F.obj s ∈ U) :
    (A.subFunctor hU).comp (codRestrict F hU h) = F :=
  EpFunctor.ext rfl rfl

variable (A) in
/-- **The inclusion `X|V → X|U`** for ep-subgroupoids `V ⊆ U`. -/
def subIncl {U V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V) (hU : A.X.IsEpSubgroupoid U)
    (hVU : V ⊆ U) : EpFunctor (A.sub hV).X (A.sub hU).X :=
  codRestrict (A.subFunctor hV) hU fun v => hVU (A.subFunctor_obj_mem hV v)

/-! ### The local model -/

section Model

variable {U : Set A.Obj} (hU : A.X.IsEpSubgroupoid U) {xU : (A.sub hU).Obj}
  (R : (A.sub hU).X.NaturalRep xU)

/-- The saturation `π⁻¹(π(U(x)))` in `X` of the domain `U(x) ⊆ U` of a natural representation
in `X|U`. -/
def modelSet : Set A.Obj := A.X.saturation ((A.subFunctor hU).obj '' R.U)

theorem mem_modelSet (y : R.U) : (A.subFunctor hU).obj y ∈ modelSet hU R :=
  A.X.subset_saturation _ ⟨y.1, y.2, rfl⟩

/-- `π⁻¹(π(U(x))) ⊆ U`, since `U` is saturated. -/
theorem modelSet_subset : modelSet hU R ⊆ U := by
  have h : (A.subFunctor hU).obj '' R.U ⊆ U := by
    rintro _ ⟨y, -, rfl⟩
    exact A.subFunctor_obj_mem hU y
  have h2 : A.X.saturation ((A.subFunctor hU).obj '' R.U) ⊆ A.X.saturation U :=
    preimage_mono (image_mono h)
  have h3 : A.X.saturation U = U := hU.isSaturated
  exact fun y hy => h3 ▸ h2 hy

include R in
/-- `π⁻¹(π(U(x)))` is open and saturated in `X` when `U` is open. -/
theorem isEpSubgroupoid_modelSet (hUo : IsOpen U) : A.X.IsEpSubgroupoid (modelSet hU R) :=
  A.X.isEpSubgroupoid_saturation (hUo.isOpenMap_subtype_val _ R.isOpen_U)

variable (hUo : IsOpen U)

/-- **The local model `G_x ⋉ U(x) → X|π⁻¹(π(U(x)))`**: Chapter 7's functor `Γ` of the natural
representation, with values in the restriction to the saturation of `U(x)`. -/
def modelFunctor :
    EpFunctor R.translationEP.X (A.sub (isEpSubgroupoid_modelSet hU R hUo)).X :=
  codRestrict (S := R.translationEP) (F := (A.subFunctor hU).comp R.epFunctor)
    (isEpSubgroupoid_modelSet hU R hUo) fun y : R.U => mem_modelSet hU R y

/-- The local model composed with `X|π⁻¹(π(U(x))) → X|U` is `Γ : G_x ⋉ U(x) → X|U`. -/
theorem subIncl_comp_modelFunctor :
    (A.subIncl (isEpSubgroupoid_modelSet hU R hUo) hU (modelSet_subset hU R)).comp
      (modelFunctor hU R hUo) = R.epFunctor :=
  EpFunctor.ext (funext fun _ => Subtype.ext rfl) (funext fun _ => Subtype.ext rfl)

include R hUo in
theorem isOpen_modelSet : IsOpen (modelSet hU R) :=
  (A.X.proposition_7_1_8 _ (hUo.isOpenMap_subtype_val _ R.isOpen_U)).preimage A.X.continuous_π

/-- **The local model `G_x ⋉ U(x) → X|π⁻¹(π(U(x)))` is an equivalence** of ep-groupoids: full
and faithful by the uniqueness property of `Γ` (Theorem 7.1.13), essentially surjective by the
definition of the saturation, and a local sc-diffeomorphism on objects (Lemma 10.1.2). -/
theorem isEquivalence_modelFunctor : (modelFunctor hU R hUo).IsEquivalence := by
  have hV := isEpSubgroupoid_modelSet hU R hUo
  have hobj : ∀ y : R.U, (A.subFunctor hV).obj ((modelFunctor hU R hUo).obj y) =
      (A.subFunctor hU).obj y := fun _ => rfl
  have hmor : ∀ m : (A.sub hU).X.Isotropy xU × R.U,
      (A.subFunctor hV).mor ((modelFunctor hU R hUo).mor m) =
        (A.subFunctor hU).mor (R.Γ m.1 m.2) := fun _ => rfl
  refine EpFunctor.lemma_10_1_2 _ { faithful := ?_, full := ?_, essSurj := ?_ } ?_
  · refine (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs _ he => ?_
    have hs' : φ.2 = φ'.2 := hs
    have h1 : R.Γ φ.1 φ.2 = R.Γ φ'.1 φ'.2 :=
      A.subFunctor_mor_injective hU (((hmor φ).symm.trans
        (congrArg (A.subFunctor hV).mor he)).trans (hmor φ'))
    rw [← hs'] at h1
    exact Prod.ext ((R.Γ_inj φ.2.2).1 h1) hs'
  · refine (GroupoidFunctor.full_iff _).2 fun y y' ψ hs ht => ?_
    have hs1 : A.X.src ((A.subFunctor hV).mor ψ) = (A.subFunctor hU).obj (y : R.U) :=
      ((A.subFunctor hV).src_mor ψ).trans (congrArg (A.subFunctor hV).obj hs)
    have ht1 : A.X.tgt ((A.subFunctor hV).mor ψ) = (A.subFunctor hU).obj (y' : R.U) :=
      ((A.subFunctor hV).tgt_mor ψ).trans (congrArg (A.subFunctor hV).obj ht)
    obtain ⟨χ, hχs, hχt, hχ⟩ := ((A.subFunctor hU).full_iff.1 (A.subFunctor_full hU))
      (y : R.U).1 (y' : R.U).1 _ hs1 ht1
    obtain ⟨g, hg, -⟩ := R.existsUnique_Γ χ (hχs ▸ (y : R.U).2) (hχt ▸ (y' : R.U).2)
    rw [hχs] at hg
    refine ⟨(g, y), rfl, Subtype.ext ?_, A.subFunctor_mor_injective hV ?_⟩
    · change R.Φ g (y : R.U).1 = (y' : R.U).1
      rw [← R.tgt_Γ g _ (y : R.U).2, hg, hχt]
    · exact (hmor (g, y)).trans ((congrArg (A.subFunctor hU).mor hg).trans hχ)
  · refine (GroupoidFunctor.essSurj_iff _).2 fun v => ?_
    have hv : (A.subFunctor hV).obj v ∈ modelSet hU R := A.subFunctor_obj_mem hV v
    obtain ⟨w, ⟨y, hy, rfl⟩, hw⟩ := hv
    obtain ⟨φ, hφs, hφt⟩ := A.X.π_eq_π_iff.1 hw
    obtain ⟨ψ, hψs, hψt, -⟩ := ((A.subFunctor hV).full_iff.1 (A.subFunctor_full hV))
      ((modelFunctor hU R hUo).obj (⟨y, hy⟩ : R.U)) v φ hφs hφt
    exact ⟨(⟨y, hy⟩ : R.U), ψ, hψs, hψt⟩
  · have hval := A.isLocalScDiffeo_subFunctor_obj hV (isOpen_modelSet hU R hUo)
    have hcomp : R.translationEP.X.PObj.IsLocalScDiffeo A.X.PObj
        ((A.subFunctor hU).obj ∘ (Subtype.val : R.U → (A.sub hU).Obj)) :=
      (A.isLocalScDiffeo_subFunctor_obj hU hUo).comp
        (MPolyfold.isLocalScDiffeo_subtypeVal R.isOpen_U)
    intro y
    refine MPolyfold.IsLocalScDiffeoAt.of_comp_left (hval _)
      (continuousOn_univ.1 (modelFunctor hU R hUo).isScSmoothMap_obj.continuousOn) ?_
    exact hcomp y

end Model

end EP

end Polyfold
