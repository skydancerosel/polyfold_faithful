import Polyfold.Chapter17.BranchedOrientationExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.5 (pp. 815–817): the functors `ν : C_∞ → SET` and `ν̂ : C_∞ → SET`, the categories
`Gr(C) := L_ν → C_∞` and `Gr̂(C) → C_∞`, the forgetful functor `f : Gr̂(C) → Gr(C)` of (17.87),
and the section functors `TΘ` of **Proposition 17.5.7** and `T̂Θ` of **Definition 17.5.8**.
Numbers and pages are the 2021 text's.

# The Grassmannian functors `Gr(C)` and `Gr̂(C)`

## The text, paraphrased

(p. 815) On the full subcategory `C_∞` of the smooth objects there is a functor `ν : C_∞ → SET`:
`ν(α)` is the set of finite formal sums `∑ σ_L · L`, `σ_L ≥ 0` rational, of smooth
finite-dimensional subspaces `L ⊂ T_αC`, and `ν(φ)(∑ σ_L · L) = ∑ σ_L · Tφ(L)`.  Associated to `ν`
is the category `L_ν` of the pairs `(α, L)`, `L ∈ ν(α)`, fibred over `C_∞`; `Gr(C) := L_ν`.
(p. 816, Proposition 17.5.7) A branched ep⁺-subcategory `Θ` has a section functor `TΘ` of
`Gr(C) → C_∞`.  (p. 817) `Gr̂(α)` consists of the finite formal sums of smooth oriented
finite-dimensional subspaces of `T_αC`; `Gr̂(C) → C_∞`, and the forgetful functor
`f : Gr̂(C) → Gr(C)` (17.87) forgets the orientations.  (Definition 17.5.8) An orientation is a
section functor `T̂Θ` of `Gr̂(C) → C_∞` with `f ∘ T̂Θ = TΘ` (and the pull-back condition).

## What is formalized

* On formal sums: `grPushC_unit` (`ν(1_α) = id`), `OrTC.move_unit`, `OrTC.move_move`,
  `grHatPushC_mem`, `grHatPushC_comp`, `grHatPushC_unit` (`ν̂` is a functor on the formal sums of
  `BranchedTangent.lean`), `grForgetC_mem`, `grForgetC_grHatPushC` (`f` is natural).
* `C_∞` is Mathlib's groupoid `S.regSubInf.Ob`; `smoothObjVal`, `smoothMorVal` and their
  `src`, `tgt`, identity and composition lemmas.
* **`grFunctorC hU : S.regSubInf.Ob ⥤ Type`** (`ν`), **`grHatFunctorC hU`** (`ν̂`),
  **`grForgetNatC hU : ν̂ ⟶ ν`** (17.87).
* `Gr(C) := (grFunctorC hU).Elements`, `Gr̂(C) := (grHatFunctorC hU).Elements` (Mathlib's
  category of elements, i.e. `L_ν`; groupoids), the projections `CategoryOfElements.π`, and the
  forgetful functor `grForgetFunctorC hU : Gr̂(C) ⥤ Gr(C)` with `grForgetFunctorC_comp_π`
  (`f` lies over `C_∞`).
* **`tangentSectionFunctorC hU hΘ : C_∞ ⥤ Gr(C)`**, the section functor `TΘ` of Proposition
  17.5.7 (`tangentSectionFunctorC_comp_π`: a section of `Gr(C) → C_∞`), and
  **`orientationSectionC hT : C_∞ ⥤ Gr̂(C)`** for an orientation `T̂Θ` (Definition 17.5.8), with
  `orientationSectionC_comp_π` (a section of `Gr̂(C) → C_∞`), `orientationSectionC_forget_obj`
  (`f ∘ T̂Θ = TΘ` on objects) and **`orientationSectionCForgetIso`** (`f ∘ T̂Θ ≅ TΘ`, an
  isomorphism of functors whose components lie over identities).
* Witness: `reflection_orientationSectionC` (on `ℤ/2 ⋉ ℝ`, the two orientations of `Θ₀ = 1_{0}`
  of `BranchedOrientationExamples.lean` give two different section functors of `Gr̂(C) → C_∞`
  whose value at the smooth object `0`, with isotropy `ℤ/2`, is not `0`).

## Readings

* `SET` is read as Mathlib's category `Type`; `C_∞` is the full subgroupoid `regSubInf` of the
  smooth objects (Mathlib's groupoid on `regSubInf.Ob`); `L_ν` is Mathlib's category of elements
  `ν.Elements` (objects `(α, L)`, `L ∈ ν(α)`; morphisms `φ : α → α'` with `ν(φ)(L) = L'`).
* `Gr(α)` and `Gr̂(α)` are the sets `GrC α`, `GrHatC α` of `BranchedTangent.lean` (formal sums of
  subsets, resp. oriented subsets, of the fibre of `TC` over `α`).  Smooth objects lie in `C¹`
  and have uniformizers under `HasUniformizers`, so `T_αC` is defined for them.
* "A section functor `T̂Θ`" is read as a functor `C_∞ → Gr̂(C)` whose composite with the
  projection is the identity; `IsOrientationC` (its fields `mem`, `natural`) gives one, and its
  field `lifts` gives `f ∘ T̂Θ = TΘ`.
-/

set_option maxSynthPendingDepth 3

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-! ### `ν` and `ν̂` on formal sums -/

section FormalSums

/-- `ν(1_α) = id` on `Gr(α)`. -/
theorem grPushC_unit {α : C.Obj} {w : Set S.TangentCatObj →₀ ℚ} (hw : w ∈ S.GrC α) :
    S.grPushC (C.toGroupoidStr.unit α) w = w := by
  rw [grPushC]
  conv_rhs => rw [← Finsupp.mapDomain_id (v := w)]
  refine Finsupp.mapDomain_congr fun L hL => ?_
  refine (image_congr fun e he => ?_).trans (image_id L)
  rw [← hw.2 L hL e he]
  exact tcMove_unit e

/-- `T1_α(L̂) = L̂` for `L̂ ⊂ T_αC`. -/
theorem OrTC.move_unit {α : C.Obj} {g : S.OrTC} (hc : ∀ e ∈ g.carrier, e.base = α)
    (hf : ∀ v ∈ g.frames, ∀ i, v i ∈ g.carrier) :
    OrTC.move S (C.toGroupoidStr.unit α) g = g := by
  obtain ⟨n, L, F⟩ := g
  have h1 : S.tcMove (C.toGroupoidStr.unit α) '' L = L := by
    refine (image_congr fun e he => ?_).trans (image_id L)
    rw [← hc e he]
    exact tcMove_unit e
  have h2 : (fun v => S.tcMove (C.toGroupoidStr.unit α) ∘ v) '' F = F := by
    refine (image_congr fun v hv => funext fun i => ?_).trans (image_id F)
    change S.tcMove (C.toGroupoidStr.unit α) (v i) = v i
    rw [← hc (v i) (hf v hv i)]
    exact tcMove_unit (v i)
  change (⟨n, S.tcMove (C.toGroupoidStr.unit α) '' L,
    (fun v => S.tcMove (C.toGroupoidStr.unit α) ∘ v) '' F⟩ : S.OrTC) = ⟨n, L, F⟩
  rw [h1, h2]

/-- `Tφ'(Tφ(L̂)) = T(φ' ∘ φ)(L̂)` for `L̂ ⊂ T_{s φ}C`. -/
theorem OrTC.move_move {φ φ' : C.Mor} {g : S.OrTC}
    (hc : ∀ e ∈ g.carrier, e.base = C.toGroupoidStr.src φ)
    (hf : ∀ v ∈ g.frames, ∀ i, v i ∈ g.carrier) (ht : S.TangentObj (C.toGroupoidStr.tgt φ))
    (hφ : C.toGroupoidStr.src φ' = C.toGroupoidStr.tgt φ)
    (ht' : S.TangentObj (C.toGroupoidStr.tgt φ')) :
    OrTC.move S φ' (OrTC.move S φ g) = OrTC.move S (C.toGroupoidStr.comp φ' φ) g := by
  obtain ⟨n, L, F⟩ := g
  have h1 : S.tcMove φ' '' (S.tcMove φ '' L) = S.tcMove (C.toGroupoidStr.comp φ' φ) '' L := by
    rw [image_image]
    exact image_congr fun e he => tcMove_tcMove (hc e he).symm ht hφ ht'
  have h2 : (fun v => S.tcMove φ' ∘ v) '' ((fun v => S.tcMove φ ∘ v) '' F) =
      (fun v => S.tcMove (C.toGroupoidStr.comp φ' φ) ∘ v) '' F := by
    rw [image_image]
    exact image_congr fun v hv => funext fun i =>
      tcMove_tcMove (hc (v i) (hf v hv i)).symm ht hφ ht'
  change (⟨n, S.tcMove φ' '' (S.tcMove φ '' L),
    (fun v => S.tcMove φ' ∘ v) '' ((fun v => S.tcMove φ ∘ v) '' F)⟩ : S.OrTC) =
    ⟨n, S.tcMove (C.toGroupoidStr.comp φ' φ) '' L,
      (fun v => S.tcMove (C.toGroupoidStr.comp φ' φ) ∘ v) '' F⟩
  rw [h1, h2]

/-- **`ν̂(φ)` maps `Gr̂(s φ)` to `Gr̂(t φ)`.** -/
theorem grHatPushC_mem {φ : C.Mor} (ht : S.TangentObj (C.toGroupoidStr.tgt φ))
    {w : S.OrTC →₀ ℚ} (hw : w ∈ S.GrHatC (C.toGroupoidStr.src φ)) :
    S.grHatPushC φ w ∈ S.GrHatC (C.toGroupoidStr.tgt φ) := by
  classical
  refine ⟨grC_mapDomain_nonneg hw.1 _, fun g' hg' => ?_⟩
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg')
  obtain ⟨hc, hf⟩ := hw.2 g hg
  refine ⟨fun e' he' => ?_, fun v' hv' i => ?_⟩
  · obtain ⟨e, he, rfl⟩ := he'
    exact tcMove_base (hc e he).symm ht
  · obtain ⟨v, hv, rfl⟩ := hv'
    exact ⟨v i, hf v hv i, rfl⟩

/-- **`ν̂(φ') ∘ ν̂(φ) = ν̂(φ' ∘ φ)`.** -/
theorem grHatPushC_comp {φ φ' : C.Mor} (ht : S.TangentObj (C.toGroupoidStr.tgt φ))
    (hφ : C.toGroupoidStr.src φ' = C.toGroupoidStr.tgt φ)
    (ht' : S.TangentObj (C.toGroupoidStr.tgt φ')) {w : S.OrTC →₀ ℚ}
    (hw : w ∈ S.GrHatC (C.toGroupoidStr.src φ)) :
    S.grHatPushC φ' (S.grHatPushC φ w) = S.grHatPushC (C.toGroupoidStr.comp φ' φ) w := by
  rw [grHatPushC, grHatPushC, grHatPushC, ← Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_congr fun g hg => OrTC.move_move (hw.2 g hg).1 (hw.2 g hg).2 ht hφ ht'

/-- **`ν̂(1_α) = id`** on `Gr̂(α)`. -/
theorem grHatPushC_unit {α : C.Obj} {w : S.OrTC →₀ ℚ} (hw : w ∈ S.GrHatC α) :
    S.grHatPushC (C.toGroupoidStr.unit α) w = w := by
  rw [grHatPushC]
  conv_rhs => rw [← Finsupp.mapDomain_id (v := w)]
  exact Finsupp.mapDomain_congr fun g hg => OrTC.move_unit (hw.2 g hg).1 (hw.2 g hg).2

/-- **`f` maps `Gr̂(α)` to `Gr(α)`** (17.87). -/
theorem grForgetC_mem {α : C.Obj} {w : S.OrTC →₀ ℚ} (hw : w ∈ S.GrHatC α) :
    S.grForgetC w ∈ S.GrC α := by
  classical
  refine ⟨grC_mapDomain_nonneg hw.1 _, fun L hL e he => ?_⟩
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hL)
  exact (hw.2 g hg).1 e he

/-- **`f` is natural**: `f ∘ ν̂(φ) = ν(φ) ∘ f`. -/
theorem grForgetC_grHatPushC (φ : C.Mor) (w : S.OrTC →₀ ℚ) :
    S.grForgetC (S.grHatPushC φ w) = S.grPushC φ (S.grForgetC w) := by
  rw [grForgetC, grHatPushC, grPushC, grForgetC, ← Finsupp.mapDomain_comp,
    ← Finsupp.mapDomain_comp]
  rfl

end FormalSums

/-! ### The groupoid `C_∞` -/

section SmoothSub

/-- The object of `C` underlying an object of `C_∞`. -/
abbrev smoothObjVal (α : S.regSubInf.Ob) : C.Obj := (show S.regSetInf from α).1

theorem isSmoothObj_smoothObjVal (α : S.regSubInf.Ob) : S.IsSmoothObj (smoothObjVal α) :=
  (show S.regSetInf from α).2

/-- The morphism of `C` underlying a morphism of `C_∞`. -/
abbrev smoothMorVal {α β : S.regSubInf.Ob} (f : α ⟶ β) : C.Mor := f.1.1

theorem src_smoothMorVal {α β : S.regSubInf.Ob} (f : α ⟶ β) :
    C.toGroupoidStr.src (smoothMorVal f) = smoothObjVal α :=
  congrArg Subtype.val f.2.1

theorem tgt_smoothMorVal {α β : S.regSubInf.Ob} (f : α ⟶ β) :
    C.toGroupoidStr.tgt (smoothMorVal f) = smoothObjVal β :=
  congrArg Subtype.val f.2.2

theorem smoothMorVal_id (α : S.regSubInf.Ob) :
    smoothMorVal (𝟙 α) = C.toGroupoidStr.unit (smoothObjVal α) :=
  rfl

theorem smoothMorVal_comp {α β γ : S.regSubInf.Ob} (f : α ⟶ β) (g : β ⟶ γ) :
    smoothMorVal (f ≫ g) = C.toGroupoidStr.comp (smoothMorVal g) (smoothMorVal f) := by
  have h : C.toGroupoidStr.src g.1.1 = C.toGroupoidStr.tgt f.1.1 :=
    (src_smoothMorVal g).trans (tgt_smoothMorVal f).symm
  change ((C.toGroupoidStr.fullSub S.regSetInf).comp g.1 f.1).1 = _
  simp only [GroupoidStr.fullSub, dif_pos h]

end SmoothSub

/-! ### The functors `ν`, `ν̂` and the forgetful transformation -/

section Functors

variable (hU : S.HasUniformizers)

omit hU in
theorem tangentObj_smoothObjVal (hU : S.HasUniformizers) (α : S.regSubInf.Ob) :
    S.TangentObj (smoothObjVal α) :=
  tangentObj_of_isSmoothObj hU (isSmoothObj_smoothObjVal α)

/-- `ν(φ)` on `Gr(s φ)`, `φ` a morphism of `C_∞`. -/
def grMapC {α β : S.regSubInf.Ob} (f : α ⟶ β) (w : S.GrC (smoothObjVal α)) :
    S.GrC (smoothObjVal β) :=
  ⟨S.grPushC (smoothMorVal f) w.1, by
    have h := grPushC_mem (φ := smoothMorVal f)
      (by rw [tgt_smoothMorVal]; exact tangentObj_smoothObjVal hU β)
      (by rw [src_smoothMorVal]; exact w.2)
    rwa [tgt_smoothMorVal] at h⟩

/-- `ν̂(φ)` on `Gr̂(s φ)`, `φ` a morphism of `C_∞`. -/
def grHatMapC {α β : S.regSubInf.Ob} (f : α ⟶ β) (w : S.GrHatC (smoothObjVal α)) :
    S.GrHatC (smoothObjVal β) :=
  ⟨S.grHatPushC (smoothMorVal f) w.1, by
    have h := grHatPushC_mem (φ := smoothMorVal f)
      (by rw [tgt_smoothMorVal]; exact tangentObj_smoothObjVal hU β)
      (by rw [src_smoothMorVal]; exact w.2)
    rwa [tgt_smoothMorVal] at h⟩

theorem grMapC_id (α : S.regSubInf.Ob) : grMapC hU (𝟙 α) = id :=
  funext fun w => Subtype.ext (grPushC_unit w.2)

theorem grMapC_comp {α β γ : S.regSubInf.Ob} (f : α ⟶ β) (g : β ⟶ γ) :
    grMapC hU (f ≫ g) = grMapC hU g ∘ grMapC hU f := by
  funext w
  apply Subtype.ext
  change S.grPushC (smoothMorVal (f ≫ g)) w.1 =
    S.grPushC (smoothMorVal g) (S.grPushC (smoothMorVal f) w.1)
  rw [smoothMorVal_comp, grPushC_comp (by rw [tgt_smoothMorVal]; exact tangentObj_smoothObjVal hU β)
    ((src_smoothMorVal g).trans (tgt_smoothMorVal f).symm)
    (by rw [tgt_smoothMorVal]; exact tangentObj_smoothObjVal hU γ)
    (by rw [src_smoothMorVal]; exact w.2)]

theorem grHatMapC_id (α : S.regSubInf.Ob) : grHatMapC hU (𝟙 α) = id :=
  funext fun w => Subtype.ext (grHatPushC_unit w.2)

theorem grHatMapC_comp {α β γ : S.regSubInf.Ob} (f : α ⟶ β) (g : β ⟶ γ) :
    grHatMapC hU (f ≫ g) = grHatMapC hU g ∘ grHatMapC hU f := by
  funext w
  apply Subtype.ext
  change S.grHatPushC (smoothMorVal (f ≫ g)) w.1 =
    S.grHatPushC (smoothMorVal g) (S.grHatPushC (smoothMorVal f) w.1)
  rw [smoothMorVal_comp, grHatPushC_comp
    (by rw [tgt_smoothMorVal]; exact tangentObj_smoothObjVal hU β)
    ((src_smoothMorVal g).trans (tgt_smoothMorVal f).symm)
    (by rw [tgt_smoothMorVal]; exact tangentObj_smoothObjVal hU γ)
    (by rw [src_smoothMorVal]; exact w.2)]

variable (S) in
/-- **The functor `ν : C_∞ → SET`** (2021 p. 815): `ν(α) = Gr(α)`, `ν(φ)(∑ σ_L · L) =
∑ σ_L · Tφ(L)`. -/
def grFunctorC : S.regSubInf.Ob ⥤ Type (max u 1) where
  obj α := S.GrC (smoothObjVal α)
  map f := ↾(grMapC hU f)
  map_id α := by
    rw [grMapC_id]
    rfl
  map_comp f g := by
    rw [grMapC_comp]
    rfl

variable (S) in
/-- **The functor `ν̂ : C_∞ → SET`** (2021 p. 817): `ν̂(α) = Gr̂(α)`. -/
def grHatFunctorC : S.regSubInf.Ob ⥤ Type (max u 1) where
  obj α := S.GrHatC (smoothObjVal α)
  map f := ↾(grHatMapC hU f)
  map_id α := by
    rw [grHatMapC_id]
    rfl
  map_comp f g := by
    rw [grHatMapC_comp]
    rfl

theorem grFunctorC_map_apply {α β : S.regSubInf.Ob} (f : α ⟶ β)
    (w : (S.grFunctorC hU).obj α) :
    ((S.grFunctorC hU).map f w).1 = S.grPushC (smoothMorVal f) w.1 :=
  rfl

theorem grHatFunctorC_map_apply {α β : S.regSubInf.Ob} (f : α ⟶ β)
    (w : (S.grHatFunctorC hU).obj α) :
    ((S.grHatFunctorC hU).map f w).1 = S.grHatPushC (smoothMorVal f) w.1 :=
  rfl

variable (S) in
/-- **The forgetful transformation `f : ν̂ → ν`** (17.87): it forgets the orientations. -/
def grForgetNatC : S.grHatFunctorC hU ⟶ S.grFunctorC hU where
  app α := ↾(fun w : S.GrHatC (smoothObjVal α) =>
    (⟨S.grForgetC w.1, grForgetC_mem w.2⟩ : S.GrC (smoothObjVal α)))
  naturality α β f := by
    have h : (fun w : S.GrHatC (smoothObjVal α) =>
          (⟨S.grForgetC (grHatMapC hU f w).1, grForgetC_mem (grHatMapC hU f w).2⟩ :
            S.GrC (smoothObjVal β))) =
        fun w => grMapC hU f ⟨S.grForgetC w.1, grForgetC_mem w.2⟩ :=
      funext fun w => Subtype.ext (grForgetC_grHatPushC _ _)
    change ↾(fun w : S.GrHatC (smoothObjVal α) =>
        (⟨S.grForgetC (grHatMapC hU f w).1, grForgetC_mem (grHatMapC hU f w).2⟩ :
          S.GrC (smoothObjVal β))) = _
    rw [h]
    rfl

theorem grForgetNatC_app_apply (α : S.regSubInf.Ob) (w : (S.grHatFunctorC hU).obj α) :
    ((S.grForgetNatC hU).app α w).1 = S.grForgetC w.1 :=
  rfl

end Functors

/-! ### `Gr(C) → C_∞`, `Gr̂(C) → C_∞` and the section functors -/

section Sections

variable (hU : S.HasUniformizers)

variable (S) in
/-- **The forgetful functor `f : Gr̂(C) → Gr(C)`** (17.87), between the categories of elements
`Gr̂(C) = L_ν̂` and `Gr(C) = L_ν`. -/
abbrev grForgetFunctorC : (S.grHatFunctorC hU).Elements ⥤ (S.grFunctorC hU).Elements :=
  CategoryOfElements.map (S.grForgetNatC hU)

/-- `f` lies over `C_∞`. -/
theorem grForgetFunctorC_comp_π :
    S.grForgetFunctorC hU ⋙ CategoryOfElements.π (S.grFunctorC hU) =
      CategoryOfElements.π (S.grHatFunctorC hU) :=
  CategoryOfElements.map_π _

variable {Θ : C.Obj → ℚ}

variable (S) in
/-- **The section functor `TΘ : C_∞ → Gr(C)`** of Proposition 17.5.7 (2021 p. 816). -/
def tangentSectionFunctorC (hΘ : S.IsBranchedSubcategory Θ) :
    S.regSubInf.Ob ⥤ (S.grFunctorC hU).Elements where
  obj α := ⟨α, ⟨S.branchedTangentSection hU Θ (smoothObjVal α),
    (S.proposition_17_5_7 hU hΘ).1 _ (tangentObj_smoothObjVal hU α)⟩⟩
  map {α β} f := ⟨f, by
    apply Subtype.ext
    change S.grPushC (smoothMorVal f) (S.branchedTangentSection hU Θ (smoothObjVal α)) =
      S.branchedTangentSection hU Θ (smoothObjVal β)
    have h := (S.proposition_17_5_7 hU hΘ).2.2.1 (smoothMorVal f)
      (by rw [tgt_smoothMorVal]; exact tangentObj_smoothObjVal hU β)
    rw [src_smoothMorVal, tgt_smoothMorVal] at h
    exact h.symm⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `TΘ` is a section of `Gr(C) → C_∞`. -/
theorem tangentSectionFunctorC_comp_π (hΘ : S.IsBranchedSubcategory Θ) :
    S.tangentSectionFunctorC hU hΘ ⋙ CategoryOfElements.π (S.grFunctorC hU) = 𝟭 _ :=
  rfl

variable {T : C.Obj → S.OrTC →₀ ℚ}

variable (S) in
/-- **The section functor `T̂Θ : C_∞ → Gr̂(C)`** of an orientation (Definition 17.5.8, 2021
p. 817). -/
def orientationSectionC (hT : S.IsOrientationC hU Θ T) :
    S.regSubInf.Ob ⥤ (S.grHatFunctorC hU).Elements where
  obj α := ⟨α, ⟨T (smoothObjVal α), hT.mem _ (isSmoothObj_smoothObjVal α)⟩⟩
  map {α β} f := ⟨f, by
    apply Subtype.ext
    change S.grHatPushC (smoothMorVal f) (T (smoothObjVal α)) = T (smoothObjVal β)
    have h := hT.natural (smoothMorVal f)
      (by rw [src_smoothMorVal]; exact isSmoothObj_smoothObjVal α)
    rw [src_smoothMorVal, tgt_smoothMorVal] at h
    exact h.symm⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `T̂Θ` is a section of `Gr̂(C) → C_∞`. -/
theorem orientationSectionC_comp_π (hT : S.IsOrientationC hU Θ T) :
    S.orientationSectionC hU hT ⋙ CategoryOfElements.π (S.grHatFunctorC hU) = 𝟭 _ :=
  rfl

/-- The fibre part of `f ∘ T̂Θ = TΘ`: `ν(1_α)(f(T̂Θ(α))) = TΘ(α)`. -/
theorem orientationSectionC_forget_snd (hΘ : S.IsBranchedSubcategory Θ)
    (hT : S.IsOrientationC hU Θ T) (α : S.regSubInf.Ob) :
    (S.grFunctorC hU).map (𝟙 α)
        ((S.grForgetFunctorC hU).obj ((S.orientationSectionC hU hT).obj α)).2 =
      ((S.tangentSectionFunctorC hU hΘ).obj α).2 := by
  apply Subtype.ext
  change S.grPushC (C.toGroupoidStr.unit (smoothObjVal α)) (S.grForgetC (T (smoothObjVal α))) =
    S.branchedTangentSection hU Θ (smoothObjVal α)
  rw [grPushC_unit (grForgetC_mem (hT.mem _ (isSmoothObj_smoothObjVal α)))]
  exact hT.lifts _ (isSmoothObj_smoothObjVal α)

/-- **`f ∘ T̂Θ = TΘ` on objects** (Definition 17.5.8). -/
theorem orientationSectionC_forget_obj (hΘ : S.IsBranchedSubcategory Θ)
    (hT : S.IsOrientationC hU Θ T) (α : S.regSubInf.Ob) :
    (S.grForgetFunctorC hU).obj ((S.orientationSectionC hU hT).obj α) =
      (S.tangentSectionFunctorC hU hΘ).obj α :=
  Functor.Elements.ext _ _ rfl (orientationSectionC_forget_snd hU hΘ hT α)

/-- **2021 Definition 17.5.8 (`f ∘ T̂Θ = TΘ`) as functors**: `f ∘ T̂Θ ≅ TΘ`, with components lying
over the identities of `C_∞`. -/
def orientationSectionCForgetIso (hΘ : S.IsBranchedSubcategory Θ) (hT : S.IsOrientationC hU Θ T) :
    S.orientationSectionC hU hT ⋙ S.grForgetFunctorC hU ≅ S.tangentSectionFunctorC hU hΘ :=
  NatIso.ofComponents
    (fun α => CategoryOfElements.isoMk _ _ (Iso.refl _)
      (orientationSectionC_forget_snd hU hΘ hT α))
    (fun f => by
      apply CategoryOfElements.ext
      change f ≫ 𝟙 _ = 𝟙 _ ≫ f
      rw [Category.comp_id, Category.id_comp])

theorem orientationSectionCForgetIso_hom_app_val (hΘ : S.IsBranchedSubcategory Θ)
    (hT : S.IsOrientationC hU Θ T) (α : S.regSubInf.Ob) :
    ((S.orientationSectionCForgetIso hU hΘ hT).hom.app α).val = 𝟙 α :=
  rfl

end Sections

/-! ### Witness -/

open EpGroupoid.Examples

/-- **Witness for the section functors of `Gr̂(C) → C_∞`**: on the reflection polyfold
`ℤ/2 ⋉ ℝ`, the two orientations `T̂_±` of `Θ₀ = 1_{0}` give section functors of
`Gr̂(C) → C_∞` lifting `TΘ₀`; they differ, and their value at the smooth object `0` (isotropy
`ℤ/2`) is not `0`. -/
theorem reflection_orientationSectionC :
    (∀ b, reflectionConstruction.orientationSectionC reflectionConstruction_hasUniformizers
        (isOrientationC_reflection b) ⋙ CategoryOfElements.π _ = 𝟭 _) ∧
      pointOrientationC isScSmoothMap_units_smul true ≠
        pointOrientationC isScSmoothMap_units_smul false ∧
      ∀ b, pointOrientationC isScSmoothMap_units_smul b 0 ≠ 0 :=
  ⟨fun b => orientationSectionC_comp_π _ (isOrientationC_reflection b), pointOrientationC_ne.1,
    pointOrientationC_ne.2⟩

end GCT.PolyfoldConstruction

end Polyfold
