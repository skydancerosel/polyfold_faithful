import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_36

/-! Round trip for V8_36 (Theorem 8.5.8 / 2017: Theorem 8.6, Proper Covering II).

The item lists the definitions `FullOb`, `FiberCat`, `fiberIsotropy`, `restrictFiber`,
`fintypeFiberCat`, `MPolyfoldCat.ofOpen`, `ScDiffeo.ofOpen`, `IsFullyFaithfulOpenEmbedding`,
`ProperCoveringChart.geometricLift`, `.Φ`, `.Ψ` (vocabulary) and ten theorems.  `A` is the
conjunction of the types of `covering_restrict`, `nonempty_fiberCat`,
`ProperCoveringChart.isFullyFaithfulOpenEmbedding_Φ`, `…_Ψ`, `range_Φ_obj`, `range_Φ_mor`,
`range_Ψ_obj`, `range_Ψ_mor`, `comp_Ψ` and `theorem_8_6` (all in `Type`, no universe parameters).

* `A ⇒ B`: (a) is `covering_restrict`.  For (b), `V` is the `W` of the non-item
  `theorem_8_5_of_naturalRep`: B's data `(U, Φr, Γr)` (`IsNatAction`, connected) is a project
  `NaturalRep` (`natRep`; the inverse of `Φr g` is `Φr g⁻¹`), hence the `R` of a chart `C` of
  Theorem 8.5.  The lift is `C.geometricLift`, `K = geometricLiftSource`, `Ψ = C.Ψ hF`.  B's
  `L = G_x ⋉ U(x)` has morphisms `G_x × U(x)`, the project's `ULift G_x × U(x)`, so `Lg`, `A`
  and `Φ` are the project's `actionEpGroupoid`, `geometricLiftFunctor` and `C.Φ` rebuilt without
  `ULift` (`LgB`, `AB`, `PhiB`).  The facts about `Ψ` (fully faithful open embedding, ranges,
  `F ∘ Ψ = Φ ∘ A` on morphisms) come from A's theorems; the facts about `PhiB` are re-proved by
  the project's arguments (non-item lemmas of Chapter 7).  B's "sc-diffeomorphism onto the image"
  follows from "injective local sc-diffeomorphism" (`isScDiffeoOn_range`).  `L_D(y) = U(y)` and
  the sheets are the non-item `connectedComponentIn_U`, `connectedComponentIn_sheet`.
* `B ⇒ A`: `covering_restrict` and `theorem_8_6` (a) are B's first conjunct.  The other
  theorems are about the project's concrete chart witnesses `C.Φ`, `C.Ψ hF` (for every chart, and
  with `(geometricLiftFunctor L).IsProperCovering`), which B (an existential over small `U`) does
  not mention: they are re-proved outright by the project's arguments (non-item lemmas), and
  `theorem_8_6` (b) is the non-item `theorem_8_5`.
-/

namespace RoundTrip.V8_36
open Polyfold Set Function CategoryTheory
open scoped Polyfold.EpGroupoid.NaturalRep Polyfold.GeometricLift

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.covering_restrict) ∧
  (type_of% @Polyfold.EpFunctor.nonempty_fiberCat) ∧
  (type_of% @Polyfold.EpFunctor.ProperCoveringChart.isFullyFaithfulOpenEmbedding_Φ) ∧
  (type_of% @Polyfold.EpFunctor.ProperCoveringChart.isFullyFaithfulOpenEmbedding_Ψ) ∧
  (type_of% @Polyfold.EpFunctor.ProperCoveringChart.range_Φ_obj) ∧
  (type_of% @Polyfold.EpFunctor.ProperCoveringChart.range_Φ_mor) ∧
  (type_of% @Polyfold.EpFunctor.ProperCoveringChart.range_Ψ_obj) ∧
  (type_of% @Polyfold.EpFunctor.ProperCoveringChart.range_Ψ_mor) ∧
  (type_of% @Polyfold.EpFunctor.ProperCoveringChart.comp_Ψ) ∧
  (type_of% @Polyfold.EpFunctor.theorem_8_6)

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.covering_restrict, @Polyfold.EpFunctor.nonempty_fiberCat,
    @Polyfold.EpFunctor.ProperCoveringChart.isFullyFaithfulOpenEmbedding_Φ,
    @Polyfold.EpFunctor.ProperCoveringChart.isFullyFaithfulOpenEmbedding_Ψ,
    @Polyfold.EpFunctor.ProperCoveringChart.range_Φ_obj,
    @Polyfold.EpFunctor.ProperCoveringChart.range_Φ_mor,
    @Polyfold.EpFunctor.ProperCoveringChart.range_Ψ_obj,
    @Polyfold.EpFunctor.ProperCoveringChart.range_Ψ_mor,
    @Polyfold.EpFunctor.ProperCoveringChart.comp_Ψ, @Polyfold.EpFunctor.theorem_8_6⟩

/-! ### General glue -/

section General

variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

/-- An injective local sc-diffeomorphism is an sc-diffeomorphism onto its (open) image. -/
theorem isScDiffeoOn_range {P : MPolyfold Obj'} {Q : MPolyfold Obj} {f : Obj' → Obj}
    [Nonempty Obj'] (hf : P.IsLocalScDiffeo Q f) (hinj : Injective f) :
    ∃ g : Obj → Obj', P.IsScDiffeoOn Q f g univ (range f) := by
  refine ⟨invFun f, ?_, ?_, fun x _ => mem_range_self x, fun _ _ => mem_univ _,
    fun x _ => leftInverse_invFun hinj x, ?_⟩
  · refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x _ => ?_
    obtain ⟨U, V, h, hx, hd⟩ := hf x
    exact ⟨U, hd.isScSmoothOn.isOpen, hx, subset_univ _, hd.isScSmoothOn⟩
  · refine MPolyfold.IsScSmoothOn.of_locally hf.isOpenMap.isOpen_range ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨U, V, h, hx, hd⟩ := hf x
    refine ⟨V, hd.isScSmoothOn_inv.isOpen, hd.mapsTo hx,
      fun v hv => ⟨h v, hd.right_inv v hv⟩, hd.isScSmoothOn_inv.congr fun v hv => ?_⟩
    have hv' : f (h v) = v := hd.right_inv v hv
    change h v = invFun f v
    calc h v = invFun f (f (h v)) := (leftInverse_invFun hinj (h v)).symm
      _ = invFun f v := by rw [hv']
  · rintro _ ⟨x, rfl⟩
    exact congrArg f (leftInverse_invFun hinj x)

/-- The project's fully faithful open embedding data give B's `IsFFOEB`. -/
theorem isFFOEB_of {X' : EpGroupoid Obj' Mor'} {X : EpGroupoid Obj Mor} (Φ : EpFunctor X' X)
    [Nonempty Obj'] (hfull : Φ.toFunctor.Full) (hio : Injective Φ.obj)
    (hlo : X'.PObj.IsLocalScDiffeo X.PObj Φ.obj) (him : Injective Φ.mor)
    (hlm : X'.PMor.IsLocalScDiffeo X.PMor Φ.mor) : IsFFOEB Φ := by
  have : Nonempty Mor' := ⟨X'.unit (Classical.arbitrary Obj')⟩
  refine ⟨fun a b => ⟨?_, him.injOn, ?_⟩, isScDiffeoOn_range hlo hio,
    isScDiffeoOn_range hlm him⟩
  · intro φ hφ
    exact ⟨by rw [Φ.src_mor, hφ.1], by rw [Φ.tgt_mor, hφ.2]⟩
  · intro φ hφ
    obtain ⟨ψ, hψ⟩ := hfull.map_surjective (X := X'.toGroupoidStr.toOb a)
      (Y := X'.toGroupoidStr.toOb b) (X.toGroupoidStr.homMk φ hφ.1 hφ.2)
    exact ⟨ψ.1, ψ.2, congrArg Subtype.val hψ⟩

end General

/-! ### B's natural action is a project `NaturalRep` -/

section NatRep

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid Obj Mor} {x : Obj} {U : Set Obj} {Φr : X.Isotropy x → Obj → Obj}
  {Γr : X.Isotropy x → Obj → Mor}

theorem natAction_one (h : IsNatAction X x U Φr Γr) : ∀ y ∈ U, Φr 1 y = y := by
  intro y hy
  obtain ⟨ψ, hψ⟩ := h.diffeo 1
  have h1 := h.hom 1 1 y hy
  rw [mul_one] at h1
  have h2 := hψ.left_inv (Φr 1 y) (hψ.mapsTo hy)
  rw [← h1, hψ.left_inv y hy] at h2
  exact h2.symm

theorem natAction_diffeo (h : IsNatAction X x U Φr Γr) (g : X.Isotropy x) :
    X.PObj.IsScDiffeoOn X.PObj (Φr g) (Φr g⁻¹) U U := by
  obtain ⟨ψ, hψ⟩ := h.diffeo g
  refine (hψ.symm.congr_left fun y hy => ?_).symm
  have hy' := hψ.mapsTo_inv hy
  calc ψ y = Φr 1 (ψ y) := (natAction_one h _ hy').symm
    _ = Φr (g⁻¹ * g) (ψ y) := by rw [inv_mul_cancel]
    _ = Φr g⁻¹ (Φr g (ψ y)) := h.hom _ _ _ hy'
    _ = Φr g⁻¹ y := by rw [hψ.right_inv y hy]

/-- B's natural action data, as a project `NaturalRep`. -/
def natRep (h : IsNatAction X x U Φr Γr) (hc : IsConnected U) : X.NaturalRep x where
  U := U
  isOpen_U := h.isOpen
  isConnected_U := hc
  mem_U := h.mem
  Φ := Φr
  Γ := Γr
  isScDiffeoOn_Φ := natAction_diffeo h
  Φ_mul := h.hom
  isScSmoothOn_Γ := h.smooth
  Γ_self := h.Γ_x
  src_Γ g y hy := (h.src_tgt g y hy).1
  tgt_Γ g y hy := (h.src_tgt g y hy).2
  existsUnique_Γ := h.unique

end NatRep

/-! ### `L = G ⋉ U(x)` and `A : K → L` without `ULift` -/

section Lift

variable {D : Type} [Groupoid.{0} D] {G : Type} [Group G] [Finite G] [TopologicalSpace G]
  [DiscreteTopology G] {f : D ⥤ SingleObj G} (L : GeometricLift.{0} f)

omit [Finite G] [TopologicalSpace G] [DiscreteTopology G] in
theorem smul_smoothB (g : G) :
    (L.LC.obj (SingleObj.star G)).P.IsScSmoothMap (L.LC.obj (SingleObj.star G)).P
      fun z : L.Ux => g • z :=
  (L.LC.map (g : SingleObj.star G ⟶ SingleObj.star G)).isScDiffeoOn.isScSmoothOn

/-- `G ⋉ U(x)` with morphisms `G × U(x)` (the project's `geometricLiftTarget` without `ULift`). -/
noncomputable def LgB : EpGroupoid (UxB L) (G × UxB L) :=
  EpGroupoid.Examples.actionEpGroupoid (smul_smoothB L)

variable [Fintype D] [∀ a b : D, Fintype (a ⟶ b)]

/-- The functor of Proposition 8.5.7 into `LgB` (the project's `geometricLiftFunctor`
without `ULift`). -/
noncomputable def AB : EpFunctor (geometricLiftSource L) (LgB L) where
  obj p := L.τy p.1 p.2
  mor p := ((f.map p.1.2.2 : G), L.τy p.1.1 p.2)
  src_mor _ := rfl
  tgt_mor p := (L.τy_φ p.1.2.2 p.2).symm
  mor_comp p q h := by
    refine L.composable_cases (P := fun p q => (((f.map (L.yComp p q).1.2.2 : G),
      L.τy (L.yComp p q).1.1 (L.yComp p q).2) : G × L.Ux) =
      ((f.map p.1.2.2 : G) * (f.map q.1.2.2 : G), L.τy q.1.1 q.2)) h ?_
    intro a b c ψ γ z
    rw [GeometricLift.yComp_mk]
    refine Prod.ext ?_ rfl
    change (f.map (γ ≫ ψ) : G) = (f.map ψ : G) * (f.map γ : G)
    rw [f.map_comp, SingleObj.comp_as_mul]
  mor_unit x := by
    refine Prod.ext ?_ rfl
    change (f.map (𝟙 x.1) : G) = 1
    rw [f.map_id, SingleObj.id_as_one]
  isScSmoothMap_obj := (MPolyfold.isScSmoothMap_sigma_iff _).2 fun y =>
    (L.isScDiffeoOn_τy y).isScSmoothOn
  isScSmoothMap_mor := (MPolyfold.isScSmoothMap_sigma_iff _).2 fun ψ =>
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_const_discrete (f.map ψ.2.2 : G))
      (L.isScDiffeoOn_τy ψ.1).isScSmoothOn

theorem isModelB_AB (hne : ∀ y : D, Nonempty (L.LD.obj y).carrier) :
    IsModelB L (geometricLiftSource L) (LgB L) (AB L) := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl,
    ⟨id, MPolyfold.isScDiffeoOn_id isOpen_univ⟩, fun g => ⟨Prod.snd, ?_⟩, fun _ _ => rfl,
    fun _ _ _ _ => rfl, fun a b c γ ψ z => geometricLiftSource_comp_mk L ψ γ _ z,
    fun _ _ => rfl, fun _ _ _ _ => rfl, fun y => ?_, fun ψ => ?_, fun _ _ => rfl,
    fun _ _ _ _ => rfl⟩
  · have hs : ({g} ×ˢ univ : Set (G × UxB L)) = {p | p.1 = g} := by
      ext p
      simp
    have h := (isScDiffeoOn_snd_sheet (PX := (L.LC.obj (SingleObj.star G)).P) g).symm
    rw [hs] at h
    exact h
  · obtain ⟨z₀⟩ := hne y
    exact ⟨sigmaProj y z₀,
      MPolyfold.isScDiffeoOn_sigmaMk (fun y : D => (L.LD.obj y).P) y z₀⟩
  · obtain ⟨z₀⟩ := hne ψ.1
    exact ⟨sigmaProj ψ z₀,
      MPolyfold.isScDiffeoOn_sigmaMk (fun ψ : (Σ a b : D, a ⟶ b) => (L.LD.obj ψ.1).P) ψ z₀⟩

end Lift

/-! ### `Φ : L → X` without `ULift` -/

section Main

variable {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX} {F : EpFunctor Y X} {x : ObjX}
  (C : F.ProperCoveringChart x)

/-- The project's `C.Φ` with `G_x` in place of `ULift G_x`. -/
noncomputable def PhiB : EpFunctor (LgB C.geometricLift) X where
  obj z := (z : C.R.U).1
  mor p := C.R.Γ p.1 (p.2 : C.R.U).1
  src_mor p := C.R.src_Γ _ _ (p.2 : C.R.U).2
  tgt_mor p := C.R.tgt_Γ _ _ (p.2 : C.R.U).2
  mor_comp p q h := by
    have h' : (p.2 : C.R.U).1 = C.R.Φ q.1 (q.2 : C.R.U).1 := congrArg Subtype.val h
    change C.R.Γ (p.1 * q.1) (q.2 : C.R.U).1 =
      X.comp (C.R.Γ p.1 (p.2 : C.R.U).1) (C.R.Γ q.1 (q.2 : C.R.U).1)
    rw [h', C.R.Γ_mul _ _ (q.2 : C.R.U).2]
  mor_unit z := C.R.Γ_one (z : C.R.U).2
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_subtypeVal C.R.isOpen_U
  isScSmoothMap_mor := isScSmoothMap_prod_discrete_iff.2 fun g =>
    (C.R.isScSmoothOn_Γ g).comp (MPolyfold.isScSmoothMap_subtypeVal C.R.isOpen_U)
      fun z _ => z.2

theorem injective_PhiB_mor : Injective (PhiB C).mor := by
  rintro ⟨g, a⟩ ⟨g', a'⟩ h
  have h1 : X.src (C.R.Γ g (a : C.R.U).1) = X.src (C.R.Γ g' (a' : C.R.U).1) :=
    congrArg X.src h
  rw [C.R.src_Γ _ _ (a : C.R.U).2, C.R.src_Γ _ _ (a' : C.R.U).2] at h1
  obtain rfl : a = a' := Subtype.ext h1
  obtain rfl : g = g' := (C.R.Γ_inj (a : C.R.U).2).1 h
  rfl

theorem isLocalScDiffeo_PhiB_mor :
    (LgB C.geometricLift).PMor.IsLocalScDiffeo X.PMor (PhiB C).mor := by
  rintro ⟨g, a⟩
  refine ⟨{g} ×ˢ univ, C.R.Γ g '' C.R.U,
    (fun z => (g, z)) ∘ (MPolyfold.openRetraction C.R.U ∘ X.src), ⟨rfl, mem_univ _⟩, ?_⟩
  refine (((C.R.isScDiffeoOn_src_image g).symm.comp
    (MPolyfold.isScDiffeoOn_subtypeVal C.R.isOpen_U)).comp
      (isScDiffeoOn_snd_sheet (PX := (C.liftLC.obj (SingleObj.star _)).P) g)).congr_left ?_
  rintro ⟨g', a'⟩ ⟨hg', -⟩
  obtain rfl : g' = g := hg'
  rfl

theorem range_PhiB_obj : range (PhiB C).obj = C.R.U := Subtype.range_coe

theorem range_PhiB_mor : range (PhiB C).mor = morOnB X.toGroupoidStr C.R.U := by
  ext φ
  constructor
  · rintro ⟨⟨g, a⟩, rfl⟩
    exact C.R.Γ_mem_morOn g (a : C.R.U).2
  · intro hφ
    obtain ⟨g, hg⟩ := C.R.exists_Γ_eq hφ
    exact ⟨(g, (⟨X.src φ, hφ.1⟩ : C.R.U)), hg⟩

theorem isFFOEB_PhiB : IsFFOEB (PhiB C) := by
  refine ⟨fun a b => ⟨?_, (injective_PhiB_mor C).injOn, ?_⟩,
    ⟨MPolyfold.openRetraction C.R.U, ?_⟩, ?_⟩
  · intro p hp
    exact ⟨by rw [(PhiB C).src_mor, hp.1], by rw [(PhiB C).tgt_mor, hp.2]⟩
  · intro φ hφ
    have h1 : X.src φ = (a : C.R.U).1 := hφ.1
    have h2 : X.tgt φ = (b : C.R.U).1 := hφ.2
    obtain ⟨g, hg, -⟩ := C.R.existsUnique_Γ φ (by rw [h1]; exact a.2) (by rw [h2]; exact b.2)
    rw [h1] at hg
    refine ⟨(g, a), ⟨rfl, Subtype.ext ?_⟩, hg⟩
    change C.R.Φ g (a : C.R.U).1 = (b : C.R.U).1
    rw [← C.R.tgt_Γ g _ a.2, hg, h2]
  · rw [range_PhiB_obj]
    exact MPolyfold.isScDiffeoOn_subtypeVal C.R.isOpen_U
  · have : Nonempty (X.Isotropy x × UxB C.geometricLift) :=
      ⟨(1, (⟨x, C.R.mem_U⟩ : C.R.U))⟩
    exact isScDiffeoOn_range (isLocalScDiffeo_PhiB_mor C) (injective_PhiB_mor C)

/-- The construction for one chart `C`, from A's facts about `C.Ψ hF`. -/
theorem main (hF : F.IsProperCovering) [Fintype (F.FiberCat x)]
    [∀ a b : F.FiberCat x, Fintype (a ⟶ b)] [Fintype (X.Isotropy x)] [Nonempty (F.FiberCat x)]
    (hΨ : (C.Ψ hF).IsFullyFaithfulOpenEmbedding)
    (hro : range (C.Ψ hF).obj = F.obj ⁻¹' C.R.U)
    (hrm : range (C.Ψ hF).mor = Y.morOn (F.obj ⁻¹' C.R.U))
    (hcomp : F.comp (C.Ψ hF) = C.Φ.comp (geometricLiftFunctor C.geometricLift)) :
    letI : TopologicalSpace (X.Isotropy x) := ⊥
    haveI : DiscreteTopology (X.Isotropy x) := ⟨rfl⟩
    ∃ (L : GeometricLift.{0} (F.restrictFiber x))
      (_ : ParacompactSpace (ObjYB L)) (_ : ParacompactSpace (MorYB L))
      (_ : ParacompactSpace (X.Isotropy x × UxB L))
      (K : EpGroupoid (ObjYB L) (MorYB L)) (Lg : EpGroupoid (UxB L) (X.Isotropy x × UxB L))
      (A : EpFunctor K Lg) (Φ : EpFunctor Lg X) (Ψ : EpFunctor K Y),
      IsModelB L K Lg A ∧ IsFFOEB Φ ∧ IsFFOEB Ψ ∧
      Set.range Φ.obj = C.R.U ∧ Set.range Φ.mor = morOnB X.toGroupoidStr C.R.U ∧
      Set.range Ψ.obj = F.obj ⁻¹' C.R.U ∧
      Set.range Ψ.mor = morOnB Y.toGroupoidStr (F.obj ⁻¹' C.R.U) ∧
      F.obj ∘ Ψ.obj = Φ.obj ∘ A.obj ∧ F.mor ∘ Ψ.mor = Φ.mor ∘ A.mor ∧
      (∀ (g : X.Isotropy x) (z : UxB L), Φ.obj (actB L g z) = C.R.Φ g (Φ.obj z)) ∧
      (∀ y : F.FiberCat x,
        Set.range (fun z : (L.LD.obj y).carrier => Ψ.obj ⟨y, z⟩) =
          connectedComponentIn (F.obj ⁻¹' C.R.U) y.val) ∧
      (∀ (a b : F.FiberCat x) (ψ : a ⟶ b) (z : (L.LD.obj a).carrier),
        Ψ.mor ⟨⟨a, b, ψ⟩, z⟩ ∈ connectedComponentIn
          {φ : MorY | Y.src φ ∈ connectedComponentIn (F.obj ⁻¹' C.R.U) a.val ∧
            Y.tgt φ ∈ connectedComponentIn (F.obj ⁻¹' C.R.U) b.val} ψ.1) := by
  have hneY : Nonempty (ObjYB C.geometricLift) := by
    obtain ⟨a⟩ := ‹Nonempty (F.FiberCat x)›
    exact ⟨⟨a, (⟨a.val, C.mem_U _ a.mem⟩ : C.U a.val)⟩⟩
  refine ⟨C.geometricLift, inferInstance, inferInstance,
    MPolyfold.paracompactSpace_prod (discretePolyfold _) (C.geometricLift.LC.obj _).P,
    geometricLiftSource C.geometricLift, LgB C.geometricLift, AB C.geometricLift, PhiB C,
    C.Ψ hF, isModelB_AB C.geometricLift fun a => C.instNonemptyU a, isFFOEB_PhiB C,
    isFFOEB_of _ hΨ.full hΨ.injective_obj hΨ.isLocalScDiffeo_obj hΨ.injective_mor
      hΨ.isLocalScDiffeo_mor,
    range_PhiB_obj C, range_PhiB_mor C, hro, hrm, rfl,
    funext fun p => congrFun (congrArg (fun E => E.mor) hcomp) p, fun _ _ => rfl,
    fun y => ?_, fun a b ψ z => ?_⟩
  · rw [C.connectedComponentIn_U y.mem]
    exact Subtype.range_coe
  · have h := C.connectedComponentIn_sheet (EpFunctor.mem_morOn_of_hom ψ)
    rw [show Y.src ψ.1 = a.val from ψ.2.1, show Y.tgt ψ.1 = b.val from ψ.2.2] at h
    rw [C.connectedComponentIn_U a.mem, C.connectedComponentIn_U b.mem, h]
    exact (C.isScDiffeoOn_σSrc ψ).mapsTo_inv (z : C.U a.val).2

end Main

theorem A_to_B : A → B := by
  intro hA
  obtain ⟨hcov, hne, -, hffΨ, -, -, hrΨo, hrΨm, hcomp, -⟩ := hA
  intro ObjY MorY ObjX MorX _ _ _ _ _ _ _ _ _ _ _ _ Y X F hF x
  refine ⟨hcov x hF, ?_⟩
  obtain ⟨W, hWo, hxW, hW⟩ := EpFunctor.theorem_8_5_of_naturalRep hF x
  refine ⟨W, hWo, hxW, fun U Φr Γr hN hUc hUW => ?_⟩
  obtain ⟨C, hC⟩ := hW (natRep hN hUc) hUW
  have hUeq : C.R.U = U := congrArg EpGroupoid.NaturalRep.U hC
  have hΦeq : C.R.Φ = Φr := congrArg EpGroupoid.NaturalRep.Φ hC
  rw [← hUeq, ← hΦeq]
  let _ := EpFunctor.fintypeFiberCat x hF
  let _ := EpFunctor.fintypeFiberCatHom x hF
  let _ : Fintype (X.Isotropy x) := Fintype.ofFinite _
  have := hne x hF
  exact main C hF (hffΨ C hF) (hrΨo C hF) (hrΨm C hF) (hcomp C hF)

/-! ### `B ⇒ A`: the chart theorems re-proved by the project's arguments -/

section Copies

variable {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}

theorem nonempty' {F : EpFunctor Y X} (x : ObjX) (hF : F.IsProperCovering) :
    Nonempty (F.FiberCat x) := by
  obtain ⟨y, hy⟩ := hF.surjective x
  exact ⟨⟨y, hy⟩⟩

theorem ffΦ' {F : EpFunctor Y X} {x : ObjX} (C : F.ProperCoveringChart x)
    [Fintype (X.Isotropy x)] : C.Φ.IsFullyFaithfulOpenEmbedding where
  full := C.full_Φ
  faithful := EpFunctor.faithful_of_injective_mor C.injective_Φ_mor
  injective_obj := Subtype.val_injective
  isLocalScDiffeo_obj := MPolyfold.isLocalScDiffeo_subtypeVal C.R.isOpen_U
  injective_mor := C.injective_Φ_mor
  isLocalScDiffeo_mor := C.isLocalScDiffeo_Φ_mor

theorem ffΨ' {F : EpFunctor Y X} {x : ObjX} (C : F.ProperCoveringChart x)
    [Fintype (F.FiberCat x)] [∀ a b : F.FiberCat x, Fintype (a ⟶ b)] (hF : F.IsProperCovering) :
    (C.Ψ hF).IsFullyFaithfulOpenEmbedding where
  full := C.full_Ψ hF
  faithful := EpFunctor.faithful_of_injective_mor (C.injective_Ψ_mor hF)
  injective_obj := C.injective_Ψ_obj hF
  isLocalScDiffeo_obj := (MPolyfold.isLocalScDiffeo_sigma_iff _).2 fun a =>
    MPolyfold.isLocalScDiffeo_subtypeVal (C.isOpen_U' a)
  injective_mor := C.injective_Ψ_mor hF
  isLocalScDiffeo_mor := C.isLocalScDiffeo_Ψ_mor hF

theorem rΦo' {F : EpFunctor Y X} {x : ObjX} (C : F.ProperCoveringChart x)
    [Fintype (X.Isotropy x)] : range C.Φ.obj = C.R.U := Subtype.range_coe

theorem rΦm' {F : EpFunctor Y X} {x : ObjX} (C : F.ProperCoveringChart x)
    [Fintype (X.Isotropy x)] : range C.Φ.mor = X.morOn C.R.U := by
  ext φ
  constructor
  · rintro ⟨⟨g, a⟩, rfl⟩
    exact C.R.Γ_mem_morOn g.down (a : C.R.U).2
  · intro hφ
    obtain ⟨g, hg⟩ := C.R.exists_Γ_eq hφ
    exact ⟨(ULift.up g, (⟨X.src φ, hφ.1⟩ : C.R.U)), hg⟩

theorem rΨo' {F : EpFunctor Y X} {x : ObjX} (C : F.ProperCoveringChart x)
    [Fintype (F.FiberCat x)] [∀ a b : F.FiberCat x, Fintype (a ⟶ b)] (hF : F.IsProperCovering) :
    range (C.Ψ hF).obj = F.obj ⁻¹' C.R.U := by
  rw [C.preimage_eq]
  ext w
  simp only [mem_range, mem_iUnion]
  constructor
  · rintro ⟨⟨a, z⟩, rfl⟩
    exact ⟨a.val, a.mem, (z : C.U a.val).2⟩
  · rintro ⟨y, hy, hw⟩
    exact ⟨⟨⟨y, hy⟩, (⟨w, hw⟩ : C.U y)⟩, rfl⟩

theorem rΨm' {F : EpFunctor Y X} {x : ObjX} (C : F.ProperCoveringChart x)
    [Fintype (F.FiberCat x)] [∀ a b : F.FiberCat x, Fintype (a ⟶ b)] (hF : F.IsProperCovering) :
    range (C.Ψ hF).mor = Y.morOn (F.obj ⁻¹' C.R.U) := by
  ext φ
  constructor
  · rintro ⟨⟨⟨a, b, ψ⟩, z⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · change F.obj (Y.src (C.σSrc ψ (z : C.U a.val).1)) ∈ C.R.U
      rw [C.src_σSrc ψ (z : C.U a.val).2]
      exact C.obj_mem (z : C.U a.val).2
    · exact C.obj_mem (C.tgt_σSrc_mem ψ (z : C.U a.val).2)
  · rintro ⟨hs, ht⟩
    rw [C.preimage_eq] at hs ht
    obtain ⟨a, ha, hsa⟩ := mem_iUnion₂.1 hs
    obtain ⟨b, hb, htb⟩ := mem_iUnion₂.1 ht
    have hmem : φ ∈ {ψ | Y.src ψ ∈ C.U a ∧ Y.tgt ψ ∈ C.U b} := ⟨hsa, htb⟩
    rw [C.morOn_U_eq a ha b hb] at hmem
    obtain ⟨ψ₀, hψ₀, hφ⟩ := mem_iUnion₂.1 hmem
    let ψ : (⟨a, ha⟩ : F.FiberCat x) ⟶ ⟨b, hb⟩ := ⟨ψ₀, hψ₀⟩
    exact ⟨⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ψ⟩, (⟨Y.src φ, hsa⟩ : C.U a)⟩,
      (C.isScDiffeoOn_σSrc ψ).left_inv φ hφ⟩

theorem compΨ' {F : EpFunctor Y X} {x : ObjX} (C : F.ProperCoveringChart x)
    [Fintype (F.FiberCat x)] [∀ a b : F.FiberCat x, Fintype (a ⟶ b)] (hF : F.IsProperCovering)
    [Fintype (X.Isotropy x)] :
    F.comp (C.Ψ hF) = C.Φ.comp (geometricLiftFunctor C.geometricLift) :=
  EpFunctor.ext rfl (funext fun p => C.mor_σSrc p.1.2.2 (p.2 : C.U p.1.1.val).2)

end Copies

theorem B_to_A : B → A := by
  intro hB
  have hcov : ∀ {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY]
      [ParacompactSpace ObjY] [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
      {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
      [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
      {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX} {F : EpFunctor Y X} (x : ObjX),
      F.IsProperCovering → IsCoveringFunctor (F.restrictFiber x) :=
    fun {ObjY MorY} _ _ _ _ _ _ {ObjX MorX} _ _ _ _ _ _ {Y X F} x hF =>
      (hB ObjY MorY ObjX MorX Y X F hF x).1
  refine ⟨@hcov, @nonempty', @ffΦ', @ffΨ', @rΦo', @rΦm', @rΨo', @rΨm', @compΨ', ?_⟩
  intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x
  refine ⟨hcov x hF, fun V hV hx => EpFunctor.theorem_8_5 hF x hV hx, fun C => ?_⟩
  let _ := EpFunctor.fintypeFiberCat x hF
  let _ := EpFunctor.fintypeFiberCatHom x hF
  let _ : Fintype (X.Isotropy x) := Fintype.ofFinite _
  have := nonempty' x hF
  exact ⟨C.geometricLift, C.Φ, C.Ψ hF, proposition_8_3 (hcov x hF) _, ffΦ' C, ffΨ' C hF,
    rΦo' C, rΦm' C, rΨo' C hF, rΨm' C hF, compΨ' C hF⟩

#rt_check RoundTrip.V8_36.A_to_B [Polyfold.EpFunctor.covering_restrict,
  Polyfold.EpFunctor.nonempty_fiberCat,
  Polyfold.EpFunctor.ProperCoveringChart.isFullyFaithfulOpenEmbedding_Φ,
  Polyfold.EpFunctor.ProperCoveringChart.isFullyFaithfulOpenEmbedding_Ψ,
  Polyfold.EpFunctor.ProperCoveringChart.range_Φ_obj,
  Polyfold.EpFunctor.ProperCoveringChart.range_Φ_mor,
  Polyfold.EpFunctor.ProperCoveringChart.range_Ψ_obj,
  Polyfold.EpFunctor.ProperCoveringChart.range_Ψ_mor,
  Polyfold.EpFunctor.ProperCoveringChart.comp_Ψ, Polyfold.EpFunctor.theorem_8_6]
#rt_check RoundTrip.V8_36.B_to_A [Polyfold.EpFunctor.covering_restrict,
  Polyfold.EpFunctor.nonempty_fiberCat,
  Polyfold.EpFunctor.ProperCoveringChart.isFullyFaithfulOpenEmbedding_Φ,
  Polyfold.EpFunctor.ProperCoveringChart.isFullyFaithfulOpenEmbedding_Ψ,
  Polyfold.EpFunctor.ProperCoveringChart.range_Φ_obj,
  Polyfold.EpFunctor.ProperCoveringChart.range_Φ_mor,
  Polyfold.EpFunctor.ProperCoveringChart.range_Ψ_obj,
  Polyfold.EpFunctor.ProperCoveringChart.range_Ψ_mor,
  Polyfold.EpFunctor.ProperCoveringChart.comp_Ψ, Polyfold.EpFunctor.theorem_8_6]
#rt_overlap RoundTrip.V8_36.B_to_A [Polyfold.EpFunctor.covering_restrict,
  Polyfold.EpFunctor.nonempty_fiberCat,
  Polyfold.EpFunctor.ProperCoveringChart.isFullyFaithfulOpenEmbedding_Φ,
  Polyfold.EpFunctor.ProperCoveringChart.isFullyFaithfulOpenEmbedding_Ψ,
  Polyfold.EpFunctor.ProperCoveringChart.range_Φ_obj,
  Polyfold.EpFunctor.ProperCoveringChart.range_Φ_mor,
  Polyfold.EpFunctor.ProperCoveringChart.range_Ψ_obj,
  Polyfold.EpFunctor.ProperCoveringChart.range_Ψ_mor,
  Polyfold.EpFunctor.ProperCoveringChart.comp_Ψ, Polyfold.EpFunctor.theorem_8_6]

end RoundTrip.V8_36
