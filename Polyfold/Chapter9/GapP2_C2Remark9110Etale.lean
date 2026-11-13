import Polyfold.Chapter9.GapP2_C2Remark9110

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 9,
§9.1, **Remark 9.1.10** (p. 405; 2017: Remark 9.2, p. 295), continued: the structure maps in
Mathlib's language.

# Local sc-diffeomorphisms are Mathlib local diffeomorphisms; the text's groupoid is étale

## What is formalized

* `MPolyfold.CornerCoords.pullback`: coordinate corner charts without boundary pulled back along
  an sc-diffeomorphism `f : U → V`; in the pulled-back coordinates `f` is the identity.
* **`MPolyfold.isLocalDiffeomorph_of_isLocalScDiffeo`** (the bridge): a local sc-diffeomorphism
  between M-polyfolds with corner structures of dimension `n` and `d ≡ 0` is a local
  diffeomorphism (`C^∞`) of the Mathlib manifolds `interiorChartedSpace`
  (`IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f`); `contMDiff_of_isLocalScDiffeo`.
* `EpGroupoid.isLocalScDiffeo_unit`, `EpGroupoid.isLocalScDiffeo_inv`: in an ep-groupoid the unit
  map (a section of the local sc-diffeomorphism `s`) and the inverse are local
  sc-diffeomorphisms.
* **`EpGroupoid.remark_9_1_10_orbifold_etale`** (case (2)): for `Θ` of orbifold-type and
  `n`-dimensional with `d_{|X|} = 0` on `|supp(Θ)|`, the source, target, unit and inverse maps of
  the text's groupoid `M` are Mathlib local diffeomorphisms of the classical `n`-manifolds of
  `remark_9_1_10_orbifold`, and the equivalence `M → supp(Θ)` is one on objects.
* **`EpGroupoid.remark_9_1_10_manifold_proj`** (case (1)): `p : supp(Θ) → Z`, `a ↦ |a|`, is a
  Mathlib local diffeomorphism from the classical `n`-manifold `supp(Θ)` to the classical
  `n`-manifold `Z` of `remark_9_1_10_manifold`.

## What is not formalized

The composition `M ₛ×ₜ M → M` in Mathlib's language: the fibred product is not given a Mathlib
manifold structure here (in the sc-sense the composition is sc-smooth, `EpGroupoid.isScSmoothComp`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology Module Manifold WithLp
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y} {n : ℕ}

namespace CornerCoords

variable {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}

/-- **Coordinates pulled back along an sc-diffeomorphism** `f : U → V`: the chart
`transportChart hd κ.χ = κ.χ ∘ f` on the piece `U ∩ f⁻¹(κ.s)`, with the same linear coordinates;
its coordinate image is `κ.W ∩ κ.coordInv⁻¹(V)`. -/
def pullback (hd : P.IsScDiffeoOn Q f g U V) (κ : CornerCoords Q n) (hκ : κ.IsInterior) :
    CornerCoords P n where
  χ := transportChart hd κ.χ
  isChart := transportChart_isChart hd κ.isChart
  isCornerChart := isCornerChart_transportChart hd κ.isCornerChart
  s := U ∩ f ⁻¹' κ.s
  isOpen_s := hd.isScSmoothOn.continuousOn.isOpen_inter_preimage hd.isScSmoothOn.isOpen κ.isOpen_s
  s_subset _ hx := ⟨hx.1, κ.s_subset hx.2⟩
  Ψ := κ.Ψ
  c := κ.c
  W := κ.W ∩ κ.coordInv ⁻¹' V
  isOpen_W := (κ.continuousOn_coordInv.mono fun _ hy => ⟨hy, hκ hy⟩).isOpen_inter_preimage
    κ.isOpen_W hd.isScSmoothOn_inv.isOpen
  image_s := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hc : κ.Ψ (κ.χ (f x)) + κ.c = κ.coord (f x) := rfl
      change κ.Ψ (κ.χ (f x)) + κ.c ∈ _
      rw [hc]
      refine ⟨⟨κ.coord_mem_W hx.2, ?_⟩, κ.coord_nonneg hx.2⟩
      change κ.coordInv (κ.coord (f x)) ∈ V
      rw [κ.coordInv_coord hx.2]
      exact hd.mapsTo hx.1
    · rintro ⟨⟨hyW, hyV⟩, hy⟩
      have hw := κ.coordInv_mem hyW hy
      have hfg : f (g (κ.coordInv y)) = κ.coordInv y := hd.right_inv _ hyV
      refine ⟨_, ⟨g (κ.coordInv y), ⟨hd.mapsTo_inv hyV, ?_⟩, rfl⟩, ?_⟩
      · rw [mem_preimage, hfg]; exact hw
      · change κ.Ψ (κ.χ (f (g (κ.coordInv y)))) + κ.c = y
        rw [hfg]
        exact κ.coord_coordInv hyW hy

variable (hd : P.IsScDiffeoOn Q f g U V) (κ : CornerCoords Q n) (hκ : κ.IsInterior)

theorem pullback_isInterior : (pullback hd κ hκ).IsInterior := fun _ hy => hκ hy.1

theorem pullback_coord (x : X) : (pullback hd κ hκ).coord x = κ.coord (f x) := rfl

theorem pullback_s : (pullback hd κ hκ).s = U ∩ f ⁻¹' κ.s := rfl

end CornerCoords

/-- **The bridge for maps**: a local sc-diffeomorphism `f : X → Y` between M-polyfolds with
corner structures of dimension `n` without boundary is a local diffeomorphism (`C^∞`) of the
Mathlib manifolds `interiorChartedSpace` (`IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f`).  At `x`, with
interior coordinates `κ` of `Y` at `f(x)` and their pull-back `κ'` along `f`, `f` read in the
charts `κ'`, `κ` is the identity. -/
theorem isLocalDiffeomorph_of_isLocalScDiffeo {f : X → Y} (hf : P.IsLocalScDiffeo Q f)
    (hP : P.HasCornerStructureOfDim n) (hP0 : ∀ x, P.degIndex x = 0)
    (hQ : Q.HasCornerStructureOfDim n) (hQ0 : ∀ y, Q.degIndex y = 0) :
    letI := P.interiorChartedSpace hP hP0
    letI := Q.interiorChartedSpace hQ hQ0
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f := by
  let _ := P.interiorChartedSpace hP hP0
  let _ := Q.interiorChartedSpace hQ hQ0
  have := isManifold_interiorChartedSpace hP hP0
  have := isManifold_interiorChartedSpace hQ hQ0
  intro x
  obtain ⟨U, V, g, hx, hd⟩ := hf x
  obtain ⟨κ, hfx, hκ⟩ := hQ.exists_cornerCoords_isInterior hQ0 (f x)
  set κ' := CornerCoords.pullback hd κ hκ
  have hκ' : κ'.IsInterior := CornerCoords.pullback_isInterior hd κ hκ
  set eX := κ'.toEuclideanChart hκ'
  set eY := κ.toEuclideanChart hκ
  have heX : eX ∈ IsManifold.maximalAtlas (𝓡 n) ∞ X :=
    IsManifold.subset_maximalAtlas (I := 𝓡 n) (n := ∞) ⟨κ', hκ', rfl⟩
  have heY : eY ∈ IsManifold.maximalAtlas (𝓡 n) ∞ Y :=
    IsManifold.subset_maximalAtlas (I := 𝓡 n) (n := ∞) ⟨κ, hκ, rfl⟩
  have hVo : IsOpen V := hd.isScSmoothOn_inv.isOpen
  let Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) X Y ∞ :=
    { toFun := f
      invFun := g
      source := U ∩ f ⁻¹' κ.s
      target := V ∩ κ.s
      map_source' := fun y hy => ⟨hd.mapsTo hy.1, hy.2⟩
      map_target' := fun y hy => ⟨hd.mapsTo_inv hy.1, by
        rw [mem_preimage, hd.right_inv y hy.1]; exact hy.2⟩
      left_inv' := fun y hy => hd.left_inv y hy.1
      right_inv' := fun y hy => hd.right_inv y hy.1
      open_source := κ'.isOpen_s
      open_target := hVo.inter κ.isOpen_s
      contMDiffOn_toFun := by
        refine (contMDiffOn_iff_of_mem_maximalAtlas' heX heY subset_rfl
          fun y hy => hy.2).2 (contDiffOn_id.congr ?_)
        rintro _ ⟨y, hy, rfl⟩
        simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
          OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
          modelWithCornersSelf_coe_symm, id]
        rw [eX.left_inv hy]
        rfl
      contMDiffOn_invFun := by
        refine (contMDiffOn_iff_of_mem_maximalAtlas' heY heX (fun y hy => hy.2)
          fun y hy => ⟨hd.mapsTo_inv hy.1, by
            rw [mem_preimage, hd.right_inv y hy.1]; exact hy.2⟩).2 (contDiffOn_id.congr ?_)
        rintro _ ⟨y, hy, rfl⟩
        simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
          OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
          modelWithCornersSelf_coe_symm, id]
        rw [eY.left_inv hy.2]
        change toLp 2 (κ.coord (f (g y))) = toLp 2 (κ.coord y)
        rw [hd.right_inv y hy.1] }
  exact ⟨Φ, ⟨hx, hfx⟩, fun _ _ => rfl⟩

/-- A local sc-diffeomorphism as in `isLocalDiffeomorph_of_isLocalScDiffeo` is `C^∞` in Mathlib's
sense. -/
theorem contMDiff_of_isLocalScDiffeo {f : X → Y} (hf : P.IsLocalScDiffeo Q f)
    (hP : P.HasCornerStructureOfDim n) (hP0 : ∀ x, P.degIndex x = 0)
    (hQ : Q.HasCornerStructureOfDim n) (hQ0 : ∀ y, Q.degIndex y = 0) :
    letI := P.interiorChartedSpace hP hP0
    letI := Q.interiorChartedSpace hQ hQ0
    ContMDiff (𝓡 n) (𝓡 n) ∞ f := by
  let _ := P.interiorChartedSpace hP hP0
  let _ := Q.interiorChartedSpace hQ hQ0
  exact (isLocalDiffeomorph_of_isLocalScDiffeo hf hP hP0 hQ hQ0).contMDiff

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- In an ep-groupoid the **unit map is a local sc-diffeomorphism**: it is a continuous section of
the local sc-diffeomorphism `s` (`s ∘ 1 = id`). -/
theorem isLocalScDiffeo_unit (Y : EpGroupoid Obj Mor) : Y.PObj.IsLocalScDiffeo Y.PMor Y.unit :=
  fun x => by
    have hid : Y.PObj.IsLocalScDiffeoAt Y.PObj (Y.src ∘ Y.unit) x := by
      have : Y.src ∘ Y.unit = id := funext Y.src_unit
      rw [this]
      exact ⟨univ, univ, id, mem_univ x, MPolyfold.isScDiffeoOn_id isOpen_univ⟩
    exact MPolyfold.IsLocalScDiffeoAt.of_comp_left (Y.isLocalScDiffeo_src.at _)
      (continuousOn_univ.1 Y.isScSmoothMap_unit.continuousOn) hid

/-- In an ep-groupoid the **inverse is an sc-diffeomorphism** (an involution). -/
theorem isLocalScDiffeo_inv (Y : EpGroupoid Obj Mor) : Y.PMor.IsLocalScDiffeo Y.PMor Y.inv :=
  fun φ => ⟨univ, univ, Y.inv, mem_univ φ,
    { isScSmoothOn := Y.isScSmoothMap_inv
      isScSmoothOn_inv := Y.isScSmoothMap_inv
      mapsTo := mapsTo_univ _ _
      mapsTo_inv := mapsTo_univ _ _
      left_inv := fun ψ _ => Y.inv_inv ψ
      right_inv := fun ψ _ => Y.inv_inv ψ }⟩

variable {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {n : ℕ}

/-- **2021 Remark 9.1.10, case (2), the structure maps**: under the hypotheses of
`remark_9_1_10_orbifold` (`Θ` of orbifold-type, `n`-dimensional, `d_{|X|} = 0` on `|supp(Θ)|`),
for the classical `n`-manifolds `Obj(M) = ⊔ M_x` and `Mor(M)` of the text's groupoid `M`, the
source, target, unit and inverse maps of `M` are Mathlib local diffeomorphisms (`C^∞`), and so is
the equivalence `M → supp(Θ)` on objects (`supp(Θ)` with its classical structure).  With
`remark_9_1_10_orbifold` (`M` proper, `|M| ≃ₜ Z`): `M` is an étale proper groupoid of classical
`n`-manifolds whose orbit space is `Z`, except that the composition is not stated in Mathlib's
language. -/
theorem remark_9_1_10_orbifold_etale (hΘ : X.IsBranchedEpSubgroupoid Θ) (ho : IsOrbifoldType Θ)
    (hn : X.IsNDimensional Θ n) (h0 : ∀ z ∈ X.orbitSupp Θ, X.degIndexOrbit z = 0)
    [Nonempty (supp Θ)] (c : X.SheetChoice Θ) :
    haveI := X.PObj.paracompactSpace_subtype (supp Θ)
    let hA := isEpSubgroupoid_supp_of_isOrbifoldType hΘ ho
    let M := textGroupoid hA c
    ∃ (hcO : M.PObj.HasCornerStructureOfDim n) (hdO : ∀ p, M.PObj.degIndex p = 0)
      (hcM : M.PMor.HasCornerStructureOfDim n) (hdM : ∀ q, M.PMor.degIndex q = 0)
      (hcA : (subEpGroupoid hA).PObj.HasCornerStructureOfDim n)
      (hdA : ∀ a, (subEpGroupoid hA).PObj.degIndex a = 0),
      letI := M.PObj.interiorChartedSpace hcO hdO
      letI := M.PMor.interiorChartedSpace hcM hdM
      letI := (subEpGroupoid hA).PObj.interiorChartedSpace hcA hdA
      IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ M.src ∧ IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ M.tgt ∧
        IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ M.unit ∧ IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ M.inv ∧
        IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (sheetCover hA c).functor.obj := by
  have := X.PObj.paracompactSpace_subtype (supp Θ)
  set hA := isEpSubgroupoid_supp_of_isOrbifoldType hΘ ho
  obtain ⟨hcA, hdA⟩ := hasCornerStructureOfDim_subObj hΘ ho hn h0 hA
  set M := textGroupoid hA c
  have hF := (sheetCover hA c).proposition_10_1_3.isLocalScDiffeo_obj
  have hcO : M.PObj.HasCornerStructureOfDim n := hcA.of_isLocalScDiffeo hF
  have hdO : ∀ p, M.PObj.degIndex p = 0 := fun p => by
    rw [← hF.degIndex_eq p]; exact hdA _
  have hcM : M.PMor.HasCornerStructureOfDim n := hcO.of_isLocalScDiffeo M.isLocalScDiffeo_src
  have hdM : ∀ q, M.PMor.degIndex q = 0 := fun q => by
    rw [← M.isLocalScDiffeo_src.degIndex_eq q]; exact hdO _
  exact ⟨hcO, hdO, hcM, hdM, hcA, hdA,
    MPolyfold.isLocalDiffeomorph_of_isLocalScDiffeo M.isLocalScDiffeo_src hcM hdM hcO hdO,
    MPolyfold.isLocalDiffeomorph_of_isLocalScDiffeo M.isLocalScDiffeo_tgt hcM hdM hcO hdO,
    MPolyfold.isLocalDiffeomorph_of_isLocalScDiffeo (isLocalScDiffeo_unit M) hcO hdO hcM hdM,
    MPolyfold.isLocalDiffeomorph_of_isLocalScDiffeo (isLocalScDiffeo_inv M) hcM hdM hcM hdM,
    MPolyfold.isLocalDiffeomorph_of_isLocalScDiffeo hF hcO hdO hcA hdA⟩

/-- **2021 Remark 9.1.10, case (1), the projection**: under the hypotheses of
`remark_9_1_10_manifold`, `p : supp(Θ) → Z`, `a ↦ |a|`, is a Mathlib local diffeomorphism (`C^∞`)
from the classical `n`-manifold `supp(Θ)` to the classical `n`-manifold `Z = |supp(Θ)|`, for every
M-polyfold structure `PZ` on `Z` making `p` a local sc-diffeomorphism (Proposition 9.1.9 (1),
unique by `proposition_9_1_9_one_unique`). -/
theorem remark_9_1_10_manifold_proj (hΘ : X.IsBranchedEpSubgroupoid Θ) (hm : X.IsManifoldType Θ)
    (hn : X.IsNDimensional Θ n) (h0 : ∀ z ∈ X.orbitSupp Θ, X.degIndexOrbit z = 0) :
    haveI := X.PObj.paracompactSpace_subtype (supp Θ)
    haveI := hΘ.paracompactSpace_orbitSupp
    let hA := isEpSubgroupoid_supp_of_isOrbifoldType hΘ hm.1
    ∀ PZ : MPolyfold (X.orbitSupp Θ),
      (subEpGroupoid hA).PObj.IsLocalScDiffeo PZ (X.orbitSuppProj Θ) →
      ∃ (hcA : (subEpGroupoid hA).PObj.HasCornerStructureOfDim n)
        (hdA : ∀ a, (subEpGroupoid hA).PObj.degIndex a = 0)
        (hc : PZ.HasCornerStructureOfDim n) (hd : ∀ z, PZ.degIndex z = 0),
        letI := (subEpGroupoid hA).PObj.interiorChartedSpace hcA hdA
        letI := PZ.interiorChartedSpace hc hd
        IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (X.orbitSuppProj Θ) := by
  have := X.PObj.paracompactSpace_subtype (supp Θ)
  have := hΘ.paracompactSpace_orbitSupp
  intro hA PZ hPZ
  obtain ⟨hcA, hdA⟩ := hasCornerStructureOfDim_subObj hΘ hm.1 hn h0 hA
  have hsurj : Surjective (X.orbitSuppProj Θ) := (isDescentMap_orbitSupp hm hA).surjective
  have hc : PZ.HasCornerStructureOfDim n := hcA.of_isLocalScDiffeo_surjective hPZ hsurj
  have hd : ∀ z, PZ.degIndex z = 0 := fun z => by
    obtain ⟨a, rfl⟩ := hsurj z
    rw [hPZ.degIndex_eq a]
    exact hdA a
  exact ⟨hcA, hdA, hc, hd, MPolyfold.isLocalDiffeomorph_of_isLocalScDiffeo hPZ hcA hdA hc hd⟩

end EpGroupoid

end Polyfold
