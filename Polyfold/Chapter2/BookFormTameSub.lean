import Polyfold.Chapter2.TameSub
import Polyfold.Chapter2.SubMPolyfoldTangent
import Polyfold.Chapter2.ReducedTangentIntrinsic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §2.5:
**Definitions 2.5.18 and 2.5.19** (pp. 62–63, new in the 2021 edition), with condition (3) stated
in the tangent space `T_yX`.

# Tame sub-M-polyfolds in book form

## The text, paraphrased

(Definition 2.5.18) The structure induced on a sub-M-polyfold `Y` is tame if it admits an
equivalent atlas with tame models.  (Definition 2.5.19) For a tame `X` and a sub-M-polyfold `Y`,
`Y` is a tame sub-M-polyfold if every `y ∈ Y` has an open `V` and an sc-smooth retraction
`r : V → V` with (1) `r(V) = Y ∩ V`, (2) `d_X ∘ r = d_X` on `V`, and (3) at every smooth
`y ∈ Y ∩ V`, an sc-subspace `A ⊆ T^R_yX` with `T_yX = T_yY ⊕ A`.

## What is formalized

* `MPolyfold.fiberCoord_subInclusionCLM`, `MPolyfold.coe_map_range_subInclusionCLM`: for a chart
  `φ` of `X` and the sub-chart of `Y` built on it, `Tφ(x) ∘ Ti` is the chart map of the sub-chart,
  so `Tφ(x)` maps `T_yY ⊆ T_yX` (the image of `Ti`, `subTangentRange`) onto the tangent space of
  the chart image `φ(W ∩ Y)` of `Y`.
* `MPolyfold.HasReducedScComplement`: (3) in `T_yX`, with `T_yY` the image of `Ti` and `T^R_yX` the
  reduced tangent space `reducedTangentFiber` of Definition 2.5.8; `hasReducedScComplement_iff`:
  it is the chart form of `TameSubData`.
* `MPolyfold.TameSubData2021`, `MPolyfold.IsTameSubMPolyfold2021`: Definition 2.5.19 with (3) in
  `T_yX`; **`MPolyfold.definition_2_5_19_book`**: it is `IsTameSubMPolyfold` (the chart form, row
  V2.78), it implies the tame induced structure of Definition 2.5.18 (`HasTameInducedStructure`),
  and `Y = X` satisfies it for tame `X`.  Through the equivalence, the examples `A`, `B` in
  `[0, ∞)² × ℝ` of p. 63 (`isTameSubMPolyfold_setA`, `not_mem_tameSubData_setB`) apply to it.

## The reading

* The linear and Banach structure of `T_yX` is intrinsic (Definition 2.3.14,
  `TangentSpaceLinear.lean`); its sc-structure at a smooth `y` is carried by a chart, as in the text
  ("an sc-Banach space, since `T_{φ(y)}O` is one"), and is the same through every chart
  (`transitionCLM_mem_range_toBase`).  "`A` is an sc-subspace and `T_yX = T_yY ⊕ A`" is therefore
  stated as an algebraic splitting `IsCompl` of `T_yX`, together with the sc-subspace property and
  the levelwise splitting of the images in the chart `φ` that also defines `T^R_yX` (with a
  presentation `T` of its partial quadrant; `T^R_yX` does not depend on `(φ, T)`,
  `reducedTangentFiber_eq`).
* `T_yY ⊆ T_yX` is read through `Ti : T_yY → T_yX`, the tangent of the inclusion (injective,
  Proposition 2.3.19).
-/

open Set Function Topology

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

section SubChartTangent

variable {Y : Set X} (hY : P.IsSubMPolyfold Y) [ParacompactSpace Y]
  {a : (subPolyfold hY).Level 1} {x : P.Level 1}
  (hax : ((subPolyfold hY).levelVal 1 a : Y).1 = P.levelVal 1 x)
  (d : P.SubData Y) {φ : MChart X} (hφ : P.IsChart φ) (a₀ : Y)
  (ha : (subPolyfold hY).levelVal 1 a ∈ (subChart d hφ a₀).source)

/-- **`T_aY ⊆ T_xX`**: the image `Ti(T_aY)` of the tangent space of `Y` in that of `X`
(`Ti` is injective, `injective_subInclusionCLM`). -/
def subTangentRange : Submodule ℝ (P.tangentFiber x) :=
  LinearMap.range (subInclusionCLM hY hax : (subPolyfold hY).tangentFiber a →ₗ[ℝ] P.tangentFiber x)

include hax ha in
lemma levelVal_mem_source_of_subChart : P.levelVal 1 x ∈ φ.source :=
  hax ▸ d.shrink_subset_source φ ha

omit [ParacompactSpace Y] in
/-- The chart image of the domain of `φ ∘ i ∘ σ⁻¹` for the sub-chart `σ = subChart d hφ a₀` is the
model `φ(W ∩ Y)` of `σ`. -/
lemma subChart_image_fdom :
    (subChart d hφ a₀) '' TangentPre.fdom (subChart d hφ a₀) Subtype.val φ =
      φ '' (d.shrink φ ∩ Y) := by
  ext z
  constructor
  · rintro ⟨y, ⟨hy, -⟩, rfl⟩
    exact ⟨y.1, ⟨hy, y.2⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hyY⟩, rfl⟩
    exact ⟨⟨y, hyY⟩, ⟨hy, d.shrink_subset_source φ hy⟩, rfl⟩

omit [ParacompactSpace Y] in
/-- `φ ∘ i ∘ σ⁻¹ = id` on the model `φ(W ∩ Y)` of the sub-chart `σ`. -/
lemma eqOn_subChart_symm :
    EqOn (α := (subChart d hφ a₀).model.E 0) (β := (subChart d hφ a₀).model.E 0)
      (φ ∘ Subtype.val ∘ (subChart d hφ a₀).symm) id (φ '' (d.shrink φ ∩ Y)) := by
  rintro _ ⟨y, hy, rfl⟩
  change φ ((subChart d hφ a₀).symm (φ y) : X) = φ y
  rw [subChart_symm_apply d hφ a₀ ⟨y, hy, rfl⟩, φ.symm_apply_apply (d.shrink_subset_source φ hy.1)]

/-- **The chart coordinate of `Ti`**: for the sub-chart `σ = subChart d hφ a₀` of `Y` built on
`φ`, `Tφ(x) ∘ Ti = Tσ(a)` on `T_aY`; both land in `E`. -/
theorem fiberCoord_subInclusionCLM (β : (subPolyfold hY).tangentFiber a) :
    fiberCoord hφ (levelVal_mem_source_of_subChart hY hax d hφ a₀ ha)
        (subInclusionCLM hY hax β) =
      fiberCoord (subPolyfold_isChart hY d hφ a₀) ha β := by
  have hσ := subPolyfold_isChart hY d hφ a₀
  have hβ : β.1 ∈ tangentChartSet (subChart d hφ a₀) := mem_tangentChartSet_of_mem_fiber ha β.2
  have hfβ : (((subPolyfold hY).levelVal 1 ((subPolyfold hY).tangentProj β.1)) : X) ∈
      φ.source := by
    rw [tangentProj_eq_of_mem_fiber β.2]
    exact d.shrink_subset_source φ ha
  rw [fiberCoord_apply, fiberCoord_apply, subInclusionCLM_apply,
    tangentChartMap_tangentMap (subPolyfold_inclusion_isScSmooth hY) hσ hφ hβ hfβ,
    subChart_image_fdom]
  have hO : IsScRetract (subChart d hφ a₀).model.E (subChart d hφ a₀).model.C
      (φ '' (d.shrink φ ∩ Y)) := d.isScRetract_image φ hφ
  exact congrArg Prod.snd
    (retractTangentMap_id hO (eqOn_subChart_symm d hφ a₀) (tangentChartMap_mem hσ hβ))

/-- **The chart image of `Ti(T_aY)`**: for a chart `φ` of `X` around `x` and any retraction datum
`d` of `Y` with `a` in the sub-chart built on `φ`, `Tφ(x)` maps `Ti(T_aY) ⊆ T_xX` onto the tangent
space at `φ(x)` of the chart image `φ(W ∩ Y)` of `Y` (`W = d.shrink φ`). -/
theorem coe_map_range_subInclusionCLM :
    ((subTangentRange hY hax).map
        (fiberCoord hφ (levelVal_mem_source_of_subChart hY hax d hφ a₀ ha)) : Set (φ.model.E 0)) =
      tangentSpace φ.model.E φ.model.C (φ '' (d.shrink φ ∩ Y))
        (levelLift φ 1 (P.levelVal 1 x)) := by
  have hσ := subPolyfold_isChart hY d hφ a₀
  have hlift : levelLift (subChart d hφ a₀) 1 ((subPolyfold hY).levelVal 1 a) =
      levelLift φ 1 (P.levelVal 1 x) := by
    rw [← hax]; rfl
  rw [← hlift]
  change _ = (tangentFiberModel hσ ha : Set ((subChart d hφ a₀).model.E 0))
  ext v
  simp only [SetLike.mem_coe, Submodule.mem_map, subTangentRange, LinearMap.mem_range]
  constructor
  · rintro ⟨_, ⟨β, rfl⟩, rfl⟩
    change fiberCoord hφ _ (subInclusionCLM hY hax β) ∈
      (tangentFiberModel hσ ha : Set ((subChart d hφ a₀).model.E 0))
    rw [fiberCoord_subInclusionCLM hY hax d hφ a₀ ha β, fiberCoord_eq_coe]
    exact (tangentFiberEquiv hσ ha β).2
  · intro hv
    refine ⟨_, ⟨(tangentFiberEquiv hσ ha).symm ⟨v, hv⟩, rfl⟩, ?_⟩
    change fiberCoord hφ _ (subInclusionCLM hY hax ((tangentFiberEquiv hσ ha).symm ⟨v, hv⟩)) = v
    rw [fiberCoord_subInclusionCLM hY hax d hφ a₀ ha, fiberCoord_eq_coe, Equiv.apply_symm_apply]

end SubChartTangent

/-! ### Linear algebra -/

section LinearAlgebra

variable {V E : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup E] [Module ℝ E]

/-- Pulling back a splitting of the range of an injective linear map. -/
lemma isCompl_comap_of_injective {f : V →ₗ[ℝ] E} (hf : Injective f) {N A : Submodule ℝ E}
    (hd : Disjoint N A) (hs : N ⊔ A = LinearMap.range f) : IsCompl (N.comap f) (A.comap f) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro v hvN hvA
    exact hf (by rw [map_zero]; exact (Submodule.disjoint_def.1 hd) _ hvN hvA)
  · rw [codisjoint_iff_le_sup]
    intro v _
    have hv : f v ∈ N ⊔ A := hs ▸ LinearMap.mem_range_self f v
    obtain ⟨n, hn, b, hb, hnb⟩ := Submodule.mem_sup.1 hv
    obtain ⟨v₁, rfl⟩ : n ∈ LinearMap.range f := hs ▸ Submodule.mem_sup_left hn
    obtain ⟨v₂, rfl⟩ : b ∈ LinearMap.range f := hs ▸ Submodule.mem_sup_right hb
    refine Submodule.mem_sup.2 ⟨v₁, hn, v₂, hb, hf ?_⟩
    rw [map_add, hnb]

end LinearAlgebra

lemma range_fiberCoord {φ : MChart X} (hφ : P.IsChart φ) {x : P.Level 1}
    (hx : P.levelVal 1 x ∈ φ.source) :
    LinearMap.range (fiberCoord hφ hx) = tangentFiberModel hφ hx := by
  rw [fiberCoord, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    Submodule.range_subtype]

lemma injective_fiberCoord {φ : MChart X} (hφ : P.IsChart φ) {x : P.Level 1}
    (hx : P.levelVal 1 x ∈ φ.source) : Injective (fiberCoord hφ hx) :=
  (tangentFiberModel hφ hx).injective_subtype.comp (LinearEquiv.injective _)

/-! ### Definition 2.5.19 (3) in `T_yX` -/

section Intrinsic

variable {Y : Set X} (hY : P.IsSubMPolyfold Y) [ParacompactSpace Y]

/-- **2021 Definition 2.5.19 (3), p. 63, in `T_yX`**: for `a ∈ Y₁` over `x ∈ X₁`, there is a
subspace `A` of `T_xX` with `T_xX = Ti(T_aY) ⊕ A` and `A ⊆ T^R_xX` (`reducedTangentFiber`), and
`A` is an sc-subspace and the splitting is an sc-splitting.  The sc-structure of `T_xX` at a smooth
point is the one carried by a chart `φ` (`isScSubspace_tangentFiberModel`; the same through every
chart, `transitionCLM_mem_range_toBase`), so the last two conditions are read through the chart
`φ` that also gives the presentation `T` of its partial quadrant defining `T^R_xX`
(chart-independent, `reducedTangentFiber_eq`). -/
def HasReducedScComplement {a : (subPolyfold hY).Level 1} {x : P.Level 1}
    (hax : ((subPolyfold hY).levelVal 1 a : Y).1 = P.levelVal 1 x) : Prop :=
  ∃ A : Submodule ℝ (P.tangentFiber x), IsCompl (subTangentRange hY hax) A ∧
    ∃ (φ : MChart X) (hφ : P.IsChart φ) (hx : P.levelVal 1 x ∈ φ.source) (n : ℕ) (W : ScBanach)
      (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
      φ.model.C = T 0 ⁻¹' quadrant n W 0 ∧ A ≤ reducedTangentFiber hφ hx T ∧
      φ.model.E.IsScSubspace (A.map (fiberCoord hφ hx)) ∧
      ∀ m, Disjoint (φ.model.E.levelSub ((subTangentRange hY hax).map (fiberCoord hφ hx)) m)
          (φ.model.E.levelSub (A.map (fiberCoord hφ hx)) m) ∧
        φ.model.E.levelSub ((subTangentRange hY hax).map (fiberCoord hφ hx)) m ⊔
            φ.model.E.levelSub (A.map (fiberCoord hφ hx)) m =
          φ.model.E.levelSub (tangentFiberModel hφ hx) m

/-- **(3) in `T_yX` is (3) in a chart**: for a retraction datum `d` of `Y` around `x`, the condition
in `T_xX` holds iff, in some chart `φ` around `x` with a presentation `T`, the chart image
`φ(W ∩ Y)` has a reduced sc-complement at `φ(x)` (the condition of `TameSubData`). -/
theorem hasReducedScComplement_iff (d : P.SubData Y) {a : (subPolyfold hY).Level 1}
    {x : P.Level 1} (hax : ((subPolyfold hY).levelVal 1 a : Y).1 = P.levelVal 1 x)
    (hxV : P.levelVal 1 x ∈ d.V) :
    HasReducedScComplement hY hax ↔
      ∃ (φ : MChart X) (n : ℕ) (W : ScBanach)
        (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)) (z : φ.model.E 1),
        P.IsChart φ ∧ P.levelVal 1 x ∈ φ.source ∧ φ.model.C = T 0 ⁻¹' quadrant n W 0 ∧
          φ.model.E.toBase 1 z = φ (P.levelVal 1 x) ∧
          HasReducedComplementAt φ.model.C φ.model.O (φ '' (d.shrink φ ∩ Y)) T z := by
  have ha : ∀ {φ : MChart X} (hφ : P.IsChart φ), P.levelVal 1 x ∈ φ.source →
      (subPolyfold hY).levelVal 1 a ∈ (subChart d hφ ((subPolyfold hY).levelVal 1 a)).source :=
    fun hφ hx => d.mem_shrink _ ((subPolyfold hY).levelVal 1 a).2 (hax ▸ hxV) (hax ▸ hx)
  constructor
  · rintro ⟨A, -, φ, hφ, hx, n, W, T, hT, hAR, hsc, hlev⟩
    have hz := P.toBase_levelLift hφ hx (levelVal_mem x)
    refine ⟨φ, n, W, T, levelLift φ 1 (P.levelVal 1 x), hφ, hx, hT, hz,
      (subTangentRange hY hax).map (fiberCoord hφ hx), tangentFiberModel hφ hx,
      A.map (fiberCoord hφ hx), coe_map_range_subInclusionCLM hY hax d hφ _ (ha hφ hx),
      coe_tangentFiberModel hφ hx, ?_, hsc, hlev⟩
    rw [hz]
    refine le_inf ?_ (Submodule.map_le_iff_le_comap.2 hAR)
    rw [← range_fiberCoord hφ hx]
    exact LinearMap.map_le_range
  · rintro ⟨φ, n, W, T, z, hφ, hx, hT, hz, N, M, A', hN, hM, hA', hsc, hlev⟩
    rw [hz] at hA'
    obtain rfl : z = levelLift φ 1 (P.levelVal 1 x) :=
      φ.model.E.toBase_injective 1 (by rw [hz, P.toBase_levelLift hφ hx (levelVal_mem x)])
    obtain rfl : M = tangentFiberModel hφ hx :=
      SetLike.coe_injective (hM.trans (coe_tangentFiberModel hφ hx).symm)
    obtain rfl : N = (subTangentRange hY hax).map (fiberCoord hφ hx) :=
      SetLike.coe_injective (hN.trans (coe_map_range_subInclusionCLM hY hax d hφ _ (ha hφ hx)).symm)
    have hinj := injective_fiberCoord hφ hx
    have hmap : (A'.comap (fiberCoord hφ hx)).map (fiberCoord hφ hx) = A' :=
      Submodule.map_comap_eq_self ((range_fiberCoord hφ hx).symm ▸ hA'.trans inf_le_left)
    refine ⟨A'.comap (fiberCoord hφ hx), ?_, φ, hφ, hx, n, W, T, hT,
      Submodule.comap_mono (hA'.trans inf_le_right), hmap.symm ▸ hsc, hmap.symm ▸ hlev⟩
    have h0 := hlev 0
    simp only [ScBanach.levelSub_zero] at h0
    have h := isCompl_comap_of_injective hinj h0.1 (h0.2.trans (range_fiberCoord hφ hx).symm)
    rwa [Submodule.comap_map_eq_of_injective hinj] at h

/-- A smooth point `y ∈ Y` lies on level `1` of `Y` and of `X`. -/
lemma exists_level_one_of_mem_smoothSet {y : X} (hyY : y ∈ Y) (hys : y ∈ P.smoothSet) :
    ∃ (a : (subPolyfold hY).Level 1) (x : P.Level 1)
      (_ : ((subPolyfold hY).levelVal 1 a : Y).1 = P.levelVal 1 x), P.levelVal 1 x = y := by
  have hy1 : y ∈ P.levelSet 1 := mem_iInter.1 hys 1
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  have hσy : (⟨y, hyY⟩ : Y) ∈ (subChart (hY.data hyY) hφ ⟨y, hyY⟩).source :=
    (hY.data hyY).mem_shrink φ hyY (hY.mem_data_V hyY) hyφ
  have ha1 : (⟨y, hyY⟩ : Y) ∈ (subPolyfold hY).levelSet 1 :=
    ((subPolyfold hY).mem_levelSet_iff (subPolyfold_isChart hY _ hφ _) hσy).2
      ((P.mem_levelSet_iff hφ hyφ).1 hy1)
  exact ⟨(subPolyfold hY).levelMk 1 _ ha1, P.levelMk 1 y hy1, by simp, by simp⟩

variable (Y) in
/-- **2021 Definition 2.5.19, p. 63** (new in the 2021 edition), the data at a point, with (3) in
`T_yX`: an open `V` and an sc-smooth retraction `r : V → V` with (1) `r(V) = Y ∩ V`,
(2) `d_X ∘ r = d_X` on `V`, (3) at every smooth `y ∈ Y ∩ V`, `T_yX = Ti(T_yY) ⊕ A` for an
sc-subspace `A ⊆ T^R_yX` (`HasReducedScComplement`, for the level-`1` points `a ∈ Y₁`, `x ∈ X₁`
over `y`). -/
structure TameSubData2021 extends P.SubData Y where
  degIndex_apply : ∀ x ∈ V, P.degIndex (r x) = P.degIndex x
  complement : ∀ (a : (subPolyfold hY).Level 1) (x : P.Level 1)
    (hax : ((subPolyfold hY).levelVal 1 a : Y).1 = P.levelVal 1 x),
    P.levelVal 1 x ∈ V → P.levelVal 1 x ∈ P.smoothSet → HasReducedScComplement hY hax

variable {hY} in
/-- The chart form of the data gives the form in `T_yX`. -/
def TameSubData.toTameSubData2021 (d : P.TameSubData Y) : TameSubData2021 Y hY where
  toSubData := d.toSubData
  degIndex_apply := d.degIndex_apply
  complement a x hax hxV hxs := by
    have hyY : P.levelVal 1 x ∈ Y := hax ▸ ((subPolyfold hY).levelVal 1 a).2
    exact (hasReducedScComplement_iff hY d.toSubData hax hxV).2 (d.complement _ ⟨hyY, hxV⟩ hxs)

variable {hY} in
/-- The form of the data in `T_yX` gives the chart form. -/
def TameSubData2021.toTameSubData (d : TameSubData2021 Y hY) : P.TameSubData Y where
  toSubData := d.toSubData
  degIndex_apply := d.degIndex_apply
  complement y hy hys := by
    obtain ⟨a, x, hax, rfl⟩ := exists_level_one_of_mem_smoothSet hY hy.1 hys
    exact (hasReducedScComplement_iff hY d.toSubData hax hy.2).1 (d.complement a x hax hy.2 hys)

end Intrinsic

/-- **2021 Definition 2.5.19, p. 63** (new in the 2021 edition), with (3) in `T_yX`: the
sub-M-polyfold `Y` of the tame M-polyfold `X` is a **tame sub-M-polyfold** if every `y ∈ Y` lies
in the domain of a `TameSubData2021`. -/
def IsTameSubMPolyfold2021 {Y : Set X} (hY : P.IsSubMPolyfold Y) : Prop :=
  letI := P.paracompactSpace_subtype Y
  P.IsTame ∧ ∀ y ∈ Y, ∃ d : TameSubData2021 Y hY, y ∈ d.V

/-- **2021 Definition 2.5.19 with (3) in `T_yX` is `IsTameSubMPolyfold`** (the form with (3) in a
chart, row V2.78). -/
theorem isTameSubMPolyfold2021_iff {Y : Set X} (hY : P.IsSubMPolyfold Y) :
    IsTameSubMPolyfold2021 hY ↔ P.IsTameSubMPolyfold Y := by
  have := P.paracompactSpace_subtype Y
  constructor
  · rintro ⟨hP, h⟩
    refine ⟨hP, fun y hy => ?_⟩
    obtain ⟨d, hd⟩ := h y hy
    exact ⟨d.toTameSubData, hd⟩
  · rintro ⟨hP, h⟩
    refine ⟨hP, fun y hy => ?_⟩
    obtain ⟨d, hd⟩ := h y hy
    exact ⟨d.toTameSubData2021, hd⟩

/-- **2021 Definitions 2.5.18 and 2.5.19, pp. 62–63** (new in the 2021 edition), in book form,
with (3) stated in `T_yX`: for a sub-M-polyfold `Y` of `X`,
(a) `Y` is a tame sub-M-polyfold in the sense of Definition 2.5.19 with (3) in `T_yX`
(`IsTameSubMPolyfold2021`) iff it is one with (3) in a chart (`IsTameSubMPolyfold`);
(b) then the structure induced on `Y` is tame (Definition 2.5.18; the remark after
Definition 2.5.19, `IsTameSubMPolyfold.hasTameInducedStructure`);
(c) for a tame `X`, `Y = X` is a tame sub-M-polyfold (`isTameSubMPolyfold_univ`). -/
theorem definition_2_5_19_book {Y : Set X} (hY : P.IsSubMPolyfold Y) :
    (IsTameSubMPolyfold2021 hY ↔ P.IsTameSubMPolyfold Y) ∧
      (IsTameSubMPolyfold2021 hY → P.HasTameInducedStructure Y) ∧
      (P.IsTame → IsTameSubMPolyfold2021 P.isSubMPolyfold_univ) :=
  ⟨isTameSubMPolyfold2021_iff hY,
    fun h => ((isTameSubMPolyfold2021_iff hY).1 h).hasTameInducedStructure,
    fun hP => (isTameSubMPolyfold2021_iff _).2 (P.isTameSubMPolyfold_univ hP)⟩

end MPolyfold

end Polyfold
