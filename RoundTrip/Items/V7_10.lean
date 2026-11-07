import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_10

/-! Round trip for V7_10 (the remark after Definition 7.7, pp. 228–229: sc-smoothness on objects
suffices).

`A` is the conjunction of the types of the five listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `EpGroupoid.mor_eq_srcInv_obj_src` (the text's formula),
`EpGroupoid.isScSmoothMap_mor_of_continuous` (the remark *with continuity on morphisms*),
`EpGroupoid.isScSmoothMap_mor_iff_continuous`, `EpFunctor.continuous_mor`, and
`EpGroupoid.Examples.remark_definition_7_7_counterexample` (no universe parameters: on
`ℤ/3 × ℝ ⇉ ℝ` there is a functor sc-smooth on objects that is neither continuous nor sc-smooth
on morphisms).  The listed `EpFunctor.ofContinuous` is a definition (vocabulary).

* `B` (literal: sc-smoothness on objects alone gives sc-smoothness on morphisms) is **false**:
  `not_B`, with the project's functor `remarkFunctor` (identity on objects, `(g, y) ↦ (g², y)`
  for `y > 0`).  Hence `A → B` is false (`not_A_to_B`) and `B → A` holds only ex falso.
* `BRepaired` is `B` with the hypothesis `Continuous f₁` added (as the blind author suggests:
  "with `f₁` continuous the text's argument goes through").  `A_to_BRepaired` and
  `BRepaired_to_A` are both proved; in `BRepaired_to_A` the formula, `continuous_mor`, the
  forward half of the iff and the counterexample are re-proved outright (they are not
  consequences of `BRepaired`), while `isScSmoothMap_mor_of_continuous` and the backward half of
  the iff come from `BRepaired`. -/

namespace RoundTrip.V7_10
open Polyfold Set Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.mor_eq_srcInv_obj_src.{0, 0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScSmoothMap_mor_of_continuous.{0, 0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScSmoothMap_mor_iff_continuous.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.continuous_mor.{0, 0}) ∧
  (type_of% @Polyfold.EpGroupoid.Examples.remark_definition_7_7_counterexample)

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.mor_eq_srcInv_obj_src.{0, 0},
    @Polyfold.EpGroupoid.isScSmoothMap_mor_of_continuous.{0, 0},
    @Polyfold.EpGroupoid.isScSmoothMap_mor_iff_continuous.{0, 0},
    @Polyfold.EpFunctor.continuous_mor.{0, 0},
    @Polyfold.EpGroupoid.Examples.remark_definition_7_7_counterexample⟩

/-! ### `B` is false -/

open Polyfold.EpGroupoid.Examples in
theorem not_B : ¬ B := by
  intro hB
  have h := hB _ _ _ _ trivialZ3EpGroupoid trivialZ3EpGroupoid remarkFunctor.obj
    remarkFunctor.mor ⟨remarkFunctor.src_mor, remarkFunctor.tgt_mor, remarkFunctor.mor_comp,
      remarkFunctor.mor_unit⟩ isScSmoothMap_remarkFunctor_obj
  exact not_isScSmoothMap_remarkFunctor_mor h.1

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B → A` only ex falso. -/
theorem B_to_A : B → A := fun h => absurd h not_B

/-! ### The repaired statement: `B` with continuity of `f₁` -/

/-- `B` with the hypothesis `Continuous f₁` added. -/
def BRepaired : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type)
    [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (f₀ : Obj → Obj') (f₁ : Mor → Mor'),
    IsFunctorB X.toGroupoidStr Y.toGroupoidStr f₀ f₁ → X.PObj.IsScSmoothMap Y.PObj f₀ →
    Continuous f₁ →
      X.PMor.IsScSmoothMap Y.PMor f₁ ∧
      (∀ φ : Mor, ∃ (Uφ : Set Mor) (Uψ : Set Mor') (Usφ : Set Obj) (Usψ : Set Obj')
          (σ : Obj → Mor) (σ' : Obj' → Mor'),
        IsOpen Uφ ∧ IsOpen Uψ ∧ IsOpen Usφ ∧ IsOpen Usψ ∧ φ ∈ Uφ ∧ f₁ φ ∈ Uψ ∧
        X.PMor.IsScDiffeoOn X.PObj X.src σ Uφ Usφ ∧
        Y.PMor.IsScDiffeoOn Y.PObj Y.src σ' Uψ Usψ ∧
        Set.MapsTo f₀ Usφ Usψ ∧ Set.MapsTo f₁ Uφ Uψ ∧
        ∀ γ ∈ Uφ, f₁ γ = σ' (f₀ (X.src γ)))

theorem A_to_BRepaired : A → BRepaired := by
  intro hA Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y f₀ f₁ hF hobj hcont
  obtain ⟨h1, h2, h3, h4⟩ := hF
  let F : GroupoidFunctor X.toGroupoidStr Y.toGroupoidStr := ⟨f₀, f₁, h1, h2, h3, h4⟩
  refine ⟨hA.2.1 (F := F) hobj hcont, fun φ => ?_⟩
  obtain ⟨W, V, σ', hψ, hd⟩ := Y.isLocalScDiffeo_src (f₁ φ)
  obtain ⟨W₀, V₀, σ, hφ, hd₀⟩ := X.isLocalScDiffeo_src φ
  have hUo : IsOpen (W₀ ∩ f₁ ⁻¹' W) := hd₀.isOpen_source.inter (hd.isOpen_source.preimage hcont)
  have hd₀r := hd₀.restrict hUo inter_subset_left
  refine ⟨W₀ ∩ f₁ ⁻¹' W, W, V₀ ∩ σ ⁻¹' (W₀ ∩ f₁ ⁻¹' W), V, σ, σ', hUo, hd.isOpen_source,
    hd₀r.isOpen_target, hd.isOpen_target, ⟨hφ, hψ⟩, hψ, hd₀r, hd, fun x hx => ?_,
    fun γ hγ => hγ.2, fun γ hγ => ?_⟩
  · rw [← hd₀r.right_inv x hx, ← h1]
    exact hd.mapsTo (hd₀r.mapsTo_inv hx).2
  · rw [← h1 γ, hd.left_inv _ hγ.2]

open Polyfold.EpGroupoid.Examples in
theorem BRepaired_to_A : BRepaired → A := by
  intro hR
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F σ W V hd γ hγ
    rw [← F.src_mor, hd.left_inv _ hγ]
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hobj hmor
    exact (hR Obj Mor Obj' Mor' X Y F.obj F.mor
      ⟨F.src_mor, F.tgt_mor, F.mor_comp, F.mor_unit⟩ hobj hmor).1
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hobj
    exact ⟨fun h => continuousOn_univ.1 h.continuousOn, fun hmor => (hR Obj Mor Obj' Mor' X Y
      F.obj F.mor ⟨F.src_mor, F.tgt_mor, F.mor_comp, F.mor_unit⟩ hobj hmor).1⟩
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F
    exact continuousOn_univ.1 F.isScSmoothMap_mor.continuousOn
  · refine ⟨remarkFunctor, isScSmoothMap_remarkFunctor_obj, not_continuous_remarkFunctor_mor,
      not_isScSmoothMap_remarkFunctor_mor, ?_⟩
    rintro ⟨E, hE⟩
    have h := continuousOn_univ.1 E.isScSmoothMap_mor.continuousOn
    rw [show E.mor = remarkFunctor.mor from congrArg GroupoidFunctor.mor hE] at h
    exact not_continuous_remarkFunctor_mor h

#rt_check RoundTrip.V7_10.not_B [Polyfold.EpGroupoid.mor_eq_srcInv_obj_src,
  Polyfold.EpGroupoid.isScSmoothMap_mor_of_continuous,
  Polyfold.EpGroupoid.isScSmoothMap_mor_iff_continuous, Polyfold.EpFunctor.continuous_mor,
  Polyfold.EpGroupoid.Examples.remark_definition_7_7_counterexample]
#rt_check RoundTrip.V7_10.B_to_A [Polyfold.EpGroupoid.mor_eq_srcInv_obj_src,
  Polyfold.EpGroupoid.isScSmoothMap_mor_of_continuous,
  Polyfold.EpGroupoid.isScSmoothMap_mor_iff_continuous, Polyfold.EpFunctor.continuous_mor,
  Polyfold.EpGroupoid.Examples.remark_definition_7_7_counterexample]
#rt_check RoundTrip.V7_10.A_to_BRepaired [Polyfold.EpGroupoid.mor_eq_srcInv_obj_src,
  Polyfold.EpGroupoid.isScSmoothMap_mor_of_continuous,
  Polyfold.EpGroupoid.isScSmoothMap_mor_iff_continuous, Polyfold.EpFunctor.continuous_mor,
  Polyfold.EpGroupoid.Examples.remark_definition_7_7_counterexample]
#rt_check RoundTrip.V7_10.BRepaired_to_A [Polyfold.EpGroupoid.mor_eq_srcInv_obj_src,
  Polyfold.EpGroupoid.isScSmoothMap_mor_of_continuous,
  Polyfold.EpGroupoid.isScSmoothMap_mor_iff_continuous, Polyfold.EpFunctor.continuous_mor,
  Polyfold.EpGroupoid.Examples.remark_definition_7_7_counterexample]
#rt_overlap RoundTrip.V7_10.B_to_A [Polyfold.EpGroupoid.mor_eq_srcInv_obj_src,
  Polyfold.EpGroupoid.isScSmoothMap_mor_of_continuous,
  Polyfold.EpGroupoid.isScSmoothMap_mor_iff_continuous, Polyfold.EpFunctor.continuous_mor,
  Polyfold.EpGroupoid.Examples.remark_definition_7_7_counterexample]
#rt_overlap RoundTrip.V7_10.BRepaired_to_A [Polyfold.EpGroupoid.mor_eq_srcInv_obj_src,
  Polyfold.EpGroupoid.isScSmoothMap_mor_of_continuous,
  Polyfold.EpGroupoid.isScSmoothMap_mor_iff_continuous, Polyfold.EpFunctor.continuous_mor,
  Polyfold.EpGroupoid.Examples.remark_definition_7_7_counterexample]

end RoundTrip.V7_10
