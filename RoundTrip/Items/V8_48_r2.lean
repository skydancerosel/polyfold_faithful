import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_48

set_option maxSynthPendingDepth 3

/-! Round trip for V8_48_r2 (refresh of V8_48: 2021 Definition 8.4.2 and Proposition 8.4.3,
p. 382).  `B` is the existing blind statement `RoundTrip.V8_48.B`.

* `A`: the conjunction of the types of the 18 theorems of the decls list (universe `0`); the
  definitions `natLift`, `IsLR`, `IsLRLocal`, `IsLRGerm`, `HasLocalIsoExtension`,
  `StrongPolyfoldBundleStructure` are vocabulary.
* Glue (proved, no item theorem used): the blind notion `IsLRB` is exactly the project's
  `IsLRLocal` (`isLRB_iff_isLRLocal`: `IsSBIsoOnB ↔ StrongBundle.IsLocalIsoOn`, `IsoW ↔` equality
  of orbits); hence `IsLRB → IsLR` (`isLR_of_isLRB`).
* Main conjunct `proposition_8_4_3_isLRLocal`: `B_to_Amain` proved; from `A` one gets clause (ii)
  of `B` only under the project's standing instance `[ParacompactSpace (pullbackSpace P X.src)]`
  (`A_to_B_ii_of_inst`), which `B` does not assume.
* `A_to_B` not proved: clause (i) of `B` says `IsLR ↔ IsLRB` for every strong bundle; its `→`
  direction (`IsLR → IsLRLocal`: extend a strong bundle isomorphism of `W|U(x)` to a strong bundle
  map of `W`) is not in `A` (`A` has only the germ form `IsLR.isLRGerm` under
  `HasLocalIsoExtension`).
* `B_to_A` not proved: `A` also contains Chapter 10/12 consequences (`proposition_10_4_7_of_isLRGerm`,
  the orientation transport theorems), examples and helper lemmas which `B` does not mention. -/

namespace RoundTrip.V8_48_r2
open Polyfold

abbrev B : Prop := RoundTrip.V8_48.B

section glue
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {Bd : StrongBundle X.PObj P}

theorem isoW_iff (E : EpStrongBundle X Bd) (w w' : W) :
    RoundTrip.V8_48.IsoW E w w' ↔ E.toGroupoidStr.π w' = E.toGroupoidStr.π w := by
  constructor
  · rintro ⟨φ, h, hμ⟩
    exact ((E.toGroupoidStr.π_eq_π_iff (x := w) (y := w')).2 ⟨⟨(φ, w), h⟩, rfl, hμ⟩).symm
  · intro h
    obtain ⟨q, hqs, hqt⟩ := (GroupoidStr.π_eq_π_iff _).1 h.symm
    obtain ⟨⟨ψ, w''⟩, hq⟩ := q
    have hqs' : w'' = w := hqs
    subst hqs'
    exact ⟨ψ, hq, hqt⟩

theorem isSBIsoOnB_iff (U : Set Obj) (β : Obj → Obj) (Φ : W → W) :
    RoundTrip.V8_48.IsSBIsoOnB Bd U β Φ ↔ Bd.IsLocalIsoOn β Φ U := by
  constructor
  · rintro ⟨hβ, hcov, hlin, h0, hone, Ψ₁, h1⟩
    refine ⟨fun x hx => ⟨IsLinearMap.mk' _ (hlin x hx), fun v => rfl⟩, hβ, h0, ⟨RoundTrip.V8_48.oneMapB Bd hone, Ψ₁,
      fun y hy => ?_, h1⟩⟩
    simp only [RoundTrip.V8_48.oneMapB, hy, dif_pos, StrongBundle.oneVal_oneMk]
  · rintro ⟨hlin, hβ, h0, Φ₁, Ψ₁, hagree, h1⟩
    have hcov : ∀ w, P w ∈ U → P (Φ w) = β (P w) := fun w hw => by
      obtain ⟨L, hL⟩ := hlin (P w) hw
      rw [← hL ⟨w, rfl⟩]
      exact (L ⟨w, rfl⟩).2
    refine ⟨hβ, hcov, fun x hx => ?_, h0, ?_⟩
    · obtain ⟨L, hL⟩ := hlin x hx
      have : RoundTrip.V8_48.fibreMapB hcov x hx = fun v => L v := by
        funext v; exact Subtype.ext (hL v).symm
      rw [this]
      exact L.isLinear
    · have hone : ∀ w : Bd.One, P (Bd.oneVal w) ∈ U → Φ (Bd.oneVal w) ∈ Bd.oneSet :=
        fun w hw => hagree w hw ▸ Bd.oneVal_mem (Φ₁ w)
      refine ⟨hone, Ψ₁, h1.congr_left fun y hy => ?_⟩
      have hy' : P (Bd.oneVal y) ∈ U := hy
      apply Bd.oneVal_injective
      simp only [RoundTrip.V8_48.oneMapB, hy', dif_pos, StrongBundle.oneVal_oneMk]
      exact hagree y hy'

/-- The blind notion is the project's `IsLRLocal`. -/
theorem isLRB_iff_isLRLocal (E : EpStrongBundle X Bd) :
    RoundTrip.V8_48.IsLRB E ↔ E.IsLRLocal := by
  constructor
  · intro h x O hO hxO
    obtain ⟨R, hRO, hR⟩ := h x O hO hxO
    exact ⟨R, hRO, fun β Φ hΦ hπ => hR β Φ ((isSBIsoOnB_iff _ _ _).2 hΦ)
      (fun w hw => (isoW_iff E _ _).2 (hπ w hw))⟩
  · intro h x O hO hxO
    obtain ⟨R, hRO, hR⟩ := h x O hO hxO
    exact ⟨R, hRO, fun β Φ hΦ hπ => hR β Φ ((isSBIsoOnB_iff _ _ _).1 hΦ)
      (fun w hw => (isoW_iff E _ _).1 (hπ w hw))⟩

/-- One direction of B's clause (i) holds outright: the blind (printed) notion implies the
project's `IsLR` (which quantifies only over strong bundle maps defined on all of `W`). -/
theorem isLR_of_isLRB (E : EpStrongBundle X Bd) (h : RoundTrip.V8_48.IsLRB E) : E.IsLR :=
  fun x O hO hxO =>
    let ⟨R, hRO, hR⟩ := (isLRB_iff_isLRLocal E).1 h x O hO hxO
    ⟨R, hRO, fun β Φ _ hi hπ => hR β Φ hi.isLocalIsoOn hπ⟩
end glue

/-- The project's statement: the conjunction of the types of the item's theorems (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.isLR_trivial.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.proposition_8_4_3.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.eq_of_isRegular_src.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.exists_mor_of_π_eq.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.IsLRLocal.isLR.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isLRLocal_trivial.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.IsLR.isLRGerm.{0}) ∧
  (type_of% @Polyfold.StrongBundle.isStrongBundleMap_cutOff.{0}) ∧
  (type_of% @Polyfold.MPolyfold.AdmitsBumpFunctions.hasLocalIsoExtension.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.IsLR.isLRGerm_of_admitsBumpFunctions.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.proposition_10_4_7_of_isLRGerm.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLR.{0}) ∧
  (type_of% @Polyfold.HalfSpaceBundle.isLRGerm_of_admitsBumpFunctions_halfSEP) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.isLRGerm_of_admitsBumpFunctions_z3SEP) ∧
  (type_of% @Polyfold.EpStrongBundle.proposition_8_4_3_isLRLocal.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.exists_mor_of_π_eq_of_isLocalIsoOn.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundleStructure.isLR.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLRLocal.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.isLR_trivial.{0},
   @Polyfold.EpStrongBundle.proposition_8_4_3.{0},
   @Polyfold.EpGroupoid.eq_of_isRegular_src.{0},
   @Polyfold.EpStrongBundle.exists_mor_of_π_eq.{0},
   @Polyfold.EpStrongBundle.IsLRLocal.isLR.{0},
   @Polyfold.EpStrongBundle.isLRLocal_trivial.{0},
   @Polyfold.EpStrongBundle.IsLR.isLRGerm.{0},
   @Polyfold.StrongBundle.isStrongBundleMap_cutOff.{0},
   @Polyfold.MPolyfold.AdmitsBumpFunctions.hasLocalIsoExtension.{0},
   @Polyfold.EpStrongBundle.IsLR.isLRGerm_of_admitsBumpFunctions.{0},
   @Polyfold.EpStrongBundle.proposition_10_4_7_of_isLRGerm.{0},
   @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLR.{0},
   @Polyfold.HalfSpaceBundle.isLRGerm_of_admitsBumpFunctions_halfSEP,
   @Polyfold.StrongBundleLocalizationExamples.isLRGerm_of_admitsBumpFunctions_z3SEP,
   @Polyfold.EpStrongBundle.proposition_8_4_3_isLRLocal.{0},
   @Polyfold.EpStrongBundle.exists_mor_of_π_eq_of_isLocalIsoOn.{0},
   @Polyfold.StrongPolyfoldBundleStructure.isLR.{0},
   @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLRLocal.{0}⟩

/-- The main conjunct: Proposition 8.4.3 with Definition 8.4.2 as printed (`IsLRLocal`). -/
abbrev Amain : Prop := type_of% @Polyfold.EpStrongBundle.proposition_8_4_3_isLRLocal.{0}

/-- `B` gives the main conjunct (A's extra instance hypothesis is simply not used). -/
theorem B_to_Amain : B → Amain := by
  intro hB Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ Bd _ E hX hLR
  exact (isLRB_iff_isLRLocal E).1 (hB.2 Obj Mor X W P Bd E hX hLR)

/-- From `A` (indeed from the main conjunct alone), clause (ii) of `B` under the project's
standing instance `[ParacompactSpace (pullbackSpace P X.src)]`, which `B` does not have. -/
theorem A_to_B_ii_of_inst (hA : A) :
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (Bd : StrongBundle X.PObj P)
      [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X Bd),
      X.IsEffective → X.IsLR → RoundTrip.V8_48.IsLRB E := by
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ Bd _ E hX hLR
  exact (isLRB_iff_isLRLocal E).2 (hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 E hX hLR)

#rt_check RoundTrip.V8_48_r2.B_to_Amain [Polyfold.EpStrongBundle.isLR_trivial, Polyfold.EpStrongBundle.proposition_8_4_3, Polyfold.EpGroupoid.eq_of_isRegular_src, Polyfold.EpStrongBundle.exists_mor_of_π_eq, Polyfold.EpStrongBundle.IsLRLocal.isLR, Polyfold.EpStrongBundle.isLRLocal_trivial, Polyfold.EpStrongBundle.IsLR.isLRGerm, Polyfold.StrongBundle.isStrongBundleMap_cutOff, Polyfold.MPolyfold.AdmitsBumpFunctions.hasLocalIsoExtension, Polyfold.EpStrongBundle.IsLR.isLRGerm_of_admitsBumpFunctions, Polyfold.EpStrongBundle.proposition_10_4_7_of_isLRGerm, Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLR, Polyfold.HalfSpaceBundle.isLRGerm_of_admitsBumpFunctions_halfSEP, Polyfold.StrongBundleLocalizationExamples.isLRGerm_of_admitsBumpFunctions_z3SEP, Polyfold.EpStrongBundle.proposition_8_4_3_isLRLocal, Polyfold.EpStrongBundle.exists_mor_of_π_eq_of_isLocalIsoOn, Polyfold.StrongPolyfoldBundleStructure.isLR, Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLRLocal]
#rt_check RoundTrip.V8_48_r2.A_to_B_ii_of_inst [Polyfold.EpStrongBundle.isLR_trivial, Polyfold.EpStrongBundle.proposition_8_4_3, Polyfold.EpGroupoid.eq_of_isRegular_src, Polyfold.EpStrongBundle.exists_mor_of_π_eq, Polyfold.EpStrongBundle.IsLRLocal.isLR, Polyfold.EpStrongBundle.isLRLocal_trivial, Polyfold.EpStrongBundle.IsLR.isLRGerm, Polyfold.StrongBundle.isStrongBundleMap_cutOff, Polyfold.MPolyfold.AdmitsBumpFunctions.hasLocalIsoExtension, Polyfold.EpStrongBundle.IsLR.isLRGerm_of_admitsBumpFunctions, Polyfold.EpStrongBundle.proposition_10_4_7_of_isLRGerm, Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLR, Polyfold.HalfSpaceBundle.isLRGerm_of_admitsBumpFunctions_halfSEP, Polyfold.StrongBundleLocalizationExamples.isLRGerm_of_admitsBumpFunctions_z3SEP, Polyfold.EpStrongBundle.proposition_8_4_3_isLRLocal, Polyfold.EpStrongBundle.exists_mor_of_π_eq_of_isLocalIsoOn, Polyfold.StrongPolyfoldBundleStructure.isLR, Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLRLocal]
#rt_check RoundTrip.V8_48_r2.isLR_of_isLRB [Polyfold.EpStrongBundle.isLR_trivial, Polyfold.EpStrongBundle.proposition_8_4_3, Polyfold.EpGroupoid.eq_of_isRegular_src, Polyfold.EpStrongBundle.exists_mor_of_π_eq, Polyfold.EpStrongBundle.IsLRLocal.isLR, Polyfold.EpStrongBundle.isLRLocal_trivial, Polyfold.EpStrongBundle.IsLR.isLRGerm, Polyfold.StrongBundle.isStrongBundleMap_cutOff, Polyfold.MPolyfold.AdmitsBumpFunctions.hasLocalIsoExtension, Polyfold.EpStrongBundle.IsLR.isLRGerm_of_admitsBumpFunctions, Polyfold.EpStrongBundle.proposition_10_4_7_of_isLRGerm, Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLR, Polyfold.HalfSpaceBundle.isLRGerm_of_admitsBumpFunctions_halfSEP, Polyfold.StrongBundleLocalizationExamples.isLRGerm_of_admitsBumpFunctions_z3SEP, Polyfold.EpStrongBundle.proposition_8_4_3_isLRLocal, Polyfold.EpStrongBundle.exists_mor_of_π_eq_of_isLocalIsoOn, Polyfold.StrongPolyfoldBundleStructure.isLR, Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLRLocal]
#rt_overlap RoundTrip.V8_48_r2.B_to_Amain [Polyfold.EpStrongBundle.isLR_trivial, Polyfold.EpStrongBundle.proposition_8_4_3, Polyfold.EpGroupoid.eq_of_isRegular_src, Polyfold.EpStrongBundle.exists_mor_of_π_eq, Polyfold.EpStrongBundle.IsLRLocal.isLR, Polyfold.EpStrongBundle.isLRLocal_trivial, Polyfold.EpStrongBundle.IsLR.isLRGerm, Polyfold.StrongBundle.isStrongBundleMap_cutOff, Polyfold.MPolyfold.AdmitsBumpFunctions.hasLocalIsoExtension, Polyfold.EpStrongBundle.IsLR.isLRGerm_of_admitsBumpFunctions, Polyfold.EpStrongBundle.proposition_10_4_7_of_isLRGerm, Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLR, Polyfold.HalfSpaceBundle.isLRGerm_of_admitsBumpFunctions_halfSEP, Polyfold.StrongBundleLocalizationExamples.isLRGerm_of_admitsBumpFunctions_z3SEP, Polyfold.EpStrongBundle.proposition_8_4_3_isLRLocal, Polyfold.EpStrongBundle.exists_mor_of_π_eq_of_isLocalIsoOn, Polyfold.StrongPolyfoldBundleStructure.isLR, Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLRLocal]

end RoundTrip.V8_48_r2
