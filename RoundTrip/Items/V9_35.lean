import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_35

/-! Round trip for V9_35 (Lemma 9.3.7, p. 426 of the 2021 book: equal tangent spaces have equal
degeneracy).

`A` is the conjunction of the types of the four listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `subDegIndex_eq_quotDim_of_hasTameInducedStructure` (for a tame induced
structure, `d_M(y) = dim(T_yM / T_yM ∩ E_y)` in every chart), `subDegIndex_eq_of_tangentSpace_eq`
(the chart form of the lemma, with neither `Y` tame nor equal dimensions), `lemma_9_3_7` (the
text's hypotheses, tangent equality in one chart) and `subDegIndex_eq_of_submanifoldTangent_eq`
(the chart-free form, again without `Y` tame or equal dimensions).

* `A_to_B` applies the last conjunct: `B`'s `dMB` is the project's `subDegIndex` of the same
  sub-M-polyfold (proof irrelevance for the `IsSubMPolyfold` witness), `IsSubmanifoldOfDim`
  gives `IsSmoothSubmanifold`.  `B`'s tameness of `Y` and its common dimension `n` are not used.
* `B_to_A` cannot use `B`: every conjunct of `A` drops `B`'s hypotheses `P.IsTame` (and three of
  them the equal dimension), and two are chart formulas `B` does not state.  It re-proves the four
  statements outright, as copies of the project's proofs from unbanned lemmas
  (`degIndex_eq_quotDim_of_isTame`, `subPolyfold_isChart`, `chartVec_image_submanifoldTangent`,
  `tangentSpace_eq_coe_submodule`). -/

namespace RoundTrip.V9_35
open Polyfold Polyfold.MPolyfold Set Module Submodule

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.subDegIndex_eq_quotDim_of_hasTameInducedStructure.{0}) ∧
  (type_of% @Polyfold.MPolyfold.subDegIndex_eq_of_tangentSpace_eq.{0}) ∧
  (type_of% @Polyfold.MPolyfold.lemma_9_3_7.{0}) ∧
  (type_of% @Polyfold.MPolyfold.subDegIndex_eq_of_submanifoldTangent_eq.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.subDegIndex_eq_quotDim_of_hasTameInducedStructure.{0},
    @Polyfold.MPolyfold.subDegIndex_eq_of_tangentSpace_eq.{0},
    @Polyfold.MPolyfold.lemma_9_3_7.{0},
    @Polyfold.MPolyfold.subDegIndex_eq_of_submanifoldTangent_eq.{0}⟩

/-- `dMB` is the project's `subDegIndex` at points of a sub-M-polyfold. -/
theorem dMB_eq {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    {P : MPolyfold Z} {M : Set Z} (hM : P.IsSubMPolyfold M) {y : Z} (hy : y ∈ M) :
    dMB P M y = P.subDegIndex hM ⟨y, hy⟩ := by
  unfold dMB
  rw [dif_pos ⟨hM, hy⟩]

theorem A_to_B : A → B := by
  intro hA Z _ _ _ P _ M₁ M₂ n h₁ h₂ ht₁ ht₂ y hy heq
  rw [dMB_eq h₁.1.isSubMPolyfold hy.1, dMB_eq h₂.1.isSubMPolyfold hy.2]
  exact hA.2.2.2 h₁.1 h₂.1 ht₁ ht₂ hy.1 hy.2 heq

/-! ### `B → A`: the four statements re-proved outright (copies of the project's proofs) -/

section Copies
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

theorem quotDim_copy {A : Set X}
    (hA : P.IsSmoothSubmanifold A) (htame : P.HasTameInducedStructure A)
    (d : P.SubmanifoldData A) {φ : MChart X} (hφ : P.IsChart φ)
    (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ '' (d.toSubData.shrink φ ∩ A))
    {n : ℕ} {W : ScBanach} (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) {a : A} (haV : a.1 ∈ d.V)
    (haφ : a.1 ∈ φ.source) {z : φ.model.E 1} (hz : φ.model.E.toBase 1 z = φ a) :
    P.subDegIndex hA.isSubMPolyfold a =
      quotDim (LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0))
        (reducedTangentSpaceWith R T z) := by
  let := P.paracompactSpace_subtype A
  obtain ⟨_, hY⟩ := htame
  have hψ := subPolyfold_isChart hA.isSubMPolyfold d.toSubData hφ a
  have haψ : a ∈ (subChart d.toSubData hφ a).source := d.toSubData.mem_shrink φ a.2 haV haφ
  have hs : a ∈ (subPolyfold hA.isSubMPolyfold).smoothSet := hA.proposition_4_15_1.2 a
  exact (subPolyfold hA.isSubMPolyfold).degIndex_eq_quotDim_of_isTame hY hψ R hR T hT haψ hs hz

theorem tangentSpace_eq_copy {A₁ A₂ : Set X} (hA₁ : P.IsSmoothSubmanifold A₁)
    (hA₂ : P.IsSmoothSubmanifold A₂) (ht₁ : P.HasTameInducedStructure A₁)
    (ht₂ : P.HasTameInducedStructure A₂) {y : X} (hy₁ : y ∈ A₁) (hy₂ : y ∈ A₂)
    (d₁ : P.SubmanifoldData A₁) (d₂ : P.SubmanifoldData A₂) {φ : MChart X} (hφ : P.IsChart φ)
    (hyV₁ : y ∈ d₁.V) (hyV₂ : y ∈ d₂.V) (hyφ : y ∈ φ.source) {z : φ.model.E 1}
    (hz : φ.model.E.toBase 1 z = φ y)
    (heq : tangentSpace φ.model.E φ.model.C (φ '' (d₁.toSubData.shrink φ ∩ A₁)) z =
      tangentSpace φ.model.E φ.model.C (φ '' (d₂.toSubData.shrink φ ∩ A₂)) z) :
    P.subDegIndex hA₁.isSubMPolyfold ⟨y, hy₁⟩ = P.subDegIndex hA₂.isSubMPolyfold ⟨y, hy₂⟩ := by
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  obtain ⟨R₁, hR₁⟩ := d₁.toSubData.isScRetract_image φ hφ
  obtain ⟨R₂, hR₂⟩ := d₂.toSubData.isScRetract_image φ hφ
  have hz₁ : z ∈ φ.model.E.lvlSet R₁.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, hR₁]
    exact mem_image_of_mem φ ⟨d₁.toSubData.mem_shrink φ hy₁ hyV₁ hyφ, hy₁⟩
  have hz₂ : z ∈ φ.model.E.lvlSet R₂.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, hR₂]
    exact mem_image_of_mem φ ⟨d₂.toSubData.mem_shrink φ hy₂ hyV₂ hyφ, hy₂⟩
  have hrange : LinearMap.range (scDeriv R₁.U R₁ z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) =
      LinearMap.range (scDeriv R₂.U R₂ z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) := by
    apply SetLike.coe_injective
    rw [← tangentSpace_eq_coe_submodule R₁ hz₁, ← tangentSpace_eq_coe_submodule R₂ hz₂, hR₁, hR₂]
    exact heq
  rw [quotDim_copy hA₁ ht₁ d₁ hφ R₁ hR₁ T hT (a := ⟨y, hy₁⟩) hyV₁ hyφ hz,
    quotDim_copy hA₂ ht₂ d₂ hφ R₂ hR₂ T hT (a := ⟨y, hy₂⟩) hyV₂ hyφ hz]
  unfold reducedTangentSpaceWith
  rw [hrange]

theorem submanifoldTangent_eq_copy {A₁ A₂ : Set X} (hA₁ : P.IsSmoothSubmanifold A₁)
    (hA₂ : P.IsSmoothSubmanifold A₂) (ht₁ : P.HasTameInducedStructure A₁)
    (ht₂ : P.HasTameInducedStructure A₂) {y : X} (hy₁ : y ∈ A₁) (hy₂ : y ∈ A₂)
    (h : P.submanifoldTangent A₁ y = P.submanifoldTangent A₂ y) :
    P.subDegIndex hA₁.isSubMPolyfold ⟨y, hy₁⟩ = P.subDegIndex hA₂.isSubMPolyfold ⟨y, hy₂⟩ := by
  obtain ⟨φ, hφm, hyφ⟩ := P.atlas.cover y
  have hφ := P.isChart_of_mem hφm
  have hyV₁ := hA₁.mem_data_V hy₁
  have hyV₂ := hA₂.mem_data_V hy₂
  have hy1 : y ∈ P.levelSet 1 := (hA₁.data hy₁).mem_levelSet_one hy₁ hyV₁
  have hz := P.toBase_levelLift hφ hyφ hy1
  refine tangentSpace_eq_copy hA₁ hA₂ ht₁ ht₂ hy₁ hy₂ (hA₁.data hy₁) (hA₂.data hy₂)
    hφ hyV₁ hyV₂ hyφ hz ?_
  rw [← chartVec_image_submanifoldTangent hφ (hA₁.data hy₁) hy₁ hyV₁ hyφ,
    ← chartVec_image_submanifoldTangent hφ (hA₂.data hy₂) hy₂ hyV₂ hyφ, h]

theorem lemma_9_3_7_copy (_hP : P.IsTame) {A₁ A₂ : Set X} {k : ℕ}
    (hA₁ : P.IsSubmanifoldOfDim A₁ k)
    (hA₂ : P.IsSubmanifoldOfDim A₂ k) (ht₁ : P.HasTameInducedStructure A₁)
    (ht₂ : P.HasTameInducedStructure A₂) {y : X} (hy₁ : y ∈ A₁) (hy₂ : y ∈ A₂)
    (d₁ : P.SubmanifoldData A₁) (d₂ : P.SubmanifoldData A₂) {φ : MChart X} (hφ : P.IsChart φ)
    (hyV₁ : y ∈ d₁.V) (hyV₂ : y ∈ d₂.V) (hyφ : y ∈ φ.source) {z : φ.model.E 1}
    (hz : φ.model.E.toBase 1 z = φ y)
    (heq : tangentSpace φ.model.E φ.model.C (φ '' (d₁.toSubData.shrink φ ∩ A₁)) z =
      tangentSpace φ.model.E φ.model.C (φ '' (d₂.toSubData.shrink φ ∩ A₂)) z) :
    P.subDegIndex hA₁.1.isSubMPolyfold ⟨y, hy₁⟩ = P.subDegIndex hA₂.1.isSubMPolyfold ⟨y, hy₂⟩ :=
  tangentSpace_eq_copy hA₁.1 hA₂.1 ht₁ ht₂ hy₁ hy₂ d₁ d₂ hφ hyV₁ hyV₂ hyφ hz heq

end Copies

/-- `B → A`, by re-proving `A` outright: `A` has no use for `B`, whose hypotheses (`Y` tame, equal
dimensions) its conjuncts do not have. -/
theorem B_to_A : B → A := fun _ =>
  ⟨@quotDim_copy, @tangentSpace_eq_copy, @lemma_9_3_7_copy, @submanifoldTangent_eq_copy⟩

#rt_check RoundTrip.V9_35.A_to_B [Polyfold.MPolyfold.subDegIndex_eq_quotDim_of_hasTameInducedStructure,
  Polyfold.MPolyfold.subDegIndex_eq_of_tangentSpace_eq, Polyfold.MPolyfold.lemma_9_3_7,
  Polyfold.MPolyfold.subDegIndex_eq_of_submanifoldTangent_eq]
#rt_check RoundTrip.V9_35.B_to_A [Polyfold.MPolyfold.subDegIndex_eq_quotDim_of_hasTameInducedStructure,
  Polyfold.MPolyfold.subDegIndex_eq_of_tangentSpace_eq, Polyfold.MPolyfold.lemma_9_3_7,
  Polyfold.MPolyfold.subDegIndex_eq_of_submanifoldTangent_eq]
#rt_overlap RoundTrip.V9_35.B_to_A [Polyfold.MPolyfold.subDegIndex_eq_quotDim_of_hasTameInducedStructure,
  Polyfold.MPolyfold.subDegIndex_eq_of_tangentSpace_eq, Polyfold.MPolyfold.lemma_9_3_7,
  Polyfold.MPolyfold.subDegIndex_eq_of_submanifoldTangent_eq]

end RoundTrip.V9_35
