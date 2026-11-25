import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_142

set_option maxSynthPendingDepth 3

/-! Round trip for V17_142 (2021 Proposition 17.8.16, pp. 839–840; 2017: Proposition 17.13:
pull-backs of branched ep⁺-subcategories along proper polyfold covering functors).

`A` is the conjunction of the types of the item's eighteen theorems (the four definitions
`IsBranchedBase`, `IsBranchedHat`, `IsTameBase`, `IsTameHat` are vocabulary), all instantiated at
universe `0` (`paracompactSpace_of_isProperMap.{0,0}`), since `B` lives in `GCT.{0}`.

* `not_B`: `B` does not hold as written.  Its compactness clause (4) has no hypothesis that the
  construction `F` has a uniformizer at the points of `supp Θ` (the project's `unif_hyp` in
  `proposition_17_8_16_four`; the text: "we take a proper covering uniformizer around `β`").  A
  `ProperPolyfoldCoveringStructure` may have `F(β) = ∅` for every `β` (nothing in Definition
  17.1.8 / 17.8.13 as formalized asks `F(β) ≠ ∅`), and then Definition 17.8.1 alone does not make
  `|P|` proper.  Counterexample: the trivial groupoid on `ℕ`, `|A| = ℕ` discrete,
  `|B| = ℕ` with the topology of `{0} ∪ {1/n}` ⊆ `ℝ` (compact), `P = id`, `F = ∅`, `Θ = 1`.
* `B_to_A`: from `not_B` (vacuous).
* `A_to_Bpart`: `A` gives every clause of `B` except (4) (branched, (1), (2), (3)).
-/
namespace RoundTrip.V17_142
open Polyfold

def A : Prop :=
  type_of% @Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16.{0} ∧
  type_of% @Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_one.{0} ∧
  type_of% @Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_two.{0} ∧
  type_of% @Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_four.{0} ∧
  type_of% @Polyfold.ProperCoveringUniformizerConstruction.orbitSupp_comp_eq_preimage.{0} ∧
  type_of% @Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_three.{0} ∧
  type_of% @Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_branched_tame.{0} ∧
  type_of% @Polyfold.ProperCoveringUniformizer.isProperCovering_τ.{0} ∧
  type_of% @Polyfold.ProperCoveringUniformizer.comp_hat_eq_pullbackTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.IsProperCovering.isProperMap_orbitMap.{0} ∧
  type_of% @Polyfold.EpFunctor.IsProperCovering.isBranchedEpSubgroupoid_pullbackTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.IsProperCovering.isManifoldType_pullbackTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.IsProperCovering.isCompactBranched_pullbackTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.IsProperCovering.isTameBranched_pullbackTheta.{0} ∧
  type_of% @Polyfold.paracompactSpace_of_isProperMap.{0, 0} ∧
  type_of% @Polyfold.proposition_17_8_16_reflection ∧
  type_of% @Polyfold.isTameBranched_reflectionTheta ∧
  type_of% @Polyfold.proposition_17_8_16_three_reflection

theorem A_holds : A :=
  ⟨@ProperCoveringUniformizerConstruction.proposition_17_8_16.{0},
   @ProperCoveringUniformizerConstruction.proposition_17_8_16_one.{0},
   @ProperCoveringUniformizerConstruction.proposition_17_8_16_two.{0},
   @ProperCoveringUniformizerConstruction.proposition_17_8_16_four.{0},
   @ProperCoveringUniformizerConstruction.orbitSupp_comp_eq_preimage.{0},
   @ProperCoveringUniformizerConstruction.proposition_17_8_16_three.{0},
   @ProperCoveringUniformizerConstruction.proposition_17_8_16_branched_tame.{0},
   @ProperCoveringUniformizer.isProperCovering_τ.{0},
   @ProperCoveringUniformizer.comp_hat_eq_pullbackTheta.{0},
   @EpFunctor.IsProperCovering.isProperMap_orbitMap.{0},
   @EpFunctor.IsProperCovering.isBranchedEpSubgroupoid_pullbackTheta.{0},
   @EpFunctor.IsProperCovering.isManifoldType_pullbackTheta.{0},
   @EpFunctor.IsProperCovering.isCompactBranched_pullbackTheta.{0},
   @EpFunctor.IsProperCovering.isTameBranched_pullbackTheta.{0},
   @paracompactSpace_of_isProperMap.{0, 0},
   @proposition_17_8_16_reflection,
   @isTameBranched_reflectionTheta,
   @proposition_17_8_16_three_reflection⟩

/-! ### `B` without its compactness clause, from `A` -/

/-- `B` without clause (4). -/
def Bpart : Prop :=
  ∀ (A B : GCT.{0}) (Pc : ProperPolyfoldCoveringFunctor A B) (Θ : B.Obj → ℚ),
    Pc.S.toC.IsBranchedBase Θ →
      Pc.S.toC.IsBranchedHat (fun α => Θ (Pc.P.obj α)) ∧
      (B.IsManifoldTypeBranched Θ → A.IsManifoldTypeBranched (fun α => Θ (Pc.P.obj α))) ∧
      (B.IsOrbifoldTypeBranched Θ → A.IsOrbifoldTypeBranched (fun α => Θ (Pc.P.obj α))) ∧
      (Pc.S.toC.IsTameBase Θ → Pc.S.toC.IsTameHat (fun α => Θ (Pc.P.obj α)))

theorem A_to_Bpart : A → Bpart := by
  rintro ⟨h0, h1, h2, -, -, h3, -⟩ A B Pc Θ hΘ
  refine ⟨h0 Pc.isProperCovering hΘ, fun hm => ?_, fun ho => h2 ho, fun ht =>
    h3 Pc.isProperCovering ht⟩
  exact h1 Pc.isProperCovering hm.1 hm.2

/-- The main conjunct alone gives the branched clause. -/
theorem main_to_Bbranched :
    type_of% @Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16.{0} →
    ∀ (A B : GCT.{0}) (Pc : ProperPolyfoldCoveringFunctor A B) (Θ : B.Obj → ℚ),
      Pc.S.toC.IsBranchedBase Θ → Pc.S.toC.IsBranchedHat (fun α => Θ (Pc.P.obj α)) :=
  fun h _ _ Pc _ hΘ => h Pc.isProperCovering hΘ

/-! ### `B` does not hold: a proper covering functor with an empty uniformizer construction -/

noncomputable section

namespace Counter

/-- The trivial groupoid on `ℕ`, as a groupoidal category. -/
def gc : GroupoidalCategory.{0} where
  Obj := ℕ
  Mor := ℕ
  toGroupoidStr := GroupoidStr.trivial ℕ
  finite_mor α _ := (Set.finite_singleton α).subset fun _ h => h.1

/-- `|gc| → ℕ`. -/
def ofOrb : gc.OrbitSpace → ℕ :=
  Quotient.lift (fun n : ℕ => n) fun _ _ ⟨_, ha, hb⟩ => ha.symm.trans hb

theorem ofOrb_π (n : ℕ) : ofOrb (gc.toGroupoidStr.π n) = n := rfl

theorem ofOrb_injective : Function.Injective ofOrb := by
  intro x y h
  induction x using Quotient.inductionOn with
  | h a =>
  induction y using Quotient.inductionOn with
  | h b =>
  exact Quotient.sound ⟨a, rfl, h⟩

theorem ofOrb_surjective : Function.Surjective ofOrb := fun n => ⟨gc.toGroupoidStr.π n, rfl⟩

/-- `n ↦ 1/n` (with `1/0 = 0`), injective, with compact range `{0} ∪ {1/n}`. -/
def e (n : ℕ) : ℝ := (n : ℝ)⁻¹

theorem e_injective : Function.Injective e := fun a b h => by
  simpa [e] using h

theorem isCompact_range_e : IsCompact (Set.range e) := by
  have h := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).isCompact_insert_range
  have h0 : (0 : ℝ) ∈ Set.range e := ⟨0, by simp [e]⟩
  change IsCompact (insert 0 (Set.range e)) at h
  rwa [Set.insert_eq_of_mem h0] at h

def g : gc.OrbitSpace → ℝ := fun z => e (ofOrb z)

/-- `A`: `|A| = ℕ`, discrete. -/
def GA : GCT.{0} :=
  letI : TopologicalSpace gc.OrbitSpace := ⊥
  haveI : DiscreteTopology gc.OrbitSpace := ⟨rfl⟩
  { toGroupoidalCategory := gc, top := ⊥, metrizable := inferInstance }

/-- `B`: `|B| = ℕ` with the topology of `{0} ∪ {1/n} ⊆ ℝ`. -/
def GB : GCT.{0} :=
  letI : TopologicalSpace gc.OrbitSpace := TopologicalSpace.induced g inferInstance
  { toGroupoidalCategory := gc, top := TopologicalSpace.induced g inferInstance,
    metrizable := (Topology.IsEmbedding.mk ⟨rfl⟩
      (e_injective.comp ofOrb_injective)).metrizableSpace }

instance : DiscreteTopology GA.OrbitSpace := ⟨rfl⟩

theorem isEmbedding_g : @Topology.IsEmbedding GB.OrbitSpace ℝ GB.top _ g :=
  Topology.IsEmbedding.mk ⟨rfl⟩ (e_injective.comp ofOrb_injective)

/-- The identity functor. -/
def P : GroupoidFunctor GA.toGroupoidStr GB.toGroupoidStr := GroupoidFunctor.id _

theorem orbitMap_P (z : GA.OrbitSpace) : P.orbitMap z = z := by
  induction z using Quotient.inductionOn with
  | h a => rfl

theorem hP : P.IsProperCoveringGCT where
  continuous_orbitMap := continuous_of_discreteTopology
  surjective_orbitMap z := ⟨z, orbitMap_P z⟩
  finite_fiber β := (Set.finite_singleton β).subset fun _ h => h
  surjective_obj β := ⟨β, rfl⟩
  evenlyCovered z := by
    have hfib : P.orbitMap ⁻¹' {z} = {z} := by
      ext y
      show P.orbitMap y = z ↔ y = z
      rw [orbitMap_P]
      exact Iff.rfl
    refine ⟨by rw [hfib]; exact Set.finite_singleton z, Set.univ, fun _ => Set.univ, isOpen_univ,
      Set.mem_univ _, fun _ _ => ⟨isOpen_univ, Set.mem_univ _⟩, ?_, ?_⟩
    · rw [hfib]
      exact Set.pairwiseDisjoint_singleton _ _
    · rw [hfib, Set.preimage_univ]
      refine (Set.eq_univ_of_forall fun x => ?_).symm
      exact Set.mem_iUnion₂.2 ⟨z, rfl, Set.mem_univ x⟩
  bijective_fibredMor := by
    refine ⟨fun φ ψ h => congrArg (fun p => p.1.1) h, ?_⟩
    rintro ⟨⟨m, a⟩, h⟩
    refine ⟨a, ?_⟩
    have h' : m = a := h
    subst h'
    rfl

/-- The empty proper covering uniformizer construction. -/
def C0 : ProperCoveringUniformizerConstruction P := ⟨fun _ => ∅⟩

theorem noUnifB (Ψ : GCT.Unif (fun _ : GB.Obj => (∅ : Set GB.LocalUniformizer))) : False := by
  obtain ⟨_, _, h⟩ := Ψ
  exact h

theorem noUnifC (U : C0.Unif) : False := U.2

/-- The polyfold structure of `B` with no uniformizers. -/
def SB0 : GB.PolyfoldConstruction where
  F _ := ∅
  isAt _ _ h := h.elim
  topM Ψ := (noUnifB Ψ).elim
  t2M Ψ := (noUnifB Ψ).elim
  paraM Ψ := (noUnifB Ψ).elim
  M Ψ := (noUnifB Ψ).elim
  isLocalScDiffeo_src Ψ := (noUnifB Ψ).elim
  isLocalScDiffeo_tgt Ψ := (noUnifB Ψ).elim
  isScSmoothMap_unit Ψ := (noUnifB Ψ).elim
  isScSmoothMap_inv Ψ := (noUnifB Ψ).elim
  isScSmoothMap_mul Ψ := (noUnifB Ψ).elim

def S0 : ProperPolyfoldCoveringStructure P where
  toC := C0
  SB := SB0
  SB_F _ := (Set.image_empty _).symm
  topH U := (noUnifC U).elim
  t2H U := (noUnifC U).elim
  paraH U := (noUnifC U).elim
  MH U := (noUnifC U).elim
  isLocalScDiffeo_src U := (noUnifC U).elim
  isLocalScDiffeo_tgt U := (noUnifC U).elim
  isScSmoothMap_unit U := (noUnifC U).elim
  isScSmoothMap_inv U := (noUnifC U).elim
  isScSmoothMap_mul U := (noUnifC U).elim
  isLocalScDiffeo_p U := (noUnifC U).elim

def Pc : ProperPolyfoldCoveringFunctor GA GB := ⟨P, hP, S0⟩

end Counter

end

open Counter in
theorem not_B : ¬ B := by
  intro hB
  have hbr : Pc.S.toC.IsBranchedBase (fun _ : GB.Obj => (1 : ℚ)) :=
    ⟨fun _ => zero_le_one, fun _ => rfl, fun _ _ h => h.elim⟩
  have h4 := (hB GA GB Pc (fun _ => 1) hbr).2.2.2.2
  have hsupp : ∀ C : GCT.{0}, C.toGroupoidStr.orbitSupp (fun _ : C.Obj => (1 : ℚ)) = Set.univ :=
    fun C => by
      rw [GroupoidStr.orbitSupp, Set.eq_univ_iff_forall]
      intro z
      obtain ⟨a, rfl⟩ := C.toGroupoidStr.surjective_π z
      exact ⟨a, by exact (zero_lt_one : (0 : ℚ) < 1), rfl⟩
  have hcB : GB.IsCompactBranched (fun _ => 1) := by
    rw [GCT.IsCompactBranched, hsupp]
    rw [isEmbedding_g.isCompact_iff]
    convert isCompact_range_e using 1
    ext x
    constructor
    · rintro ⟨z, -, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨n, rfl⟩; exact ⟨gc.toGroupoidStr.π n, trivial, rfl⟩
  have hcA := h4 hcB
  rw [GCT.IsCompactBranched, hsupp, isCompact_iff_finite, Set.finite_univ_iff] at hcA
  have : Finite ℕ := @Finite.of_surjective _ _ hcA ofOrb ofOrb_surjective
  exact not_finite ℕ

/-- Vacuous: `B` does not hold. -/
theorem B_to_A : B → A := fun h => (not_B h).elim

#rt_check RoundTrip.V17_142.A_to_Bpart [Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_one, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_two, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_four, Polyfold.ProperCoveringUniformizerConstruction.orbitSupp_comp_eq_preimage, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_three, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_branched_tame, Polyfold.ProperCoveringUniformizer.isProperCovering_τ, Polyfold.ProperCoveringUniformizer.comp_hat_eq_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isProperMap_orbitMap, Polyfold.EpFunctor.IsProperCovering.isBranchedEpSubgroupoid_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isManifoldType_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isCompactBranched_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isTameBranched_pullbackTheta, Polyfold.paracompactSpace_of_isProperMap, Polyfold.proposition_17_8_16_reflection, Polyfold.isTameBranched_reflectionTheta, Polyfold.proposition_17_8_16_three_reflection]
#rt_check RoundTrip.V17_142.main_to_Bbranched [Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_one, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_two, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_four, Polyfold.ProperCoveringUniformizerConstruction.orbitSupp_comp_eq_preimage, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_three, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_branched_tame, Polyfold.ProperCoveringUniformizer.isProperCovering_τ, Polyfold.ProperCoveringUniformizer.comp_hat_eq_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isProperMap_orbitMap, Polyfold.EpFunctor.IsProperCovering.isBranchedEpSubgroupoid_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isManifoldType_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isCompactBranched_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isTameBranched_pullbackTheta, Polyfold.paracompactSpace_of_isProperMap, Polyfold.proposition_17_8_16_reflection, Polyfold.isTameBranched_reflectionTheta, Polyfold.proposition_17_8_16_three_reflection]
#rt_check RoundTrip.V17_142.not_B [Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_one, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_two, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_four, Polyfold.ProperCoveringUniformizerConstruction.orbitSupp_comp_eq_preimage, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_three, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_branched_tame, Polyfold.ProperCoveringUniformizer.isProperCovering_τ, Polyfold.ProperCoveringUniformizer.comp_hat_eq_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isProperMap_orbitMap, Polyfold.EpFunctor.IsProperCovering.isBranchedEpSubgroupoid_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isManifoldType_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isCompactBranched_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isTameBranched_pullbackTheta, Polyfold.paracompactSpace_of_isProperMap, Polyfold.proposition_17_8_16_reflection, Polyfold.isTameBranched_reflectionTheta, Polyfold.proposition_17_8_16_three_reflection]
#rt_check RoundTrip.V17_142.B_to_A [Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_one, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_two, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_four, Polyfold.ProperCoveringUniformizerConstruction.orbitSupp_comp_eq_preimage, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_three, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_branched_tame, Polyfold.ProperCoveringUniformizer.isProperCovering_τ, Polyfold.ProperCoveringUniformizer.comp_hat_eq_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isProperMap_orbitMap, Polyfold.EpFunctor.IsProperCovering.isBranchedEpSubgroupoid_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isManifoldType_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isCompactBranched_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isTameBranched_pullbackTheta, Polyfold.paracompactSpace_of_isProperMap, Polyfold.proposition_17_8_16_reflection, Polyfold.isTameBranched_reflectionTheta, Polyfold.proposition_17_8_16_three_reflection]
#rt_overlap RoundTrip.V17_142.B_to_A [Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_one, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_two, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_four, Polyfold.ProperCoveringUniformizerConstruction.orbitSupp_comp_eq_preimage, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_three, Polyfold.ProperCoveringUniformizerConstruction.proposition_17_8_16_branched_tame, Polyfold.ProperCoveringUniformizer.isProperCovering_τ, Polyfold.ProperCoveringUniformizer.comp_hat_eq_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isProperMap_orbitMap, Polyfold.EpFunctor.IsProperCovering.isBranchedEpSubgroupoid_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isManifoldType_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isCompactBranched_pullbackTheta, Polyfold.EpFunctor.IsProperCovering.isTameBranched_pullbackTheta, Polyfold.paracompactSpace_of_isProperMap, Polyfold.proposition_17_8_16_reflection, Polyfold.isTameBranched_reflectionTheta, Polyfold.proposition_17_8_16_three_reflection]

end RoundTrip.V17_142
