import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_39

set_option maxSynthPendingDepth 3

/-! Round trip for V19_39 (2021 Proposition 19.5.9, p. 890).  Universes at `0`.

`A` speaks of the project's structure `toPolyfoldConstruction hm`; `B` of every natural polyfold
structure `P` (uniformizer sets those of `F`, `M(Ψ, Ψ')` with `T_{Ψ,Ψ'}`).
* `A_to_B` uses the conjuncts `isLUCLevel_zero_of_isLUC` and `EP.isGenIsoInvariant_isLUC_lift`;
  the model step (a level-`i` (LUC) of the basic construction gives (LUC) of the `i`-th lift of
  some model) is shown directly for the natural `P` (`exists_isLUC_lift_model_P`: the project's
  argument, with the covering family taken in `P` through naturality and `Ψ̂` continuous since
  `M(Ψ, Ψ)` carries `T_{Ψ,Ψ}`).  The main conjunct `proposition_19_5_9` (about
  `toPolyfoldConstruction` only) is not used: passing from it to another natural `P` would need an
  equivalence of the models of `P` and of `toPolyfoldConstruction` (same objects and morphisms,
  equal topologies, identity sc-diffeomorphisms on morphisms), which is not proved here.
* `B_to_A`: `B` at `P = toPolyfoldConstruction` (natural) gives `proposition_19_5_9`; the
  helper conjuncts (single levels, the level-0 identification, invariance under generalized
  isomorphisms) are not in `B` and are re-proved outright. -/

namespace RoundTrip.V19_39
open Polyfold Polyfold.GroupoidalCategory Set
open Polyfold.GroupoidalCategory.BasicConstruction Polyfold.GCT.PolyfoldConstruction

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_9.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.exists_isLUC_lift_model.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.isLUCLevel_zero_of_isLUC.{0}) ∧
  (type_of% @Polyfold.EP.isGenIsoInvariant_isLUC_lift.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_9.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.exists_isLUC_lift_model.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.isLUCLevel_zero_of_isLUC.{0},
    @Polyfold.EP.isGenIsoInvariant_isLUC_lift.{0}⟩

section
variable {C : GroupoidalCategory.{0}} {B : C.BasicConstruction} {hB : B.U.HasClassUniformizers}
  {hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (B.natTop hB)}
  {P : (B.toGCTOfMetrizable hB hm).PolyfoldConstruction}

/-- In a natural structure `Ψ̂ : G × O → M(Ψ, Ψ)` is continuous (`M(Ψ, Ψ)` carries `T_{Ψ,Ψ}`). -/
theorem hat_cont (hnat : IsNaturalStructure B hB hm P) (Ψ : P.Unif) : Continuous (P.hat Ψ) := by
  have hΨ : ∃ α, Ψ.1.toUniformizer ∈ B.U.F α := by
    obtain ⟨α, h⟩ := Ψ.2; exact ⟨α, (hnat.1 α Ψ.1).1 h⟩
  have ht : P.topM Ψ Ψ = B.rep.topology ⟨Ψ.1.toUniformizer, hΨ⟩ ⟨Ψ.1.toUniformizer, hΨ⟩ :=
    hnat.2.2 Ψ Ψ hΨ hΨ B.rep B.mk_rep
  have hc := (B.rep.hatHomeomorph ⟨Ψ.1.toUniformizer, hΨ⟩).continuous
  show @Continuous _ _ _ (P.topM Ψ Ψ) (P.hat Ψ)
  rw [ht]
  exact hc

/-- The model step for a natural `P` (the project's argument for `toPolyfoldConstruction`). -/
theorem exists_isLUC_lift_model_P (hnat : IsNaturalStructure B hB hm P) (i : ℕ)
    (h : B.IsLUCLevel i) : ∃ c : P.CoveringFamily, ((P.modelEP c.Ψ).lift i).X.IsLUC := by
  have key : ∀ z : C.OrbitSpace, ∃ (α : C.Obj)
      (Ψl : (B.toGCTOfMetrizable hB hm).LocalUniformizer) (_ : Ψl ∈ P.F α),
      C.π α = z ∧ (B.IsLevelClass i z → ∃ p : (Ψl.toUniformizer.toEP.lift i).Obj,
        Ψl.toUniformizer.obj (Ψl.toUniformizer.toEP.liftVal i p) = α ∧
          (Ψl.toUniformizer.toEP.lift i).X.IsLUCAt p) := by
    intro z
    by_cases hz : B.IsLevelClass i z
    · obtain ⟨α, Ψ, hΨ, p, hα, hp, hL⟩ := h z hz
      obtain ⟨Ψl, hΨl, rfl⟩ := hnat.2.1 α Ψ hΨ
      exact ⟨α, Ψl, hΨl, hα, fun _ => ⟨p, hp, hL⟩⟩
    · obtain ⟨α, hα, Ψ, hΨ⟩ := hB z
      obtain ⟨Ψl, hΨl, rfl⟩ := hnat.2.1 α Ψ hΨ
      exact ⟨α, Ψl, hΨl, hα, fun h' => absurd h' hz⟩
  choose α Ψl hΨl hα hy using key
  let Φ : C.OrbitSpace → P.Unif := fun z => ⟨Ψl z, α z, hΨl z⟩
  have hF : ∀ z, (Ψl z).toUniformizer ∈ B.U.F (α z) := fun z => (hnat.1 (α z) (Ψl z)).1 (hΨl z)
  have hcov : ⋃ z, (Φ z).1.footprint = univ := eq_univ_of_forall fun z => mem_iUnion.2
    ⟨z, by
      obtain ⟨o, ho⟩ := B.U.isAt (α z) (Ψl z).toUniformizer (hF z)
      exact (Ψl z).mem_footprint_iff.2 ⟨o, (congrArg C.π ho).trans (hα z)⟩⟩
  refine ⟨⟨C.OrbitSpace, Φ, hcov⟩, fun p' => ?_⟩
  change (((P.modelEP Φ).lift i).X).IsLUCAt p'
  have hmem := (P.modelEP Φ).liftVal_mem_levelSet_self i p'
  rcases hyv : (P.modelEP Φ).liftVal i p' with ⟨j, q⟩
  rw [hyv] at hmem
  have hq : q ∈ (Ψl j).P.levelSet i :=
    ((MPolyfold.isLocalScDiffeo_sigmaMk (fun i => (Φ i).1.P) j).mem_levelSet_iff q i).1 hmem
  have hz : B.IsLevelClass i (C.π ((Ψl j).obj q)) :=
    ⟨⟨(Ψl j).toUniformizer, α j, hF j⟩, q, hq, rfl⟩
  set z := C.π ((Ψl j).obj q) with hzdef
  obtain ⟨p, hpo, hL⟩ := hy z hz
  have hc := hat_cont hnat (Φ z)
  let F : EpFunctor (Ψl z).toUniformizer.toEP.X (P.modelEP Φ).X := pieceFunctor Φ z hc
  have hLF : ((P.modelEP Φ).lift i).X.IsLUCAt ((EP.liftFunctor F i).obj p) :=
    (EP.liftFunctor F i).isLUCAt_obj
      (EP.isLocalScDiffeo_liftFunctor (isLocalScDiffeo_pieceFunctor_obj Φ z hc) i)
      (EP.full_liftFunctor (full_pieceFunctor Φ z hc) i) hL
  obtain ⟨φ, hφs, hφt⟩ := C.π_eq_π_iff.1
    (show C.π ((Ψl z).obj ((Ψl z).toUniformizer.toEP.liftVal i p)) = C.π ((Ψl j).obj q) from
      (congrArg C.π hpo).trans ((hα z).trans hzdef))
  let ψ : P.ModelMor Φ :=
    ⟨(z, j), ⟨(Ψl z).toUniformizer.toEP.liftVal i p, φ, q, hφs, hφt⟩⟩
  obtain ⟨ψ', hs', ht'⟩ := (P.modelEP Φ).exists_liftMor i ((EP.liftFunctor F i).obj p) p' ψ
    (by rw [EP.liftVal_liftFunctor_obj]; rfl) (by rw [hyv]; rfl)
  exact EpGroupoid.isLUCAt_of_isomorphic hs' ht' hLF

end

theorem A_to_B (hA : A) : B := by
  intro C B hB hm P hnat
  refine ⟨fun h => exists_isLUC_lift_model_P hnat 0 (hA.2.2.1 h), fun h => ?_⟩
  choose c hc using fun i => exists_isLUC_lift_model_P hnat i (h i)
  exact ⟨c 0, fun i => (hA.2.2.2 i (P.isGeneralizedIso_comparison (c i) (c 0))).1 (hc i)⟩

/-- The project's `(F, M)` is natural in `B`'s sense. -/
theorem natural_toPolyfoldConstruction {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    (hB : B.U.HasClassUniformizers)
    (hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (B.natTop hB)) :
    IsNaturalStructure B hB hm (toPolyfoldConstruction hm) := by
  refine ⟨fun α Ψ => Iff.rfl, fun α Ψ hΨ => ⟨toLocalUniformizer hm hΨ, hΨ, rfl⟩,
    fun Ψ Ψ' hΨ hΨ' F hF => ?_⟩
  show B.rep.topology _ _ = _
  exact TopologicalSpace.ext (UniformizerConstruction.TransitionData.lemma_19_3_1
    (Quotient.exact (B.mk_rep.trans hF.symm)) ⟨Ψ.1.toUniformizer, hΨ⟩ ⟨Ψ'.1.toUniformizer, hΨ'⟩)

theorem main_B_to_A (hB' : B) :
    type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_9.{0} :=
  fun {_C} {B} {hB} hm => hB' _ B hB hm _ (natural_toPolyfoldConstruction B hB hm)

section Copies
variable {C : GroupoidalCategory.{0}} {B : C.BasicConstruction} {hB : B.U.HasClassUniformizers}

theorem exists_isLUC_lift_model' (hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (B.natTop hB))
    (i : ℕ) (h : B.IsLUCLevel i) :
    ∃ c : (toPolyfoldConstruction hm).CoveringFamily,
      (((toPolyfoldConstruction hm).modelEP c.Ψ).lift i).X.IsLUC :=
  exists_isLUC_lift_model_P (natural_toPolyfoldConstruction B hB hm) i h

theorem isLUCLevel_zero_of_isLUC' (h : B.IsLUC) : B.IsLUCLevel 0 := fun z _ => by
  obtain ⟨α, Ψ, hΨ, o, hα, ho, hL⟩ := h z
  exact ⟨α, Ψ, hΨ, o, hα, ho, (Ψ.isLUCAt_iff o).1 hL⟩

end Copies

open EPLocalization EPLocalization.EPLoc in
theorem isGenIsoInvariant_isLUC_lift' (i : ℕ) :
    GCT.PolyfoldConstruction.IsGenIsoInvariant fun A : EP.{0} => (A.lift i).X.IsLUC :=
  fun hf => iff_of_isGeneralizedIso (fun A : EP.{0} => (A.lift i).X.IsLUC)
    (fun _ hF => by
      obtain ⟨G, hG⟩ := EP.exists_isEquivalence_lift hF i
      exact EpFunctor.proposition_10_1_16 hG) hf

theorem B_to_A (hB' : B) : A :=
  ⟨main_B_to_A hB', @exists_isLUC_lift_model', @isLUCLevel_zero_of_isLUC',
    isGenIsoInvariant_isLUC_lift'⟩

#rt_check RoundTrip.V19_39.A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_9,
  Polyfold.GroupoidalCategory.BasicConstruction.exists_isLUC_lift_model,
  Polyfold.GroupoidalCategory.BasicConstruction.isLUCLevel_zero_of_isLUC,
  Polyfold.EP.isGenIsoInvariant_isLUC_lift]
#rt_check RoundTrip.V19_39.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_9,
  Polyfold.GroupoidalCategory.BasicConstruction.exists_isLUC_lift_model,
  Polyfold.GroupoidalCategory.BasicConstruction.isLUCLevel_zero_of_isLUC,
  Polyfold.EP.isGenIsoInvariant_isLUC_lift]
#rt_check RoundTrip.V19_39.main_B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_9,
  Polyfold.GroupoidalCategory.BasicConstruction.exists_isLUC_lift_model,
  Polyfold.GroupoidalCategory.BasicConstruction.isLUCLevel_zero_of_isLUC,
  Polyfold.EP.isGenIsoInvariant_isLUC_lift]
#rt_overlap RoundTrip.V19_39.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_9,
  Polyfold.GroupoidalCategory.BasicConstruction.exists_isLUC_lift_model,
  Polyfold.GroupoidalCategory.BasicConstruction.isLUCLevel_zero_of_isLUC,
  Polyfold.EP.isGenIsoInvariant_isLUC_lift]
#rt_overlap RoundTrip.V19_39.A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_9,
  Polyfold.GroupoidalCategory.BasicConstruction.exists_isLUC_lift_model,
  Polyfold.GroupoidalCategory.BasicConstruction.isLUCLevel_zero_of_isLUC,
  Polyfold.EP.isGenIsoInvariant_isLUC_lift]

end RoundTrip.V19_39
