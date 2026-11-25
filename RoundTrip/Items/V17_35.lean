import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_35

set_option maxSynthPendingDepth 3

/-! Round trip for V17_35 (2021 Corollary 17.1.29, p. 766: (ZHOU), (SLUC), (SLR) pass to `C¹`).

`A` is the conjunction of the types of `corollary_17_1_29_model`,
`isEquivalence_levelOneModelFunctor`, `corollary_17_1_29_of_coveringFamily`, `corollary_17_1_29`,
`UniformizedPolyfold.level_properties` and `z3Taut_levelOne` (`levelOneModelFunctor` is
vocabulary), with `u := 0`.

* `B_to_A`: `corollary_17_1_29_of_coveringFamily` from `B` (`C¹` has the property, hence the model
  of every covering family of `F¹` has it, Definition 17.1.22 / `HasModelProperty.forall`);
  `corollary_17_1_29` from `B` with `hc` obtained from `F(α) ≠ ∅`; `level_properties` by induction
  from `B`.  The model form, the equivalence `X_L → X_Ψ¹` and the ℤ/3 witness are re-proved
  outright (the project's proofs, copied; they are not consequences of `B`).
* `A_to_B` is not proved: `B` assumes only that the footprints of `F` cover `|C|` (`hc`), while
  `A`'s `corollary_17_1_29` assumes `F(α) ≠ ∅` for every `α`, and `A`'s
  `corollary_17_1_29_of_coveringFamily` needs a covering family of `F¹`.  "`C¹` satisfies P" asks
  for a covering family of `F¹`; `F¹(α)` (for `α ∈ C_1`) only contains lifts `Ψ¹` of uniformizers
  `Ψ ∈ F(α)` attached at objects of regularity `1`.  Under `hc` alone the uniformizers of `F` may
  all be attached at objects of regularity `0` but not `1` (possible as soon as the local models are
  infinite-dimensional), with `C_1 ≠ ∅`; then `F¹ ≡ ∅`, `|C¹|` has no covering family and
  `C¹` satisfies none of the properties.  So `B` is stronger than `A` in this hypothesis; we did not
  build such an example.
-/

namespace RoundTrip.V17_35
open Polyfold Polyfold.GCT.PolyfoldConstruction

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29_model.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isEquivalence_levelOneModelFunctor.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29_of_coveringFamily.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29.{0}) ∧
  (type_of% @Polyfold.GCT.UniformizedPolyfold.level_properties.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.z3Taut_levelOne)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29_model.{0},
    @Polyfold.GCT.PolyfoldConstruction.isEquivalence_levelOneModelFunctor.{0},
    @Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29_of_coveringFamily.{0},
    @Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29.{0},
    @Polyfold.GCT.UniformizedPolyfold.level_properties.{0},
    @Polyfold.GCT.PolyfoldConstruction.z3Taut_levelOne⟩

/-! ### Copies of the project's proofs (not consequences of `B`) -/

theorem model' {C : GCT.{0}} (S : C.PolyfoldConstruction) (c : S.CoveringFamily) :
    (S.IsZhou → (S.modelEP c.Ψ).liftOne.X.IsZhou) ∧
      (S.IsSLUC → (S.modelEP c.Ψ).liftOne.IsSLUC) ∧
      (S.IsSLR → (S.modelEP c.Ψ).liftOne.IsSLR) := by
  obtain ⟨-, hSLR, -, hSLUC, hZ⟩ := S.proposition_17_1_24 c
  refine ⟨fun h => (S.modelPolyfoldStructure c (hZ h)).liftOne_isZhou, fun h i => ?_,
    fun h i => ?_⟩
  · exact (congrArg (fun A : EP.{0} => A.X.IsLUC) (EP.lift_succ' _ i)).mp (hSLUC h (i + 1))
  · exact (congrArg (fun A : EP.{0} => A.X.IsLR) (EP.lift_succ' _ i)).mp (hSLR h (i + 1))

theorem isEquivalence' {C : GCT.{0}} (S : C.PolyfoldConstruction) (hc : S.HasCoveringUniformizers)
    (L : (S.levelOneConstruction hc).CoveringFamily) (c₀ : S.CoveringFamily) :
    (S.levelOneModelFunctor hc L c₀).IsEquivalence :=
  EpFunctor.lemma_10_1_2 _
    { faithful := S.levelOneModelFunctor_faithful hc L c₀
      full := S.levelOneModelFunctor_full hc L c₀
      essSurj := S.levelOneModelFunctor_essSurj hc L c₀ }
    (S.isLocalScDiffeo_levelOneModelFunctor_obj hc L c₀)

/-! ### `B ⇒ A` -/

theorem ofCoveringFamily_of_B (hB : B) {C : GCT.{0}} (S : C.PolyfoldConstruction)
    (hc : S.HasCoveringUniformizers) (L : (S.levelOneConstruction hc).CoveringFamily) :
    (S.IsZhou → ((S.levelOneConstruction hc).modelEP L.Ψ).X.IsZhou) ∧
      (S.IsSLUC → ((S.levelOneConstruction hc).modelEP L.Ψ).IsSLUC) ∧
      (S.IsSLR → ((S.levelOneConstruction hc).modelEP L.Ψ).IsSLR) := by
  obtain ⟨h1, h2, h3⟩ := hB C S hc
  exact ⟨fun h => (h1 h).model L, fun h => (h2 h).forall isGenIsoInvariant_isSLUC L,
    fun h => (h3 h).forall isGenIsoInvariant_isSLR L⟩

theorem main_B_to_A : B → (type_of% @Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29.{0}) :=
  fun hB _ S hu => hB _ S (S.hasCoveringUniformizers_of_hasUniformizers hu)

theorem levelProperties_of_B (hB : B) (X : GCT.UniformizedPolyfold.{0}) (i : ℕ) :
    (X.str.IsZhou → (X.level i).str.IsZhou) ∧ (X.str.IsSLUC → (X.level i).str.IsSLUC) ∧
      (X.str.IsSLR → (X.level i).str.IsSLR) := by
  induction i with
  | zero => exact ⟨id, id, id⟩
  | succ i ih =>
    obtain ⟨h1, h2, h3⟩ := hB _ (X.level i).str (X.level i).hasCoveringUniformizers
    exact ⟨fun h => h1 (ih.1 h), fun h => h2 (ih.2.1 h), fun h => h3 (ih.2.2 h)⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun S c => model' S c, fun S hc L c₀ => isEquivalence' S hc L c₀,
    fun S hc L => ofCoveringFamily_of_B hB S hc L, main_B_to_A hB, levelProperties_of_B hB, ?_⟩
  obtain ⟨hZ, -, hSLUC, -, hSLR⟩ := z3Taut_properties
  obtain ⟨h1, h2, h3⟩ := model' z3TautConstruction z3Family
  exact ⟨z3TautConstruction.levelOnePolyfoldClass_eq _ hZ z3Family, h1 hZ, h2 hSLUC, h3 hSLR,
    z3TautConstruction.raiseIncl_levelOneHomeomorphRaised _ hZ⟩

#rt_check RoundTrip.V17_35.B_to_A [Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29_model,
  Polyfold.GCT.PolyfoldConstruction.isEquivalence_levelOneModelFunctor,
  Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29_of_coveringFamily,
  Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29,
  Polyfold.GCT.UniformizedPolyfold.level_properties,
  Polyfold.GCT.PolyfoldConstruction.z3Taut_levelOne]
#rt_overlap RoundTrip.V17_35.B_to_A [Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29_model,
  Polyfold.GCT.PolyfoldConstruction.isEquivalence_levelOneModelFunctor,
  Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29_of_coveringFamily,
  Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29,
  Polyfold.GCT.UniformizedPolyfold.level_properties,
  Polyfold.GCT.PolyfoldConstruction.z3Taut_levelOne]
#rt_check RoundTrip.V17_35.main_B_to_A [Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29_model,
  Polyfold.GCT.PolyfoldConstruction.isEquivalence_levelOneModelFunctor,
  Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29_of_coveringFamily,
  Polyfold.GCT.PolyfoldConstruction.corollary_17_1_29,
  Polyfold.GCT.UniformizedPolyfold.level_properties,
  Polyfold.GCT.PolyfoldConstruction.z3Taut_levelOne]

end RoundTrip.V17_35
