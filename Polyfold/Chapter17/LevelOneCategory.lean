import Polyfold.Chapter17.PolyfoldLevels
import Polyfold.Chapter16.RaisedPolyfold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (p. 766): the metrizable topology of `|C_1|`, the GCT `C¹` of **Theorem 17.1.28**, and the
model form of **Corollary 17.1.29**.  Numbers and pages are the 2021 text's.

# The GCT `C¹`

## The text, paraphrased

(p. 766) The equivalence `Γ_Ψ : X_Ψ → C` induces the homeomorphism `|Γ_Ψ| : |X_Ψ| → |C|`; `|X|`
(`X := X_Ψ`) is metrizable, hence paracompact and Hausdorff, so `|X¹|` is paracompact, Hausdorff
and locally metrizable, therefore metrizable, and consequently `|C_1|` has a natural metrizable
topology (Section 7.3).  In particular `C¹` is a GCT.  `F¹(α)` consists of the `Ψ¹ : G ⋉ O¹ → C_1`
obtained from `Ψ` by lifting the index, with `M_{F¹}(Ψ¹, Ψ'¹) := (M(Ψ, Ψ'))¹`.
(Theorem 17.1.28) `C_1` is in a natural way a GCT with the natural polyfold structure
`(F¹, M_{F¹})`.  (Corollary 17.1.29) If `C` satisfies (ZHOU), (SLUC) or (SLR), so does `C¹`.
`C^{i+1} := (C^i)¹`.

## What is formalized

* General full subgroupoids: `GroupoidStr.fullSubInclusion` (the inclusion functor),
  `GroupoidStr.isomorphic_fullSub_iff`, `GroupoidStr.injective_orbitMap_fullSubInclusion`,
  `GroupoidStr.range_orbitMap_fullSubInclusion` (`|C_A| → |C|` is injective with image `π(A)`),
  `GroupoidFunctor.corestrict` (a functor into `C` whose objects lie in `A` is one into `C_A`).
* `modelFunctorOne Ψ : X_Ψ¹ → C_1` (the functor `Γ_Ψ` on level `1`), `orbitIncl_modelFunctorOne`
  (`|C_1 → C| ∘ |Γ_Ψ¹| = |Γ_Ψ| ∘ |X_Ψ¹ → X_Ψ|`), and for a covering family `c`
  `modelOrbitEquivOne c : |X_Ψ¹| ≃ |C_1|` (`bijective_orbitMap_modelFunctorOne`).
* `modelOrbitEquivOne_eq_comp`: `|Γ_Ψ¹| = |Γ_Ψ'¹| ∘ |f_{Ψ,Ψ'}¹|` for two covering families
  (`f¹` the index raise of the comparison, Chapter 16).
* The topology `levelOneTopology hc` of `|C_1|` (transported from `|X_Ψ¹|` for a chosen covering
  family) and **`isHomeomorph_modelOrbitEquivOne`**: for *every* covering family,
  `|Γ_Ψ¹| : |X_Ψ¹| → |C_1|` is a homeomorphism (so the topology does not depend on the choice);
  `metrizableSpace_levelOne` (it is metrizable), `continuous_orbitIncl_levelOne`
  (`|C_1| → |C|` is continuous).
* **Theorem 17.1.28 (the GCT)**: `levelOneGCT hc`, the GCT `C¹` (objects of regularity `1`, the full
  subcategory, finite morphism sets, the metrizable topology), `theorem_17_1_28_gct`.
* Under (ZHOU): `levelOnePolyfoldStructure` (`(X_Ψ¹, |Γ_Ψ¹|)`, a polyfold structure on `|C¹|`
  in the sense of Definition 16.1.1), `levelOnePolyfoldClass` (independent of the covering
  family, `levelOnePolyfoldClass_eq`), and `levelOneHomeomorphRaised`: `|C¹|` is homeomorphic to
  the raised polyfold `(|C|, c_C)¹` of §16.2 over the inclusions into `|C|`
  (`raiseIncl_levelOneHomeomorphRaised`).
* **Corollary 17.1.29 (model form)**: `corollary_17_1_29_model`: if `C` satisfies (ZHOU), (SLUC)
  or (SLR), so does `X_Ψ¹` for every covering family.

## Readings

* "Pick `Ψ`" for the topology presupposes a covering set (`HasCoveringUniformizers`, implicit in
  the text).  We transport the topology of `|X_Ψ¹|` for one chosen covering family and prove
  that `|Γ_Ψ¹|` is a homeomorphism for every covering family; this is the text's "natural"
  topology.  It is finer than the subspace topology of `|C_1| ⊆ |C|` in general.
* We read Corollary 17.1.29 through the models: (ZHOU), (SLUC), (SLR) for `C¹` are those of the
  models `X_{Ψ¹}` of the lifted construction, which are the index raises `X_Ψ¹`
  (`X_{Ψ¹} = ⊔ G_λ ⋉ O_λ¹` with transitions `M(Ψ_λ, Ψ_μ)¹`); `corollary_17_1_29_model` states the
  conclusion for `X_Ψ¹`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace CategoryTheory

noncomputable section

universe u

namespace Polyfold

open EPLocalization EPLocalization.EPLoc

/-! ### Full subgroupoids -/

namespace GroupoidStr

variable {Obj Mor : Type u} (G : GroupoidStr Obj Mor)

/-- **The inclusion functor** `C_A → C` of the full subgroupoid on `A`. -/
def fullSubInclusion (A : Set Obj) : GroupoidFunctor (G.fullSub A) G where
  obj := Subtype.val
  mor := Subtype.val
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp φ ψ h := by
    have h' : G.src φ.1 = G.tgt ψ.1 := congrArg Subtype.val h
    simp only [fullSub, dif_pos h']
  mor_unit _ := rfl

variable {G} in
/-- Objects of `A` are isomorphic in `C_A` iff they are in `C` (the subcategory is full). -/
theorem isomorphic_fullSub_iff {A : Set Obj} {x y : A} :
    (G.fullSub A).Isomorphic x y ↔ G.Isomorphic x.1 y.1 := by
  constructor
  · rintro ⟨φ, hs, ht⟩
    exact ⟨φ.1, congrArg Subtype.val hs, congrArg Subtype.val ht⟩
  · rintro ⟨φ, hs, ht⟩
    exact ⟨⟨φ, hs ▸ x.2, ht ▸ y.2⟩, Subtype.ext hs, Subtype.ext ht⟩

/-- **`|C_A| → |C|` is injective.** -/
theorem injective_orbitMap_fullSubInclusion (A : Set Obj) :
    Injective (G.fullSubInclusion A).orbitMap := by
  intro a b h
  induction a using Quotient.inductionOn with | h x => ?_
  induction b using Quotient.inductionOn with | h y => ?_
  have h' : G.π x.1 = G.π y.1 := h
  exact ((G.fullSub A).π_eq_π_iff).2 (isomorphic_fullSub_iff.2 ((G.π_eq_π_iff).1 h'))

/-- The image of `|C_A| → |C|` is `π(A)`. -/
theorem range_orbitMap_fullSubInclusion (A : Set Obj) :
    range (G.fullSubInclusion A).orbitMap = G.π '' A := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    induction w using Quotient.inductionOn with
    | h x => exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(G.fullSub A).π ⟨x, hx⟩, rfl⟩

end GroupoidStr

namespace GroupoidFunctor

variable {Obj Mor Obj' Mor' : Type u} {G : GroupoidStr Obj Mor} {H : GroupoidStr Obj' Mor'}

/-- **The corestriction** of a functor `F : G → H` whose objects lie in `A` to `H_A`. -/
def corestrict (F : GroupoidFunctor G H) (A : Set Obj') (hA : ∀ x, F.obj x ∈ A) :
    GroupoidFunctor G (H.fullSub A) where
  obj x := ⟨F.obj x, hA x⟩
  mor φ := ⟨F.mor φ, by rw [F.src_mor]; exact hA _, by rw [F.tgt_mor]; exact hA _⟩
  src_mor φ := Subtype.ext (F.src_mor φ)
  tgt_mor φ := Subtype.ext (F.tgt_mor φ)
  mor_comp φ ψ h := by
    have h' : H.src (F.mor φ) = H.tgt (F.mor ψ) := by rw [F.src_mor, F.tgt_mor, h]
    apply Subtype.ext
    simp only [GroupoidStr.fullSub, dif_pos h']
    exact F.mor_comp φ ψ h
  mor_unit x := Subtype.ext (F.mor_unit x)

theorem orbitMap_fullSubInclusion_corestrict (F : GroupoidFunctor G H) (A : Set Obj')
    (hA : ∀ x, F.obj x ∈ A) :
    (H.fullSubInclusion A).orbitMap ∘ (F.corestrict A hA).orbitMap = F.orbitMap := by
  funext z
  induction z using Quotient.inductionOn with
  | h x => rfl

end GroupoidFunctor

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} (S : C.PolyfoldConstruction)

/-! ### The functor `Γ_Ψ¹ : X_Ψ¹ → C_1` -/

/-- The inclusion `C_1 → C`. -/
abbrev levelOneInclusion : GroupoidFunctor (S.regSub 1) C.toGroupoidStr :=
  C.toGroupoidStr.fullSubInclusion (S.regSet 1)

/-- **`|C_1| → |C|`**, injective with image the classes of regularity `1`. -/
abbrev orbitInclLevelOne : (S.regSub 1).OrbitSpace → C.toGroupoidStr.OrbitSpace :=
  (S.levelOneInclusion).orbitMap

theorem injective_orbitInclLevelOne : Injective S.orbitInclLevelOne :=
  C.toGroupoidStr.injective_orbitMap_fullSubInclusion _

variable {ι : Type u} (Ψ : ι → S.Unif)

/-- **`Γ_Ψ¹ : X_Ψ¹ → C_1`**: `Γ_Ψ` on the level-`1` points (they have regularity `1`). -/
def modelFunctorOne :
    GroupoidFunctor (S.modelEP Ψ).X.liftOne.toGroupoidStr (S.regSub 1) :=
  ((S.modelFunctor Ψ).comp (S.modelEP Ψ).X.liftIncl).corestrict (S.regSet 1) fun x =>
    (S.hasRegularity_modelFunctor_obj Ψ _ 1).2 ((S.modelEP Ψ).X.PObj.levelVal_mem x)

/-- `|C_1 → C| ∘ |Γ_Ψ¹| = |Γ_Ψ| ∘ |X_Ψ¹ → X_Ψ|`. -/
theorem orbitIncl_modelFunctorOne :
    S.orbitInclLevelOne ∘ (S.modelFunctorOne Ψ).orbitMap =
      (S.modelFunctor Ψ).orbitMap ∘ (S.modelEP Ψ).X.orbitIncl := by
  funext z
  induction z using Quotient.inductionOn with
  | h x => rfl

/-- **`|Γ_Ψ¹| : |X_Ψ¹| → |C_1|` is bijective** for a covering family. -/
theorem bijective_orbitMap_modelFunctorOne (c : S.CoveringFamily) :
    Bijective (S.modelFunctorOne c.Ψ).orbitMap := by
  have hΓ := (S.lemma_17_1_15 c).2
  refine ⟨fun a b h => ?_, fun z => ?_⟩
  · have h' := congrArg S.orbitInclLevelOne h
    simp only [← Function.comp_apply (f := S.orbitInclLevelOne),
      orbitIncl_modelFunctorOne] at h'
    exact (S.modelEP c.Ψ).X.orbitIncl_injective (hΓ.injective h')
  · induction z using Quotient.inductionOn with
    | h α => ?_
    obtain ⟨w, hw⟩ := hΓ.surjective (C.toGroupoidStr.π α.1)
    induction w using Quotient.inductionOn with
    | h x => ?_
    have hiso : C.toGroupoidStr.Isomorphic ((S.modelFunctor c.Ψ).obj x) α.1 :=
      (C.toGroupoidStr.π_eq_π_iff).1 hw
    have hx : x ∈ (S.modelEP c.Ψ).X.PObj.levelSet 1 :=
      (S.hasRegularity_modelFunctor_obj c.Ψ x 1).1 (α.2.of_isomorphic hiso.symm)
    refine ⟨(S.modelEP c.Ψ).X.liftOne.π ((S.modelEP c.Ψ).X.PObj.levelMk 1 x hx), ?_⟩
    exact ((S.regSub 1).π_eq_π_iff).2 (GroupoidStr.isomorphic_fullSub_iff.2 hiso)

/-- **`|Γ_Ψ¹|` as a bijection** `|X_Ψ¹| ≃ |C_1|` (a covering family). -/
def modelOrbitEquivOne (c : S.CoveringFamily) :
    (S.modelEP c.Ψ).X.liftOne.OrbitSpace ≃ (S.regSub 1).OrbitSpace :=
  Equiv.ofBijective _ (S.bijective_orbitMap_modelFunctorOne c)

@[simp] theorem modelOrbitEquivOne_apply (c : S.CoveringFamily)
    (z : (S.modelEP c.Ψ).X.liftOne.OrbitSpace) :
    S.modelOrbitEquivOne c z = (S.modelFunctorOne c.Ψ).orbitMap z := rfl

/-- The comparison `f_{Ψ,Ψ'}` as a morphism `of X_Ψ ⟶ of X_Ψ'` of `EP(E⁻¹)`. -/
abbrev comparisonOf (c c' : S.CoveringFamily) :
    EPLoc.of (S.modelEP c.Ψ) ⟶ EPLoc.of (S.modelEP c'.Ψ) :=
  S.comparison c c'

/-- **`|Γ_Ψ¹| = |Γ_Ψ'¹| ∘ |f_{Ψ,Ψ'}¹|`** for two covering families. -/
theorem modelOrbitEquivOne_eq_comp (c c' : S.CoveringFamily) :
    ⇑(S.modelOrbitEquivOne c) =
      ⇑(S.modelOrbitEquivOne c') ∘ orbitMap (liftOneHom (S.comparisonOf c c')) := by
  funext z
  apply S.injective_orbitInclLevelOne
  have h1 : S.orbitInclLevelOne ((S.modelFunctorOne c.Ψ).orbitMap z) =
      (S.modelFunctor c.Ψ).orbitMap ((S.modelEP c.Ψ).X.orbitIncl z) :=
    congrFun (S.orbitIncl_modelFunctorOne c.Ψ) z
  have h2 : S.orbitInclLevelOne
        ((S.modelFunctorOne c'.Ψ).orbitMap (orbitMap (liftOneHom (S.comparisonOf c c')) z)) =
      (S.modelFunctor c'.Ψ).orbitMap
        ((S.modelEP c'.Ψ).X.orbitIncl (orbitMap (liftOneHom (S.comparisonOf c c')) z)) :=
    congrFun (S.orbitIncl_modelFunctorOne c'.Ψ) _
  have h3 : (S.modelEP c'.Ψ).X.orbitIncl (orbitMap (liftOneHom (S.comparisonOf c c')) z) =
      orbitMap (S.comparisonOf c c') ((S.modelEP c.Ψ).X.orbitIncl z) :=
    congrFun (orbitIncl_orbitMap_liftOneHom (S.comparisonOf c c')) z
  have h4 : (S.modelFunctor c'.Ψ).orbitMap
        (orbitMap (S.comparisonOf c c') ((S.modelEP c.Ψ).X.orbitIncl z)) =
      (S.modelFunctor c.Ψ).orbitMap ((S.modelEP c.Ψ).X.orbitIncl z) :=
    congrFun (S.orbitMap_comparison c c') _
  change S.orbitInclLevelOne ((S.modelFunctorOne c.Ψ).orbitMap z) = S.orbitInclLevelOne
    ((S.modelFunctorOne c'.Ψ).orbitMap (orbitMap (liftOneHom (S.comparisonOf c c')) z))
  rw [h1, h2, h3]
  exact h4.symm

/-! ### The topology of `|C_1|` -/

variable (hc : S.HasCoveringUniformizers)

/-- The covering family chosen to transport the topology. -/
def levelOneCover : S.CoveringFamily := (S.exists_coveringFamily_iff.2 hc).some

/-- **The natural topology of `|C_1|`** (p. 766), transported from `|X_Ψ¹|` along `|Γ_Ψ¹|` for the
chosen covering family (`isHomeomorph_modelOrbitEquivOne`: the same for every covering family). -/
@[instance_reducible]
def levelOneTopology : TopologicalSpace (S.regSub 1).OrbitSpace :=
  TopologicalSpace.coinduced (S.modelOrbitEquivOne (S.levelOneCover hc)) inferInstance

/-- **`|Γ_Ψ¹| : |X_Ψ¹| → |C_1|` is a homeomorphism for every covering family** (p. 766). -/
theorem isHomeomorph_modelOrbitEquivOne (c : S.CoveringFamily) :
    @IsHomeomorph _ _ _ (S.levelOneTopology hc) (S.modelOrbitEquivOne c) := by
  let := S.levelOneTopology hc
  have h₀ : IsHomeomorph (S.modelOrbitEquivOne (S.levelOneCover hc)) :=
    ((S.modelOrbitEquivOne (S.levelOneCover hc)).toHomeomorph fun _ => isOpen_coinduced.symm
      ).isHomeomorph
  have hf : IsHomeomorph (orbitMap (liftOneHom (S.comparisonOf c (S.levelOneCover hc)))) :=
    isHomeomorph_orbitMap_of_isGeneralizedIso
      (isGeneralizedIso_liftOneHom (S.isGeneralizedIso_comparison c _))
  rw [S.modelOrbitEquivOne_eq_comp c (S.levelOneCover hc)]
  exact h₀.comp hf

/-- `|Γ_Ψ¹|` as a homeomorphism `|X_Ψ¹| ≃ₜ |C_1|`. -/
def modelOrbitHomeomorphOne (c : S.CoveringFamily) :
    @Homeomorph (S.modelEP c.Ψ).X.liftOne.OrbitSpace (S.regSub 1).OrbitSpace _
      (S.levelOneTopology hc) :=
  @IsHomeomorph.homeomorph _ _ _ (S.levelOneTopology hc) _ (S.isHomeomorph_modelOrbitEquivOne hc c)

theorem modelOrbitHomeomorphOne_apply (c : S.CoveringFamily)
    (z : (S.modelEP c.Ψ).X.liftOne.OrbitSpace) :
    S.modelOrbitHomeomorphOne hc c z = (S.modelFunctorOne c.Ψ).orbitMap z := rfl

/-- **`|C_1|` is metrizable** (p. 766). -/
theorem metrizableSpace_levelOne :
    @MetrizableSpace (S.regSub 1).OrbitSpace (S.levelOneTopology hc) := by
  let := S.levelOneTopology hc
  have := (S.modelEP (S.levelOneCover hc).Ψ).X.metrizableSpace_liftOne_orbitSpace
    (S.hasParacompactOrbitSpace_model _)
  exact (S.modelOrbitHomeomorphOne hc (S.levelOneCover hc)).symm.isEmbedding.metrizableSpace

/-- `|C_1| → |C|` is continuous. -/
theorem continuous_orbitInclLevelOne :
    @Continuous _ _ (S.levelOneTopology hc) _ S.orbitInclLevelOne := by
  let := S.levelOneTopology hc
  rw [continuous_coinduced_dom]
  have h := S.orbitIncl_modelFunctorOne (S.levelOneCover hc).Ψ
  change Continuous (S.orbitInclLevelOne ∘ (S.modelFunctorOne _).orbitMap)
  rw [h]
  exact (S.lemma_17_1_15 _).2.continuous.comp (EpGroupoid.continuous_orbitIncl _)

/-! ### Theorem 17.1.28: the GCT `C¹` -/

/-- **2021 Theorem 17.1.28, p. 766, the GCT `C¹`**: the full subcategory `C_1` of the objects of
regularity `1`, with the natural metrizable topology on `|C_1|` (`hc`: the footprints of `F`
cover `|C|`). -/
def levelOneGCT : GCT.{u} where
  Obj := S.regSet 1
  Mor := C.toGroupoidStr.morOn (S.regSet 1)
  toGroupoidStr := S.regSub 1
  finite_mor x y := by
    refine Set.Finite.of_finite_image ((C.finite_mor x.1 y.1).subset ?_)
      Subtype.val_injective.injOn
    rintro _ ⟨φ, ⟨hs, ht⟩, rfl⟩
    exact ⟨congrArg Subtype.val hs, congrArg Subtype.val ht⟩
  top := S.levelOneTopology hc
  metrizable := S.metrizableSpace_levelOne hc

/-- **2021 Theorem 17.1.28, p. 766 (the GCT)**: `C¹` is the full subcategory `C_1`, and for every
covering family `|Γ_Ψ¹| : |X_Ψ¹| → |C¹|` is a homeomorphism; `|C¹|` is metrizable and
`|C¹| → |C|` is a continuous injection onto the classes of regularity `1`. -/
theorem theorem_17_1_28_gct :
    (S.levelOneGCT hc).toGroupoidStr = S.regSub 1 ∧
      (∀ c : S.CoveringFamily, @IsHomeomorph _ (S.levelOneGCT hc).toGroupoidStr.OrbitSpace _
        (S.levelOneGCT hc).top (S.modelFunctorOne c.Ψ).orbitMap) ∧
      MetrizableSpace (S.levelOneGCT hc).toGroupoidStr.OrbitSpace ∧
      @Continuous _ _ (S.levelOneGCT hc).top _ S.orbitInclLevelOne ∧
      Injective S.orbitInclLevelOne ∧
      range S.orbitInclLevelOne = C.toGroupoidStr.π '' S.regSet 1 :=
  ⟨rfl, fun c => S.isHomeomorph_modelOrbitEquivOne hc c, S.metrizableSpace_levelOne hc,
    S.continuous_orbitInclLevelOne hc, S.injective_orbitInclLevelOne,
    C.toGroupoidStr.range_orbitMap_fullSubInclusion _⟩

/-! ### Under (ZHOU): the polyfold `|C¹|` -/

/-- **`(X_Ψ¹, |Γ_Ψ¹|)`, a polyfold structure on `|C¹|`** (Definition 16.1.1) when `X_Ψ` satisfies
(ZHOU). -/
def levelOnePolyfoldStructure (c : S.CoveringFamily) (hZ : (S.modelEP c.Ψ).X.IsZhou) :
    PolyfoldStructure (S.levelOneGCT hc).toGroupoidStr.OrbitSpace :=
  ⟨(S.modelEP c.Ψ).liftOne, (S.modelPolyfoldStructure c hZ).liftOne_paracompact,
    (S.modelPolyfoldStructure c hZ).liftOne_isZhou, S.modelOrbitHomeomorphOne hc c⟩

theorem levelOnePolyfoldStructure_equiv (c c' : S.CoveringFamily)
    (hZ : (S.modelEP c.Ψ).X.IsZhou) (hZ' : (S.modelEP c'.Ψ).X.IsZhou) :
    PolyfoldStructure.Equiv (S.levelOnePolyfoldStructure hc c hZ)
      (S.levelOnePolyfoldStructure hc c' hZ') :=
  ⟨liftOneHom (S.comparisonOf c c'),
    isGeneralizedIso_liftOneHom (S.isGeneralizedIso_comparison c c'),
    S.modelOrbitEquivOne_eq_comp c c'⟩

/-- **The class of polyfold structures on `|C¹|`** under (ZHOU). -/
def levelOnePolyfoldClass (h : S.IsZhou) :
    PolyfoldClass (S.levelOneGCT hc).toGroupoidStr.OrbitSpace :=
  ⟦S.levelOnePolyfoldStructure hc h.choose h.choose_spec⟧

/-- Every covering family represents the class on `|C¹|`. -/
theorem levelOnePolyfoldClass_eq (h : S.IsZhou) (c : S.CoveringFamily) :
    (⟦S.levelOnePolyfoldStructure hc c (h.model c)⟧ :
        PolyfoldClass (S.levelOneGCT hc).toGroupoidStr.OrbitSpace) =
      S.levelOnePolyfoldClass hc h :=
  Quotient.sound (S.levelOnePolyfoldStructure_equiv hc c h.choose (h.model c) h.choose_spec)

/-- **`|C¹|` is the raised polyfold `(|C|, c_C)¹`** (§16.2): a homeomorphism
`|C¹| ≃ₜ (|C|, c_C)¹` over the inclusions into `|C|`. -/
def levelOneHomeomorphRaised (h : S.IsZhou) :
    (S.levelOneGCT hc).toGroupoidStr.OrbitSpace ≃ₜ PolyfoldClass.RaisedSpace (S.polyfoldClass h) :=
  (S.levelOnePolyfoldStructure hc h.choose h.choose_spec).β.symm.trans
    (PolyfoldClass.raiseHomeomorph (S.modelPolyfoldStructure h.choose h.choose_spec)
      (S.polyfoldClass_eq h h.choose))

theorem raiseIncl_levelOneHomeomorphRaised (h : S.IsZhou) :
    PolyfoldClass.raiseIncl (S.polyfoldClass h) ∘ S.levelOneHomeomorphRaised hc h =
      S.orbitInclLevelOne := by
  funext z
  set p := S.levelOnePolyfoldStructure hc h.choose h.choose_spec
  obtain ⟨w, rfl⟩ := p.β.surjective z
  have h1 := congrFun (PolyfoldClass.raiseIncl_raiseMap
    (S.modelPolyfoldStructure h.choose h.choose_spec) (S.polyfoldClass_eq h h.choose)) w
  have h2 := congrFun (S.orbitIncl_modelFunctorOne h.choose.Ψ) w
  simp only at h1 h2
  change PolyfoldClass.raiseIncl (S.polyfoldClass h) (PolyfoldClass.raiseHomeomorph
    (S.modelPolyfoldStructure h.choose h.choose_spec) (S.polyfoldClass_eq h h.choose)
    (p.β.symm (p.β w))) = _
  rw [Homeomorph.symm_apply_apply]
  exact h1.trans h2.symm

/-! ### Corollary 17.1.29 (model form) -/

/-- **2021 Corollary 17.1.29, p. 766 (model form)**: if `C` satisfies (ZHOU), (SLUC) or (SLR),
so does the index raise `X_Ψ¹` of every model (Propositions 7.4.8, 7.4.9; `X^{i+1} = (X¹)ⁱ`). -/
theorem corollary_17_1_29_model (c : S.CoveringFamily) :
    (S.IsZhou → (S.modelEP c.Ψ).liftOne.X.IsZhou) ∧
      (S.IsSLUC → (S.modelEP c.Ψ).liftOne.IsSLUC) ∧
      (S.IsSLR → (S.modelEP c.Ψ).liftOne.IsSLR) := by
  obtain ⟨-, hSLR, -, hSLUC, hZ⟩ := S.proposition_17_1_24 c
  refine ⟨fun h => (S.modelPolyfoldStructure c (hZ h)).liftOne_isZhou, fun h i => ?_,
    fun h i => ?_⟩
  · exact (congrArg (fun A : EP.{u} => A.X.IsLUC) (EP.lift_succ' _ i)).mp (hSLUC h (i + 1))
  · exact (congrArg (fun A : EP.{u} => A.X.IsLR) (EP.lift_succ' _ i)).mp (hSLR h (i + 1))

end GCT.PolyfoldConstruction

end Polyfold
