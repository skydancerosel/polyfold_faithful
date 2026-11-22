import Polyfold.Chapter17.TangentUnifExamples
import Polyfold.Chapter17.BranchedOrientation
import Polyfold.Chapter17.StrongBundleStructuresExamples
import Polyfold.Chapter17.ModelPropertiesExamples
import Polyfold.Chapter10.BundleLocalRegularityPrinted
import Polyfold.Chapter16.StrongPolyfoldBundle
import Polyfold.Chapter8.SmoothRegularAssembly

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.7 (pp. 825–828): the strong polyfold bundle construction of **Definition 17.7.4** (pp.
827–828) and its bundle model, as a **strong polyfold bundle structure of Definition 16.3.1**
(p. 721) under (ZHOU) and (LR); with **Definition 7.4.5** (p. 331, (ZHOU)), **Proposition 7.4.22**
(p. 338, (ZHOU) ⇒ (LR)), **Proposition 8.4.3** (p. 382, local regularity of a strong bundle) and
**Definition 17.1.22** (p. 758) for the reflection `ℤ/2 ⋉ ℝ`.  Numbers and pages are the 2021
text's.

# The bundle model as a strong polyfold bundle structure

## The text, paraphrased

(Definition 17.7.4) A strong polyfold bundle construction `(F̄, M)` for a vector bundle GCT
`P : E → C`, compatible with a polyfold structure `(F, M)` of `C`, consists of strong bundle
uniformizers `Ψ̄ : G ⋉ K → E` over the uniformizers of `F` and strong bundle structures on the
transition sets `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` for which source, target, inversion, unit and
multiplication are sc-smooth strong bundle maps.  As in §17.1, a covering family gives the
bundle model `W_Ψ̄ → X_Ψ` (Theorem 17.1.14 for the bundle), with `|Γ̄| : |W_Ψ̄| → |E|` and
`|Γ| : |X_Ψ| → |C|` homeomorphisms over `|P|`.

(Definition 16.3.1) A strong polyfold bundle structure on `p : Y → Z` is a strong bundle
`P : W → X` over an ep-groupoid with (ZHOU), paracompact orbit space and the local regularity
property, and homeomorphisms `Γ : |W| → Y`, `γ : |X| → Z` with `p ∘ Γ = γ ∘ |P|`.
(Definition 16.3.3) Two structures are equivalent through a generalized strong bundle isomorphism
compatible with the `Γ` and `γ`.

## What is formalized

* (ZHOU) for the reflection: `EpGroupoid.Examples.isZhou_reflection` (Definition 7.4.5 for
  `ℤ/2 ⋉ ℝ`; at `0` the reflection `−1` reverses the tangent vector `(0, 1)`, so `T_0 = {1}`),
  `GCT.PolyfoldConstruction.reflection_isZhou` (Definition 17.1.22),
  `reflection_properties` ((ZHOU), (LUC), (SLUC), (LR), (SLR), Proposition 17.1.23) and
  `reflection_proposition_17_1_25` (Proposition 17.1.25 for an effective GCT with (LR) and
  non-trivial isotropy).
* `StrongPolyfoldBundleConstruction.bundleModelOrbitHomeomorph` (`|Γ̄|` as a homeomorphism),
  `isLRLocal_of_isEffective` (the bundle model of an effective polyfold with (ZHOU) has the local
  regularity property, Propositions 7.4.22 and 8.4.3).
* **Definition 16.3.1 for the bundle model**: `bundleModelStructure hZ c hLR`; its independence of
  the covering family, `bundleModelStructure_equiv` (Definition 16.3.3, through the bundle
  comparison of §17.7), and the strong polyfold bundle `bundleModelBundle hZ c hLR`
  (Definition 16.3.4) with `bundleModelBundle_eq`.
* Witness (namespace `GCT.VectorBundle.ReflectionBundle`): the trivial bundle `ℝ × ℝ → ℝ` over the
  reflection, `−1` acting by `(x, v) ↦ (−x, −v)`: `reflSingle_isLRLocal`, `reflPair_isLRLocal`,
  `reflBundleStructure`, `reflBundleStructure_equiv_pair` (the one- and two-uniformizer models
  are equivalent), and `reflBundleStructure_nondegenerate`: the morphism `(−1, 0)` of the base
  model is a non-unit automorphism of `0` that sends the fibre vector `1` to `−1`, and the base
  model is effective.

## Readings

* (ZHOU) and (LR) are taken for the polyfold construction of `C` (`S.IsZhou`, Definition
  17.1.22) and for the bundle model (`(Q.modelSEP c.Ψ).E.IsLRLocal`, Definition 8.4.2) as
  Definition 16.3.1 asks; the bundle construction alone does not supply them.  For an effective
  `C`, (ZHOU) gives (LR) of the bundle model (`isLRLocal_of_isEffective`).
-/

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

namespace EpGroupoid.Examples

open GCT.PolyfoldConstruction MPolyfold in
/-- **(ZHOU) for `ℤ/2 ⋉ ℝ`** (2021 Definition 7.4.5, p. 331), with isotropy `G_0 = ℤ/2`:
`T(−1, 0) = T(y ↦ −y)` reverses the vector `(0, 1)` of `T_0ℝ`, so `T_y = {1}` for every `y`. -/
theorem isZhou_reflection : reflectionEpGroupoid.IsZhou := by
  intro y g hg
  rw [trivialSubgroup_reflection, Subgroup.mem_bot]
  obtain ⟨⟨k, x⟩, hs, ht⟩ := g
  change x = _ at hs
  change k • x = _ at ht
  subst hs
  rcases Int.units_eq_one_or k with rfl | rfl
  · exact GroupoidStr.Isotropy.ext rfl
  · exfalso
    have hx : (rnPolyfold 1).smoothVal y = 0 := by
      have h2 : -(rnPolyfold 1).smoothVal y = (rnPolyfold 1).smoothVal y := by
        rw [← units_smul_rn_neg_one]; exact ht
      have h3 := congrFun h2 0
      funext i
      fin_cases i
      simp only [Pi.neg_apply] at h3
      change (rnPolyfold 1).smoothVal y 0 = 0
      linarith
    have hv : fstSwapTangent ∈ (rnPolyfold 1).tangentFiber ((rnPolyfold 1).smoothIncl y 1) := by
      change (rnPolyfold 1).tangentProj fstSwapTangent = _
      refine level_ext ?_
      exact basePt_fstSwapTangent.trans hx.symm
    have h1 := hg fstSwapTangent hv
    have hb : (rnPolyfold 1).smoothVal y =
        (rnPolyfold 1).levelVal 1 ((rnPolyfold 1).tangentProj fstSwapTangent) :=
      hx.trans basePt_fstSwapTangent.symm
    change reflectionEpGroupoid.tangentMor ((-1 : ℤˣ), (rnPolyfold 1).smoothVal y)
      fstSwapTangent = fstSwapTangent at h1
    rw [hb] at h1
    replace h1 : MPolyfold.tangentMap (isScSmoothMap_units_smul (-1)) fstSwapTangent =
        fstSwapTangent :=
      (tangentMor_actionEpGroupoid isScSmoothMap_units_smul
        ((reflectionEpGroupoid.mem_levelSet_src_iff _ 1).1 (MPolyfold.levelVal_mem _))
        (α := fstSwapTangent) rfl).symm.trans h1
    have h4 := congrArg (tangentChartMap (isChart_rnChart 0)) h1
    rw [tangentChartMap_tangentMap_neg, tangentChartMap_fstSwapTangent] at h4
    have h5 := congrFun (congrArg Prod.snd h4) 0
    change (-1 : ℝ) = 1 at h5
    norm_num at h5

end EpGroupoid.Examples

universe u

open EPLocalization SBLocalization SBLocalization.SEPLoc

namespace GCT.PolyfoldConstruction

open EpGroupoid.Examples

/-- **The reflection polyfold `ℤ/2 ⋉ ℝ` has (ZHOU)** (2021 Definition 17.1.22, p. 758). -/
theorem reflection_isZhou : reflectionConstruction.IsZhou :=
  (tautConstruction_hasModelProperty_iff isScSmoothMap_units_smul isGenIsoInvariant_isZhou 0).2
    isZhou_reflection

/-- **`ℤ/2 ⋉ ℝ` has (ZHOU), (LUC), (SLUC), (LR) and (SLR)** (2021 Definition 17.1.22 and
Proposition 17.1.23, p. 758), with isotropy `ℤ/2` at `0` acting effectively. -/
theorem reflection_properties :
    reflectionConstruction.IsZhou ∧ reflectionConstruction.IsLUC ∧
      reflectionConstruction.IsSLUC ∧ reflectionConstruction.IsLR ∧
      reflectionConstruction.IsSLR ∧ reflectionConstruction.IsEffective :=
  ⟨reflection_isZhou, (reflectionConstruction.proposition_17_1_23 reflection_isZhou).1,
    (reflectionConstruction.proposition_17_1_23 reflection_isZhou).2.1,
    (reflectionConstruction.proposition_17_1_23 reflection_isZhou).2.2.1,
    (reflectionConstruction.proposition_17_1_23 reflection_isZhou).2.2.2, reflection_isEffective⟩

/-- **2021 Proposition 17.1.25, p. 758, for `ℤ/2 ⋉ ℝ`**: an effective GCT with (LR) and
non-trivial isotropy; every generalized isomorphism between two models compatible with the
`|Γ|` is the comparison. -/
theorem reflection_proposition_17_1_25 (c c' : reflectionConstruction.CoveringFamily)
    {h : EPLocalization.EPLoc.localizationFunctor.obj (reflectionConstruction.modelEP c.Ψ) ⟶
      EPLocalization.EPLoc.localizationFunctor.obj (reflectionConstruction.modelEP c'.Ψ)}
    (hgen : EPLocalization.EPLoc.IsGeneralizedIso h)
    (hh : (reflectionConstruction.modelFunctor c'.Ψ).orbitMap ∘ EPLoc.orbitMap h =
      (reflectionConstruction.modelFunctor c.Ψ).orbitMap) :
    h = reflectionConstruction.comparison c c' :=
  reflectionConstruction.proposition_17_1_25_of_isZhou reflection_isZhou reflection_isEffective
    c c' hgen hh

end GCT.PolyfoldConstruction

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory GroupoidalCategory.BanachFunctor PolyfoldConstruction

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  (Q : V.StrongPolyfoldBundleConstruction S)

/-- `|Γ̄| : |W_Ψ̄| → |E|` as a homeomorphism, for a covering family (Theorem 17.1.14 for the
bundle, §17.7). -/
def bundleModelOrbitHomeomorph (c : Q.BundleCoveringFamily) :
    (Q.modelSEP c.Ψ).E.toEpGroupoid.OrbitSpace ≃ₜ V.groupoid.OrbitSpace :=
  (isHomeomorph_bundleModelOrbitMap c.cover).homeomorph

@[simp] theorem bundleModelOrbitHomeomorph_apply (c : Q.BundleCoveringFamily)
    (z : (Q.modelSEP c.Ψ).E.toEpGroupoid.OrbitSpace) :
    Q.bundleModelOrbitHomeomorph c z = (Q.bundleModelFunctor c.Ψ).orbitMap z := rfl

variable {Q} in
/-- The bundle model of an effective polyfold construction with (ZHOU) has the local regularity
property (2021 Propositions 7.4.22, p. 338, and 8.4.3, p. 382). -/
theorem isLRLocal_of_isEffective (hZ : S.IsZhou) (hE : S.IsEffective)
    (c : Q.BundleCoveringFamily) : (Q.modelSEP c.Ψ).E.IsLRLocal :=
  EpStrongBundle.proposition_8_4_3_isLRLocal (Q.modelEpStrongBundle c.Ψ) (hE.model c.base)
    ((S.modelEP c.base.Ψ).X.proposition_7_4_22_of_isZhou (hZ.model c.base))

/-- **The bundle model as a strong polyfold bundle structure** (2021 Definition 16.3.1, p. 721,
for the construction of Definition 17.7.4, pp. 827–828): the strong bundle `W_Ψ̄ → X_Ψ` of a
covering family, with (ZHOU) of `C` and the local regularity property `hLR`, `Γ = |Γ̄|`,
`γ = |Γ|`. -/
def bundleModelStructure (hZ : S.IsZhou) (c : Q.BundleCoveringFamily)
    (hLR : (Q.modelSEP c.Ψ).E.IsLRLocal) : StrongPolyfoldBundleStructure V.proj.orbitMap where
  A := Q.modelSEP c.Ψ
  isZhou := hZ.model c.base
  paracompact := S.hasParacompactOrbitSpace_model c.base
  isLRLocal := hLR
  Γ := Q.bundleModelOrbitHomeomorph c
  γ := S.modelOrbitHomeomorph c.base
  comm := Q.orbitMap_proj_comp_bundleModel c.Ψ

/-- **Two covering families give equivalent structures** (2021 Definition 16.3.3, p. 722),
through the bundle comparison of §17.7. -/
theorem bundleModelStructure_equiv (hZ : S.IsZhou) (c c' : Q.BundleCoveringFamily)
    (hLR : (Q.modelSEP c.Ψ).E.IsLRLocal) (hLR' : (Q.modelSEP c'.Ψ).E.IsLRLocal) :
    StrongPolyfoldBundleStructure.Equiv (Q.bundleModelStructure hZ c hLR)
      (Q.bundleModelStructure hZ c' hLR') := by
  refine ⟨Q.bundleComparison c c', Q.isGeneralizedIso_bundleComparison c c', ?_,
    Q.orbitMap_bundleComparison c c'⟩
  change (S.modelFunctor c'.base.Ψ).orbitMap ∘
      EPLoc.orbitMap (baseFunctor.map (Q.bundleComparison c c')) =
    (S.modelFunctor c.base.Ψ).orbitMap
  rw [Q.baseFunctor_map_bundleComparison]
  exact S.orbitMap_comparison c.base c'.base

/-- **The strong polyfold bundle `|P| : |E| → |C|`** (2021 Definition 16.3.4, p. 723) of the
bundle model. -/
def bundleModelBundle (hZ : S.IsZhou) (c : Q.BundleCoveringFamily)
    (hLR : (Q.modelSEP c.Ψ).E.IsLRLocal) : StrongPolyfoldBundle V.proj.orbitMap :=
  ⟦Q.bundleModelStructure hZ c hLR⟧

/-- The strong polyfold bundle does not depend on the covering family. -/
theorem bundleModelBundle_eq (hZ : S.IsZhou) (c c' : Q.BundleCoveringFamily)
    (hLR : (Q.modelSEP c.Ψ).E.IsLRLocal) (hLR' : (Q.modelSEP c'.Ψ).E.IsLRLocal) :
    Q.bundleModelBundle hZ c hLR = Q.bundleModelBundle hZ c' hLR' :=
  Quotient.sound (Q.bundleModelStructure_equiv hZ c c' hLR hLR')

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

namespace GCT.VectorBundle.ReflectionBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor EpGroupoid.Examples TrivialBundle
  PolyfoldConstruction StrongBundleUniformizerConstruction StrongBundleUniformizerData
  StrongPolyfoldBundleConstruction

/-- The one-uniformizer bundle model of the reflection bundle has the local regularity property. -/
theorem reflSingle_isLRLocal : (reflQ.modelSEP reflSingle.Ψ).E.IsLRLocal :=
  isLRLocal_of_isEffective reflection_isZhou reflection_isEffective reflSingle

/-- The two-uniformizer bundle model of the reflection bundle has the local regularity
property. -/
theorem reflPair_isLRLocal : (reflQ.modelSEP reflPair.Ψ).E.IsLRLocal :=
  isLRLocal_of_isEffective reflection_isZhou reflection_isEffective reflPair

/-- **The strong polyfold bundle structure of the reflection bundle** (Definition 16.3.1): the
trivial bundle `ℝ × ℝ → ℝ` over `ℤ/2 ⋉ ℝ`, `−1` acting by `(x, v) ↦ (−x, −v)`. -/
def reflBundleStructure : StrongPolyfoldBundleStructure reflV.proj.orbitMap :=
  reflQ.bundleModelStructure reflection_isZhou reflSingle reflSingle_isLRLocal

/-- The one- and two-uniformizer models of the reflection bundle are equivalent
(Definition 16.3.3). -/
theorem reflBundleStructure_equiv_pair :
    StrongPolyfoldBundleStructure.Equiv reflBundleStructure
      (reflQ.bundleModelStructure reflection_isZhou reflPair reflPair_isLRLocal) :=
  reflQ.bundleModelStructure_equiv reflection_isZhou reflSingle reflPair _ _

/-- The transition of the reflection uniformizer to itself over the element `−1` at `0`, with the
fibre vector `1`. -/
def singleTrans : reflQ.TransSpace (reflSingle.Ψ ()) (reflSingle.Ψ ()) :=
  ⟨(⟨(0 : Fin 1 → ℝ), ((-1 : ℤˣ), 0), (0 : Fin 1 → ℝ), rfl, smul_zero _⟩,
    ((0 : Fin 1 → ℝ), fun _ => 1)), rfl⟩

/-- The corresponding morphism of the bundle model `W_Ψ̄`. -/
abbrev singleMorVec := pullbackSigmaIncl (p := fun i => (reflSingle.Ψ i).1.p)
  (s := reflQ.modelSrcPiece reflSingle.Ψ) ((), ()) singleTrans

/-- **The structure is non-degenerate**: the base model is effective, and its morphism over
`(−1, 0)` is a non-unit automorphism of `0` acting on the fibre by `1 ↦ −1`. -/
theorem reflBundleStructure_nondegenerate :
    reflBundleStructure.A.X.src singleMorVec.1.1 = ⟨(), (0 : Fin 1 → ℝ)⟩ ∧
      reflBundleStructure.A.X.tgt singleMorVec.1.1 = ⟨(), (0 : Fin 1 → ℝ)⟩ ∧
      singleMorVec.1.1 ≠ reflBundleStructure.A.X.unit ⟨(), (0 : Fin 1 → ℝ)⟩ ∧
      singleMorVec.1.2 = ⟨(), ((0 : Fin 1 → ℝ), fun _ => (1 : ℝ))⟩ ∧
      reflBundleStructure.A.E.μ singleMorVec = ⟨(), ((0 : Fin 1 → ℝ), -fun _ => (1 : ℝ))⟩ ∧
      reflBundleStructure.A.X.IsEffective := by
  refine ⟨rfl, rfl, fun h => ?_, rfl, ?_, reflection_isEffective.model reflSingle.base⟩
  · have h1 := congrArg (fun φ : reflectionConstruction.ModelMor (reflQ.modelBase reflSingle.Ψ) =>
      (φ.2.mor.1 : ℤˣ)) h
    change (-1 : ℤˣ) = 1 at h1
    exact absurd h1 (by decide)
  · rw [show reflBundleStructure.A.E.μ = (reflQ.modelEpStrongBundle reflSingle.Ψ).μ from rfl,
      (reflQ.theorem_17_1_14_bundle reflSingle.Ψ).2.2 ((), ()) singleTrans]
    refine congrArg (Sigma.mk ()) ((transT_eq singleTrans).trans ?_)
    change (((-1 : ℤˣ) • (0 : Fin 1 → ℝ)), (-1 : ℤˣ) • fun _ => (1 : ℝ)) = _
    rw [units_smul_rn_neg_one, units_smul_rn_neg_one, neg_zero]

end GCT.VectorBundle.ReflectionBundle

end Polyfold
