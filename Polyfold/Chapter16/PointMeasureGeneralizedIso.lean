import Polyfold.Chapter16.PointCountEquivalence
import Polyfold.Chapter11.MeasureGeneralizedIso

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 11,
§11.4, **Theorem 11.4.1** (p. 543; 2017: Theorem 11.8) **for dimension `n = 0`**, both
identities, as measure identities, for generalized isomorphisms.  Numbers and pages are the
2021 text's.

# The weighted counting measures along generalized isomorphisms

## The text, paraphrased

(Theorem 11.4.1) For a generalized isomorphism `f : X → Y`, oriented tame compact branched
ep⁺-subgroupoids `Θ̂` on `X`, `Θ̂'` on `Y` of dimension `n` and `K ∈ L(|supp Θ|)`,
`K' ∈ L(|supp Θ'|)`: `|f|(K) ∈ L(|supp f_*Θ|)` with `µ^Θ̂_ω(K) = µ^{f_*Θ̂}_{f_*ω}(|f|(K))`, and
`|f|(K) ∈ L(|supp Θ'|)` with `µ^{f^*Θ̂'}_{f^*ω'}(K) = µ^Θ̂'_{ω'}(|f|(K))` for `K` in
`L(|supp f^*Θ'|)`.  The proof reduces to an equivalence on a representative `X ←F A →Φ Y`.
For `n = 0` the measures are the weighted signed counts of Theorem 9.5.4 over oriented points.

## What is formalized

For the integration of `0`-forms over oriented points (`EP.zeroFormIntegration`) and the
structures with point sheets (`EpGroupoid.IsPointTame`; by `EpGroupoid.isPointTame_iff` this is
tameness of dimension `0`):

* `EpFunctor.measurable_suppMap_point`, `EpFunctor.measurableSet_preimage_val_point`: `|Φ|⁻¹`
  maps `L(|supp Θ'|)` into `L(|supp Φ^*Θ'|)` (Definition 9.5.3 with the `0`-dimensional null
  sets, of which only `∅` lies in `|supp Θ|`).
* **`EpFunctor.point_measure_span_core`**: for equivalences `F : A → X`, `G : A → Y`,
  `Θ_A = F^*Θ_X = G^*Θ_Y`, orientations moved by the transport charts, all tame of dimension `0`,
  and `F^*ω = G^*ω'`: `|G|(|F|⁻¹(K)) ∈ L(|supp Θ_Y|)` and
  `µ^{Θ̂_X}_ω(K) = µ^{Θ̂_Y}_{ω'}(|G|(|F|⁻¹(K)))`.
* `EPLocalization.Diagram.isPointTame_pullTheta`, `isPointTame_pushTheta`,
  **`Diagram.point_theorem_11_4_1_pull`**, **`Diagram.point_theorem_11_4_1_push`**: Theorem
  11.4.1 for `n = 0` and a diagram `X ←F A →Φ Y` with `Φ` an equivalence.
* `EPLocalization.EPLoc.isPointTame_push`, **`EPLoc.point_theorem_11_4_1_pull`**,
  **`EPLoc.point_theorem_11_4_1_push`**: Theorem 11.4.1 for `n = 0` and a generalized
  isomorphism `f`, in the form of Definition 11.3.6 (`OrientedBranched.pull`, `push`).
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

namespace EpFunctor

section Measurable

variable {A B : EP.{u}} {Φ : EpFunctor A.X B.X} {Θ' : B.Obj → ℚ}

/-- **`|Φ|` is measurable for the σ-algebras `L` of dimension `0`** (Definition 9.5.3). -/
theorem measurable_suppMap_point (hΘ' : B.X.IsFunctorial Θ') :
    @Measurable _ _ (A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X))
        (Φ.pullbackTheta Θ'))
      (B.X.lebesgueSigma (SheetNullSets.point (pointSheets B.X)) Θ') (suppMap (Φ := Φ) hΘ') := by
  let _ : MeasurableSpace (A.X.orbitSupp (Φ.pullbackTheta Θ')) :=
    A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) (Φ.pullbackTheta Θ')
  refine measurable_generateFrom fun t ht => ?_
  rcases ht with ht | ht
  · exact borel_le_borelNullSigma _ _ ((continuous_suppMap hΘ').borel_measurable ht)
  · rw [eq_empty_of_mem_measureZeroSets_point ht, preimage_empty]
    exact MeasurableSet.empty

/-- **`|Φ|⁻¹(K) ∈ L`** for `K ∈ L(|supp Θ'|)` and `Θ = Φ^*Θ'`, in dimension `0`. -/
theorem measurableSet_preimage_val_point (hΘ' : B.X.IsFunctorial Θ') {Θ : A.Obj → ℚ}
    (hΘeq : Φ.pullbackTheta Θ' = Θ) {K : Set (B.X.orbitSupp Θ')}
    (hK : MeasurableSet[B.X.lebesgueSigma (SheetNullSets.point (pointSheets B.X)) Θ'] K) :
    MeasurableSet[A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) Θ]
      (Subtype.val ⁻¹' (Φ.orbitMap ⁻¹' (Subtype.val '' K)) : Set (A.X.orbitSupp Θ)) := by
  subst hΘeq
  have h := measurable_suppMap_point (Φ := Φ) hΘ' hK
  convert h using 1
  ext q
  constructor
  · rintro ⟨k, hk, he⟩
    change suppMap hΘ' q ∈ K
    convert hk
    exact Subtype.ext he.symm
  · intro h
    exact ⟨_, h, rfl⟩

end Measurable

variable {C X Y : EP.{u}}

/-- **The core of Theorem 11.4.1 for `n = 0` and `X ←F A →G Y`**: for equivalences `F`, `G`,
`Θ_A = F^*Θ_X = G^*Θ_Y`, orientations moved by the transport charts of `F` and `G`, all three
tame of dimension `0` and compact, and `F^*ω = G^*ω'`:
`µ^{Θ̂_X}_ω(K) = µ^{Θ̂_Y}_{ω'}(|G|(|F|⁻¹(K)))`, with `|G|(|F|⁻¹(K)) ∈ L(|supp Θ_Y|)`. -/
theorem point_measure_span_core {F : EpFunctor C.X X.X} {G : EpFunctor C.X Y.X}
    (hF : F.IsEquivalence) (hG : G.IsEquivalence)
    {ΘA : C.Obj → ℚ} {ΘX : X.Obj → ℚ} {ΘY : Y.Obj → ℚ} {TA : C.Obj → C.X.PObj.OrTangent →₀ ℚ}
    {TX : X.Obj → X.X.PObj.OrTangent →₀ ℚ} {TY : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (heF : F.pullbackTheta ΘX = ΘA) (heG : G.pullbackTheta ΘY = ΘA)
    (hTF : F.IsTransported TA TX) (hTG : G.IsTransported TA TY)
    (hΘA : C.X.IsBranchedEpSubgroupoid ΘA) (hcptA : C.X.IsCompactBranched ΘA)
    (hTA : C.X.IsOrientation ΘA TA) (hlocA : C.X.IsPointTame ΘA TA)
    (hΘX : X.X.IsBranchedEpSubgroupoid ΘX) (hcptX : X.X.IsCompactBranched ΘX)
    (hTX : X.X.IsOrientation ΘX TX) (hlocX : X.X.IsPointTame ΘX TX)
    (hΘY : Y.X.IsBranchedEpSubgroupoid ΘY) (hcptY : Y.X.IsCompactBranched ΘY)
    (hTY : Y.X.IsOrientation ΘY TY) (hlocY : Y.X.IsPointTame ΘY TY)
    {ω : X.epFormsInfty 0} {ω' : Y.epFormsInfty 0}
    (hω : EP.epFormsInftyPullback F 0 ω = EP.epFormsInftyPullback G 0 ω')
    {K : Set (X.X.orbitSupp ΘX)}
    (hK : MeasurableSet[X.X.lebesgueSigma (SheetNullSets.point (pointSheets X.X)) ΘX] K) :
    MeasurableSet[Y.X.lebesgueSigma (SheetNullSets.point (pointSheets Y.X)) ΘY]
        (Subtype.val ⁻¹' (G.orbitMap '' (F.orbitMap ⁻¹' (Subtype.val '' K)))) ∧
      branchedMeasure X.zeroFormIntegration hΘX hcptX hTX hlocX ω K =
        branchedMeasure Y.zeroFormIntegration hΘY hcptY hTY hlocY ω'
          (Subtype.val ⁻¹' (G.orbitMap '' (F.orbitMap ⁻¹' (Subtype.val '' K)))) := by
  set KA : Set (C.X.orbitSupp ΘA) := Subtype.val ⁻¹' (F.orbitMap ⁻¹' (Subtype.val '' K))
  have hsuppA : C.X.orbitSupp ΘA = F.orbitMap ⁻¹' X.X.orbitSupp ΘX := by
    rw [← heF]; exact orbitSupp_pullbackTheta F hΘX.isFunctorial
  have hvalA : Subtype.val '' KA = F.orbitMap ⁻¹' (Subtype.val '' K) := by
    refine image_preimage_eq_of_subset ?_
    rw [Subtype.range_coe, hsuppA]
    refine preimage_mono ?_
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  have hKA : MeasurableSet[C.X.lebesgueSigma (SheetNullSets.point (pointSheets C.X)) ΘA] KA :=
    measurableSet_preimage_val_point hΘX.isFunctorial heF hK
  have hcancel : (Subtype.val ⁻¹' (F.orbitMap '' (Subtype.val '' KA)) :
      Set (X.X.orbitSupp ΘX)) = K := by
    rw [hvalA, image_preimage_eq _ hF.isHomeomorph_orbitMap.surjective,
      preimage_image_eq _ Subtype.val_injective]
  have eF := (point_measure_pull_core hF hΘX hcptX hTX hlocX heF hΘA hcptA hTA hTF hlocA ω
    hKA).2
  rw [hcancel] at eF
  have eG := point_measure_pull_core hG hΘY hcptY hTY hlocY heG hΘA hcptA hTA hTG hlocA ω' hKA
  rw [hvalA] at eG
  refine ⟨eG.1, ?_⟩
  rw [← eF, hω]
  exact eG.2

end EpFunctor

namespace EPLocalization

open EpFunctor CategoryTheory

namespace Diagram

variable {X Y : EP.{u}}

/-- **`d^*Θ̂' = F_*Φ^*Θ̂'` is tame of dimension `0`** if `Θ̂'` is. -/
theorem isPointTame_pullTheta (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {Θ' : Y.Obj → ℚ}
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ')
    (hT' : Y.X.IsOrientation Θ' T') (hloc' : Y.X.IsPointTame Θ' T') :
    X.X.IsPointTame (d.pullTheta Θ') (d.pullSection T') :=
  isPointTame_push_of_isTransported d.isEquivalence_F
    (d.Φ.isFunctorial_pullbackTheta hΘ'.isFunctorial)
    (isTransported_push d.isEquivalence_F
      (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := Y.X) _) hT').isGrHatSection)
    (EpFunctor.isPointTame_pull hΦ hΘ' hT' hloc')

/-- **`d_*Θ̂ = Φ_*F^*Θ̂` is tame of dimension `0`** if `Θ̂` is. -/
theorem isPointTame_pushTheta (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {Θ : X.Obj → ℚ}
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hΘ : X.X.IsBranchedEpSubgroupoid Θ)
    (hT : X.X.IsOrientation Θ T) (hloc : X.X.IsPointTame Θ T) :
    Y.X.IsPointTame (d.pushTheta Θ) (d.pushSection T) :=
  isPointTame_push_of_isTransported hΦ (d.F.isFunctorial_pullbackTheta hΘ.isFunctorial)
    (isTransported_push hΦ (isOrientation_pullSection d.isEquivalence_F
      (hasIndependentTangentSums (X := X.X) _) hT).isGrHatSection)
    (EpFunctor.isPointTame_pull d.isEquivalence_F hΘ hT hloc)

/-- **Theorem 11.4.1, 2021 p. 543, second identity, for `n = 0` and a diagram
`d : X ←F A →Φ Y` with `Φ` an equivalence**: for `Θ̂'` on `Y` oriented, compact and tame of
dimension `0`, `ω` with `F^*ω = Φ^*ω'` and `K ∈ L(|supp d^*Θ'|)`: `|d|(K) ∈ L(|supp Θ'|)` and
`µ^{d^*Θ̂'}_ω(K) = µ^Θ̂'_{ω'}(|d|(K))`. -/
theorem point_theorem_11_4_1_pull (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {Θ' : Y.Obj → ℚ}
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : Y.X.IsCompactBranched Θ') (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : Y.X.IsPointTame Θ' T') {ω : X.epFormsInfty 0} {ω' : Y.epFormsInfty 0}
    (hω : EP.epFormsInftyPullback d.F 0 ω = EP.epFormsInftyPullback d.Φ 0 ω')
    {K : Set (X.X.orbitSupp (d.pullTheta Θ'))}
    (hK : MeasurableSet[X.X.lebesgueSigma (SheetNullSets.point (pointSheets X.X))
      (d.pullTheta Θ')] K) :
    MeasurableSet[Y.X.lebesgueSigma (SheetNullSets.point (pointSheets Y.X)) Θ']
        (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) ∧
      branchedMeasure X.zeroFormIntegration (d.isBranchedEpSubgroupoid_pullTheta hΦ hΘ')
          (d.isCompactBranched_pullTheta hΦ hΘ'.isFunctorial hcpt')
          (d.isOrientation_dPullSection hΦ hΘ' (hasIndependentTangentSums (X := Y.X) _) hT')
          (d.isPointTame_pullTheta hΦ hΘ' hT' hloc') ω K =
        branchedMeasure Y.zeroFormIntegration hΘ' hcpt' hT' hloc' ω'
          (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) := by
  rw [orbitMap_image]
  have hind := hasIndependentTangentSums (X := Y.X) Θ'
  exact point_measure_span_core d.isEquivalence_F hΦ
    (pullbackTheta_pushforwardTheta d.isEquivalence_F.full
      (d.Φ.isFunctorial_pullbackTheta hΘ'.isFunctorial)) rfl
    (isTransported_push d.isEquivalence_F (isOrientation_pullSection hΦ hind hT').isGrHatSection)
    (isTransported_pull hΦ hT'.isGrHatSection) (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
    (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
    (isOrientation_pullSection hΦ hind hT') (EpFunctor.isPointTame_pull hΦ hΘ' hT' hloc')
    _ _ _ _ _ _ _ _ hω hK

/-- **Theorem 11.4.1, 2021 p. 543, first identity, for `n = 0` and a diagram
`d : X ←F A →Φ Y` with `Φ` an equivalence**: for `Θ̂` on `X` oriented, compact and tame of
dimension `0`, `ω'` with `Φ^*ω' = F^*ω` and `K ∈ L(|supp Θ|)`: `|d|(K) ∈ L(|supp d_*Θ|)` and
`µ^Θ̂_ω(K) = µ^{d_*Θ̂}_{ω'}(|d|(K))`. -/
theorem point_theorem_11_4_1_push (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {Θ : X.Obj → ℚ}
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hΘ : X.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.X.IsCompactBranched Θ) (hT : X.X.IsOrientation Θ T)
    (hloc : X.X.IsPointTame Θ T) {ω : X.epFormsInfty 0} {ω' : Y.epFormsInfty 0}
    (hω : EP.epFormsInftyPullback d.F 0 ω = EP.epFormsInftyPullback d.Φ 0 ω')
    {K : Set (X.X.orbitSupp Θ)}
    (hK : MeasurableSet[X.X.lebesgueSigma (SheetNullSets.point (pointSheets X.X)) Θ] K) :
    MeasurableSet[Y.X.lebesgueSigma (SheetNullSets.point (pointSheets Y.X)) (d.pushTheta Θ)]
        (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) ∧
      branchedMeasure X.zeroFormIntegration hΘ hcpt hT hloc ω K =
        branchedMeasure Y.zeroFormIntegration (d.isBranchedEpSubgroupoid_pushTheta hΦ hΘ)
          (d.isCompactBranched_pushTheta hΦ hΘ.isFunctorial hcpt)
          (d.isOrientation_dPushSection hΦ hΘ (hasIndependentTangentSums (X := X.X) _) hT)
          (d.isPointTame_pushTheta hΦ hΘ hT hloc) ω'
          (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) := by
  rw [orbitMap_image]
  have hind := hasIndependentTangentSums (X := X.X) Θ
  exact point_measure_span_core d.isEquivalence_F hΦ rfl
    (pullbackTheta_pushforwardTheta hΦ.full (d.F.isFunctorial_pullbackTheta hΘ.isFunctorial))
    (isTransported_pull d.isEquivalence_F hT.isGrHatSection)
    (isTransported_push hΦ (isOrientation_pullSection d.isEquivalence_F hind hT).isGrHatSection)
    (isBranchedEpSubgroupoid_pullbackTheta d.isEquivalence_F hΘ)
    (isCompactBranched_pullbackTheta d.isEquivalence_F hΘ.isFunctorial hcpt)
    (isOrientation_pullSection d.isEquivalence_F hind hT)
    (EpFunctor.isPointTame_pull d.isEquivalence_F hΘ hT hloc) _ _ _ _ _ _ _ _ hω hK

end Diagram

namespace EPLoc

variable {X Y : EP.{u}}

/-- **`f_*Θ̂` is tame of dimension `0`** for a generalized isomorphism `f` and `Θ̂` tame of
dimension `0`. -/
theorem isPointTame_push {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (A : OrientedBranched X)
    (hlocA : X.X.IsPointTame A.Θ A.T) :
    Y.X.IsPointTame (OrientedBranched.push hf A).Θ (OrientedBranched.push hf A).T :=
  (rep f).isPointTame_pushTheta (isEquivalence_rep_Φ hf) A.isBranchedEpSubgroupoid
    A.isOrientation hlocA

/-- **Theorem 11.4.1, 2021 p. 543 (2017: Theorem 11.8), second identity, for `n = 0`**: for a
generalized isomorphism `f : X → Y`, `Θ̂'` on `Y` oriented, compact and tame of dimension `0`, a
`0`-form `ω'` and `K ∈ L(|supp f^*Θ'|)`: `|f|(K) ∈ L(|supp Θ'|)` and
`µ^{f^*Θ̂'}_{f^*ω'}(K) = µ^Θ̂'_{ω'}(|f|(K))`. -/
theorem point_theorem_11_4_1_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    (B : OrientedBranched Y) (hcptB : Y.X.IsCompactBranched B.Θ)
    (hlocB : Y.X.IsPointTame B.Θ B.T) (ω' : Y.epFormsInfty 0)
    {K : Set (X.X.orbitSupp (OrientedBranched.pull hf B).Θ)}
    (hK : MeasurableSet[X.X.lebesgueSigma (SheetNullSets.point (pointSheets X.X))
      (OrientedBranched.pull hf B).Θ] K) :
    MeasurableSet[Y.X.lebesgueSigma (SheetNullSets.point (pointSheets Y.X)) B.Θ]
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      branchedMeasure X.zeroFormIntegration (OrientedBranched.pull hf B).isBranchedEpSubgroupoid
          ((rep f).isCompactBranched_pullTheta (isEquivalence_rep_Φ hf)
            B.isBranchedEpSubgroupoid.isFunctorial hcptB)
          (OrientedBranched.pull hf B).isOrientation (isPointTame_pull hf B hlocB)
          (formsPullback f 0 ω') K =
        branchedMeasure Y.zeroFormIntegration B.isBranchedEpSubgroupoid hcptB B.isOrientation
          hlocB ω' (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) := by
  rw [orbitMap_eq_rep]
  exact (rep f).point_theorem_11_4_1_pull (isEquivalence_rep_Φ hf) B.isBranchedEpSubgroupoid
    hcptB B.isOrientation hlocB (pullback_formsPullback f ω') hK

/-- **Theorem 11.4.1, 2021 p. 543 (2017: Theorem 11.8), first identity, for `n = 0`**: for a
generalized isomorphism `f : X → Y`, `Θ̂` on `X` oriented, compact and tame of dimension `0`, a
`0`-form `ω` and `K ∈ L(|supp Θ|)`: `|f|(K) ∈ L(|supp f_*Θ|)` and
`µ^Θ̂_ω(K) = µ^{f_*Θ̂}_{f_*ω}(|f|(K))` (`f_*` computed on the representative `rep f`). -/
theorem point_theorem_11_4_1_push {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    (A : OrientedBranched X) (hcptA : X.X.IsCompactBranched A.Θ)
    (hlocA : X.X.IsPointTame A.Θ A.T) (ω : X.epFormsInfty 0) {K : Set (X.X.orbitSupp A.Θ)}
    (hK : MeasurableSet[X.X.lebesgueSigma (SheetNullSets.point (pointSheets X.X)) A.Θ] K) :
    MeasurableSet[Y.X.lebesgueSigma (SheetNullSets.point (pointSheets Y.X))
        (OrientedBranched.push hf A).Θ]
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      branchedMeasure X.zeroFormIntegration A.isBranchedEpSubgroupoid hcptA A.isOrientation hlocA
          ω K =
        branchedMeasure Y.zeroFormIntegration (OrientedBranched.push hf A).isBranchedEpSubgroupoid
          ((rep f).isCompactBranched_pushTheta (isEquivalence_rep_Φ hf)
            A.isBranchedEpSubgroupoid.isFunctorial hcptA)
          (OrientedBranched.push hf A).isOrientation (isPointTame_push hf A hlocA)
          ((rep f).formsPush (isEquivalence_rep_Φ hf) 0 ω)
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) := by
  rw [orbitMap_eq_rep]
  exact (rep f).point_theorem_11_4_1_push (isEquivalence_rep_Φ hf) A.isBranchedEpSubgroupoid
    hcptA A.isOrientation hlocA (pullback_formsPush hf ω).symm hK

end EPLoc

end EPLocalization

end Polyfold
