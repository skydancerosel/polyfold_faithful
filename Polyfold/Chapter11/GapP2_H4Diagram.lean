import Polyfold.Chapter11.GapP2_H4Measure
import Polyfold.Chapter11.GapP2_H4CompatInst
import Polyfold.Chapter11.GapP2_B2_GeneralizedForms

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4, **Theorem 11.4.1** (p. 543; 2017: Theorem 11.8, p. 396) for
generalized isomorphisms, and **Remark 11.4.3** (p. 545), gap G.131.  Numbers and pages are the
2021 text's.

# The canonical measures along a generalized isomorphism

The text: "if `f = [X ←F A →G Y]` we compute
`µ^{f_*Θ̂}_{f_*ω}(|f|(K)) = µ^{G_*F^*Θ̂}_{G_*F^*ω}(|f|(K))`"
using the case of an equivalence twice.

* `measure_span_core`: for equivalences `F : A → X`, `G : A → Y` and `Θ_A = F^*Θ_X = G^*Θ_Y`,
  `µ^{Θ̂_X}_{ω_X}(K) = µ^{Θ̂_Y}_{ω_Y}(|G|(|F|⁻¹(K)))` whenever `F^*ω_X = G^*ω_Y`.
* `Diagram.theorem_11_4_1_pull`, `Diagram.theorem_11_4_1_push`: Theorem 11.4.1 for a diagram
  `d : X ←F A →Φ Y` with `Φ` an equivalence, any evaluations compatible with the pull-backs.
* `EPLoc.theorem_11_4_1_pull`, `EPLoc.theorem_11_4_1_push`: Theorem 11.4.1 for a generalized
  isomorphism `f : X → Y` and the forms `Ωⁿ_{ep,∞}` (Definition 11.2.7: `f^*ω' = F_*Φ^*ω'`,
  `f_*ω = Φ_*F^*ω`), with `|f|` of Definition 10.3.7.
* `EPLoc.integral_pull`, `EPLoc.integral_push` (Remark 11.4.3 in the form used in Chapter 11: two
  ep-groupoid models of the same polyfold related by a generalized isomorphism give the same
  branched integrals).
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

namespace EpFunctor

variable {ObjA MorA Obj Mor Obj' Mor' : Type u}
  [TopologicalSpace ObjA] [T2Space ObjA] [ParacompactSpace ObjA]
  [TopologicalSpace MorA] [T2Space MorA] [ParacompactSpace MorA]
  [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {A : EpGroupoid ObjA MorA} {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {n : ℕ}

/-- **`|Φ|⁻¹(K) ∈ L`** for `K ∈ L(|supp Θ'|)` and `Θ = Φ^*Θ'`. -/
theorem measurableSet_preimage_val {Φ : EpFunctor X Y} {Ω Ω' : Type*} [AddCommGroup Ω]
    [Module ℝ Ω] [AddCommGroup Ω'] [Module ℝ Ω'] {FX : X.FormEval n Ω} {FY : Y.FormEval n Ω'}
    {P : Ω' →ₗ[ℝ] Ω} (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P) {Θ' : Obj' → ℚ}
    (hΘ' : Y.IsFunctorial Θ') {Θ : Obj → ℚ} (hΘeq : Φ.pullbackTheta Θ' = Θ)
    (hTSX : X.HasTameSheetsIn FX.sheets Θ) (hTSY : Y.HasTameSheetsIn FY.sheets Θ')
    (hcovY : ∀ y ∈ supp Θ', ∃ D : Y.OrientedTameStructure n Θ' y, ∀ i, D.M i ∈ FY.sheets)
    {K : Set (Y.orbitSupp Θ')} (hK : MeasurableSet[Y.lebesgueSigma FY.sheetNull Θ'] K) :
    MeasurableSet[X.lebesgueSigma FX.sheetNull Θ]
      (Subtype.val ⁻¹' (Φ.orbitMap ⁻¹' (Subtype.val '' K)) : Set (X.orbitSupp Θ)) := by
  subst hΘeq
  have h := measurable_suppMap hΦ hP hΘ' hTSX hTSY hcovY hK
  convert h using 1
  ext q
  constructor
  · rintro ⟨k, hk, he⟩
    change suppMap hΘ' q ∈ K
    convert hk
    exact Subtype.ext he.symm
  · intro h
    exact ⟨_, h, rfl⟩

/-- **The core of Theorem 11.4.1 for `X ←F A →G Y`**: for equivalences `F`, `G`,
`Θ_A = F^*Θ_X = G^*Θ_Y`, orientations moved by the transport charts of `F` and `G`, and
`F^*ω_X = G^*ω_Y`: `µ^{Θ̂_X}_{ω_X}(K) = µ^{Θ̂_Y}_{ω_Y}(|G|(|F|⁻¹(K)))`. -/
theorem measure_span_core {F : EpFunctor A X} {G : EpFunctor A Y}
    {ΩA Ω Ω' : Type*} [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup Ω] [Module ℝ Ω]
    [AddCommGroup Ω'] [Module ℝ Ω'] {FA : A.FormEval n ΩA} {FX : X.FormEval n Ω}
    {FY : Y.FormEval n Ω'} {PF : Ω →ₗ[ℝ] ΩA} {PG : Ω' →ₗ[ℝ] ΩA}
    (hF : F.IsEquivalence) (hG : G.IsEquivalence) (hPF : FA.IsPullback FX F PF)
    (hPG : FA.IsPullback FY G PG) (hn : 0 < n)
    {ΘA : ObjA → ℚ} {ΘX : Obj → ℚ} {ΘY : Obj' → ℚ} {TA : ObjA → A.PObj.OrTangent →₀ ℚ}
    {TX : Obj → X.PObj.OrTangent →₀ ℚ} {TY : Obj' → Y.PObj.OrTangent →₀ ℚ}
    (heF : F.pullbackTheta ΘX = ΘA) (heG : G.pullbackTheta ΘY = ΘA)
    (hTF : F.IsTransported TA TX) (hTG : G.IsTransported TA TY)
    (hΘA : A.IsBranchedEpSubgroupoid ΘA) (hcptA : A.IsCompactBranched ΘA)
    (hTA : A.IsOrientation ΘA TA)
    (hcovA : ∀ a ∈ supp ΘA, ∃ C : A.OrientedTameStructure n ΘA a,
      (∀ i, C.M i ∈ FA.sheets) ∧ C.Represents TA)
    (hΘX : X.IsBranchedEpSubgroupoid ΘX) (hcptX : X.IsCompactBranched ΘX)
    (hTX : X.IsOrientation ΘX TX)
    (hcovX : ∀ x ∈ supp ΘX, ∃ C : X.OrientedTameStructure n ΘX x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents TX)
    (hΘY : Y.IsBranchedEpSubgroupoid ΘY) (hcptY : Y.IsCompactBranched ΘY)
    (hTY : Y.IsOrientation ΘY TY)
    (hcovY : ∀ y ∈ supp ΘY, ∃ D : Y.OrientedTameStructure n ΘY y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents TY)
    {ω : Ω} {ω' : Ω'} (hω : PF ω = PG ω') {K : Set (X.orbitSupp ΘX)}
    (hK : MeasurableSet[X.lebesgueSigma FX.sheetNull ΘX] K) :
    MeasurableSet[Y.lebesgueSigma FY.sheetNull ΘY]
        (Subtype.val ⁻¹' (G.orbitMap '' (F.orbitMap ⁻¹' (Subtype.val '' K)))) ∧
      branchedMeasure (FX.sheetIntegration hn) hΘX hcptX hTX hcovX ω K =
        branchedMeasure (FY.sheetIntegration hn) hΘY hcptY hTY hcovY ω'
          (Subtype.val ⁻¹' (G.orbitMap '' (F.orbitMap ⁻¹' (Subtype.val '' K)))) := by
  set KA : Set (A.orbitSupp ΘA) := Subtype.val ⁻¹' (F.orbitMap ⁻¹' (Subtype.val '' K))
  have hsuppA : A.orbitSupp ΘA = F.orbitMap ⁻¹' X.orbitSupp ΘX := by
    rw [← heF]; exact orbitSupp_pullbackTheta F hΘX.isFunctorial
  have hvalA : Subtype.val '' KA = F.orbitMap ⁻¹' (Subtype.val '' K) := by
    refine image_preimage_eq_of_subset ?_
    rw [Subtype.range_coe, hsuppA]
    refine preimage_mono ?_
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  have hKA : MeasurableSet[A.lebesgueSigma FA.sheetNull ΘA] KA :=
    measurableSet_preimage_val hF hPF hΘX.isFunctorial heF (hasTameSheetsIn_of_hcov hcovA)
      (hasTameSheetsIn_of_hcov hcovX) (fun x hx => let ⟨C, hC, _⟩ := hcovX x hx; ⟨C, hC⟩) hK
  have hcancel : (Subtype.val ⁻¹' (F.orbitMap '' (Subtype.val '' KA)) : Set (X.orbitSupp ΘX)) =
      K := by
    rw [hvalA, image_preimage_eq _ hF.isHomeomorph_orbitMap.surjective,
      preimage_image_eq _ Subtype.val_injective]
  have eF := (measure_pull_core hF hPF hn hΘX hcptX hTX hcovX heF hΘA hcptA hTA hTF hcovA ω
    hKA).2
  rw [hcancel] at eF
  have eG := measure_pull_core hG hPG hn hΘY hcptY hTY hcovY heG hΘA hcptA hTA hTG hcovA ω' hKA
  rw [hvalA] at eG
  refine ⟨eG.1, ?_⟩
  rw [← eF, hω]
  exact eG.2

end EpFunctor

namespace EPLocalization

open EpFunctor CategoryTheory

namespace Diagram

variable {X Y : EP.{u}} {n : ℕ}

/-- `|d|(S) = |Φ|(|F|⁻¹(S))`. -/
theorem orbitMap_image (d : Diagram X Y) (S : Set X.X.OrbitSpace) :
    d.orbitMap '' S = d.Φ.orbitMap '' (d.F.orbitMap ⁻¹' S) := by
  unfold Diagram.orbitMap
  rw [image_comp,
    congrFun (IsHomeomorph.homeomorph _ d.isEquivalence_F.isHomeomorph_orbitMap).image_symm S]
  rfl

/-! #### The pull-back `d^*Θ̂' = F_*Φ^*Θ̂'` is oriented, tame, compact -/

theorem isBranchedEpSubgroupoid_pullTheta (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence)
    {Θ' : Y.Obj → ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') :
    X.X.IsBranchedEpSubgroupoid (d.pullTheta Θ') :=
  isBranchedEpSubgroupoid_pushforwardTheta d.isEquivalence_F
    (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')

theorem isCompactBranched_pullTheta (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence)
    {Θ' : Y.Obj → ℚ} (hΘ' : Y.X.IsFunctorial Θ') (hcpt' : Y.X.IsCompactBranched Θ') :
    X.X.IsCompactBranched (d.pullTheta Θ') :=
  d.F.isCompactBranched_pushforwardTheta d.isEquivalence_F.full
    (d.Φ.isFunctorial_pullbackTheta hΘ') (isCompactBranched_pullbackTheta hΦ hΘ' hcpt')

theorem isOrientation_dPullSection (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence)
    {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hind' : Y.X.HasIndependentTangentSums Θ')
    (hT' : Y.X.IsOrientation Θ' T') : X.X.IsOrientation (d.pullTheta Θ') (d.pullSection T') :=
  isOrientation_pushSection d.isEquivalence_F (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
    (hasIndependentTangentSums_pullbackTheta hΦ hind') (isOrientation_pullSection hΦ hind' hT')

theorem hcov_pullTheta (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {ΩX ΩA ΩY : Type*}
    [AddCommGroup ΩX] [Module ℝ ΩX] [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup ΩY]
    [Module ℝ ΩY] {FX : X.X.FormEval n ΩX} {FA : d.A.X.FormEval n ΩA} {FY : Y.X.FormEval n ΩY}
    {PF : ΩX →ₗ[ℝ] ΩA} {PG : ΩY →ₗ[ℝ] ΩA} (hPF : FA.IsPullback FX d.F PF)
    (hPG : FA.IsPullback FY d.Φ PG) {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hind' : Y.X.HasIndependentTangentSums Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T') :
    ∀ x ∈ supp (d.pullTheta Θ'), ∃ C : X.X.OrientedTameStructure n (d.pullTheta Θ') x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents (d.pullSection T') :=
  hcov_push d.isEquivalence_F hPF (d.Φ.isFunctorial_pullbackTheta hΘ'.isFunctorial)
    (isTransported_push d.isEquivalence_F (isOrientation_pullSection hΦ hind' hT').isGrHatSection)
    (hcov_pull hΦ hPG hΘ'.isFunctorial (isOrientation_pullSection hΦ hind' hT').isGrHatSection
      (isTransported_pull hΦ hT'.isGrHatSection) hcov')

/-! #### The push-forward `d_*Θ̂ = Φ_*F^*Θ̂` is oriented, tame, compact -/

theorem isBranchedEpSubgroupoid_pushTheta (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence)
    {Θ : X.Obj → ℚ} (hΘ : X.X.IsBranchedEpSubgroupoid Θ) :
    Y.X.IsBranchedEpSubgroupoid (d.pushTheta Θ) :=
  isBranchedEpSubgroupoid_pushforwardTheta hΦ
    (isBranchedEpSubgroupoid_pullbackTheta d.isEquivalence_F hΘ)

theorem isCompactBranched_pushTheta (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence)
    {Θ : X.Obj → ℚ} (hΘ : X.X.IsFunctorial Θ) (hcpt : X.X.IsCompactBranched Θ) :
    Y.X.IsCompactBranched (d.pushTheta Θ) :=
  d.Φ.isCompactBranched_pushforwardTheta hΦ.full (d.F.isFunctorial_pullbackTheta hΘ)
    (isCompactBranched_pullbackTheta d.isEquivalence_F hΘ hcpt)

theorem isOrientation_dPushSection (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence)
    {Θ : X.Obj → ℚ} {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hind : X.X.HasIndependentTangentSums Θ)
    (hT : X.X.IsOrientation Θ T) : Y.X.IsOrientation (d.pushTheta Θ) (d.pushSection T) :=
  isOrientation_pushSection hΦ (isBranchedEpSubgroupoid_pullbackTheta d.isEquivalence_F hΘ)
    (hasIndependentTangentSums_pullbackTheta d.isEquivalence_F hind)
    (isOrientation_pullSection d.isEquivalence_F hind hT)

theorem hcov_pushTheta (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {ΩX ΩA ΩY : Type*}
    [AddCommGroup ΩX] [Module ℝ ΩX] [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup ΩY]
    [Module ℝ ΩY] {FX : X.X.FormEval n ΩX} {FA : d.A.X.FormEval n ΩA} {FY : Y.X.FormEval n ΩY}
    {PF : ΩX →ₗ[ℝ] ΩA} {PG : ΩY →ₗ[ℝ] ΩA} (hPF : FA.IsPullback FX d.F PF)
    (hPG : FA.IsPullback FY d.Φ PG) {Θ : X.Obj → ℚ} {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hind : X.X.HasIndependentTangentSums Θ)
    (hT : X.X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T) :
    ∀ y ∈ supp (d.pushTheta Θ), ∃ D : Y.X.OrientedTameStructure n (d.pushTheta Θ) y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents (d.pushSection T) :=
  hcov_push hΦ hPG (d.F.isFunctorial_pullbackTheta hΘ.isFunctorial)
    (isTransported_push hΦ (isOrientation_pullSection d.isEquivalence_F hind hT).isGrHatSection)
    (hcov_pull d.isEquivalence_F hPF hΘ.isFunctorial
      (isOrientation_pullSection d.isEquivalence_F hind hT).isGrHatSection
      (isTransported_pull d.isEquivalence_F hT.isGrHatSection) hcov)

/-! #### Theorem 11.4.1 for a diagram -/

/-- **Theorem 11.4.1, 2021 p. 543 (2017: Theorem 11.8, p. 396), second identity, for a diagram
`d : X ←F A →Φ Y` with `Φ` an equivalence**: `|d|(K) ∈ L(|supp Θ'|)` and
`µ^{d^*Θ̂'}_{d^*ω'}(K) = µ^Θ̂'_{ω'}(|d|(K))`, `d^*ω'` being any `ω` with `F^*ω = Φ^*ω'`. -/
theorem theorem_11_4_1_pull (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {ΩX ΩA ΩY : Type*}
    [AddCommGroup ΩX] [Module ℝ ΩX] [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup ΩY]
    [Module ℝ ΩY] {FX : X.X.FormEval n ΩX} {FA : d.A.X.FormEval n ΩA} {FY : Y.X.FormEval n ΩY}
    {PF : ΩX →ₗ[ℝ] ΩA} {PG : ΩY →ₗ[ℝ] ΩA} (hPF : FA.IsPullback FX d.F PF)
    (hPG : FA.IsPullback FY d.Φ PG) (hn : 0 < n) {Θ' : Y.Obj → ℚ}
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : Y.X.IsCompactBranched Θ') (hind' : Y.X.HasIndependentTangentSums Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T')
    {ω : ΩX} {ω' : ΩY} (hω : PF ω = PG ω') {K : Set (X.X.orbitSupp (d.pullTheta Θ'))}
    (hK : MeasurableSet[X.X.lebesgueSigma FX.sheetNull (d.pullTheta Θ')] K) :
    MeasurableSet[Y.X.lebesgueSigma FY.sheetNull Θ']
        (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) ∧
      branchedMeasure (FX.sheetIntegration hn) (d.isBranchedEpSubgroupoid_pullTheta hΦ hΘ')
        (d.isCompactBranched_pullTheta hΦ hΘ'.isFunctorial hcpt')
        (d.isOrientation_dPullSection hΦ hΘ' hind' hT')
        (d.hcov_pullTheta hΦ hPF hPG hΘ' hind' hT' hcov') ω K =
        branchedMeasure (FY.sheetIntegration hn) hΘ' hcpt' hT' hcov' ω'
          (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) := by
  rw [orbitMap_image]
  exact measure_span_core d.isEquivalence_F hΦ hPF hPG hn
    (pullbackTheta_pushforwardTheta d.isEquivalence_F.full
      (d.Φ.isFunctorial_pullbackTheta hΘ'.isFunctorial)) rfl
    (isTransported_push d.isEquivalence_F (isOrientation_pullSection hΦ hind' hT').isGrHatSection)
    (isTransported_pull hΦ hT'.isGrHatSection) (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
    (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
    (isOrientation_pullSection hΦ hind' hT')
    (hcov_pull hΦ hPG hΘ'.isFunctorial (isOrientation_pullSection hΦ hind' hT').isGrHatSection
      (isTransported_pull hΦ hT'.isGrHatSection) hcov') _ _ _ _ _ _ _ _ hω hK

/-- **Theorem 11.4.1, 2021 p. 543 (2017: Theorem 11.8, p. 396), first identity, for a diagram
`d : X ←F A →Φ Y` with `Φ` an equivalence**: `|d|(K) ∈ L(|supp d_*Θ|)` and
`µ^Θ̂_ω(K) = µ^{d_*Θ̂}_{d_*ω}(|d|(K))`, `d_*ω` being any `ω'` with `Φ^*ω' = F^*ω`. -/
theorem theorem_11_4_1_push (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {ΩX ΩA ΩY : Type*}
    [AddCommGroup ΩX] [Module ℝ ΩX] [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup ΩY]
    [Module ℝ ΩY] {FX : X.X.FormEval n ΩX} {FA : d.A.X.FormEval n ΩA} {FY : Y.X.FormEval n ΩY}
    {PF : ΩX →ₗ[ℝ] ΩA} {PG : ΩY →ₗ[ℝ] ΩA} (hPF : FA.IsPullback FX d.F PF)
    (hPG : FA.IsPullback FY d.Φ PG) (hn : 0 < n) {Θ : X.Obj → ℚ}
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hΘ : X.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.X.IsCompactBranched Θ) (hind : X.X.HasIndependentTangentSums Θ)
    (hT : X.X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T)
    {ω : ΩX} {ω' : ΩY} (hω : PF ω = PG ω') {K : Set (X.X.orbitSupp Θ)}
    (hK : MeasurableSet[X.X.lebesgueSigma FX.sheetNull Θ] K) :
    MeasurableSet[Y.X.lebesgueSigma FY.sheetNull (d.pushTheta Θ)]
        (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) ∧
      branchedMeasure (FX.sheetIntegration hn) hΘ hcpt hT hcov ω K =
        branchedMeasure (FY.sheetIntegration hn) (d.isBranchedEpSubgroupoid_pushTheta hΦ hΘ)
          (d.isCompactBranched_pushTheta hΦ hΘ.isFunctorial hcpt)
          (d.isOrientation_dPushSection hΦ hΘ hind hT)
          (d.hcov_pushTheta hΦ hPF hPG hΘ hind hT hcov) ω'
          (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) := by
  rw [orbitMap_image]
  exact measure_span_core d.isEquivalence_F hΦ hPF hPG hn rfl
    (pullbackTheta_pushforwardTheta hΦ.full (d.F.isFunctorial_pullbackTheta hΘ.isFunctorial))
    (isTransported_pull d.isEquivalence_F hT.isGrHatSection)
    (isTransported_push hΦ (isOrientation_pullSection d.isEquivalence_F hind hT).isGrHatSection)
    (isBranchedEpSubgroupoid_pullbackTheta d.isEquivalence_F hΘ)
    (isCompactBranched_pullbackTheta d.isEquivalence_F hΘ.isFunctorial hcpt)
    (isOrientation_pullSection d.isEquivalence_F hind hT)
    (hcov_pull d.isEquivalence_F hPF hΘ.isFunctorial
      (isOrientation_pullSection d.isEquivalence_F hind hT).isGrHatSection
      (isTransported_pull d.isEquivalence_F hT.isGrHatSection) hcov) _ _ _ _ _ _ _ _ hω hK

end Diagram

/-! #### Theorem 11.4.1 for a generalized isomorphism and the forms `Ωⁿ_{ep,∞}` -/

namespace EPLoc

variable {X Y : EP.{u}} {n : ℕ}

theorem orbitMap_eq_rep (f : of X ⟶ of Y) : orbitMap f = (rep f).orbitMap := by
  conv_lhs => rw [← homMk_rep f]
  rfl

theorem formsPullback_eq_rep (f : of X ⟶ of Y) (k : ℕ) :
    formsPullback f k = (rep f).formsPullback k := by
  conv_lhs => rw [← homMk_rep f]
  rfl

/-- `F^*(f^*ω') = Φ^*ω'` on a representative `X ←F A →Φ Y`. -/
theorem pullback_formsPullback (f : of X ⟶ of Y) (ω' : Y.epFormsInfty n) :
    EP.epFormsInftyPullback (rep f).F n (formsPullback f n ω') =
      EP.epFormsInftyPullback (rep f).Φ n ω' := by
  rw [formsPullback_eq_rep]
  exact EP.epFormsInftyPullback_epFormsInftyPush (rep f).isEquivalence_F n _

/-- `Φ^*(f_*ω) = F^*ω` on a representative `X ←F A →Φ Y`. -/
theorem pullback_formsPush {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (ω : X.epFormsInfty n) :
    EP.epFormsInftyPullback (rep f).Φ n ((rep f).formsPush (isEquivalence_rep_Φ hf) n ω) =
      EP.epFormsInftyPullback (rep f).F n ω :=
  EP.epFormsInftyPullback_epFormsInftyPush (isEquivalence_rep_Φ hf) n _

/-- **Theorem 11.4.1, 2021 p. 543 (2017: Theorem 11.8, p. 396), second identity**: for a
generalized isomorphism `f : X → Y`, `Θ̂'` on `Y` oriented, tame (with sheets in the class of
`Ωⁿ_{ep,∞}`), compact, of dimension `n ≥ 1`, and `K ∈ L(|supp f^*Θ'|)`:
`|f|(K) ∈ L(|supp Θ'|)` and `µ^{f^*Θ̂'}_{f^*ω'}(K) = µ^Θ̂'_{ω'}(|f|(K))`. -/
theorem theorem_11_4_1_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hn : 0 < n)
    {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hind' : Y.X.HasIndependentTangentSums Θ') (hT' : Y.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ (Y.epFormsInftyEval n).sheets) ∧ D.Represents T')
    (ω' : Y.epFormsInfty n) {K : Set (X.X.orbitSupp (pullTheta f Θ'))}
    (hK : MeasurableSet[X.X.lebesgueSigma (X.epFormsInftyEval n).sheetNull (pullTheta f Θ')] K) :
    MeasurableSet[Y.X.lebesgueSigma (Y.epFormsInftyEval n).sheetNull Θ']
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      branchedMeasure ((X.epFormsInftyEval n).sheetIntegration hn)
          ((rep f).isBranchedEpSubgroupoid_pullTheta (isEquivalence_rep_Φ hf) hΘ')
          ((rep f).isCompactBranched_pullTheta (isEquivalence_rep_Φ hf) hΘ'.isFunctorial hcpt')
          ((rep f).isOrientation_dPullSection (isEquivalence_rep_Φ hf) hΘ' hind' hT')
          ((rep f).hcov_pullTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) hΘ' hind' hT' hcov')
          (formsPullback f n ω') K =
        branchedMeasure ((Y.epFormsInftyEval n).sheetIntegration hn) hΘ' hcpt' hT' hcov' ω'
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) := by
  rw [orbitMap_eq_rep]
  exact (rep f).theorem_11_4_1_pull (isEquivalence_rep_Φ hf)
    (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
    (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) hn hΘ' hcpt' hind' hT' hcov'
    (pullback_formsPullback f ω') hK

/-- **Theorem 11.4.1, 2021 p. 543 (2017: Theorem 11.8, p. 396), first identity**: for a
generalized isomorphism `f : X → Y`, `Θ̂` on `X` oriented, tame (with sheets in the class of
`Ωⁿ_{ep,∞}`), compact, of dimension `n ≥ 1`, and `K ∈ L(|supp Θ|)`: `|f|(K) ∈ L(|supp f_*Θ|)`
and `µ^Θ̂_ω(K) = µ^{f_*Θ̂}_{f_*ω}(|f|(K))` (`f_*` computed on the representative `rep f`, as
`EPLoc.pushTheta`, `EPLoc.pushSection`). -/
theorem theorem_11_4_1_push {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hn : 0 < n)
    {Θ : X.Obj → ℚ} {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hcpt : X.X.IsCompactBranched Θ)
    (hind : X.X.HasIndependentTangentSums Θ) (hT : X.X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ (X.epFormsInftyEval n).sheets) ∧ C.Represents T)
    (ω : X.epFormsInfty n) {K : Set (X.X.orbitSupp Θ)}
    (hK : MeasurableSet[X.X.lebesgueSigma (X.epFormsInftyEval n).sheetNull Θ] K) :
    MeasurableSet[Y.X.lebesgueSigma (Y.epFormsInftyEval n).sheetNull (pushTheta f Θ)]
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      branchedMeasure ((X.epFormsInftyEval n).sheetIntegration hn) hΘ hcpt hT hcov ω K =
        branchedMeasure ((Y.epFormsInftyEval n).sheetIntegration hn)
          ((rep f).isBranchedEpSubgroupoid_pushTheta (isEquivalence_rep_Φ hf) hΘ)
          ((rep f).isCompactBranched_pushTheta (isEquivalence_rep_Φ hf) hΘ.isFunctorial hcpt)
          ((rep f).isOrientation_dPushSection (isEquivalence_rep_Φ hf) hΘ hind hT)
          ((rep f).hcov_pushTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) hΘ hind hT hcov)
          ((rep f).formsPush (isEquivalence_rep_Φ hf) n ω)
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) := by
  rw [orbitMap_eq_rep]
  exact (rep f).theorem_11_4_1_push (isEquivalence_rep_Φ hf)
    (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
    (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) hn hΘ hcpt hind hT hcov
    (pullback_formsPush hf ω).symm hK

/-- `|supp Θ'| = |f|(|supp f^*Θ'|)`. -/
theorem orbitSupp_eq_image_pullTheta {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {Θ' : Y.Obj → ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') :
    Y.X.orbitSupp Θ' = orbitMap f '' X.X.orbitSupp (pullTheta f Θ') := by
  rw [← orbitSupp_pushTheta hf (theorem_11_3_3_two hf hΘ').isFunctorial,
    pushTheta_pullTheta hf hΘ'.isFunctorial]

/-- **Theorem 11.4.1 for the integrals** (Definition 9.5.6, `K = |supp f^*Θ'|`):
`∫_{f^*Θ̂'} f^*ω' = ∫_{Θ̂'} ω'`. -/
theorem integral_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hn : 0 < n)
    {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hind' : Y.X.HasIndependentTangentSums Θ') (hT' : Y.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ (Y.epFormsInftyEval n).sheets) ∧ D.Represents T')
    (ω' : Y.epFormsInfty n) :
    branchedIntegral ((X.epFormsInftyEval n).sheetIntegration hn)
          ((rep f).isBranchedEpSubgroupoid_pullTheta (isEquivalence_rep_Φ hf) hΘ')
          ((rep f).isCompactBranched_pullTheta (isEquivalence_rep_Φ hf) hΘ'.isFunctorial hcpt')
          ((rep f).isOrientation_dPullSection (isEquivalence_rep_Φ hf) hΘ' hind' hT')
          ((rep f).hcov_pullTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) hΘ' hind' hT' hcov')
          (formsPullback f n ω') =
      branchedIntegral ((Y.epFormsInftyEval n).sheetIntegration hn) hΘ' hcpt' hT' hcov' ω' := by
  have h := (theorem_11_4_1_pull hf hn hΘ' hcpt' hind' hT' hcov' ω' MeasurableSet.univ).2
  rw [image_univ, Subtype.range_coe, ← orbitSupp_eq_image_pullTheta hf hΘ',
    Subtype.coe_preimage_self] at h
  exact h

/-- **Theorem 11.4.1 for the integrals** (Definition 9.5.6, `K = |supp Θ|`):
`∫_Θ̂ ω = ∫_{f_*Θ̂} f_*ω`. -/
theorem integral_push {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hn : 0 < n)
    {Θ : X.Obj → ℚ} {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hcpt : X.X.IsCompactBranched Θ)
    (hind : X.X.HasIndependentTangentSums Θ) (hT : X.X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ (X.epFormsInftyEval n).sheets) ∧ C.Represents T)
    (ω : X.epFormsInfty n) :
    branchedIntegral ((X.epFormsInftyEval n).sheetIntegration hn) hΘ hcpt hT hcov ω =
      branchedIntegral ((Y.epFormsInftyEval n).sheetIntegration hn)
          ((rep f).isBranchedEpSubgroupoid_pushTheta (isEquivalence_rep_Φ hf) hΘ)
          ((rep f).isCompactBranched_pushTheta (isEquivalence_rep_Φ hf) hΘ.isFunctorial hcpt)
          ((rep f).isOrientation_dPushSection (isEquivalence_rep_Φ hf) hΘ hind hT)
          ((rep f).hcov_pushTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) hΘ hind hT hcov)
          ((rep f).formsPush (isEquivalence_rep_Φ hf) n ω) := by
  have h := (theorem_11_4_1_push hf hn hΘ hcpt hind hT hcov ω MeasurableSet.univ).2
  rw [image_univ, Subtype.range_coe, ← orbitSupp_pushTheta hf hΘ.isFunctorial] at h
  unfold branchedIntegral
  rw [h]
  exact congrArg _ (Subtype.coe_preimage_self _)

/-- **Remark 11.4.3, 2021 p. 544 (2017: p. 397), the measure on a polyfold**: let
`β : |X| → Z`, `β' : |Y| → Z` with `β' ∘ |f| = β` for a generalized isomorphism `f : X → Y`
(equivalent polyfold structures on `Z`), `Θ̂'` oriented, tame, compact on `Y`, `ω'` on `Y`, and
`(X, β, f^*Θ̂', f^*ω')` the equivalent representative.  For `B ⊆ Z` with `β⁻¹(B) ∩ |supp f^*Θ'|`
measurable, `µ^{f^*Θ̂'}_{f^*ω'}(β⁻¹(B)) = µ^Θ̂'_{ω'}(β'⁻¹(B))`: the signed measure
`µ^{[(X,β),Θ̂]}_{[(X,β),ω]}` on `S ⊆ Z` does not depend on the representative. -/
theorem remark_11_4_3 {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hn : 0 < n)
    {Z : Type*} (β : X.X.OrbitSpace → Z) (β' : Y.X.OrbitSpace → Z) (hβ : β' ∘ orbitMap f = β)
    {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hind' : Y.X.HasIndependentTangentSums Θ') (hT' : Y.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ (Y.epFormsInftyEval n).sheets) ∧ D.Represents T')
    (ω' : Y.epFormsInfty n) {B : Set Z}
    (hB : MeasurableSet[X.X.lebesgueSigma (X.epFormsInftyEval n).sheetNull (pullTheta f Θ')]
      (Subtype.val ⁻¹' (β ⁻¹' B))) :
    MeasurableSet[Y.X.lebesgueSigma (Y.epFormsInftyEval n).sheetNull Θ']
        (Subtype.val ⁻¹' (β' ⁻¹' B)) ∧
      branchedMeasure ((X.epFormsInftyEval n).sheetIntegration hn)
          ((rep f).isBranchedEpSubgroupoid_pullTheta (isEquivalence_rep_Φ hf) hΘ')
          ((rep f).isCompactBranched_pullTheta (isEquivalence_rep_Φ hf) hΘ'.isFunctorial hcpt')
          ((rep f).isOrientation_dPullSection (isEquivalence_rep_Φ hf) hΘ' hind' hT')
          ((rep f).hcov_pullTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) hΘ' hind' hT' hcov')
          (formsPullback f n ω') (Subtype.val ⁻¹' (β ⁻¹' B)) =
        branchedMeasure ((Y.epFormsInftyEval n).sheetIntegration hn) hΘ' hcpt' hT' hcov' ω'
          (Subtype.val ⁻¹' (β' ⁻¹' B)) := by
  have hset : (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val ''
      (Subtype.val ⁻¹' (β ⁻¹' B) : Set (X.X.orbitSupp (pullTheta f Θ'))))) :
        Set (Y.X.orbitSupp Θ')) = Subtype.val ⁻¹' (β' ⁻¹' B) := by
    ext q'
    constructor
    · rintro ⟨p, ⟨q, hq, rfl⟩, he⟩
      change β' q'.1 ∈ B
      rw [← he]
      change (β' ∘ orbitMap f) q.1 ∈ B
      rw [hβ]
      exact hq
    · intro h
      obtain ⟨p, hp, he⟩ := (orbitSupp_eq_image_pullTheta hf hΘ').subset q'.2
      refine ⟨p, ⟨⟨p, hp⟩, ?_, rfl⟩, he⟩
      change β p ∈ B
      rw [← hβ]
      change β' (orbitMap f p) ∈ B
      rw [he]
      exact h
  have h := theorem_11_4_1_pull hf hn hΘ' hcpt' hind' hT' hcov' ω' hB
  rw [hset] at h
  exact h

end EPLoc

end EPLocalization

end Polyfold
