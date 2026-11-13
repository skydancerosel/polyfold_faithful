import Polyfold.Chapter11.EffectiveMeasureEquivalence
import Polyfold.Chapter11.MeasureGeneralizedIso

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4, **Theorem 11.4.2** (p. 544, new in the 2021 edition) for generalized
isomorphisms, gap G.131.  Numbers and pages are the 2021 text's.

# The effective canonical measures along a generalized isomorphism

As `MeasureGeneralizedIso.lean`, with the effective measures of Theorem 9.5.5 (`EffectiveMeasureEquivalence.lean`); the
middle ep-groupoid `A` of `X ←F A →Φ Y` has LUC by Proposition 10.1.16.

* `measure_span_core_eff`; `Diagram.hcovL_pullTheta`, `Diagram.hcovL_pushTheta`;
  `Diagram.theorem_11_4_2_pull`, `Diagram.theorem_11_4_2_push`.
* **`EPLoc.theorem_11_4_2_pull`**, **`EPLoc.theorem_11_4_2_push`** (generalized isomorphism between
  ep-groupoids with LUC, forms `Ωⁿ_{ep,∞}`), `EPLoc.integralEff_pull`, `EPLoc.integralEff_push`.
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

/-- **The core of Theorem 11.4.2 for `X ←F A →G Y`**: for equivalences `F`, `G`,
`Θ_A = F^*Θ_X = G^*Θ_Y`, orientations moved by the transport charts of `F` and `G`, and
`F^*ω_X = G^*ω_Y`: `µ_eff^{Θ̂_X}_{ω_X}(K) = µ_eff^{Θ̂_Y}_{ω_Y}(|G|(|F|⁻¹(K)))`. -/
theorem measure_span_core_eff {F : EpFunctor A X} {G : EpFunctor A Y}
    {ΩA Ω Ω' : Type*} [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup Ω] [Module ℝ Ω]
    [AddCommGroup Ω'] [Module ℝ Ω'] {FA : A.FormEval n ΩA} {FX : X.FormEval n Ω}
    {FY : Y.FormEval n Ω'} {PF : Ω →ₗ[ℝ] ΩA} {PG : Ω' →ₗ[ℝ] ΩA}
    (hF : F.IsEquivalence) (hG : G.IsEquivalence) (hPF : FA.IsPullback FX F PF)
    (hPG : FA.IsPullback FY G PG) (hn : 0 < n) (hLA : A.IsLUC)
    {ΘA : ObjA → ℚ} {ΘX : Obj → ℚ} {ΘY : Obj' → ℚ} {TA : ObjA → A.PObj.OrTangent →₀ ℚ}
    {TX : Obj → X.PObj.OrTangent →₀ ℚ} {TY : Obj' → Y.PObj.OrTangent →₀ ℚ}
    (heF : F.pullbackTheta ΘX = ΘA) (heG : G.pullbackTheta ΘY = ΘA)
    (hTF : F.IsTransported TA TX) (hTG : G.IsTransported TA TY)
    (hΘA : A.IsBranchedEpSubgroupoid ΘA) (hcptA : A.IsCompactBranched ΘA)
    (hTA : A.IsOrientation ΘA TA)
    (hcovA : ∀ a ∈ supp ΘA, ∃ C : A.OrientedTameStructure n ΘA a,
      (∀ i, C.M i ∈ FA.sheets) ∧ C.Represents TA ∧ C.rep.HasLUC)
    (hΘX : X.IsBranchedEpSubgroupoid ΘX) (hcptX : X.IsCompactBranched ΘX)
    (hTX : X.IsOrientation ΘX TX)
    (hcovX : ∀ x ∈ supp ΘX, ∃ C : X.OrientedTameStructure n ΘX x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents TX ∧ C.rep.HasLUC)
    (hΘY : Y.IsBranchedEpSubgroupoid ΘY) (hcptY : Y.IsCompactBranched ΘY)
    (hTY : Y.IsOrientation ΘY TY)
    (hcovY : ∀ y ∈ supp ΘY, ∃ D : Y.OrientedTameStructure n ΘY y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents TY ∧ D.rep.HasLUC)
    {ω : Ω} {ω' : Ω'} (hω : PF ω = PG ω') {K : Set (X.orbitSupp ΘX)}
    (hK : MeasurableSet[X.lebesgueSigma FX.sheetNull ΘX] K) :
    MeasurableSet[Y.lebesgueSigma FY.sheetNull ΘY]
        (Subtype.val ⁻¹' (G.orbitMap '' (F.orbitMap ⁻¹' (Subtype.val '' K)))) ∧
      branchedMeasureEff (FX.sheetIntegration hn) hΘX hcptX hTX hcovX ω K =
        branchedMeasureEff (FY.sheetIntegration hn) hΘY hcptY hTY hcovY ω'
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
    measurableSet_preimage_val hF hPF hΘX.isFunctorial heF (hasTameSheetsIn_of_hcov
      (plainCov hcovA))
      (hasTameSheetsIn_of_hcov (plainCov hcovX))
        (fun x hx => let ⟨C, hC, _⟩ := hcovX x hx; ⟨C, hC⟩) hK
  have hcancel : (Subtype.val ⁻¹' (F.orbitMap '' (Subtype.val '' KA)) : Set (X.orbitSupp ΘX)) =
      K := by
    rw [hvalA, image_preimage_eq _ hF.isHomeomorph_orbitMap.surjective,
      preimage_image_eq _ Subtype.val_injective]
  have eF := (measure_pull_core_eff hF hPF hn
      ((proposition_10_1_16 hF).1 hLA) hΘX hcptX hTX hcovX heF hΘA hcptA hTA hTF hcovA ω
    hKA).2
  rw [hcancel] at eF
  have eG := measure_pull_core_eff hG hPG hn
      ((proposition_10_1_16 hG).1 hLA) hΘY hcptY hTY hcovY heG hΘA hcptA hTA hTG hcovA ω' hKA
  rw [hvalA] at eG
  refine ⟨eG.1, ?_⟩
  rw [← eF, hω]
  exact eG.2


end EpFunctor

namespace EPLocalization

open EpFunctor CategoryTheory

namespace Diagram

variable {X Y : EP.{u}} {n : ℕ}

theorem hcovL_pullTheta (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {ΩX ΩA ΩY : Type*}
    [AddCommGroup ΩX] [Module ℝ ΩX] [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup ΩY]
    [Module ℝ ΩY] {FX : X.X.FormEval n ΩX} {FA : d.A.X.FormEval n ΩA} {FY : Y.X.FormEval n ΩY}
    {PF : ΩX →ₗ[ℝ] ΩA} {PG : ΩY →ₗ[ℝ] ΩA} (hPF : FA.IsPullback FX d.F PF)
    (hPG : FA.IsPullback FY d.Φ PG) (hLX : X.X.IsLUC) {Θ' : Y.Obj → ℚ}
      {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hind' : Y.X.HasIndependentTangentSums Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T' ∧ D.rep.HasLUC) :
    ∀ x ∈ supp (d.pullTheta Θ'), ∃ C : X.X.OrientedTameStructure n (d.pullTheta Θ') x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents (d.pullSection T') ∧ C.rep.HasLUC :=
  hcovL_push d.isEquivalence_F hPF hLX (d.Φ.isFunctorial_pullbackTheta hΘ'.isFunctorial)
    (isTransported_push d.isEquivalence_F (isOrientation_pullSection hΦ hind' hT').isGrHatSection)
    (hcovL_pull hΦ hPG ((proposition_10_1_16 d.isEquivalence_F).2 hLX) hΘ'.isFunctorial
      (isOrientation_pullSection hΦ hind' hT').isGrHatSection
      (isTransported_pull hΦ hT'.isGrHatSection) hcov')


theorem hcovL_pushTheta (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {ΩX ΩA ΩY : Type*}
    [AddCommGroup ΩX] [Module ℝ ΩX] [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup ΩY]
    [Module ℝ ΩY] {FX : X.X.FormEval n ΩX} {FA : d.A.X.FormEval n ΩA} {FY : Y.X.FormEval n ΩY}
    {PF : ΩX →ₗ[ℝ] ΩA} {PG : ΩY →ₗ[ℝ] ΩA} (hPF : FA.IsPullback FX d.F PF)
    (hPG : FA.IsPullback FY d.Φ PG) (hLY : Y.X.IsLUC) {Θ : X.Obj → ℚ}
      {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hind : X.X.HasIndependentTangentSums Θ)
    (hT : X.X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T ∧ C.rep.HasLUC) :
    ∀ y ∈ supp (d.pushTheta Θ), ∃ D : Y.X.OrientedTameStructure n (d.pushTheta Θ) y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents (d.pushSection T) ∧ D.rep.HasLUC :=
  hcovL_push hΦ hPG hLY (d.F.isFunctorial_pullbackTheta hΘ.isFunctorial)
    (isTransported_push hΦ (isOrientation_pullSection d.isEquivalence_F hind hT).isGrHatSection)
    (hcovL_pull d.isEquivalence_F hPF ((proposition_10_1_16 hΦ).2 hLY) hΘ.isFunctorial
      (isOrientation_pullSection d.isEquivalence_F hind hT).isGrHatSection
      (isTransported_pull d.isEquivalence_F hT.isGrHatSection) hcov)


/-! #### Theorem 11.4.2 for a diagram -/

/-- **Theorem 11.4.2, 2021 p. 544 (new in the 2021 edition), second identity, for a diagram
`d : X ←F A →Φ Y` with `Φ` an equivalence**: `|d|(K) ∈ L(|supp Θ'|)` and
`µ_eff^{d^*Θ̂'}_{d^*ω'}(K) = µ_eff^Θ̂'_{ω'}(|d|(K))`, `d^*ω'` being any `ω` with `F^*ω = Φ^*ω'`. -/
theorem theorem_11_4_2_pull (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {ΩX ΩA ΩY : Type*}
    [AddCommGroup ΩX] [Module ℝ ΩX] [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup ΩY]
    [Module ℝ ΩY] {FX : X.X.FormEval n ΩX} {FA : d.A.X.FormEval n ΩA} {FY : Y.X.FormEval n ΩY}
    {PF : ΩX →ₗ[ℝ] ΩA} {PG : ΩY →ₗ[ℝ] ΩA} (hPF : FA.IsPullback FX d.F PF)
    (hPG : FA.IsPullback FY d.Φ PG) (hn : 0 < n)
    (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC) {Θ' : Y.Obj → ℚ}
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : Y.X.IsCompactBranched Θ') (hind' : Y.X.HasIndependentTangentSums Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T' ∧ D.rep.HasLUC)
    {ω : ΩX} {ω' : ΩY} (hω : PF ω = PG ω') {K : Set (X.X.orbitSupp (d.pullTheta Θ'))}
    (hK : MeasurableSet[X.X.lebesgueSigma FX.sheetNull (d.pullTheta Θ')] K) :
    MeasurableSet[Y.X.lebesgueSigma FY.sheetNull Θ']
        (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) ∧
      branchedMeasureEff (FX.sheetIntegration hn) (d.isBranchedEpSubgroupoid_pullTheta hΦ hΘ')
        (d.isCompactBranched_pullTheta hΦ hΘ'.isFunctorial hcpt')
        (d.isOrientation_dPullSection hΦ hΘ' hind' hT')
        (d.hcovL_pullTheta hΦ hPF hPG hLX hΘ' hind' hT' hcov') ω K =
        branchedMeasureEff (FY.sheetIntegration hn) hΘ' hcpt' hT' hcov' ω'
          (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) := by
  rw [orbitMap_image]
  exact measure_span_core_eff d.isEquivalence_F hΦ hPF hPG hn ((proposition_10_1_16 hΦ).2 hLY)
    (pullbackTheta_pushforwardTheta d.isEquivalence_F.full
      (d.Φ.isFunctorial_pullbackTheta hΘ'.isFunctorial)) rfl
    (isTransported_push d.isEquivalence_F (isOrientation_pullSection hΦ hind' hT').isGrHatSection)
    (isTransported_pull hΦ hT'.isGrHatSection) (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
    (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
    (isOrientation_pullSection hΦ hind' hT')
    (hcovL_pull hΦ hPG ((proposition_10_1_16 hΦ).2 hLY) hΘ'.isFunctorial
      (isOrientation_pullSection hΦ hind' hT').isGrHatSection
      (isTransported_pull hΦ hT'.isGrHatSection) hcov') _ _ _ _ _ _ _ _ hω hK

/-- **Theorem 11.4.2, 2021 p. 544 (new in the 2021 edition), first identity, for a diagram
`d : X ←F A →Φ Y` with `Φ` an equivalence**: `|d|(K) ∈ L(|supp d_*Θ|)` and
`µ_eff^Θ̂_ω(K) = µ_eff^{d_*Θ̂}_{d_*ω}(|d|(K))`, `d_*ω` being any `ω'` with `Φ^*ω' = F^*ω`. -/
theorem theorem_11_4_2_push (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {ΩX ΩA ΩY : Type*}
    [AddCommGroup ΩX] [Module ℝ ΩX] [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup ΩY]
    [Module ℝ ΩY] {FX : X.X.FormEval n ΩX} {FA : d.A.X.FormEval n ΩA} {FY : Y.X.FormEval n ΩY}
    {PF : ΩX →ₗ[ℝ] ΩA} {PG : ΩY →ₗ[ℝ] ΩA} (hPF : FA.IsPullback FX d.F PF)
    (hPG : FA.IsPullback FY d.Φ PG) (hn : 0 < n)
    (hLY : Y.X.IsLUC) {Θ : X.Obj → ℚ}
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hΘ : X.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.X.IsCompactBranched Θ) (hind : X.X.HasIndependentTangentSums Θ)
    (hT : X.X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T ∧ C.rep.HasLUC)
    {ω : ΩX} {ω' : ΩY} (hω : PF ω = PG ω') {K : Set (X.X.orbitSupp Θ)}
    (hK : MeasurableSet[X.X.lebesgueSigma FX.sheetNull Θ] K) :
    MeasurableSet[Y.X.lebesgueSigma FY.sheetNull (d.pushTheta Θ)]
        (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) ∧
      branchedMeasureEff (FX.sheetIntegration hn) hΘ hcpt hT hcov ω K =
        branchedMeasureEff (FY.sheetIntegration hn) (d.isBranchedEpSubgroupoid_pushTheta hΦ hΘ)
          (d.isCompactBranched_pushTheta hΦ hΘ.isFunctorial hcpt)
          (d.isOrientation_dPushSection hΦ hΘ hind hT)
          (d.hcovL_pushTheta hΦ hPF hPG hLY hΘ hind hT hcov) ω'
          (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) := by
  rw [orbitMap_image]
  exact measure_span_core_eff d.isEquivalence_F hΦ hPF hPG hn ((proposition_10_1_16 hΦ).2 hLY) rfl
    (pullbackTheta_pushforwardTheta hΦ.full (d.F.isFunctorial_pullbackTheta hΘ.isFunctorial))
    (isTransported_pull d.isEquivalence_F hT.isGrHatSection)
    (isTransported_push hΦ (isOrientation_pullSection d.isEquivalence_F hind hT).isGrHatSection)
    (isBranchedEpSubgroupoid_pullbackTheta d.isEquivalence_F hΘ)
    (isCompactBranched_pullbackTheta d.isEquivalence_F hΘ.isFunctorial hcpt)
    (isOrientation_pullSection d.isEquivalence_F hind hT)
    (hcovL_pull d.isEquivalence_F hPF ((proposition_10_1_16 hΦ).2 hLY) hΘ.isFunctorial
      (isOrientation_pullSection d.isEquivalence_F hind hT).isGrHatSection
      (isTransported_pull d.isEquivalence_F hT.isGrHatSection) hcov) _ _ _ _ _ _ _ _ hω hK


end Diagram

namespace EPLoc

variable {X Y : EP.{u}} {n : ℕ}

/-- **Theorem 11.4.2, 2021 p. 544 (new in the 2021 edition), second identity**: for a
generalized isomorphism `f : X → Y`, `Θ̂'` on `Y` oriented, tame (with sheets in the class of
`Ωⁿ_{ep,∞}`), compact, of dimension `n ≥ 1`, and `K ∈ L(|supp f^*Θ'|)`:
`|f|(K) ∈ L(|supp Θ'|)` and `µ_eff^{f^*Θ̂'}_{f^*ω'}(K) = µ_eff^Θ̂'_{ω'}(|f|(K))`. -/
theorem theorem_11_4_2_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hn : 0 < n)
    (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC)
    {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hind' : Y.X.HasIndependentTangentSums Θ') (hT' : Y.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ (Y.epFormsInftyEval n).sheets) ∧ D.Represents T' ∧
        D.rep.HasLUC)
    (ω' : Y.epFormsInfty n) {K : Set (X.X.orbitSupp (pullTheta f Θ'))}
    (hK : MeasurableSet[X.X.lebesgueSigma (X.epFormsInftyEval n).sheetNull (pullTheta f Θ')] K) :
    MeasurableSet[Y.X.lebesgueSigma (Y.epFormsInftyEval n).sheetNull Θ']
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      branchedMeasureEff ((X.epFormsInftyEval n).sheetIntegration hn)
          ((rep f).isBranchedEpSubgroupoid_pullTheta (isEquivalence_rep_Φ hf) hΘ')
          ((rep f).isCompactBranched_pullTheta (isEquivalence_rep_Φ hf) hΘ'.isFunctorial hcpt')
          ((rep f).isOrientation_dPullSection (isEquivalence_rep_Φ hf) hΘ' hind' hT')
          ((rep f).hcovL_pullTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) hLX hΘ' hind' hT' hcov')
          (formsPullback f n ω') K =
        branchedMeasureEff ((Y.epFormsInftyEval n).sheetIntegration hn) hΘ' hcpt' hT' hcov' ω'
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) := by
  rw [orbitMap_eq_rep]
  exact (rep f).theorem_11_4_2_pull (isEquivalence_rep_Φ hf)
    (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
    (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) hn hLX hLY hΘ' hcpt' hind' hT' hcov'
    (pullback_formsPullback f ω') hK

/-- **Theorem 11.4.2, 2021 p. 544 (new in the 2021 edition), first identity**: for a
generalized isomorphism `f : X → Y`, `Θ̂` on `X` oriented, tame (with sheets in the class of
`Ωⁿ_{ep,∞}`), compact, of dimension `n ≥ 1`, and `K ∈ L(|supp Θ|)`: `|f|(K) ∈ L(|supp f_*Θ|)`
and `µ_eff^Θ̂_ω(K) = µ_eff^{f_*Θ̂}_{f_*ω}(|f|(K))` (`f_*` computed on the representative `rep f`, as
`EPLoc.pushTheta`, `EPLoc.pushSection`).  Both LUC hypotheses are the book's; this
identity uses only `Y`'s (they are equivalent by Proposition 10.1.16). -/
theorem theorem_11_4_2_push {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hn : 0 < n)
    (_hLX : X.X.IsLUC) (hLY : Y.X.IsLUC)
    {Θ : X.Obj → ℚ} {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hcpt : X.X.IsCompactBranched Θ)
    (hind : X.X.HasIndependentTangentSums Θ) (hT : X.X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ (X.epFormsInftyEval n).sheets) ∧ C.Represents T ∧
        C.rep.HasLUC)
    (ω : X.epFormsInfty n) {K : Set (X.X.orbitSupp Θ)}
    (hK : MeasurableSet[X.X.lebesgueSigma (X.epFormsInftyEval n).sheetNull Θ] K) :
    MeasurableSet[Y.X.lebesgueSigma (Y.epFormsInftyEval n).sheetNull (pushTheta f Θ)]
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      branchedMeasureEff ((X.epFormsInftyEval n).sheetIntegration hn) hΘ hcpt hT hcov ω K =
        branchedMeasureEff ((Y.epFormsInftyEval n).sheetIntegration hn)
          ((rep f).isBranchedEpSubgroupoid_pushTheta (isEquivalence_rep_Φ hf) hΘ)
          ((rep f).isCompactBranched_pushTheta (isEquivalence_rep_Φ hf) hΘ.isFunctorial hcpt)
          ((rep f).isOrientation_dPushSection (isEquivalence_rep_Φ hf) hΘ hind hT)
          ((rep f).hcovL_pushTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) hLY hΘ hind hT hcov)
          ((rep f).formsPush (isEquivalence_rep_Φ hf) n ω)
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) := by
  rw [orbitMap_eq_rep]
  exact (rep f).theorem_11_4_2_push (isEquivalence_rep_Φ hf)
    (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
    (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) hn hLY hΘ hcpt hind hT hcov
    (pullback_formsPush hf ω).symm hK


/-- **Theorem 11.4.2 for the integrals** (Definition 9.5.6, `K = |supp f^*Θ'|`):
`∮_{f^*Θ̂'} f^*ω' = ∮_{Θ̂'} ω'`. -/
theorem integralEff_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hn : 0 < n)
    (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC)
    {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hind' : Y.X.HasIndependentTangentSums Θ') (hT' : Y.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ (Y.epFormsInftyEval n).sheets) ∧ D.Represents T' ∧
        D.rep.HasLUC)
    (ω' : Y.epFormsInfty n) :
    branchedIntegralEff ((X.epFormsInftyEval n).sheetIntegration hn)
          ((rep f).isBranchedEpSubgroupoid_pullTheta (isEquivalence_rep_Φ hf) hΘ')
          ((rep f).isCompactBranched_pullTheta (isEquivalence_rep_Φ hf) hΘ'.isFunctorial hcpt')
          ((rep f).isOrientation_dPullSection (isEquivalence_rep_Φ hf) hΘ' hind' hT')
          ((rep f).hcovL_pullTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) hLX hΘ' hind' hT' hcov')
          (formsPullback f n ω') =
      branchedIntegralEff ((Y.epFormsInftyEval n).sheetIntegration hn) hΘ' hcpt' hT' hcov' ω' := by
  have h := (theorem_11_4_2_pull hf hn hLX hLY hΘ' hcpt' hind' hT' hcov' ω' MeasurableSet.univ).2
  rw [image_univ, Subtype.range_coe, ← orbitSupp_eq_image_pullTheta hf hΘ',
    Subtype.coe_preimage_self] at h
  exact h

/-- **Theorem 11.4.2 for the integrals** (Definition 9.5.6, `K = |supp Θ|`):
`∮_Θ̂ ω = ∮_{f_*Θ̂} f_*ω`. -/
theorem integralEff_push {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hn : 0 < n)
    (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC)
    {Θ : X.Obj → ℚ} {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hcpt : X.X.IsCompactBranched Θ)
    (hind : X.X.HasIndependentTangentSums Θ) (hT : X.X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ (X.epFormsInftyEval n).sheets) ∧ C.Represents T ∧
        C.rep.HasLUC)
    (ω : X.epFormsInfty n) :
    branchedIntegralEff ((X.epFormsInftyEval n).sheetIntegration hn) hΘ hcpt hT hcov ω =
      branchedIntegralEff ((Y.epFormsInftyEval n).sheetIntegration hn)
          ((rep f).isBranchedEpSubgroupoid_pushTheta (isEquivalence_rep_Φ hf) hΘ)
          ((rep f).isCompactBranched_pushTheta (isEquivalence_rep_Φ hf) hΘ.isFunctorial hcpt)
          ((rep f).isOrientation_dPushSection (isEquivalence_rep_Φ hf) hΘ hind hT)
          ((rep f).hcovL_pushTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) hLY hΘ hind hT hcov)
          ((rep f).formsPush (isEquivalence_rep_Φ hf) n ω) := by
  have h := (theorem_11_4_2_push hf hn hLX hLY hΘ hcpt hind hT hcov ω MeasurableSet.univ).2
  rw [image_univ, Subtype.range_coe, ← orbitSupp_pushTheta hf hΘ.isFunctorial] at h
  unfold branchedIntegralEff
  rw [h]
  exact congrArg _ (Subtype.coe_preimage_self _)


end EPLoc

end EPLocalization

end Polyfold
