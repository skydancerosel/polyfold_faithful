import Polyfold.Chapter11.GapP2_H4Bd
import Polyfold.Chapter11.GapP2_H4Diagram

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4, **Theorems 11.4.4 and 11.4.5** (p. 545, new in the 2021 edition)
for generalized isomorphisms, gap G.131.  Numbers and pages are the 2021 text's.

# The canonical boundary measures along a generalized isomorphism

As `GapP2_H4Diagram.lean`, with the boundary measures of Theorems 9.5.15 and 9.5.16
(`GapP2_H4Bd.lean`): for `X ←F A →Φ Y`, the equivalence case is used along `F` and along `Φ`.

* `measure_span_core_bd`;
* `Diagram.hcovB_pullTheta`, `Diagram.hcovB_pushTheta` (E7's `hcov` for `d^*Θ̂'`, `d_*Θ̂`),
  `Diagram.isNDimensional_dPullTheta`, `Diagram.isNDimensional_dPushTheta`;
* `Diagram.theorem_11_4_4_pull`, `_push`, `Diagram.theorem_11_4_5_pull`, `_push`;
* **`EPLoc.theorem_11_4_4_pull`**, **`EPLoc.theorem_11_4_4_push`**,
  **`EPLoc.theorem_11_4_5_pull`**, **`EPLoc.theorem_11_4_5_push`** (generalized isomorphisms,
  forms `Ωᵐ_{ep,∞}` of degree `m = n - 1`).
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
  {A : EpGroupoid ObjA MorA} {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {m : ℕ}

/-- **The core of Theorems 11.4.4 and 11.4.5 for `X ←F A →G Y`**: for equivalences `F`, `G`,
`Θ_A = F^*Θ_X = G^*Θ_Y`, orientations moved by the transport charts, `F^*ω_X = G^*ω_Y`, and three
measures with the local formulas of Theorem 9.5.15 whose normalizations agree along transport
charts: `µ_X(K) = µ_Y(|G|(|F|⁻¹(K)))`. -/
theorem measure_span_core_bd {F : EpFunctor A X} {G : EpFunctor A Y}
    {ΩA Ω Ω' : Type*} [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup Ω] [Module ℝ Ω]
    [AddCommGroup Ω'] [Module ℝ Ω'] {FA : A.FormEval m ΩA} {FX : X.FormEval m Ω}
    {FY : Y.FormEval m Ω'} {PF : Ω →ₗ[ℝ] ΩA} {PG : Ω' →ₗ[ℝ] ΩA}
    (hF : F.IsEquivalence) (hG : G.IsEquivalence) (hPF : FA.IsPullback FX F PF)
    (hPG : FA.IsPullback FY G PG) (hm : 0 < m)
    {ΘA : ObjA → ℚ} {ΘX : Obj → ℚ} {ΘY : Obj' → ℚ} {TA : ObjA → A.PObj.OrTangent →₀ ℚ}
    {TX : Obj → X.PObj.OrTangent →₀ ℚ} {TY : Obj' → Y.PObj.OrTangent →₀ ℚ}
    (heF : F.pullbackTheta ΘX = ΘA) (heG : G.pullbackTheta ΘY = ΘA)
    (hTF : F.IsTransported TA TX) (hTG : G.IsTransported TA TY)
    (hΘA : A.IsBranchedEpSubgroupoid ΘA) (hcptA : A.IsCompactBranched ΘA)
    (hTA : A.IsOrientation ΘA TA)
    (hΘX : X.IsBranchedEpSubgroupoid ΘX) (hndX : X.IsNDimensional ΘX (m + 1))
    (hcovX : ∀ x ∈ supp (X.boundaryTheta ΘX), ∃ C : X.OrientedTameStructure (m + 1) ΘX x,
      C.Represents TX ∧ ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ FX.msheets)
    (hΘY : Y.IsBranchedEpSubgroupoid ΘY) (hndY : Y.IsNDimensional ΘY (m + 1))
    (hcovY : ∀ y ∈ supp (Y.boundaryTheta ΘY), ∃ D : Y.OrientedTameStructure (m + 1) ΘY y,
      D.Represents TY ∧ ∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ FY.msheets)
    (cA : ObjA → ℝ) (cX : Obj → ℝ) (cY : Obj' → ℝ)
    (hcF : ∀ {a : ObjA} {x : Obj} (Tc : F.TransportChart a x) (R : A.NaturalRep a)
      (R' : X.NaturalRep x), R.U ⊆ Tc.W → R'.U = Tc.Q '' R.U → cA a = cX x)
    (hcG : ∀ {a : ObjA} {y : Obj'} (Tc : G.TransportChart a y) (R : A.NaturalRep a)
      (R' : Y.NaturalRep y), R.U ⊆ Tc.W → R'.U = Tc.Q '' R.U → cA a = cY y)
    {ω : Ω} {ω' : Ω'} (hω : PF ω = PG ω')
    (μA : @SignedMeasure (A.orbitSupp (A.boundaryTheta ΘA))
      (A.lebesgueSigmaBoundaryH (m + 1) ΘA))
    (μX : @SignedMeasure (X.orbitSupp (X.boundaryTheta ΘX))
      (X.lebesgueSigmaBoundaryH (m + 1) ΘX))
    (μY : @SignedMeasure (Y.orbitSupp (Y.boundaryTheta ΘY))
      (Y.lebesgueSigmaBoundaryH (m + 1) ΘY))
    (hμA : ∀ (a : ObjA) (C : A.OrientedTameStructure (m + 1) ΘA a) (hCT : C.Represents TA),
      a ∈ supp (A.boundaryTheta ΘA) →
      (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ FA.msheets) →
      ∀ K, MeasurableSet[A.lebesgueSigmaBoundaryH (m + 1) ΘA] K →
        Subtype.val '' K ⊆ A.π '' C.U →
        μA K = cA a * (C.boundaryFamily hΘA hCT).nonemptyPart.sheetSum (FA.msheetIntegration hm)
          (PF ω) (A.π ⁻¹' (Subtype.val '' K)))
    (hμX : ∀ (x : Obj) (C : X.OrientedTameStructure (m + 1) ΘX x) (hCT : C.Represents TX),
      x ∈ supp (X.boundaryTheta ΘX) →
      (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ FX.msheets) →
      ∀ K, MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) ΘX] K →
        Subtype.val '' K ⊆ X.π '' C.U →
        μX K = cX x * (C.boundaryFamily hΘX hCT).nonemptyPart.sheetSum (FX.msheetIntegration hm)
          ω (X.π ⁻¹' (Subtype.val '' K)))
    (hμY : ∀ (y : Obj') (D : Y.OrientedTameStructure (m + 1) ΘY y) (hDT : D.Represents TY),
      y ∈ supp (Y.boundaryTheta ΘY) →
      (∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ FY.msheets) →
      ∀ K, MeasurableSet[Y.lebesgueSigmaBoundaryH (m + 1) ΘY] K →
        Subtype.val '' K ⊆ Y.π '' D.U →
        μY K = cY y * (D.boundaryFamily hΘY hDT).nonemptyPart.sheetSum (FY.msheetIntegration hm)
          ω' (Y.π ⁻¹' (Subtype.val '' K)))
    {K : Set (X.orbitSupp (X.boundaryTheta ΘX))}
    (hK : MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) ΘX] K) :
    MeasurableSet[Y.lebesgueSigmaBoundaryH (m + 1) ΘY]
        (Subtype.val ⁻¹' (G.orbitMap '' (F.orbitMap ⁻¹' (Subtype.val '' K)))) ∧
      μX K = μY (Subtype.val ⁻¹' (G.orbitMap '' (F.orbitMap ⁻¹' (Subtype.val '' K)))) := by
  subst heF
  have hsuppA := orbitSupp_boundaryTheta_pull hF hΘX
  set KA : Set (A.orbitSupp (A.boundaryTheta (F.pullbackTheta ΘX))) :=
    Subtype.val ⁻¹' (F.orbitMap ⁻¹' (Subtype.val '' K))
  have hvalA : Subtype.val '' KA = F.orbitMap ⁻¹' (Subtype.val '' K) := by
    refine image_preimage_eq_of_subset ?_
    rw [Subtype.range_coe, hsuppA]
    refine preimage_mono ?_
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  have hcovXne : ∀ x ∈ supp (X.boundaryTheta ΘX),
      Nonempty (X.OrientedTameStructure (m + 1) ΘX x) := fun x hx => by
    obtain ⟨C, -⟩ := hcovX x hx
    exact ⟨C⟩
  have hKA : MeasurableSet[A.lebesgueSigmaBoundaryH (m + 1) (F.pullbackTheta ΘX)] KA := by
    have h := measurable_bsuppMap hF hΘX hcovXne hK
    convert h using 1
    ext q
    constructor
    · rintro ⟨k, hk, he⟩
      change bsuppMap _ q ∈ K
      convert hk
      exact Subtype.ext he.symm
    · intro h
      exact ⟨_, h, rfl⟩
  have hcancel : (Subtype.val ⁻¹' (F.orbitMap '' (Subtype.val '' KA)) :
      Set (X.orbitSupp (X.boundaryTheta ΘX))) = K := by
    rw [hvalA, image_preimage_eq _ hF.isHomeomorph_orbitMap.surjective,
      preimage_image_eq _ Subtype.val_injective]
  have eF := (measure_pull_core_bd hF hPF hm hΘX hndX hcovX rfl hΘA hcptA hTA hTF cA cX hcF ω
    μA μX hμA hμX hKA).2
  rw [hcancel] at eF
  rw [hω] at hμA
  have eG := measure_pull_core_bd hG hPG hm hΘY hndY hcovY heG hΘA hcptA hTA hTG cA cY hcG ω'
    μA μY hμA hμY hKA
  rw [hvalA] at eG
  exact ⟨eG.1, eF.symm.trans eG.2⟩

end EpFunctor

namespace EPLocalization

open EpFunctor CategoryTheory

namespace Diagram

variable {X Y : EP.{u}} {m : ℕ}

theorem isNDimensional_dPullTheta (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence)
    {Θ' : Y.Obj → ℚ} (hΘ' : Y.X.IsFunctorial Θ') {n : ℕ} (h : Y.X.IsNDimensional Θ' n) :
    X.X.IsNDimensional (d.pullTheta Θ') n :=
  isNDimensional_pushforwardTheta d.isEquivalence_F (d.Φ.isFunctorial_pullbackTheta hΘ')
    (isNDimensional_pullbackTheta hΦ h)

theorem isNDimensional_dPushTheta (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence)
    {Θ : X.Obj → ℚ} (hΘ : X.X.IsFunctorial Θ) {n : ℕ} (h : X.X.IsNDimensional Θ n) :
    Y.X.IsNDimensional (d.pushTheta Θ) n :=
  isNDimensional_pushforwardTheta hΦ (d.F.isFunctorial_pullbackTheta hΘ)
    (isNDimensional_pullbackTheta d.isEquivalence_F h)

/-- **E7's `hcov` for `d^*Θ̂' = F_*Φ^*Θ̂'`.** -/
theorem hcovB_pullTheta (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {ΩX ΩA ΩY : Type*}
    [AddCommGroup ΩX] [Module ℝ ΩX] [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup ΩY]
    [Module ℝ ΩY] {FX : X.X.FormEval m ΩX} {FA : d.A.X.FormEval m ΩA} {FY : Y.X.FormEval m ΩY}
    {PF : ΩX →ₗ[ℝ] ΩA} {PG : ΩY →ₗ[ℝ] ΩA} (hPF : FA.IsPullback FX d.F PF)
    (hPG : FA.IsPullback FY d.Φ PG) {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hT' : Y.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp (Y.X.boundaryTheta Θ'), ∃ D : Y.X.OrientedTameStructure (m + 1) Θ' y,
      D.Represents T' ∧ ∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ FY.msheets) :
    ∀ x ∈ supp (X.X.boundaryTheta (d.pullTheta Θ')),
      ∃ C : X.X.OrientedTameStructure (m + 1) (d.pullTheta Θ') x,
        C.Represents (d.pullSection T') ∧
          ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ FX.msheets :=
  hcovB_push d.isEquivalence_F hPF (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
    (isTransported_push d.isEquivalence_F (isOrientation_pullSection hΦ
      (hasIndependentTangentSums (X := Y.X) Θ') hT').isGrHatSection)
    (hcovB_pull hΦ hPG hΘ' (isOrientation_pullSection hΦ
      (hasIndependentTangentSums (X := Y.X) Θ') hT').isGrHatSection
      (isTransported_pull hΦ hT'.isGrHatSection) hcov')

/-- **E7's `hcov` for `d_*Θ̂ = Φ_*F^*Θ̂`.** -/
theorem hcovB_pushTheta (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {ΩX ΩA ΩY : Type*}
    [AddCommGroup ΩX] [Module ℝ ΩX] [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup ΩY]
    [Module ℝ ΩY] {FX : X.X.FormEval m ΩX} {FA : d.A.X.FormEval m ΩA} {FY : Y.X.FormEval m ΩY}
    {PF : ΩX →ₗ[ℝ] ΩA} {PG : ΩY →ₗ[ℝ] ΩA} (hPF : FA.IsPullback FX d.F PF)
    (hPG : FA.IsPullback FY d.Φ PG) {Θ : X.Obj → ℚ} {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hT : X.X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp (X.X.boundaryTheta Θ), ∃ C : X.X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ FX.msheets) :
    ∀ y ∈ supp (Y.X.boundaryTheta (d.pushTheta Θ)),
      ∃ D : Y.X.OrientedTameStructure (m + 1) (d.pushTheta Θ) y,
        D.Represents (d.pushSection T) ∧
          ∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ FY.msheets :=
  hcovB_push hΦ hPG (isBranchedEpSubgroupoid_pullbackTheta d.isEquivalence_F hΘ)
    (isTransported_push hΦ (isOrientation_pullSection d.isEquivalence_F
      (hasIndependentTangentSums (X := X.X) Θ) hT).isGrHatSection)
    (hcovB_pull d.isEquivalence_F hPF hΘ (isOrientation_pullSection d.isEquivalence_F
      (hasIndependentTangentSums (X := X.X) Θ) hT).isGrHatSection
      (isTransported_pull d.isEquivalence_F hT.isGrHatSection) hcov)

/-! #### Theorems 11.4.4 and 11.4.5 for a diagram -/

/-- **Theorem 11.4.4, 2021 p. 545 (new in the 2021 edition), second identity, for a diagram
`d : X ←F A →Φ Y` with `Φ` an equivalence**: `|d|(K) ∈ L(|supp ∂Θ'|)` and
`µ^{∂d^*Θ̂'}_{d^*ω'}(K) = µ^{∂Θ̂'}_{ω'}(|d|(K))`, `d^*ω'` being any `ω` with `F^*ω = Φ^*ω'`. -/
theorem theorem_11_4_4_pull (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {ΩX ΩA ΩY : Type*}
    [AddCommGroup ΩX] [Module ℝ ΩX] [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup ΩY]
    [Module ℝ ΩY] {FX : X.X.FormEval m ΩX} {FA : d.A.X.FormEval m ΩA} {FY : Y.X.FormEval m ΩY}
    {PF : ΩX →ₗ[ℝ] ΩA} {PG : ΩY →ₗ[ℝ] ΩA} (hPF : FA.IsPullback FX d.F PF)
    (hPG : FA.IsPullback FY d.Φ PG) (hm : 0 < m) {Θ' : Y.Obj → ℚ}
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : Y.X.IsCompactBranched Θ') (hnd' : Y.X.IsNDimensional Θ' (m + 1))
    (hT' : Y.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp (Y.X.boundaryTheta Θ'), ∃ D : Y.X.OrientedTameStructure (m + 1) Θ' y,
      D.Represents T' ∧ ∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ FY.msheets)
    {ω : ΩX} {ω' : ΩY} (hω : PF ω = PG ω')
    {K : Set (X.X.orbitSupp (X.X.boundaryTheta (d.pullTheta Θ')))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (m + 1) (d.pullTheta Θ')] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (m + 1) Θ']
        (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) ∧
      X.X.boundaryMeasure FX hm (d.isBranchedEpSubgroupoid_pullTheta hΦ hΘ')
        (d.isCompactBranched_pullTheta hΦ hΘ'.isFunctorial hcpt')
        (d.isNDimensional_dPullTheta hΦ hΘ'.isFunctorial hnd')
        (d.isOrientation_dPullSection hΦ hΘ' (hasIndependentTangentSums (X := Y.X) Θ') hT')
        (d.hcovB_pullTheta hΦ hPF hPG hΘ' hT' hcov') ω K =
        Y.X.boundaryMeasure FY hm hΘ' hcpt' hnd' hT' hcov' ω'
          (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) := by
  have hind' := hasIndependentTangentSums (X := Y.X) Θ'
  have hΦF := d.isEquivalence_F
  rw [orbitMap_image]
  exact measure_span_core_bd hΦF hΦ hPF hPG hm
    (pullbackTheta_pushforwardTheta hΦF.full (d.Φ.isFunctorial_pullbackTheta hΘ'.isFunctorial))
    rfl (isTransported_push hΦF (isOrientation_pullSection hΦ hind' hT').isGrHatSection)
    (isTransported_pull hΦ hT'.isGrHatSection) (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
    (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
    (isOrientation_pullSection hΦ hind' hT') (d.isBranchedEpSubgroupoid_pullTheta hΦ hΘ')
    (d.isNDimensional_dPullTheta hΦ hΘ'.isFunctorial hnd')
    (d.hcovB_pullTheta hΦ hPF hPG hΘ' hT' hcov') hΘ' hnd' hcov'
    (fun a => (Nat.card (d.A.X.Isotropy a) : ℝ)⁻¹) (fun x => (Nat.card (X.X.Isotropy x) : ℝ)⁻¹)
    (fun y => (Nat.card (Y.X.Isotropy y) : ℝ)⁻¹)
    (fun Tc _ _ _ _ => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj hΦF))))
    (fun Tc _ _ _ _ => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj hΦ)))) hω
    (d.A.X.boundaryMeasure FA hm (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
      (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
      (isNDimensional_pullbackTheta hΦ hnd') (isOrientation_pullSection hΦ hind' hT')
      (hcovB_pull hΦ hPG hΘ' (isOrientation_pullSection hΦ hind' hT').isGrHatSection
        (isTransported_pull hΦ hT'.isGrHatSection) hcov') (PF ω)) _ _
    (fun _ C hCT hx hS _ hK hKU => boundaryMeasure_apply _ _ _ _ _ _ _ _ C hCT hx hS hK hKU)
    (fun _ C hCT hx hS _ hK hKU => boundaryMeasure_apply _ _ _ _ _ _ _ _ C hCT hx hS hK hKU)
    (fun _ D hDT hy hS _ hK hKU => boundaryMeasure_apply _ _ _ _ _ _ _ _ D hDT hy hS hK hKU) hK

/-- **Theorem 11.4.4, 2021 p. 545 (new in the 2021 edition), first identity, for a diagram
`d : X ←F A →Φ Y` with `Φ` an equivalence**: `|d|(K) ∈ L(|supp ∂d_*Θ|)` and
`µ^{∂Θ̂}_ω(K) = µ^{∂d_*Θ̂}_{d_*ω}(|d|(K))`, `d_*ω` being any `ω'` with `Φ^*ω' = F^*ω`. -/
theorem theorem_11_4_4_push (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {ΩX ΩA ΩY : Type*}
    [AddCommGroup ΩX] [Module ℝ ΩX] [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup ΩY]
    [Module ℝ ΩY] {FX : X.X.FormEval m ΩX} {FA : d.A.X.FormEval m ΩA} {FY : Y.X.FormEval m ΩY}
    {PF : ΩX →ₗ[ℝ] ΩA} {PG : ΩY →ₗ[ℝ] ΩA} (hPF : FA.IsPullback FX d.F PF)
    (hPG : FA.IsPullback FY d.Φ PG) (hm : 0 < m) {Θ : X.Obj → ℚ}
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hΘ : X.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.X.IsCompactBranched Θ) (hnd : X.X.IsNDimensional Θ (m + 1))
    (hT : X.X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp (X.X.boundaryTheta Θ), ∃ C : X.X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ FX.msheets)
    {ω : ΩX} {ω' : ΩY} (hω : PF ω = PG ω') {K : Set (X.X.orbitSupp (X.X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (m + 1) Θ] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (m + 1) (d.pushTheta Θ)]
        (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) ∧
      X.X.boundaryMeasure FX hm hΘ hcpt hnd hT hcov ω K =
        Y.X.boundaryMeasure FY hm (d.isBranchedEpSubgroupoid_pushTheta hΦ hΘ)
          (d.isCompactBranched_pushTheta hΦ hΘ.isFunctorial hcpt)
          (d.isNDimensional_dPushTheta hΦ hΘ.isFunctorial hnd)
          (d.isOrientation_dPushSection hΦ hΘ (hasIndependentTangentSums (X := X.X) Θ) hT)
          (d.hcovB_pushTheta hΦ hPF hPG hΘ hT hcov) ω'
          (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) := by
  have hind := hasIndependentTangentSums (X := X.X) Θ
  have hΦF := d.isEquivalence_F
  rw [orbitMap_image]
  exact measure_span_core_bd hΦF hΦ hPF hPG hm rfl
    (pullbackTheta_pushforwardTheta hΦ.full (d.F.isFunctorial_pullbackTheta hΘ.isFunctorial))
    (isTransported_pull hΦF hT.isGrHatSection)
    (isTransported_push hΦ (isOrientation_pullSection hΦF hind hT).isGrHatSection)
    (isBranchedEpSubgroupoid_pullbackTheta hΦF hΘ)
    (isCompactBranched_pullbackTheta hΦF hΘ.isFunctorial hcpt)
    (isOrientation_pullSection hΦF hind hT) hΘ hnd hcov (d.isBranchedEpSubgroupoid_pushTheta hΦ hΘ)
    (d.isNDimensional_dPushTheta hΦ hΘ.isFunctorial hnd) (d.hcovB_pushTheta hΦ hPF hPG hΘ hT hcov)
    (fun a => (Nat.card (d.A.X.Isotropy a) : ℝ)⁻¹) (fun x => (Nat.card (X.X.Isotropy x) : ℝ)⁻¹)
    (fun y => (Nat.card (Y.X.Isotropy y) : ℝ)⁻¹)
    (fun Tc _ _ _ _ => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj hΦF))))
    (fun Tc _ _ _ _ => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj hΦ)))) hω
    (d.A.X.boundaryMeasure FA hm (isBranchedEpSubgroupoid_pullbackTheta hΦF hΘ)
      (isCompactBranched_pullbackTheta hΦF hΘ.isFunctorial hcpt)
      (isNDimensional_pullbackTheta hΦF hnd) (isOrientation_pullSection hΦF hind hT)
      (hcovB_pull hΦF hPF hΘ (isOrientation_pullSection hΦF hind hT).isGrHatSection
        (isTransported_pull hΦF hT.isGrHatSection) hcov) (PF ω)) _ _
    (fun _ C hCT hx hS _ hK hKU => boundaryMeasure_apply _ _ _ _ _ _ _ _ C hCT hx hS hK hKU)
    (fun _ C hCT hx hS _ hK hKU => boundaryMeasure_apply _ _ _ _ _ _ _ _ C hCT hx hS hK hKU)
    (fun _ D hDT hy hS _ hK hKU => boundaryMeasure_apply _ _ _ _ _ _ _ _ D hDT hy hS hK hKU) hK

/-- **Theorem 11.4.5, 2021 p. 545 (new in the 2021 edition), second identity, for a diagram
`d : X ←F A →Φ Y` with `Φ` an equivalence, `X`, `Y` with the local unique continuation
property**: as `theorem_11_4_4_pull` for the effective boundary measures of Theorem 9.5.16. -/
theorem theorem_11_4_5_pull (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {ΩX ΩA ΩY : Type*}
    [AddCommGroup ΩX] [Module ℝ ΩX] [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup ΩY]
    [Module ℝ ΩY] {FX : X.X.FormEval m ΩX} {FA : d.A.X.FormEval m ΩA} {FY : Y.X.FormEval m ΩY}
    {PF : ΩX →ₗ[ℝ] ΩA} {PG : ΩY →ₗ[ℝ] ΩA} (hPF : FA.IsPullback FX d.F PF)
    (hPG : FA.IsPullback FY d.Φ PG) (hm : 0 < m) (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC)
    {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hnd' : Y.X.IsNDimensional Θ' (m + 1)) (hT' : Y.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp (Y.X.boundaryTheta Θ'), ∃ D : Y.X.OrientedTameStructure (m + 1) Θ' y,
      D.Represents T' ∧ (∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ FY.msheets) ∧
        D.rep.HasLUC)
    {ω : ΩX} {ω' : ΩY} (hω : PF ω = PG ω')
    {K : Set (X.X.orbitSupp (X.X.boundaryTheta (d.pullTheta Θ')))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (m + 1) (d.pullTheta Θ')] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (m + 1) Θ']
        (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) ∧
      X.X.boundaryMeasureEff FX hm (d.isBranchedEpSubgroupoid_pullTheta hΦ hΘ')
        (d.isCompactBranched_pullTheta hΦ hΘ'.isFunctorial hcpt')
        (d.isNDimensional_dPullTheta hΦ hΘ'.isFunctorial hnd')
        (d.isOrientation_dPullSection hΦ hΘ' (hasIndependentTangentSums (X := Y.X) Θ') hT')
        (hcovB_addLUC hLX (d.hcovB_pullTheta hΦ hPF hPG hΘ' hT' (hcovB_dropLUC hcov'))) ω K =
        Y.X.boundaryMeasureEff FY hm hΘ' hcpt' hnd' hT' hcov' ω'
          (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) := by
  have hind' := hasIndependentTangentSums (X := Y.X) Θ'
  have hΦF := d.isEquivalence_F
  have hLA := (proposition_10_1_16 hΦF).2 hLX
  rw [orbitMap_image]
  exact measure_span_core_bd hΦF hΦ hPF hPG hm
    (pullbackTheta_pushforwardTheta hΦF.full (d.Φ.isFunctorial_pullbackTheta hΘ'.isFunctorial))
    rfl (isTransported_push hΦF (isOrientation_pullSection hΦ hind' hT').isGrHatSection)
    (isTransported_pull hΦ hT'.isGrHatSection) (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
    (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
    (isOrientation_pullSection hΦ hind' hT') (d.isBranchedEpSubgroupoid_pullTheta hΦ hΘ')
    (d.isNDimensional_dPullTheta hΦ hΘ'.isFunctorial hnd')
    (d.hcovB_pullTheta hΦ hPF hPG hΘ' hT' (hcovB_dropLUC hcov')) hΘ' hnd' (hcovB_dropLUC hcov')
    (fun a => (Nat.card (d.A.X.EffIsotropy a) : ℝ)⁻¹)
    (fun x => (Nat.card (X.X.EffIsotropy x) : ℝ)⁻¹)
    (fun y => (Nat.card (Y.X.EffIsotropy y) : ℝ)⁻¹)
    (fun Tc R R' hRW hR' => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Tc.card_effIsotropy_eq hΦF R R' hRW hR' (d.A.X.isLUC_iff_forall_naturalRep.1 hLA _ R)
        (X.X.isLUC_iff_forall_naturalRep.1 hLX _ R')))
    (fun Tc R R' hRW hR' => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Tc.card_effIsotropy_eq hΦ R R' hRW hR' (d.A.X.isLUC_iff_forall_naturalRep.1 hLA _ R)
        (Y.X.isLUC_iff_forall_naturalRep.1 hLY _ R'))) hω
    (d.A.X.boundaryMeasureEff FA hm (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
      (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
      (isNDimensional_pullbackTheta hΦ hnd') (isOrientation_pullSection hΦ hind' hT')
      (hcovB_addLUC hLA (hcovB_pull hΦ hPG hΘ'
        (isOrientation_pullSection hΦ hind' hT').isGrHatSection
        (isTransported_pull hΦ hT'.isGrHatSection) (hcovB_dropLUC hcov'))) (PF ω)) _ _
    (fun _ C hCT hx hS _ hK hKU => boundaryMeasureEff_apply _ _ _ _ _ _ _ _ C hCT hx hS
      (d.A.X.isLUC_iff_forall_naturalRep.1 hLA _ C.rep) hK hKU)
    (fun _ C hCT hx hS _ hK hKU => boundaryMeasureEff_apply _ _ _ _ _ _ _ _ C hCT hx hS
      (X.X.isLUC_iff_forall_naturalRep.1 hLX _ C.rep) hK hKU)
    (fun _ D hDT hy hS _ hK hKU => boundaryMeasureEff_apply _ _ _ _ _ _ _ _ D hDT hy hS
      (Y.X.isLUC_iff_forall_naturalRep.1 hLY _ D.rep) hK hKU) hK

/-- **Theorem 11.4.5, 2021 p. 545 (new in the 2021 edition), first identity, for a diagram
`d : X ←F A →Φ Y` with `Φ` an equivalence, `X`, `Y` with the local unique continuation
property**: as `theorem_11_4_4_push` for the effective boundary measures of Theorem 9.5.16. -/
theorem theorem_11_4_5_push (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {ΩX ΩA ΩY : Type*}
    [AddCommGroup ΩX] [Module ℝ ΩX] [AddCommGroup ΩA] [Module ℝ ΩA] [AddCommGroup ΩY]
    [Module ℝ ΩY] {FX : X.X.FormEval m ΩX} {FA : d.A.X.FormEval m ΩA} {FY : Y.X.FormEval m ΩY}
    {PF : ΩX →ₗ[ℝ] ΩA} {PG : ΩY →ₗ[ℝ] ΩA} (hPF : FA.IsPullback FX d.F PF)
    (hPG : FA.IsPullback FY d.Φ PG) (hm : 0 < m) (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC)
    {Θ : X.Obj → ℚ} {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hcpt : X.X.IsCompactBranched Θ)
    (hnd : X.X.IsNDimensional Θ (m + 1)) (hT : X.X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp (X.X.boundaryTheta Θ), ∃ C : X.X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ FX.msheets) ∧
        C.rep.HasLUC)
    {ω : ΩX} {ω' : ΩY} (hω : PF ω = PG ω') {K : Set (X.X.orbitSupp (X.X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (m + 1) Θ] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (m + 1) (d.pushTheta Θ)]
        (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) ∧
      X.X.boundaryMeasureEff FX hm hΘ hcpt hnd hT hcov ω K =
        Y.X.boundaryMeasureEff FY hm (d.isBranchedEpSubgroupoid_pushTheta hΦ hΘ)
          (d.isCompactBranched_pushTheta hΦ hΘ.isFunctorial hcpt)
          (d.isNDimensional_dPushTheta hΦ hΘ.isFunctorial hnd)
          (d.isOrientation_dPushSection hΦ hΘ (hasIndependentTangentSums (X := X.X) Θ) hT)
          (hcovB_addLUC hLY (d.hcovB_pushTheta hΦ hPF hPG hΘ hT (hcovB_dropLUC hcov))) ω'
          (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) := by
  have hind := hasIndependentTangentSums (X := X.X) Θ
  have hΦF := d.isEquivalence_F
  have hLA := (proposition_10_1_16 hΦF).2 hLX
  rw [orbitMap_image]
  exact measure_span_core_bd hΦF hΦ hPF hPG hm rfl
    (pullbackTheta_pushforwardTheta hΦ.full (d.F.isFunctorial_pullbackTheta hΘ.isFunctorial))
    (isTransported_pull hΦF hT.isGrHatSection)
    (isTransported_push hΦ (isOrientation_pullSection hΦF hind hT).isGrHatSection)
    (isBranchedEpSubgroupoid_pullbackTheta hΦF hΘ)
    (isCompactBranched_pullbackTheta hΦF hΘ.isFunctorial hcpt)
    (isOrientation_pullSection hΦF hind hT) hΘ hnd (hcovB_dropLUC hcov)
    (d.isBranchedEpSubgroupoid_pushTheta hΦ hΘ) (d.isNDimensional_dPushTheta hΦ hΘ.isFunctorial hnd)
    (d.hcovB_pushTheta hΦ hPF hPG hΘ hT (hcovB_dropLUC hcov))
    (fun a => (Nat.card (d.A.X.EffIsotropy a) : ℝ)⁻¹)
    (fun x => (Nat.card (X.X.EffIsotropy x) : ℝ)⁻¹)
    (fun y => (Nat.card (Y.X.EffIsotropy y) : ℝ)⁻¹)
    (fun Tc R R' hRW hR' => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Tc.card_effIsotropy_eq hΦF R R' hRW hR' (d.A.X.isLUC_iff_forall_naturalRep.1 hLA _ R)
        (X.X.isLUC_iff_forall_naturalRep.1 hLX _ R')))
    (fun Tc R R' hRW hR' => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Tc.card_effIsotropy_eq hΦ R R' hRW hR' (d.A.X.isLUC_iff_forall_naturalRep.1 hLA _ R)
        (Y.X.isLUC_iff_forall_naturalRep.1 hLY _ R'))) hω
    (d.A.X.boundaryMeasureEff FA hm (isBranchedEpSubgroupoid_pullbackTheta hΦF hΘ)
      (isCompactBranched_pullbackTheta hΦF hΘ.isFunctorial hcpt)
      (isNDimensional_pullbackTheta hΦF hnd) (isOrientation_pullSection hΦF hind hT)
      (hcovB_addLUC hLA (hcovB_pull hΦF hPF hΘ
        (isOrientation_pullSection hΦF hind hT).isGrHatSection
        (isTransported_pull hΦF hT.isGrHatSection) (hcovB_dropLUC hcov))) (PF ω)) _ _
    (fun _ C hCT hx hS _ hK hKU => boundaryMeasureEff_apply _ _ _ _ _ _ _ _ C hCT hx hS
      (d.A.X.isLUC_iff_forall_naturalRep.1 hLA _ C.rep) hK hKU)
    (fun _ C hCT hx hS _ hK hKU => boundaryMeasureEff_apply _ _ _ _ _ _ _ _ C hCT hx hS
      (X.X.isLUC_iff_forall_naturalRep.1 hLX _ C.rep) hK hKU)
    (fun _ D hDT hy hS _ hK hKU => boundaryMeasureEff_apply _ _ _ _ _ _ _ _ D hDT hy hS
      (Y.X.isLUC_iff_forall_naturalRep.1 hLY _ D.rep) hK hKU) hK

end Diagram

/-! #### Theorems 11.4.4 and 11.4.5 for a generalized isomorphism and the forms `Ωᵐ_{ep,∞}` -/

namespace EPLoc

variable {X Y : EP.{u}} {m : ℕ}

/-- **Theorem 11.4.4, 2021 p. 545 (new in the 2021 edition), second identity**: for a
generalized isomorphism `f : X → Y`, `Θ̂'` on `Y` oriented, compact, of dimension `n = m + 1 ≥ 2`,
with E7's corner hypothesis `hcov'` (each point of `supp ∂Θ'` has an oriented tame structure
whose nonempty boundary sheets lie in the integration class of `Ωᵐ_{ep,∞}`), and
`K ∈ L(|supp ∂f^*Θ'|)`: `|f|(K) ∈ L(|supp ∂Θ'|)` and
`µ^{∂f^*Θ̂'}_{f^*ω'}(K) = µ^{∂Θ̂'}_{ω'}(|f|(K))`. -/
theorem theorem_11_4_4_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hm : 0 < m)
    {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hnd' : Y.X.IsNDimensional Θ' (m + 1)) (hT' : Y.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp (Y.X.boundaryTheta Θ'), ∃ D : Y.X.OrientedTameStructure (m + 1) Θ' y,
      D.Represents T' ∧ ∀ i, (D.boundarySheet i).Nonempty →
        D.boundarySheet i ∈ (Y.epFormsInftyEval m).msheets)
    (ω' : Y.epFormsInfty m) {K : Set (X.X.orbitSupp (X.X.boundaryTheta (pullTheta f Θ')))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (m + 1) (pullTheta f Θ')] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (m + 1) Θ']
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      X.X.boundaryMeasure (X.epFormsInftyEval m) hm
          ((rep f).isBranchedEpSubgroupoid_pullTheta (isEquivalence_rep_Φ hf) hΘ')
          ((rep f).isCompactBranched_pullTheta (isEquivalence_rep_Φ hf) hΘ'.isFunctorial hcpt')
          ((rep f).isNDimensional_dPullTheta (isEquivalence_rep_Φ hf) hΘ'.isFunctorial hnd')
          ((rep f).isOrientation_dPullSection (isEquivalence_rep_Φ hf) hΘ'
            (hasIndependentTangentSums (X := Y.X) Θ') hT')
          ((rep f).hcovB_pullTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F m)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) m) hΘ' hT' hcov')
          (formsPullback f m ω') K =
        Y.X.boundaryMeasure (Y.epFormsInftyEval m) hm hΘ' hcpt' hnd' hT' hcov' ω'
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) := by
  rw [orbitMap_eq_rep]
  exact (rep f).theorem_11_4_4_pull (isEquivalence_rep_Φ hf)
    (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F m)
    (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) m) hm hΘ' hcpt' hnd' hT' hcov'
    (pullback_formsPullback f ω') hK

/-- **Theorem 11.4.4, 2021 p. 545 (new in the 2021 edition), first identity**: for a
generalized isomorphism `f : X → Y`, `Θ̂` on `X` oriented, compact, of dimension `n = m + 1 ≥ 2`,
with E7's corner hypothesis `hcov`, and `K ∈ L(|supp ∂Θ|)`: `|f|(K) ∈ L(|supp ∂f_*Θ|)` and
`µ^{∂Θ̂}_ω(K) = µ^{∂f_*Θ̂}_{f_*ω}(|f|(K))` (`f_*` computed on the representative `rep f`). -/
theorem theorem_11_4_4_push {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hm : 0 < m)
    {Θ : X.Obj → ℚ} {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hcpt : X.X.IsCompactBranched Θ)
    (hnd : X.X.IsNDimensional Θ (m + 1)) (hT : X.X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp (X.X.boundaryTheta Θ), ∃ C : X.X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ ∀ i, (C.boundarySheet i).Nonempty →
        C.boundarySheet i ∈ (X.epFormsInftyEval m).msheets)
    (ω : X.epFormsInfty m) {K : Set (X.X.orbitSupp (X.X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (m + 1) Θ] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (m + 1) (pushTheta f Θ)]
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      X.X.boundaryMeasure (X.epFormsInftyEval m) hm hΘ hcpt hnd hT hcov ω K =
        Y.X.boundaryMeasure (Y.epFormsInftyEval m) hm
          ((rep f).isBranchedEpSubgroupoid_pushTheta (isEquivalence_rep_Φ hf) hΘ)
          ((rep f).isCompactBranched_pushTheta (isEquivalence_rep_Φ hf) hΘ.isFunctorial hcpt)
          ((rep f).isNDimensional_dPushTheta (isEquivalence_rep_Φ hf) hΘ.isFunctorial hnd)
          ((rep f).isOrientation_dPushSection (isEquivalence_rep_Φ hf) hΘ
            (hasIndependentTangentSums (X := X.X) Θ) hT)
          ((rep f).hcovB_pushTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F m)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) m) hΘ hT hcov)
          ((rep f).formsPush (isEquivalence_rep_Φ hf) m ω)
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) := by
  rw [orbitMap_eq_rep]
  exact (rep f).theorem_11_4_4_push (isEquivalence_rep_Φ hf)
    (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F m)
    (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) m) hm hΘ hcpt hnd hT hcov
    (pullback_formsPush hf ω).symm hK

/-- **Theorem 11.4.5, 2021 p. 545 (new in the 2021 edition), second identity**: as
`theorem_11_4_4_pull` for the effective boundary measures of Theorem 9.5.16, `X` and `Y` having
the local unique continuation property and E7's `hcov'` asking `HasLUC` of the structures. -/
theorem theorem_11_4_5_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hm : 0 < m)
    (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC)
    {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hnd' : Y.X.IsNDimensional Θ' (m + 1)) (hT' : Y.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp (Y.X.boundaryTheta Θ'), ∃ D : Y.X.OrientedTameStructure (m + 1) Θ' y,
      D.Represents T' ∧ (∀ i, (D.boundarySheet i).Nonempty →
        D.boundarySheet i ∈ (Y.epFormsInftyEval m).msheets) ∧ D.rep.HasLUC)
    (ω' : Y.epFormsInfty m) {K : Set (X.X.orbitSupp (X.X.boundaryTheta (pullTheta f Θ')))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (m + 1) (pullTheta f Θ')] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (m + 1) Θ']
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      X.X.boundaryMeasureEff (X.epFormsInftyEval m) hm
          ((rep f).isBranchedEpSubgroupoid_pullTheta (isEquivalence_rep_Φ hf) hΘ')
          ((rep f).isCompactBranched_pullTheta (isEquivalence_rep_Φ hf) hΘ'.isFunctorial hcpt')
          ((rep f).isNDimensional_dPullTheta (isEquivalence_rep_Φ hf) hΘ'.isFunctorial hnd')
          ((rep f).isOrientation_dPullSection (isEquivalence_rep_Φ hf) hΘ'
            (hasIndependentTangentSums (X := Y.X) Θ') hT')
          (hcovB_addLUC hLX ((rep f).hcovB_pullTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F m)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) m) hΘ' hT'
            (hcovB_dropLUC hcov')))
          (formsPullback f m ω') K =
        Y.X.boundaryMeasureEff (Y.epFormsInftyEval m) hm hΘ' hcpt' hnd' hT' hcov' ω'
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) := by
  rw [orbitMap_eq_rep]
  exact (rep f).theorem_11_4_5_pull (isEquivalence_rep_Φ hf)
    (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F m)
    (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) m) hm hLX hLY hΘ' hcpt' hnd' hT'
    hcov' (pullback_formsPullback f ω') hK

/-- **Theorem 11.4.5, 2021 p. 545 (new in the 2021 edition), first identity**: as
`theorem_11_4_4_push` for the effective boundary measures of Theorem 9.5.16, `X` and `Y` having
the local unique continuation property and E7's `hcov` asking `HasLUC` of the structures. -/
theorem theorem_11_4_5_push {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hm : 0 < m)
    (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC)
    {Θ : X.Obj → ℚ} {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hcpt : X.X.IsCompactBranched Θ)
    (hnd : X.X.IsNDimensional Θ (m + 1)) (hT : X.X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp (X.X.boundaryTheta Θ), ∃ C : X.X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty →
        C.boundarySheet i ∈ (X.epFormsInftyEval m).msheets) ∧ C.rep.HasLUC)
    (ω : X.epFormsInfty m) {K : Set (X.X.orbitSupp (X.X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (m + 1) Θ] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (m + 1) (pushTheta f Θ)]
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      X.X.boundaryMeasureEff (X.epFormsInftyEval m) hm hΘ hcpt hnd hT hcov ω K =
        Y.X.boundaryMeasureEff (Y.epFormsInftyEval m) hm
          ((rep f).isBranchedEpSubgroupoid_pushTheta (isEquivalence_rep_Φ hf) hΘ)
          ((rep f).isCompactBranched_pushTheta (isEquivalence_rep_Φ hf) hΘ.isFunctorial hcpt)
          ((rep f).isNDimensional_dPushTheta (isEquivalence_rep_Φ hf) hΘ.isFunctorial hnd)
          ((rep f).isOrientation_dPushSection (isEquivalence_rep_Φ hf) hΘ
            (hasIndependentTangentSums (X := X.X) Θ) hT)
          (hcovB_addLUC hLY ((rep f).hcovB_pushTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F m)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) m) hΘ hT
            (hcovB_dropLUC hcov)))
          ((rep f).formsPush (isEquivalence_rep_Φ hf) m ω)
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) := by
  rw [orbitMap_eq_rep]
  exact (rep f).theorem_11_4_5_push (isEquivalence_rep_Φ hf)
    (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F m)
    (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) m) hm hLX hLY hΘ hcpt hnd hT hcov
    (pullback_formsPush hf ω).symm hK

end EPLoc

end EPLocalization

end Polyfold
