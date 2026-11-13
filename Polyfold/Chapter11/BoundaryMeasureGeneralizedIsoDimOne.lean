import Polyfold.Chapter11.BoundaryMeasureEquivalenceDimOne
import Polyfold.Chapter11.BoundaryMeasureGeneralizedIso

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4, **Theorems 11.4.4 and 11.4.5 for `n = 1` and a generalized
isomorphism** (p. 545, new in the 2021 edition), gap G.131.  Numbers and pages are the 2021
text's.

H4's `BoundaryMeasureGeneralizedIso` for `m = 0`: a generalized isomorphism `f : X → Y` is represented by a
diagram `X ←F A →Φ Y` of equivalences, and the two equivalence cores of
`BoundaryMeasureEquivalenceDimOne` are composed (`measure_span_core_bd_dim1`).

* `EpFunctor.measure_span_core_bd_dim1`: the core for `X ←F A →G Y`, `n = 1`.
* `Diagram.theorem_11_4_4_pull_dim1`, `Diagram.theorem_11_4_4_push_dim1`,
  `Diagram.theorem_11_4_5_pull_dim1`, `Diagram.theorem_11_4_5_push_dim1`.
* **`EPLoc.theorem_11_4_4_pull_dim1`**, **`EPLoc.theorem_11_4_4_push_dim1`**,
  **`EPLoc.theorem_11_4_5_pull_dim1`**, **`EPLoc.theorem_11_4_5_push_dim1`**: Theorems 11.4.4 and
  11.4.5 for a generalized isomorphism and `n = 1`, with only the text's hypotheses (an oriented
  tame structure describing `T̂` at every point; LUC of the ep-groupoids for 11.4.5).
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

namespace EpFunctor

variable {A X Y : EP.{u}}

/-- **The core of Theorems 11.4.4 and 11.4.5 for `X ←F A →G Y` and `n = 1`** (H4's
`measure_span_core_bd` for `m = 0`): `µ_X(K) = µ_Y(|G|(|F|⁻¹(K)))` for measures with the local
formulas of Theorem 9.5.15 (`n = 1`), `F^*ω = G^*ω'`. -/
theorem measure_span_core_bd_dim1 {F : EpFunctor A.X X.X} {G : EpFunctor A.X Y.X}
    (hF : F.IsEquivalence) (hG : G.IsEquivalence)
    {ΘA : A.Obj → ℚ} {ΘX : X.Obj → ℚ} {ΘY : Y.Obj → ℚ} {TA : A.Obj → A.X.PObj.OrTangent →₀ ℚ}
    {TX : X.Obj → X.X.PObj.OrTangent →₀ ℚ} {TY : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (heF : F.pullbackTheta ΘX = ΘA) (heG : G.pullbackTheta ΘY = ΘA)
    (hTF : F.IsTransported TA TX) (hTG : G.IsTransported TA TY)
    (hΘA : A.X.IsBranchedEpSubgroupoid ΘA) (hcptA : A.X.IsCompactBranched ΘA)
    (hTA : A.X.IsOrientation ΘA TA)
    (hΘX : X.X.IsBranchedEpSubgroupoid ΘX)
    (hcovX : ∀ x ∈ supp (X.X.boundaryTheta ΘX), ∃ C : X.X.OrientedTameStructure (0 + 1) ΘX x,
      C.Represents TX ∧ ∀ i, (C.boundarySheet i).Subsingleton)
    (hΘY : Y.X.IsBranchedEpSubgroupoid ΘY)
    (hcovY : ∀ y ∈ supp (Y.X.boundaryTheta ΘY), ∃ D : Y.X.OrientedTameStructure (0 + 1) ΘY y,
      D.Represents TY ∧ ∀ i, (D.boundarySheet i).Subsingleton)
    (cA : A.Obj → ℝ) (cX : X.Obj → ℝ) (cY : Y.Obj → ℝ)
    (hcF : ∀ {a : A.Obj} {x : X.Obj} (Tc : F.TransportChart a x) (R : A.X.NaturalRep a)
      (R' : X.X.NaturalRep x), R.U ⊆ Tc.W → R'.U = Tc.Q '' R.U → cA a = cX x)
    (hcG : ∀ {a : A.Obj} {y : Y.Obj} (Tc : G.TransportChart a y) (R : A.X.NaturalRep a)
      (R' : Y.X.NaturalRep y), R.U ⊆ Tc.W → R'.U = Tc.Q '' R.U → cA a = cY y)
    {ω : X.epFormsInfty 0} {ω' : Y.epFormsInfty 0}
    (hω : EP.epFormsInftyPullback F 0 ω = EP.epFormsInftyPullback G 0 ω')
    (μA : @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta ΘA))
      (A.X.lebesgueSigmaBoundaryH (0 + 1) ΘA))
    (μX : @SignedMeasure (X.X.orbitSupp (X.X.boundaryTheta ΘX))
      (X.X.lebesgueSigmaBoundaryH (0 + 1) ΘX))
    (μY : @SignedMeasure (Y.X.orbitSupp (Y.X.boundaryTheta ΘY))
      (Y.X.lebesgueSigmaBoundaryH (0 + 1) ΘY))
    (hμA : ∀ (a : A.Obj) (C : A.X.OrientedTameStructure (0 + 1) ΘA a) (hCT : C.Represents TA),
      a ∈ supp (A.X.boundaryTheta ΘA) →
      (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ pointSheets A.X) →
      ∀ K, MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) ΘA] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        μA K = cA a * (C.boundaryFamily hΘA hCT).nonemptyPart.sheetSum A.zeroFormIntegration
          (EP.epFormsInftyPullback F 0 ω) (A.X.π ⁻¹' (Subtype.val '' K)))
    (hμX : ∀ (x : X.Obj) (C : X.X.OrientedTameStructure (0 + 1) ΘX x) (hCT : C.Represents TX),
      x ∈ supp (X.X.boundaryTheta ΘX) →
      (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ pointSheets X.X) →
      ∀ K, MeasurableSet[X.X.lebesgueSigmaBoundaryH (0 + 1) ΘX] K →
        Subtype.val '' K ⊆ X.X.π '' C.U →
        μX K = cX x * (C.boundaryFamily hΘX hCT).nonemptyPart.sheetSum X.zeroFormIntegration
          ω (X.X.π ⁻¹' (Subtype.val '' K)))
    (hμY : ∀ (y : Y.Obj) (D : Y.X.OrientedTameStructure (0 + 1) ΘY y) (hDT : D.Represents TY),
      y ∈ supp (Y.X.boundaryTheta ΘY) →
      (∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ pointSheets Y.X) →
      ∀ K, MeasurableSet[Y.X.lebesgueSigmaBoundaryH (0 + 1) ΘY] K →
        Subtype.val '' K ⊆ Y.X.π '' D.U →
        μY K = cY y * (D.boundaryFamily hΘY hDT).nonemptyPart.sheetSum Y.zeroFormIntegration
          ω' (Y.X.π ⁻¹' (Subtype.val '' K)))
    {K : Set (X.X.orbitSupp (X.X.boundaryTheta ΘX))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (0 + 1) ΘX] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (0 + 1) ΘY]
        (Subtype.val ⁻¹' (G.orbitMap '' (F.orbitMap ⁻¹' (Subtype.val '' K)))) ∧
      μX K = μY (Subtype.val ⁻¹' (G.orbitMap '' (F.orbitMap ⁻¹' (Subtype.val '' K)))) := by
  subst heF
  have hsuppA := orbitSupp_boundaryTheta_pull hF hΘX
  set KA : Set (A.X.orbitSupp (A.X.boundaryTheta (F.pullbackTheta ΘX))) :=
    Subtype.val ⁻¹' (F.orbitMap ⁻¹' (Subtype.val '' K))
  have hvalA : Subtype.val '' KA = F.orbitMap ⁻¹' (Subtype.val '' K) := by
    refine image_preimage_eq_of_subset ?_
    rw [Subtype.range_coe, hsuppA]
    refine preimage_mono ?_
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  have hcovXne : ∀ x ∈ supp (X.X.boundaryTheta ΘX),
      Nonempty (X.X.OrientedTameStructure (0 + 1) ΘX x) := fun x hx => by
    obtain ⟨C, -⟩ := hcovX x hx
    exact ⟨C⟩
  have hKA : MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) (F.pullbackTheta ΘX)] KA := by
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
      Set (X.X.orbitSupp (X.X.boundaryTheta ΘX))) = K := by
    rw [hvalA, image_preimage_eq _ hF.isHomeomorph_orbitMap.surjective,
      preimage_image_eq _ Subtype.val_injective]
  have eF := (measure_pull_core_bd_dim1 hF hΘX hcovX rfl hΘA hcptA hTA hTF cA cX hcF ω
    μA μX hμA hμX hKA).2
  rw [hcancel] at eF
  rw [hω] at hμA
  have eG := measure_pull_core_bd_dim1 hG hΘY hcovY heG hΘA hcptA hTA hTG cA cY hcG ω'
    μA μY hμA hμY hKA
  rw [hvalA] at eG
  exact ⟨eG.1, eF.symm.trans eG.2⟩

end EpFunctor

namespace EPLocalization

open EpFunctor CategoryTheory

namespace Diagram

variable {X Y : EP.{u}}

/-- `d^*Θ̂' = F_*Φ^*Θ̂'` is oriented and tame when `Θ̂'` is (`n = 1`). -/
theorem hloc_pullTheta_dim1 (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {Θ' : Y.Obj → ℚ}
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure (0 + 1) Θ' y, D.Represents T') :
    ∀ x ∈ supp (d.pullTheta Θ'), ∃ C : X.X.OrientedTameStructure (0 + 1) (d.pullTheta Θ') x,
      C.Represents (d.pullSection T') :=
  hloc_push_dim1 d.isEquivalence_F (d.Φ.isFunctorial_pullbackTheta hΘ'.isFunctorial)
    (isTransported_push d.isEquivalence_F (isOrientation_pullSection hΦ
      (hasIndependentTangentSums (X := Y.X) Θ') hT').isGrHatSection)
    (hloc_pull_dim1 hΦ hΘ'.isFunctorial (isOrientation_pullSection hΦ
      (hasIndependentTangentSums (X := Y.X) Θ') hT').isGrHatSection
      (isTransported_pull hΦ hT'.isGrHatSection) hloc')

/-- `d_*Θ̂ = Φ_*F^*Θ̂` is oriented and tame when `Θ̂` is (`n = 1`). -/
theorem hloc_pushTheta_dim1 (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {Θ : X.Obj → ℚ}
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hΘ : X.X.IsBranchedEpSubgroupoid Θ)
    (hT : X.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T) :
    ∀ y ∈ supp (d.pushTheta Θ), ∃ D : Y.X.OrientedTameStructure (0 + 1) (d.pushTheta Θ) y,
      D.Represents (d.pushSection T) :=
  hloc_push_dim1 hΦ (d.F.isFunctorial_pullbackTheta hΘ.isFunctorial)
    (isTransported_push hΦ (isOrientation_pullSection d.isEquivalence_F
      (hasIndependentTangentSums (X := X.X) Θ) hT).isGrHatSection)
    (hloc_pull_dim1 d.isEquivalence_F hΘ.isFunctorial (isOrientation_pullSection d.isEquivalence_F
      (hasIndependentTangentSums (X := X.X) Θ) hT).isGrHatSection
      (isTransported_pull d.isEquivalence_F hT.isGrHatSection) hloc)

/-- **Theorem 11.4.4, second identity, for a diagram `d : X ←F A →Φ Y` and `n = 1`**:
`µ^{∂d^*Θ̂'}_{ω}(K) = µ^{∂Θ̂'}_{ω'}(|d|(K))` for `F^*ω = Φ^*ω'`. -/
theorem theorem_11_4_4_pull_dim1 (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {Θ' : Y.Obj → ℚ}
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : Y.X.IsCompactBranched Θ') (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure (0 + 1) Θ' y, D.Represents T')
    {ω : X.epFormsInfty 0} {ω' : Y.epFormsInfty 0}
    (hω : EP.epFormsInftyPullback d.F 0 ω = EP.epFormsInftyPullback d.Φ 0 ω')
    {K : Set (X.X.orbitSupp (X.X.boundaryTheta (d.pullTheta Θ')))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (0 + 1) (d.pullTheta Θ')] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (0 + 1) Θ']
        (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) ∧
      X.boundaryBranchedMeasureDim1 (d.isBranchedEpSubgroupoid_pullTheta hΦ hΘ')
        (d.isCompactBranched_pullTheta hΦ hΘ'.isFunctorial hcpt')
        (d.isOrientation_dPullSection hΦ hΘ' (hasIndependentTangentSums (X := Y.X) Θ') hT')
        (d.hloc_pullTheta_dim1 hΦ hΘ' hT' hloc') ω K =
        Y.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc' ω'
          (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) := by
  have hind' := hasIndependentTangentSums (X := Y.X) Θ'
  have hΦF := d.isEquivalence_F
  have hlocA := hloc_pull_dim1 hΦ hΘ'.isFunctorial
    (isOrientation_pullSection hΦ hind' hT').isGrHatSection
    (isTransported_pull hΦ hT'.isGrHatSection) hloc'
  have hlocX := d.hloc_pullTheta_dim1 hΦ hΘ' hT' hloc'
  rw [orbitMap_image]
  exact measure_span_core_bd_dim1 hΦF hΦ
    (pullbackTheta_pushforwardTheta hΦF.full (d.Φ.isFunctorial_pullbackTheta hΘ'.isFunctorial))
    rfl (isTransported_push hΦF (isOrientation_pullSection hΦ hind' hT').isGrHatSection)
    (isTransported_pull hΦ hT'.isGrHatSection) (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
    (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
    (isOrientation_pullSection hΦ hind' hT') (d.isBranchedEpSubgroupoid_pullTheta hΦ hΘ')
    (hcov_subsingleton_of_loc hlocX) hΘ' (hcov_subsingleton_of_loc hloc')
    (fun a => (Nat.card (d.A.X.Isotropy a) : ℝ)⁻¹) (fun x => (Nat.card (X.X.Isotropy x) : ℝ)⁻¹)
    (fun y => (Nat.card (Y.X.Isotropy y) : ℝ)⁻¹)
    (fun Tc _ _ _ _ => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj hΦF))))
    (fun Tc _ _ _ _ => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj hΦ)))) hω
    (d.A.boundaryBranchedMeasureDim1 (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
      (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
      (isOrientation_pullSection hΦ hind' hT') hlocA (EP.epFormsInftyPullback d.F 0 ω)) _ _
    (fun a C hCT hx hS K hK hKU => d.A.boundaryBranchedMeasureDim1_spec _ _ _ _ _ a C hCT hx hS
      K hK hKU)
    (fun x C hCT hx hS K hK hKU => X.boundaryBranchedMeasureDim1_spec _ _ _ _ _ x C hCT hx hS
      K hK hKU)
    (fun y D hDT hy hS K hK hKU => Y.boundaryBranchedMeasureDim1_spec _ _ _ _ _ y D hDT hy hS
      K hK hKU) hK

/-- **Theorem 11.4.4, first identity, for a diagram `d : X ←F A →Φ Y` and `n = 1`**:
`µ^{∂Θ̂}_ω(K) = µ^{∂d_*Θ̂}_{ω'}(|d|(K))` for `F^*ω = Φ^*ω'`. -/
theorem theorem_11_4_4_push_dim1 (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {Θ : X.Obj → ℚ}
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hΘ : X.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.X.IsCompactBranched Θ) (hT : X.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    {ω : X.epFormsInfty 0} {ω' : Y.epFormsInfty 0}
    (hω : EP.epFormsInftyPullback d.F 0 ω = EP.epFormsInftyPullback d.Φ 0 ω')
    {K : Set (X.X.orbitSupp (X.X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (0 + 1) (d.pushTheta Θ)]
        (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) ∧
      X.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc ω K =
        Y.boundaryBranchedMeasureDim1 (d.isBranchedEpSubgroupoid_pushTheta hΦ hΘ)
          (d.isCompactBranched_pushTheta hΦ hΘ.isFunctorial hcpt)
          (d.isOrientation_dPushSection hΦ hΘ (hasIndependentTangentSums (X := X.X) Θ) hT)
          (d.hloc_pushTheta_dim1 hΦ hΘ hT hloc) ω'
          (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) := by
  have hind := hasIndependentTangentSums (X := X.X) Θ
  have hΦF := d.isEquivalence_F
  have hlocA := hloc_pull_dim1 hΦF hΘ.isFunctorial
    (isOrientation_pullSection hΦF hind hT).isGrHatSection
    (isTransported_pull hΦF hT.isGrHatSection) hloc
  have hlocY := d.hloc_pushTheta_dim1 hΦ hΘ hT hloc
  rw [orbitMap_image]
  exact measure_span_core_bd_dim1 hΦF hΦ rfl
    (pullbackTheta_pushforwardTheta hΦ.full (d.F.isFunctorial_pullbackTheta hΘ.isFunctorial))
    (isTransported_pull hΦF hT.isGrHatSection)
    (isTransported_push hΦ (isOrientation_pullSection hΦF hind hT).isGrHatSection)
    (isBranchedEpSubgroupoid_pullbackTheta hΦF hΘ)
    (isCompactBranched_pullbackTheta hΦF hΘ.isFunctorial hcpt)
    (isOrientation_pullSection hΦF hind hT) hΘ (hcov_subsingleton_of_loc hloc)
    (d.isBranchedEpSubgroupoid_pushTheta hΦ hΘ) (hcov_subsingleton_of_loc hlocY)
    (fun a => (Nat.card (d.A.X.Isotropy a) : ℝ)⁻¹) (fun x => (Nat.card (X.X.Isotropy x) : ℝ)⁻¹)
    (fun y => (Nat.card (Y.X.Isotropy y) : ℝ)⁻¹)
    (fun Tc _ _ _ _ => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj hΦF))))
    (fun Tc _ _ _ _ => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj hΦ)))) hω
    (d.A.boundaryBranchedMeasureDim1 (isBranchedEpSubgroupoid_pullbackTheta hΦF hΘ)
      (isCompactBranched_pullbackTheta hΦF hΘ.isFunctorial hcpt)
      (isOrientation_pullSection hΦF hind hT) hlocA (EP.epFormsInftyPullback d.F 0 ω)) _ _
    (fun a C hCT hx hS K hK hKU => d.A.boundaryBranchedMeasureDim1_spec _ _ _ _ _ a C hCT hx hS
      K hK hKU)
    (fun x C hCT hx hS K hK hKU => X.boundaryBranchedMeasureDim1_spec _ _ _ _ _ x C hCT hx hS
      K hK hKU)
    (fun y D hDT hy hS K hK hKU => Y.boundaryBranchedMeasureDim1_spec _ _ _ _ _ y D hDT hy hS
      K hK hKU) hK

/-- **Theorem 11.4.5, second identity, for a diagram `d : X ←F A →Φ Y` and `n = 1`**, `X`, `Y`
with the local unique continuation property: as `theorem_11_4_4_pull_dim1` for the effective
boundary measures of Theorem 9.5.16. -/
theorem theorem_11_4_5_pull_dim1 (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) (hLX : X.X.IsLUC)
    (hLY : Y.X.IsLUC) {Θ' : Y.Obj → ℚ}
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : Y.X.IsCompactBranched Θ') (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure (0 + 1) Θ' y, D.Represents T')
    {ω : X.epFormsInfty 0} {ω' : Y.epFormsInfty 0}
    (hω : EP.epFormsInftyPullback d.F 0 ω = EP.epFormsInftyPullback d.Φ 0 ω')
    {K : Set (X.X.orbitSupp (X.X.boundaryTheta (d.pullTheta Θ')))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (0 + 1) (d.pullTheta Θ')] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (0 + 1) Θ']
        (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) ∧
      X.boundaryBranchedMeasureEffDim1 (d.isBranchedEpSubgroupoid_pullTheta hΦ hΘ')
        (d.isCompactBranched_pullTheta hΦ hΘ'.isFunctorial hcpt')
        (d.isOrientation_dPullSection hΦ hΘ' (hasIndependentTangentSums (X := Y.X) Θ') hT')
        (hlocEff_of_isLUC hLX (d.hloc_pullTheta_dim1 hΦ hΘ' hT' hloc')) ω K =
        Y.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT' (hlocEff_of_isLUC hLY hloc') ω'
          (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) := by
  have hind' := hasIndependentTangentSums (X := Y.X) Θ'
  have hΦF := d.isEquivalence_F
  have hLA := (proposition_10_1_16 hΦF).2 hLX
  have hlocA := hloc_pull_dim1 hΦ hΘ'.isFunctorial
    (isOrientation_pullSection hΦ hind' hT').isGrHatSection
    (isTransported_pull hΦ hT'.isGrHatSection) hloc'
  have hlocX := d.hloc_pullTheta_dim1 hΦ hΘ' hT' hloc'
  rw [orbitMap_image]
  exact measure_span_core_bd_dim1 hΦF hΦ
    (pullbackTheta_pushforwardTheta hΦF.full (d.Φ.isFunctorial_pullbackTheta hΘ'.isFunctorial))
    rfl (isTransported_push hΦF (isOrientation_pullSection hΦ hind' hT').isGrHatSection)
    (isTransported_pull hΦ hT'.isGrHatSection) (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
    (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
    (isOrientation_pullSection hΦ hind' hT') (d.isBranchedEpSubgroupoid_pullTheta hΦ hΘ')
    (hcov_subsingleton_of_loc hlocX) hΘ' (hcov_subsingleton_of_loc hloc')
    (fun a => (Nat.card (d.A.X.EffIsotropy a) : ℝ)⁻¹)
    (fun x => (Nat.card (X.X.EffIsotropy x) : ℝ)⁻¹)
    (fun y => (Nat.card (Y.X.EffIsotropy y) : ℝ)⁻¹)
    (fun Tc R R' hRW hR' => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Tc.card_effIsotropy_eq hΦF R R' hRW hR' (d.A.X.isLUC_iff_forall_naturalRep.1 hLA _ R)
        (X.X.isLUC_iff_forall_naturalRep.1 hLX _ R')))
    (fun Tc R R' hRW hR' => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Tc.card_effIsotropy_eq hΦ R R' hRW hR' (d.A.X.isLUC_iff_forall_naturalRep.1 hLA _ R)
        (Y.X.isLUC_iff_forall_naturalRep.1 hLY _ R'))) hω
    (d.A.boundaryBranchedMeasureEffDim1 (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
      (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
      (isOrientation_pullSection hΦ hind' hT') (hlocEff_of_isLUC hLA hlocA)
      (EP.epFormsInftyPullback d.F 0 ω)) _ _
    (fun a C hCT hx hS K hK hKU => d.A.boundaryBranchedMeasureEffDim1_spec _ _ _ _ _ a C hCT hx
      hS (d.A.X.isLUC_iff_forall_naturalRep.1 hLA _ C.rep) K hK hKU)
    (fun x C hCT hx hS K hK hKU => X.boundaryBranchedMeasureEffDim1_spec _ _ _ _ _ x C hCT hx
      hS (X.X.isLUC_iff_forall_naturalRep.1 hLX _ C.rep) K hK hKU)
    (fun y D hDT hy hS K hK hKU => Y.boundaryBranchedMeasureEffDim1_spec _ _ _ _ _ y D hDT hy
      hS (Y.X.isLUC_iff_forall_naturalRep.1 hLY _ D.rep) K hK hKU) hK

/-- **Theorem 11.4.5, first identity, for a diagram `d : X ←F A →Φ Y` and `n = 1`**, `X`, `Y`
with the local unique continuation property: as `theorem_11_4_4_push_dim1` for the effective
boundary measures of Theorem 9.5.16. -/
theorem theorem_11_4_5_push_dim1 (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) (hLX : X.X.IsLUC)
    (hLY : Y.X.IsLUC) {Θ : X.Obj → ℚ}
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hΘ : X.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.X.IsCompactBranched Θ) (hT : X.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    {ω : X.epFormsInfty 0} {ω' : Y.epFormsInfty 0}
    (hω : EP.epFormsInftyPullback d.F 0 ω = EP.epFormsInftyPullback d.Φ 0 ω')
    {K : Set (X.X.orbitSupp (X.X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (0 + 1) (d.pushTheta Θ)]
        (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) ∧
      X.boundaryBranchedMeasureEffDim1 hΘ hcpt hT (hlocEff_of_isLUC hLX hloc) ω K =
        Y.boundaryBranchedMeasureEffDim1 (d.isBranchedEpSubgroupoid_pushTheta hΦ hΘ)
          (d.isCompactBranched_pushTheta hΦ hΘ.isFunctorial hcpt)
          (d.isOrientation_dPushSection hΦ hΘ (hasIndependentTangentSums (X := X.X) Θ) hT)
          (hlocEff_of_isLUC hLY (d.hloc_pushTheta_dim1 hΦ hΘ hT hloc)) ω'
          (Subtype.val ⁻¹' (d.orbitMap '' (Subtype.val '' K))) := by
  have hind := hasIndependentTangentSums (X := X.X) Θ
  have hΦF := d.isEquivalence_F
  have hLA := (proposition_10_1_16 hΦF).2 hLX
  have hlocA := hloc_pull_dim1 hΦF hΘ.isFunctorial
    (isOrientation_pullSection hΦF hind hT).isGrHatSection
    (isTransported_pull hΦF hT.isGrHatSection) hloc
  have hlocY := d.hloc_pushTheta_dim1 hΦ hΘ hT hloc
  rw [orbitMap_image]
  exact measure_span_core_bd_dim1 hΦF hΦ rfl
    (pullbackTheta_pushforwardTheta hΦ.full (d.F.isFunctorial_pullbackTheta hΘ.isFunctorial))
    (isTransported_pull hΦF hT.isGrHatSection)
    (isTransported_push hΦ (isOrientation_pullSection hΦF hind hT).isGrHatSection)
    (isBranchedEpSubgroupoid_pullbackTheta hΦF hΘ)
    (isCompactBranched_pullbackTheta hΦF hΘ.isFunctorial hcpt)
    (isOrientation_pullSection hΦF hind hT) hΘ (hcov_subsingleton_of_loc hloc)
    (d.isBranchedEpSubgroupoid_pushTheta hΦ hΘ) (hcov_subsingleton_of_loc hlocY)
    (fun a => (Nat.card (d.A.X.EffIsotropy a) : ℝ)⁻¹)
    (fun x => (Nat.card (X.X.EffIsotropy x) : ℝ)⁻¹)
    (fun y => (Nat.card (Y.X.EffIsotropy y) : ℝ)⁻¹)
    (fun Tc R R' hRW hR' => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Tc.card_effIsotropy_eq hΦF R R' hRW hR' (d.A.X.isLUC_iff_forall_naturalRep.1 hLA _ R)
        (X.X.isLUC_iff_forall_naturalRep.1 hLX _ R')))
    (fun Tc R R' hRW hR' => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Tc.card_effIsotropy_eq hΦ R R' hRW hR' (d.A.X.isLUC_iff_forall_naturalRep.1 hLA _ R)
        (Y.X.isLUC_iff_forall_naturalRep.1 hLY _ R'))) hω
    (d.A.boundaryBranchedMeasureEffDim1 (isBranchedEpSubgroupoid_pullbackTheta hΦF hΘ)
      (isCompactBranched_pullbackTheta hΦF hΘ.isFunctorial hcpt)
      (isOrientation_pullSection hΦF hind hT) (hlocEff_of_isLUC hLA hlocA)
      (EP.epFormsInftyPullback d.F 0 ω)) _ _
    (fun a C hCT hx hS K hK hKU => d.A.boundaryBranchedMeasureEffDim1_spec _ _ _ _ _ a C hCT hx
      hS (d.A.X.isLUC_iff_forall_naturalRep.1 hLA _ C.rep) K hK hKU)
    (fun x C hCT hx hS K hK hKU => X.boundaryBranchedMeasureEffDim1_spec _ _ _ _ _ x C hCT hx
      hS (X.X.isLUC_iff_forall_naturalRep.1 hLX _ C.rep) K hK hKU)
    (fun y D hDT hy hS K hK hKU => Y.boundaryBranchedMeasureEffDim1_spec _ _ _ _ _ y D hDT hy
      hS (Y.X.isLUC_iff_forall_naturalRep.1 hLY _ D.rep) K hK hKU) hK

end Diagram

namespace EPLoc

variable {X Y : EP.{u}}

/-- **Theorem 11.4.4, 2021 p. 545 (new in the 2021 edition), second identity, for `n = 1`**: for a
generalized isomorphism `f : X → Y`, `Θ̂'` on `Y` oriented, tame (an oriented tame structure
describing `T̂'` at every point), compact, `1`-dimensional, a `0`-form `ω'` and
`K ∈ L(|supp ∂f^*Θ'|)`: `|f|(K) ∈ L(|supp ∂Θ'|)` and
`µ^{∂f^*Θ̂'}_{f^*ω'}(K) = µ^{∂Θ̂'}_{ω'}(|f|(K))`. -/
theorem theorem_11_4_4_pull_dim1 {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure (0 + 1) Θ' y, D.Represents T')
    (ω' : Y.epFormsInfty 0) {K : Set (X.X.orbitSupp (X.X.boundaryTheta (pullTheta f Θ')))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (0 + 1) (pullTheta f Θ')] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (0 + 1) Θ']
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      X.boundaryBranchedMeasureDim1
          ((rep f).isBranchedEpSubgroupoid_pullTheta (isEquivalence_rep_Φ hf) hΘ')
          ((rep f).isCompactBranched_pullTheta (isEquivalence_rep_Φ hf) hΘ'.isFunctorial hcpt')
          ((rep f).isOrientation_dPullSection (isEquivalence_rep_Φ hf) hΘ'
            (hasIndependentTangentSums (X := Y.X) Θ') hT')
          ((rep f).hloc_pullTheta_dim1 (isEquivalence_rep_Φ hf) hΘ' hT' hloc')
          (formsPullback f 0 ω') K =
        Y.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc' ω'
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) := by
  rw [orbitMap_eq_rep]
  exact (rep f).theorem_11_4_4_pull_dim1 (isEquivalence_rep_Φ hf) hΘ' hcpt' hT' hloc'
    (pullback_formsPullback f ω') hK

/-- **Theorem 11.4.4, 2021 p. 545 (new in the 2021 edition), first identity, for `n = 1`**: for a
generalized isomorphism `f : X → Y`, `Θ̂` on `X` oriented, tame, compact, `1`-dimensional, a
`0`-form `ω` and `K ∈ L(|supp ∂Θ|)`: `|f|(K) ∈ L(|supp ∂f_*Θ|)` and
`µ^{∂Θ̂}_ω(K) = µ^{∂f_*Θ̂}_{f_*ω}(|f|(K))`. -/
theorem theorem_11_4_4_push_dim1 {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {Θ : X.Obj → ℚ} {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hcpt : X.X.IsCompactBranched Θ)
    (hT : X.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    (ω : X.epFormsInfty 0) {K : Set (X.X.orbitSupp (X.X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (0 + 1) (pushTheta f Θ)]
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      X.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc ω K =
        Y.boundaryBranchedMeasureDim1
          ((rep f).isBranchedEpSubgroupoid_pushTheta (isEquivalence_rep_Φ hf) hΘ)
          ((rep f).isCompactBranched_pushTheta (isEquivalence_rep_Φ hf) hΘ.isFunctorial hcpt)
          ((rep f).isOrientation_dPushSection (isEquivalence_rep_Φ hf) hΘ
            (hasIndependentTangentSums (X := X.X) Θ) hT)
          ((rep f).hloc_pushTheta_dim1 (isEquivalence_rep_Φ hf) hΘ hT hloc)
          ((rep f).formsPush (isEquivalence_rep_Φ hf) 0 ω)
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) := by
  rw [orbitMap_eq_rep]
  exact (rep f).theorem_11_4_4_push_dim1 (isEquivalence_rep_Φ hf) hΘ hcpt hT hloc
    (pullback_formsPush hf ω).symm hK

/-- **Theorem 11.4.5, 2021 p. 545 (new in the 2021 edition), second identity, for `n = 1`**: as
`theorem_11_4_4_pull_dim1` for the effective boundary measures of Theorem 9.5.16, `X` and `Y`
having the local unique continuation property. -/
theorem theorem_11_4_5_pull_dim1 {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC) {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure (0 + 1) Θ' y, D.Represents T')
    (ω' : Y.epFormsInfty 0) {K : Set (X.X.orbitSupp (X.X.boundaryTheta (pullTheta f Θ')))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (0 + 1) (pullTheta f Θ')] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (0 + 1) Θ']
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      X.boundaryBranchedMeasureEffDim1
          ((rep f).isBranchedEpSubgroupoid_pullTheta (isEquivalence_rep_Φ hf) hΘ')
          ((rep f).isCompactBranched_pullTheta (isEquivalence_rep_Φ hf) hΘ'.isFunctorial hcpt')
          ((rep f).isOrientation_dPullSection (isEquivalence_rep_Φ hf) hΘ'
            (hasIndependentTangentSums (X := Y.X) Θ') hT')
          (hlocEff_of_isLUC hLX
            ((rep f).hloc_pullTheta_dim1 (isEquivalence_rep_Φ hf) hΘ' hT' hloc'))
          (formsPullback f 0 ω') K =
        Y.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT' (hlocEff_of_isLUC hLY hloc') ω'
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) := by
  rw [orbitMap_eq_rep]
  exact (rep f).theorem_11_4_5_pull_dim1 (isEquivalence_rep_Φ hf) hLX hLY hΘ' hcpt' hT' hloc'
    (pullback_formsPullback f ω') hK

/-- **Theorem 11.4.5, 2021 p. 545 (new in the 2021 edition), first identity, for `n = 1`**: as
`theorem_11_4_4_push_dim1` for the effective boundary measures of Theorem 9.5.16, `X` and `Y`
having the local unique continuation property. -/
theorem theorem_11_4_5_push_dim1 {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC) {Θ : X.Obj → ℚ} {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hcpt : X.X.IsCompactBranched Θ)
    (hT : X.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    (ω : X.epFormsInfty 0) {K : Set (X.X.orbitSupp (X.X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (0 + 1) (pushTheta f Θ)]
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      X.boundaryBranchedMeasureEffDim1 hΘ hcpt hT (hlocEff_of_isLUC hLX hloc) ω K =
        Y.boundaryBranchedMeasureEffDim1
          ((rep f).isBranchedEpSubgroupoid_pushTheta (isEquivalence_rep_Φ hf) hΘ)
          ((rep f).isCompactBranched_pushTheta (isEquivalence_rep_Φ hf) hΘ.isFunctorial hcpt)
          ((rep f).isOrientation_dPushSection (isEquivalence_rep_Φ hf) hΘ
            (hasIndependentTangentSums (X := X.X) Θ) hT)
          (hlocEff_of_isLUC hLY
            ((rep f).hloc_pushTheta_dim1 (isEquivalence_rep_Φ hf) hΘ hT hloc))
          ((rep f).formsPush (isEquivalence_rep_Φ hf) 0 ω)
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) := by
  rw [orbitMap_eq_rep]
  exact (rep f).theorem_11_4_5_push_dim1 (isEquivalence_rep_Φ hf) hLX hLY hΘ hcpt hT hloc
    (pullback_formsPush hf ω).symm hK

end EPLoc

end EPLocalization

end Polyfold
