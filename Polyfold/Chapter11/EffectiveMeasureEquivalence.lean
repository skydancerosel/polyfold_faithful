import Polyfold.Chapter11.MeasureEquivalence
import Polyfold.Chapter9.MeasureEffective
import Polyfold.Chapter10.EquivalenceReduced

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4, **Theorem 11.4.2** (p. 544, new in the 2021 edition), gap G.131.
Numbers and pages are the 2021 text's.

# The effective canonical measures along an equivalence

## The text, paraphrased

(Theorem 11.4.2) Let `f : X → Y` be a generalized isomorphism between ep-groupoids with the local
unique continuation property (Definition 7.2.18), `Θ̂`, `Θ̂'` oriented, tame, compact of dimension
`n`.  Then `µ^{Θ̂,eff}_ω(K) = µ^{f_*Θ̂,eff}_{f_*ω}(|f|(K))` and
`µ^{f^*Θ̂',eff}_{f^*ω'}(K) = µ^{Θ̂',eff}_{ω'}(|f|(K))`.  "The proof is similar to the previous
theorem."

## What is formalized

The proof of Theorem 11.4.1 (`MeasureEquivalence.lean`) with the effective measures of Theorem 9.5.5:

* `TransportChart.card_effIsotropy_eq`: `♯G_x^eff = ♯G_y^eff` along a transport chart, for natural
  representations `R`, `R'` with `R'.U = Q(R.U)` and the property of Definition 7.2.18
  (`TransportChart.conj` carries `ker Φ_R = T_x` onto `ker Φ_{R'} = T_y`, via the equivariance
  `Q_Φ_of_subset`).
* Under LUC every natural representation has the property (`isLUC_iff_forall_naturalRep`), and LUC
  passes along equivalences (Proposition 10.1.16), so `hcovL_pull`, `hcovL_push` give the
  covering hypotheses of Theorem 9.5.5 for `Φ^*Θ̂'`, `Φ_*Θ̂`.
* **`measure_pull_core_eff`**, **`theorem_11_4_2_pull_equiv`**, **`theorem_11_4_2_push_equiv`**,
  `integralEff_pull_equiv`, `integralEff_push_equiv`.
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

namespace EpFunctor

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Φ : EpFunctor X Y} {n : ℕ}
  {Ω Ω' : Type*} [AddCommGroup Ω] [Module ℝ Ω] [AddCommGroup Ω'] [Module ℝ Ω']
  {FX : X.FormEval n Ω} {FY : Y.FormEval n Ω'} {P : Ω' →ₗ[ℝ] Ω}
  {Θ' : Obj' → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ} {T' : Obj' → Y.PObj.OrTangent →₀ ℚ}

open OrientedTameStructure

/-- **`♯G_x^eff = ♯G_y^eff` along a transport chart** (the effective version of
`TransportChart.bijective_conj`): for natural representations `R` at `x`, `R'` at `y` with
`R.U ⊆ W`, `R'.U = Q(R.U)`, both with the property of Definition 7.2.18. -/
theorem TransportChart.card_effIsotropy_eq {x : Obj} {y : Obj'} (Tc : Φ.TransportChart x y)
    (hΦ : Φ.IsEquivalence) (R : X.NaturalRep x) (R' : Y.NaturalRep y) (hRW : R.U ⊆ Tc.W)
    (hR' : R'.U = Tc.Q '' R.U) (hL : R.HasLUC) (hL' : R'.HasLUC) :
    Nat.card (X.EffIsotropy x) = Nat.card (Y.EffIsotropy y) := by
  have hR : R.U ⊆ Tc.W ∩ Tc.Q ⁻¹' R'.U := fun u hu =>
    ⟨hRW hu, by rw [mem_preimage, hR']; exact mem_image_of_mem _ hu⟩
  set e := MulEquiv.ofBijective Tc.conj (Tc.bijective_conj hΦ)
  have hmap : (X.trivialSubgroup x).map e.toMonoidHom = Y.trivialSubgroup y := by
    rw [← R.kerΦ_eq_trivialSubgroup hL, ← R'.kerΦ_eq_trivialSubgroup hL']
    ext k
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine R'.mem_kerΦ.2 fun z hz => ?_
      rw [hR'] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      change R'.Φ (Tc.conj g) (Tc.Q u) = Tc.Q u
      rw [← Tc.Q_Φ_of_subset R R' hR g u hu, R.mem_kerΦ.1 hg u hu]
    · intro hk
      obtain ⟨g, rfl⟩ := (Tc.bijective_conj hΦ).2 k
      refine ⟨g, R.mem_kerΦ.2 fun u hu => ?_, rfl⟩
      have h1 := Tc.Q_Φ_of_subset R R' hR g u hu
      rw [R'.mem_kerΦ.1 hk _ (by rw [hR']; exact mem_image_of_mem _ hu)] at h1
      have h2 := congrArg Tc.Qinv h1
      rwa [Tc.isScDiffeoOn_Q.left_inv _ (hRW (R.mapsTo_Φ g hu)),
        Tc.isScDiffeoOn_Q.left_inv _ (hRW hu)] at h2
  rw [Nat.card_congr (X.effIsotropyEquiv x).toEquiv, Nat.card_congr (Y.effIsotropyEquiv y).toEquiv]
  exact Nat.card_congr (QuotientGroup.congr _ _ e hmap).toEquiv

/-- The covering hypothesis of Theorem 9.5.4 from that of Theorem 9.5.5. -/
theorem plainCov {Z ZM : Type u} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] [TopologicalSpace ZM] [T2Space ZM] [ParacompactSpace ZM]
    {E : EpGroupoid Z ZM} {S : Set (Set Z)} {Θ : Z → ℚ} {TE : Z → E.PObj.OrTangent →₀ ℚ}
    (hcov : ∀ x ∈ supp Θ, ∃ C : E.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents TE ∧ C.rep.HasLUC) :
    ∀ x ∈ supp Θ, ∃ C : E.OrientedTameStructure n Θ x, (∀ i, C.M i ∈ S) ∧ C.Represents TE :=
  fun x hx => let ⟨C, h1, h2, _⟩ := hcov x hx; ⟨C, h1, h2⟩

/-- **The covering hypothesis of Theorem 9.5.5 for `Φ^*Θ̂'`** (`X` with LUC). -/
theorem hcovL_pull (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P) (hLX : X.IsLUC)
    (hΘ' : Y.IsFunctorial Θ') (hT : X.IsGrHatSection T) (hTT : Φ.IsTransported T T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T' ∧ D.rep.HasLUC) :
    ∀ x ∈ supp (Φ.pullbackTheta Θ'), ∃ C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T ∧ C.rep.HasLUC := fun x hx => by
  obtain ⟨C, h1, h2⟩ := hcov_pull hΦ hP hΘ' hT hTT (plainCov hcov') x hx
  exact ⟨C, h1, h2, X.isLUC_iff_forall_naturalRep.1 hLX x C.rep⟩

/-- **The covering hypothesis of Theorem 9.5.5 for `Φ_*Θ̂`** (`Y` with LUC). -/
theorem hcovL_push (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P) (hLY : Y.IsLUC)
    {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) (hTT : Φ.IsTransported T T')
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T ∧ C.rep.HasLUC) :
    ∀ y ∈ supp (Φ.pushforwardTheta Θ), ∃ D : Y.OrientedTameStructure n (Φ.pushforwardTheta Θ) y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T' ∧ D.rep.HasLUC := fun y hy => by
  obtain ⟨D, h1, h2⟩ := hcov_push hΦ hP hΘ hTT (plainCov hcov) y hy
  exact ⟨D, h1, h2, Y.isLUC_iff_forall_naturalRep.1 hLY y D.rep⟩

/-- **The core of Theorem 11.4.2, 2021 p. 544 (new in the 2021 edition)**: for an equivalence `Φ`,
`Θ = Φ^*Θ'`, `T̂'` the orientation `T̂` moved by the transport charts, and the pull-back `P` of
the forms, `|Φ|` maps `L(|supp Θ|)` into `L(|supp Θ'|)` and
`µ_eff^Θ̂_{Pω'}(K) = µ^Θ̂'_{ω'}(|Φ|(K))`. -/
theorem measure_pull_core_eff (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P) (hn : 0 < n)
    (hLY : Y.IsLUC)
    (hΘ' : Y.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.IsCompactBranched Θ')
    (hT' : Y.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T' ∧ D.rep.HasLUC)
    {Θ : Obj → ℚ} (hΘeq : Φ.pullbackTheta Θ' = Θ) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T) (hTT : Φ.IsTransported T T')
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T ∧ C.rep.HasLUC)
    (ω' : Ω') {K : Set (X.orbitSupp Θ)} (hK : MeasurableSet[X.lebesgueSigma FX.sheetNull Θ] K) :
    MeasurableSet[Y.lebesgueSigma FY.sheetNull Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      branchedMeasureEff (FX.sheetIntegration hn) hΘ hcpt hT hcov (P ω') K =
        branchedMeasureEff (FY.sheetIntegration hn) hΘ' hcpt' hT' hcov' ω'
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := by
  subst hΘeq
  have hΘf := hΘ'.isFunctorial
  have hLX : X.IsLUC := (proposition_10_1_16 hΦ).2 hLY
  have hcov0 : ∀ x ∈ supp (Φ.pullbackTheta Θ'),
      ∃ C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x,
        (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T :=
    fun x hx => let ⟨C, h1, h2, _⟩ := hcov x hx; ⟨C, h1, h2⟩
  have hcov'0 := plainCov hcov'
  have hTSX : X.HasTameSheetsIn FX.sheets (Φ.pullbackTheta Θ') := hasTameSheetsIn_of_hcov hcov0
  have hTSY : Y.HasTameSheetsIn FY.sheets Θ' := hasTameSheetsIn_of_hcov hcov'0
  have hcovX : ∀ x ∈ supp (Φ.pullbackTheta Θ'),
      ∃ C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x, ∀ i, C.M i ∈ FX.sheets :=
    fun x hx => let ⟨C, hC, _⟩ := hcov x hx; ⟨C, hC⟩
  have hm := measurable_suppInv hΦ hP hΘf hTSX hTSY hcovX
  have hmeas : ∀ K : Set (X.orbitSupp (Φ.pullbackTheta Θ')),
      MeasurableSet[X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ')] K →
      MeasurableSet[Y.lebesgueSigma FY.sheetNull Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := fun K hK => by
    rw [← preimage_suppInv hΦ hΘf K]; exact hm hK
  refine ⟨hmeas K hK, ?_⟩
  let _ : MeasurableSpace (X.orbitSupp (Φ.pullbackTheta Θ')) :=
    X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ')
  let _ : MeasurableSpace (Y.orbitSupp Θ') := Y.lebesgueSigma FY.sheetNull Θ'
  have : CompactSpace (X.orbitSupp (Φ.pullbackTheta Θ')) := isCompact_iff_compactSpace.1 hcpt
  set μ₁ := branchedMeasureEff (FX.sheetIntegration hn) hΘ hcpt hT hcov (P ω')
  set μY := branchedMeasureEff (FY.sheetIntegration hn) hΘ' hcpt' hT' hcov' ω'
  set μ₂ : SignedMeasure (X.orbitSupp (Φ.pullbackTheta Θ')) := μY.map (suppInv hΦ hΘf)
  have hμ₂ : ∀ K, MeasurableSet K →
      μ₂ K = μY (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := fun K hK => by
    rw [VectorMeasure.map_apply _ hm hK, preimage_suppInv]
  -- the local agreement on a pulled-back structure: (11.12) = (11.13)
  have hloc : ∀ {x : Obj} (C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x),
      IsPulled FY Φ hΘf T' C → ∀ K, MeasurableSet K → Subtype.val '' K ⊆ X.π '' C.U →
      μ₂ K = μ₁ K := by
    intro x C hC K hK hKU
    have hS := hC.mem_sheets hP
    have hR := hC.represents hΦ hT.isGrHatSection hTT
    obtain ⟨y, Tc, D, hDS, hDT, R, R', h1, h2, h3, h4, rfl⟩ := hC
    have hval := val_image_preimage (Θ' := Θ') (Φ := Φ)
      (fun p hp => orbitMap_mem_orbitSupp hΘf hp) K
    have hD'S := D.restrictRep_mem_sheets R' h1 hDS
    have hK' := hmeas K hK
    have hKU' : Subtype.val '' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K)) :
        Set (Y.orbitSupp Θ')) ⊆ Y.π '' (D.restrictRep R' h1).U := by
      rw [hval, restrictRep_U, h3]
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨u, hu, hπ⟩ := hKU hp
      rw [pullStructure_U] at hu
      exact ⟨Tc.Q u, mem_image_of_mem _ hu, by rw [Tc.π_Q (h2 hu), ← Φ.orbitMap_π, hπ]⟩
    have hW' : ∀ {z}, z ∈ (D.restrictRep R' h1).U → z ∈ Tc.W' := fun hz =>
      restrictRep_U_subset_W' Tc D R R' h1 h2 h3 hz
    have hA := (D.restrictRep R' h1).isMeas_preimage hTSY hD'S hK'
    have hB : ∀ i, X.π ⁻¹' (Subtype.val '' K) ∩ Tc.Qinv '' (D.restrictRep R' h1).M i =
        Tc.Qinv '' (Y.π ⁻¹' (Subtype.val '' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K)) :
          Set (Y.orbitSupp Θ'))) ∩ (D.restrictRep R' h1).M i) := by
      intro i
      ext u
      constructor
      · rintro ⟨hu, z, hz, rfl⟩
        have hzW' := hW' ((D.restrictRep R' h1).subset_U i hz)
        refine ⟨z, ⟨?_, hz⟩, rfl⟩
        rw [mem_preimage, hval]
        refine ⟨_, hu, ?_⟩
        rw [Φ.orbitMap_π, ← Tc.π_Q (Tc.isScDiffeoOn_Q.mapsTo_inv hzW'),
          Tc.isScDiffeoOn_Q.right_inv z hzW']
      · rintro ⟨z, ⟨hzA, hz⟩, rfl⟩
        have hzW' := hW' ((D.restrictRep R' h1).subset_U i hz)
        refine ⟨?_, z, hz, rfl⟩
        rw [mem_preimage, hval] at hzA
        obtain ⟨p, hp, he⟩ := hzA
        rw [← Tc.isScDiffeoOn_Q.right_inv z hzW', Tc.π_Q (Tc.isScDiffeoOn_Q.mapsTo_inv hzW'),
          ← Φ.orbitMap_π] at he
        rw [mem_preimage, ← Φ.injective_orbitMap_of_full hΦ.full he]
        exact hp
    have e := (D.restrictRep R' h1).sheetSum_move (FS := FY) (FT := FX) hn
      Tc.isScDiffeoOn_Q.symm _ _ _ R _ _ hD'S hS
      (fun i => Tc.evCompatOn_Qinv hP ω'
        (((D.restrictRep R' h1).isSmoothSubmanifold i).inter_isOpen Tc.isOpen_W')
        inter_subset_right) hA hB
    have hcard : (Nat.card (Y.EffIsotropy y) : ℝ) = Nat.card (X.EffIsotropy x) := by
      exact_mod_cast (Tc.card_effIsotropy_eq hΦ R R' h2 h3
        (X.isLUC_iff_forall_naturalRep.1 hLX x R) (Y.isLUC_iff_forall_naturalRep.1 hLY y R')).symm
    rw [hμ₂ K hK, branchedMeasureEff_apply _ hΘ' hcpt' hT' hcov' ω' (D.restrictRep R' h1) hD'S
      (D.represents_restrictRep R' h1 hDT)
      (Y.isLUC_iff_forall_naturalRep.1 hLY _ _) hK' hKU',
      branchedMeasureEff_apply _ hΘ hcpt hT hcov (P ω') _ hS hR
      (X.isLUC_iff_forall_naturalRep.1 hLX _ _) hK hKU, localMeasureEff, localMeasureEff,
      hcard]
    exact congrArg _ e.symm
  -- gluing (Theorem 9.5.4's uniqueness) over the pulled-back structures
  let J := {j : Σ x, X.OrientedTameStructure n (Φ.pullbackTheta Θ') x //
    IsPulled FY Φ hΘf T' j.2}
  let O : J → Set (X.orbitSupp (Φ.pullbackTheta Θ')) := fun j => Subtype.val ⁻¹' (X.π '' j.1.2.U)
  have hO : ∀ j, IsOpen (O j) := fun j =>
    (X.proposition_7_1_8 _ j.1.2.isOpen_U).preimage continuous_subtype_val
  have hcovO : ⋃ j, O j = univ := eq_univ_of_forall fun q => by
    obtain ⟨x, hx, hxq⟩ := q.2
    obtain ⟨C, hC⟩ := exists_isPulled hΦ hΘf hcov'0 hx
    exact mem_iUnion.2 ⟨⟨⟨x, C⟩, hC⟩, x, C.mem_U, hxq⟩
  obtain ⟨Ψ, -, huniq⟩ := existsUnique_linearMap_signedMeasure_of_openCover (V := ℝ)
    (borel_le_borelNullSigma _) O hO hcovO (fun _ => LinearMap.toSpanSingleton ℝ _ μ₁)
    (fun _ _ _ _ _ _ => rfl)
  have e1 := huniq (LinearMap.toSpanSingleton ℝ _ μ₁) fun _ _ _ _ _ => rfl
  have e2 := huniq (LinearMap.toSpanSingleton ℝ _ μ₂) fun j t K hK hKO => by
    change (t • μ₂) K = (t • μ₁) K
    change t • μ₂ K = t • μ₁ K
    rw [hloc j.1.2 j.2 K hK (by rintro _ ⟨q, hq, rfl⟩; exact hKO hq)]
  have e3 := congrArg (fun L : ℝ →ₗ[ℝ] SignedMeasure (X.orbitSupp (Φ.pullbackTheta Θ')) => L 1)
    (e2.trans e1.symm)
  simp only [LinearMap.toSpanSingleton_apply, one_smul] at e3
  rw [← hμ₂ K hK, e3]

/-- **Theorem 11.4.2, 2021 p. 544 (new in the 2021 edition), second identity, for an
equivalence `Φ : X → Y`**: for `Θ̂'` on `Y` oriented, tame (with sheets in the class), compact,
of dimension `n`, and `K ∈ L(|supp Φ^*Θ|)`, `|Φ|(K) ∈ L(|supp Θ'|)` and
`µ_eff^{Φ^*Θ̂'}_{Φ^*ω'}(K) = µ^Θ̂'_{ω'}(|Φ|(K))`.  (`Φ^*Θ̂' = (Φ^*Θ', Φ^*T̂')` is oriented by
Theorem 11.3.5, which asks for `HasIndependentTangentSums`.) -/
theorem theorem_11_4_2_pull_equiv (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hn : 0 < n) (hLY : Y.IsLUC) (hΘ' : Y.IsBranchedEpSubgroupoid Θ')
    (hcpt' : Y.IsCompactBranched Θ')
    (hind' : Y.HasIndependentTangentSums Θ') (hT' : Y.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T' ∧ D.rep.HasLUC)
    (ω' : Ω') {K : Set (X.orbitSupp (Φ.pullbackTheta Θ'))}
    (hK : MeasurableSet[X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ')] K) :
    MeasurableSet[Y.lebesgueSigma FY.sheetNull Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      branchedMeasureEff (FX.sheetIntegration hn) (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
        (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
        (isOrientation_pullSection hΦ hind' hT')
        (hcovL_pull hΦ hP ((proposition_10_1_16 hΦ).2 hLY) hΘ'.isFunctorial
          (isOrientation_pullSection hΦ hind' hT').isGrHatSection
          (isTransported_pull hΦ hT'.isGrHatSection) hcov') (P ω') K =
        branchedMeasureEff (FY.sheetIntegration hn) hΘ' hcpt' hT' hcov' ω'
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) :=
  measure_pull_core_eff hΦ hP hn hLY hΘ' hcpt' hT' hcov' rfl _ _ _
    (isTransported_pull hΦ hT'.isGrHatSection) _ ω' hK

/-- **Theorem 11.4.2, 2021 p. 544 (new in the 2021 edition), first identity, for an
equivalence `Φ : X → Y`**: for `Θ̂` on `X` oriented, tame (with sheets in the class), compact, of
dimension `n`, `K ∈ L(|supp Θ|)` and `Φ_*ω = ω'` (the form with `Φ^*ω' = ω`), `|Φ|(K) ∈
L(|supp Φ_*Θ|)` and `µ_eff^Θ̂_ω(K) = µ^{Φ_*Θ̂}_{Φ_*ω}(|Φ|(K))`. -/
theorem theorem_11_4_2_push_equiv (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hn : 0 < n) (hLX : X.IsLUC) {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ)
    (hind : X.HasIndependentTangentSums Θ) (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T ∧ C.rep.HasLUC)
    {ω : Ω} {ω' : Ω'} (hω : P ω' = ω) {K : Set (X.orbitSupp Θ)}
    (hK : MeasurableSet[X.lebesgueSigma FX.sheetNull Θ] K) :
    MeasurableSet[Y.lebesgueSigma FY.sheetNull (Φ.pushforwardTheta Θ)]
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      branchedMeasureEff (FX.sheetIntegration hn) hΘ hcpt hT hcov ω K =
        branchedMeasureEff (FY.sheetIntegration hn) (isBranchedEpSubgroupoid_pushforwardTheta hΦ hΘ)
          (isCompactBranched_pushforwardTheta Φ hΦ.full hΘ.isFunctorial hcpt)
          (isOrientation_pushSection hΦ hΘ hind hT)
          (hcovL_push hΦ hP ((proposition_10_1_16 hΦ).1 hLX) hΘ.isFunctorial
            (isTransported_push hΦ hT.isGrHatSection) hcov) ω'
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := by
  subst hω
  exact measure_pull_core_eff hΦ hP hn ((proposition_10_1_16 hΦ).1 hLX) _ _ _ _
      (pullbackTheta_pushforwardTheta hΦ.full hΘ.isFunctorial)
    hΘ hcpt hT (isTransported_push hΦ hT.isGrHatSection) hcov ω' hK

/-- **Theorem 11.4.2 for the effective integrals** (`K = |supp|`, Definition 9.5.6):
`∮_{Φ^*Θ̂'} Φ^*ω' = ∮_{Θ̂'} ω'`. -/
theorem integralEff_pull_equiv (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hn : 0 < n) (hLY : Y.IsLUC) (hΘ' : Y.IsBranchedEpSubgroupoid Θ')
    (hcpt' : Y.IsCompactBranched Θ')
    (hind' : Y.HasIndependentTangentSums Θ') (hT' : Y.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T' ∧ D.rep.HasLUC) (ω' : Ω') :
    branchedIntegralEff (FX.sheetIntegration hn) (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
        (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
        (isOrientation_pullSection hΦ hind' hT')
        (hcovL_pull hΦ hP ((proposition_10_1_16 hΦ).2 hLY) hΘ'.isFunctorial
          (isOrientation_pullSection hΦ hind' hT').isGrHatSection
          (isTransported_pull hΦ hT'.isGrHatSection) hcov') (P ω') =
      branchedIntegralEff (FY.sheetIntegration hn) hΘ' hcpt' hT' hcov' ω' := by
  have h := (theorem_11_4_2_pull_equiv hΦ hP hn hLY hΘ' hcpt' hind' hT' hcov' ω'
    MeasurableSet.univ).2
  rw [image_univ_eq_univ hΦ hΘ'.isFunctorial rfl] at h
  exact h

/-- **Theorem 11.4.2 for the effective integrals** (`K = |supp|`, Definition 9.5.6):
`∮_Θ̂ ω = ∮_{Φ_*Θ̂} Φ_*ω`. -/
theorem integralEff_push_equiv (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hn : 0 < n) (hLX : X.IsLUC) {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ)
    (hind : X.HasIndependentTangentSums Θ) (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T ∧ C.rep.HasLUC)
    {ω : Ω} {ω' : Ω'} (hω : P ω' = ω) :
    branchedIntegralEff (FX.sheetIntegration hn) hΘ hcpt hT hcov ω =
      branchedIntegralEff (FY.sheetIntegration hn) (isBranchedEpSubgroupoid_pushforwardTheta hΦ hΘ)
        (isCompactBranched_pushforwardTheta Φ hΦ.full hΘ.isFunctorial hcpt)
        (isOrientation_pushSection hΦ hΘ hind hT)
        (hcovL_push hΦ hP ((proposition_10_1_16 hΦ).1 hLX) hΘ.isFunctorial
          (isTransported_push hΦ hT.isGrHatSection) hcov) ω' := by
  have h := (theorem_11_4_2_push_equiv hΦ hP hn hLX hΘ hcpt hind hT hcov hω MeasurableSet.univ).2
  rw [image_univ_eq_univ hΦ (isFunctorial_pushforwardTheta hΦ.full hΘ.isFunctorial)
    (pullbackTheta_pushforwardTheta hΦ.full hΘ.isFunctorial)] at h
  exact h

end EpFunctor

end Polyfold
