import Polyfold.Chapter16.PointCountEquivalence
import Polyfold.Chapter15.RestrictedIntegralCore

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 11,
§11.4, **Theorems 11.4.1, 11.4.2** (pp. 543–544) **for dimension `n = 0`**, in the form used in
§15.4 and Chapter 16 for the restriction of an ep-groupoid to a saturated open set.

# The weighted counts along a full and faithful local sc-diffeomorphism

## The text, paraphrased

(Theorem 11.4.1) `µ^{f^*Θ̂'}_{f^*ω'}(K) = µ^Θ̂'_{ω'}(|f|(K))`; the proof is local on the support.
For `n = 0` the sheets are oriented points and the measures are the weighted signed counts of
Definition 9.5.6.

## What is formalized (namespace `Polyfold.EpFunctor`)

The statements of `Polyfold/Chapter15/RestrictedIntegralCore.lean` for the integration of
`0`-forms over oriented points (`EP.zeroFormIntegration`).  The functor `Φ : X → Y` is a local
sc-diffeomorphism on objects, full, and bijective on the isotropy groups; it need not be
essentially surjective, and `|supp Θ'|` lies in the image of `|Φ|`.

* `TransportChart.zeroFormEval_pull_Q_of`: `(Φ^*ω')(u) = ω'(Q(u))` on a transport chart.
* `isPointTame_pullSection_of`: `Φ^*Θ̂'` is tame of dimension `0` if `Θ̂'` is.
* `exists_local_comparison_point`: the local comparison (11.12) = (11.13) for oriented points.
* **`pointIntegral_pull_of`**, **`pointIntegralEff_pull_of`**: `∫_{Φ^*Θ̂'} Φ^*ω' = ∫_{Θ̂'} ω'`
  and `∮_{Φ^*Θ̂'} Φ^*ω' = ∮_{Θ̂'} ω'` for `0`-forms.
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

namespace EpFunctor

open OrientedTameStructure

variable {A B : EP.{u}} {Φ : EpFunctor A.X B.X}
  {Θ' : B.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} {T' : B.Obj → B.X.PObj.OrTangent →₀ ℚ}

/-- **On a transport chart, `(Φ^*ω')(u) = ω'(Q(u))`** for a `0`-form `ω'`, for a functor which is
a local sc-diffeomorphism on objects. -/
theorem TransportChart.zeroFormEval_pull_Q_of {x : A.Obj} {y : B.Obj}
    (hd : A.X.PObj.IsLocalScDiffeo B.X.PObj Φ.obj)
    (Tc : Φ.TransportChart x y) (ω' : B.epFormsInfty 0) {u : A.Obj} (hu : u ∈ Tc.W) :
    A.zeroFormEval (EP.epFormsInftyPullback Φ 0 ω') u = B.zeroFormEval ω' (Tc.Q u) := by
  by_cases hs : u ∈ A.X.PObj.smoothSet
  · have hFs : Φ.obj u ∈ B.X.PObj.smoothSet := (hd.mem_smoothSet_iff u).2 hs
    rw [EP.zeroFormEval_epFormsInftyPullback Φ ω' hs hFs, ← Tc.src_ψ u hu, ← Tc.tgt_ψ u hu,
      B.zeroFormEval_src_eq_tgt]
  · have hQs : Tc.Q u ∉ B.X.PObj.smoothSet := fun h => hs ((Tc.mem_smoothSet_iff hd hu).1 h)
    rw [A.zeroFormEval_of_not_mem _ hs, B.zeroFormEval_of_not_mem _ hQs]

/-- **`Φ^*Θ̂' = (Φ^*Θ', Φ^*T̂')` is tame of dimension `0`** if `Θ̂'` is: a structure of `Θ̂'` at
`Φ(x)` with point sheets, restricted and moved back by the chart `Q`, has point sheets and
describes `Φ^*T̂'` at `x`. -/
theorem isPointTame_pullSection_of (hd : A.X.PObj.IsLocalScDiffeo B.X.PObj Φ.obj)
    (hiso : ∀ x, Bijective (Φ.isotropyHom x)) (hΘ' : B.X.IsFunctorial Θ')
    (hT' : B.X.IsGrHatSection T') (hloc' : B.X.IsPointTame Θ' T') :
    A.X.IsPointTame (Φ.pullbackTheta Θ') (Φ.pullSection T') := fun x hx => by
  obtain ⟨Tc⟩ := nonempty_transportChart_unit hd x
  obtain ⟨D, hDS, hDT⟩ := hloc' (Φ.obj x) hx
  obtain ⟨V, hxV, hVP⟩ := A.X.exists_hasPropernessProperty x
  obtain ⟨R₀, hR₀⟩ := A.X.theorem_7_1_13 x hVP.1 hxV
  obtain ⟨R, R', hRR₀, hRW, hRD, hR'⟩ := Tc.exists_rep_push_of hiso R₀ D.isOpen_U D.mem_U
  have h1 : R'.U ⊆ D.U := hR' ▸ hRD
  have h4 : A.X.HasPropernessProperty R.U := hVP.mono R.isOpen_U (hRR₀.trans hR₀)
  have hS := isGrHatSection_pullSection hd hT'
  refine ⟨pullStructure Tc (Tc.pullbackTheta_Q hΘ') D R R' h1 hRW hR' h4, fun i => ?_, ?_⟩
  · have hM : (pullStructure Tc (Tc.pullbackTheta_Q hΘ') D R R' h1 hRW hR' h4).M i =
        Tc.Qinv '' ((D.M i ∩ R'.U) ∩ Tc.W') := rfl
    rw [hM]
    rcases inter_mem_pointSheets (inter_mem_pointSheets (hDS i) R'.U) Tc.W' with
      h0 | ⟨p, hp, hpe⟩
    · left; rw [h0, image_empty]
    · right
      have hpW' : p ∈ Tc.W' := (hpe ▸ mem_singleton p : p ∈ (D.M i ∩ R'.U) ∩ Tc.W').2
      refine ⟨Tc.Qinv p, ?_, by rw [hpe, image_singleton]⟩
      refine (Tc.mem_smoothSet_iff hd (Tc.isScDiffeoOn_Q.mapsTo_inv hpW')).1 ?_
      rw [Tc.isScDiffeoOn_Q.right_inv p hpW']; exact hp
  · refine (D.restrictRep R' h1).represents_move _ _ _ _ _ _ _
      (D.represents_restrictRep R' h1 hDT) ?_
    rintro _ ⟨z, hz, rfl⟩ hus
    have hzW' := restrictRep_U_subset_W' Tc D R R' h1 hRW hR' hz
    have hgz := Tc.isScDiffeoOn_Q.mapsTo_inv hzW'
    have hzs : z ∈ B.X.PObj.smoothSet := by
      have h := (Tc.mem_smoothSet_iff hd hgz).2 hus
      rwa [Tc.isScDiffeoOn_Q.right_inv z hzW'] at h
    refine ⟨?_, ?_⟩
    · rw [Tc.isScDiffeoOn_Q.right_inv z hzW']; exact hzs
    · rw [Tc.isScDiffeoOn_Q.right_inv z hzW']
      exact rel_symm Tc.isScDiffeoOn_Q hS (Tc.pullSection_Q hd hT') hzW' hus

section Integrals

variable (hd : A.X.PObj.IsLocalScDiffeo B.X.PObj Φ.obj) (hfull : Φ.toFunctor.Full)
  (hiso : ∀ x, Bijective (Φ.isotropyHom x))

include hd hfull hiso in
/-- **The local data of the comparison (11.12) = (11.13) for oriented points** at a point `x` of
`supp Φ^*Θ'`: a structure `C` of `Φ^*Θ̂'` at `x` with point sheets, restricted to `C₁` and moved
by the chart `Q` to a structure `D` of `Θ̂'` at `Φ(x)` with point sheets, such that for every
Borel set `K ⊆ |D.U|` of `|supp Θ'|` the sums of `Φ^*ω'` over `C₁` and of `ω'` over `D` agree,
with the same orders of the (effective) isotropy groups. -/
theorem exists_local_comparison_point (hΘ' : B.X.IsFunctorial Θ')
    (hTT : Φ.IsTransported T T')
    {x : A.Obj} (C : A.X.OrientedTameStructure 0 (Φ.pullbackTheta Θ') x)
    (hCS : ∀ i, C.M i ∈ pointSheets A.X) (hCT : C.Represents T) :
    ∃ (C₁ : A.X.OrientedTameStructure 0 (Φ.pullbackTheta Θ') x)
      (D : B.X.OrientedTameStructure 0 Θ' (Φ.obj x)),
      (∀ i, C₁.M i ∈ pointSheets A.X) ∧ C₁.Represents T ∧ (∀ i, D.M i ∈ pointSheets B.X) ∧
      D.Represents T' ∧
      Nat.card (B.X.Isotropy (Φ.obj x)) = Nat.card (A.X.Isotropy x) ∧
      (C₁.rep.HasLUC → D.rep.HasLUC →
        Nat.card (B.X.EffIsotropy (Φ.obj x)) = Nat.card (A.X.EffIsotropy x)) ∧
      ∀ (ω' : B.epFormsInfty 0) (K : Set (B.X.orbitSupp Θ')),
        MeasurableSet[borel (B.X.orbitSupp Θ')] K →
        Subtype.val '' K ⊆ B.X.π '' D.U →
        MeasurableSet[A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X))
            (Φ.pullbackTheta Θ')]
            (suppMap (Φ := Φ) hΘ' ⁻¹' K) ∧
          Subtype.val '' (suppMap (Φ := Φ) hΘ' ⁻¹' K) ⊆ A.X.π '' C₁.U ∧
          D.sheetSum B.zeroFormIntegration ω' (B.X.π ⁻¹' (Subtype.val '' K)) =
            C₁.sheetSum A.zeroFormIntegration (EP.epFormsInftyPullback Φ 0 ω')
              (A.X.π ⁻¹' (Subtype.val '' (suppMap (Φ := Φ) hΘ' ⁻¹' K))) := by
  obtain ⟨Tc⟩ := nonempty_transportChart_unit hd x
  obtain ⟨V', hyV', hV'P⟩ := B.X.exists_hasPropernessProperty (Φ.obj x)
  obtain ⟨R, R', hRC, hRW, hRV', hR'⟩ := Tc.exists_rep_push_of hiso C.rep hV'P.1 hyV'
  have hRU : R.U ⊆ C.U := C.U_eq ▸ hRC
  set C₁ := C.restrictRep R hRU with hC₁
  have hP' : B.X.HasPropernessProperty (Tc.Q '' C₁.U) := hV'P.mono (hR' ▸ R'.isOpen_U) hRV'
  have hΘQ := Tc.pullbackTheta_Q hΘ'
  have hC₁S : ∀ i, C₁.M i ∈ pointSheets A.X := fun i => inter_mem_pointSheets (hCS i) R.U
  have hC₁T : C₁.Represents T := C.represents_restrictRep R hRU hCT
  set D := C₁.move Tc.isScDiffeoOn_Q hRW Tc.Q_self hΘQ R' hR' hP' with hD
  have hDU : D.U = Tc.Q '' R.U := C₁.move_U Tc.isScDiffeoOn_Q hRW Tc.Q_self hΘQ R' hR' hP'
  have hDS : ∀ i, D.M i ∈ pointSheets B.X := fun i => by
    have hM : D.M i = Tc.Q '' ((C.M i ∩ R.U) ∩ Tc.W) := rfl
    rw [hM]
    rcases inter_mem_pointSheets (inter_mem_pointSheets (hCS i) R.U) Tc.W with h0 | ⟨p, hp, hpe⟩
    · left; rw [h0, image_empty]
    · right
      have hpW : p ∈ Tc.W := (hpe ▸ mem_singleton p : p ∈ (C.M i ∩ R.U) ∩ Tc.W).2
      exact ⟨Tc.Q p, (Tc.mem_smoothSet_iff hd hpW).2 hp, by rw [hpe, image_singleton]⟩
  have hDT : D.Represents T' := by
    refine C₁.represents_move _ _ _ _ _ _ _ hC₁T ?_
    rintro _ ⟨u, hu, rfl⟩ hzs
    have huW := hRW hu
    have hus := (Tc.mem_smoothSet_iff hd huW).1 hzs
    rw [Tc.isScDiffeoOn_Q.left_inv u huW]
    exact ⟨hus, hTT Tc u huW hus⟩
  refine ⟨C₁, D, hC₁S, hC₁T, hDS, hDT,
    (Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj_of hiso))).symm,
    fun hL hL' => (Tc.card_effIsotropy_eq_of hiso R R' hRW hR' hL hL').symm, ?_⟩
  intro ω' K hK hKU
  have hmc : @Measurable _ _
      (A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) (Φ.pullbackTheta Θ'))
      (borel (B.X.orbitSupp Θ')) (suppMap (Φ := Φ) hΘ') := fun s hs =>
    borel_le_borelNullSigma _ _ ((continuous_suppMap (Φ := Φ) hΘ').borel_measurable hs)
  have hK₁ : MeasurableSet[A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X))
      (Φ.pullbackTheta Θ')]
      (suppMap (Φ := Φ) hΘ' ⁻¹' K) := hmc hK
  have hKU₁ : Subtype.val '' (suppMap (Φ := Φ) hΘ' ⁻¹' K) ⊆ A.X.π '' C₁.U := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨z, hz, hzp⟩ := hKU (mem_image_of_mem _ hp)
    rw [hDU] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    refine ⟨u, hu, ?_⟩
    apply Φ.injective_orbitMap_of_full hfull
    rw [Φ.orbitMap_π, ← Tc.π_Q (hRW hu), hzp]
    rfl
  refine ⟨hK₁, hKU₁, ?_⟩
  have hω : ∀ u ∈ Tc.W, B.zeroFormEval ω' (Tc.Q u) =
      A.zeroFormEval (EP.epFormsInftyPullback Φ 0 ω') u := fun u hu =>
    (Tc.zeroFormEval_pull_Q_of hd ω' hu).symm
  refine C₁.sheetSum_move_point Tc.isScDiffeoOn_Q hRW Tc.Q_self hΘQ R' hR' hP'
    (fun i => subsingleton_of_mem_pointSheets (hC₁S i)) hω fun i => ?_
  ext z
  constructor
  · rintro ⟨hzK, u, hu, rfl⟩
    refine ⟨u, ⟨?_, hu⟩, rfl⟩
    obtain ⟨k, hk, hkz⟩ := hzK
    have huW : u ∈ Tc.W := hRW (C₁.subset_U i hu)
    have hus : A.X.π u ∈ A.X.orbitSupp (Φ.pullbackTheta Θ') :=
      ⟨u, C₁.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i hu, rfl⟩
    refine ⟨⟨A.X.π u, hus⟩, ?_, rfl⟩
    have he : suppMap (Φ := Φ) hΘ' ⟨A.X.π u, hus⟩ = k := by
      apply Subtype.ext
      change Φ.orbitMap (A.X.π u) = k.1
      rw [Φ.orbitMap_π, ← Tc.π_Q huW, hkz]
    rw [mem_preimage, he]
    exact hk
  · rintro ⟨u, ⟨⟨p, hp, hpu⟩, hu⟩, rfl⟩
    have huW : u ∈ Tc.W := hRW (C₁.subset_U i hu)
    refine ⟨⟨_, hp, ?_⟩, u, hu, rfl⟩
    change Φ.orbitMap p.1 = B.X.π (Tc.Q u)
    rw [hpu, Φ.orbitMap_π, Tc.π_Q huW]


include hd hfull hiso in
/-- **Theorem 11.4.1, 2021 p. 543, for the weighted counts (`n = 0`), along a full and faithful
local sc-diffeomorphism** `Φ : X → Y` whose image contains the support: for `Θ̂'` on `Y` oriented,
tame of dimension `0` and compact, with `|supp Θ'| ⊆ |Φ|(|X|)`,
`∫_{Φ^*Θ̂'} Φ^*ω' = ∫_{Θ̂'} ω'`. -/
theorem pointIntegral_pull_of (hΘ' : B.X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : B.X.IsCompactBranched Θ')
    (hT' : B.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : B.X.OrientedTameStructure 0 Θ' y,
      (∀ i, D.M i ∈ pointSheets B.X) ∧ D.Represents T')
    (hrange : B.X.orbitSupp Θ' ⊆ range Φ.orbitMap)
    (hΘ : A.X.IsBranchedEpSubgroupoid (Φ.pullbackTheta Θ'))
    (hcpt : A.X.IsCompactBranched (Φ.pullbackTheta Θ'))
    (hT : A.X.IsOrientation (Φ.pullbackTheta Θ') T) (hTT : Φ.IsTransported T T')
    (hcov : ∀ x ∈ supp (Φ.pullbackTheta Θ'),
      ∃ C : A.X.OrientedTameStructure 0 (Φ.pullbackTheta Θ') x,
        (∀ i, C.M i ∈ pointSheets A.X) ∧ C.Represents T)
    (ω' : B.epFormsInfty 0) :
    branchedIntegral A.zeroFormIntegration hΘ hcpt hT hcov (EP.epFormsInftyPullback Φ 0 ω') =
      branchedIntegral B.zeroFormIntegration hΘ' hcpt' hT' hcov' ω' := by
  have hΘf := hΘ'.isFunctorial
  have : CompactSpace (B.X.orbitSupp Θ') := isCompact_iff_compactSpace.1 hcpt'
  have hmc : @Measurable _ _
      (A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) (Φ.pullbackTheta Θ'))
      (borel (B.X.orbitSupp Θ')) (suppMap (Φ := Φ) hΘf) := fun s hs =>
    borel_le_borelNullSigma _ _ ((continuous_suppMap (Φ := Φ) hΘf).borel_measurable hs)
  set μ₁ := branchedMeasure A.zeroFormIntegration hΘ hcpt hT hcov
    (EP.epFormsInftyPullback Φ 0 ω') with hμ₁
  set μY := branchedMeasure B.zeroFormIntegration hΘ' hcpt' hT' hcov' ω' with hμY
  set ν : @SignedMeasure (B.X.orbitSupp Θ') (borel _) :=
    @VectorMeasure.map _ _
      (A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) (Φ.pullbackTheta Θ'))
      (borel (B.X.orbitSupp Θ')) ℝ _ _ μ₁ (suppMap (Φ := Φ) hΘf) with hν
  have hνK : ∀ K : Set (B.X.orbitSupp Θ'), MeasurableSet[borel (B.X.orbitSupp Θ')] K →
      ν K = μ₁ (suppMap (Φ := Φ) hΘf ⁻¹' K) := fun K hK =>
    @VectorMeasure.map_apply _ _
      (A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) (Φ.pullbackTheta Θ'))
      (borel (B.X.orbitSupp Θ')) ℝ _ _ μ₁ _ hmc K hK
  have key := signedMeasure_univ_eq_of_local (borel_le_borelNullSigma _) le_rfl μY ν fun q => by
    obtain ⟨p, hp⟩ := hrange q.2
    have hps : p ∈ A.X.orbitSupp (Φ.pullbackTheta Θ') := by
      rw [Φ.orbitSupp_pullbackTheta hΘf, mem_preimage, hp]; exact q.2
    obtain ⟨x, hx, rfl⟩ := hps
    obtain ⟨C, hCS, hCT⟩ := hcov x hx
    obtain ⟨C₁, D, hC₁S, hC₁T, hDS, hDT, hcard, -, hsum⟩ :=
      exists_local_comparison_point hd hfull hiso hΘf hTT C hCS hCT
    refine ⟨Subtype.val ⁻¹' (B.X.π '' D.U),
      (B.X.proposition_7_1_8 _ D.isOpen_U).preimage continuous_subtype_val,
      ⟨Φ.obj x, D.mem_U, by rw [← hp, Φ.orbitMap_π]⟩, fun K hK hKN => ?_⟩
    have hKU : Subtype.val '' K ⊆ B.X.π '' D.U := by
      rintro _ ⟨k, hk, rfl⟩
      exact hKN hk
    obtain ⟨hK₁, hKU₁, e⟩ := hsum ω' K hK hKU
    rw [hνK K hK, hμ₁, hμY,
      branchedMeasure_apply _ hΘ hcpt hT hcov (EP.epFormsInftyPullback Φ 0 ω') C₁ hC₁S hC₁T hK₁
        hKU₁,
      branchedMeasure_apply _ hΘ' hcpt' hT' hcov' ω' D hDS hDT
        (borel_le_borelNullSigma _ _ hK) hKU, localMeasure, localMeasure, hcard, e]
  have hu := hνK univ (@MeasurableSet.univ _ (borel _))
  rw [preimage_univ] at hu
  unfold branchedIntegral
  rw [← hμ₁, ← hμY, ← hu, key]

include hd hfull hiso in
/-- **Theorem 11.4.2, 2021 p. 544, for the effective weighted counts (`n = 0`), along a full and
faithful local sc-diffeomorphism** `Φ : X → Y` whose image contains the support:
`∮_{Φ^*Θ̂'} Φ^*ω' = ∮_{Θ̂'} ω'`. -/
theorem pointIntegralEff_pull_of (hΘ' : B.X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : B.X.IsCompactBranched Θ')
    (hT' : B.X.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : B.X.OrientedTameStructure 0 Θ' y,
      (∀ i, D.M i ∈ pointSheets B.X) ∧ D.Represents T' ∧ D.rep.HasLUC)
    (hLY : B.X.IsLUC)
    (hrange : B.X.orbitSupp Θ' ⊆ range Φ.orbitMap)
    (hΘ : A.X.IsBranchedEpSubgroupoid (Φ.pullbackTheta Θ'))
    (hcpt : A.X.IsCompactBranched (Φ.pullbackTheta Θ'))
    (hT : A.X.IsOrientation (Φ.pullbackTheta Θ') T) (hTT : Φ.IsTransported T T')
    (hcov : ∀ x ∈ supp (Φ.pullbackTheta Θ'),
      ∃ C : A.X.OrientedTameStructure 0 (Φ.pullbackTheta Θ') x,
        (∀ i, C.M i ∈ pointSheets A.X) ∧ C.Represents T ∧ C.rep.HasLUC)
    (ω' : B.epFormsInfty 0) :
    branchedIntegralEff A.zeroFormIntegration hΘ hcpt hT hcov (EP.epFormsInftyPullback Φ 0 ω') =
      branchedIntegralEff B.zeroFormIntegration hΘ' hcpt' hT' hcov' ω' := by
  have hΘf := hΘ'.isFunctorial
  have hLX : A.X.IsLUC := isLUC_of_isLocalScDiffeo hd hLY
  have : CompactSpace (B.X.orbitSupp Θ') := isCompact_iff_compactSpace.1 hcpt'
  have hmc : @Measurable _ _
      (A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) (Φ.pullbackTheta Θ'))
      (borel (B.X.orbitSupp Θ')) (suppMap (Φ := Φ) hΘf) := fun s hs =>
    borel_le_borelNullSigma _ _ ((continuous_suppMap (Φ := Φ) hΘf).borel_measurable hs)
  set μ₁ := branchedMeasureEff A.zeroFormIntegration hΘ hcpt hT hcov
    (EP.epFormsInftyPullback Φ 0 ω') with hμ₁
  set μY := branchedMeasureEff B.zeroFormIntegration hΘ' hcpt' hT' hcov' ω' with hμY
  set ν : @SignedMeasure (B.X.orbitSupp Θ') (borel _) :=
    @VectorMeasure.map _ _
      (A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) (Φ.pullbackTheta Θ'))
      (borel (B.X.orbitSupp Θ')) ℝ _ _ μ₁ (suppMap (Φ := Φ) hΘf) with hν
  have hνK : ∀ K : Set (B.X.orbitSupp Θ'), MeasurableSet[borel (B.X.orbitSupp Θ')] K →
      ν K = μ₁ (suppMap (Φ := Φ) hΘf ⁻¹' K) := fun K hK =>
    @VectorMeasure.map_apply _ _
      (A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) (Φ.pullbackTheta Θ'))
      (borel (B.X.orbitSupp Θ')) ℝ _ _ μ₁ _ hmc K hK
  have key := signedMeasure_univ_eq_of_local (borel_le_borelNullSigma _) le_rfl μY ν fun q => by
    obtain ⟨p, hp⟩ := hrange q.2
    have hps : p ∈ A.X.orbitSupp (Φ.pullbackTheta Θ') := by
      rw [Φ.orbitSupp_pullbackTheta hΘf, mem_preimage, hp]; exact q.2
    obtain ⟨x, hx, rfl⟩ := hps
    obtain ⟨C, hCS, hCT, -⟩ := hcov x hx
    obtain ⟨C₁, D, hC₁S, hC₁T, hDS, hDT, -, hcard, hsum⟩ :=
      exists_local_comparison_point hd hfull hiso hΘf hTT C hCS hCT
    have hL₁ : C₁.rep.HasLUC := A.X.isLUC_iff_forall_naturalRep.1 hLX _ _
    have hLD : D.rep.HasLUC := B.X.isLUC_iff_forall_naturalRep.1 hLY _ _
    refine ⟨Subtype.val ⁻¹' (B.X.π '' D.U),
      (B.X.proposition_7_1_8 _ D.isOpen_U).preimage continuous_subtype_val,
      ⟨Φ.obj x, D.mem_U, by rw [← hp, Φ.orbitMap_π]⟩, fun K hK hKN => ?_⟩
    have hKU : Subtype.val '' K ⊆ B.X.π '' D.U := by
      rintro _ ⟨k, hk, rfl⟩
      exact hKN hk
    obtain ⟨hK₁, hKU₁, e⟩ := hsum ω' K hK hKU
    rw [hνK K hK, hμ₁, hμY,
      branchedMeasureEff_apply _ hΘ hcpt hT hcov (EP.epFormsInftyPullback Φ 0 ω') C₁ hC₁S hC₁T
        hL₁ hK₁ hKU₁,
      branchedMeasureEff_apply _ hΘ' hcpt' hT' hcov' ω' D hDS hDT hLD
        (borel_le_borelNullSigma _ _ hK) hKU, localMeasureEff, localMeasureEff,
      hcard hL₁ hLD, e]
  have hu := hνK univ (@MeasurableSet.univ _ (borel _))
  rw [preimage_univ] at hu
  unfold branchedIntegralEff
  rw [← hμ₁, ← hμY, ← hu, key]

end Integrals

end EpFunctor

end Polyfold
