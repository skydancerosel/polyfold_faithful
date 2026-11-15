import Polyfold.Chapter16.IndexZeroInvariant
import Polyfold.Chapter11.BoundaryMeasureEquivalenceDimOne
import Polyfold.Chapter11.EffectiveMeasureEquivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 11,
§11.4, **Theorem 11.4.1** (p. 543; 2017: Theorem 11.8) **for dimension `n = 0`**, as needed for
Theorem 16.6.6 (p. 739) with Fredholm index `0`.  Numbers and pages are the 2021 text's.

# The weighted count along an equivalence

## The text, paraphrased

(Theorem 11.4.1) For a generalized isomorphism `f : X → Y`, oriented tame compact branched
ep⁺-subgroupoids of dimension `n` and sc-differential `n`-forms,
`µ^{f^*Θ̂'}_{f^*ω'}(K) = µ^Θ̂'_{ω'}(|f|(K))`.  The proof takes an equivalence `F`, moves the local
branching structures by the local sc-diffeomorphisms and compares the local formulas.  For
`n = 0` the sheets are oriented points and the measures are the weighted signed counts of
Definition 9.5.6.

## What is formalized

For an equivalence `Φ : X → Y` between the ep-groupoids of two EPs and the integration of
`0`-forms over oriented points (`EP.zeroFormIntegration`):

* `EpGroupoid.eq_empty_of_mem_measureZeroSets_point`: for the `0`-dimensional null sets, the
  only set of measure zero in `|supp Θ|` is the empty set (so `L(|supp Θ|)` is the Borel
  σ-algebra).
* `EpGroupoid.OrientedTameStructure.sheetSum_move_point`: (11.12) = (11.13) for oriented points.
* `EpFunctor.pullStructure_mem_pointSheets`: a structure with point sheets moved back along a
  transport chart has point sheets.
* **`EpFunctor.point_measure_pull_core`**: for `Θ = Φ^*Θ'`, `T̂'` the orientation `T̂` moved by
  the transport charts, both tame of dimension `0`: `|Φ|(K) ∈ L(|supp Θ'|)` and
  `µ^Θ̂_{Φ^*ω'}(K) = µ^Θ̂'_{ω'}(|Φ|(K))`.
* `EpFunctor.point_measure_pull_core_eff`: the same for the effective measures of Theorem 9.5.5
  (Theorem 11.4.2 for `n = 0`); both follow from the gluing lemma `point_measure_pull_aux`.
* `EpFunctor.isPointTame_pull`: `Φ^*Θ̂'` is tame of dimension `0` if `Θ̂'` is.
* **`EpFunctor.theorem_11_4_1_pull_equiv_point`**, **`EpFunctor.pointBranchedIntegral_pull_equiv`**:
  Theorem 11.4.1 (second identity) for `n = 0` and an equivalence, and the equality of the
  weighted counts `∫_{Φ^*Θ̂'} Φ^*ω' = ∫_{Θ̂'} ω'`.
* `EpFunctor.pointBranchedIntegral_eq_of_isTransported`: the count form of the core statement;
  `EpFunctor.isPointTame_push_of_isTransported`: `Φ_*Θ̂` is tame of dimension `0` if `Θ̂` is
  (together they contain the first identity of Theorem 11.4.1 for the counts).
* `EPLoc.isPointTame_pull`, **`EPLoc.pointBranchedIntegral_pull`**: for a generalized
  isomorphism `f`, `f^*Θ̂'` is tame of dimension `0` and `∫_{f^*Θ̂'} f^*ω' = ∫_{Θ̂'} ω'`.
* `PolyfoldClass.OrientedRep.pointIntegral`, **`pointIntegral_eq_of_rel`**,
  `isPointTame_of_rel`: the weighted count of a `0`-form over a representative of an oriented
  branched suborbifold of a polyfold does not depend on the representative (2021 p. 732 for
  dimension `0`).
* `PolyfoldClass.OrientedSuborbifold.IsPointTame`, `isPointTame_iff`, **`pointIntegral`**,
  **`pointIntegral_eq`**: the weighted count `∫_θ̂ τ` of a `0`-form over a compact oriented
  branched suborbifold of the polyfold, tame of dimension `0`, computed on any representative.
* The effective counts `∮`: `EpFunctor.pointBranchedIntegralEff_eq_of_isTransported`,
  `EPLoc.pointBranchedIntegralEff_pull`, `OrientedRep.pointIntegralEff`,
  **`pointIntegralEff_eq_of_rel`**, `OrientedSuborbifold.pointIntegralEff`,
  `pointIntegralEff_eq`.
* `StrongPolyfoldBundle.pointOrientedRep`, `count_eq_pointIntegral`,
  `countEff_eq_pointIntegralEff`, **`count_eq_of_mk_eq`**: the counts `∫`, `∮` of a regular
  perturbation of dimension `0` (`SBLocalization.PointPerturbation`) are the counts of its class
  on the polyfold, so they agree for perturbations in two models that define the same oriented
  branched suborbifold of `Z`.

## Reading

As in `EpGroupoid.IsPointTame`, tame of dimension `0` is read with sheets that are points.
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

/-! ### The `0`-dimensional null sets -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- **For the `0`-dimensional null sets the only set of measure zero in `|supp Θ|` is `∅`**
(Definition 9.5.1 with the counting measure on the sheets): every point of `supp Θ` lies on
every sheet of a local branching structure around it. -/
theorem eq_empty_of_mem_measureZeroSets_point {S : Set (Set Obj)} {Θ : Obj → ℚ}
    {t : Set (X.orbitSupp Θ)} (ht : t ∈ X.measureZeroSets (SheetNullSets.point S) Θ) :
    t = ∅ := by
  classical
  rw [eq_empty_iff_forall_notMem]
  intro q hq
  obtain ⟨x, hx, hxq⟩ := q.2
  obtain ⟨Bs, -, hnull⟩ := ht x hx
  set L := Bs.toLocalBranchingStructure
  have hpos : (0 : ℚ) < ∑ i with x ∈ L.M i, L.σ i := by
    rw [← L.eq_sum x L.mem_U]; exact hx
  obtain ⟨i, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  have hd : Disjoint (L.M i ∩ X.π ⁻¹' (Subtype.val '' t)) (L.M i) := hnull i
  exact disjoint_left.1 hd ⟨L.mem_M i, q, hq, hxq.symm⟩ (L.mem_M i)

/-- A subset of a point sheet cut out by a set is a point sheet. -/
theorem inter_mem_pointSheets {N : Set Obj} (hN : N ∈ pointSheets X) (V : Set Obj) :
    N ∩ V ∈ pointSheets X := by
  rcases hN with h0 | ⟨p, hp, rfl⟩
  · left; rw [h0, empty_inter]
  · by_cases hpV : p ∈ V
    · right; exact ⟨p, hp, inter_eq_left.2 (singleton_subset_iff.2 hpV)⟩
    · left; exact singleton_inter_eq_empty.2 hpV

namespace OrientedTameStructure

variable {S T : EP.{u}} {Θ : S.Obj → ℚ} {Θ' : T.Obj → ℚ} {x : S.Obj}
  (C : S.X.OrientedTameStructure 0 Θ x)
  {f : S.Obj → T.Obj} {g : T.Obj → S.Obj} {W : Set S.Obj} {W' : Set T.Obj}

open scoped Classical in
/-- **(11.12) = (11.13) for oriented points** (`n = 0`): for a structure `C` whose sheets have
at most one point and its moved structure,
`∑ σᵢ ∫_{B ∩ f(Mᵢ)} ω_T|(f(Mᵢ), f_* oᵢ) = ∑ σᵢ ∫_{A ∩ Mᵢ} ω_S|(Mᵢ, oᵢ)` whenever `B` meets
`f(Mᵢ)` in `f(A ∩ Mᵢ)` and `ω_T ∘ f = ω_S` on `W`. -/
theorem sheetSum_move_point (hf : S.X.PObj.IsScDiffeoOn T.X.PObj f g W W') (hUW : C.U ⊆ W)
    {y : T.Obj} (hxy : f x = y) (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u) (R' : T.X.NaturalRep y)
    (hR' : R'.U = f '' C.U) (hP : T.X.HasPropernessProperty (f '' C.U))
    (hs : ∀ i, (C.M i).Subsingleton) {ωS : S.epFormsInfty 0} {ωT : T.epFormsInfty 0}
    (hω : ∀ u ∈ W, T.zeroFormEval ωT (f u) = S.zeroFormEval ωS u) {A : Set S.Obj}
    {B : Set T.Obj} (hB : ∀ i, B ∩ f '' C.M i = f '' (A ∩ C.M i)) :
    (C.move hf hUW hxy hΘ R' hR' hP).sheetSum T.zeroFormIntegration ωT B =
      C.sheetSum S.zeroFormIntegration ωS A := by
  set C' := C.move hf hUW hxy hΘ R' hR' hP with hC'
  unfold sheetSum
  refine Finset.sum_congr rfl ?_
  intro i _
  have hM : C'.M i = f '' C.M i := C.move_M_eq hf hUW hxy hΘ R' hR' hP i
  have hMW : C.M i ⊆ W := (C.subset_U i).trans hUW
  have hs' : (C'.M i).Subsingleton := by rw [hM]; exact (hs i).image f
  suffices e : T.zeroFormIntegration.integ ωT (C'.M i) (C'.orient i).tangent (B ∩ C'.M i) =
      S.zeroFormIntegration.integ ωS (C.M i) (C.orient i).tangent (A ∩ C.M i) from
    congrArg ((C.σ i : ℝ) * ·) e
  rw [EP.zeroFormIntegration_integ, EP.zeroFormIntegration_integ]
  by_cases hne : (A ∩ C.M i).Nonempty
  · obtain ⟨p, hpA, hp⟩ := hne
    have hfp : f p ∈ C'.M i := by rw [hM]; exact mem_image_of_mem f hp
    have hfB : f p ∈ B := by
      have : f p ∈ B ∩ f '' C.M i := by rw [hB i]; exact mem_image_of_mem f ⟨hpA, hp⟩
      exact this.1
    rw [pointInteg_of_mem (hs i) (show p ∈ (A ∩ C.M i) ∩ C.M i from ⟨⟨hpA, hp⟩, hp⟩),
      pointInteg_of_mem hs' (show f p ∈ (B ∩ C'.M i) ∩ C'.M i from ⟨⟨hfB, hfp⟩, hfp⟩),
      hω p (hMW hp)]
    congr 1
    have h := MPolyfold.SubmanifoldOrientation.mapDiffeo_tangent
      ((C.orient i).restrict hf.isScSmoothOn.isOpen)
      ((C.isSmoothSubmanifold i).inter_isOpen hf.isScSmoothOn.isOpen) hf inter_subset_right
      (y := p) ⟨hp, hMW hp⟩
    rw [(C.orient i).restrict_tangent hf.isScSmoothOn.isOpen (hMW hp)] at h
    have h' : (C'.orient i).tangent (f p) =
        ((C.orient i).tangent p).map (tangentMapOn hf.isScSmoothOn) := h
    rw [h']
    unfold frameSign
    have hiff : (((C.orient i).tangent p).map (tangentMapOn hf.isScSmoothOn)).frames.Nonempty ↔
        ((C.orient i).tangent p).frames.Nonempty := by
      change ((fun v => tangentMapOn hf.isScSmoothOn ∘ v) ''
        ((C.orient i).tangent p).frames).Nonempty ↔ _
      exact image_nonempty
    by_cases h : ((C.orient i).tangent p).frames.Nonempty
    · rw [if_pos h, if_pos (hiff.2 h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]
  · have h0 : (A ∩ C.M i) ∩ C.M i = ∅ :=
      eq_empty_of_forall_notMem fun q hq => hne ⟨q, hq.1⟩
    have h0' : (B ∩ C'.M i) ∩ C'.M i = ∅ := eq_empty_of_forall_notMem fun z hz => by
      have hz' : z ∈ B ∩ f '' C.M i := ⟨hz.1.1, hM ▸ hz.2⟩
      rw [hB i] at hz'
      obtain ⟨q, hq, -⟩ := hz'
      exact hne ⟨q, hq⟩
    rw [pointInteg_of_empty h0, pointInteg_of_empty h0']

end OrientedTameStructure

end EpGroupoid

namespace EpFunctor

open OrientedTameStructure

section PointSheets

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Φ : EpFunctor X Y} {n : ℕ}
  {Θ : Obj → ℚ} {Θ' : Obj' → ℚ} {x : Obj} {y : Obj'}

/-- **A structure with point sheets moved back along a transport chart has point sheets.** -/
theorem pullStructure_mem_pointSheets (hΦ : Φ.IsEquivalence) (Tc : Φ.TransportChart x y)
    (hΘ : ∀ u ∈ Tc.W, Θ' (Tc.Q u) = Θ u) (D : Y.OrientedTameStructure n Θ' y)
    (R : X.NaturalRep x) (R' : Y.NaturalRep y) (hR'D : R'.U ⊆ D.U) (hRW : R.U ⊆ Tc.W)
    (hR' : R'.U = Tc.Q '' R.U) (hRP : X.HasPropernessProperty R.U)
    (hDS : ∀ i, D.M i ∈ pointSheets Y) (i : D.ι) :
    (pullStructure Tc hΘ D R R' hR'D hRW hR' hRP).M i ∈ pointSheets X := by
  have hM : (pullStructure Tc hΘ D R R' hR'D hRW hR' hRP).M i =
      Tc.Qinv '' ((D.M i ∩ R'.U) ∩ Tc.W') := rfl
  rw [hM]
  rcases inter_mem_pointSheets (inter_mem_pointSheets (hDS i) R'.U) Tc.W' with h0 | ⟨p, hp, hpe⟩
  · left; rw [h0, image_empty]
  · right
    have hpW' : p ∈ Tc.W' := (hpe ▸ mem_singleton p : p ∈ (D.M i ∩ R'.U) ∩ Tc.W').2
    refine ⟨Tc.Qinv p, ?_, by rw [hpe, image_singleton]⟩
    refine (Tc.mem_smoothSet_iff hΦ.isLocalScDiffeo_obj (Tc.isScDiffeoOn_Q.mapsTo_inv hpW')).1 ?_
    rw [Tc.isScDiffeoOn_Q.right_inv p hpW']; exact hp

end PointSheets

variable {A B : EP.{u}} {Φ : EpFunctor A.X B.X}
  {Θ' : B.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} {T' : B.Obj → B.X.PObj.OrTangent →₀ ℚ}

/-- **The pulled-back structures with point sheets**: a structure at `y` with point sheets
restricted to `Q(U(x))` and moved to `x`. -/
def IsPointPulled (Φ : EpFunctor A.X B.X) (hΘ' : B.X.IsFunctorial Θ')
    (T' : B.Obj → B.X.PObj.OrTangent →₀ ℚ) {x : A.Obj}
    (C : A.X.OrientedTameStructure 0 (Φ.pullbackTheta Θ') x) : Prop :=
  ∃ (y : B.Obj) (Tc : Φ.TransportChart x y) (D : B.X.OrientedTameStructure 0 Θ' y)
    (_ : ∀ i, D.M i ∈ pointSheets B.X) (_ : D.Represents T') (R : A.X.NaturalRep x)
    (R' : B.X.NaturalRep y) (h1 : R'.U ⊆ D.U) (h2 : R.U ⊆ Tc.W) (h3 : R'.U = Tc.Q '' R.U)
    (h4 : A.X.HasPropernessProperty R.U),
    C = pullStructure Tc (Tc.pullbackTheta_Q hΘ') D R R' h1 h2 h3 h4

/-- Every point of `supp Φ^*Θ'` carries a pulled-back structure with point sheets. -/
theorem exists_isPointPulled (hΦ : Φ.IsEquivalence) (hΘ' : B.X.IsFunctorial Θ')
    (hloc' : B.X.IsPointTame Θ' T') {x : A.Obj} (hx : x ∈ supp (Φ.pullbackTheta Θ')) :
    ∃ C : A.X.OrientedTameStructure 0 (Φ.pullbackTheta Θ') x, IsPointPulled Φ hΘ' T' C := by
  obtain ⟨Tc⟩ := TransportChart.nonempty hΦ x
  obtain ⟨D, hDS, hDT⟩ := hloc' _ hx
  obtain ⟨R, R', h1, h2, h3, h4⟩ := exists_pullData hΦ Tc D
  exact ⟨_, _, Tc, D, hDS, hDT, R, R', h1, h2, h3, h4, rfl⟩

theorem IsPointPulled.mem_pointSheets (hΦ : Φ.IsEquivalence) {hΘ' : B.X.IsFunctorial Θ'}
    {x : A.Obj} {C : A.X.OrientedTameStructure 0 (Φ.pullbackTheta Θ') x}
    (hC : IsPointPulled Φ hΘ' T' C) : ∀ i, C.M i ∈ pointSheets A.X := by
  obtain ⟨y, Tc, D, hDS, hDT, R, R', h1, h2, h3, h4, rfl⟩ := hC
  exact pullStructure_mem_pointSheets hΦ Tc _ D R R' h1 h2 h3 h4 hDS

theorem IsPointPulled.represents (hΦ : Φ.IsEquivalence) {hΘ' : B.X.IsFunctorial Θ'}
    {x : A.Obj} (hT : A.X.IsGrHatSection T) (hTT : Φ.IsTransported T T')
    {C : A.X.OrientedTameStructure 0 (Φ.pullbackTheta Θ') x}
    (hC : IsPointPulled Φ hΘ' T' C) : C.Represents T := by
  obtain ⟨y, Tc, D, hDS, hDT, R, R', h1, h2, h3, h4, rfl⟩ := hC
  exact represents_pullStructure Tc _ D R R' h1 h2 h3 h4 hΦ hT (hTT Tc) hDT

/-- **`Φ^*Θ̂'` is tame of dimension `0`** if `Θ̂'` is and `T̂'` is `T̂` moved by the transport
charts. -/
theorem isPointTame_of_isTransported (hΦ : Φ.IsEquivalence) (hΘ' : B.X.IsFunctorial Θ')
    (hT : A.X.IsGrHatSection T) (hTT : Φ.IsTransported T T') (hloc' : B.X.IsPointTame Θ' T') :
    A.X.IsPointTame (Φ.pullbackTheta Θ') T := fun x hx => by
  obtain ⟨C, hC⟩ := exists_isPointPulled hΦ hΘ' hloc' hx
  exact ⟨C, hC.mem_pointSheets hΦ, hC.represents hΦ hT hTT⟩

/-- **`|Φ|⁻¹` is measurable for the σ-algebras `L`** of dimension `0` (Definition 9.5.3). -/
theorem measurable_suppInv_point (hΦ : Φ.IsEquivalence) (hΘ' : B.X.IsFunctorial Θ') :
    @Measurable _ _ (B.X.lebesgueSigma (SheetNullSets.point (pointSheets B.X)) Θ')
      (A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) (Φ.pullbackTheta Θ'))
      (suppInv hΦ hΘ') := by
  let _ : MeasurableSpace (B.X.orbitSupp Θ') :=
    B.X.lebesgueSigma (SheetNullSets.point (pointSheets B.X)) Θ'
  refine measurable_generateFrom fun t ht => ?_
  rcases ht with ht | ht
  · exact borel_le_borelNullSigma _ _ ((continuous_suppInv hΦ hΘ').borel_measurable ht)
  · rw [eq_empty_of_mem_measureZeroSets_point ht, preimage_empty]
    exact MeasurableSet.empty

/-- **The gluing argument of Theorem 11.4.1 for `n = 0`**: for an equivalence `Φ`, `Θ = Φ^*Θ'`,
`T̂'` the orientation `T̂` moved by the transport charts and `Θ̂'` tame of dimension `0`, two
signed measures `µ₁` on `L(|supp Θ|)` and `µ'` on `L(|supp Θ'|)` given by the local formulas
`c(x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` over oriented points (for `Φ^*ω'` and `ω'`), with normalizations
`c`, `c'` that agree along transport charts, satisfy `µ₁(K) = µ'(|Φ|(K))`, and
`|Φ|(K) ∈ L(|supp Θ'|)`. -/
theorem point_measure_pull_aux (hΦ : Φ.IsEquivalence)
    (hΘ' : B.X.IsBranchedEpSubgroupoid Θ') (hloc' : B.X.IsPointTame Θ' T')
    {Θ : A.Obj → ℚ} (hΘeq : Φ.pullbackTheta Θ' = Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsGrHatSection T) (hTT : Φ.IsTransported T T')
    (c : A.Obj → ℝ) (c' : B.Obj → ℝ)
    (hc : ∀ {x : A.Obj} {y : B.Obj} (Tc : Φ.TransportChart x y) (R : A.X.NaturalRep x)
      (R' : B.X.NaturalRep y), R.U ⊆ Tc.W → R'.U = Tc.Q '' R.U → c x = c' y)
    (ω' : B.epFormsInfty 0)
    (μ₁ : @SignedMeasure (A.X.orbitSupp Θ)
      (A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) Θ))
    (μY : @SignedMeasure (B.X.orbitSupp Θ')
      (B.X.lebesgueSigma (SheetNullSets.point (pointSheets B.X)) Θ'))
    (hμ₁ : ∀ (x : A.Obj) (C : A.X.OrientedTameStructure 0 Θ x),
      (∀ i, C.M i ∈ pointSheets A.X) → C.Represents T → ∀ K,
      MeasurableSet[A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) Θ] K →
      Subtype.val '' K ⊆ A.X.π '' C.U →
      μ₁ K = c x * C.sheetSum A.zeroFormIntegration (EP.epFormsInftyPullback Φ 0 ω')
        (A.X.π ⁻¹' (Subtype.val '' K)))
    (hμY : ∀ (y : B.Obj) (D : B.X.OrientedTameStructure 0 Θ' y),
      (∀ i, D.M i ∈ pointSheets B.X) → D.Represents T' → ∀ K,
      MeasurableSet[B.X.lebesgueSigma (SheetNullSets.point (pointSheets B.X)) Θ'] K →
      Subtype.val '' K ⊆ B.X.π '' D.U →
      μY K = c' y * D.sheetSum B.zeroFormIntegration ω' (B.X.π ⁻¹' (Subtype.val '' K)))
    {K : Set (A.X.orbitSupp Θ)}
    (hK : MeasurableSet[A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) Θ] K) :
    MeasurableSet[B.X.lebesgueSigma (SheetNullSets.point (pointSheets B.X)) Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      μ₁ K = μY (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := by
  subst hΘeq
  have hΘf := hΘ'.isFunctorial
  have hm := measurable_suppInv_point (A := A) hΦ hΘf
  have hmeas : ∀ K : Set (A.X.orbitSupp (Φ.pullbackTheta Θ')),
      MeasurableSet[A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X))
        (Φ.pullbackTheta Θ')] K →
      MeasurableSet[B.X.lebesgueSigma (SheetNullSets.point (pointSheets B.X)) Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := fun K hK => by
    rw [← preimage_suppInv hΦ hΘf K]; exact hm hK
  refine ⟨hmeas K hK, ?_⟩
  let _ : MeasurableSpace (A.X.orbitSupp (Φ.pullbackTheta Θ')) :=
    A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) (Φ.pullbackTheta Θ')
  let _ : MeasurableSpace (B.X.orbitSupp Θ') :=
    B.X.lebesgueSigma (SheetNullSets.point (pointSheets B.X)) Θ'
  have : CompactSpace (A.X.orbitSupp (Φ.pullbackTheta Θ')) := isCompact_iff_compactSpace.1 hcpt
  set μ₂ : SignedMeasure (A.X.orbitSupp (Φ.pullbackTheta Θ')) := μY.map (suppInv hΦ hΘf)
  have hμ₂ : ∀ K, MeasurableSet K →
      μ₂ K = μY (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := fun K hK => by
    rw [VectorMeasure.map_apply _ hm hK, preimage_suppInv]
  -- the local agreement on a pulled-back structure: (11.12) = (11.13)
  have hlocal : ∀ {x : A.Obj} (C : A.X.OrientedTameStructure 0 (Φ.pullbackTheta Θ') x),
      IsPointPulled Φ hΘf T' C → ∀ K, MeasurableSet K → Subtype.val '' K ⊆ A.X.π '' C.U →
      μ₂ K = μ₁ K := by
    intro x C hC K hK hKU
    have hS := hC.mem_pointSheets hΦ
    have hR := hC.represents hΦ hT hTT
    obtain ⟨y, Tc, D, hDS, hDT, R, R', h1, h2, h3, h4, rfl⟩ := hC
    set D₁ := D.restrictRep R' h1
    have hval := val_image_preimage (Θ' := Θ') (Φ := Φ)
      (fun p hp => orbitMap_mem_orbitSupp hΘf hp) K
    have hD₁S : ∀ i, D₁.M i ∈ pointSheets B.X := fun i =>
      inter_mem_pointSheets (hDS i) R'.U
    have hD₁T := D.represents_restrictRep R' h1 hDT
    have hK' := hmeas K hK
    have hKU' : Subtype.val '' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K)) :
        Set (B.X.orbitSupp Θ')) ⊆ B.X.π '' D₁.U := by
      rw [hval, restrictRep_U, h3]
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨u, hu, hπ⟩ := hKU hp
      rw [pullStructure_U] at hu
      exact ⟨Tc.Q u, mem_image_of_mem _ hu, by rw [Tc.π_Q (h2 hu), ← Φ.orbitMap_π, hπ]⟩
    have hW' : ∀ {z}, z ∈ D₁.U → z ∈ Tc.W' := fun hz =>
      restrictRep_U_subset_W' Tc D R R' h1 h2 h3 hz
    have hB : ∀ i, A.X.π ⁻¹' (Subtype.val '' K) ∩ Tc.Qinv '' D₁.M i =
        Tc.Qinv '' (B.X.π ⁻¹' (Subtype.val '' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K)) :
          Set (B.X.orbitSupp Θ'))) ∩ D₁.M i) := by
      intro i
      ext u
      constructor
      · rintro ⟨hu, z, hz, rfl⟩
        have hzW' := hW' (D₁.subset_U i hz)
        refine ⟨z, ⟨?_, hz⟩, rfl⟩
        rw [mem_preimage, hval]
        refine ⟨_, hu, ?_⟩
        rw [Φ.orbitMap_π, ← Tc.π_Q (Tc.isScDiffeoOn_Q.mapsTo_inv hzW'),
          Tc.isScDiffeoOn_Q.right_inv z hzW']
      · rintro ⟨z, ⟨hzA, hz⟩, rfl⟩
        have hzW' := hW' (D₁.subset_U i hz)
        refine ⟨?_, z, hz, rfl⟩
        rw [mem_preimage, hval] at hzA
        obtain ⟨p, hp, he⟩ := hzA
        rw [← Tc.isScDiffeoOn_Q.right_inv z hzW', Tc.π_Q (Tc.isScDiffeoOn_Q.mapsTo_inv hzW'),
          ← Φ.orbitMap_π] at he
        rw [mem_preimage, ← Φ.injective_orbitMap_of_full hΦ.full he]
        exact hp
    have hω : ∀ z ∈ Tc.W', A.zeroFormEval (EP.epFormsInftyPullback Φ 0 ω') (Tc.Qinv z) =
        B.zeroFormEval ω' z := fun z hz => by
      rw [Tc.zeroFormEval_pull_Q hΦ ω' (Tc.isScDiffeoOn_Q.mapsTo_inv hz),
        Tc.isScDiffeoOn_Q.right_inv z hz]
    have e : (pullStructure Tc (Tc.pullbackTheta_Q hΘf) D R R' h1 h2 h3 h4).sheetSum
        A.zeroFormIntegration (EP.epFormsInftyPullback Φ 0 ω')
          (A.X.π ⁻¹' (Subtype.val '' K)) =
        D₁.sheetSum B.zeroFormIntegration ω' (B.X.π ⁻¹' (Subtype.val ''
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K)) : Set (B.X.orbitSupp Θ')))) :=
      D₁.sheetSum_move_point Tc.isScDiffeoOn_Q.symm _ _ _ R _ _
        (fun i => subsingleton_of_mem_pointSheets (hD₁S i)) hω hB
    rw [hμ₂ K hK, hμY y D₁ hD₁S hD₁T _ hK' hKU', hμ₁ x _ hS hR K hK hKU, hc Tc R R' h2 h3]
    exact congrArg _ e.symm
  -- gluing (Theorem 9.5.4's uniqueness) over the pulled-back structures
  let J := {j : Σ x, A.X.OrientedTameStructure 0 (Φ.pullbackTheta Θ') x //
    IsPointPulled Φ hΘf T' j.2}
  let O : J → Set (A.X.orbitSupp (Φ.pullbackTheta Θ')) :=
    fun j => Subtype.val ⁻¹' (A.X.π '' j.1.2.U)
  have hO : ∀ j, IsOpen (O j) := fun j =>
    (A.X.proposition_7_1_8 _ j.1.2.isOpen_U).preimage continuous_subtype_val
  have hcovO : ⋃ j, O j = univ := eq_univ_of_forall fun q => by
    obtain ⟨x, hx, hxq⟩ := q.2
    obtain ⟨C, hC⟩ := exists_isPointPulled hΦ hΘf hloc' hx
    exact mem_iUnion.2 ⟨⟨⟨x, C⟩, hC⟩, x, C.mem_U, hxq⟩
  obtain ⟨Ψ, -, huniq⟩ := existsUnique_linearMap_signedMeasure_of_openCover (V := ℝ)
    (borel_le_borelNullSigma _) O hO hcovO (fun _ => LinearMap.toSpanSingleton ℝ _ μ₁)
    (fun _ _ _ _ _ _ => rfl)
  have e1 := huniq (LinearMap.toSpanSingleton ℝ _ μ₁) fun _ _ _ _ _ => rfl
  have e2 := huniq (LinearMap.toSpanSingleton ℝ _ μ₂) fun j t K hK hKO => by
    change (t • μ₂) K = (t • μ₁) K
    change t • μ₂ K = t • μ₁ K
    rw [hlocal j.1.2 j.2 K hK (by rintro _ ⟨q, hq, rfl⟩; exact hKO hq)]
  have e3 := congrArg (fun L : ℝ →ₗ[ℝ] SignedMeasure (A.X.orbitSupp (Φ.pullbackTheta Θ')) =>
    L 1) (e2.trans e1.symm)
  simp only [LinearMap.toSpanSingleton_apply, one_smul] at e3
  rw [← hμ₂ K hK, e3]

/-- **The core of Theorem 11.4.1 for `n = 0`**: for an equivalence `Φ`, `Θ = Φ^*Θ'`, `T̂'` the
orientation `T̂` moved by the transport charts, both tame of dimension `0`, `|Φ|` maps
`L(|supp Θ|)` into `L(|supp Θ'|)` and `µ^Θ̂_{Φ^*ω'}(K) = µ^Θ̂'_{ω'}(|Φ|(K))` for the weighted
counting measures of Theorem 9.5.4. -/
theorem point_measure_pull_core (hΦ : Φ.IsEquivalence)
    (hΘ' : B.X.IsBranchedEpSubgroupoid Θ') (hcpt' : B.X.IsCompactBranched Θ')
    (hT' : B.X.IsOrientation Θ' T') (hloc' : B.X.IsPointTame Θ' T')
    {Θ : A.Obj → ℚ} (hΘeq : Φ.pullbackTheta Θ' = Θ) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T) (hTT : Φ.IsTransported T T')
    (hloc : A.X.IsPointTame Θ T) (ω' : B.epFormsInfty 0) {K : Set (A.X.orbitSupp Θ)}
    (hK : MeasurableSet[A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) Θ] K) :
    MeasurableSet[B.X.lebesgueSigma (SheetNullSets.point (pointSheets B.X)) Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      branchedMeasure A.zeroFormIntegration hΘ hcpt hT hloc (EP.epFormsInftyPullback Φ 0 ω') K =
        branchedMeasure B.zeroFormIntegration hΘ' hcpt' hT' hloc' ω'
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) :=
  point_measure_pull_aux hΦ hΘ' hloc' hΘeq hcpt hT.isGrHatSection hTT
    (fun x => (Nat.card (A.X.Isotropy x) : ℝ)⁻¹) (fun y => (Nat.card (B.X.Isotropy y) : ℝ)⁻¹)
    (fun {x y} Tc _ _ _ _ => by
      have h : Nat.card (A.X.Isotropy x) = Nat.card (B.X.Isotropy y) :=
        Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj hΦ))
      change ((Nat.card (A.X.Isotropy x) : ℝ))⁻¹ = ((Nat.card (B.X.Isotropy y) : ℝ))⁻¹
      rw [h])
    ω' _ _
    (fun x C hS hR K hK hKU =>
      branchedMeasure_apply _ hΘ hcpt hT hloc (EP.epFormsInftyPullback Φ 0 ω') C hS hR hK hKU)
    (fun y D hS hR K hK hKU => branchedMeasure_apply _ hΘ' hcpt' hT' hloc' ω' D hS hR hK hKU)
    hK

/-- **The core of Theorem 11.4.2 for `n = 0`**: the same for the effective weighted counting
measures of Theorem 9.5.5 (weights `1/♯G_x^eff`), `Y` (hence `X`) with the local unique
continuation property. -/
theorem point_measure_pull_core_eff (hΦ : Φ.IsEquivalence) (hLY : B.X.IsLUC)
    (hΘ' : B.X.IsBranchedEpSubgroupoid Θ') (hcpt' : B.X.IsCompactBranched Θ')
    (hT' : B.X.IsOrientation Θ' T') (hloc' : B.X.IsPointTame Θ' T')
    {Θ : A.Obj → ℚ} (hΘeq : Φ.pullbackTheta Θ' = Θ) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T) (hTT : Φ.IsTransported T T')
    (hloc : A.X.IsPointTame Θ T) (ω' : B.epFormsInfty 0) {K : Set (A.X.orbitSupp Θ)}
    (hK : MeasurableSet[A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) Θ] K) :
    MeasurableSet[B.X.lebesgueSigma (SheetNullSets.point (pointSheets B.X)) Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      branchedMeasureEff A.zeroFormIntegration hΘ hcpt hT
          (hloc.hasLUC ((proposition_10_1_16 hΦ).2 hLY)) (EP.epFormsInftyPullback Φ 0 ω') K =
        branchedMeasureEff B.zeroFormIntegration hΘ' hcpt' hT' (hloc'.hasLUC hLY) ω'
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := by
  have hLX : A.X.IsLUC := (proposition_10_1_16 hΦ).2 hLY
  exact point_measure_pull_aux hΦ hΘ' hloc' hΘeq hcpt hT.isGrHatSection hTT
    (fun x => (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹)
    (fun y => (Nat.card (B.X.EffIsotropy y) : ℝ)⁻¹)
    (fun {x y} Tc R R' h2 h3 => by
      have h := Tc.card_effIsotropy_eq hΦ R R' h2 h3
        (A.X.isLUC_iff_forall_naturalRep.1 hLX x R) (B.X.isLUC_iff_forall_naturalRep.1 hLY y R')
      change ((Nat.card (A.X.EffIsotropy x) : ℝ))⁻¹ = ((Nat.card (B.X.EffIsotropy y) : ℝ))⁻¹
      rw [h])
    ω' _ _
    (fun x C hS hR K hK hKU =>
      branchedMeasureEff_apply _ hΘ hcpt hT (hloc.hasLUC hLX) (EP.epFormsInftyPullback Φ 0 ω')
        C hS hR (A.X.isLUC_iff_forall_naturalRep.1 hLX _ _) hK hKU)
    (fun y D hS hR K hK hKU =>
      branchedMeasureEff_apply _ hΘ' hcpt' hT' (hloc'.hasLUC hLY) ω' D hS hR
        (B.X.isLUC_iff_forall_naturalRep.1 hLY _ _) hK hKU)
    hK

/-- **The weighted counts agree along an equivalence** (the count form of
`point_measure_pull_core`, Definition 9.5.6 for `n = 0`): for `Θ = Φ^*Θ'` and `T̂'` the
orientation `T̂` moved by the transport charts, `∫_Θ̂ Φ^*ω' = ∫_Θ̂' ω'`. -/
theorem pointBranchedIntegral_eq_of_isTransported (hΦ : Φ.IsEquivalence)
    (hΘ' : B.X.IsBranchedEpSubgroupoid Θ') (hcpt' : B.X.IsCompactBranched Θ')
    (hT' : B.X.IsOrientation Θ' T') (hloc' : B.X.IsPointTame Θ' T')
    {Θ : A.Obj → ℚ} (hΘeq : Φ.pullbackTheta Θ' = Θ) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T) (hTT : Φ.IsTransported T T')
    (hloc : A.X.IsPointTame Θ T) (ω' : B.epFormsInfty 0) :
    A.pointBranchedIntegral hΘ hcpt hT hloc (EP.epFormsInftyPullback Φ 0 ω') =
      B.pointBranchedIntegral hΘ' hcpt' hT' hloc' ω' := by
  have h := (point_measure_pull_core hΦ hΘ' hcpt' hT' hloc' hΘeq hΘ hcpt hT hTT hloc ω'
    MeasurableSet.univ).2
  rw [image_univ_eq_univ hΦ hΘ'.isFunctorial hΘeq] at h
  exact h

/-- **The effective weighted counts agree along an equivalence** (Theorem 11.4.2 for `n = 0`
with `K = |supp Θ|`): `∮_Θ̂ Φ^*ω' = ∮_Θ̂' ω'`. -/
theorem pointBranchedIntegralEff_eq_of_isTransported (hΦ : Φ.IsEquivalence) (hLX : A.X.IsLUC)
    (hLY : B.X.IsLUC) (hΘ' : B.X.IsBranchedEpSubgroupoid Θ') (hcpt' : B.X.IsCompactBranched Θ')
    (hT' : B.X.IsOrientation Θ' T') (hloc' : B.X.IsPointTame Θ' T')
    {Θ : A.Obj → ℚ} (hΘeq : Φ.pullbackTheta Θ' = Θ) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T) (hTT : Φ.IsTransported T T')
    (hloc : A.X.IsPointTame Θ T) (ω' : B.epFormsInfty 0) :
    A.pointBranchedIntegralEff hLX hΘ hcpt hT hloc (EP.epFormsInftyPullback Φ 0 ω') =
      B.pointBranchedIntegralEff hLY hΘ' hcpt' hT' hloc' ω' := by
  have h := (point_measure_pull_core_eff hΦ hLY hΘ' hcpt' hT' hloc' hΘeq hΘ hcpt hT hTT hloc ω'
    MeasurableSet.univ).2
  rw [image_univ_eq_univ hΦ hΘ'.isFunctorial hΘeq] at h
  exact h

/-- **`Φ^*Θ̂' = (Φ^*Θ', Φ^*T̂')` is tame of dimension `0`** if `Θ̂'` is. -/
theorem isPointTame_pull (hΦ : Φ.IsEquivalence) (hΘ' : B.X.IsBranchedEpSubgroupoid Θ')
    (hT' : B.X.IsOrientation Θ' T') (hloc' : B.X.IsPointTame Θ' T') :
    A.X.IsPointTame (Φ.pullbackTheta Θ') (Φ.pullSection T') :=
  isPointTame_of_isTransported hΦ hΘ'.isFunctorial
    (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := B.X) _) hT').isGrHatSection
    (isTransported_pull hΦ hT'.isGrHatSection) hloc'

/-- **Theorem 11.4.1, 2021 p. 543, second identity, for an equivalence and `n = 0`**: for `Θ̂'`
on `Y` oriented, tame of dimension `0` and compact, a `0`-form `ω'` and
`K ∈ L(|supp Φ^*Θ'|)`: `|Φ|(K) ∈ L(|supp Θ'|)` and
`µ^{Φ^*Θ̂'}_{Φ^*ω'}(K) = µ^Θ̂'_{ω'}(|Φ|(K))`. -/
theorem theorem_11_4_1_pull_equiv_point (hΦ : Φ.IsEquivalence)
    (hΘ' : B.X.IsBranchedEpSubgroupoid Θ') (hcpt' : B.X.IsCompactBranched Θ')
    (hT' : B.X.IsOrientation Θ' T') (hloc' : B.X.IsPointTame Θ' T')
    (ω' : B.epFormsInfty 0) {K : Set (A.X.orbitSupp (Φ.pullbackTheta Θ'))}
    (hK : MeasurableSet[A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X))
      (Φ.pullbackTheta Θ')] K) :
    MeasurableSet[B.X.lebesgueSigma (SheetNullSets.point (pointSheets B.X)) Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      branchedMeasure A.zeroFormIntegration (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
        (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
        (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := B.X) _) hT')
        (isPointTame_pull hΦ hΘ' hT' hloc') (EP.epFormsInftyPullback Φ 0 ω') K =
        branchedMeasure B.zeroFormIntegration hΘ' hcpt' hT' hloc' ω'
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) :=
  point_measure_pull_core hΦ hΘ' hcpt' hT' hloc' rfl _ _ _
    (isTransported_pull hΦ hT'.isGrHatSection) _ ω' hK

/-- **Theorem 11.4.1 for the weighted counts** (`n = 0`, `K = |supp|`, Definition 9.5.6):
`∫_{Φ^*Θ̂'} Φ^*ω' = ∫_{Θ̂'} ω'` for an equivalence `Φ`. -/
theorem pointBranchedIntegral_pull_equiv (hΦ : Φ.IsEquivalence)
    (hΘ' : B.X.IsBranchedEpSubgroupoid Θ') (hcpt' : B.X.IsCompactBranched Θ')
    (hT' : B.X.IsOrientation Θ' T') (hloc' : B.X.IsPointTame Θ' T')
    (ω' : B.epFormsInfty 0) :
    A.pointBranchedIntegral (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
        (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
        (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := B.X) _) hT')
        (isPointTame_pull hΦ hΘ' hT' hloc') (EP.epFormsInftyPullback Φ 0 ω') =
      B.pointBranchedIntegral hΘ' hcpt' hT' hloc' ω' :=
  pointBranchedIntegral_eq_of_isTransported hΦ hΘ' hcpt' hT' hloc' rfl _ _ _
    (isTransported_pull hΦ hT'.isGrHatSection) _ ω'

/-- **`Φ_*Θ̂` is tame of dimension `0`** if `Θ̂` is and `T̂'` is `T̂` moved by the transport
charts (the structures at `x` moved forward along the transport charts). -/
theorem isPointTame_push_of_isTransported (hΦ : Φ.IsEquivalence) {Θ : A.Obj → ℚ}
    (hΘ : A.X.IsFunctorial Θ) (hTT : Φ.IsTransported T T') (hloc : A.X.IsPointTame Θ T) :
    B.X.IsPointTame (Φ.pushforwardTheta Θ) T' := fun y hy => by
  have hΘ' := isFunctorial_pushforwardTheta hΦ.full hΘ
  have he := pullbackTheta_pushforwardTheta hΦ.full hΘ
  obtain ⟨x, hx, ⟨Tc⟩⟩ := exists_transportChart_of_mem_supp hΦ hΘ' hy
  rw [he] at hx
  obtain ⟨C, hCS, hCT⟩ := hloc x hx
  have hΘQ : ∀ u ∈ Tc.W, Φ.pushforwardTheta Θ (Tc.Q u) = Θ u := fun u hu => by
    rw [Tc.pullbackTheta_Q hΘ' u hu, he]
  obtain ⟨V', hyV', hV'P⟩ := B.X.exists_hasPropernessProperty y
  obtain ⟨R, R', hRC, hRW, hRV', hR'⟩ := Tc.exists_rep_push hΦ C.rep hV'P.1 hyV'
  have hRU : R.U ⊆ C.U := C.U_eq ▸ hRC
  set C₁ := C.restrictRep R hRU
  have hP' : B.X.HasPropernessProperty (Tc.Q '' C₁.U) :=
    hV'P.mono (hR' ▸ R'.isOpen_U) hRV'
  refine ⟨C₁.move Tc.isScDiffeoOn_Q hRW Tc.Q_self hΘQ R' hR' hP', fun i => ?_, ?_⟩
  · have hM : (C₁.move Tc.isScDiffeoOn_Q hRW Tc.Q_self hΘQ R' hR' hP').M i =
        Tc.Q '' ((C.M i ∩ R.U) ∩ Tc.W) := rfl
    rw [hM]
    rcases inter_mem_pointSheets (inter_mem_pointSheets (hCS i) R.U) Tc.W with h0 | ⟨p, hp, hpe⟩
    · left; rw [h0, image_empty]
    · right
      have hpW : p ∈ Tc.W := (hpe ▸ mem_singleton p : p ∈ (C.M i ∩ R.U) ∩ Tc.W).2
      exact ⟨Tc.Q p, (Tc.mem_smoothSet_iff hΦ.isLocalScDiffeo_obj hpW).2 hp,
        by rw [hpe, image_singleton]⟩
  · refine C₁.represents_move _ _ _ _ _ _ _ (C.represents_restrictRep R hRU hCT) ?_
    rintro _ ⟨u, hu, rfl⟩ hzs
    have huW := hRW hu
    have hus := (Tc.mem_smoothSet_iff hΦ.isLocalScDiffeo_obj huW).1 hzs
    rw [Tc.isScDiffeoOn_Q.left_inv u huW]
    exact ⟨hus, hTT Tc u huW hus⟩

end EpFunctor

/-! ### Generalized isomorphisms and polyfolds -/

namespace EPLocalization.EPLoc

open CategoryTheory

variable {X Y : EP.{u}}

/-- **`f^*Θ̂'` is tame of dimension `0`** for a generalized isomorphism `f` and `Θ̂'` tame of
dimension `0`. -/
theorem isPointTame_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (B : OrientedBranched Y)
    (hlocB : Y.X.IsPointTame B.Θ B.T) :
    X.X.IsPointTame (OrientedBranched.pull hf B).Θ (OrientedBranched.pull hf B).T :=
  EpFunctor.isPointTame_push_of_isTransported (rep f).isEquivalence_F
    ((rep f).Φ.isFunctorial_pullbackTheta B.isBranchedEpSubgroupoid.isFunctorial)
    (EpFunctor.isTransported_push (rep f).isEquivalence_F
      (EpFunctor.isOrientation_pullSection (isEquivalence_rep_Φ hf) B.hasIndependentTangentSums
        B.isOrientation).isGrHatSection)
    (EpFunctor.isPointTame_pull (isEquivalence_rep_Φ hf) B.isBranchedEpSubgroupoid
      B.isOrientation hlocB)

/-- **The weighted count is invariant under pull-back along generalized isomorphisms** (Theorem
11.4.1 for `n = 0` with `K = |supp Θ|`): `∫_{f^*Θ̂'} f^*ω' = ∫_Θ̂' ω'`, for `A = f^*B`, both
compact and tame of dimension `0`. -/
theorem pointBranchedIntegral_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    (A : OrientedBranched X) (B : OrientedBranched Y) (hAB : OrientedBranched.pull hf B = A)
    (hcptA : X.X.IsCompactBranched A.Θ) (hlocA : X.X.IsPointTame A.Θ A.T)
    (hcptB : Y.X.IsCompactBranched B.Θ) (hlocB : Y.X.IsPointTame B.Θ B.T)
    (ω' : Y.epFormsInfty 0) :
    X.pointBranchedIntegral A.isBranchedEpSubgroupoid hcptA A.isOrientation hlocA
        (formsPullback f 0 ω') =
      Y.pointBranchedIntegral B.isBranchedEpSubgroupoid hcptB B.isOrientation hlocB ω' := by
  subst hAB
  have hF := (rep f).isEquivalence_F
  have hΦ := isEquivalence_rep_Φ hf
  have hΘB := B.isBranchedEpSubgroupoid
  have hΘM := EpFunctor.isBranchedEpSubgroupoid_pullbackTheta hΦ hΘB
  have hcM := EpFunctor.isCompactBranched_pullbackTheta hΦ hΘB.isFunctorial hcptB
  have hTM := EpFunctor.isOrientation_pullSection hΦ B.hasIndependentTangentSums B.isOrientation
  have hlM := EpFunctor.isPointTame_pull hΦ hΘB B.isOrientation hlocB
  have e1 := EpFunctor.pointBranchedIntegral_eq_of_isTransported hF
    (OrientedBranched.pull hf B).isBranchedEpSubgroupoid hcptA
    (OrientedBranched.pull hf B).isOrientation hlocA
    (EpFunctor.pullbackTheta_pushforwardTheta hF.full
      ((rep f).Φ.isFunctorial_pullbackTheta hΘB.isFunctorial)) hΘM hcM hTM
    (EpFunctor.isTransported_push hF hTM.isGrHatSection) hlM (formsPullback f 0 ω')
  have e2 := EpFunctor.pointBranchedIntegral_pull_equiv hΦ hΘB hcptB B.isOrientation hlocB ω'
  rw [pullback_formsPullback f ω'] at e1
  exact e1.symm.trans e2

/-- **The effective weighted count is invariant under pull-back along generalized
isomorphisms** (Theorem 11.4.2 for `n = 0` with `K = |supp Θ|`), for ep-groupoids with the
local unique continuation property. -/
theorem pointBranchedIntegralEff_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC)
    (A : OrientedBranched X) (B : OrientedBranched Y) (hAB : OrientedBranched.pull hf B = A)
    (hcptA : X.X.IsCompactBranched A.Θ) (hlocA : X.X.IsPointTame A.Θ A.T)
    (hcptB : Y.X.IsCompactBranched B.Θ) (hlocB : Y.X.IsPointTame B.Θ B.T)
    (ω' : Y.epFormsInfty 0) :
    X.pointBranchedIntegralEff hLX A.isBranchedEpSubgroupoid hcptA A.isOrientation hlocA
        (formsPullback f 0 ω') =
      Y.pointBranchedIntegralEff hLY B.isBranchedEpSubgroupoid hcptB B.isOrientation hlocB
        ω' := by
  subst hAB
  have hF := (rep f).isEquivalence_F
  have hΦ := isEquivalence_rep_Φ hf
  have hLM : (rep f).A.X.IsLUC := (EpFunctor.proposition_10_1_16 hΦ).2 hLY
  have hΘB := B.isBranchedEpSubgroupoid
  have hΘM := EpFunctor.isBranchedEpSubgroupoid_pullbackTheta hΦ hΘB
  have hcM := EpFunctor.isCompactBranched_pullbackTheta hΦ hΘB.isFunctorial hcptB
  have hTM := EpFunctor.isOrientation_pullSection hΦ B.hasIndependentTangentSums B.isOrientation
  have hlM := EpFunctor.isPointTame_pull hΦ hΘB B.isOrientation hlocB
  have e1 := EpFunctor.pointBranchedIntegralEff_eq_of_isTransported hF hLM hLX
    (OrientedBranched.pull hf B).isBranchedEpSubgroupoid hcptA
    (OrientedBranched.pull hf B).isOrientation hlocA
    (EpFunctor.pullbackTheta_pushforwardTheta hF.full
      ((rep f).Φ.isFunctorial_pullbackTheta hΘB.isFunctorial)) hΘM hcM hTM
    (EpFunctor.isTransported_push hF hTM.isGrHatSection) hlM (formsPullback f 0 ω')
  have e2 := EpFunctor.pointBranchedIntegralEff_eq_of_isTransported hΦ hLM hLY hΘB hcptB
    B.isOrientation hlocB rfl hΘM hcM hTM (EpFunctor.isTransported_pull hΦ
      B.isOrientation.isGrHatSection) hlM ω'
  rw [pullback_formsPullback f ω'] at e1
  exact e1.symm.trans e2

end EPLocalization.EPLoc

namespace PolyfoldClass

open EPLocalization EPLocalization.EPLoc

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z}

namespace OrientedRep

/-- **The weighted signed count `∫_θ̂ τ`** of a `0`-form `τ` over a compact representative that
is tame of dimension `0` (2021 p. 732 and Definition 9.5.6 for `n = 0`), `ω` the representative
of `τ` on `(X, α)`. -/
def pointIntegral (a : OrientedRep c) (hcpt : a.p.X.X.IsCompactBranched a.A.Θ)
    (hloc : a.p.X.X.IsPointTame a.A.Θ a.A.T) (τ : ScForm c 0) : ℝ :=
  a.p.X.pointBranchedIntegral a.A.isBranchedEpSubgroupoid hcpt a.A.isOrientation hloc
    (ScForm.toStructure a.p a.mem τ)

/-- A representative related to one that is tame of dimension `0` is tame of dimension `0`
(Definition 16.4.4). -/
theorem isPointTame_of_rel {a b : OrientedRep c} (h : Rel a b)
    (hlocb : b.p.X.X.IsPointTame b.A.Θ b.A.T) : a.p.X.X.IsPointTame a.A.Θ a.A.T := by
  obtain ⟨f, hf, -, hA⟩ := h
  rw [← hA]
  exact isPointTame_pull hf b.A hlocb

/-- **The weighted count does not depend on the representative** (2021 p. 732, for dimension
`0`; Theorem 11.4.1 for `n = 0`), among the compact representatives that are tame of dimension
`0`. -/
theorem pointIntegral_eq_of_rel {a b : OrientedRep c} (h : Rel a b)
    (hcpta : a.p.X.X.IsCompactBranched a.A.Θ) (hloca : a.p.X.X.IsPointTame a.A.Θ a.A.T)
    (hcptb : b.p.X.X.IsCompactBranched b.A.Θ) (hlocb : b.p.X.X.IsPointTame b.A.Θ b.A.T)
    (τ : ScForm c 0) : a.pointIntegral hcpta hloca τ = b.pointIntegral hcptb hlocb τ := by
  obtain ⟨f, hf, hβ, hA⟩ := h
  unfold pointIntegral
  rw [ScForm.toStructure_eq_formsPullback a.mem b.mem hf hβ τ]
  exact pointBranchedIntegral_pull hf a.A b.A hA hcpta hloca hcptb hlocb _

/-- **The effective weighted count `∮_θ̂ τ`** of a `0`-form (2021 p. 732 and Definition 9.5.6
(2) for `n = 0`); (ZHOU) gives the local unique continuation property (Proposition 7.4.10). -/
def pointIntegralEff (a : OrientedRep c) (hcpt : a.p.X.X.IsCompactBranched a.A.Θ)
    (hloc : a.p.X.X.IsPointTame a.A.Θ a.A.T) (τ : ScForm c 0) : ℝ :=
  a.p.X.pointBranchedIntegralEff (a.p.X.X.proposition_7_4_10_of_isZhou a.p.isZhou)
    a.A.isBranchedEpSubgroupoid hcpt a.A.isOrientation hloc (ScForm.toStructure a.p a.mem τ)

/-- **The effective weighted count does not depend on the representative** (2021 p. 732, for
dimension `0`; Theorem 11.4.2 for `n = 0`). -/
theorem pointIntegralEff_eq_of_rel {a b : OrientedRep c} (h : Rel a b)
    (hcpta : a.p.X.X.IsCompactBranched a.A.Θ) (hloca : a.p.X.X.IsPointTame a.A.Θ a.A.T)
    (hcptb : b.p.X.X.IsCompactBranched b.A.Θ) (hlocb : b.p.X.X.IsPointTame b.A.Θ b.A.T)
    (τ : ScForm c 0) :
    a.pointIntegralEff hcpta hloca τ = b.pointIntegralEff hcptb hlocb τ := by
  obtain ⟨f, hf, hβ, hA⟩ := h
  unfold pointIntegralEff
  rw [ScForm.toStructure_eq_formsPullback a.mem b.mem hf hβ τ]
  exact pointBranchedIntegralEff_pull hf _ _ a.A b.A hA hcpta hloca hcptb hlocb _

end OrientedRep

namespace OrientedSuborbifold

/-- **`θ̂` is tame of dimension `0`**: a representative is. -/
def IsPointTame (θ : OrientedSuborbifold c) : Prop :=
  ∃ a : OrientedRep c, ⟦a⟧ = θ ∧ a.p.X.X.IsPointTame a.A.Θ a.A.T

/-- **Tameness of dimension `0` does not depend on the representative**: `θ̂` is tame of
dimension `0` iff every representative is. -/
theorem isPointTame_iff (θ : OrientedSuborbifold c) :
    θ.IsPointTame ↔ ∀ a : OrientedRep c, ⟦a⟧ = θ → a.p.X.X.IsPointTame a.A.Θ a.A.T := by
  refine ⟨fun ⟨a, ha, h⟩ b hb => ?_, fun h => ?_⟩
  · exact OrientedRep.isPointTame_of_rel (Quotient.exact (hb.trans ha.symm)) h
  · obtain ⟨a, rfl⟩ := Quotient.exists_rep θ
    exact ⟨a, rfl, h a rfl⟩

/-- **The weighted signed count `∫_θ̂ τ`** of a `0`-form `τ` over a compact oriented branched
suborbifold `θ̂` of the polyfold that is tame of dimension `0` (2021 p. 732 for dimension `0`),
on a chosen representative. -/
def pointIntegral (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsPointTame) (τ : ScForm c 0) : ℝ :=
  θ.out.pointIntegral (isCompactBranched_of_mk hcpt _ (Quotient.out_eq θ))
    ((isPointTame_iff θ).1 htame _ (Quotient.out_eq θ)) τ

/-- **The weighted count is computed on every representative** (2021 p. 732, "does not depend
on the choice of the representatives", for dimension `0`). -/
theorem pointIntegral_eq (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsPointTame) (τ : ScForm c 0) (a : OrientedRep c) (ha : ⟦a⟧ = θ) :
    θ.pointIntegral hcpt htame τ = a.pointIntegral (isCompactBranched_of_mk hcpt a ha)
      ((isPointTame_iff θ).1 htame a ha) τ :=
  OrientedRep.pointIntegral_eq_of_rel (Quotient.exact ((Quotient.out_eq θ).trans ha.symm))
    _ _ _ _ τ

/-- **The effective weighted count `∮_θ̂ τ`** on a chosen representative. -/
def pointIntegralEff (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsPointTame) (τ : ScForm c 0) : ℝ :=
  θ.out.pointIntegralEff (isCompactBranched_of_mk hcpt _ (Quotient.out_eq θ))
    ((isPointTame_iff θ).1 htame _ (Quotient.out_eq θ)) τ

/-- **The effective weighted count is computed on every representative.** -/
theorem pointIntegralEff_eq (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsPointTame) (τ : ScForm c 0) (a : OrientedRep c) (ha : ⟦a⟧ = θ) :
    θ.pointIntegralEff hcpt htame τ = a.pointIntegralEff (isCompactBranched_of_mk hcpt a ha)
      ((isPointTame_iff θ).1 htame a ha) τ :=
  OrientedRep.pointIntegralEff_eq_of_rel (Quotient.exact ((Quotient.out_eq θ).trans ha.symm))
    _ _ _ _ τ

end OrientedSuborbifold

end PolyfoldClass

/-! ### The counts of the perturbed solutions on the polyfold -/

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- **The oriented branched suborbifold representative `((Λ ∘ F, T̂), (X, γ))`** of a regular
perturbation of dimension `0` in the model of a representative `a` of the section, with `T̂` cut
off outside `X_∞` (where an orientation is not read). -/
def pointOrientedRep (a : SectionRep c) (P : PointPerturbation a.S.A a.F) :
    OrientedRep c.polyfold where
  p := a.S.toPolyfoldStructure
  mem := toPolyfoldStructure_mem a.hS
  A := ⟨fun z => (P.Λ (a.F z) : ℚ), a.S.A.X.smoothPart P.T, P.isBranched,
    EpGroupoid.hasIndependentTangentSums _, P.isOrientation.smoothPart⟩
  smooth := fun _ hx => EpGroupoid.smoothPart_of_notMem hx

theorem isPointTame_pointOrientedRep (a : SectionRep c) (P : PointPerturbation a.S.A a.F) :
    (pointOrientedRep a P).p.X.X.IsPointTame (pointOrientedRep a P).A.Θ
      (pointOrientedRep a P).A.T := fun x hx => by
  obtain ⟨C, hS, hC⟩ := P.loc x hx
  exact ⟨C, hS, C.represents_congr (fun y hy => (EpGroupoid.smoothPart_of_mem hy).symm) hC⟩

/-- **The count in the model is the count of the class on the polyfold**: `∫_{(Λ ∘ f, o)} ω` for
the representative `ω` of `τ` in the model equals the weighted count of `τ` over the
representative `((Λ ∘ F, T̂), (X, γ))`. -/
theorem count_eq_pointIntegral (a : SectionRep c) (P : PointPerturbation a.S.A a.F)
    (τ : ScForm c.polyfold 0) :
    P.count (ScForm.toStructure a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) τ) =
      (pointOrientedRep a P).pointIntegral P.isCompact (isPointTame_pointOrientedRep a P) τ := by
  unfold PointPerturbation.count OrientedRep.pointIntegral EP.pointBranchedIntegral
    branchedIntegral
  rw [EpGroupoid.branchedMeasure_congr_orientation _ P.isBranched P.isCompact P.isOrientation
    P.isOrientation.smoothPart (fun y hy => (EpGroupoid.smoothPart_of_mem hy).symm) P.loc
    (isPointTame_pointOrientedRep a P)]
  rfl

/-- The same for the effective count. -/
theorem countEff_eq_pointIntegralEff (a : SectionRep c) (P : PointPerturbation a.S.A a.F)
    (τ : ScForm c.polyfold 0) :
    P.countEff (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou)
        (ScForm.toStructure a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) τ) =
      (pointOrientedRep a P).pointIntegralEff P.isCompact (isPointTame_pointOrientedRep a P)
        τ := by
  unfold PointPerturbation.countEff OrientedRep.pointIntegralEff EP.pointBranchedIntegralEff
    branchedIntegralEff
  rw [EpGroupoid.branchedMeasureEff_congr_orientation _ P.isBranched P.isCompact P.isOrientation
    P.isOrientation.smoothPart (fun y hy => (EpGroupoid.smoothPart_of_mem hy).symm)
    (P.loc.hasLUC (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou))
    ((isPointTame_pointOrientedRep a P).hasLUC
      (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou))]
  rfl

/-- **The count of the perturbed solutions does not depend on the model** (Theorem 16.6.6 for
Fredholm index `0`; Theorem 11.4.1 for `n = 0`): if regular perturbations of dimension `0` in the
models of two representatives `a`, `b` define the same oriented branched suborbifold of `Z`,
the weighted counts of a `0`-form `τ`, read through its representatives in the two models,
agree; so do the effective counts. -/
theorem count_eq_of_mk_eq (a b : SectionRep c) (Pa : PointPerturbation a.S.A a.F)
    (Pb : PointPerturbation b.S.A b.F)
    (h : (⟦pointOrientedRep a Pa⟧ : OrientedSuborbifold c.polyfold) = ⟦pointOrientedRep b Pb⟧)
    (τ : ScForm c.polyfold 0) :
    Pa.count (ScForm.toStructure a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) τ) =
        Pb.count
          (ScForm.toStructure b.S.toPolyfoldStructure (toPolyfoldStructure_mem b.hS) τ) ∧
      Pa.countEff (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou)
          (ScForm.toStructure a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) τ) =
        Pb.countEff (b.S.A.X.proposition_7_4_10_of_isZhou b.S.isZhou)
          (ScForm.toStructure b.S.toPolyfoldStructure (toPolyfoldStructure_mem b.hS) τ) := by
  rw [count_eq_pointIntegral, count_eq_pointIntegral, countEff_eq_pointIntegralEff,
    countEff_eq_pointIntegralEff]
  exact ⟨OrientedRep.pointIntegral_eq_of_rel (Quotient.exact h) _ _ _ _ τ,
    OrientedRep.pointIntegralEff_eq_of_rel (Quotient.exact h) _ _ _ _ τ⟩

end StrongPolyfoldBundle

end Polyfold
