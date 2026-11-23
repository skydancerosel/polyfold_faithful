import Polyfold.Chapter9.LocalFormsStokes
import Polyfold.Chapter9.LocalFormsDimOneSheets
import Polyfold.Chapter11.BoundaryMeasureEquivalenceDimOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, proof of **Theorem 9.5.18, 2021 pp. 450–451**, and
**Remark 9.5.19, p. 451** (2017: Theorem 9.7, Remark 9.8), point G.153, the case `n = 1`.
Numbers and pages are the 2021 text's.

# The functions of the restriction `X|U` with values on the objects of `X`

For a saturated open set `U` of an ep-groupoid `X` and a cut-off `χ` on `X`, constant on the
orbits and with support in `U`, a class `b ∈ Ω⁰_{ep,∞}(X|U)` has the values `χ(y) · b(y)` at the
objects `y ∈ U` of `X` (and `0` off `U`).  These are functions constant on the orbits, to be
integrated over oriented points (`EpGroupoid.pointIntegration`).

* `EP.subVal`, `EP.subVal0`: the values `χ · b`, as a linear map to the functions constant on the
  orbits.
* `EP.subVal_pullback`: where `χ = 1`, the restriction `η|U` of a class of `X` has the values of
  `η`.
* `EP.subVal_subSmul_eq_zero`: `β·ω` vanishes at the points with `β = 0`.
* **`EP.subEval_stokes_sheet_dim1`**: `∫_{(M,o)} d(β·ω) = ∫_{∂₁M} β·ω|(∂₁M, o_∂)` for a tame
  oriented sheet `M ⊆ U` of dimension `1` with `χ = 1` on `M`, whose boundary stratum has at most
  one point.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EP

open MPolyfold EpGroupoid

variable (A : EP.{u}) {U : Set A.Obj} (hU : A.X.IsEpSubgroupoid U)

/-- **The values `χ · b` of a class `b ∈ Ω⁰_{ep,∞}(X|U)` at the objects of `X`** (Remark 9.5.19,
2021 p. 451). -/
def subVal (a : (A.sub hU).Obj) (χ : A.Obj → ℝ) (b : (A.sub hU).epFormsInfty 0) : A.Obj → ℝ :=
  fun y => χ y * (A.sub hU).zeroFormEval b (A.subRetract hU a y)

theorem subVal_apply (a : (A.sub hU).Obj) (χ : A.Obj → ℝ) (b : (A.sub hU).epFormsInfty 0)
    (y : A.Obj) :
    A.subVal hU a χ b y = χ y * (A.sub hU).zeroFormEval b (A.subRetract hU a y) := rfl

variable {χ : A.Obj → ℝ} (a : (A.sub hU).Obj) (hχU : tsupport χ ⊆ U)
  (hχinv : ∀ ψ : A.Mor, χ (A.X.src ψ) = χ (A.X.tgt ψ))

include hχU hχinv in
/-- The values `χ · b` are constant on the orbits of `X`. -/
theorem subVal_src_eq_tgt (b : (A.sub hU).epFormsInfty 0) (ψ : A.Mor) :
    A.subVal hU a χ b (A.X.src ψ) = A.subVal hU a χ b (A.X.tgt ψ) := by
  rw [subVal_apply, subVal_apply, ← hχinv ψ]
  by_cases hψ : A.X.src ψ ∈ U
  · have ht : A.X.tgt ψ ∈ U := A.X.isSaturated_iff.1 hU.isSaturated ψ hψ
    let ψ' : (A.sub hU).Mor := (⟨ψ, hψ, ht⟩ : A.X.morOn U)
    have hs : (A.sub hU).X.src ψ' = A.subRetract hU a (A.X.src ψ) := by
      rw [A.subRetract_of_mem hU a hψ]; rfl
    have htt : (A.sub hU).X.tgt ψ' = A.subRetract hU a (A.X.tgt ψ) := by
      rw [A.subRetract_of_mem hU a ht]; rfl
    rw [← hs, ← htt, (A.sub hU).zeroFormEval_src_eq_tgt b ψ']
  · rw [image_eq_zero_of_notMem_tsupport fun h => hψ (hχU h), zero_mul, zero_mul]

/-- **The values `χ · b`, `b ∈ Ω⁰_{ep,∞}(X|U)`, as functions on the objects of `X` constant on the
orbits.** -/
def subVal0 : (A.sub hU).epFormsInfty 0 →ₗ[ℝ] EpGroupoid.invariantFunctions A.X where
  toFun b := ⟨A.subVal hU a χ b, fun ψ => A.subVal_src_eq_tgt hU a hχU hχinv b ψ⟩
  map_add' b c := by
    refine Subtype.ext (funext fun y => ?_)
    change A.subVal hU a χ (b + c) y = A.subVal hU a χ b y + A.subVal hU a χ c y
    rw [subVal_apply, subVal_apply, subVal_apply, map_add, Pi.add_apply, mul_add]
  map_smul' r b := by
    refine Subtype.ext (funext fun y => ?_)
    change A.subVal hU a χ (r • b) y = r * A.subVal hU a χ b y
    rw [subVal_apply, subVal_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    ring

theorem coe_subVal0 (b : (A.sub hU).epFormsInfty 0) :
    (A.subVal0 hU a hχU hχinv b : A.Obj → ℝ) = A.subVal hU a χ b := rfl

variable (hUo : IsOpen U)

include hUo in
/-- **Where `χ = 1`, the restriction `η|U` of a class `η ∈ Ω⁰_{ep,∞}(X)` has the values of
`η`.** -/
theorem subVal_pullback (η : A.epFormsInfty 0) {y : A.Obj} (hyU : y ∈ U) (h1 : χ y = 1) :
    A.subVal hU a χ (epFormsInftyPullback (A.subFunctor hU) 0 η) y = A.zeroFormEval η y := by
  rw [subVal_apply, h1, one_mul]
  have hobj := A.subFunctor_obj_subRetract hU a hyU
  have hiff := (A.isLocalScDiffeo_subFunctor_obj hU hUo).mem_smoothSet_iff (A.subRetract hU a y)
  rw [hobj] at hiff
  by_cases hy : y ∈ A.X.PObj.smoothSet
  · have hp : A.subRetract hU a y ∈ (A.sub hU).X.PObj.smoothSet := by tauto
    rw [zeroFormEval_epFormsInftyPullback (A.subFunctor hU) η hp (by rw [hobj]; exact hy), hobj]
  · have hp : A.subRetract hU a y ∉ (A.sub hU).X.PObj.smoothSet := by tauto
    rw [(A.sub hU).zeroFormEval_of_not_mem _ hp, A.zeroFormEval_of_not_mem _ hy]

variable {β : A.Obj → ℝ} (hβ : A.X.PObj.IsScSmoothOn realPolyfold β U)
  (hβinv : ∀ φ : A.Mor, A.X.src φ ∈ U → β (A.X.src φ) = β (A.X.tgt φ))

include hχU in
/-- **`β·ω` vanishes at the points with `β = 0`.** -/
theorem subVal_subSmul_eq_zero (ω : A.epFormsInfty 0) {y : A.Obj} (h0 : β y = 0) :
    A.subVal hU a χ (A.subSmul hU hβ hβinv 0 ω) y = 0 := by
  rw [subVal_apply]
  by_cases hyU : y ∈ U
  · rw [subSmul, (A.sub hU).zeroFormEval_epFormsInftySmul (A.isScSmoothMap_subFun hU hβ)
      (A.subFun_src_eq_tgt hU hβinv), A.subFun_subRetract hU a β hyU, h0, zero_mul, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport fun h => hyU (hχU h), zero_mul]

variable (hχ : Continuous χ)

/-- **Stokes on one tame oriented sheet `M ⊆ U` of dimension `1` on which `χ = 1`, for the
functions `β·ω`** (the third and the last equality of the display on p. 451, proof of Theorem
9.5.18, for `n = 1`): `∫_{(M,o)} d(βω) = ∫_{∂₁M} βω|(∂₁M, o_∂)`, when `M` meets the closure of
`U ∩ {β ≠ 0}` in a compact set, `M` is in the class of the integral and `∂₁M` has at most one
point. -/
theorem subEval_stokes_sheet_dim1 {M : Set A.Obj}
    (hM : A.X.PObj.IsSubmanifoldOfDim M (0 + 1)) (ht : A.X.PObj.HasTameInducedStructure M)
    (o : A.X.PObj.SubmanifoldOrientation M (0 + 1)) (hMU : M ⊆ U) (h1 : ∀ y ∈ M, χ y = 1)
    (hMs : M ∈ (A.subEval hU hUo a (Nat.succ_pos 0) hχ hχU hχinv).sheets)
    (hs : (A.X.PObj.boundaryStratum M).Subsingleton)
    (hK : IsCompact (M ∩ closure (U ∩ {z | β z ≠ 0}))) (ω : A.epFormsInfty 0) :
    (A.subEval hU hUo a (Nat.succ_pos 0) hχ hχU hχinv).integ
        ((A.sub hU).epFormsInftyD 0 (A.subSmul hU hβ hβinv 0 ω)) M o.tangent M =
      pointInteg (A.subVal hU a χ (A.subSmul hU hβ hβinv 0 ω))
        (A.X.PObj.boundaryStratum M) (o.stratumOrientation hM ht).tangent
        (A.X.PObj.boundaryStratum M) := by
  have hd := A.isScDiffeoOn_subRetract hU hUo a
  set r := A.subRetract hU a with hr
  set F1 := A.subEval hU hUo a (Nat.succ_pos 0) hχ hχU hχinv with hF1
  set uu := A.subSmul hU hβ hβinv 0 ω with huu
  have hM' : (A.sub hU).X.PObj.IsSubmanifoldOfDim (r '' M) (0 + 1) :=
    hM.image_isScDiffeoOn hd hMU
  have ht' : (A.sub hU).X.PObj.HasTameInducedStructure (r '' M) :=
    MPolyfold.HasTameInducedStructure.image_of_isScDiffeoOn hM.1 ht hd hMU
  have hM's : r '' M ∈ ((A.sub hU).epFormsInftyEval (0 + 1)).sheets :=
    FormEval.image_mem_sheets_cross hd hMs hMU fun ωT =>
      ⟨ωT, A.evCompatOn_subEval hU hUo a _ hχ hχU hχinv h1 ωT⟩
  have step1 : ((A.sub hU).epFormsInftyEval (0 + 1)).integ ((A.sub hU).epFormsInftyD 0 uu)
      (r '' M) (o.mapDiffeo hM.1 hd hMU).tangent (r '' M) =
      F1.integ ((A.sub hU).epFormsInftyD 0 uu) M o.tangent M :=
    FormEval.integ_image_cross hd hMs hM's hMU o
      (A.evCompatOn_subEval hU hUo a _ hχ hχU hχinv h1 _) (SheetNullSets.isMeasIn_self M)
      (by rw [inter_self, inter_self])
  have hbd : (A.sub hU).X.PObj.boundaryStratum (r '' M) = r '' A.X.PObj.boundaryStratum M :=
    boundaryStratum_image_of_isScDiffeoOn hd hM.1 hMU
  have hbM : A.X.PObj.boundaryStratum M ⊆ M := fun _ h => h.1
  have hs' : ((A.sub hU).X.PObj.boundaryStratum (r '' M)).Subsingleton := by
    rw [hbd]; exact hs.image r
  have hK' : IsCompact (r '' M ∩ tsupport (A.subFun hU β)) := by
    have e : r '' M ∩ tsupport (A.subFun hU β) =
        r '' (M ∩ closure (U ∩ {z | β z ≠ 0})) ∩ tsupport (A.subFun hU β) := by
      ext z
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hz⟩
        refine ⟨⟨y, ⟨hy, ?_⟩, rfl⟩, hz⟩
        by_contra hcl
        exact A.subRetract_notMem_tsupport_subFun hU a (hMU hy) hcl hz
      · rintro ⟨⟨y, hy, rfl⟩, hz⟩
        exact ⟨⟨y, hy.1, rfl⟩, hz⟩
    rw [e]
    exact (hK.image_of_continuousOn (hd.isScSmoothOn.continuousOn.mono
      (inter_subset_left.trans hMU))).inter_right (isClosed_tsupport _)
  have step2 := (A.sub hU).integ_d_smul_eq_pointInteg_sheet hM' ht' (o.mapDiffeo hM.1 hd hMU)
    hM's (A.isScSmoothMap_subFun hU hβ) (A.subFun_src_eq_tgt hU hβinv) hK'
    (epFormsInftyPullback (A.subFunctor hU) 0 ω) hs'
  rw [← step1]
  refine step2.trans ?_
  change pointInteg ((A.sub hU).zeroFormEval uu) _ _ _ = _
  by_cases hne : (A.X.PObj.boundaryStratum M).Nonempty
  · obtain ⟨p, hp⟩ := hne
    have hp' : r p ∈ (A.sub hU).X.PObj.boundaryStratum (r '' M) := by
      rw [hbd]; exact mem_image_of_mem r hp
    have hg : ((o.mapDiffeo hM.1 hd hMU).stratumOrientation hM' ht').tangent (r p) =
        ((o.stratumOrientation hM ht).tangent p).map (tangentMapOn hd.isScSmoothOn) := by
      rw [SubmanifoldOrientation.stratumOrientation_tangent _ hM' ht' hp',
        SubmanifoldOrientation.mapDiffeo_tangent o hM.1 hd hMU (hbM hp),
        o.stratumOrientation_tangent hM ht hp]
      exact boundaryOp_map_tangentMapOn hd (hMU (hbM hp)) (o.isOrientedAt_tangent (hbM hp))
    have hiff : (((o.stratumOrientation hM ht).tangent p).map
        (tangentMapOn hd.isScSmoothOn)).frames.Nonempty ↔
        ((o.stratumOrientation hM ht).tangent p).frames.Nonempty := by
      change ((fun v => tangentMapOn hd.isScSmoothOn ∘ v) ''
        ((o.stratumOrientation hM ht).tangent p).frames).Nonempty ↔ _
      exact image_nonempty
    have hsign : frameSign (((o.stratumOrientation hM ht).tangent p).map
        (tangentMapOn hd.isScSmoothOn)) = frameSign ((o.stratumOrientation hM ht).tangent p) := by
      classical
      unfold frameSign
      by_cases h : ((o.stratumOrientation hM ht).tangent p).frames.Nonempty
      · rw [if_pos h, if_pos (hiff.2 h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]
    rw [pointInteg_of_mem hs' ⟨hp', hp'⟩, pointInteg_of_mem hs ⟨hp, hp⟩, hg, hsign,
      subVal_apply, h1 p (hbM hp), one_mul]
  · have hne' : ¬ ((A.sub hU).X.PObj.boundaryStratum (r '' M)).Nonempty := by
      rw [hbd]; exact fun h => hne (image_nonempty.1 h)
    rw [pointInteg_of_empty (by rw [inter_self]; exact not_nonempty_iff_eq_empty.1 hne'),
      pointInteg_of_empty (by rw [inter_self]; exact not_nonempty_iff_eq_empty.1 hne)]

end EP

end Polyfold
