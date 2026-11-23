import Polyfold.Chapter9.LocalFormsSub
import Polyfold.Chapter9.LocalFormsSheets

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, proof of **Theorem 9.5.18, 2021 pp. 450–451**, and
**Remark 9.5.19, p. 451** (2017: Theorem 9.7, Remark 9.8), point G.153.  Numbers and pages are
the 2021 text's.

# The forms `β·ω` for a function `β` which is sc-smooth on a saturated open set `U`

Let `U` be a saturated open subset of the object space of `X`, `β` a function sc-smooth on `U`
and constant on the orbits in `U`, and `χ` a continuous cut-off, constant on the orbits, with
support in `U`.  The form `β·(ω|U)` is a class of `Ωᵐ_{ep,∞}(X|U)`; its values on the tangent
vectors of `X` are those of `EP.subEval`.  On the sheets on which `χ = 1` these values are the
values of `β·ω`, and the statements of the proof of Theorem 9.5.18 for one sheet hold.

* `EP.subFun`, `EP.subSmul`: `β|U` and `β·(ω|U)`.
* `EP.subEval_d_subSmul_eq_zero`, `EP.subEval_subSmul_eq_zero`: `d(β·ω)` and `β·ω` vanish on
  the tangent spaces of the sheets off the closure of `U ∩ {β ≠ 0}`.
* **`EP.subEval_stokes_sheet`**: `∫_{(M,o)} d(β·ω) = ∫_{∂₁M} β·ω|(∂₁M, o_∂)` for a tame oriented
  sheet `M ⊆ U` with `χ = 1` on `M`.
* `EP.subEval_boundaryStratum_inter_mem_msheets`: the boundary stratum near a compact part of
  such a sheet is in the class `msheets`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EP

open MPolyfold EpGroupoid

variable (A : EP.{u}) {U : Set A.Obj} (hU : A.X.IsEpSubgroupoid U)

/-- The restriction `β|U` as a function on the object space of `X|U`. -/
def subFun (β : A.Obj → ℝ) : (A.sub hU).Obj → ℝ := fun w => β ((A.subFunctor hU).obj w)

theorem subFun_subRetract (a : (A.sub hU).Obj) (β : A.Obj → ℝ) {y : A.Obj} (hy : y ∈ U) :
    A.subFun hU β (A.subRetract hU a y) = β y := by
  unfold subFun
  rw [A.subFunctor_obj_subRetract hU a hy]

theorem isScSmoothMap_subFun {β : A.Obj → ℝ}
    (hβ : A.X.PObj.IsScSmoothOn realPolyfold β U) :
    (A.sub hU).X.PObj.IsScSmoothMap realPolyfold (A.subFun hU β) :=
  hβ.comp (A.subFunctor hU).isScSmoothMap_obj fun w _ => A.subFunctor_obj_mem hU w

theorem subFun_src_eq_tgt {β : A.Obj → ℝ}
    (hβinv : ∀ φ : A.Mor, A.X.src φ ∈ U → β (A.X.src φ) = β (A.X.tgt φ))
    (φ : (A.sub hU).Mor) :
    A.subFun hU β ((A.sub hU).X.src φ) = A.subFun hU β ((A.sub hU).X.tgt φ) := by
  unfold subFun
  rw [← (A.subFunctor hU).src_mor φ, ← (A.subFunctor hU).tgt_mor φ]
  refine hβinv _ ?_
  rw [(A.subFunctor hU).src_mor]
  exact A.subFunctor_obj_mem hU _

theorem continuous_subFunctor_obj : Continuous (A.subFunctor hU).obj :=
  continuousOn_univ.1 (A.subFunctor hU).isScSmoothMap_obj.continuousOn

/-- A point of `U` off the closure of `U ∩ {β ≠ 0}` is off the support of `β|U`. -/
theorem subRetract_notMem_tsupport_subFun (a : (A.sub hU).Obj) {β : A.Obj → ℝ} {y : A.Obj}
    (hy : y ∈ U) (h : y ∉ closure (U ∩ {z | β z ≠ 0})) :
    A.subRetract hU a y ∉ tsupport (A.subFun hU β) := by
  intro hmem
  have hcl : IsClosed ((A.subFunctor hU).obj ⁻¹' closure (U ∩ {z | β z ≠ 0})) :=
    isClosed_closure.preimage (A.continuous_subFunctor_obj hU)
  have h2 : A.subRetract hU a y ∈ (A.subFunctor hU).obj ⁻¹' closure (U ∩ {z | β z ≠ 0}) :=
    closure_minimal (s := Function.support (A.subFun hU β))
      (t := (A.subFunctor hU).obj ⁻¹' closure (U ∩ {z | β z ≠ 0})) (fun w hw =>
      subset_closure (show (A.subFunctor hU).obj w ∈ U ∩ {z | β z ≠ 0} from
        ⟨A.subFunctor_obj_mem hU w, hw⟩)) hcl hmem
  rw [mem_preimage, A.subFunctor_obj_subRetract hU a hy] at h2
  exact h h2

variable {β : A.Obj → ℝ} (hβ : A.X.PObj.IsScSmoothOn realPolyfold β U)
  (hβinv : ∀ φ : A.Mor, A.X.src φ ∈ U → β (A.X.src φ) = β (A.X.tgt φ))

/-- **The form `β·(ω|U)`** of `Ωᵐ_{ep,∞}(X|U)` (2021 p. 451: `ω_k = β_k ω`, with `β_k` defined
near `supp Θ`, Remark 9.5.19). -/
def subSmul (m : ℕ) (ω : A.epFormsInfty m) : (A.sub hU).epFormsInfty m :=
  (A.sub hU).epFormsInftySmul (A.subFun hU β) m (A.isScSmoothMap_subFun hU hβ)
    (A.subFun_src_eq_tgt hU hβinv) (epFormsInftyPullback (A.subFunctor hU) m ω)

variable {m : ℕ} {χ : A.Obj → ℝ} (hUo : IsOpen U) (a : (A.sub hU).Obj)
  (hχ : Continuous χ) (hχU : tsupport χ ⊆ U)
  (hχinv : ∀ ψ : A.Mor, χ (A.X.src ψ) = χ (A.X.tgt ψ))

/-- **`d(β·ω)` vanishes on the tangent spaces of a tame oriented sheet `M ⊆ U` at the points
off the closure of `U ∩ {β ≠ 0}`.** -/
theorem subEval_d_subSmul_eq_zero {M : Set A.Obj}
    (hM : A.X.PObj.IsSubmanifoldOfDim M (m + 1)) (ht : A.X.PObj.HasTameInducedStructure M)
    (o : A.X.PObj.SubmanifoldOrientation M (m + 1)) (hMU : M ⊆ U) (ω : A.epFormsInfty m)
    {y : A.Obj} (hy : y ∈ M) (hyβ : y ∉ closure (U ∩ {z | β z ≠ 0}))
    {α : Fin (m + 1) → A.X.PObj.TangentSpace}
    (hα : ∀ j, α j ∈ A.X.PObj.submanifoldTangent M y) :
    (A.subEval hU hUo a (Nat.succ_pos m) hχ hχU hχinv).ev
      ((A.sub hU).epFormsInftyD m (A.subSmul hU hβ hβinv m ω)) α = 0 := by
  have hd := A.isScDiffeoOn_subRetract hU hUo a
  rw [A.subEval_ev hU hUo a (Nat.succ_pos m) hχ hχU hχinv _ hα]
  have h0 := (A.sub hU).ev_d_smul_eq_zero_sheet (hM.image_isScDiffeoOn hd hMU)
    (MPolyfold.HasTameInducedStructure.image_of_isScDiffeoOn hM.1 ht hd hMU)
    (o.mapDiffeo hM.1 hd hMU) (A.isScSmoothMap_subFun hU hβ) (A.subFun_src_eq_tgt hU hβinv)
    (epFormsInftyPullback (A.subFunctor hU) m ω) (y := A.subRetract hU a y) ⟨y, hy, rfl⟩
    (A.subRetract_notMem_tsupport_subFun hU a (hMU hy) hyβ)
    (α := fun i => tangentMapOn hd.isScSmoothOn (α i)) (fun j => by
      rw [submanifoldTangent_image_of_isScDiffeoOn hd hM.1 hMU hy]
      exact ⟨α j, hα j, rfl⟩)
  rw [subSmul, h0, mul_zero]

/-- **`β·ω` vanishes on the tangent spaces over the points with `β = 0`.** -/
theorem subEval_subSmul_eq_zero (hm : 0 < m) (ω : A.epFormsInfty m) {N' : Set A.Obj}
    (hN' : A.X.PObj.IsSmoothSubmanifold N') {y : A.Obj} (hy : y ∈ N') (h0 : β y = 0)
    {α : Fin m → A.X.PObj.TangentSpace} (hα : ∀ j, α j ∈ A.X.PObj.submanifoldTangent N' y) :
    (A.subEval hU hUo a hm hχ hχU hχinv).ev (A.subSmul hU hβ hβinv m ω) α = 0 := by
  have hd := A.isScDiffeoOn_subRetract hU hUo a
  rw [A.subEval_ev hU hUo a hm hχ hχU hχinv _ hα]
  by_cases hyU : y ∈ U
  · rw [subSmul, (A.sub hU).epFormsInftyEval_epFormsInftySmul (A.isScSmoothMap_subFun hU hβ)
      (A.subFun_src_eq_tgt hU hβinv) _
      ((hN'.inter_isOpen hUo).image_of_isScDiffeoOn hd inter_subset_right)
      (y := A.subRetract hU a y) ⟨y, ⟨hy, hyU⟩, rfl⟩
      (fun i => tangentMapOn_mem_submanifoldTangent_image hd hN' hyU (hα i)),
      A.subFun_subRetract hU a β hyU, h0, zero_mul, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport fun h => hyU (hχU h), zero_mul]

/-- **Stokes on one tame oriented sheet `M ⊆ U` on which `χ = 1`, for the forms `β·ω`**
(the third and the last equality of the display on p. 451, proof of Theorem 9.5.18):
`∫_{(M,o)} d(βω) = ∫_{∂₁M} βω|(∂₁M, o_∂)`, when `M` meets the closure of `U ∩ {β ≠ 0}` in a
compact set, `M` is in the class of the integral and `∂₁M` in the class `msheets` when it is
nonempty. -/
theorem subEval_stokes_sheet (hm : 0 < m) {M : Set A.Obj}
    (hM : A.X.PObj.IsSubmanifoldOfDim M (m + 1)) (ht : A.X.PObj.HasTameInducedStructure M)
    (o : A.X.PObj.SubmanifoldOrientation M (m + 1)) (hMU : M ⊆ U) (h1 : ∀ y ∈ M, χ y = 1)
    (hMs : M ∈ (A.subEval hU hUo a (Nat.succ_pos m) hχ hχU hχinv).sheets)
    (hb : (A.X.PObj.boundaryStratum M).Nonempty →
      A.X.PObj.boundaryStratum M ∈ (A.subEval hU hUo a hm hχ hχU hχinv).msheets)
    (hK : IsCompact (M ∩ closure (U ∩ {z | β z ≠ 0}))) (ω : A.epFormsInfty m) :
    (A.subEval hU hUo a (Nat.succ_pos m) hχ hχU hχinv).integ
        ((A.sub hU).epFormsInftyD m (A.subSmul hU hβ hβinv m ω)) M o.tangent M =
      (A.subEval hU hUo a hm hχ hχU hχinv).msInteg (A.subSmul hU hβ hβinv m ω)
        (A.X.PObj.boundaryStratum M) (o.stratumOrientation hM ht).tangent
        (A.X.PObj.boundaryStratum M) := by
  have hd := A.isScDiffeoOn_subRetract hU hUo a
  set r := A.subRetract hU a with hr
  set F1 := A.subEval hU hUo a (Nat.succ_pos m) hχ hχU hχinv with hF1
  set G0 := A.subEval hU hUo a hm hχ hχU hχinv with hG0
  set uu := A.subSmul hU hβ hβinv m ω with huu
  have hM' : (A.sub hU).X.PObj.IsSubmanifoldOfDim (r '' M) (m + 1) :=
    hM.image_isScDiffeoOn hd hMU
  have ht' : (A.sub hU).X.PObj.HasTameInducedStructure (r '' M) :=
    MPolyfold.HasTameInducedStructure.image_of_isScDiffeoOn hM.1 ht hd hMU
  have hM's : r '' M ∈ ((A.sub hU).epFormsInftyEval (m + 1)).sheets :=
    FormEval.image_mem_sheets_cross hd hMs hMU fun ωT =>
      ⟨ωT, A.evCompatOn_subEval hU hUo a _ hχ hχU hχinv h1 ωT⟩
  have step1 : ((A.sub hU).epFormsInftyEval (m + 1)).integ ((A.sub hU).epFormsInftyD m uu)
      (r '' M) (o.mapDiffeo hM.1 hd hMU).tangent (r '' M) =
      F1.integ ((A.sub hU).epFormsInftyD m uu) M o.tangent M :=
    FormEval.integ_image_cross hd hMs hM's hMU o
      (A.evCompatOn_subEval hU hUo a _ hχ hχU hχinv h1 _) (SheetNullSets.isMeasIn_self M)
      (by rw [inter_self, inter_self])
  have hbd : (A.sub hU).X.PObj.boundaryStratum (r '' M) = r '' A.X.PObj.boundaryStratum M :=
    boundaryStratum_image_of_isScDiffeoOn hd hM.1 hMU
  have hbM : A.X.PObj.boundaryStratum M ⊆ M := fun _ h => h.1
  have hcompat0 : ∀ ωT, FormEval.EvCompatOn G0 ((A.sub hU).epFormsInftyEval m) hd
      (A.X.PObj.boundaryStratum M) ωT ωT := fun ωT =>
    A.evCompatOn_subEval hU hUo a hm hχ hχU hχinv (fun y hy => h1 y (hbM hy)) ωT
  have himg : (A.X.PObj.boundaryStratum M).Nonempty →
      r '' A.X.PObj.boundaryStratum M ∈ ((A.sub hU).epFormsInftyEval m).msheets := fun hne =>
    FormEval.image_mem_msheets_cross hd (hb hne) (hbM.trans hMU) fun ωT => ⟨ωT, hcompat0 ωT⟩
  have hb' : ((A.sub hU).X.PObj.boundaryStratum (r '' M)).Nonempty →
      (A.sub hU).X.PObj.boundaryStratum (r '' M) ∈ ((A.sub hU).epFormsInftyEval m).msheets :=
    fun hne => by
      rw [hbd] at hne ⊢
      exact himg (image_nonempty.1 hne)
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
  have step2 := (A.sub hU).integ_d_smul_eq_msInteg_sheet hm hM' ht' (o.mapDiffeo hM.1 hd hMU)
    hM's (A.isScSmoothMap_subFun hU hβ) (A.subFun_src_eq_tgt hU hβinv) hK'
    (epFormsInftyPullback (A.subFunctor hU) m ω) hb'
  rw [← step1]
  refine step2.trans ?_
  change ((A.sub hU).epFormsInftyEval m).msInteg uu _ _ _ = _
  by_cases hne : (A.X.PObj.boundaryStratum M).Nonempty
  · have hN := hb hne
    have hfN := himg hne
    have hN' : (A.sub hU).X.PObj.boundaryStratum (r '' M) ∈
        ((A.sub hU).epFormsInftyEval m).msheets := by rw [hbd]; exact hfN
    have e1 := (((A.sub hU).epFormsInftyEval m).msheetIntegration hm).integ_congr uu _ hN' _ hfN
      ((o.mapDiffeo hM.1 hd hMU).stratumOrientation hM' ht')
      ((o.stratumOrientation hM ht).mapDiffeo (isSubmanifoldOfDim_boundaryStratum hM ht).1 hd
        (hbM.trans hMU))
      ((A.sub hU).X.PObj.boundaryStratum (r '' M)) (fun z hz => ⟨hz, hbd.subset hz⟩)
      (SheetNullSets.isMeasIn_self _) (fun z hz => by
        obtain ⟨y, hy, rfl⟩ := hbd.subset hz
        rw [SubmanifoldOrientation.stratumOrientation_tangent _ hM' ht' hz,
          SubmanifoldOrientation.mapDiffeo_tangent _ _ hd _ hy,
          SubmanifoldOrientation.mapDiffeo_tangent o hM.1 hd hMU (hbM hy),
          o.stratumOrientation_tangent hM ht hy]
        exact boundaryOp_map_tangentMapOn hd (hMU (hbM hy)) (o.isOrientedAt_tangent (hbM hy)))
    simp only [FormEval.msheetIntegration_integ] at e1
    rw [e1]
    exact FormEval.msInteg_image_cross hd hm hN hfN (hbM.trans hMU)
      (o.stratumOrientation hM ht) (hcompat0 uu) (SheetNullSets.isMeasIn_self _)
      (by rw [hbd, inter_self, inter_self])
  · have hne' : ¬ ((A.sub hU).X.PObj.boundaryStratum (r '' M)).Nonempty := by
      rw [hbd]; exact fun h => hne (image_nonempty.1 h)
    rw [FormEval.msInteg_of_inter_eq_empty _ _
        (by rw [inter_self]; exact not_nonempty_iff_eq_empty.1 hne'),
      FormEval.msInteg_of_inter_eq_empty _ _
        (by rw [inter_self]; exact not_nonempty_iff_eq_empty.1 hne)]

/-- **The boundary stratum near a compact part of a tame sheet `M ⊆ U` on which `χ = 1` lies in
the class `msheets`** of the values `χ · a`, `a ∈ Ωᵐ_{ep,∞}(X|U)`
(as `EP.boundaryStratum_inter_mem_msheets`). -/
theorem subEval_boundaryStratum_inter_mem_msheets (hm : 0 < m) {M : Set A.Obj}
    (hM : A.X.PObj.IsSubmanifoldOfDim M (m + 1)) (ht : A.X.PObj.HasTameInducedStructure M)
    (hMU : M ⊆ U) (h1 : ∀ y ∈ M, χ y = 1) {V : Set A.Obj} (hV : IsOpen V) {K : Set A.Obj}
    (hK : IsCompact K) (hKM : K ⊆ M) (hNK : A.X.PObj.boundaryStratum M ∩ V ⊆ K)
    (hne : (A.X.PObj.boundaryStratum M ∩ V).Nonempty) :
    A.X.PObj.boundaryStratum M ∩ V ∈ (A.subEval hU hUo a hm hχ hχU hχinv).msheets := by
  have hd := A.isScDiffeoOn_subRetract hU hUo a
  set r := A.subRetract hU a with hr
  have hbM : A.X.PObj.boundaryStratum M ⊆ M := fun _ h => h.1
  have hbd : (A.sub hU).X.PObj.boundaryStratum (r '' M) = r '' A.X.PObj.boundaryStratum M :=
    boundaryStratum_image_of_isScDiffeoOn hd hM.1 hMU
  have himg : (A.sub hU).X.PObj.boundaryStratum (r '' M) ∩ (A.subFunctor hU).obj ⁻¹' V =
      r '' (A.X.PObj.boundaryStratum M ∩ V) := by
    rw [hbd]
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hz⟩
      rw [mem_preimage, A.subFunctor_obj_subRetract hU a (hMU (hbM hy))] at hz
      exact ⟨y, ⟨hy, hz⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hyV⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, ?_⟩
      rw [mem_preimage, A.subFunctor_obj_subRetract hU a (hMU (hbM hy))]
      exact hyV
  have h := (A.sub hU).boundaryStratum_inter_mem_msheets hm (hM.image_isScDiffeoOn hd hMU)
    (MPolyfold.HasTameInducedStructure.image_of_isScDiffeoOn hM.1 ht hd hMU)
    (hV.preimage (A.continuous_subFunctor_obj hU))
    (hK.image_of_continuousOn (hd.isScSmoothOn.continuousOn.mono (hKM.trans hMU)))
    (image_mono hKM) (by rw [himg]; exact image_mono hNK) (by rw [himg]; exact hne.image _)
  rw [himg] at h
  have hsub : A.X.PObj.boundaryStratum M ∩ V ⊆ U := inter_subset_left.trans (hbM.trans hMU)
  have h2 := FormEval.image_mem_msheets_cross hd.symm h (subset_univ _) fun ωT =>
    ⟨ωT, A.evCompatOn_symm_subEval hU hUo a hm hχ hχU hχinv
      (N' := r '' (A.X.PObj.boundaryStratum M ∩ V)) (fun z hz => by
        obtain ⟨y, hy, rfl⟩ := hz
        rw [A.subFunctor_obj_subRetract hU a (hsub hy)]
        exact h1 y (hbM hy.1)) ωT⟩
  have e : (A.subFunctor hU).obj '' (r '' (A.X.PObj.boundaryStratum M ∩ V)) =
      A.X.PObj.boundaryStratum M ∩ V := by
    rw [image_image]
    exact (image_congr fun y hy => A.subFunctor_obj_subRetract hU a (hsub hy)).trans
      (image_id' _)
  rw [e] at h2
  exact h2

end EP

end Polyfold
