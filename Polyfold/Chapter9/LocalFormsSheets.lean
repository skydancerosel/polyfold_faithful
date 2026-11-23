import Polyfold.Chapter9.BoundaryCover

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, proof of **Theorem 9.5.18, 2021 pp. 450–451**, and
**Remark 9.5.19, p. 451** (2017: Theorem 9.7, Remark 9.8), point G.153.  Numbers and pages are
the 2021 text's.

# The forms `β·ω` on one tame oriented sheet

The statements of `StokesSheetAllDegrees.lean`, `StokesBoundaryMeasure.lean` and
`BoundaryIntegralStratum.lean` for the sheets `Mᵢ` of an oriented tame structure only use the
sheet: a tame submanifold `N` of dimension `m + 1` with an orientation.  They are restated here
for such a sheet.

* `EP.ev_d_smul_eq_zero_sheet`: `d(β·ω)` vanishes on `T_yN` for `y ∉ supp β`.
* **`EP.integ_d_smul_eq_msInteg_sheet`**: `∫_{(N,o)} d(β·ω) = ∫_{∂₁N} β·ω|(∂₁N, o_∂)` when
  `N ∩ supp β` is compact.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

open MPolyfold

namespace EP

variable (A : EP.{u}) {m : ℕ} {N : Set A.Obj} {β : A.Obj → ℝ}

/-- **`d(β·ω)` vanishes on the tangent spaces `T_yN` of a tame oriented sheet at the points off
`supp β`** (2021 p. 451). -/
theorem ev_d_smul_eq_zero_sheet (hN : A.X.PObj.IsSubmanifoldOfDim N (m + 1))
    (ht : A.X.PObj.HasTameInducedStructure N) (o : A.X.PObj.SubmanifoldOrientation N (m + 1))
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (ω : A.epFormsInfty m) {y : A.Obj}
    (hy : y ∈ N) (hyβ : y ∉ tsupport β) {α : Fin (m + 1) → A.X.PObj.TangentSpace}
    (hα : ∀ j, α j ∈ A.X.PObj.submanifoldTangent N y) :
    (A.epFormsInftyEval (m + 1)).ev (A.epFormsInftyD m (A.epFormsInftySmul β m hβ hinv ω)) α =
      0 := by
  let _ := A.X.PObj.paracompactSpace_subtype N
  let hcs := hN.hasCornerStructureOfDim_of_hasTameInducedStructure ht
  let _ := (subPolyfold hN.1.isSubMPolyfold).cornerChartedSpace hcs
  exact A.epFormsInftyEval_eq_zero_of_restrict (hcs := hcs) (Nat.succ_pos m) hN o _ ⟨y, hy⟩
    (A.formsInftyRestrict_d_smul_eq_zero_all rfl hβ hinv ω ⟨y, hy⟩ hyβ) hα

/-- **Stokes on one tame oriented sheet, for the integrals of §9.5** (the third and the last
equality of the display on p. 451, proof of Theorem 9.5.18): for a tame oriented sheet `N` of
dimension `m + 1` in the class of §9.5, an sc-smooth `β` constant on the orbits with
`N ∩ supp β` compact, and `∂₁N` in the class `msheets` when it is nonempty,
`∫_{(N,o)} d(βω) = ∫_{∂₁N} βω|(∂₁N, o_∂)`. -/
theorem integ_d_smul_eq_msInteg_sheet (hm : 0 < m) (hN : A.X.PObj.IsSubmanifoldOfDim N (m + 1))
    (ht : A.X.PObj.HasTameInducedStructure N) (o : A.X.PObj.SubmanifoldOrientation N (m + 1))
    (hNs : N ∈ (A.epFormsInftyEval (m + 1)).sheets)
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (hK : IsCompact (N ∩ tsupport β))
    (ω : A.epFormsInfty m)
    (hb : (A.X.PObj.boundaryStratum N).Nonempty →
      A.X.PObj.boundaryStratum N ∈ (A.epFormsInftyEval m).msheets) :
    (A.epFormsInftyEval (m + 1)).integ (A.epFormsInftyD m (A.epFormsInftySmul β m hβ hinv ω))
        N o.tangent N =
      (A.epFormsInftyEval m).msInteg (A.epFormsInftySmul β m hβ hinv ω)
        (A.X.PObj.boundaryStratum N) (o.stratumOrientation hN ht).tangent
        (A.X.PObj.boundaryStratum N) := by
  set a := A.epFormsInftySmul β m hβ hinv ω with ha
  let _ := A.X.PObj.paracompactSpace_subtype N
  have := EpGroupoid.FormEval.sigmaCompactSpace_of_mem_sheets hNs
  let hcs := hN.hasCornerStructureOfDim_of_hasTameInducedStructure ht
  let _ := (subPolyfold hN.1.isSubMPolyfold).cornerChartedSpace hcs
  have := (subPolyfold hN.1.isSubMPolyfold).isManifold_cornerChartedSpace hcs
  let Ns : MPolyfold.OrientedSheet A.X.PObj m :=
    { carrier := N
      isSub := hN.1.isSubMPolyfold
      hcs := hcs
      o := bridgeOrientation hcs o
      isContinuous := isContinuous_bridgeOrientation rfl (Nat.succ_pos m) hN o }
  have h0 : Ns.VanishesOff (tsupport β) (A.epFormsInftyToObj m a) := fun y hy =>
    A.formsInftyRestrict_smul_eq_zero_all (hcs := hcs) hβ hinv ω y hy
  have hst := Ns.stokes (isClosed_tsupport β) hK (A.epFormsInftyToObj m a) h0
  have e : (BundledMPolyfold.of A.X.PObj).formsInftyD m (A.epFormsInftyToObj m a) =
      A.epFormsInftyToObj (m + 1) (A.epFormsInftyD m a) :=
    LinearMap.congr_fun (A.formsInftyD_comp_epFormsInftyToObj m) a
  have hcl : IsClosed ((↑) ⁻¹' tsupport β : Set N) :=
    (isClosed_tsupport β).preimage continuous_subtype_val
  have hcp : IsCompact ((↑) ⁻¹' tsupport β : Set N) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
    exact hK
  have hc1 : IsCompact (ManifoldForm.tsupport (formsInftyRestrict (m + 1) hcs
      (A.epFormsInftyToObj (m + 1) (A.epFormsInftyD m a)))) := by
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal (fun y hy => ?_) hcl)
    by_contra hyC
    exact hy (A.formsInftyRestrict_d_smul_eq_zero_all rfl hβ hinv ω y hyC)
  have hc0 : IsCompact (ManifoldForm.tsupport (formsInftyRestrict m hcs
      (A.epFormsInftyToObj m a))) := by
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal (fun y hy => ?_) hcl)
    by_contra hyC
    exact hy (h0 y hyC)
  have hA := A.epFormsInftyEval_integ_eq_integral (hcs := hcs) rfl (Nat.succ_pos m) hNs o
    (A.epFormsInftyD m a) hc1
  have hC1 : ManifoldForm.ContMDiffForm (𝓠 (m + 1)) 1
      (formsInftyRestrict m hcs (A.epFormsInftyToObj m a)) :=
    (contMDiffForm_formsInftyRestrict (hcs := hcs) rfl (A.epFormsInftyToObj m a)).of_le
      (by exact_mod_cast le_top)
  have key := (A.epFormsInftyEval m).boundaryIntegral_eq_msInteg (M := N) (hcs := hcs) rfl hm
    hN ht o a (formsInftyRestrict m hcs (A.epFormsInftyToObj m a)) hC1 hc0
    (fun y v => A.formsInftyRestrict_epFormsInftyToObj hm hN.1 a y v) hb
  rw [hA, ← e]
  exact hst.trans key

end EP

end Polyfold
