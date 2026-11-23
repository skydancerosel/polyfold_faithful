import Polyfold.Chapter9.LocalFormsSheets
import Polyfold.Chapter9.FaceIntegralDimOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, proof of **Theorem 9.5.18, 2021 pp. 450–451**, and
**Remark 9.5.19, p. 451** (2017: Theorem 9.7, Remark 9.8), point G.153, the case `n = 1`.
Numbers and pages are the 2021 text's.

# The functions `β·ω` on one tame oriented sheet of dimension `1`

`LocalFormsSheets.lean` for `n = 1`: the boundary stratum of the sheet is a set of oriented
points, and the integral over it is the integral over oriented points
(`EpGroupoid.pointInteg`).

* **`EP.integ_d_smul_eq_pointInteg_sheet`**: `∫_{(N,o)} d(β·ω) = ∫_{∂₁N} β·ω|(∂₁N, o_∂)` for a
  tame oriented sheet `N` of dimension `1` whose boundary stratum has at most one point, when
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

variable (A : EP.{u}) {N : Set A.Obj} {β : A.Obj → ℝ}

/-- **Stokes on one tame oriented sheet of dimension `1`, for the integrals of §9.5** (the third
and the last equality of the display on p. 451, proof of Theorem 9.5.18, for `n = 1`): for a tame
oriented sheet `N` of dimension `1` in the class of §9.5 whose boundary stratum has at most one
point, and an sc-smooth `β` constant on the orbits with `N ∩ supp β` compact,
`∫_{(N,o)} d(βω) = ∫_{∂₁N} βω|(∂₁N, o_∂)`, i.e. `±(βω)(p)` if `∂₁N = {p}` and `0` if
`∂₁N = ∅`. -/
theorem integ_d_smul_eq_pointInteg_sheet (hN : A.X.PObj.IsSubmanifoldOfDim N (0 + 1))
    (ht : A.X.PObj.HasTameInducedStructure N) (o : A.X.PObj.SubmanifoldOrientation N (0 + 1))
    (hNs : N ∈ (A.epFormsInftyEval (0 + 1)).sheets)
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (hK : IsCompact (N ∩ tsupport β))
    (ω : A.epFormsInfty 0) (hs : (A.X.PObj.boundaryStratum N).Subsingleton) :
    (A.epFormsInftyEval (0 + 1)).integ (A.epFormsInftyD 0 (A.epFormsInftySmul β 0 hβ hinv ω))
        N o.tangent N =
      EpGroupoid.pointInteg (A.zeroFormEval (A.epFormsInftySmul β 0 hβ hinv ω))
        (A.X.PObj.boundaryStratum N) (o.stratumOrientation hN ht).tangent
        (A.X.PObj.boundaryStratum N) := by
  set a := A.epFormsInftySmul β 0 hβ hinv ω with ha
  let _ := A.X.PObj.paracompactSpace_subtype N
  have := EpGroupoid.FormEval.sigmaCompactSpace_of_mem_sheets hNs
  let hcs := hN.hasCornerStructureOfDim_of_hasTameInducedStructure ht
  let _ := (subPolyfold hN.1.isSubMPolyfold).cornerChartedSpace hcs
  have := (subPolyfold hN.1.isSubMPolyfold).isManifold_cornerChartedSpace hcs
  let Ns : MPolyfold.OrientedSheet A.X.PObj 0 :=
    { carrier := N
      isSub := hN.1.isSubMPolyfold
      hcs := hcs
      o := bridgeOrientation hcs o
      isContinuous := isContinuous_bridgeOrientation rfl (Nat.succ_pos 0) hN o }
  have h0 : Ns.VanishesOff (tsupport β) (A.epFormsInftyToObj 0 a) := fun y hy =>
    A.formsInftyRestrict_smul_eq_zero_all (hcs := hcs) hβ hinv ω y hy
  have hst := Ns.stokes (isClosed_tsupport β) hK (A.epFormsInftyToObj 0 a) h0
  have e : (BundledMPolyfold.of A.X.PObj).formsInftyD 0 (A.epFormsInftyToObj 0 a) =
      A.epFormsInftyToObj (0 + 1) (A.epFormsInftyD 0 a) :=
    LinearMap.congr_fun (A.formsInftyD_comp_epFormsInftyToObj 0) a
  have hcl : IsClosed ((↑) ⁻¹' tsupport β : Set N) :=
    (isClosed_tsupport β).preimage continuous_subtype_val
  have hcp : IsCompact ((↑) ⁻¹' tsupport β : Set N) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
    exact hK
  have hc1 : IsCompact (ManifoldForm.tsupport (formsInftyRestrict (0 + 1) hcs
      (A.epFormsInftyToObj (0 + 1) (A.epFormsInftyD 0 a)))) := by
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal (fun y hy => ?_) hcl)
    by_contra hyC
    exact hy (A.formsInftyRestrict_d_smul_eq_zero_all rfl hβ hinv ω y hyC)
  have hc0 : IsCompact (ManifoldForm.tsupport (formsInftyRestrict 0 hcs
      (A.epFormsInftyToObj 0 a))) := by
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal (fun y hy => ?_) hcl)
    by_contra hyC
    exact hy (h0 y hyC)
  have hA := A.epFormsInftyEval_integ_eq_integral (hcs := hcs) rfl (Nat.succ_pos 0) hNs o
    (A.epFormsInftyD 0 a) hc1
  have hC1 : ManifoldForm.ContMDiffForm (𝓠 (0 + 1)) 1
      (formsInftyRestrict 0 hcs (A.epFormsInftyToObj 0 a)) :=
    (contMDiffForm_formsInftyRestrict (hcs := hcs) rfl (A.epFormsInftyToObj 0 a)).of_le
      (by exact_mod_cast le_top)
  have key := EpGroupoid.boundaryIntegral_eq_pointInteg (M := N) (hcs := hcs) rfl hN ht o
    (A.zeroFormEval a) (formsInftyRestrict 0 hcs (A.epFormsInftyToObj 0 a)) hC1 hc0
    (fun y v => A.formsInftyRestrict_zero_eq a y (hN.1.subset_smoothSet y.2) v) hs
  rw [hA, ← e]
  exact hst.trans key

end EP

end Polyfold
