import Polyfold.Chapter9.MeasureWholeSheets
import Polyfold.Chapter9.LevelRestrict
import Polyfold.Chapter9.TameOpen

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, proof of Theorem 9.5.18, pp. 450–451 (gap G.110).  Numbers and pages are
the 2021 text's.

# Stokes' theorem on the sheets of one `U(x_k)`, for `ω_k = β_k ω`

## What is formalized

* `FormEval.sigmaCompactSpace_of_mem_sheets`: a sheet of the class `F.sheets` is σ-compact.
* `OrientedTameStructure.orientedSheet`: the sheet `Mᵢ` of an oriented tame structure of dimension
  `m + 1` with sheets in the class, as an oriented sheet of the Stokes file (`OrientedSheet`), with
  the tangent orientation `bridgeOrientation oᵢ` of the orientation `oᵢ` of Definition 9.3.3.
* On a sheet `N` with a corner structure: `(β·ω)|_N` and `(d(β·ω))|_N` vanish off `supp β`
  (`formsInftyRestrict_smul_eq_zero`, `formsInftyRestrict_d_smul_eq_zero`), and a class whose
  restriction vanishes at `y` vanishes on the frames of `T_yN` (`epFormsInftyEval_eq_zero_of_restrict`).
* **`EP.stokes_one_structure`**: for `Φ` with the local formula of Theorem 9.5.4 or 9.5.5 (weights
  `c`), a structure `C` of the class at `x`, an sc-smooth `β` constant on the orbits with
  `supp β ⊆ U(x)^*` and `ω ∈ Ωᵐ_{ep,∞}(X)`, `m ≥ 1`:
  `Φ(d(βω))(S) = c(x) ∑ᵢ σᵢ ∫_{∂(Mᵢ,oᵢ)} βω` (the second and third equalities of the display on
  p. 451).
* `EP.stokes_off_support`: `Φ(d(βω))(S) = 0` if `supp β` does not meet `supp Θ` (the term `k = 0`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

open MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]

/-- **A sheet of the class `F.sheets` is σ-compact** (it is homeomorphic to a subset of `ℝⁿ` and
locally compact). -/
theorem FormEval.sigmaCompactSpace_of_mem_sheets {n : ℕ} {F : X.FormEval n Ω} {N : Set Obj}
    (hN : N ∈ F.sheets) : SigmaCompactSpace N := by
  have : SecondCountableTopology N :=
    (FormEval.coordHomeomorph (FormEval.chart hN)).secondCountableTopology
  have : WeaklyLocallyCompactSpace N := ⟨fun y => by
    obtain ⟨W, hW, hyW, K, hK, hNW, hKN⟩ := exists_compact_nhds_submanifold hN.1 y.2
    refine ⟨Subtype.val ⁻¹' K, ?_, ?_⟩
    · rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hKN]
      exact hK
    · exact mem_of_superset ((hW.preimage continuous_subtype_val).mem_nhds hyW)
        fun z hz => hNW ⟨z.2, hz⟩⟩
  infer_instance

/-- **The sheet `Mᵢ` of an oriented tame structure of dimension `m + 1`, as an oriented sheet**
(`MPolyfold.OrientedSheet`): the corner structure of the tame sheet (Definition 9.3.6) and the
tangent orientation given by the orientation `oᵢ` of Definition 9.3.3 (`bridgeOrientation`). -/
def OrientedTameStructure.orientedSheet {m : ℕ} {Θ : Obj → ℚ} {x : Obj}
    (C : X.OrientedTameStructure (m + 1) Θ x) (F : X.FormEval (m + 1) Ω)
    (hS : ∀ i, C.M i ∈ F.sheets) (i : C.ι) : MPolyfold.OrientedSheet X.PObj m :=
  letI := X.PObj.paracompactSpace_subtype (C.M i)
  haveI := FormEval.sigmaCompactSpace_of_mem_sheets (hS i)
  let hcs := C.toTameBranchingStructure.hasCornerStructureOfDim C.isSubmanifoldOfDim i
  letI := (subPolyfold (C.isSubmanifoldOfDim i).1.isSubMPolyfold).cornerChartedSpace hcs
  { carrier := C.M i
    isSub := (C.isSubmanifoldOfDim i).1.isSubMPolyfold
    hcs := hcs
    o := bridgeOrientation hcs (C.orient i)
    isContinuous := isContinuous_bridgeOrientation rfl (Nat.succ_pos m)
      (C.isSubmanifoldOfDim i) (C.orient i) }

@[simp] theorem OrientedTameStructure.orientedSheet_carrier {m : ℕ} {Θ : Obj → ℚ} {x : Obj}
    (C : X.OrientedTameStructure (m + 1) Θ x) (F : X.FormEval (m + 1) Ω)
    (hS : ∀ i, C.M i ∈ F.sheets) (i : C.ι) : (C.orientedSheet F hS i).carrier = C.M i := rfl

end EpGroupoid

namespace EP

variable (A : EP.{u}) {n k : ℕ} {N : Set A.Obj} [ParacompactSpace N]
  {hY : A.X.PObj.IsSubMPolyfold N} {hcs : (subPolyfold hY).HasCornerStructureOfDim n}
  [inst : ChartedSpace (EuclideanQuadrant n) N] {β : A.Obj → ℝ}

/-- **A class whose restriction to the sheet `N` vanishes at `y` vanishes on the frames of
`T_yN`.** -/
theorem epFormsInftyEval_eq_zero_of_restrict (hn : 0 < n)
    (hN : A.X.PObj.IsSubmanifoldOfDim N n) (o : A.X.PObj.SubmanifoldOrientation N n)
    (a : A.epFormsInfty n) (y : N)
    (h : formsInftyRestrict n hcs (A.epFormsInftyToObj n a) y = 0)
    {α : Fin n → A.X.PObj.TangentSpace}
    (hα : ∀ j, α j ∈ A.X.PObj.submanifoldTangent N y.1) :
    (A.epFormsInftyEval n).ev a α = 0 := by
  obtain ⟨b, hb⟩ := exists_basis_incFrame_mem_frames (hcs := hcs) hn hN o (hcs.coords y)
    (hcs.mem_coords y)
  obtain ⟨φ, hφ, hyφ⟩ := A.X.PObj.exists_isChart_mem_source y.1
  obtain ⟨M, hM⟩ := exists_matrix_of_mem_frames hN o y.2 hφ hyφ hb hα
  rw [(A.epFormsInftyEval n).ev_det a hN.1 y.2 hφ hyφ _ α
    (fun i => incFrame_mem hN.1 (hcs.coords y) (hcs.mem_coords y) (b i)) hα M hM,
    ← A.formsInftyRestrict_epFormsInftyToObj hn hN.1 a y (fun i => b i), h]
  exact mul_zero _

/-- **`(β·ω)|_N` vanishes off the support of `β`.** -/
theorem formsInftyRestrict_smul_eq_zero (hk : 0 < k) (hN : A.X.PObj.IsSmoothSubmanifold N)
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (ω : A.epFormsInfty k) (y : N)
    (hy : y.1 ∉ tsupport β) :
    formsInftyRestrict k hcs (A.epFormsInftyToObj k (A.epFormsInftySmul β k hβ hinv ω)) y =
      0 := by
  ext v
  rw [A.formsInftyRestrict_epFormsInftySmul hk hN hβ hinv ω y v,
    image_eq_zero_of_notMem_tsupport hy, zero_mul]
  rfl

/-- **`(d(β·ω))|_N` vanishes off the support of `β`** (`d` is local on the manifold `N`). -/
theorem formsInftyRestrict_d_smul_eq_zero
    (hch : inst = (subPolyfold hY).cornerChartedSpace hcs) (hk : 0 < k)
    (hN : A.X.PObj.IsSmoothSubmanifold N) (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (ω : A.epFormsInfty k) (y : N)
    (hy : y.1 ∉ tsupport β) :
    formsInftyRestrict (k + 1) hcs (A.epFormsInftyToObj (k + 1)
      (A.epFormsInftyD k (A.epFormsInftySmul β k hβ hinv ω))) y = 0 := by
  set a := A.epFormsInftySmul β k hβ hinv ω with ha
  have e : A.epFormsInftyToObj (k + 1) (A.epFormsInftyD k a) =
      A.objPolyfold.formsInftyD k (A.epFormsInftyToObj k a) :=
    (LinearMap.congr_fun (A.formsInftyD_comp_epFormsInftyToObj k) a).symm
  have e2 := extDeriv_formsInftyRestrict (hcs := hcs) hch (A.epFormsInftyToObj k a)
  rw [e]
  refine (congrFun e2.symm y).trans ?_
  refine ManifoldForm.extDeriv_eq_zero_of_eventually_eq_zero ?_
  have hopen : IsOpen {z : N | z.1 ∉ tsupport β} :=
    (isClosed_tsupport β).isOpen_compl.preimage continuous_subtype_val
  filter_upwards [hopen.mem_nhds hy] with z hz
  exact A.formsInftyRestrict_smul_eq_zero hk hN hβ hinv ω z hz

/-! ### The sheets of one structure -/

variable {m : ℕ} {Θ : A.Obj → ℚ}

/-- **The integrals of `d(β·ω)` over the subsets of a sheet disjoint from `supp β` vanish.** -/
theorem integ_d_smul_eq_zero (hm : 0 < m) {x : A.Obj}
    (C : A.X.OrientedTameStructure (m + 1) Θ x) (i : C.ι)
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (ω : A.epFormsInfty m) {B : Set A.Obj}
    (hd : Disjoint B (tsupport β)) :
    (A.epFormsInftyEval (m + 1)).integ (A.epFormsInftyD m (A.epFormsInftySmul β m hβ hinv ω))
      (C.M i) (C.orient i).tangent B = 0 := by
  let _ := A.X.PObj.paracompactSpace_subtype (C.M i)
  let hcs := C.toTameBranchingStructure.hasCornerStructureOfDim C.isSubmanifoldOfDim i
  let _ := (subPolyfold (C.isSubmanifoldOfDim i).1.isSubMPolyfold).cornerChartedSpace hcs
  refine EpGroupoid.FormEval.integ_eq_zero_of_ev_eq_zero _ _ _ fun y hy α hα => ?_
  exact A.epFormsInftyEval_eq_zero_of_restrict (hcs := hcs) (Nat.succ_pos m)
    (C.isSubmanifoldOfDim i) (C.orient i) _ ⟨y, hy.2⟩
    (A.formsInftyRestrict_d_smul_eq_zero rfl hm (C.isSubmanifoldOfDim i).1 hβ hinv ω ⟨y, hy.2⟩
      fun h => Set.disjoint_left.1 hd hy.1 h) hα

/-- **The standard Stokes theorem on one sheet, for the integral of §9.5** (the third equality of
the display on p. 451): `∫_{(Mᵢ,oᵢ)} d(βω) = ∫_{∂(Mᵢ,oᵢ)} βω` for `supp β ⊆ U(x)^*`, `Θ`
compact; the left side is the integral `FormEval.integ` of §9.5, the right side Part I's
boundary integral for the tangent orientation of `oᵢ`. -/
theorem integ_d_smul_eq_boundaryIntegral (hm : 0 < m) (hcpt : A.X.IsCompactBranched Θ)
    {x : A.Obj} (C : A.X.OrientedTameStructure (m + 1) Θ x)
    (hS : ∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets)
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ))
    (hsupp : tsupport β ⊆ A.X.π ⁻¹' (A.X.π '' C.U)) (ω : A.epFormsInfty m) (i : C.ι) :
    (A.epFormsInftyEval (m + 1)).integ (A.epFormsInftyD m (A.epFormsInftySmul β m hβ hinv ω))
        (C.M i) (C.orient i).tangent (C.M i) =
      (C.orientedSheet (A.epFormsInftyEval (m + 1)) hS i).boundaryIntegral
        (A.epFormsInftyToObj m (A.epFormsInftySmul β m hβ hinv ω)) := by
  set a := A.epFormsInftySmul β m hβ hinv ω with ha
  set Ns := C.orientedSheet (A.epFormsInftyEval (m + 1)) hS i with hNs
  have hK : IsCompact (C.M i ∩ tsupport β) :=
    C.toTameBranchingStructure.isCompact_inter hcpt (isClosed_tsupport β)
      (EpGroupoid.isSaturated_tsupport hinv) hsupp i
  let _ := A.X.PObj.paracompactSpace_subtype (C.M i)
  have := EpGroupoid.FormEval.sigmaCompactSpace_of_mem_sheets (hS i)
  let hcs := C.toTameBranchingStructure.hasCornerStructureOfDim C.isSubmanifoldOfDim i
  let _ := (subPolyfold (C.isSubmanifoldOfDim i).1.isSubMPolyfold).cornerChartedSpace hcs
  have := (subPolyfold (C.isSubmanifoldOfDim i).1.isSubMPolyfold).isManifold_cornerChartedSpace
    hcs
  have h0 : Ns.VanishesOff (tsupport β) (A.epFormsInftyToObj m a) := fun y hy =>
    A.formsInftyRestrict_smul_eq_zero (hcs := hcs) hm (C.isSubmanifoldOfDim i).1 hβ hinv ω y hy
  have hst := Ns.stokes (isClosed_tsupport β) hK (A.epFormsInftyToObj m a) h0
  have e : (BundledMPolyfold.of A.X.PObj).formsInftyD m (A.epFormsInftyToObj m a) =
      A.epFormsInftyToObj (m + 1) (A.epFormsInftyD m a) :=
    LinearMap.congr_fun (A.formsInftyD_comp_epFormsInftyToObj m) a
  rw [← hst, e]
  have hc : IsCompact (ManifoldForm.tsupport (formsInftyRestrict (m + 1) hcs
      (A.epFormsInftyToObj (m + 1) (A.epFormsInftyD m a)))) := by
    have hcl : IsClosed ((↑) ⁻¹' tsupport β : Set (C.M i)) :=
      (isClosed_tsupport β).preimage continuous_subtype_val
    have hcp : IsCompact ((↑) ⁻¹' tsupport β : Set (C.M i)) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
      exact hK
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal (fun y hy => ?_) hcl)
    by_contra hyC
    exact hy (A.formsInftyRestrict_d_smul_eq_zero rfl hm (C.isSubmanifoldOfDim i).1 hβ hinv ω y
      hyC)
  exact A.epFormsInftyEval_integ_eq_integral (hcs := hcs) rfl (Nat.succ_pos m) (hS i)
    (C.orient i) (A.epFormsInftyD m a) hc

variable (Φ : A.epFormsInfty (m + 1) →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp Θ)
    (A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ))
  (c : A.Obj → ℝ) (Good : ∀ x, A.X.OrientedTameStructure (m + 1) Θ x → Prop)

/-- **The second and third equalities of the display on p. 451** (proof of Theorem 9.5.18): let
`Φ` have the local formula of Theorem 9.5.4 or 9.5.5 with the weights `c` for a class of oriented
tame structures covering `supp Θ`, with sheets in the class of `SheetIntegrationConcrete.lean`.
For a structure `C` of the class at `x`, an sc-smooth `β` constant on the orbits with
`supp β ⊆ U(x)^*` and `ω ∈ Ωᵐ_{ep,∞}(X)`, `m ≥ 1`:
`Φ(d(βω))(S) = c(x) ∑ᵢ σᵢ ∫_{∂(Mᵢ,oᵢ)} βω`. -/
theorem stokes_one_structure (hm : 0 < m) (hcpt : A.X.IsCompactBranched Θ)
    (hGS : ∀ x C, Good x C → ∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets)
    (hcov : ∀ x ∈ EpGroupoid.supp Θ, ∃ C, Good x C)
    (hΦ : ∀ (η : A.epFormsInfty (m + 1)) (x : A.Obj)
      (C : A.X.OrientedTameStructure (m + 1) Θ x), Good x C →
      ∀ K : Set (A.X.orbitSupp Θ),
        MeasurableSet[A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        Φ η K = c x * C.sheetSum ((A.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m))
          η (A.X.π ⁻¹' (Subtype.val '' K)))
    {x : A.Obj} (C : A.X.OrientedTameStructure (m + 1) Θ x) (hC : Good x C)
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ))
    (hsupp : tsupport β ⊆ A.X.π ⁻¹' (A.X.π '' C.U)) (ω : A.epFormsInfty m) :
    Φ (A.epFormsInftyD m (A.epFormsInftySmul β m hβ hinv ω)) univ =
      c x * ∑ i, (C.σ i : ℝ) *
        (C.orientedSheet (A.epFormsInftyEval (m + 1)) (hGS x C hC) i).boundaryIntegral
          (A.epFormsInftyToObj m (A.epFormsInftySmul β m hβ hinv ω)) := by
  have h1 := EpGroupoid.measure_univ_eq_of_integ_eq_zero
    ((A.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m)) Φ c Good hcpt hGS hcov hΦ
    (A.epFormsInftyD m (A.epFormsInftySmul β m hβ hinv ω)) C hC (isClosed_tsupport β)
    (EpGroupoid.isSaturated_tsupport hinv) hsupp
    (fun x' C' _ i B _ hd => A.integ_d_smul_eq_zero hm C' i hβ hinv ω hd)
  rw [h1]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact A.integ_d_smul_eq_boundaryIntegral hm hcpt C (hGS x C hC) hβ hinv hsupp ω i

/-- **The term `k = 0` of the proof of Theorem 9.5.18** (`U_0^*` does not meet `supp Θ`): if
`supp β` does not meet `supp Θ`, then `Φ(d(βω))(S) = 0`. -/
theorem stokes_off_support (hm : 0 < m) (hcpt : A.X.IsCompactBranched Θ)
    (hcov : ∀ x ∈ EpGroupoid.supp Θ, ∃ C, Good x C)
    (hΦ : ∀ (η : A.epFormsInfty (m + 1)) (x : A.Obj)
      (C : A.X.OrientedTameStructure (m + 1) Θ x), Good x C →
      ∀ K : Set (A.X.orbitSupp Θ),
        MeasurableSet[A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        Φ η K = c x * C.sheetSum ((A.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m))
          η (A.X.π ⁻¹' (Subtype.val '' K)))
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ))
    (hd : Disjoint (tsupport β) (EpGroupoid.supp Θ)) (ω : A.epFormsInfty m) :
    Φ (A.epFormsInftyD m (A.epFormsInftySmul β m hβ hinv ω)) univ = 0 :=
  EpGroupoid.measure_eq_zero_of_integ_eq_zero
    ((A.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m)) Φ c Good hcpt hcov hΦ _
    (@MeasurableSet.univ _ (A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ))
    fun _ C _ i _ hB => A.integ_d_smul_eq_zero hm C i hβ hinv ω
      (Set.disjoint_left.2 fun _ hy hyβ => Set.disjoint_left.1 hd hyβ
        (C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i (hB hy).1))

end EP

end Polyfold
