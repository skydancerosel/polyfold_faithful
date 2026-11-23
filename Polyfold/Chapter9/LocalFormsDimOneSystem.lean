import Polyfold.Chapter9.LocalFormsDimOneSub
import Polyfold.Chapter9.LocalFormsSystem
import Polyfold.Chapter9.LocalFormSystemDimOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, proof of **Theorem 9.5.18, 2021 pp. 450–451**, and
**Remark 9.5.19, p. 451** (2017: Theorem 9.7, Remark 9.8), point G.153, the case `n = 1`.
Numbers and pages are the 2021 text's.

# The pieces `β_k ω` for a partition of unity near `supp Θ`, `n = 1`

From a partition of unity `(W, β_k, χ)` near `supp Θ` (`EP.LocalPartition`) the pieces of the
proof of Theorem 9.5.18 for a function `ω` are built (`EP.LocalFormSystemDimOne`): the `1`-forms
are the classes of `Ω¹_{ep,∞}(X|W)` with the values `χ · a` on the tangent vectors of `X`
(`EP.subEval`), the functions are the classes of `Ω⁰_{ep,∞}(X|W)` with the values `χ · b` at the
objects of `X` (`EP.subVal0`); `u_k = β_k·(ω|W)`, `v_k = d(β_k·(ω|W))`, and
`Z_k = cl(W ∩ {β_k ≠ 0}) ∩ supp χ`.

* `EP.LocalPartition.localFormSystemDimOne`: the system, for `W ≠ ∅`.
* **`EP.LocalPartition.nonempty_localFormSystemDimOne`**: every partition of unity near `supp Θ`
  has a system of pieces for `n = 1`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EP

open MPolyfold EpGroupoid

namespace LocalPartition

variable {A : EP.{u}} {Θ : A.Obj → ℚ} {N : A.Obj → Set A.Obj} (L : A.LocalPartition Θ N)

/-- **The pieces `β_k ω`, `d(β_k ω)` for a partition of unity near `supp Θ`, `n = 1`** (Remark
9.5.19, 2021 p. 451; proof of Theorem 9.5.18, pp. 450–451), for `W ≠ ∅`: functions and `1`-forms
on `X|W`, with the values `χ · b` at the objects and `χ · a` on the tangent vectors of `X`. -/
def localFormSystemDimOne (ω : A.epFormsInfty 0)
    (w₀ : (A.sub L.isEpSubgroupoid_W).Obj) : A.LocalFormSystemDimOne Θ N ω where
  Ω1 := (A.sub L.isEpSubgroupoid_W).epFormsInfty (0 + 1)
  Ω0 := (A.sub L.isEpSubgroupoid_W).epFormsInfty 0
  F1 := A.subEval L.isEpSubgroupoid_W L.isOpen_W w₀ (Nat.succ_pos 0) L.continuous_χ
    L.tsupport_χ_subset L.χ_src_eq_tgt
  val0 := A.subVal0 L.isEpSubgroupoid_W w₀ L.tsupport_χ_subset L.χ_src_eq_tgt
  j1 := epFormsInftyPullback (A.subFunctor L.isEpSubgroupoid_W) (0 + 1)
  j0 := epFormsInftyPullback (A.subFunctor L.isEpSubgroupoid_W) 0
  j1_ev η _ hM _ hy hyΘ α hα :=
    A.subEval_pullback L.isEpSubgroupoid_W L.isOpen_W w₀ (Nat.succ_pos 0) L.continuous_χ
      L.tsupport_χ_subset L.χ_src_eq_tgt η hM hy (L.χ_eq_one hyΘ) α hα
  j0_val η _ hyΘ :=
    A.subVal_pullback L.isEpSubgroupoid_W w₀ L.isOpen_W η (L.supp_subset_W hyΘ)
      (L.χ_eq_one hyΘ)
  κ := L.κ
  pt := L.pt
  pt_mem := L.pt_mem
  Z := L.Z
  isClosed_Z := L.isClosed_Z
  isSaturated_Z := L.isSaturated_Z
  Z_subset := L.Z_subset
  u k := A.subSmul L.isEpSubgroupoid_W (L.isScSmoothOn_β k) (L.β_src_eq_tgt k) 0 ω
  v k := (A.sub L.isEpSubgroupoid_W).epFormsInftyD 0
    (A.subSmul L.isEpSubgroupoid_W (L.isScSmoothOn_β k) (L.β_src_eq_tgt k) 0 ω)
  sum_u :=
    (A.sub L.isEpSubgroupoid_W).sum_epFormsInftySmul 0 Finset.univ
      (fun k => A.subFun L.isEpSubgroupoid_W (L.β k))
      (fun k => A.isScSmoothMap_subFun L.isEpSubgroupoid_W (L.isScSmoothOn_β k))
      (fun k => A.subFun_src_eq_tgt L.isEpSubgroupoid_W (L.β_src_eq_tgt k))
      (fun w => L.sum_β _ (A.subFunctor_obj_mem L.isEpSubgroupoid_W w)) _
  sum_v := by
    rw [← map_sum]
    have h := (A.sub L.isEpSubgroupoid_W).sum_epFormsInftySmul 0 Finset.univ
      (fun k => A.subFun L.isEpSubgroupoid_W (L.β k))
      (fun k => A.isScSmoothMap_subFun L.isEpSubgroupoid_W (L.isScSmoothOn_β k))
      (fun k => A.subFun_src_eq_tgt L.isEpSubgroupoid_W (L.β_src_eq_tgt k))
      (fun w => L.sum_β _ (A.subFunctor_obj_mem L.isEpSubgroupoid_W w))
      (epFormsInftyPullback (A.subFunctor L.isEpSubgroupoid_W) 0 ω)
    have h' : ∑ k, A.subSmul L.isEpSubgroupoid_W (L.isScSmoothOn_β k) (L.β_src_eq_tgt k) 0 ω =
        epFormsInftyPullback (A.subFunctor L.isEpSubgroupoid_W) 0 ω := h
    rw [h']
    exact LinearMap.congr_fun
      (epFormsInftyD_comp_epFormsInftyPullback (A.subFunctor L.isEpSubgroupoid_W) 0) ω
  integ_v_eq_zero k _ C i _ B hB hd :=
    FormEval.integ_eq_zero_of_ev_eq_zero _ _ _ fun y hy α hα =>
      A.subEval_d_subSmul_eq_zero L.isEpSubgroupoid_W (L.isScSmoothOn_β k) (L.β_src_eq_tgt k)
        L.isOpen_W w₀ L.continuous_χ L.tsupport_χ_subset L.χ_src_eq_tgt
        (C.isSubmanifoldOfDim i) (C.hasTameInducedStructure i) (C.orient i)
        ((C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i).trans
          L.supp_subset_W) ω hy.2
        (L.notMem_closure_of_notMem_Z
          (C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i hy.2)
          (disjoint_left.1 hd hy.1)) hα
  val_u_eq_zero k _ hyΘ hyZ :=
    A.subVal_subSmul_eq_zero L.isEpSubgroupoid_W w₀ L.tsupport_χ_subset (L.isScSmoothOn_β k)
      (L.β_src_eq_tgt k) ω (L.β_eq_zero_of_notMem_Z hyΘ hyZ)
  stokes_sheet k _ C i hMs hs hK := by
    have hMΘ := C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i
    have hK' : IsCompact (C.M i ∩ closure (L.W ∩ {z | L.β k z ≠ 0})) := by
      have e : C.M i ∩ closure (L.W ∩ {z | L.β k z ≠ 0}) = C.M i ∩ L.Z k := by
        ext y
        exact ⟨fun h => ⟨h.1, h.2, L.supp_subset_tsupport_χ (hMΘ h.1)⟩, fun h => ⟨h.1, h.2.1⟩⟩
      rw [e]; exact hK
    exact A.subEval_stokes_sheet_dim1 L.isEpSubgroupoid_W w₀ L.tsupport_χ_subset L.χ_src_eq_tgt
      L.isOpen_W (L.isScSmoothOn_β k) (L.β_src_eq_tgt k) L.continuous_χ
      (C.isSubmanifoldOfDim i) (C.hasTameInducedStructure i) (C.orient i)
      (hMΘ.trans L.supp_subset_W) (fun y hy => L.χ_eq_one (hMΘ hy)) hMs hs hK' ω

/-- **Every partition of unity near `supp Θ` has a system of pieces `β_k ω`, `d(β_k ω)` for
`n = 1`** (Remark 9.5.19, 2021 p. 451; proof of Theorem 9.5.18, pp. 450–451).  No hypothesis on
`Θ` is used. -/
theorem nonempty_localFormSystemDimOne (L : A.LocalPartition Θ N) (ω : A.epFormsInfty 0) :
    Nonempty (A.LocalFormSystemDimOne Θ N ω) := by
  rcases isEmpty_or_nonempty (A.sub L.isEpSubgroupoid_W).Obj with he | ⟨⟨w₀⟩⟩
  · have hno : ∀ y, y ∉ supp Θ := fun y hy =>
      he.false (show (A.sub L.isEpSubgroupoid_W).Obj from (⟨y, L.supp_subset_W hy⟩ : L.W))
    exact ⟨
      { Ω1 := A.epFormsInfty (0 + 1)
        Ω0 := A.epFormsInfty 0
        F1 := A.epFormsInftyEval (0 + 1)
        val0 := A.zeroFormEvalInv
        j1 := 0
        j0 := 0
        j1_ev := fun _ _ _ _ _ hy => (hno _ hy).elim
        j0_val := fun _ _ hy => (hno _ hy).elim
        κ := L.κ
        pt := L.pt
        pt_mem := L.pt_mem
        Z := fun _ => ∅
        isClosed_Z := fun _ => isClosed_empty
        isSaturated_Z := fun k => (hno _ (L.pt_mem k)).elim
        Z_subset := fun _ => empty_subset _
        u := fun _ => 0
        v := fun _ => 0
        sum_u := by simp
        sum_v := by simp
        integ_v_eq_zero := fun k => (hno _ (L.pt_mem k)).elim
        val_u_eq_zero := fun k => (hno _ (L.pt_mem k)).elim
        stokes_sheet := fun k => (hno _ (L.pt_mem k)).elim }⟩
  · exact ⟨L.localFormSystemDimOne ω w₀⟩

end LocalPartition

end EP

end Polyfold
