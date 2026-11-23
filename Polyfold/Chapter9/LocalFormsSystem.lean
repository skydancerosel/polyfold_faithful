import Polyfold.Chapter9.LocalFormsStokes
import Polyfold.Chapter9.LocalFormSystem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, proof of **Theorem 9.5.18, 2021 pp. 450–451**, and
**Remark 9.5.19, p. 451** (2017: Theorem 9.7, Remark 9.8), point G.153.  Numbers and pages are
the 2021 text's.

# The pieces `β_k ω` for a partition of unity near `supp Θ`

From a partition of unity `(W, β_k, χ)` near `supp Θ` (`EP.LocalPartition`) the pieces of the
proof of Theorem 9.5.18 are built (`EP.LocalFormSystem`): the forms are the classes of
`Ω_{ep,∞}(X|W)`, with the values `χ · a` on the tangent vectors of `X` (`EP.subEval`); the class
of a form of `X` is its restriction to `W`; `u_k = β_k·(ω|W)`, `v_k = d(β_k·(ω|W))`, and
`Z_k = cl(W ∩ {β_k ≠ 0}) ∩ supp χ`.

* `EP.LocalPartition.Z`, `isClosed_Z`, `isSaturated_Z`, `Z_subset`.
* `EP.LocalPartition.localFormSystem`: the system, for `W ≠ ∅`.
* **`EP.LocalPartition.nonempty_localFormSystem`**: every partition of unity near `supp Θ` has a
  system of pieces (`m ≥ 1`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- The closure of a saturated set is saturated (`π` is open, Proposition 7.1.8). -/
theorem isSaturated_closure_of_isSaturated {S : Set Obj} (hS : X.IsSaturated S) :
    X.IsSaturated (closure S) := by
  have e : closure S = X.π ⁻¹' closure (X.π '' S) := by
    rw [X.proposition_7_1_8.preimage_closure_eq_closure_preimage X.continuous_π]
    exact congrArg closure hS.symm
  refine X.isSaturated_iff.2 fun φ hφ => ?_
  rw [e] at hφ ⊢
  rw [mem_preimage, ← X.π_src_eq_π_tgt φ]
  exact hφ

end EpGroupoid

namespace EP

open MPolyfold EpGroupoid

namespace LocalPartition

variable {A : EP.{u}} {Θ : A.Obj → ℚ} {N : A.Obj → Set A.Obj} (L : A.LocalPartition Θ N)

theorem isEpSubgroupoid_W : A.X.IsEpSubgroupoid L.W :=
  A.X.isEpSubgroupoid_of_isOpen L.isOpen_W L.isSaturated_W

theorem χ_eq_one {y : A.Obj} (hy : y ∈ supp Θ) : L.χ y = 1 :=
  (L.χ_eventually_eq_one y hy).self_of_nhds

theorem supp_subset_tsupport_χ : supp Θ ⊆ tsupport L.χ := fun y hy =>
  subset_tsupport _ (by change L.χ y ≠ 0; rw [L.χ_eq_one hy]; exact one_ne_zero)

/-- The closed saturated set `Z_k = cl(W ∩ {β_k ≠ 0}) ∩ supp χ`. -/
def Z (k : L.κ) : Set A.Obj := closure (L.W ∩ {y | L.β k y ≠ 0}) ∩ tsupport L.χ

theorem isClosed_Z (k : L.κ) : IsClosed (L.Z k) := isClosed_closure.inter (isClosed_tsupport _)

theorem isSaturated_Z (k : L.κ) : A.X.IsSaturated (L.Z k) := by
  have h1 : A.X.IsSaturated (L.W ∩ {y | L.β k y ≠ 0}) := A.X.isSaturated_iff.2 fun φ hφ =>
    ⟨A.X.isSaturated_iff.1 L.isSaturated_W φ hφ.1, by
      have h2 : L.β k (A.X.src φ) ≠ 0 := hφ.2
      rw [L.β_src_eq_tgt k φ hφ.1] at h2
      exact h2⟩
  have h2 := isSaturated_closure_of_isSaturated h1
  have h3 := EpGroupoid.isSaturated_tsupport (X := A.X) L.χ_src_eq_tgt
  exact A.X.isSaturated_iff.2 fun φ hφ =>
    ⟨A.X.isSaturated_iff.1 h2 φ hφ.1, A.X.isSaturated_iff.1 h3 φ hφ.2⟩

theorem Z_subset (k : L.κ) : L.Z k ⊆ A.X.π ⁻¹' (A.X.π '' N (L.pt k)) := fun _ hy =>
  L.closure_subset k ⟨L.tsupport_χ_subset hy.2, hy.1⟩

theorem notMem_closure_of_notMem_Z {k : L.κ} {y : A.Obj} (hy : y ∈ supp Θ) (h : y ∉ L.Z k) :
    y ∉ closure (L.W ∩ {y | L.β k y ≠ 0}) := fun hc => h ⟨hc, L.supp_subset_tsupport_χ hy⟩

theorem β_eq_zero_of_notMem_Z {k : L.κ} {y : A.Obj} (hy : y ∈ supp Θ) (h : y ∉ L.Z k) :
    L.β k y = 0 := by
  by_contra hne
  exact L.notMem_closure_of_notMem_Z hy h (subset_closure ⟨L.supp_subset_W hy, hne⟩)

variable {m : ℕ}

/-- **The pieces `β_k ω`, `d(β_k ω)` for a partition of unity near `supp Θ`** (Remark 9.5.19,
2021 p. 451; proof of Theorem 9.5.18, pp. 450–451), for `W ≠ ∅`: forms on `X|W`, with the values
`χ · a` on the tangent vectors of `X`. -/
def localFormSystem (hm : 0 < m) (ω : A.epFormsInfty m)
    (w₀ : (A.sub L.isEpSubgroupoid_W).Obj) : A.LocalFormSystem m Θ N ω where
  Ω1 := (A.sub L.isEpSubgroupoid_W).epFormsInfty (m + 1)
  Ω0 := (A.sub L.isEpSubgroupoid_W).epFormsInfty m
  F1 := A.subEval L.isEpSubgroupoid_W L.isOpen_W w₀ (Nat.succ_pos m) L.continuous_χ
    L.tsupport_χ_subset L.χ_src_eq_tgt
  G0 := A.subEval L.isEpSubgroupoid_W L.isOpen_W w₀ hm L.continuous_χ
    L.tsupport_χ_subset L.χ_src_eq_tgt
  j1 := epFormsInftyPullback (A.subFunctor L.isEpSubgroupoid_W) (m + 1)
  j0 := epFormsInftyPullback (A.subFunctor L.isEpSubgroupoid_W) m
  j1_ev η _ hM _ hy hyΘ α hα :=
    A.subEval_pullback L.isEpSubgroupoid_W L.isOpen_W w₀ (Nat.succ_pos m) L.continuous_χ
      L.tsupport_χ_subset L.χ_src_eq_tgt η hM hy (L.χ_eq_one hyΘ) α hα
  j0_ev η _ hM _ hy hyΘ α hα :=
    A.subEval_pullback L.isEpSubgroupoid_W L.isOpen_W w₀ hm L.continuous_χ
      L.tsupport_χ_subset L.χ_src_eq_tgt η hM hy (L.χ_eq_one hyΘ) α hα
  boundaryStratum_mem hM ht hMΘ _ hV _ hK hKM hNK hne :=
    A.subEval_boundaryStratum_inter_mem_msheets L.isEpSubgroupoid_W L.isOpen_W w₀
      L.continuous_χ L.tsupport_χ_subset L.χ_src_eq_tgt hm hM ht (hMΘ.trans L.supp_subset_W)
      (fun y hy => L.χ_eq_one (hMΘ hy)) hV hK hKM hNK hne
  κ := L.κ
  pt := L.pt
  pt_mem := L.pt_mem
  Z := L.Z
  isClosed_Z := L.isClosed_Z
  isSaturated_Z := L.isSaturated_Z
  Z_subset := L.Z_subset
  u k := A.subSmul L.isEpSubgroupoid_W (L.isScSmoothOn_β k) (L.β_src_eq_tgt k) m ω
  v k := (A.sub L.isEpSubgroupoid_W).epFormsInftyD m
    (A.subSmul L.isEpSubgroupoid_W (L.isScSmoothOn_β k) (L.β_src_eq_tgt k) m ω)
  sum_u :=
    (A.sub L.isEpSubgroupoid_W).sum_epFormsInftySmul m Finset.univ
      (fun k => A.subFun L.isEpSubgroupoid_W (L.β k))
      (fun k => A.isScSmoothMap_subFun L.isEpSubgroupoid_W (L.isScSmoothOn_β k))
      (fun k => A.subFun_src_eq_tgt L.isEpSubgroupoid_W (L.β_src_eq_tgt k))
      (fun w => L.sum_β _ (A.subFunctor_obj_mem L.isEpSubgroupoid_W w)) _
  sum_v := by
    rw [← map_sum]
    have h := (A.sub L.isEpSubgroupoid_W).sum_epFormsInftySmul m Finset.univ
      (fun k => A.subFun L.isEpSubgroupoid_W (L.β k))
      (fun k => A.isScSmoothMap_subFun L.isEpSubgroupoid_W (L.isScSmoothOn_β k))
      (fun k => A.subFun_src_eq_tgt L.isEpSubgroupoid_W (L.β_src_eq_tgt k))
      (fun w => L.sum_β _ (A.subFunctor_obj_mem L.isEpSubgroupoid_W w))
      (epFormsInftyPullback (A.subFunctor L.isEpSubgroupoid_W) m ω)
    have h' : ∑ k, A.subSmul L.isEpSubgroupoid_W (L.isScSmoothOn_β k) (L.β_src_eq_tgt k) m ω =
        epFormsInftyPullback (A.subFunctor L.isEpSubgroupoid_W) m ω := h
    rw [h']
    exact LinearMap.congr_fun
      (epFormsInftyD_comp_epFormsInftyPullback (A.subFunctor L.isEpSubgroupoid_W) m) ω
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
  msInteg_u_eq_zero k _ C i B hB hd :=
    FormEval.msInteg_eq_zero_of_ev_eq_zero _ _ _ _ fun y hy N' hN' hyN' α hα =>
      A.subEval_subSmul_eq_zero L.isEpSubgroupoid_W (L.isScSmoothOn_β k) (L.β_src_eq_tgt k)
        L.isOpen_W w₀ L.continuous_χ L.tsupport_χ_subset L.χ_src_eq_tgt hm ω hN' hyN'
        (L.β_eq_zero_of_notMem_Z
          (C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i
            (C.boundarySheet_subset i hy.2))
          (disjoint_left.1 hd hy.1)) hα
  stokes_sheet k _ C i hMs hb hK := by
    have hMΘ := C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i
    have hK' : IsCompact (C.M i ∩ closure (L.W ∩ {z | L.β k z ≠ 0})) := by
      have e : C.M i ∩ closure (L.W ∩ {z | L.β k z ≠ 0}) = C.M i ∩ L.Z k := by
        ext y
        exact ⟨fun h => ⟨h.1, h.2, L.supp_subset_tsupport_χ (hMΘ h.1)⟩, fun h => ⟨h.1, h.2.1⟩⟩
      rw [e]; exact hK
    exact A.subEval_stokes_sheet L.isEpSubgroupoid_W (L.isScSmoothOn_β k) (L.β_src_eq_tgt k)
      L.isOpen_W w₀ L.continuous_χ L.tsupport_χ_subset L.χ_src_eq_tgt hm
      (C.isSubmanifoldOfDim i) (C.hasTameInducedStructure i) (C.orient i)
      (hMΘ.trans L.supp_subset_W) (fun y hy => L.χ_eq_one (hMΘ hy)) hMs hb hK' ω

/-- **Every partition of unity near `supp Θ` has a system of pieces `β_k ω`, `d(β_k ω)`**
(Remark 9.5.19, 2021 p. 451; proof of Theorem 9.5.18, pp. 450–451), `m ≥ 1`.  No hypothesis on
`Θ` is used. -/
theorem nonempty_localFormSystem_of_pos (L : A.LocalPartition Θ N) (hm : 0 < m)
    (ω : A.epFormsInfty m) :
    Nonempty (A.LocalFormSystem m Θ N ω) := by
  rcases isEmpty_or_nonempty (A.sub L.isEpSubgroupoid_W).Obj with he | ⟨⟨w₀⟩⟩
  · have hno : ∀ y, y ∉ supp Θ := fun y hy =>
      he.false (show (A.sub L.isEpSubgroupoid_W).Obj from (⟨y, L.supp_subset_W hy⟩ : L.W))
    exact ⟨
      { Ω1 := A.epFormsInfty (m + 1)
        Ω0 := A.epFormsInfty m
        F1 := A.epFormsInftyEval (m + 1)
        G0 := A.epFormsInftyEval m
        j1 := 0
        j0 := 0
        j1_ev := fun _ _ _ _ _ hy => (hno _ hy).elim
        j0_ev := fun _ _ _ _ _ hy => (hno _ hy).elim
        boundaryStratum_mem := fun _ _ hMΘ _ _ _ _ _ _ hne =>
          (hno _ (hMΘ hne.choose_spec.1.1)).elim
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
        msInteg_u_eq_zero := fun k => (hno _ (L.pt_mem k)).elim
        stokes_sheet := fun k => (hno _ (L.pt_mem k)).elim }⟩
  · exact ⟨L.localFormSystem hm ω w₀⟩

/-- **Every partition of unity near the support of a compact branched ep⁺-subgroupoid `Θ` has a
system of pieces `β_k ω`, `d(β_k ω)`** (Remark 9.5.19, 2021 p. 451), `m ≥ 1`. -/
theorem nonempty_localFormSystem (hm : 0 < m) (L : A.LocalPartition Θ N)
    (_hΘ : A.X.IsBranchedEpSubgroupoid Θ) (_hcpt : A.X.IsCompactBranched Θ)
    (ω : A.epFormsInfty m) : Nonempty (A.LocalFormSystem m Θ N ω) :=
  L.nonempty_localFormSystem_of_pos hm ω

end LocalPartition

end EP

end Polyfold
