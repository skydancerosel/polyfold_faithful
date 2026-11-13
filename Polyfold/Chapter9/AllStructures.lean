import Polyfold.Chapter9.StokesTextHypotheses
import Polyfold.Chapter9.SheetEssential
import Polyfold.Chapter9.PropertyTShrinking2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §9.5, Theorems 9.5.15 and 9.5.16 (p. 449; gap G.109; row V9.67).  Numbers and pages are
the 2021 text's.

# The local formula of Theorems 9.5.15, 9.5.16 for every oriented tame structure

`StokesTextHypotheses` proves Theorems 9.5.15 and 9.5.16 with the local formula for the structures
whose nonempty boundary sheets lie in the class `msheets`.  Here every oriented tame structure is
shown to have that property, so the local formula holds for every oriented tame structure
describing `T̂Θ`, as the text states it.

The argument: `∂₁Mᵢ` lies in a compact subset `K` of `supp Θ` (properness of `U(x)`).  Cover `K`
by finitely many structures `C'` whose nonempty boundary sheets lie in `msheets`
(`EP.hcovS_of_loc`).  At `z ∈ ∂₁Mᵢ ∩ U(y)'`, some sheet `M'_k ∋ z` has `T_zM'_k = T_zMᵢ`:
otherwise, near `z`, every point of `Mᵢ` (which lies in `⋃ M'_k`) would be a point of some
`Mᵢ ∩ M'_k` where the relative tangent space is not full, a set of `(m+1)`-dimensional measure
zero (Lemma 9.4.6's proof), while an open piece of `Mᵢ` is not.  The boundary stratum depends
only on the tangent space, so `z ∈ ∂₁M'_k`.  Hence `∂₁Mᵢ` lies in finitely many sheets of
`msheets`, and a submanifold dominated by finitely many sheets of `msheets` is in `msheets`.

* `MPolyfold.k1_exists_tangent_eq`, `MPolyfold.k1_mem_boundaryStratum_of_tangent_eq`;
* `EpGroupoid.FormEval.k1_msheets_of_subset_list`;
* **`EP.boundarySheet_mem_msheets_of_loc`**: every nonempty boundary sheet of every oriented tame
  structure lies in `msheets`;
* **`EP.theorem_9_5_15`**, **`EP.theorem_9_5_16`**: the theorems with the local formula for every
  oriented tame structure.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **A sheet with a common tangent space**: let `M` and `M'_k` (finitely many) be
`n`-dimensional submanifolds with `M ∩ W ⊆ ⋃ M'_k` (`W` open), each `M'_k` closed in `W`.  Then at
every `z ∈ M ∩ W` some `M'_k ∋ z` has `T_zM'_k = T_zM`. -/
theorem k1_exists_tangent_eq {n : ℕ} {ι : Type*} [Finite ι] {M : Set X} {M' : ι → Set X}
    (hM : P.IsSubmanifoldOfDim M n) (hM' : ∀ k, P.IsSubmanifoldOfDim (M' k) n) {W : Set X}
    (hW : IsOpen W) (hcov : M ∩ W ⊆ ⋃ k, M' k)
    (hcl : ∀ k, ∀ z ∈ W, z ∉ M' k → ∃ O : Set X, IsOpen O ∧ z ∈ O ∧ Disjoint O (M' k))
    {z : X} (hz : z ∈ M) (hzW : z ∈ W) :
    ∃ k, z ∈ M' k ∧ P.submanifoldTangent M z = P.submanifoldTangent (M' k) z := by
  by_contra hne
  push Not at hne
  have hO : ∀ k, ∃ O : Set X, IsOpen O ∧ z ∈ O ∧ ∀ p ∈ M ∩ M' k ∩ O,
      P.submanifoldTangent M p ≠ P.submanifoldTangent (M' k) p := by
    intro k
    by_cases hzk : z ∈ M' k
    · exact exists_isOpen_submanifoldTangent_ne hM (hM' k) hz hzk (hne k hzk)
    · obtain ⟨O, hO, hzO, hd⟩ := hcl k z hzW hzk
      exact ⟨O, hO, hzO, fun p hp => absurd hp.1.2 (Set.disjoint_left.1 hd hp.2)⟩
  choose O hOo hzO hOne using hO
  have hO'o : IsOpen (W ∩ ⋂ k, O k) := hW.inter (isOpen_iInter_of_finite hOo)
  have hnull : P.IsHNull n (M ∩ (W ∩ ⋂ k, O k)) := by
    refine (isHNull_iUnion fun k =>
      isHNull_setOf_not_isRelTangentFull hM (inter_subset_left : M ∩ M' k ⊆ M)).mono ?_
    rintro p ⟨hpM, hpW, hpO⟩
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov ⟨hpM, hpW⟩)
    refine mem_iUnion.2 ⟨k, ⟨hpM, hk⟩, fun hfull => hOne k p ⟨⟨hpM, hk⟩, mem_iInter.1 hpO k⟩ ?_⟩
    exact submanifoldTangent_eq_of_isRelTangentFull hM (hM' k) ⟨hpM, hk⟩ hfull
  have hMO := hM.inter_isOpen hO'o
  exact not_isHNull_of_hasDimAt hMO.1 (hMO.2 z ⟨hz, hzW, mem_iInter.2 hzO⟩) hnull

/-- The boundary stratum `{d = 1}` depends only on the tangent space: a point of `∂₁A` lying in
`B` with `T_zB = T_zA` lies in `∂₁B`. -/
theorem k1_mem_boundaryStratum_of_tangent_eq {A B : Set X} {z : X}
    (h : z ∈ P.boundaryStratum A) (hzB : z ∈ B)
    (hT : P.submanifoldTangent A z = P.submanifoldTangent B z) : z ∈ P.boundaryStratum B :=
  ⟨hzB, fun c => hT ▸ h.2 c⟩

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

namespace FormEval

variable {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {F : X.FormEval n Ω}

/-- **A submanifold covered by finitely many sheets of `F.msheets` is in `F.msheets`**: the
pieces `N_l ∩ V_{l,k}` of their chart covers, enumerated by `m = k q + l`, dominate it. -/
theorem k1_msheets_of_subset_list {N : Set Obj} (hN : X.PObj.IsSubmanifoldOfDim N n)
    (hne : N.Nonempty) {L : List (Set Obj)} (hL : ∀ s ∈ L, s ∈ F.msheets)
    (hcov : N ⊆ ⋃ s ∈ L, s) : N ∈ F.msheets := by
  classical
  have hL0 : 0 < L.length := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨s, hs, -⟩ := mem_iUnion₂.1 (hcov hy)
    exact List.length_pos_of_mem hs
  have hD : ∀ l : Fin L.length, ∃ D : F.ChartCover (L.get l), D.IsFinite :=
    fun l => (hL _ (List.get_mem L l)).2
  choose D hDf using hD
  let lf : ℕ → Fin L.length := fun m => ⟨m % L.length, Nat.mod_lt _ hL0⟩
  let S : ℕ → Set Obj := fun m => L.get (lf m) ∩ (D (lf m)).V (m / L.length)
  have hS : ∀ m, S m ∈ F.sheets := fun m => (D (lf m)).mem (m / L.length)
  have hlf : ∀ (k : ℕ) (l : Fin L.length), lf (k * L.length + l) = l := fun k l => Fin.ext (by
    change (k * L.length + l) % L.length = l
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt l.2])
  have hdiv : ∀ (k : ℕ) (l : Fin L.length), (k * L.length + l) / L.length = k := fun k l => by
    rw [Nat.mul_comm, Nat.mul_add_div hL0, Nat.div_eq_of_lt l.2, add_zero]
  have hmem : ∀ (k : ℕ) (l : Fin L.length) {y : Obj}, y ∈ L.get l → y ∈ (D l).V k →
      y ∈ S (k * L.length + l) := fun k l y h1 h2 => by
    change y ∈ L.get (lf (k * L.length + l)) ∩
      (D (lf (k * L.length + l))).V ((k * L.length + l) / L.length)
    rw [hlf, hdiv]
    exact ⟨h1, h2⟩
  have hcov' : N ⊆ ⋃ m, S m := by
    intro y hy
    obtain ⟨s, hs, hys⟩ := mem_iUnion₂.1 (hcov hy)
    obtain ⟨l, rfl⟩ := List.mem_iff_get.1 hs
    obtain ⟨k, hk⟩ := mem_iUnion.1 ((D l).cover hys)
    exact mem_iUnion.2 ⟨k * L.length + l, hmem k l hys hk⟩
  have hm_eq : ∀ m, m = m / L.length * L.length + (lf m : ℕ) := fun m => by
    change m = m / L.length * L.length + m % L.length
    rw [Nat.mul_comm]; exact (Nat.div_add_mod m L.length).symm
  refine msheets_of_dominated hN hne hS hcov' fun ω => ?_
  have hle : ∀ m, F.chartAbs (chart (hS m)) ω (disjointed S m) ≤
      F.chartAbs (chart (hS m)) ω ((D (lf m)).P (m / L.length)) := fun m => by
    refine F.chartAbs_mono _ ω (integrableOn_chart (hS m) ω) fun y hy => ?_
    have hyd := hy.1
    rw [disjointed_eq_inter_compl] at hyd
    refine ⟨hy.2.1, hy.2.2, fun j hj hyj => ?_⟩
    have hlt : j * L.length + (lf m : ℕ) < m := by
      conv_rhs => rw [hm_eq m]
      have : j * L.length < m / L.length * L.length := Nat.mul_lt_mul_of_pos_right hj hL0
      omega
    exact mem_iInter₂.1 hyd.2 _ hlt (hmem j (lf m) hy.2.1 hyj)
  have hg : Summable fun p : Fin L.length × ℕ =>
      F.chartAbs (chart ((D p.1).mem p.2)) ω ((D p.1).P p.2) :=
    (summable_prod_of_nonneg fun p => F.chartAbs_nonneg _ ω _).2
      ⟨fun l => hDf l ω, Summable.of_finite⟩
  have hinj : Injective fun m => (lf m, m / L.length) := fun m m' h => by
    simp only [Prod.mk.injEq] at h
    rw [hm_eq m, hm_eq m', h.1, h.2]
  let g : Fin L.length × ℕ → ℝ := fun p =>
    F.chartAbs (chart ((D p.1).mem p.2)) ω ((D p.1).P p.2)
  have hg' : Summable (g ∘ fun m => (lf m, m / L.length)) := hg.comp_injective hinj
  have key : ∀ m, F.chartAbs (chart (hS m)) ω ((D (lf m)).P (m / L.length)) =
      (g ∘ fun m => (lf m, m / L.length)) m := fun m => rfl
  exact Summable.of_nonneg_of_le (fun m => F.chartAbs_nonneg _ ω _)
    (fun m => (hle m).trans_eq (key m)) hg'

end FormEval

/-- A point of `U(x)` outside `Mᵢ` has an open neighbourhood disjoint from `Mᵢ` (`Mᵢ` is closed
in `U(x)`). -/
theorem LocalBranchingStructure.k1_exists_isOpen_disjoint {Θ : Obj → ℚ} {x : Obj}
    (B : X.LocalBranchingStructure Θ x) (i : B.ι) {z : Obj} (hzU : z ∈ B.U) (hzM : z ∉ B.M i) :
    ∃ O : Set Obj, IsOpen O ∧ z ∈ O ∧ Disjoint O (B.M i) := by
  have hcl : IsClosed (range (Set.inclusion (B.subset_U i))) :=
    (B.isProperMap i).isClosedMap.isClosed_range
  obtain ⟨F, hF, hFeq⟩ := isClosed_induced_iff.1 hcl
  have hzF : z ∉ F := fun hzF => by
    have h : (⟨z, hzU⟩ : B.U) ∈ Subtype.val ⁻¹' F := hzF
    rw [hFeq] at h
    obtain ⟨⟨w, hw⟩, hwz⟩ := h
    have hwz' : w = z := congrArg Subtype.val hwz
    exact hzM (hwz' ▸ hw)
  refine ⟨B.U ∩ Fᶜ, B.isOpen_U.inter hF.isOpen_compl, ⟨hzU, hzF⟩,
    Set.disjoint_left.2 fun y hy hyM => hy.2 ?_⟩
  have h : (⟨y, hy.1⟩ : B.U) ∈ range (Set.inclusion (B.subset_U i)) := ⟨⟨y, hyM⟩, rfl⟩
  rw [← hFeq] at h
  exact h

end EpGroupoid

namespace EP

open EpGroupoid

variable (A : EP.{u}) {m : ℕ} {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- **Every nonempty boundary sheet of every oriented tame structure lies in `msheets`**, for `Θ`
compact, branched, tame (`hloc`), of dimension `m + 1`, `m ≥ 1`. -/
theorem boundarySheet_mem_msheets_of_loc (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    {x : A.Obj} (C : A.X.OrientedTameStructure (m + 1) Θ x) (i : C.ι)
    (hne : (C.boundarySheet i).Nonempty) : C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets := by
  classical
  have hnd := FormEval.isNDimensional_of_loc hloc
  obtain ⟨K, hK, hUK, hKs⟩ :=
    exists_isCompact_supp_inter hΘ.isFunctorial hcpt hnd C.hasPropernessProperty.2
  choose G hGT hGS hGb using fun p : K => A.hcovS_of_loc hm hΘ hcpt hloc p.1 (hKs p.2)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun p : K => (G p).U) (fun p => (G p).isOpen_U)
    fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, (G _).mem_U⟩
  set L : List (Set A.Obj) := t.toList.flatMap fun p =>
    ((Finset.univ.filter fun k => ((G p).boundarySheet k).Nonempty).toList.map
      (G p).boundarySheet) with hLdef
  have hmemL : ∀ p ∈ t, ∀ k, ((G p).boundarySheet k).Nonempty → (G p).boundarySheet k ∈ L :=
    fun p hp k hk => List.mem_flatMap.2 ⟨p, Finset.mem_toList.2 hp,
      List.mem_map.2 ⟨k, Finset.mem_toList.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩), rfl⟩⟩
  refine FormEval.k1_msheets_of_subset_list (C.isSubmanifoldOfDim_boundarySheet i) hne
    (L := L) (fun s hs => ?_) fun z hz => ?_
  · obtain ⟨p, -, hs⟩ := List.mem_flatMap.1 hs
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hs
    exact hGb p k (Finset.mem_filter.1 (Finset.mem_toList.1 hk)).2
  · have hzM : z ∈ C.M i := C.boundarySheet_subset i hz
    have hzK : z ∈ K := hUK ⟨C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i
      hzM, C.subset_U i hzM⟩
    obtain ⟨p, hpt, hzp⟩ := mem_iUnion₂.1 (ht hzK)
    obtain ⟨k, hzk, hT⟩ := MPolyfold.k1_exists_tangent_eq (C.isSubmanifoldOfDim i)
      (G p).isSubmanifoldOfDim (G p).isOpen_U
      (fun q hq => mem_iUnion.2
        (((G p).toTameBranchingStructure.toLocalBranchingStructure.mem_supp_iff hq.2).1
          (C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i hq.1)))
      (fun k w hw hwk =>
        (G p).toTameBranchingStructure.toLocalBranchingStructure.k1_exists_isOpen_disjoint k hw hwk)
      hzM hzp
    have hzb : z ∈ (G p).boundarySheet k :=
      MPolyfold.k1_mem_boundaryStratum_of_tangent_eq hz hzk hT
    exact mem_iUnion₂.2 ⟨_, hmemL p hpt k ⟨z, hzb⟩, hzb⟩

/-- **Theorem 9.5.15, 2021 p. 449 (2017: Theorem 9.4)**, as stated in the text: `Θ` compact,
branched, oriented by `T̂Θ = T`, tame (`hloc`), of dimension `m + 1`, `m ≥ 1`.  There is a unique
linear map `ω ↦ μ^{∂Θ̂}_ω` from `Ωᵐ_{ep,∞}(X)` to the finite signed measures on `(∂S, L(∂S))`
with `μ^{∂Θ̂}_ω(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(∂₁Mᵢ, o_{∂Mᵢ})` for **every** oriented tame structure
at `x ∈ supp(∂Θ)` describing `T̂Θ` and every measurable `K ⊆ |U(x)|` (sum over the nonempty
`∂₁Mᵢ`). -/
theorem theorem_9_5_15 (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T) :
    ∃! Φ : A.epFormsInfty m →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
        (A.X.lebesgueSigmaBoundaryH (m + 1) Θ),
      ∀ (ω : A.epFormsInfty m) (x : A.Obj) (C : A.X.OrientedTameStructure (m + 1) Θ x)
        (hCT : C.Represents T),
        x ∈ supp (A.X.boundaryTheta Θ) →
        ∀ K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)),
          MeasurableSet[A.X.lebesgueSigmaBoundaryH (m + 1) Θ] K →
          Subtype.val '' K ⊆ A.X.π '' C.U →
          Φ ω K = (Nat.card (A.X.Isotropy x) : ℝ)⁻¹ *
            (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum
              ((A.epFormsInftyEval m).msheetIntegration hm) ω (A.X.π ⁻¹' (Subtype.val '' K)) := by
  obtain ⟨Φ, hΦ, huniq⟩ := A.theorem_9_5_15_class hm hΘ hcpt hT hloc
  exact ⟨Φ, fun ω x C hCT hx => hΦ ω x C hCT hx
      fun i hne => A.boundarySheet_mem_msheets_of_loc hm hΘ hcpt hloc C i hne,
    fun Ψ hΨ => huniq Ψ fun ω x C hCT hx _ => hΨ ω x C hCT hx⟩

/-- **Theorem 9.5.16, 2021 p. 449 (2017: Theorem 9.5)**, as stated in the text: `X` with the local
unique continuation property, `Θ` as in Theorem 9.5.15; the local formula with `1/♯G_x^eff` for
every oriented tame structure. -/
theorem theorem_9_5_16 (hm : 0 < m) (hLUC : A.X.IsLUC) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T) :
    ∃! Φ : A.epFormsInfty m →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
        (A.X.lebesgueSigmaBoundaryH (m + 1) Θ),
      ∀ (ω : A.epFormsInfty m) (x : A.Obj) (C : A.X.OrientedTameStructure (m + 1) Θ x)
        (hCT : C.Represents T),
        x ∈ supp (A.X.boundaryTheta Θ) →
        ∀ K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)),
          MeasurableSet[A.X.lebesgueSigmaBoundaryH (m + 1) Θ] K →
          Subtype.val '' K ⊆ A.X.π '' C.U →
          Φ ω K = (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹ *
            (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum
              ((A.epFormsInftyEval m).msheetIntegration hm) ω (A.X.π ⁻¹' (Subtype.val '' K)) := by
  obtain ⟨Φ, hΦ, huniq⟩ := A.theorem_9_5_16_class hm hLUC hΘ hcpt hT hloc
  exact ⟨Φ, fun ω x C hCT hx => hΦ ω x C hCT hx
      fun i hne => A.boundarySheet_mem_msheets_of_loc hm hΘ hcpt hloc C i hne,
    fun Ψ hΨ => huniq Ψ fun ω x C hCT hx _ => hΨ ω x C hCT hx⟩

/-- The canonical boundary measure (`EP.boundaryMeasure`) has the local formula of Theorem 9.5.15
for every oriented tame structure. -/
theorem boundaryMeasure_apply_all (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty m) (x : A.Obj) (C : A.X.OrientedTameStructure (m + 1) Θ x)
    (hCT : C.Represents T) (hx : x ∈ supp (A.X.boundaryTheta Θ))
    (K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)))
    (hK : MeasurableSet[A.X.lebesgueSigmaBoundaryH (m + 1) Θ] K)
    (hKU : Subtype.val '' K ⊆ A.X.π '' C.U) :
    A.boundaryMeasure hm hΘ hcpt hT hloc ω K = (Nat.card (A.X.Isotropy x) : ℝ)⁻¹ *
      (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum
        ((A.epFormsInftyEval m).msheetIntegration hm) ω (A.X.π ⁻¹' (Subtype.val '' K)) :=
  A.boundaryMeasure_spec hm hΘ hcpt hT hloc ω x C hCT hx
    (fun i hne => A.boundarySheet_mem_msheets_of_loc hm hΘ hcpt hloc C i hne) K hK hKU

end EP

end Polyfold
