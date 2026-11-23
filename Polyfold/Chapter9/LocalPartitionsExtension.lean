import Polyfold.Chapter9.LocalPartitionsBump
import Polyfold.Chapter9.GeneralLevelZero
import Polyfold.Chapter9.IntegralCovering

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Remark 9.5.19, 2021 p. 451** (point G.153).  Numbers and pages are
the 2021 text's.

# Orbit-constant functions near a branched ep⁺-subgroupoid

## What is formalized

* `LocalPart.exists_average`: the average of a function over the natural action of `G_x`.
* `LocalPart.isScSmoothOn_orbitExtension`, `LocalPart.continuous_orbitExtension`: the extension
  to the saturation (`EpGroupoid.orbitExtension`, proof of Theorem 7.5.7) of an invariant
  function which is sc-smooth on an open subset `O` of `W(x)` only is sc-smooth on the saturated
  open set `X ∖ π⁻¹π(K) ∪ π⁻¹π(O)`; the extension of a continuous one is continuous.
* `LocalPart.exists_isCompact_nhds_supp`: the support of a branched ep⁺-subgroupoid lies near
  each of its points in a compact set (the dimension of each local branch is locally constant,
  Remark 9.1.1).
* `LocalPart.exists_orbit_bump`: for `p ∈ supp Θ` and an open `N ∋ p`, a function `F ≥ 0`,
  constant on orbits, with `F(p) = 1`, vanishing off a closed subset of `π⁻¹π(N)` and sc-smooth
  on a saturated open neighbourhood of `supp Θ`.
* `LocalPart.exists_orbit_cutoff`: for a point `p` and an open `W ∋ p`, a continuous function
  `c ≥ 0`, constant on orbits, with `c(p) = 1` and vanishing off `π⁻¹π(W)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

open MPolyfold EpGroupoid

namespace LocalPart

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- A preimage under `π` is saturated. -/
theorem isSaturated_preimage_π (T : Set X.OrbitSpace) : X.IsSaturated (X.π ⁻¹' T) := by
  change X.π ⁻¹' (X.π '' (X.π ⁻¹' T)) = X.π ⁻¹' T
  rw [image_preimage_eq _ X.surjective_π]

/-- `|Φ(g)(y)| = |y|` for `y ∈ U(x)`. -/
theorem π_Φ_eq {x : Obj} (R : X.NaturalRep x) (g : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) :
    X.π (R.Φ g y) = X.π y := by
  rw [← R.tgt_Γ g y hy, ← X.π_src_eq_π_tgt, R.src_Γ g y hy]

/-! ### The average over the natural action -/

/-- **The average over the natural action** of a function `f ≥ 0` vanishing off an invariant
`V`: a function `f̄ ≥ 0` vanishing off `V`, invariant on `W(x)`, with `f̄(x) = f(x)`;
it is sc-smooth on `⋂_g Φ(g)⁻¹(O)` if `f` is sc-smooth on `O`, and continuous on `W(x)` if `f` is
continuous. -/
theorem exists_average {x : Obj} (R : X.NaturalRep x) {f : Obj → ℝ} {V : Set Obj}
    (hVinv : ∀ g, MapsTo (R.Φ g) V V) (hf0 : ∀ y, 0 ≤ f y) (hfV : support f ⊆ V) :
    ∃ fa : Obj → ℝ, (∀ y, 0 ≤ fa y) ∧ support fa ⊆ V ∧
      (∀ g, ∀ y ∈ R.U, fa (R.Φ g y) = fa y) ∧ fa x = f x ∧
      (∀ O : Set Obj, X.PObj.IsScSmoothOn realPolyfold f O →
        X.PObj.IsScSmoothOn realPolyfold fa (⋂ g, R.U ∩ R.Φ g ⁻¹' O)) ∧
      (Continuous f → ContinuousOn fa R.U) := by
  classical
  have := Fintype.ofFinite (X.Isotropy x)
  let γg : X.Isotropy x → Obj → ℝ := fun g => R.U.indicator fun y => f (R.Φ g y)
  have hγg_eq : ∀ g, ∀ y ∈ R.U, γg g y = f (R.Φ g y) := fun g y hy => indicator_of_mem hy _
  have hγg_zero : ∀ g y, y ∉ R.U → γg g y = 0 := fun g y hy => indicator_of_notMem hy _
  have hγg_nonneg : ∀ g y, 0 ≤ γg g y := fun g y => indicator_nonneg (fun z _ => hf0 _) y
  have hγg_supp : ∀ g, support (γg g) ⊆ V := by
    intro g y hy
    by_cases hyR : y ∈ R.U
    · rw [mem_support, hγg_eq g y hyR] at hy
      have h1 := hVinv g⁻¹ (hfV hy)
      rwa [R.Φ_inv_Φ g hyR] at h1
    · exact absurd (hγg_zero g y hyR) hy
  have hcard : (0 : ℝ) < Fintype.card (X.Isotropy x) := Nat.cast_pos.2 Fintype.card_pos
  have hc0 : (0 : ℝ) ≤ (Fintype.card (X.Isotropy x) : ℝ)⁻¹ := inv_nonneg.2 hcard.le
  refine ⟨fun y => (Fintype.card (X.Isotropy x) : ℝ)⁻¹ * ∑ g, γg g y,
    fun y => mul_nonneg hc0 (Finset.sum_nonneg fun g _ => hγg_nonneg g y), ?_, fun h y hy => ?_,
    ?_, fun O hO => ?_, fun hfc => ?_⟩
  · refine support_subset_iff'.2 fun y hy => ?_
    rw [Finset.sum_eq_zero fun g _ => notMem_support.1 fun h => hy (hγg_supp g h), mul_zero]
  · have hΦy := R.mapsTo_Φ h hy
    have hsum : ∑ g, γg g (R.Φ h y) = ∑ g, γg g y := by
      calc ∑ g, γg g (R.Φ h y) = ∑ g, γg (g * h) y := Finset.sum_congr rfl fun g _ => by
            rw [hγg_eq g _ hΦy, hγg_eq (g * h) y hy, R.Φ_mul g h y hy]
        _ = ∑ g, γg g y := Equiv.sum_comp (Equiv.mulRight h) fun g => γg g y
    simp only [hsum]
  · have hsum : ∑ g, γg g x = ∑ _g : X.Isotropy x, f x := Finset.sum_congr rfl fun g _ => by
      rw [hγg_eq g x R.mem_U, R.Φ_self]
    simp only [hsum]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hcard.ne', one_mul]
  · have hO' : IsOpen (⋂ g, R.U ∩ R.Φ g ⁻¹' O) := isOpen_iInter_of_finite fun g =>
      (R.continuousOn_Φ g).isOpen_inter_preimage R.isOpen_U hO.isOpen
    refine real_mul (real_const hO' _) (real_finsetSum Finset.univ hO' fun g _ => ?_)
    refine (MPolyfold.IsScSmoothOn.comp hO ((R.isScDiffeoOn_Φ g).isScSmoothOn.mono hO'
      fun y hy => (mem_iInter.1 hy g).1) fun y hy => (mem_iInter.1 hy g).2).congr fun y hy => ?_
    exact (hγg_eq g y (mem_iInter.1 hy g).1).symm
  · refine continuousOn_const.mul (continuousOn_finsetSum _ fun g _ => ?_)
    exact (hfc.comp_continuousOn (R.continuousOn_Φ g)).congr fun y hy => hγg_eq g y hy

/-! ### The extension to the saturation -/

/-- **The extension of an invariant function is sc-smooth where the function is** (the local
form of `EpGroupoid.isScSmoothMap_orbitExtension`, proof of Theorem 7.5.7): let `f` be invariant
on `W(x)`, sc-smooth on an open `O ⊆ W(x)`, and vanish off `K`, the saturation of `K` being
closed.  Then `F ∘ π` is sc-smooth on `(X ∖ π⁻¹π(K)) ∪ π⁻¹π(O)`. -/
theorem isScSmoothOn_orbitExtension {x : Obj} (R : X.NaturalRep x) {f : Obj → ℝ}
    (hinv : ∀ g, ∀ y ∈ R.U, f (R.Φ g y) = f y) {O : Set Obj} (hO : IsOpen O) (hOU : O ⊆ R.U)
    (hf : X.PObj.IsScSmoothOn realPolyfold f O) {K : Set Obj}
    (hKcl : IsClosed (X.saturation K)) (hfK : support f ⊆ K) :
    X.PObj.IsScSmoothOn realPolyfold (X.orbitExtension R f ∘ X.π)
      ((X.saturation K)ᶜ ∪ X.π ⁻¹' (X.π '' O)) := by
  refine isScSmoothOn_of_nhds
    (hKcl.isOpen_compl.union ((X.proposition_7_1_8 _ hO).preimage X.continuous_π)) ?_
  rintro y (hy | hy)
  · refine ⟨(X.saturation K)ᶜ, hy, (real_const hKcl.isOpen_compl 0).congr fun y' hy' => ?_⟩
    have h0 : X.orbitExtension R f (X.π y') = 0 := by
      by_contra hne
      obtain ⟨w, hw, hwy⟩ := X.support_orbitExtension_subset R f hne
      exact hy' ⟨w, hfK hw.2, hwy⟩
    exact h0.symm
  · obtain ⟨z, hz, hzy⟩ := hy
    obtain ⟨φ, hφs, hφt⟩ := (X.π_eq_π_iff).1 hzy
    obtain ⟨W₂, V₂, τ, hφW, hd⟩ := X.isLocalScDiffeo_tgt φ
    have hcont : ContinuousOn (X.src ∘ τ) V₂ :=
      X.continuous_src.comp_continuousOn hd.isScSmoothOn_inv.continuousOn
    have hNo : IsOpen (V₂ ∩ (X.src ∘ τ) ⁻¹' O) :=
      hcont.isOpen_inter_preimage hd.isScSmoothOn_inv.isOpen hO
    refine ⟨V₂ ∩ (X.src ∘ τ) ⁻¹' O, ⟨?_, ?_⟩, ?_⟩
    · rw [← hφt]
      exact hd.mapsTo hφW
    · change X.src (τ y) ∈ O
      rw [← hφt, hd.left_inv φ hφW, hφs]
      exact hz
    · have hsτ : X.PObj.IsScSmoothOn X.PObj (X.src ∘ τ) (V₂ ∩ (X.src ∘ τ) ⁻¹' O) :=
        MPolyfold.IsScSmoothOn.comp X.isScSmoothMap_src
          (hd.isScSmoothOn_inv.mono hNo inter_subset_left) (mapsTo_univ _ _)
      refine (MPolyfold.IsScSmoothOn.comp hf hsτ fun y' hy' => hy'.2).congr fun y' hy' => ?_
      have hy'' : X.src (τ y') ∈ R.U := hOU hy'.2
      simp only [Function.comp_apply]
      rw [← X.orbitExtension_π R hinv hy'', X.π_src_eq_π_tgt, hd.right_inv y' hy'.1]

/-- **The extension of a continuous invariant function is continuous**: let `f` be invariant
and continuous on `W(x)` and vanish off `K ⊆ W(x)`, the saturation of `K` being closed.  Then
`F ∘ π` is continuous. -/
theorem continuous_orbitExtension {x : Obj} (R : X.NaturalRep x) {f : Obj → ℝ}
    (hinv : ∀ g, ∀ y ∈ R.U, f (R.Φ g y) = f y) (hf : ContinuousOn f R.U) {K : Set Obj}
    (hKcl : IsClosed (X.saturation K)) (hfK : support f ⊆ K) (hKU : K ⊆ R.U) :
    Continuous (X.orbitExtension R f ∘ X.π) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hy : y ∈ X.π ⁻¹' (X.π '' R.U)
  · obtain ⟨z, hz, hzy⟩ := hy
    obtain ⟨φ, hφs, hφt⟩ := (X.π_eq_π_iff).1 hzy
    obtain ⟨W₂, V₂, τ, hφW, hd⟩ := X.isLocalScDiffeo_tgt φ
    have hcont : ContinuousOn (X.src ∘ τ) V₂ :=
      X.continuous_src.comp_continuousOn hd.isScSmoothOn_inv.continuousOn
    have hNo : IsOpen (V₂ ∩ (X.src ∘ τ) ⁻¹' R.U) :=
      hcont.isOpen_inter_preimage hd.isScSmoothOn_inv.isOpen R.isOpen_U
    have hyN : y ∈ V₂ ∩ (X.src ∘ τ) ⁻¹' R.U := by
      refine ⟨?_, ?_⟩
      · rw [← hφt]
        exact hd.mapsTo hφW
      · change X.src (τ y) ∈ R.U
        rw [← hφt, hd.left_inv φ hφW, hφs]
        exact hz
    have hc : ContinuousOn (X.orbitExtension R f ∘ X.π) (V₂ ∩ (X.src ∘ τ) ⁻¹' R.U) := by
      refine (hf.comp (hcont.mono inter_subset_left) fun y' hy' => hy'.2).congr fun y' hy' => ?_
      have hy'' : X.src (τ y') ∈ R.U := hy'.2
      simp only [Function.comp_apply]
      rw [← X.orbitExtension_π R hinv hy'', X.π_src_eq_π_tgt, hd.right_inv y' hy'.1]
    exact hc.continuousAt (hNo.mem_nhds hyN)
  · have hyK : y ∈ (X.saturation K)ᶜ := fun h => hy (preimage_mono (image_mono hKU) h)
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [hKcl.isOpen_compl.mem_nhds hyK] with y' hy'
    have h0 : X.orbitExtension R f (X.π y') = 0 := by
      by_contra hne
      obtain ⟨w, hw, hwy⟩ := X.support_orbitExtension_subset R f hne
      exact hy' ⟨w, hfK hw.2, hwy⟩
    exact h0.symm

/-! ### Local compactness of the support -/

variable {Θ : Obj → ℚ}

/-- **The support of a branched ep⁺-subgroupoid lies, near each of its points, in a compact
set**: the local branches are finite-dimensional submanifolds of locally constant dimension
(Remark 9.1.1, 2021 p. 402), hence locally compact. -/
theorem exists_isCompact_nhds_supp (hΘ : X.IsBranchedEpSubgroupoid Θ) {p : Obj}
    (hp : p ∈ supp Θ) :
    ∃ W : Set Obj, IsOpen W ∧ p ∈ W ∧ ∃ K : Set Obj, IsCompact K ∧ supp Θ ∩ W ⊆ K := by
  classical
  obtain ⟨B⟩ := hΘ.localBranching p hp
  choose V hV hpV n hn using fun j =>
    MPolyfold.hasLocallyConstantDimAt (P := X.PObj) p (B.M j) (B.isSmoothSubmanifold j) (B.mem_M j)
  choose W hW hpW K hK hWK hKM using fun j =>
    MPolyfold.exists_compact_nhds_submanifold (hn j) (x := p) ⟨B.mem_M j, hpV j⟩
  refine ⟨B.U ∩ ⋂ j, (V j ∩ W j),
    B.isOpen_U.inter (isOpen_iInter_of_finite fun j => (hV j).inter (hW j)),
    ⟨B.mem_U, mem_iInter.2 fun j => ⟨hpV j, hpW j⟩⟩, ⋃ j, K j, isCompact_iUnion hK, ?_⟩
  rintro y ⟨hys, hyU, hyW⟩
  obtain ⟨j, hj⟩ := (B.mem_supp_iff hyU).1 hys
  have := mem_iInter.1 hyW j
  exact mem_iUnion.2 ⟨j, hWK j ⟨⟨hj, this.1⟩, this.2⟩⟩

/-! ### The functions attached to a point -/

/-- **An orbit-constant function concentrated near the orbit of `p ∈ supp Θ` and sc-smooth near
`supp Θ`** (Remark 9.5.19, 2021 p. 451): for an open `N ∋ p` there are `F ≥ 0`, constant on
orbits, with `F(p) = 1`, a closed `C ⊆ π⁻¹π(N)` off which `F` vanishes, and a saturated open
`W ⊇ supp Θ` on which `F` is sc-smooth. -/
theorem exists_orbit_bump (hΘ : X.IsBranchedEpSubgroupoid Θ) {p : Obj} (hp : p ∈ supp Θ)
    {N : Set Obj} (hN : IsOpen N) (hpN : p ∈ N) :
    ∃ (F : Obj → ℝ) (W C : Set Obj), IsOpen W ∧ X.IsSaturated W ∧ supp Θ ⊆ W ∧
      X.PObj.IsScSmoothOn realPolyfold F W ∧ (∀ φ : Mor, F (X.src φ) = F (X.tgt φ)) ∧
      (∀ y, 0 ≤ F y) ∧ F p = 1 ∧ IsClosed C ∧ support F ⊆ C ∧ C ⊆ X.π ⁻¹' (X.π '' N) := by
  obtain ⟨R, V, hVo, hpV, hVinv, hVcl, hRN, hprop⟩ := X.exists_invariant_nhds_of_isOpen p hN hpN
  obtain ⟨f, O, C, hO, hSO, hfO, hf0, hfp, hC, hfC, hCV⟩ :=
    exists_local_bump (P := X.PObj) (S := supp Θ) hVo hpV (exists_isCompact_nhds_supp hΘ hp)
  obtain ⟨fa, hfa0, hfaV, hfainv, hfap, hfasc, -⟩ :=
    exists_average R hVinv hf0 (hfC.trans hCV)
  have hfaO := hfasc O hfO
  have hO' : IsOpen (⋂ g, R.U ∩ R.Φ g ⁻¹' O) := hfaO.isOpen
  have hO'U : (⋂ g, R.U ∩ R.Φ g ⁻¹' O) ⊆ R.U := fun y hy => (mem_iInter.1 hy 1).1
  have hKcl : IsClosed (X.saturation (closure V)) := X.isClosed_saturation_of_isProperSubset hprop
  have hsc := isScSmoothOn_orbitExtension R hfainv hO' hO'U hfaO hKcl (hfaV.trans subset_closure)
  have hWeq : (X.saturation (closure V))ᶜ ∪ X.π ⁻¹' (X.π '' ⋂ g, R.U ∩ R.Φ g ⁻¹' O) =
      X.π ⁻¹' ((X.π '' closure V)ᶜ ∪ X.π '' ⋂ g, R.U ∩ R.Φ g ⁻¹' O) := rfl
  refine ⟨X.orbitExtension R fa ∘ X.π, _, X.saturation (closure V), hsc.isOpen, ?_, ?_, hsc,
    fun φ => ?_, fun y => X.orbitExtension_nonneg R hfa0 _, ?_, hKcl, ?_,
    preimage_mono (image_mono (hVcl.trans hRN))⟩
  · rw [hWeq]
    exact isSaturated_preimage_π _
  · intro y hy
    by_cases hyK : y ∈ X.saturation (closure V)
    · obtain ⟨z, hzK, hzy⟩ := hyK
      have hzU : z ∈ R.U := hVcl hzK
      have hsat : ∀ w, X.π w = X.π y → w ∈ supp Θ := fun w hw => by
        rw [← preimage_π_orbitSupp hΘ.isFunctorial]
        exact ⟨y, hy, hw.symm⟩
      refine Or.inr ⟨z, mem_iInter.2 fun g => ⟨hzU, hSO (hsat _ ?_)⟩, hzy⟩
      rw [π_Φ_eq R g hzU, hzy]
    · exact Or.inl hyK
  · simp only [Function.comp_apply, X.π_src_eq_π_tgt φ]
  · change X.orbitExtension R fa (X.π p) = 1
    rw [X.orbitExtension_π R hfainv R.mem_U, hfap, hfp]
  · intro y hy
    obtain ⟨w, hw, hwy⟩ := X.support_orbitExtension_subset R fa hy
    exact ⟨w, subset_closure (hfaV hw.2), hwy⟩

/-- **A continuous orbit-constant function concentrated near the orbit of `p`**: for an open
`W ∋ p` there is a continuous `c ≥ 0`, constant on orbits, with `c(p) = 1`, vanishing off
`π⁻¹π(W)`. -/
theorem exists_orbit_cutoff (X : EpGroupoid Obj Mor) (p : Obj) {W : Set Obj} (hW : IsOpen W)
    (hpW : p ∈ W) :
    ∃ c : Obj → ℝ, Continuous c ∧ (∀ φ : Mor, c (X.src φ) = c (X.tgt φ)) ∧ (∀ y, 0 ≤ c y) ∧
      c p = 1 ∧ support c ⊆ X.π ⁻¹' (X.π '' W) := by
  obtain ⟨R, V, hVo, hpV, hVinv, hVcl, hRW, hprop⟩ := X.exists_invariant_nhds_of_isOpen p hW hpW
  obtain ⟨c₀, hc₀0, hc₀1, hc₀⟩ := exists_continuous_zero_one_of_isClosed hVo.isClosed_compl
    (isClosed_singleton (x := p)) (disjoint_singleton_right.2 fun h => h hpV)
  have hsupp : support (c₀ : Obj → ℝ) ⊆ V := fun y hy => by
    by_contra h
    exact hy (hc₀0 h)
  obtain ⟨fa, hfa0, hfaV, hfainv, hfap, -, hfac⟩ :=
    exists_average R hVinv (fun y => (hc₀ y).1) hsupp
  have hKcl : IsClosed (X.saturation (closure V)) := X.isClosed_saturation_of_isProperSubset hprop
  refine ⟨X.orbitExtension R fa ∘ X.π,
    continuous_orbitExtension R hfainv (hfac c₀.continuous) hKcl (hfaV.trans subset_closure) hVcl,
    fun φ => ?_, fun y => X.orbitExtension_nonneg R hfa0 _, ?_, fun y hy => ?_⟩
  · simp only [Function.comp_apply, X.π_src_eq_π_tgt φ]
  · change X.orbitExtension R fa (X.π p) = 1
    rw [X.orbitExtension_π R hfainv R.mem_U, hfap]
    exact hc₀1 rfl
  · obtain ⟨w, hw, hwy⟩ := X.support_orbitExtension_subset R fa hy
    exact ⟨w, hRW hw.1, hwy⟩

end LocalPart

end Polyfold
