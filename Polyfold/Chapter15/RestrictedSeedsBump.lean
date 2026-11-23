import Polyfold.Chapter9.BumpsNearCompact
import Polyfold.Chapter15.CubeEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 9, §9.5,
**Remark 9.5.19**, p. 451, read on an ep-groupoid and on the cylinder `[0, 1]ⁿ × X` of
Corollary 15.3.10 (p. 699).

# Functions concentrated near a point and sc-smooth on a saturated neighbourhood of a compact part

## The text, paraphrased

(Remark 9.5.19) Near a locally compact subset of an M-polyfold there are sc-smooth functions with
small supports, although a general sc-Banach space need not carry sc-smooth bump functions.

## What is formalized (namespace `Polyfold.LocalPart`)

For an ep-groupoid `X`, a compact `T ⊆ |X|`, an object `p` and an open `N ∋ p`:

* **`exists_local_bump_saturated`**, **`exists_bump_near_compact`**: a function `β ≥ 0` on `X`
  with `β(p) = 1`, vanishing off a closed `C ⊆ N`, and sc-smooth on a saturated open
  `G ⊇ π⁻¹(T)`.  The function is not constant on orbits; its support is in the given `N`.
* `exists_bump_pos_on_compact`: the same with `β > 0` on a given compact `K ⊆ N ∩ π⁻¹(T)`.
* **`exists_bump_near_compact_cube`**, `exists_bump_pos_on_compact_cube`: on `[0, 1]ⁿ × X`, with
  the set of sc-smoothness of the form `[0, 1]ⁿ × V` for a saturated open `V ⊇ π⁻¹(T)` of `X`.

## Reading

`G` depends on `(p, N)`: it is the complement of the saturation of the closed set `C ∖ O`, where
`O` is the open set of `LocalPart.exists_local_bump`; `C` lies in a proper subset, so the
saturation is closed.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

open MPolyfold EpGroupoid

namespace LocalPart

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- **A function concentrated near `p` and sc-smooth on a saturated open neighbourhood of a
saturated set `S`** which lies near `p` in a compact set (Remark 9.5.19, 2021 p. 451): for an
open `N ∋ p` there are `β ≥ 0` with `β(p) = 1`, a closed `C ⊆ N` off which `β` vanishes, and a
saturated open `G ⊇ S` on which `β` is sc-smooth. -/
theorem exists_local_bump_saturated {S : Set Obj} (hS : X.IsSaturated S) {p : Obj}
    (hloc : ∃ W : Set Obj, IsOpen W ∧ p ∈ W ∧ ∃ K : Set Obj, IsCompact K ∧ S ∩ W ⊆ K)
    {N : Set Obj} (hN : IsOpen N) (hpN : p ∈ N) :
    ∃ (β : Obj → ℝ) (G C : Set Obj), IsOpen G ∧ X.IsSaturated G ∧ S ⊆ G ∧
      X.PObj.IsScSmoothOn realPolyfold β G ∧ (∀ y, 0 ≤ β y) ∧ β p = 1 ∧ IsClosed C ∧
      support β ⊆ C ∧ C ⊆ N := by
  obtain ⟨R, V, hVo, hpV, -, hVcl, hRN, hprop⟩ := X.exists_invariant_nhds_of_isOpen p hN hpN
  obtain ⟨f, O, C, hO, hSO, hfO, hf0, hfp, hC, hfC, hCV⟩ :=
    exists_local_bump (P := X.PObj) (S := S) hVo hpV hloc
  have hDcl : IsClosed (C \ O) := hC.sdiff hO
  have hDprop : X.IsProperSubset (C \ O) :=
    hprop.of_subset (fun y hy => subset_closure (hCV hy.1)) hDcl
  have hsat : IsClosed (X.saturation (C \ O)) := X.isClosed_saturation_of_isProperSubset hDprop
  have hGeq : (X.saturation (C \ O))ᶜ = X.π ⁻¹' (X.π '' (C \ O))ᶜ := rfl
  have hGo : IsOpen (X.saturation (C \ O))ᶜ := hsat.isOpen_compl
  have hGsub : (X.saturation (C \ O))ᶜ ⊆ O ∪ Cᶜ := by
    intro y hy
    by_cases hyC : y ∈ C
    · by_cases hyO : y ∈ O
      · exact Or.inl hyO
      · exact absurd (X.subset_saturation (C \ O) (show y ∈ C \ O from ⟨hyC, hyO⟩)) hy
    · exact Or.inr hyC
  refine ⟨f, (X.saturation (C \ O))ᶜ, C, hGo, ?_, fun y hy hsy => ?_, ?_, hf0, hfp, hC, hfC,
    fun y hy => hRN (hVcl (subset_closure (hCV hy)))⟩
  · rw [hGeq]
    exact isSaturated_preimage_π _
  · obtain ⟨z, hz, hzy⟩ := hsy
    have hzS : z ∈ S := by
      rw [← hS]
      exact ⟨y, hy, hzy.symm⟩
    exact hz.2 (hSO hzS)
  · refine isScSmoothOn_of_nhds hGo fun y hy => ?_
    rcases hGsub hy with h | h
    · exact ⟨O, h, hfO⟩
    · refine ⟨Cᶜ, h, (real_const hC.isOpen_compl 0).congr fun z hz => ?_⟩
      by_contra hne
      exact hz (hfC fun h0 => hne h0.symm)

/-- **A function concentrated near `p` and sc-smooth on a saturated open neighbourhood of
`π⁻¹(T)`**, `T ⊆ |X|` compact (Remark 9.5.19, 2021 p. 451). -/
theorem exists_bump_near_compact {T : Set X.OrbitSpace} (hT : IsCompact T) (p : Obj)
    {N : Set Obj} (hN : IsOpen N) (hpN : p ∈ N) :
    ∃ (β : Obj → ℝ) (G C : Set Obj), IsOpen G ∧ X.IsSaturated G ∧ X.π ⁻¹' T ⊆ G ∧
      X.PObj.IsScSmoothOn realPolyfold β G ∧ (∀ y, 0 ≤ β y) ∧ β p = 1 ∧ IsClosed C ∧
      support β ⊆ C ∧ C ⊆ N :=
  exists_local_bump_saturated (isSaturated_preimage_π T)
    (exists_isCompact_nhds_preimage_π hT p) hN hpN

/-- **A function positive on a compact part of `π⁻¹(T)`, with support in a given open set, and
sc-smooth on a saturated open neighbourhood of `π⁻¹(T)`**: a finite sum of the functions of
`exists_bump_near_compact`. -/
theorem exists_bump_pos_on_compact {T : Set X.OrbitSpace} (hT : IsCompact T) {K : Set Obj}
    (hK : IsCompact K) (hKT : K ⊆ X.π ⁻¹' T) {N : Set Obj} (hN : IsOpen N) (hKN : K ⊆ N) :
    ∃ (β : Obj → ℝ) (G C : Set Obj), IsOpen G ∧ X.IsSaturated G ∧ X.π ⁻¹' T ⊆ G ∧
      X.PObj.IsScSmoothOn realPolyfold β G ∧ (∀ y, 0 ≤ β y) ∧ (∀ y ∈ K, 0 < β y) ∧ IsClosed C ∧
      support β ⊆ C ∧ C ⊆ N := by
  classical
  have hex : ∀ p : K, ∃ (β : Obj → ℝ) (G C : Set Obj), IsOpen G ∧ X.IsSaturated G ∧
      X.π ⁻¹' T ⊆ G ∧ X.PObj.IsScSmoothOn realPolyfold β G ∧ (∀ y, 0 ≤ β y) ∧ β p = 1 ∧
      IsClosed C ∧ support β ⊆ C ∧ C ⊆ N := fun p =>
    exists_bump_near_compact hT p.1 hN (hKN p.2)
  choose β G C hGo hGs hTG hsc h0 h1 hC hβC hCN using hex
  have hcont : ∀ p : K, ContinuousOn (β p) (G p) := fun p => (hsc p).continuousOn
  set Up : K → Set Obj := fun p => G p ∩ β p ⁻¹' Ioi 0 with hUp
  have hUo : ∀ p, IsOpen (Up p) := fun p => (hcont p).isOpen_inter_preimage (hGo p) isOpen_Ioi
  have hcov : K ⊆ ⋃ p, Up p := fun y hy =>
    mem_iUnion.2 ⟨⟨y, hy⟩, hTG _ (hKT hy), by
      change 0 < β ⟨y, hy⟩ y
      rw [h1]; exact one_pos⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover Up hUo hcov
  have hGt : IsOpen (⋂ p ∈ t, G p) := isOpen_biInter_finset fun p _ => hGo p
  refine ⟨fun y => ∑ p ∈ t, β p y, ⋂ p ∈ t, G p, ⋃ p ∈ t, C p, hGt, ?_, ?_, ?_,
    fun y => Finset.sum_nonneg fun p _ => h0 p y, fun y hy => ?_,
    t.finite_toSet.isClosed_biUnion fun p _ => hC p, fun y hy => ?_,
    iUnion₂_subset fun p _ => hCN p⟩
  · exact X.isSaturated_iff.2 fun φ hφ => mem_iInter₂.2 fun p hp =>
      X.isSaturated_iff.1 (hGs p) φ (mem_iInter₂.1 hφ p hp)
  · exact fun y hy => mem_iInter₂.2 fun p _ => hTG p hy
  · exact real_finsetSum t hGt fun p hp => (hsc p).mono hGt (biInter_subset_of_mem hp)
  · obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.1 (ht hy)
    exact lt_of_lt_of_le hyp.2 (Finset.single_le_sum (fun q _ => h0 q y) hp)
  · by_contra hn
    apply hy
    refine Finset.sum_eq_zero fun p hp => ?_
    by_contra hne
    exact hn (mem_iUnion₂.2 ⟨p, hp, hβC p hne⟩)

end LocalPart

/-! ### The product form on `[0, 1]ⁿ × X` -/

namespace LocalPart

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
  (n : ℕ) [ParacompactSpace ((Fin n → unitInterval) × Obj)]
  [ParacompactSpace ((Fin n → unitInterval) × Mor)]

/-- **The tube over a saturated open subset of `[0, 1]ⁿ × X`**: the set of the `x` with
`[0, 1]ⁿ × {x} ⊆ G̃` is open (the cube is compact) and saturated. -/
theorem isOpen_isSaturated_tube {G : Set ((Fin n → unitInterval) × Obj)} (hG : IsOpen G)
    (hGs : (X.cubeProd n).IsSaturated G) :
    IsOpen {x : Obj | ∀ q : Fin n → unitInterval, (q, x) ∈ G} ∧
      X.IsSaturated {x : Obj | ∀ q : Fin n → unitInterval, (q, x) ∈ G} := by
  constructor
  · have hcl : IsClosed (Prod.snd '' Gᶜ : Set Obj) :=
      isClosedMap_snd_of_compactSpace _ hG.isClosed_compl
    have e : {x : Obj | ∀ q : Fin n → unitInterval, (q, x) ∈ G} = (Prod.snd '' Gᶜ)ᶜ := by
      ext x
      constructor
      · rintro hx ⟨⟨q, y⟩, hqy, rfl⟩
        exact hqy (hx q)
      · intro hx q
        by_contra h
        exact hx ⟨(q, x), h, rfl⟩
    rw [e]
    exact hcl.isOpen_compl
  · refine X.isSaturated_iff.2 fun φ hφ q => ?_
    exact (X.cubeProd n).isSaturated_iff.1 hGs (q, φ) (hφ q)

/-- `univ ×ˢ π⁻¹(T)` lies over the compact set `|[0, 1]ⁿ × π⁻¹(T)|`. -/
theorem isCompact_image_π_cube_preimage {T : Set X.OrbitSpace} (hT : IsCompact T) :
    IsCompact ((X.cubeProd n).π '' (univ ×ˢ (X.π ⁻¹' T))) := by
  refine X.isCompact_image_π_cubeProd n ?_
  rw [image_preimage_eq _ X.surjective_π]
  exact hT

/-- **Remark 9.5.19 (2021 p. 451) on `[0, 1]ⁿ × X`, product form**: for `T ⊆ |X|` compact, a
point `p` of `[0, 1]ⁿ × X` and an open `N ∋ p`, a function `β ≥ 0` with `β(p) = 1`, vanishing
off a closed `C ⊆ N`, and sc-smooth on `[0, 1]ⁿ × V` for a saturated open `V ⊇ π⁻¹(T)` of
`X`. -/
theorem exists_bump_near_compact_cube {T : Set X.OrbitSpace} (hT : IsCompact T)
    (p : (Fin n → unitInterval) × Obj) {N : Set ((Fin n → unitInterval) × Obj)} (hN : IsOpen N)
    (hpN : p ∈ N) :
    ∃ (β : (Fin n → unitInterval) × Obj → ℝ) (V : Set Obj)
      (C : Set ((Fin n → unitInterval) × Obj)), IsOpen V ∧ X.IsSaturated V ∧ X.π ⁻¹' T ⊆ V ∧
      (X.cubeProd n).PObj.IsScSmoothOn realPolyfold β (univ ×ˢ V) ∧ (∀ y, 0 ≤ β y) ∧ β p = 1 ∧
      IsClosed C ∧ support β ⊆ C ∧ C ⊆ N := by
  obtain ⟨β, G, C, hGo, hGs, hTG, hsc, h0, h1, hC, hβC, hCN⟩ :=
    exists_bump_near_compact (X := X.cubeProd n) (isCompact_image_π_cube_preimage X n hT) p hN hpN
  obtain ⟨hVo, hVs⟩ := isOpen_isSaturated_tube X n hGo hGs
  refine ⟨β, _, C, hVo, hVs, fun x hx q => hTG ⟨(q, x), ⟨mem_univ _, hx⟩, rfl⟩,
    hsc.mono (isOpen_univ.prod hVo) fun z hz => hz.2 z.1, h0, h1, hC, hβC, hCN⟩

/-- **The function of `exists_bump_pos_on_compact` on `[0, 1]ⁿ × X`, product form.** -/
theorem exists_bump_pos_on_compact_cube {T : Set X.OrbitSpace} (hT : IsCompact T)
    {K : Set ((Fin n → unitInterval) × Obj)} (hK : IsCompact K)
    (hKT : K ⊆ univ ×ˢ (X.π ⁻¹' T)) {N : Set ((Fin n → unitInterval) × Obj)} (hN : IsOpen N)
    (hKN : K ⊆ N) :
    ∃ (β : (Fin n → unitInterval) × Obj → ℝ) (V : Set Obj)
      (C : Set ((Fin n → unitInterval) × Obj)), IsOpen V ∧ X.IsSaturated V ∧ X.π ⁻¹' T ⊆ V ∧
      (X.cubeProd n).PObj.IsScSmoothOn realPolyfold β (univ ×ˢ V) ∧ (∀ y, 0 ≤ β y) ∧
      (∀ y ∈ K, 0 < β y) ∧ IsClosed C ∧ support β ⊆ C ∧ C ⊆ N := by
  obtain ⟨β, G, C, hGo, hGs, hTG, hsc, h0, h1, hC, hβC, hCN⟩ :=
    exists_bump_pos_on_compact (X := X.cubeProd n) (isCompact_image_π_cube_preimage X n hT) hK
      (fun y hy => ⟨y, hKT hy, rfl⟩) hN hKN
  obtain ⟨hVo, hVs⟩ := isOpen_isSaturated_tube X n hGo hGs
  refine ⟨β, _, C, hVo, hVs, fun x hx q => hTG ⟨(q, x), ⟨mem_univ _, hx⟩, rfl⟩,
    hsc.mono (isOpen_univ.prod hVo) fun z hz => hz.2 z.1, h0, h1, hC, hβC, hCN⟩

end LocalPart

end Polyfold
