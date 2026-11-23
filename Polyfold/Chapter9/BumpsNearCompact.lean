import Polyfold.Chapter9.LocalPartitionsExtension
import Polyfold.Chapter9.LocalFormsStokes

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §12.3, **Definition
12.3.1** (p. 579, sc-smooth bump functions on an ep-groupoid), with the construction of Remark
9.5.19 (p. 451) and the proper subsets of Definition 7.5.8, Proposition 7.5.10 (pp. 250–251).

# Finitely many bump functions on a neighbourhood of a compact part of the orbit space

## The text, paraphrased

(Definition 12.3.1) `X` admits sc-smooth bump functions if every saturated open neighbourhood of
an object contains the support of an sc-smooth functor `X → ℝ` which is not zero.  The
constructions of §15.3 use such functions at the points of a compact subset of `|X|`.

## What is formalized

* `LocalPart.isCompact_inter_preimage_π`: for a proper `Q ⊆ X` and a compact `T ⊆ |X|`, the set
  `Q ∩ π⁻¹(T)` is compact; `exists_isCompact_nhds_preimage_π`: `π⁻¹(T)` lies, near every object,
  in a compact set.
* `LocalPart.exists_orbit_bump_of_locallyCompact`: the function of Remark 9.5.19 attached to a
  point, for a saturated set `S` which lies near the point in a compact set (in place of the
  support of a branched ep⁺-subgroupoid).
* **`EP.exists_bumps_near_compact`**: for a compact `T ⊆ |X|`, finitely many objects `p_i` and
  open `N_i ∋ p_i`, there is a saturated open `W ⊇ π⁻¹(T)` such that the restricted ep-groupoid
  `X|W` carries sc-smooth functors `F_i ≥ 0` with `F_i(p_i) = 1` and
  `supp F_i ⊆ π⁻¹π(N_i)` (closure in `W`).  No hypothesis on `X` is used.

## Reading

The set `W` depends on the finite family: the functions are sc-smooth near `π⁻¹(T)` only, and
`W` is where all of them are.  So the statement gives the functions of Definition 12.3.1
(pointwise reading) on `X|W` for the given finite family, not for all objects and neighbourhoods
of `X|W` at once.
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

/-- **A proper subset meets the preimage of a compact subset of `|X|` in a compact set**
(Definition 7.5.8, Proposition 7.5.10 (1), 2021 pp. 250–251): `π : Q → |X|` is a closed map
with compact fibres. -/
theorem isCompact_inter_preimage_π {Q : Set Obj} (hQ : X.IsProperSubset Q)
    {T : Set X.OrbitSpace} (hT : IsCompact T) : IsCompact (Q ∩ X.π ⁻¹' T) := by
  have hQc : IsClosed Q := hQ.isClosed
  let g : Q → X.OrbitSpace := fun y => X.π y
  have hg : Continuous g := X.continuous_π.comp continuous_subtype_val
  have hp : IsProperMap g := by
    rw [isProperMap_iff_isClosedMap_and_compact_fibers]
    refine ⟨hg, fun C hC => ?_, fun q => ?_⟩
    · have hC' : IsClosed (Subtype.val '' C : Set Obj) :=
        hQc.isClosedEmbedding_subtypeVal.isClosedMap _ hC
      have h := X.proposition_7_5_10_one
        (hQ.of_subset (by rintro _ ⟨c, -, rfl⟩; exact c.2) hC')
      rwa [image_image] at h
    · obtain ⟨y, rfl⟩ := X.surjective_π q
      rw [IsEmbedding.subtypeVal.isCompact_iff]
      have hK := (X.isProperSubset_iff_isCompact.1 hQ) {y} isCompact_singleton
      have himg := hK.image X.continuous_src
      have e : (Subtype.val '' (g ⁻¹' {X.π y}) : Set Obj) =
          X.src '' (X.src ⁻¹' Q ∩ X.tgt ⁻¹' {y}) := by
        ext x
        constructor
        · rintro ⟨⟨x, hx⟩, hxy, rfl⟩
          obtain ⟨φ, hs, ht⟩ := X.π_eq_π_iff.1 hxy
          exact ⟨φ, ⟨by rw [mem_preimage, hs]; exact hx, ht⟩, hs⟩
        · rintro ⟨φ, ⟨hφQ, hφy⟩, rfl⟩
          exact ⟨⟨_, hφQ⟩, (X.π_src_eq_π_tgt φ).trans (congrArg X.π hφy), rfl⟩
      rw [e]
      exact himg
  have h := (hp.isCompact_preimage hT).image continuous_subtype_val
  have e : Q ∩ X.π ⁻¹' T = Subtype.val '' (g ⁻¹' T) := by
    ext x
    constructor
    · rintro ⟨hxQ, hxT⟩
      exact ⟨⟨x, hxQ⟩, hxT, rfl⟩
    · rintro ⟨⟨x, hx⟩, hxT, rfl⟩
      exact ⟨hx, hxT⟩
  rw [e]
  exact h

/-- **The preimage of a compact subset of `|X|` lies, near every object, in a compact set.** -/
theorem exists_isCompact_nhds_preimage_π {T : Set X.OrbitSpace} (hT : IsCompact T) (p : Obj) :
    ∃ W : Set Obj, IsOpen W ∧ p ∈ W ∧ ∃ K : Set Obj, IsCompact K ∧ X.π ⁻¹' T ∩ W ⊆ K := by
  obtain ⟨R, V, hVo, hpV, -, -, -, hprop⟩ :=
    X.exists_invariant_nhds_of_isOpen p isOpen_univ (mem_univ p)
  exact ⟨V, hVo, hpV, _, isCompact_inter_preimage_π hprop hT,
    fun y hy => ⟨subset_closure hy.2, hy.1⟩⟩

/-- **An orbit-constant function concentrated near the orbit of `p` and sc-smooth near a
saturated set `S`** which lies near `p` in a compact set (Remark 9.5.19, 2021 p. 451): for an
open `N ∋ p` there are `F ≥ 0`, constant on orbits, with `F(p) = 1`, a closed `C ⊆ π⁻¹π(N)` off
which `F` vanishes, and a saturated open `W ⊇ S` on which `F` is sc-smooth. -/
theorem exists_orbit_bump_of_locallyCompact {S : Set Obj} (hS : X.IsSaturated S) {p : Obj}
    (hloc : ∃ W : Set Obj, IsOpen W ∧ p ∈ W ∧ ∃ K : Set Obj, IsCompact K ∧ S ∩ W ⊆ K)
    {N : Set Obj} (hN : IsOpen N) (hpN : p ∈ N) :
    ∃ (F : Obj → ℝ) (W C : Set Obj), IsOpen W ∧ X.IsSaturated W ∧ S ⊆ W ∧
      X.PObj.IsScSmoothOn realPolyfold F W ∧ (∀ φ : Mor, F (X.src φ) = F (X.tgt φ)) ∧
      (∀ y, 0 ≤ F y) ∧ F p = 1 ∧ IsClosed C ∧ support F ⊆ C ∧ C ⊆ X.π ⁻¹' (X.π '' N) := by
  obtain ⟨R, V, hVo, hpV, hVinv, hVcl, hRN, hprop⟩ := X.exists_invariant_nhds_of_isOpen p hN hpN
  obtain ⟨f, O, C, hO, hSO, hfO, hf0, hfp, hC, hfC, hCV⟩ :=
    exists_local_bump (P := X.PObj) (S := S) hVo hpV hloc
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
      have hsat : ∀ w, X.π w = X.π y → w ∈ S := fun w hw => by
        rw [← hS]
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

end LocalPart

namespace EP

open LocalPart

/-- **Finitely many bump functions on a neighbourhood of a compact part of `|X|`** (Definition
12.3.1, 2021 p. 579, pointwise reading, on a restricted ep-groupoid; construction of Remark
9.5.19, p. 451).  Let `T ⊆ |X|` be compact, `p_i` finitely many objects and `N_i ∋ p_i` open.
Then there is a saturated open `W ⊇ π⁻¹(T)` such that on the restricted ep-groupoid `X|W` there
are sc-smooth functions `F_i ≥ 0`, constant on the orbits, with `F_i(p_i) = 1` and support in
`π⁻¹π(N_i)`.  No hypothesis on `X` is used; `W` depends on the family. -/
theorem exists_bumps_near_compact (A : EP.{u}) {T : Set A.X.OrbitSpace} (hT : IsCompact T)
    {ι : Type*} [Finite ι] (p : ι → A.Obj) (N : ι → Set A.Obj) (hN : ∀ i, IsOpen (N i))
    (hpN : ∀ i, p i ∈ N i) :
    ∃ (W : Set A.Obj) (hW : A.X.IsEpSubgroupoid W), IsOpen W ∧ A.X.π ⁻¹' T ⊆ W ∧
      ∃ F : ι → A.Obj → ℝ, ∀ i,
        (A.sub hW).X.PObj.IsScSmoothMap realPolyfold (A.subFun hW (F i)) ∧
        (∀ φ : (A.sub hW).Mor, A.subFun hW (F i) ((A.sub hW).X.src φ) =
          A.subFun hW (F i) ((A.sub hW).X.tgt φ)) ∧
        (∀ y, 0 ≤ F i y) ∧ F i (p i) = 1 ∧
        tsupport (A.subFun hW (F i)) ⊆
          (A.subFunctor hW).obj ⁻¹' (A.X.π ⁻¹' (A.X.π '' N i)) := by
  have hS : A.X.IsSaturated (A.X.π ⁻¹' T) := isSaturated_preimage_π T
  choose F W C hWo hWs hSW hsc hinv h0 h1 hC hFC hCN using fun i =>
    exists_orbit_bump_of_locallyCompact hS (exists_isCompact_nhds_preimage_π hT (p i)) (hN i)
      (hpN i)
  have hWo' : IsOpen (⋂ i, W i) := isOpen_iInter_of_finite hWo
  have hWs' : A.X.IsSaturated (⋂ i, W i) := A.X.isSaturated_iff.2 fun φ hφ =>
    mem_iInter.2 fun i => A.X.isSaturated_iff.1 (hWs i) φ (mem_iInter.1 hφ i)
  have hW := A.X.isEpSubgroupoid_of_isOpen hWo' hWs'
  refine ⟨⋂ i, W i, hW, hWo', fun y hy => mem_iInter.2 fun i => hSW i hy, F, fun i =>
    ⟨A.isScSmoothMap_subFun hW ((hsc i).mono hWo' (iInter_subset _ i)),
      A.subFun_src_eq_tgt hW fun φ _ => hinv i φ, h0 i, h1 i, ?_⟩⟩
  have hcl : IsClosed ((A.subFunctor hW).obj ⁻¹' C i) :=
    (hC i).preimage (continuousOn_univ.1 (A.subFunctor hW).isScSmoothMap_obj.continuousOn)
  refine (closure_minimal (fun y hy => ?_) hcl).trans (preimage_mono (hCN i))
  exact hFC i hy

end EP

end Polyfold
