import Polyfold.Chapter12.OrientationGeneralizedIso
import Polyfold.Chapter12.OrientationTransferTheorem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, **Theorem 12.5.7** (2017: Theorem 12.12) **with the topology**, for a generalized
strong bundle isomorphism `f̄ : W → W'` (a class `GenSBMap A A'`), with Part I's hypotheses
(tame object M-polyfolds with bump functions, tame germ data) on the two ends `W`, `W'` only.

## The text, paraphrased

The map `|f̄|_* : |O_f| → |O_{f'}|` is a homeomorphism covering the homeomorphism
`|f| : |X_∞| → |X'_∞|`, and an orientation of `f` has exactly one push-forward orientation of
`f'`.

## What is formalized

* `MPolyfold.IsLocalScDiffeo.admitsBumpFunctions`: bump functions (Definition 5.3.1) pass from
  `Z` to `X` along a local sc-diffeomorphism `X → Z`.  With
  `MPolyfold.IsLocalScDiffeo.isTame` (tameness) and
  `IsStrongBundleEquivalence.isScFredholmSectionTame_pullback` (tame germ data) and
  `IsStrongBundleEquivalence.hasScPlusSectionsThrough` (sc⁺-sections), the middle of a diagram
  `W ←Φ– V –Ψ→ W'` inherits all of Part I's hypotheses from `W`.
* `GenSBMap.theorem_12_5_7_one_homeo_cls`: **(1)** for the class: homeomorphisms
  `|O_f| ≃ₜ |O_{f'}|`, `|X_∞| ≃ₜ |X'_∞|` commuting with `|σ|`, `|σ'|`, whose underlying maps are
  `GenSBMap.orbitOrMap` and `GenSBMap.smoothOrbitMap` (so independent of the representative).
* `GenSBMap.theorem_12_5_7_two_cls`: **(2)** for every representative `D` of the class: an
  orientation `o` of `f` (Definition 12.5.4) has exactly one orientation `o'` of `f'`
  corresponding to `o` over the middle of `D`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

/-! ### Bump functions along a local sc-diffeomorphism -/

section Bump

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}

/-- **Bump functions pass to the source of a local sc-diffeomorphism** `φ : X → Z`
(Definition 5.3.1): for `x ∈ U`, take `φ|_{U₁}` an sc-diffeomorphism onto `V₁` near `x`, a closed
neighbourhood `K ⊆ U ∩ U₁` of `x`, and a bump function `h` of `Z` at `φ(x)` supported in
`V₁ ∩ (φ|_{U₁})⁻¹(int K)`; then `h ∘ φ` on `U₁`, extended by `0`, is a bump function at `x`
supported in `K`. -/
theorem MPolyfold.IsLocalScDiffeo.admitsBumpFunctions {φ : X → Z}
    (hφ : PX.IsLocalScDiffeo PZ φ) (hbump : PZ.AdmitsBumpFunctions) : PX.AdmitsBumpFunctions := by
  intro x U hU hxU
  obtain ⟨U₁, V₁, g, hx₁, hd⟩ := hφ x
  have hU₁ : IsOpen U₁ := hd.isScSmoothOn.isOpen
  obtain ⟨K, hK, hKc, hKsub⟩ :=
    exists_mem_nhds_isClosed_subset ((hU.inter hU₁).mem_nhds ⟨hxU, hx₁⟩)
  have hO : IsOpen (V₁ ∩ g ⁻¹' interior K) :=
    hd.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hd.isScSmoothOn_inv.isOpen
      _root_.isOpen_interior
  have hxO : φ x ∈ V₁ ∩ g ⁻¹' interior K :=
    ⟨hd.mapsTo hx₁, by
      rw [mem_preimage, hd.left_inv x hx₁]
      exact mem_interior_iff_mem_nhds.2 hK⟩
  obtain ⟨h, hh, hhx, hhsupp⟩ := hbump (φ x) _ hO hxO
  classical
  set F : X → ℝ := fun y => if y ∈ U₁ then h (φ y) else 0 with hFdef
  have hsupp : support F ⊆ K := by
    intro y hy
    by_cases hy₁ : y ∈ U₁
    · have hy' : h (φ y) ≠ 0 := by simpa [hFdef, hy₁] using hy
      have hO' := (hhsupp (subset_tsupport _ hy')).2
      rw [mem_preimage, hd.left_inv y hy₁] at hO'
      exact interior_subset hO'
    · exact absurd (by simp [hFdef, hy₁]) hy
  have hzero : ∀ z ∉ K, F z = 0 := fun z hz => by
    by_contra hne
    exact hz (hsupp hne)
  refine ⟨F, ?_, by simpa [hFdef, hx₁] using hhx,
    (closure_minimal hsupp hKc).trans fun y hy => (hKsub hy).1⟩
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun y _ => ?_
  by_cases hy₁ : y ∈ U₁
  · refine ⟨U₁, hU₁, hy₁, subset_univ _, ?_⟩
    refine (MPolyfold.IsScSmoothOn.comp (U' := univ) hh hd.isScSmoothOn
      (mapsTo_univ _ _)).congr fun z hz => ?_
    simp [hFdef, hz]
  · have hyK : y ∉ K := fun hy => hy₁ (hKsub hy).2
    refine ⟨Kᶜ, hKc.isOpen_compl, hyK, subset_univ _, ?_⟩
    exact ((isScSmoothMap_real_const (PX := PX) 0).mono hKc.isOpen_compl
      (subset_univ _)).congr fun z hz => (hzero z hz).symm

end Bump

namespace SBLocalization

open SEP EpStrongBundle EpStrongBundle.IsStrongBundleEquivalence

variable {A A' : SEP.{u}}

/-! ### Part I's hypotheses on the middle of a diagram -/

namespace SDiagram

variable (D : SDiagram A A')

/-- The middle of a diagram is tame if the source is (local sc-diffeomorphism `φ`). -/
theorem isTame_B (hX : A.X.PObj.IsTame) : D.B.X.PObj.IsTame :=
  D.hΦ.isEquivalence_base.isLocalScDiffeo_obj.isTame hX

/-- The middle of a diagram admits bump functions if the source does. -/
theorem admitsBumpFunctions_B (hbump : A.X.PObj.AdmitsBumpFunctions) :
    D.B.X.PObj.AdmitsBumpFunctions :=
  D.hΦ.isEquivalence_base.isLocalScDiffeo_obj.admitsBumpFunctions hbump

/-- The pull-back `Φ^* f` has tame germ data if `f` has (Definition 3.6.5). -/
theorem isScFredholmSectionTame_pullback {f : A.Obj → A.W} (hfT : A.B.IsScFredholmSectionTame f) :
    D.B.B.IsScFredholmSectionTame (D.hΦ.pullback f) :=
  D.hΦ.isScFredholmSectionTame_pullback hfT

end SDiagram

/-! ### Theorem 12.5.7 with the topology for classes -/

namespace GenSBMap

variable {F : GenSBMap A A'} (hFi : F.IsGeneralizedIso) {f : A.Obj → A.W} {f' : A'.Obj → A'.W}
  (hF : A.E.IsScFredholmSectionFunctor f) (hF' : A'.E.IsScFredholmSectionFunctor f')
  (hf' : f' = pushforward hFi f)
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)
  (hX : A.X.PObj.IsTame) (hbump : A.X.PObj.AdmitsBumpFunctions)
  (hfT : A.B.IsScFredholmSectionTame f) (hX' : A'.X.PObj.IsTame)
  (hbump' : A'.X.PObj.AdmitsBumpFunctions) (hfT' : A'.B.IsScFredholmSectionTame f')

/-- **Theorem 12.5.7 (1) for a generalized strong bundle isomorphism**, p. 595 (2017:
Theorem 12.12 (1)), with the topology and Part I's hypotheses on `W` and `W'` only: there are
homeomorphisms `|O_f| ≃ₜ |O_{f'}|` and `|X_∞| ≃ₜ |X'_∞|` with `|σ'| ∘ F = G ∘ |σ|`, and they are
`|f̄|_*` and `|f|` (`GenSBMap.orbitOrMap`, `GenSBMap.smoothOrbitMap`, the maps of every
representative). -/
theorem theorem_12_5_7_one_homeo_cls :
    haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    haveI := paracompactSpace_rn_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A.B
    haveI := paracompactSpace_rn_prod A'.X.PObj
    haveI := paracompactSpace_rn_pullback A'.B
    haveI := paracompactSpace_rn_rn_prod A'.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A'.B
    letI : TopologicalSpace (OrSpace f hF.2) := orTopology (orLocalTransport hX hbump hfT hsec)
    letI : TopologicalSpace (OrSpace f' hF'.2) :=
      orTopology (orLocalTransport hX' hbump' hfT' hsec')
    ∃ (Fh : Quot (A.E.OrRel hF hsec) ≃ₜ Quot (A'.E.OrRel hF' hsec'))
      (G : Quot A.X.SmoothRel ≃ₜ Quot A'.X.SmoothRel),
      (∀ c, A'.E.orbitProj hF' hsec' (Fh c) = G (A.E.orbitProj hF hsec c)) ∧
      ⇑Fh = orbitOrMap hFi hF hF' hf' hsec hsec' ∧ ⇑G = smoothOrbitMap hFi := by
  have hΨ := isEquivalence_rep_Ψ hFi
  have hff' := pullback_eq_of_cls' hFi (cls_rep hFi) hF.1 hf'
  obtain ⟨Fh, G, h1, h2, h3⟩ := theorem_12_5_7_one_homeo (rep hFi).hΦ (sbe hΨ) hF hF'
    ((rep hFi).isScFredholm_pullback hF) rfl hff' hsec hsec'
    ((rep hFi).hasScPlusSectionsThrough_B hsec) hX hbump hfT hX' hbump' hfT'
    ((rep hFi).isTame_B hX) ((rep hFi).admitsBumpFunctions_B hbump)
    ((rep hFi).isScFredholmSectionTame_pullback hfT)
  refine ⟨Fh, G, h1, funext fun x => ?_, funext fun v => ?_⟩
  · have hb := (rep hFi).hΦ.orbitOrMap_bijective ((rep hFi).isScFredholm_pullback hF) hF rfl
      ((rep hFi).hasScPlusSectionsThrough_B hsec) hsec
    conv_lhs => rw [← (Equiv.ofBijective _ hb).apply_symm_apply x]
    rw [Equiv.ofBijective_apply, h2]
    rfl
  · have hb := (rep hFi).hΦ.smoothOrbitMap_bijective
    conv_lhs => rw [← (Equiv.ofBijective _ hb).apply_symm_apply v]
    rw [Equiv.ofBijective_apply, h3]
    rfl

/-- **Theorem 12.5.7 (2) for a generalized strong bundle isomorphism**, p. 595 (2017:
Theorem 12.12 (2)), with Part I's hypotheses on `W` and `W'` only, for any representative
`W ←Φ– V –Ψ→ W'` of `f̄`: an orientation `o` of `f` in the sense of Definition 12.5.4 has exactly
one orientation `o'` of `f'` (Definition 12.5.4) corresponding to `o` over `V`. -/
theorem theorem_12_5_7_two_cls {D : SDiagram A A'} (hD : D.cls = F)
    {o : ∀ a (hs : a ∈ A.X.PObj.smoothSet), Orx f hF.2 a hs} :
    haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    haveI := paracompactSpace_rn_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A.B
    haveI := paracompactSpace_rn_prod A'.X.PObj
    haveI := paracompactSpace_rn_pullback A'.B
    haveI := paracompactSpace_rn_rn_prod A'.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A'.B
    A.E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hfT hsec)) o →
    ∃! o' : ∀ x (hs : x ∈ A'.X.PObj.smoothSet), Orx f' hF'.2 x hs,
      A'.E.definition_12_5_4 hF' hsec' (orTopology (orLocalTransport hX' hbump' hfT' hsec')) o' ∧
        ∀ v (hv : v ∈ D.B.X.PObj.smoothSet),
          (sbe (equivalences_Ψ_of_cls hFi hD)).orEqv (D.isScFredholm_pullback hF) hF'
              (pullback_eq_of_cls' hFi hD hF.1 hf') (D.hasScPlusSectionsThrough_B hsec) hsec' v hv
              (o' (D.Ψ.ϕ.obj v) ((sbe (equivalences_Ψ_of_cls hFi hD)).smooth_obj hv)) =
            D.hΦ.orEqv (D.isScFredholm_pullback hF) hF rfl (D.hasScPlusSectionsThrough_B hsec)
              hsec v hv (o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) :=
  theorem_12_5_7_two_book D.hΦ (sbe (equivalences_Ψ_of_cls hFi hD)) hF hF'
    (D.isScFredholm_pullback hF) rfl (pullback_eq_of_cls' hFi hD hF.1 hf') hsec hsec'
    (D.hasScPlusSectionsThrough_B hsec) hX hbump hfT hX' hbump' hfT' (D.isTame_B hX)
    (D.admitsBumpFunctions_B hbump) (D.isScFredholmSectionTame_pullback hfT)

end GenSBMap

end SBLocalization

end Polyfold
