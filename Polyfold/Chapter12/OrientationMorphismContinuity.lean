import Polyfold.Chapter12.OrientationLocalCommute
import Polyfold.Chapter12.OrientationOrbit

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
p. 594: **Theorem 12.5.3** (2017: Theorem 12.11), the last sentence.

# Morphisms keep continuous local orientations continuous

For a morphism `σ : x → x'` between smooth objects, the local strong bundle isomorphism of its
sheet (`E.morIso σ : W|t(sheet) → W|s(sheet)`, the inverse of the text's `Φ̂`) carries a
continuous orientation `o` over an open `V ∋ x` (Part I's `IsContOrOn`) to a continuous
orientation over the open neighbourhood `t(sheet) ∩ ϕ⁻¹(V)` of `x'`, whose value at `x'` is
`σ_* o_x` (`orMor`, Lemma 12.5.1).

* `EpStrongBundle.pullOrx_morIso_tgt`: the value at `x'` is `σ_* o_x`.
* `EpStrongBundle.theorem_12_5_3_push_hyp`: the statement with the instance arguments of Part I's
  transport; `EpStrongBundle.theorem_12_5_3_push`: without them, with Part I's hypotheses
  (tame `X`, bump functions, tame germ data), as `theorem_12_5_3_hyp`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

section Mor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B) {f : Obj → W}
  (hF : E.IsScFredholmSectionFunctor f) (hsec : B.HasScPlusSectionsThrough)

include hF in
/-- `f = Ψ ∘ f ∘ ϕ` for the isomorphism of a morphism (functoriality). -/
theorem eqOn_morIso_of_functor (σ : Mor) :
    EqOn f ((E.morIso σ).Ψ ∘ f ∘ (E.morIso σ).ϕ) (X.sheetAt σ).tgtSet :=
  E.eqOn_morIso σ _ (E.functorial_of_isScFredholmSectionFunctor hF)

/-- **The carried section at `t(σ)` is `σ_*` of the value at `s(σ)`.** -/
theorem pullOrx_morIso_tgt (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet)
    (o : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy) :
    (E.morIso σ).pullOrx hF.2 hF.2 (E.eqOn_morIso_of_functor hF σ) hsec hsec o x' hs' =
      E.orMor hF hsec σ hx hx' hs hs' (o x hs) := by
  rw [StrongBundle.LocalIso.pullOrx, dif_pos (mem_tgtSet hx')]
  have hϕ : (E.morIso σ).ϕ x' = x := E.morIso_ϕ_eq hx hx'
  subst hϕ
  rw [StrongBundle.LocalIso.orxVia_eq_morVia _ _ _ _ _ _ _ _
    (restrPt B _ (isOpen_srcSet σ) (mem_srcSet hx) hs) (restrPt_sub _ _ _ _)]
  rfl

section Push

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]

/-- **Theorem 12.5.3, last sentence**, p. 594 (2017: Theorem 12.11), with the instance arguments
of Part I's transport: for a morphism `σ : x → x'` between smooth objects and a continuous
orientation `o` of `f` over an open `V` (`IsContOrOn` for Part I's transport), the section
carried by the local isomorphism of `σ` is a continuous orientation over
`t(sheet) ∩ ϕ⁻¹(V)`, an open set containing `x'` when `x ∈ V`, and its value at `x'` is
`σ_* o_x`. -/
theorem theorem_12_5_3_push_hyp (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions)
    (hfT : B.IsScFredholmSectionTame f) (σ : Mor) {x x' : Obj} (hx : X.src σ = x)
    (hx' : X.tgt σ = x') (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet)
    {V : Set Obj} {o : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy}
    (ho : IsContOrOn (orLocalTransport hX hbump hfT hsec) V o) :
    IsContOrOn (orLocalTransport hX hbump hfT hsec)
        ((X.sheetAt σ).tgtSet ∩ (E.morIso σ).ϕ ⁻¹' V)
        ((E.morIso σ).pullOrx hF.2 hF.2 (E.eqOn_morIso_of_functor hF σ) hsec hsec o) ∧
      (x ∈ V → x' ∈ (X.sheetAt σ).tgtSet ∩ (E.morIso σ).ϕ ⁻¹' V) ∧
      (E.morIso σ).pullOrx hF.2 hF.2 (E.eqOn_morIso_of_functor hF σ) hsec hsec o x' hs' =
        E.orMor hF hsec σ hx hx' hs hs' (o x hs) :=
  ⟨(E.morIso σ).isContOrOn_pullOrx hX hbump hfT hsec hX hbump hfT hsec
      (E.eqOn_morIso_of_functor hF σ) ho,
    fun hxV => ⟨mem_tgtSet hx', by rw [mem_preimage, E.morIso_ϕ_eq hx hx']; exact hxV⟩,
    E.pullOrx_morIso_tgt hF hsec σ hx hx' hs hs' o⟩

end Push

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- **Theorem 12.5.3, last sentence**, p. 594 (2017: Theorem 12.11), with Part I's hypotheses
(tame `X`, bump functions, tame germ data, as `theorem_12_5_3_hyp`) and no instance arguments:
the local isomorphism of a morphism `σ : x → x'` carries a continuous orientation over an open
`V ∋ x` to a continuous orientation over an open neighbourhood of `x'` with value `σ_* o_x`. -/
theorem theorem_12_5_3_push [ParacompactSpace (pullbackSpace P X.src)]
    (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions)
    (hfT : B.IsScFredholmSectionTame f) (hF : E.IsScFredholmSectionFunctor f) (σ : Mor)
    {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x') (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) {V : Set Obj}
    {o : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy} :
    haveI := paracompactSpace_rn_prod X.PObj
    haveI := paracompactSpace_rn_pullback B
    haveI := paracompactSpace_rn_rn_prod X.PObj
    haveI := paracompactSpace_rn_rn_pullback B
    IsContOrOn (orLocalTransport hX hbump hfT hbump.hasScPlusSectionsThrough) V o → x ∈ V →
      ∃ V' : Set Obj, x' ∈ V' ∧
        IsContOrOn (orLocalTransport hX hbump hfT hbump.hasScPlusSectionsThrough) V'
          ((E.morIso σ).pullOrx hF.2 hF.2 (E.eqOn_morIso_of_functor hF σ)
            hbump.hasScPlusSectionsThrough hbump.hasScPlusSectionsThrough o) ∧
        (E.morIso σ).pullOrx hF.2 hF.2 (E.eqOn_morIso_of_functor hF σ)
            hbump.hasScPlusSectionsThrough hbump.hasScPlusSectionsThrough o x' hs' =
          E.orMor hF hbump.hasScPlusSectionsThrough σ hx hx' hs hs' (o x hs) := by
  have := paracompactSpace_rn_prod X.PObj
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_rn_prod X.PObj
  have := paracompactSpace_rn_rn_pullback B
  intro ho hxV
  obtain ⟨h1, h2, h3⟩ := E.theorem_12_5_3_push_hyp hF hbump.hasScPlusSectionsThrough hX hbump hfT
    σ hx hx' hs hs' ho
  exact ⟨_, h2 hxV, h1, h3⟩

end EpStrongBundle

end Mor

end Polyfold
