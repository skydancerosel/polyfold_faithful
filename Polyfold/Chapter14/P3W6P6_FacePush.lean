import Polyfold.Chapter14.P3W6P6_FaceTransport
import Polyfold.Chapter10.WeakFibredProductTheorem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.1, **Proposition
14.1.8**, p. 645 (2017: Proposition 14.1): the push-forward hypothesis `FacePush_hyp` of
`P3W5FM_BoundaryPush` holds for strong bundle equivalences, so Proposition 14.1.8 holds without
the two added hypotheses of wave 5.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `exists_localIso_act_p6`: Chapter 10's `exists_localIso_mor` (the action `μ(σ, ·)` of a
  morphism is a local strong bundle isomorphism) with the formula exposed: on an open
  neighbourhood `𝒯` of `σ`, `t(ψ) ∈ U`, `ϕ(t(ψ)) = s(ψ)` and `Ψ(w) = μ(ψ, w)` for `ψ ∈ 𝒯`.
* `facePush_hyp_of_equivalence`: **FM's `FacePush_hyp F` holds for every strong bundle
  equivalence `F`**.  Near `z₀ = Q(u₀)` the pushed section `z ↦ μ(ψ_u, Φ(s(u)))`, `u = Q⁻¹(z)`, is
  `Ψ₂ ∘ s₁ ∘ ϕ₂` for the action of `σ = ψ_{u₀}` (`exists_localIso_act_p6`), where
  `s₁ = Φ ∘ s ∘ F⁻¹` is `s` transported along the local strong bundle isomorphism of `Φ` at
  `u₀`; the key lemma `isFaceScPlusSectionOn_of_localIso` applies twice.
* `proposition_14_1_8` (`f̄_*Λ`) and `proposition_14_1_8_pullMult` (`f̄^*Λ'`): FM's
  `proposition_14_1_8_hyp` / `_pullMult_hyp` with both hypotheses discharged; also
  `PullMap.isBoundaryStructurable_pull` (any `PullMap`, e.g. proper strong bundle coverings) and
  `isBoundaryStructurable_pushMult`.
* `SDiagram.isTame_B_p6`, `proposition_14_1_8_tame`, `proposition_14_1_8_pullMult_tame`: the
  middle of a representative is tame when `X` is (Chapter 10's `isTame_of_isTame`), so the
  statement needs only `X` and `X'` tame, as printed; `GenSBMap.proposition_14_1_8` and
  `GenSBMap.proposition_14_1_8_pullMult`: the class-level statement for
  `f̄ = [W ← V → W']` (`GenSBMap.pushMult`, `GenSBMap.pullMult`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

/-! ### The action of a morphism, with its formula -/

/-- **The action of a morphism `σ` as a local strong bundle isomorphism, with its formula**
(Chapter 10's `EpStrongBundle.exists_localIso_mor`, whose proof is followed): there are
`L : W|U → W|U'` and an open `𝒯 ∋ σ` such that for every `ψ ∈ 𝒯`, `t(ψ) ∈ U`,
`ϕ(t(ψ)) = s(ψ)` and `Ψ(w) = μ(ψ, w)` for `w` over `s(ψ)`. -/
theorem exists_localIso_act_p6 (A : SEP.{u}) (σ : A.Mor) :
    ∃ (U U' : Set A.Obj) (L : StrongBundle.LocalIso A.B A.B U U') (𝒯 : Set A.Mor),
      IsOpen 𝒯 ∧ σ ∈ 𝒯 ∧ ∀ ψ ∈ 𝒯, A.X.tgt ψ ∈ U ∧ L.ϕ (A.X.tgt ψ) = A.X.src ψ ∧
        ∀ w, A.P w = A.X.src ψ → L.Ψ w = fibAct ψ w := by
  obtain ⟨T₁, V₁, τ₁, hσ₁, hτ₁⟩ := A.X.isLocalScDiffeo_src σ
  obtain ⟨T₂, V₂, τ₂, hσ₂, hτ₂⟩ := A.X.isLocalScDiffeo_tgt σ
  have hT : IsOpen (T₁ ∩ T₂) := hτ₁.isOpen_source.inter hτ₂.isOpen_source
  have hs := hτ₁.restrict hT inter_subset_left
  have ht := hτ₂.restrict hT inter_subset_right
  set T := T₁ ∩ T₂ with hTdef
  set U := V₂ ∩ τ₂ ⁻¹' T with hUdef
  set U' := V₁ ∩ τ₁ ⁻¹' T with hU'def
  have hbase : A.X.PObj.IsScDiffeoOn A.X.PObj (A.X.src ∘ τ₂) (A.X.tgt ∘ τ₁) U U' :=
    hs.comp ht.symm
  have hU : IsOpen U := hbase.isOpen_source
  have hU' : IsOpen U' := hbase.isOpen_target
  set α₂ : A.Obj → A.Mor := fun x => A.X.inv (τ₂ x) with hα₂def
  have hα₂ : A.X.PObj.IsScSmoothOn A.X.PMor α₂ U :=
    MPolyfold.IsScSmoothOn.comp A.X.isScSmoothMap_inv ht.isScSmoothOn_inv (mapsTo_univ _ _)
  have hsrc₂ : ∀ x ∈ U, A.X.src (α₂ x) = x := fun x hx => by
    change A.X.src (A.X.inv (τ₂ x)) = x
    rw [A.X.src_inv, ht.right_inv x hx]
  have hα₁ : A.X.PObj.IsScSmoothOn A.X.PMor τ₁ U' := hs.isScSmoothOn_inv
  have hsrc₁ : ∀ x ∈ U', A.X.src (τ₁ x) = x := fun x hx => hs.right_inv x hx
  have hcov : ∀ y, A.P y ∈ U → A.P (A.E.sectionAct α₂ y) = (A.X.src ∘ τ₂) (A.P y) :=
    fun y hy => by
      rw [A.E.P_sectionAct_of_eq α₂ (hsrc₂ _ hy).symm]; exact A.X.tgt_inv _
  have hcov' : ∀ y, A.P y ∈ U' → A.P (A.E.sectionAct τ₁ y) = (A.X.tgt ∘ τ₁) (A.P y) :=
    fun y hy => A.E.P_sectionAct_of_eq τ₁ (hsrc₁ _ hy).symm
  have hmaps : MapsTo (A.E.sectionAct α₂) (A.P ⁻¹' U) (A.P ⁻¹' U') := fun y hy => by
    change A.P (A.E.sectionAct α₂ y) ∈ U'
    rw [hcov y hy]; exact hbase.mapsTo hy
  have hmaps' : MapsTo (A.E.sectionAct τ₁) (A.P ⁻¹' U') (A.P ⁻¹' U) := fun y hy => by
    change A.P (A.E.sectionAct τ₁ y) ∈ U
    rw [hcov' y hy]; exact hbase.mapsTo_inv hy
  have hleft : ∀ y, A.P y ∈ U → A.E.sectionAct τ₁ (A.E.sectionAct α₂ y) = y := fun y hy => by
    have hρ : τ₂ (A.P y) ∈ T := ht.mapsTo_inv hy
    have hy1 : A.P y = A.X.src (α₂ (A.P y)) := (hsrc₂ _ hy).symm
    have hw1 : A.P (A.E.sectionAct α₂ y) = A.X.src (τ₁ (A.P (A.E.sectionAct α₂ y))) :=
      (hsrc₁ _ (hmaps hy)).symm
    have hτρ : τ₁ (A.P (A.E.sectionAct α₂ y)) = τ₂ (A.P y) := by
      rw [hcov y hy]; exact hs.left_inv _ hρ
    have hP' : A.P (A.E.μ ⟨(A.X.inv (τ₂ (A.P y)), y), hy1⟩) = A.X.src (τ₂ (A.P y)) := by
      rw [A.E.P_μ]; exact A.X.tgt_inv _
    rw [A.E.sectionAct_of_eq τ₁ hw1]
    refine (A.E.μ_congr (q' := ⟨(τ₂ (A.P y), A.E.μ ⟨(A.X.inv (τ₂ (A.P y)), y), hy1⟩), hP'⟩)
      ?_).trans (A.E.μ_μ_inv _ y hy1 hP')
    exact Prod.ext hτρ (A.E.sectionAct_of_eq α₂ hy1)
  have hright : ∀ y', A.P y' ∈ U' → A.E.sectionAct α₂ (A.E.sectionAct τ₁ y') = y' :=
    fun y' hy' => by
      have hρ : τ₁ (A.P y') ∈ T := hs.mapsTo_inv hy'
      have hy1 : A.P y' = A.X.src (τ₁ (A.P y')) := (hsrc₁ _ hy').symm
      have hw1 : A.P (A.E.sectionAct τ₁ y') = A.X.src (α₂ (A.P (A.E.sectionAct τ₁ y'))) :=
        (hsrc₂ _ (hmaps' hy')).symm
      have hτρ : α₂ (A.P (A.E.sectionAct τ₁ y')) = A.X.inv (τ₁ (A.P y')) := by
        change A.X.inv (τ₂ (A.P (A.E.sectionAct τ₁ y'))) = _
        rw [hcov' y' hy']; exact congrArg A.X.inv (ht.left_inv _ hρ)
      have hP' : A.P (A.E.μ ⟨(τ₁ (A.P y'), y'), hy1⟩) = A.X.src (A.X.inv (τ₁ (A.P y'))) := by
        rw [A.E.P_μ, A.X.src_inv]
      rw [A.E.sectionAct_of_eq α₂ hw1]
      refine (A.E.μ_congr (q' := ⟨(A.X.inv (τ₁ (A.P y')), A.E.μ ⟨(τ₁ (A.P y'), y'), hy1⟩),
        hP'⟩) ?_).trans (A.E.μ_inv_μ ⟨(τ₁ (A.P y'), y'), hy1⟩ hP')
      exact Prod.ext hτρ (A.E.sectionAct_of_eq τ₁ hy1)
  have hzero : A.B.toMPolyfold0.IsScDiffeoOn A.B.toMPolyfold0 (A.E.sectionAct α₂)
      (A.E.sectionAct τ₁) (A.P ⁻¹' U) (A.P ⁻¹' U') :=
    ⟨A.E.isScSmoothOn_sectionAct hU hα₂ hsrc₂, A.E.isScSmoothOn_sectionAct hU' hα₁ hsrc₁, hmaps,
      hmaps', hleft, hright⟩
  have hone : A.B.toMPolyfold1.IsScDiffeoOn A.B.toMPolyfold1
      (StrongBundle.oneRestrict A.B A.B (A.E.sectionAct α₂) (A.E.mapsTo_oneSet_sectionAct α₂))
      (StrongBundle.oneRestrict A.B A.B (A.E.sectionAct τ₁) (A.E.mapsTo_oneSet_sectionAct τ₁))
      ((A.P ∘ A.B.oneVal) ⁻¹' U) ((A.P ∘ A.B.oneVal) ⁻¹' U') :=
    ⟨A.E.isScSmoothOn_sectionAct_one hU hα₂ hsrc₂, A.E.isScSmoothOn_sectionAct_one hU' hα₁ hsrc₁,
      fun w hw => hmaps hw, fun w hw => hmaps' hw,
      fun w hw => A.B.oneVal_injective (hleft _ hw),
      fun w hw => A.B.oneVal_injective (hright _ hw)⟩
  let L : StrongBundle.LocalIso A.B A.B U U' :=
    { ϕ := A.X.src ∘ τ₂
      g := A.X.tgt ∘ τ₁
      Φ := A.E.sectionAct α₂
      Ψ := A.E.sectionAct τ₁
      Φ₁ := StrongBundle.oneRestrict A.B A.B (A.E.sectionAct α₂) (A.E.mapsTo_oneSet_sectionAct α₂)
      Ψ₁ := StrongBundle.oneRestrict A.B A.B (A.E.sectionAct τ₁) (A.E.mapsTo_oneSet_sectionAct τ₁)
      base := hbase
      zero := hzero
      one := hone
      covers := hcov
      oneVal_Φ₁ := fun _ _ => rfl
      fiber_linear := fun x x' hx hx' =>
        A.E.isLinearMap_sectionAct hsrc₂ hx ((A.X.tgt_inv _).trans hx') }
  refine ⟨U, U', L, T, hT, ⟨hσ₁, hσ₂⟩, fun ψ hψ => ⟨?_, ?_, fun w hw => ?_⟩⟩
  · exact ⟨hτ₂.mapsTo hψ.2, by
      change τ₂ (A.X.tgt ψ) ∈ T
      rw [hτ₂.left_inv ψ hψ.2]; exact hψ⟩
  · change A.X.src (τ₂ (A.X.tgt ψ)) = A.X.src ψ
    rw [hτ₂.left_inv ψ hψ.2]
  · have hτ : τ₁ (A.P w) = ψ := by rw [hw]; exact hτ₁.left_inv ψ hψ.1
    have h1 : A.P w = A.X.src (τ₁ (A.P w)) := by rw [hτ]; exact hw
    change A.E.sectionAct τ₁ w = fibAct ψ w
    rw [A.E.sectionAct_of_eq τ₁ h1, fibAct_of hw]
    exact A.E.μ_congr (Prod.ext hτ rfl)

/-! ### `FacePush_hyp` holds for equivalences -/

variable {A C : SEP.{u}}

/-- **FM's hypothesis `FacePush_hyp F` holds for every strong bundle equivalence `F`**: (1) of
Definition 14.1.3 passes from `s` on `U(x)` to the pushed section `z ↦ μ(ψ_u, Φ(s(u)))` on
`U'(y)`, through the local strong bundle isomorphism of `Φ` and the action of `ψ_u`. -/
theorem facePush_hyp_of_equivalence {F : C ⟶ A} (hF : SEP.equivalences F) : FacePush_hyp F := by
  intro x y T N N' s h hs
  refine isFaceScPlusSectionOn_iff_singleton.2 fun z₀ hz₀ => ?_
  have hu₀ : T.Qinv z₀ ∈ N.bdry := h.Qinv_mem_bdry_fm hF hz₀
  have hu₀W : T.Qinv z₀ ∈ T.W := h.Qinv_mem_W hz₀.1
  -- step 1: `s₁ = Φ ∘ s ∘ F⁻¹` near `F(u₀)`
  obtain ⟨U₁, U₁', hu₀U₁, hi⟩ := (PullMap.ofEquivalence hF).isLocalIso (T.Qinv z₀)
  set L₁ := hi.toLocalIso with hL₁
  have hFu₀ : (SEP.Hom.ϕ F).obj (T.Qinv z₀) ∈ A.X.PObj.boundary :=
    ((PullMap.ofEquivalence hF).mem_boundary_iff _).2 hu₀.2
  have hstep1 : IsFaceScPlusSectionOn A (L₁.Φ ∘ s ∘ L₁.g)
      {(SEP.Hom.ϕ F).obj (T.Qinv z₀)} := by
    refine isFaceScPlusSectionOn_of_localIso L₁.symm L₁.isOpen_U' (L₁.base.mapsTo hu₀U₁)
      subset_rfl hFu₀ (fun _ _ => rfl) ?_
    change IsFaceScPlusSectionOn C s {L₁.g (L₁.ϕ (T.Qinv z₀))}
    rw [L₁.base.left_inv _ hu₀U₁]
    exact hs.mono (singleton_subset_iff.2 hu₀)
  -- step 2: the action of `σ = ψ_{u₀}`
  obtain ⟨U₂, U₂', L₂, 𝒯, h𝒯o, hσ𝒯, h𝒯⟩ := exists_localIso_act_p6 A (T.ψ (T.Qinv z₀))
  have hQc : ContinuousOn T.Qinv N'.U :=
    T.isScDiffeoOn_Q.isScSmoothOn_inv.continuousOn.mono h.subset_W'
  have hψc : ContinuousOn (T.ψ ∘ T.Qinv) N'.U :=
    T.isScSmoothOn_ψ.continuousOn.comp hQc fun z hz => h.Qinv_mem_W hz
  have hGo : IsOpen ((N'.U ∩ T.Qinv ⁻¹' U₁) ∩ (T.ψ ∘ T.Qinv) ⁻¹' 𝒯) :=
    (hψc.mono inter_subset_left).isOpen_inter_preimage
      (hQc.isOpen_inter_preimage N'.isOpen_U L₁.isOpen_U) h𝒯o
  have hGU₂ : (N'.U ∩ T.Qinv ⁻¹' U₁) ∩ (T.ψ ∘ T.Qinv) ⁻¹' 𝒯 ⊆ U₂ := fun z hz => by
    have := (h𝒯 (T.ψ (T.Qinv z)) hz.2).1
    rwa [h.tgt_ψ_Qinv hz.1.1] at this
  refine isFaceScPlusSectionOn_of_localIso L₂ (s' := L₁.Φ ∘ s ∘ L₁.g) hGo
    ⟨⟨hz₀.1, hu₀U₁⟩, hσ𝒯⟩ hGU₂ hz₀.2 ?_ ?_
  · rintro z ⟨hz, hzb⟩
    have hu : T.Qinv z ∈ N.bdry := h.Qinv_mem_bdry_fm hF ⟨hz.1.1, hzb⟩
    have hsu : C.P (s (T.Qinv z)) = T.Qinv z := (hs.1 _ hu).1
    obtain ⟨-, hϕ, hΨ⟩ := h𝒯 (T.ψ (T.Qinv z)) hz.2
    have ht : A.X.tgt (T.ψ (T.Qinv z)) = z := h.tgt_ψ_Qinv hz.1.1
    have hsrc : A.X.src (T.ψ (T.Qinv z)) = (SEP.Hom.ϕ F).obj (T.Qinv z) :=
      T.src_ψ _ (h.Qinv_mem_W hz.1.1)
    rw [ht] at hϕ
    change pushSec T s z = L₂.Ψ ((L₁.Φ ∘ s ∘ L₁.g) (L₂.ϕ z))
    have e1 : (L₁.Φ ∘ s ∘ L₁.g) (L₂.ϕ z) = (SEP.Hom.Φ F).obj (s (T.Qinv z)) := by
      rw [hϕ, hsrc]
      change L₁.Φ (s (L₁.g (L₁.ϕ (T.Qinv z)))) = _
      rw [L₁.base.left_inv _ hz.1.2]
      rfl
    rw [e1, h.pushSec_eq_fm hF hz.1.1 hsu, hΨ _ (h.P_obj_fm hF hz.1.1 hsu)]
  · have e := (h𝒯 _ hσ𝒯).2.1
    rw [h.tgt_ψ_Qinv hz₀.1, T.src_ψ _ hu₀W] at e
    rw [e]
    exact hstep1

/-! ### Proposition 14.1.8 -/

/-- Pull-backs of structurable sc⁺-multisections over `∂X'` along any `PullMap` (strong bundle
equivalences, proper strong bundle coverings) are structurable over `∂X` (tame `X`): FM's
`isBoundaryStructurable_pull_hyp` with `FacePull_hyp` proved. -/
theorem PullMap.isBoundaryStructurable_pull (M : PullMap C A) (hX : C.X.IsTame)
    {Λ' : A.W → ℚ≥0} (h : IsBoundaryStructurable A Λ') :
    IsBoundaryStructurable C (M.pull Λ') :=
  M.isBoundaryStructurable_pull_hyp hX M.facePull_hyp h

/-- Push-forwards of structurable sc⁺-multisections over `∂X` along a strong bundle equivalence
are structurable over `∂X'` (tame `X'`): FM's `isBoundaryStructurable_pushMult_hyp` with
`FacePush_hyp` proved. -/
theorem isBoundaryStructurable_pushMult {F : C ⟶ A} (hF : SEP.equivalences F)
    (hA : A.X.IsTame) {Λ : C.W → ℚ≥0} (h : IsBoundaryStructurable C Λ) :
    IsBoundaryStructurable A (pushMult F hF Λ) :=
  isBoundaryStructurable_pushMult_hyp hF hA (facePush_hyp_of_equivalence hF) h

/-- **2021 Proposition 14.1.8, p. 645 (2017: Proposition 14.1), `f̄_*Λ`**: for a representative
`W ←Φ V →Ψ W'` (`D`) of a generalized strong bundle isomorphism with `V` over a tame ep-groupoid
and `X'` tame, and `Λ` structurable over `∂X`, `f̄_*Λ = Ψ_*Φ^*Λ` is structurable over `∂X'`.
No added hypothesis beyond the tame middle of the representative (the text's proof takes such a
representative). -/
theorem proposition_14_1_8 {A A' : SEP.{u}} (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
    (hB : D.B.X.IsTame) (hA' : A'.X.IsTame) {Λ : A.W → ℚ≥0} (h : IsBoundaryStructurable A Λ) :
    IsBoundaryStructurable A' (D.pushMult hΨ Λ) :=
  proposition_14_1_8_hyp D hΨ hB hA' (PullMap.facePull_hyp _) (facePush_hyp_of_equivalence hΨ) h

/-- **2021 Proposition 14.1.8, `f̄^*Λ'`**: `f̄^*Λ' = Φ_*Ψ^*Λ'` is structurable over `∂X` for
`Λ'` structurable over `∂X'` (`X` and the middle of the representative tame). -/
theorem proposition_14_1_8_pullMult {A A' : SEP.{u}} (D : SDiagram A A')
    (hΨ : SEP.equivalences D.Ψ) (hB : D.B.X.IsTame) (hA : A.X.IsTame)
    {Λ' : A'.W → ℚ≥0} (h : IsBoundaryStructurable A' Λ') :
    IsBoundaryStructurable A (D.pullMult hΨ Λ') :=
  proposition_14_1_8_pullMult_hyp D hΨ hB hA (PullMap.facePull_hyp _)
    (facePush_hyp_of_equivalence D.isEquivalence_Φ) h

/-! ### Tame endpoints suffice; the class-level statement -/

/-- The middle `V` of a representative `W ←Φ V →Ψ W'` is tame when `X` is: `Φ` covers an
equivalence of ep-groupoids (Chapter 10's `EpFunctor.IsEquivalence.isTame_of_isTame`). -/
theorem SDiagram.isTame_B_p6 {A A' : SEP.{u}} (D : SDiagram A A') (hA : A.X.IsTame) :
    D.B.X.IsTame :=
  EpFunctor.IsEquivalence.isTame_of_isTame D.isEquivalence_Φ.isEquivalence_base hA

/-- **2021 Proposition 14.1.8, `f̄_*Λ`, with the text's hypotheses**: for a representative
`W ←Φ V →Ψ W'` of a generalized strong bundle isomorphism between strong bundles over tame
ep-groupoids, `f̄_*Λ` is structurable over `∂X'` for `Λ` structurable over `∂X`. -/
theorem proposition_14_1_8_tame {A A' : SEP.{u}} (D : SDiagram A A')
    (hΨ : SEP.equivalences D.Ψ) (hA : A.X.IsTame) (hA' : A'.X.IsTame) {Λ : A.W → ℚ≥0}
    (h : IsBoundaryStructurable A Λ) : IsBoundaryStructurable A' (D.pushMult hΨ Λ) :=
  proposition_14_1_8 D hΨ (D.isTame_B_p6 hA) hA' h

/-- **2021 Proposition 14.1.8, `f̄^*Λ'`, with the text's hypotheses** (tame `X`, `X'`). -/
theorem proposition_14_1_8_pullMult_tame {A A' : SEP.{u}} (D : SDiagram A A')
    (hΨ : SEP.equivalences D.Ψ) (hA : A.X.IsTame) {Λ' : A'.W → ℚ≥0}
    (h : IsBoundaryStructurable A' Λ') : IsBoundaryStructurable A (D.pullMult hΨ Λ') :=
  proposition_14_1_8_pullMult D hΨ (D.isTame_B_p6 hA) hA h

namespace GenSBMap

variable {A A' : SEP.{u}} {f : GenSBMap A A'} (hf : f.IsGeneralizedIso)

/-- **2021 Proposition 14.1.8, p. 645 (2017: Proposition 14.1)**, class level: for a generalized
strong bundle isomorphism `f̄ : W → W'` between strong bundles over tame ep-groupoids and `Λ`
structurable over `∂X`, `f̄_*Λ` is structurable over `∂X'`. -/
theorem proposition_14_1_8 (hA : A.X.IsTame) (hA' : A'.X.IsTame) {Λ : A.W → ℚ≥0}
    (h : IsBoundaryStructurable A Λ) : IsBoundaryStructurable A' (pushMult hf Λ) :=
  proposition_14_1_8_tame (rep hf) (isEquivalence_rep_Ψ hf) hA hA' h

/-- **2021 Proposition 14.1.8**, class level, `f̄^*Λ'`: structurable over `∂X` for `Λ'`
structurable over `∂X'` (tame `X`; `X'` enters only through `Λ'`). -/
theorem proposition_14_1_8_pullMult (hA : A.X.IsTame) {Λ' : A'.W → ℚ≥0}
    (h : IsBoundaryStructurable A' Λ') : IsBoundaryStructurable A (pullMult hf Λ') :=
  proposition_14_1_8_pullMult_tame (rep hf) (isEquivalence_rep_Ψ hf) hA h

end GenSBMap

end SBLocalization

end Polyfold
