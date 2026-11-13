import Polyfold.Chapter10.StrongBundleLocalizationCategory
import Polyfold.Chapter10.GapP2_GBundleLR

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.5: **Remark 10.5.3** (2021 p. 506, new in the 2021 edition), the strong
bundle version of **Theorem 10.3.10** (2021 p. 489; 2017: Theorem 10.4, p. 353), the converse
direction.

# Isomorphisms of `SEP(F⁻¹)` are generalized strong bundle isomorphisms

## The text, paraphrased

(Remark 10.5.3) For ep-groupoids, Theorem 10.3.10 shows that `[X ←F A →G Y]` is a generalized
isomorphism iff `G` is an equivalence; in the strong bundle case "a similar result can be
proved", and Definition 10.5.2 builds it in: a generalized strong bundle isomorphism is a class
`[W ←Φ W'' →Ψ W']` with `Φ` and `Ψ` strong bundle equivalences.

## What is formalized

* **`SBLocalization.SEPLoc.equivalences_Ψ_of_isIso`**: if `[W ←Φ W'' →Ψ W']` is an isomorphism
  of `SEP(F⁻¹)`, then `Ψ` is a strong bundle equivalence (Definition 10.4.1).
* **`SEPLoc.isIso_homMk_iff`** (`[D]` is an isomorphism iff `Ψ` is a strong bundle equivalence)
  and **`SEPLoc.isIso_iff_isGeneralizedIso`** (the isomorphisms of `SEP(F⁻¹)` are exactly the
  generalized strong bundle isomorphisms of Definition 10.5.2).  The other direction is
  `SEPLoc.theorem_10_3_10` of `StrongBundleLocalizationCategory.lean`.
* Tools: `SEP.FibInj`, `FibInjAt` (with `FibInj.of_natEquiv`, `FibInjAt.of_mor`),
  `SDiagram.fibInj_Ψ_of_equiv`, `SDiagram.exists_natEquiv_of_equiv`,
  `SEP.isStrongBundleIsoOn_of_rightInv`, `SEP.exists_isStrongBundleIsoOn`,
  `SEP.isLocalStrongBundleIso_mor_of_obj`, `SEP.full_total`, `SEP.isEquivalence_total`,
  `SEP.NatEquiv.oneOrbitMap_eq`, `SEP.isHomeomorph_oneOrbitMap_of`,
  `EpGroupoid.exists_eqOn_of_src`.
* The saturation step, **`SEP.equivalences_of_natEquiv_comp`**: a strong bundle functor
  `Ψ : W'' → W'` is a strong bundle equivalence as soon as (a) it covers an equivalence,
  (b) it is injective on the fibres (`SEP.FibInj`), and (c) `Ψ ∘ G` is naturally equivalent to a
  strong bundle equivalence `K` for some strong bundle functor `G`.

## The proof

Let `[E] = [W' ←Φ' V'' →Ψ' W]` be the inverse.  (a) is `isEquivalence_base_of_isIso`.
(b): `[D] ∘ [E] = 1` gives a strong bundle equivalence `H` into the middle `W'' ×_{W'} V''` with
`Ψ' ∘ ΠV'' ∘ H` naturally equivalent to a strong bundle equivalence; as `ΠV''(m)` is determined
by `Ψ(ΠW''(m))` (`compRight_obj_eq`), `Ψ` is injective on the fibres over the points
`ΠW''(H(c))`, and by transport along morphisms on all fibres.  (c): `[E] ∘ [D] = 1` gives `H`
into `V'' ×_W W''` with `Ψ ∘ (ΠW'' ∘ H)` naturally equivalent to a strong bundle equivalence.

The saturation step: `g` (covered by `G`) is an equivalence, so every `x` is the target of some
`γ : g(c) → x`.  The text's transport along `γ` (`isLocalIso₂_lrAct`) gives `G' = H_γ̂ ∘ G`, and
`Ψ ∘ G'` is the transport `v ↦ μ'(ψ(γ̂) ∘ τ, K(v))` of the strong bundle equivalence `K`, a local
strong bundle isomorphism near `c` (`IsStrongBundleEquivalence.exists_transport`).  So
`Θ = G' ∘ (Ψ ∘ G')⁻¹` is a local right inverse of `Ψ`, at levels `[0]` and `[1]`, near `ψ(x)`;
with the fibrewise injectivity and the local injectivity of `ψ`, `Ψ` is a strong bundle
isomorphism near `x` (`isStrongBundleIsoOn_of_rightInv`).  On morphisms this follows through the
pull-back projections (as for `isStrongBundleEquivalence_pullbackProjFunctor`).  The total
functor is then an equivalence (Lemma 10.1.2), and `|Ψ| : |W''[1]| → |W'[1]|` is a continuous
bijection with the continuous inverse `|G| ∘ |K|⁻¹`.

## The choices made

* The fibrewise injectivity is obtained from the composite `[D] ∘ [E]`, the local inverses from
  `[E] ∘ [D]`; this replaces the claims (C1), (C2) of Appendix 10.6.2 (pp. 515–519), which the
  text does not restate for strong bundles.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### `act` and `lrAct` -/

namespace EpStrongBundle

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)] {E : EpStrongBundle X B}

theorem act_eq_lrAct {γ : Mor} {w : W} (h : P w = X.src γ) : E.act γ w = E.lrAct γ w := by
  rw [act_eq h, lrAct_eq h]

end EpStrongBundle

/-! ### Fibrewise injectivity -/

namespace SEP

open EpStrongBundle

variable {A A' A'' : SEP.{u}}

/-- `F` is **injective on the fibres**: `F(w₁) = F(w₂)` and `P(w₁) = P(w₂)` give `w₁ = w₂`. -/
def FibInj (F : A ⟶ A') : Prop :=
  ∀ ⦃w₁ w₂ : A.W⦄, A.P w₁ = A.P w₂ → (Hom.Φ F).obj w₁ = (Hom.Φ F).obj w₂ → w₁ = w₂

/-- `F` is injective on the fibre over `x`. -/
def FibInjAt (F : A ⟶ A') (x : A.Obj) : Prop :=
  ∀ ⦃w₁ w₂ : A.W⦄, A.P w₁ = x → A.P w₂ = x → (Hom.Φ F).obj w₁ = (Hom.Φ F).obj w₂ → w₁ = w₂

theorem fibInj_iff (F : A ⟶ A') : FibInj F ↔ ∀ x, FibInjAt F x :=
  ⟨fun h _ _ _ h₁ h₂ he => h (h₁.trans h₂.symm) he, fun h _ _ hP he => h _ hP rfl he⟩

/-- Strong bundle equivalences are injective on the fibres. -/
theorem fibInj_of_equivalences {F : A ⟶ A'} (hF : equivalences F) : FibInj F :=
  fun _ _ hP he => IsStrongBundleEquivalence.eq_of_obj_eq hF hP he

theorem FibInj.of_comp {F : A ⟶ A'} {G : A' ⟶ A''} (h : FibInj (F ≫ G)) : FibInj F :=
  fun _ _ hP he => h hP (by change (Hom.Φ G).obj _ = (Hom.Φ G).obj _; rw [he])

/-- Fibrewise injectivity passes to naturally equivalent strong bundle functors
(`Ψ(w) = τ(P w) · Φ(w)`). -/
theorem FibInj.of_natEquiv {F G : A ⟶ A'} (h : NatEquiv F G) (hF : FibInj F) : FibInj G := by
  obtain ⟨θ⟩ := h
  intro w₁ w₂ hP he
  have hs : ∀ w, A'.P ((Hom.Φ F).obj w) = A'.X.src (θ.τ.app (A.P w)) := fun w => by
    rw [θ.τ.src_app, (Hom.isStrongBundleFunctor F).isStrongBundleMap_obj.covers]
  rw [StrongBundleNatTrans.obj_eq_act θ, StrongBundleNatTrans.obj_eq_act θ,
    act_eq_lrAct (hs w₁), act_eq_lrAct (hs w₂), hP] at he
  refine hF hP ?_
  have e := congrArg (A'.E.lrAct (A'.X.inv (θ.τ.app (A.P w₂)))) he
  rwa [lrAct_inv_lrAct (by rw [← hP]; exact hs w₁), lrAct_inv_lrAct (hs w₂)] at e

/-- **Transport of fibrewise injectivity along a morphism** `γ : a → b` (by (10.14)). -/
theorem FibInjAt.of_mor {F : A ⟶ A'} {a b : A.Obj} (h : FibInjAt F a) {γ : A.Mor}
    (hs : A.X.src γ = a) (ht : A.X.tgt γ = b) : FibInjAt F b := by
  intro w₁ w₂ h₁ h₂ he
  have hF := Hom.isStrongBundleFunctor F
  have hi : ∀ w, A.P w = b → A.P w = A.X.src (A.X.inv γ) := fun w hw => by
    rw [A.X.src_inv, ht, hw]
  have hP : ∀ w, A.P w = b → A.P (A.E.lrAct (A.X.inv γ) w) = a := fun w hw => by
    rw [P_lrAct (hi w hw), A.X.tgt_inv, hs]
  have e : A.E.lrAct (A.X.inv γ) w₁ = A.E.lrAct (A.X.inv γ) w₂ := h (hP w₁ h₁) (hP w₂ h₂) (by
    rw [hF.obj_lrAct (hi w₁ h₁), hF.obj_lrAct (hi w₂ h₂), he])
  have e' := congrArg (A.E.lrAct γ) e
  rwa [lrAct_lrAct_inv (hi w₁ h₁), lrAct_lrAct_inv (hi w₂ h₂)] at e'

end SEP

/-! ### Two local tools -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
  {M : Type*} [TopologicalSpace M]

/-- Two families of morphisms, continuous on an open `N`, with the same sources on `N` and equal
at `p₀`, agree near `p₀` (`s` is a local homeomorphism). -/
theorem exists_eqOn_of_src {f₁ f₂ : M → Mor} {N : Set M} (hN : IsOpen N) (h₁ : ContinuousOn f₁ N)
    (h₂ : ContinuousOn f₂ N) (hs : ∀ p ∈ N, X.src (f₁ p) = X.src (f₂ p)) {p₀ : M} (hp₀ : p₀ ∈ N)
    (he : f₁ p₀ = f₂ p₀) :
    ∃ N' : Set M, N' ⊆ N ∧ IsOpen N' ∧ p₀ ∈ N' ∧ ∀ p ∈ N', f₁ p = f₂ p := by
  obtain ⟨U, hU, hmem, hinj⟩ := (X.isLocalScDiffeo_src.at (f₁ p₀)).exists_injOn
  have o₁ : IsOpen (N ∩ f₁ ⁻¹' U) := h₁.isOpen_inter_preimage hN hU
  have o₂ : IsOpen (N ∩ f₂ ⁻¹' U) := h₂.isOpen_inter_preimage hN hU
  refine ⟨(N ∩ f₁ ⁻¹' U) ∩ (N ∩ f₂ ⁻¹' U), fun p hp => hp.1.1, o₁.inter o₂,
    ⟨⟨hp₀, hmem⟩, hp₀, by rw [mem_preimage, ← he]; exact hmem⟩, fun p hp => ?_⟩
  exact hinj hp.1.2 hp.2.2 (hs p hp.1.1)

end EpGroupoid

namespace SEP

open EpStrongBundle

variable {A A' : SEP.{u}}

/-- **A local strong bundle isomorphism from a local right inverse.**  Let `Ψ` be injective on
the fibres and `ψ` a local sc-diffeomorphism at `x`.  If near `ψ(x)` there are an sc-smooth `r`
with `ψ ∘ r = 1`, `r(ψ(x)) = x`, and a map `Θ`, sc-smooth at levels `[0]` and `[1]`, covering `r`,
with `Ψ ∘ Θ = 1`, then `Ψ` is a strong bundle isomorphism over a neighbourhood of `x`. -/
theorem isStrongBundleIsoOn_of_rightInv (Ψ : A ⟶ A') (hinj : FibInj Ψ) {x : A.Obj}
    (hψ : A.X.PObj.IsLocalScDiffeoAt A'.X.PObj (Hom.ϕ Ψ).obj x)
    {N' : Set A'.Obj} {r : A'.Obj → A.Obj} {Θ : A'.W → A.W}
    (hr : A'.X.PObj.IsScSmoothOn A.X.PObj r N') (hxN : (Hom.ϕ Ψ).obj x ∈ N')
    (hrx : r ((Hom.ϕ Ψ).obj x) = x) (hψr : ∀ y ∈ N', (Hom.ϕ Ψ).obj (r y) = y)
    (hΘ : A'.B.toMPolyfold0.IsScSmoothOn A.B.toMPolyfold0 Θ (A'.P ⁻¹' N'))
    (hΘP : ∀ w, A'.P w ∈ N' → A.P (Θ w) = r (A'.P w))
    (hΨΘ : ∀ w, A'.P w ∈ N' → (Hom.Φ Ψ).obj (Θ w) = w)
    (Θ₁ : A'.B.One → A.B.One)
    (hΘ₁ : ∀ y, A'.P (A'.B.oneVal y) ∈ N' → A.B.oneVal (Θ₁ y) = Θ (A'.B.oneVal y))
    (hΘ₁s : A'.B.toMPolyfold1.IsScSmoothOn A.B.toMPolyfold1 Θ₁ ((A'.P ∘ A'.B.oneVal) ⁻¹' N')) :
    ∃ (U : Set A.Obj) (U' : Set A'.Obj), x ∈ U ∧
      A.B.IsStrongBundleIsoOn A'.B (Hom.isStrongBundleFunctor Ψ).isStrongBundleMap_obj U U' := by
  have hb := (Hom.isStrongBundleFunctor Ψ).isStrongBundleMap_obj
  obtain ⟨V, hV, hxV, hinjV⟩ := hψ.exists_injOn
  have hN'o : IsOpen N' := hr.isOpen
  have hV' : IsOpen (N' ∩ r ⁻¹' V) := hr.continuousOn.isOpen_inter_preimage hN'o hV
  set U := V ∩ (Hom.ϕ Ψ).obj ⁻¹' (N' ∩ r ⁻¹' V) with hUdef
  have hU : IsOpen U := hV.inter (hV'.preimage (Hom.ϕ Ψ).continuous_obj')
  have hrψ : ∀ u ∈ U, r ((Hom.ϕ Ψ).obj u) = u := fun u hu =>
    hinjV hu.2.2 hu.1 (hψr _ hu.2.1)
  set U' := N' ∩ r ⁻¹' U with hU'def
  have hU' : IsOpen U' := hr.continuousOn.isOpen_inter_preimage hN'o hU
  have hxU : x ∈ U := ⟨hxV, hxN, by rw [mem_preimage, hrx]; exact hxV⟩
  have base : A.X.PObj.IsScDiffeoOn A'.X.PObj (Hom.ϕ Ψ).obj r U U' :=
    ⟨(Hom.ϕ Ψ).isScSmoothMap_obj.mono hU (subset_univ _), hr.mono hU' inter_subset_left,
      fun u hu => ⟨hu.2.1, by rw [mem_preimage, hrψ u hu]; exact hu⟩, fun y hy => hy.2, hrψ,
      fun y hy => hψr y hy.1⟩
  have hli : ∀ w, A.P w ∈ U → Θ ((Hom.Φ Ψ).obj w) = w := fun w hw => by
    have hm : A'.P ((Hom.Φ Ψ).obj w) ∈ N' := by rw [hb.covers]; exact hw.2.1
    exact hinj (by rw [hΘP _ hm, hb.covers, hrψ _ hw]) (hΨΘ _ hm)
  have zero : A.B.toMPolyfold0.IsScDiffeoOn A'.B.toMPolyfold0 (Hom.Φ Ψ).obj Θ
      (A.P ⁻¹' U) (A'.P ⁻¹' U') :=
    ⟨hb.isScSmoothMap.mono (hU.preimage A.B.continuous) (subset_univ _),
      hΘ.mono (hU'.preimage A'.B.continuous) (preimage_mono inter_subset_left),
      fun w hw => by change A'.P _ ∈ U'; rw [hb.covers]; exact base.mapsTo hw,
      fun w hw => by change A.P _ ∈ U; rw [hΘP w hw.1]; exact base.mapsTo_inv hw,
      hli, fun w hw => hΨΘ w hw.1⟩
  have hc : Continuous (A.P ∘ A.B.oneVal) := A.B.continuous.comp A.B.continuous_oneVal
  have hc' : Continuous (A'.P ∘ A'.B.oneVal) := A'.B.continuous.comp A'.B.continuous_oneVal
  refine ⟨U, U', hxU, ⟨r, base⟩, ⟨Θ, zero⟩, ⟨Θ₁, ?_⟩⟩
  refine ⟨hb.isScSmoothMap_one.mono (hU.preimage hc) (subset_univ _),
    hΘ₁s.mono (hU'.preimage hc') (preimage_mono inter_subset_left), fun y hy => ?_,
    fun y hy => ?_, fun y hy => A.B.oneVal_injective ?_, fun y hy => A'.B.oneVal_injective ?_⟩
  · change A'.P (A'.B.oneVal (StrongBundle.oneRestrict _ _ _ _ y)) ∈ U'
    rw [StrongBundle.oneVal_oneRestrict]; exact zero.mapsTo hy
  · change A.P (A.B.oneVal (Θ₁ y)) ∈ U
    rw [hΘ₁ y hy.1]; exact zero.mapsTo_inv hy
  · have hm : A'.P (A'.B.oneVal (StrongBundle.oneRestrict _ _ _ hb.mapsTo_oneSet y)) ∈ N' := by
      rw [StrongBundle.oneVal_oneRestrict]; exact (zero.mapsTo hy).1
    rw [hΘ₁ _ hm, StrongBundle.oneVal_oneRestrict]; exact hli _ hy
  · rw [StrongBundle.oneVal_oneRestrict, hΘ₁ y hy.1]; exact hΨΘ _ hy.1

end SEP

/-! ### The local strong bundle isomorphisms -/

namespace SEP

open EpStrongBundle

variable {A A' C : SEP.{u}}

/-- **The local step of the saturation**: if `Ψ` is injective on the fibres, covers an
equivalence `ψ`, and `Ψ ∘ G` is naturally equivalent to a strong bundle equivalence `K`, then
`Ψ` is a strong bundle isomorphism over a neighbourhood of every point.  For `γ : g(c) → x`, the
transport `G' = H_γ̂ ∘ G` satisfies `Ψ ∘ G' = μ'(ψ(γ̂) ∘ τ, K)`, a local strong bundle isomorphism
near `c` (`exists_transport`), and `G' ∘ (Ψ ∘ G')⁻¹` is a local right inverse of `Ψ`. -/
theorem exists_isStrongBundleIsoOn (Ψ : A ⟶ A') (hψ : (Hom.ϕ Ψ).IsEquivalence)
    (hinj : FibInj Ψ) (G : C ⟶ A) (K : C ⟶ A') (hK : equivalences K) (hGK : NatEquiv K (G ≫ Ψ))
    (x : A.Obj) : ∃ (U : Set A.Obj) (U' : Set A'.Obj), x ∈ U ∧
      A.B.IsStrongBundleIsoOn A'.B (Hom.isStrongBundleFunctor Ψ).isStrongBundleMap_obj U U' := by
  obtain ⟨θ⟩ := hGK
  have hGs := (Hom.isStrongBundleFunctor G).isStrongBundleMap_obj
  have hΨs := Hom.isStrongBundleFunctor Ψ
  have hKs := (Hom.isStrongBundleFunctor K).isStrongBundleMap_obj
  have hg : (Hom.ϕ G).IsEquivalence := EpFunctor.IsEquivalence.of_comp_left hψ
    ((EpFunctor.proposition_10_1_5 ⟨θ.τ⟩).1 hK.isEquivalence_base)
  obtain ⟨c, γ, hs, ht⟩ := hg.exists_iso x
  -- the transport `H_γ̂` along `γ` in `W''`
  obtain ⟨Tσ, hTσ⟩ := (EpFunctor.id A.X).exists_transportChart
    (EpFunctor.IsEquivalence.id A.X).isLocalScDiffeo_obj (x := (Hom.ϕ G).obj c) hs ht
  have hQσ : Tσ.Q ((Hom.ϕ G).obj c) = x := Tσ.Q_self
  have Aσ := isLocalIso₂_lrAct (E := A.E) Tσ.isScSmoothOn_ψ Tσ.src_ψ Tσ.tgt_ψ Tσ.isScDiffeoOn_Q
  have hN₀ : IsOpen ((Hom.ϕ G).obj ⁻¹' Tσ.W) := Tσ.isOpen_W.preimage (Hom.ϕ G).continuous_obj'
  -- the family `τ'(u) = ψ(γ̂(g u)) ∘ τ(u) : k(u) → ψ(Q_γ(g u))`
  set τ' : C.Obj → A'.Mor := fun u =>
    A'.X.comp ((Hom.ϕ Ψ).mor (Tσ.ψ ((Hom.ϕ G).obj u))) (θ.τ.app u) with hτ'
  have hab : ∀ u ∈ (Hom.ϕ G).obj ⁻¹' Tσ.W,
      A'.X.src ((Hom.ϕ Ψ).mor (Tσ.ψ ((Hom.ϕ G).obj u))) = A'.X.tgt (θ.τ.app u) := fun u hu => by
    rw [(Hom.ϕ Ψ).src_mor, Tσ.src_ψ _ hu, θ.τ.tgt_app]; rfl
  have hτ's : C.X.PObj.IsScSmoothOn A'.X.PMor τ' ((Hom.ϕ G).obj ⁻¹' Tσ.W) :=
    A'.X.isScSmoothOn_comp_of
      (MPolyfold.IsScSmoothOn.comp (Hom.ϕ Ψ).isScSmoothMap_mor
        (MPolyfold.IsScSmoothOn.comp Tσ.isScSmoothOn_ψ
          ((Hom.ϕ G).isScSmoothMap_obj.mono hN₀ (subset_univ _)) fun u hu => hu) (mapsTo_univ _ _))
      (θ.τ.isScSmoothMap_app.mono hN₀ (subset_univ _)) hab
  have hsτ' : ∀ u ∈ (Hom.ϕ G).obj ⁻¹' Tσ.W, A'.X.src (τ' u) = (Hom.ϕ K).obj u := fun u hu => by
    rw [hτ', A'.X.src_comp _ _ (hab u hu), θ.τ.src_app]
  have htτ' : ∀ u ∈ (Hom.ϕ G).obj ⁻¹' Tσ.W,
      A'.X.tgt (τ' u) = (Hom.ϕ Ψ).obj (Tσ.Q ((Hom.ϕ G).obj u)) := fun u hu => by
    rw [hτ', A'.X.tgt_comp _ _ (hab u hu), (Hom.ϕ Ψ).tgt_mor, Tσ.tgt_ψ _ hu]
  have hcN₀ : c ∈ (Hom.ϕ G).obj ⁻¹' Tσ.W := Tσ.mem_W
  -- the chart of `k` along `τ'(c)`, and the transport of `K`
  obtain ⟨T, hT⟩ := (Hom.ϕ K).exists_transportChart hK.isEquivalence_base.isLocalScDiffeo_obj
    (hsτ' c hcN₀) (y := (Hom.ϕ Ψ).obj x) (by rw [htτ' c hcN₀, hQσ])
  obtain ⟨N₁, hN₁sub, hN₁, hcN₁, hagree⟩ := A'.X.exists_eqOn_of_src (T.isOpen_W.inter hN₀)
    (T.continuousOn_ψ.mono inter_subset_left) (hτ's.continuousOn.mono inter_subset_right)
    (fun u hu => by rw [T.src_ψ _ hu.1, hsτ' u hu.2]) ⟨T.mem_W, hcN₀⟩ (by rw [T.ψ_self, hT])
  obtain ⟨S, hS, hcS, -, H', hL⟩ := hK.exists_transport T
  have hS₁ : IsOpen (S ∩ N₁) := hS.inter hN₁
  have hL₁ := hL.restrict_image hS₁ inter_subset_left
  -- `Ψ ∘ G' = μ'(T.ψ, K)` over `S ∩ N₁`
  set G' : C.W → A.W := fun v =>
    A.E.lrAct (Tσ.ψ (A.P ((Hom.Φ G).obj v))) ((Hom.Φ G).obj v) with hG'
  have key : ∀ v, C.P v ∈ S ∩ N₁ → (Hom.Φ Ψ).obj (G' v) =
      A'.E.lrAct (T.ψ (C.P v)) ((Hom.Φ K).obj v) := fun v hv => by
    have hu : C.P v ∈ (Hom.ϕ G).obj ⁻¹' Tσ.W := (hN₁sub hv.2).2
    have hPG : A.P ((Hom.Φ G).obj v) = (Hom.ϕ G).obj (C.P v) := hGs.covers v
    have h1 : A.P ((Hom.Φ G).obj v) = A.X.src (Tσ.ψ (A.P ((Hom.Φ G).obj v))) := by
      rw [Tσ.src_ψ _ (by rw [hPG]; exact hu)]; rfl
    have h2 : A'.P ((Hom.Φ K).obj v) = A'.X.src (θ.τ.app (C.P v)) := by
      rw [θ.τ.src_app, hKs.covers]
    have e1 : (Hom.Φ Ψ).obj ((Hom.Φ G).obj v) = A'.E.lrAct (θ.τ.app (C.P v)) ((Hom.Φ K).obj v) :=
      (StrongBundleNatTrans.obj_eq_act θ v).trans (act_eq_lrAct h2)
    change (Hom.Φ Ψ).obj (A.E.lrAct _ _) = _
    rw [hΨs.obj_lrAct h1, e1, hPG, ← lrAct_comp h2 (hab _ hu), hagree _ hv.2]
  have hL₂ := hL₁.congr (Φ' := fun v => (Hom.Φ Ψ).obj (G' v)) (fun v hv => key v hv)
    (fun _ _ => rfl)
  -- the local right inverse `Θ = G' ∘ H'` over `N' = T.Q(S ∩ N₁)`
  have hmS : ∀ u ∈ S ∩ N₁, (Hom.ϕ G).obj u ∈ Tσ.W := fun u hu => (hN₁sub hu.2).2
  have hQu : ∀ u ∈ S ∩ N₁, (Hom.ϕ Ψ).obj (Tσ.Q ((Hom.ϕ G).obj u)) = T.Q u := fun u hu => by
    rw [← htτ' u (hmS u hu), ← hagree u hu.2, T.tgt_ψ _ (hN₁sub hu.2).1]
  have hQc : T.Q c = (Hom.ϕ Ψ).obj x := by rw [← hQu c ⟨hcS, hcN₁⟩, hQσ]
  obtain ⟨L₁, H'₁, -, hb₁, hc₁⟩ := hL₂.one
  obtain ⟨Aσ₁, Aσ₁', ha₁, -, hc₁'⟩ := Aσ.one
  have hGmem : ∀ v, C.P v ∈ S ∩ N₁ → A.P ((Hom.Φ G).obj v) ∈ Tσ.W := fun v hv => by
    rw [hGs.covers]; exact hmS _ hv
  refine isStrongBundleIsoOn_of_rightInv Ψ hinj (hψ.isLocalScDiffeo_obj.at x)
    (N' := T.Q '' (S ∩ N₁)) (r := Tσ.Q ∘ (Hom.ϕ G).obj ∘ T.Qinv) (Θ := G' ∘ H') ?_
    ⟨c, ⟨hcS, hcN₁⟩, hQc⟩ ?_ ?_ ?_ ?_ (fun w hw => hL₂.right_inv hw)
    (fun y => Aσ₁ (StrongBundle.oneRestrict C.B A.B (Hom.Φ G).obj hGs.mapsTo_oneSet (H'₁ y)))
    ?_ ?_
  · exact MPolyfold.IsScSmoothOn.comp Tσ.isScDiffeoOn_Q.isScSmoothOn
      (MPolyfold.IsScSmoothOn.comp ((Hom.ϕ G).isScSmoothMap_obj.mono hS₁ (subset_univ _))
        hL₂.base.isScSmoothOn_inv hL₂.base.mapsTo_inv) fun y hy => hmS _ (hL₂.base.mapsTo_inv hy)
  · have e : T.Qinv (T.Q c) = c := hL₂.base.left_inv c ⟨hcS, hcN₁⟩
    rw [hQc] at e
    change Tσ.Q ((Hom.ϕ G).obj (T.Qinv ((Hom.ϕ Ψ).obj x))) = x
    rw [e, hQσ]
  · rintro y ⟨u, hu, rfl⟩
    change (Hom.ϕ Ψ).obj (Tσ.Q ((Hom.ϕ G).obj (T.Qinv (T.Q u)))) = T.Q u
    rw [hL₂.base.left_inv u hu, hQu u hu]
  · have hGo : IsOpen (C.P ⁻¹' (S ∩ N₁)) := hS₁.preimage C.B.continuous
    exact MPolyfold.IsScSmoothOn.comp (MPolyfold.IsScSmoothOn.comp Aσ.zero.isScSmoothOn
      (hGs.isScSmoothMap.mono hGo (subset_univ _)) fun v hv => hGmem v hv)
      hL₂.zero.isScSmoothOn_inv hL₂.zero.mapsTo_inv
  · intro w hw
    have hw' : C.P (H' w) ∈ S ∩ N₁ := hL₂.mapsTo_inv hw
    change A.P (A.E.lrAct _ _) = Tσ.Q ((Hom.ϕ G).obj (T.Qinv (A'.P w)))
    rw [Aσ.covers (hGmem _ hw'), hGs.covers, hL₂.covers_inv hw]
  · intro y hy
    have hy' : C.P (C.B.oneVal (H'₁ y)) ∈ S ∩ N₁ := hc₁.mapsTo_inv hy
    rw [ha₁ _ (by rw [StrongBundle.oneVal_oneRestrict]; exact hGmem _ hy'),
      StrongBundle.oneVal_oneRestrict, hb₁ y hy]
    rfl
  · have hc : Continuous (C.P ∘ C.B.oneVal) := C.B.continuous.comp C.B.continuous_oneVal
    refine MPolyfold.IsScSmoothOn.comp hc₁'.isScSmoothOn
      (MPolyfold.IsScSmoothOn.comp (hGs.isScSmoothMap_one.mono (hS₁.preimage hc) (subset_univ _))
        hc₁.isScSmoothOn_inv hc₁.mapsTo_inv) fun y hy => ?_
    have hy' : C.P (C.B.oneVal (H'₁ y)) ∈ S ∩ N₁ := hc₁.mapsTo_inv hy
    change A.P (A.B.oneVal (StrongBundle.oneRestrict _ _ _ _ (H'₁ y))) ∈ Tσ.W
    rw [StrongBundle.oneVal_oneRestrict]; exact hGmem _ hy'

end SEP

/-! ### Morphisms, the total functor, `|W[1]|`, and the saturation theorem -/

namespace StrongBundle

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]

/-- A local strong bundle isomorphism for `Φ` is one for any `Φ' = Φ`. -/
theorem IsStrongBundleIsoOn.of_eq_map {B : StrongBundle PX P} {B' : StrongBundle PX' P'}
    {f : X → X'} {Φ Φ' : Y → Y'} {h : B.IsStrongBundleMap B' f Φ} {U : Set X} {U' : Set X'}
    (hi : B.IsStrongBundleIsoOn B' h U U') (hΦ : Φ = Φ') (h' : B.IsStrongBundleMap B' f Φ') :
    B.IsStrongBundleIsoOn B' h' U U' := by
  subst hΦ; exact hi

end StrongBundle

namespace SEP

open EpStrongBundle

variable {A A' C : SEP.{u}}

/-- **On morphisms**: a strong bundle functor which is a local strong bundle isomorphism on
objects is one on morphisms (through the pull-back projections `𝐖 → W`, local strong bundle
isomorphisms as `s` is a local sc-diffeomorphism). -/
theorem isLocalStrongBundleIso_mor_of_obj (Ψ : A ⟶ A')
    (h : ∀ x : A.Obj, ∃ (U : Set A.Obj) (U' : Set A'.Obj), x ∈ U ∧
      A.B.IsStrongBundleIsoOn A'.B (Hom.isStrongBundleFunctor Ψ).isStrongBundleMap_obj U U')
    (φ : A.Mor) : ∃ (U : Set A.Mor) (U' : Set A'.Mor), φ ∈ U ∧
      (A.B.pullback A.X.isScSmoothMap_src).IsStrongBundleIsoOn
        (A'.B.pullback A'.X.isScSmoothMap_src)
        (Hom.isStrongBundleFunctor Ψ).isStrongBundleMap_mor U U' := by
  have hΨ := Hom.isStrongBundleFunctor Ψ
  obtain ⟨U₃, V₃, σ₃, hm₃, hd₃⟩ := A.X.isLocalScDiffeo_src φ
  have i₃ := A.B.isStrongBundleIsoOn_pullbackProj' A.X.isScSmoothMap_src hd₃ φ
  obtain ⟨U₂, U₂', hm₂, i₂⟩ := h (A.X.src φ)
  obtain ⟨U₀, U₀'', hm₀, i₀⟩ := i₂.exists_comp i₃ hm₃ hm₂
  have i₀' := i₀.of_eq (show (Hom.ϕ Ψ).obj ∘ A.X.src = A'.X.src ∘ (Hom.ϕ Ψ).mor from
    funext fun m => ((Hom.ϕ Ψ).src_mor m).symm)
  obtain ⟨U₁, V₁, σ₁, hm₁, hd₁⟩ := A'.X.isLocalScDiffeo_src ((Hom.ϕ Ψ).mor φ)
  have i₁ := A'.B.isStrongBundleIsoOn_pullbackProj' A'.X.isScSmoothMap_src hd₁ ((Hom.ϕ Ψ).mor φ)
  obtain ⟨G, hG⟩ := i₀'.isScDiffeoOn_base
  obtain ⟨g', hg'⟩ := i₁.isScDiffeoOn_base
  have hU₄ : IsOpen (U₀ ∩ (Hom.ϕ Ψ).mor ⁻¹' U₁) :=
    hG.isOpen_source.inter (hg'.isOpen_source.preimage (Hom.ϕ Ψ).continuous_mor)
  have i₄ := i₀'.restrict hG hU₄ inter_subset_left
  have hfun : (Hom.Φ Ψ).obj ∘ pullbackProj' A.P A.X.src =
      pullbackProj' A'.P A'.X.src ∘ (Hom.Φ Ψ).mor := funext fun q => ((Hom.Φ Ψ).src_mor q).symm
  exact ⟨U₀ ∩ (Hom.ϕ Ψ).mor ⁻¹' U₁, _, ⟨hm₀, hm₁⟩, StrongBundle.IsStrongBundleIsoOn.of_comp
    (h := hΨ.isStrongBundleMap_mor)
    (h' := A'.B.isStrongBundleMap_pullbackProj' A'.X.isScSmoothMap_src)
    (i₄.of_eq_map hfun _) i₁ fun _ hy => hy.2⟩

/-- `Ψ` is full on the total spaces if `ψ` is full and `Ψ` injective on the fibres. -/
theorem full_total (Ψ : A ⟶ A') (hψ : (Hom.ϕ Ψ).IsEquivalence) (hinj : FibInj Ψ) :
    (Hom.Φ Ψ).toFunctor.Full := by
  have hΨ := Hom.isStrongBundleFunctor Ψ
  refine (GroupoidFunctor.full_iff _).2 fun w w' q' hs ht => ?_
  have hs' : (q' : A'.Mor × A'.W).2 = (Hom.Φ Ψ).obj w := hs
  have ht' : A'.E.μ q' = (Hom.Φ Ψ).obj w' := ht
  have hq := q'.2
  obtain ⟨γ, hγs, hγt, hγ⟩ := hψ.exists_mor_eq (x := A.P w) (x' := A.P w')
    (ψ := (q' : A'.Mor × A'.W).1) (by rw [← hq, hs', hΨ.isStrongBundleMap_obj.covers])
    (by rw [← A'.E.P_μ q', ht', hΨ.isStrongBundleMap_obj.covers])
  have hw : A.P w = A.X.src γ := hγs.symm
  let q : pullbackSpace A.P A.X.src := ⟨(γ, w), hw⟩
  have hq' : (q' : A'.Mor × A'.W) = ((Hom.ϕ Ψ).mor γ, (Hom.Φ Ψ).obj w) := Prod.ext hγ.symm hs'
  have hPμ : A.P (A.E.μ q) = A.P w' := by rw [A.E.P_μ]; exact hγt
  have hΨμ : (Hom.Φ Ψ).obj (A.E.μ q) = (Hom.Φ Ψ).obj w' := by
    have hw' : A'.P ((Hom.Φ Ψ).obj w) = A'.X.src ((Hom.ϕ Ψ).mor γ) := by
      rw [hΨ.isStrongBundleMap_obj.covers, (Hom.ϕ Ψ).src_mor, hw]
    rw [← lrAct_eq hw, hΨ.obj_lrAct hw, lrAct_eq hw', ← ht']
    exact A'.E.μ_congr hq'.symm
  refine ⟨q, rfl, hinj hPμ hΨμ, Subtype.ext ?_⟩
  rw [hΨ.mor_val q, hq']

/-- **The total functor is an equivalence**, under the hypotheses of the saturation theorem. -/
theorem isEquivalence_total (Ψ : A ⟶ A') (hψ : (Hom.ϕ Ψ).IsEquivalence) (hinj : FibInj Ψ)
    (hloc : ∀ x : A.Obj, ∃ (U : Set A.Obj) (U' : Set A'.Obj), x ∈ U ∧
      A.B.IsStrongBundleIsoOn A'.B (Hom.isStrongBundleFunctor Ψ).isStrongBundleMap_obj U U') :
    (Hom.Φ Ψ).IsEquivalence := by
  have hΨ := Hom.isStrongBundleFunctor Ψ
  refine (Hom.Φ Ψ).lemma_10_1_2 { full := full_total Ψ hψ hinj, faithful := ?_, essSurj := ?_ }
    fun w => ?_
  · refine (GroupoidFunctor.faithful_iff _).2 fun q q' hs ht he => ?_
    have hs' : (q : A.Mor × A.W).2 = (q' : A.Mor × A.W).2 := hs
    have ht' : A.E.μ q = A.E.μ q' := ht
    have h1 : (Hom.ϕ Ψ).mor (q : A.Mor × A.W).1 = (Hom.ϕ Ψ).mor (q' : A.Mor × A.W).1 := by
      have e := congrArg (fun r : pullbackSpace A'.P A'.X.src => (r : A'.Mor × A'.W).1) he
      simp only [hΨ.mor_val] at e
      exact e
    have h2 : (q : A.Mor × A.W).1 = (q' : A.Mor × A.W).1 := hψ.mor_injective
      (by rw [← q.2, ← q'.2, hs']) (by rw [← A.E.P_μ q, ← A.E.P_μ q', ht']) h1
    exact Subtype.ext (Prod.ext h2 hs')
  · refine (GroupoidFunctor.essSurj_iff _).2 fun w' => ?_
    obtain ⟨x, γ', hs, ht⟩ := hψ.exists_iso (A'.P w')
    have hi : A'.P w' = A'.X.src (A'.X.inv γ') := by rw [A'.X.src_inv, ht]
    have hv : A'.P (A'.E.lrAct (A'.X.inv γ') w') = (Hom.ϕ Ψ).obj x := by
      rw [P_lrAct hi, A'.X.tgt_inv, hs]
    obtain ⟨U, U', hxU, hi'⟩ := hloc x
    obtain ⟨v, hv'⟩ := (hi'.fiberEquiv hxU).surjective ⟨_, hv⟩
    have e : (Hom.Φ Ψ).obj v = A'.E.lrAct (A'.X.inv γ') w' := congrArg Subtype.val hv'
    have hq : A'.P ((Hom.Φ Ψ).obj v) = A'.X.src γ' := by
      rw [hΨ.isStrongBundleMap_obj.covers, v.2, hs]
    refine ⟨v, ⟨(γ', (Hom.Φ Ψ).obj v), hq⟩, rfl, ?_⟩
    change A'.E.μ _ = w'
    rw [← lrAct_eq hq, e, lrAct_lrAct_inv hi]
  · obtain ⟨U, U', hxU, hi'⟩ := hloc (A.P w)
    obtain ⟨Θ, hΘ⟩ := hi'.isScDiffeoOn_zero
    exact hΘ.isLocalScDiffeoAt (show w ∈ A.P ⁻¹' U from hxU)

/-- Naturally equivalent strong bundle functors induce the same map `|W[1]| → |W'[1]|`. -/
theorem NatEquiv.oneOrbitMap_eq {F G : A ⟶ A'} (h : NatEquiv F G) :
    A.E.oneOrbitMap A'.E (Hom.Φ F)
        (Hom.isStrongBundleFunctor F).isStrongBundleMap_obj.mapsTo_oneSet =
      A.E.oneOrbitMap A'.E (Hom.Φ G)
        (Hom.isStrongBundleFunctor G).isStrongBundleMap_obj.mapsTo_oneSet := by
  obtain ⟨θ⟩ := h
  funext q
  induction q using Quotient.inductionOn with
  | h w => exact Quotient.sound ⟨θ.T (A.B.oneVal w), θ.src_T _, θ.tgt_T _⟩

/-- **`|Ψ| : |W''[1]| → |W'[1]|` is a homeomorphism**: it is injective (fullness), and
`|Ψ| ∘ |G| = |K|` gives the continuous inverse `|G| ∘ |K|⁻¹`. -/
theorem isHomeomorph_oneOrbitMap_of (Ψ : A ⟶ A') (hfull : (Hom.Φ Ψ).toFunctor.Full)
    (G : C ⟶ A) (K : C ⟶ A') (hK : equivalences K) (hGK : NatEquiv K (G ≫ Ψ)) :
    IsHomeomorph (A.E.oneOrbitMap A'.E (Hom.Φ Ψ)
      (Hom.isStrongBundleFunctor Ψ).isStrongBundleMap_obj.mapsTo_oneSet) := by
  set F := A.E.oneOrbitMap A'.E (Hom.Φ Ψ)
    (Hom.isStrongBundleFunctor Ψ).isStrongBundleMap_obj.mapsTo_oneSet with hF
  set Gm := C.E.oneOrbitMap A.E (Hom.Φ G)
    (Hom.isStrongBundleFunctor G).isStrongBundleMap_obj.mapsTo_oneSet with hGm
  set eK := IsHomeomorph.homeomorph _ hK.isHomeomorph_oneOrbitMap with heK
  have hFG : ∀ q, F (Gm q) = eK q := fun q => by
    induction q using Quotient.inductionOn with
    | h w => exact (congrFun (NatEquiv.oneOrbitMap_eq hGK) (Quotient.mk _ w)).symm
  have hcF : Continuous F := continuous_oneOrbitMap (continuousOn_univ.1
    (Hom.isStrongBundleFunctor Ψ).isStrongBundleMap_obj.isScSmoothMap_one.continuousOn)
  have hcG : Continuous Gm := continuous_oneOrbitMap (continuousOn_univ.1
    (Hom.isStrongBundleFunctor G).isStrongBundleMap_obj.isScSmoothMap_one.continuousOn)
  have hinj : Injective F := fun a b hab => by
    induction a using Quotient.inductionOn with | h a => ?_
    induction b using Quotient.inductionOn with | h b => ?_
    obtain ⟨q', hs, ht⟩ := Quotient.exact hab
    obtain ⟨q, hqs, hqt, -⟩ := (GroupoidFunctor.full_iff _).1 hfull _ _ q' hs ht
    exact Quotient.sound ⟨q, hqs, hqt⟩
  have hr : ∀ q, F (Gm (eK.symm q)) = q := fun q => by rw [hFG, eK.apply_symm_apply]
  let e : A.E.OneOrbitSpace ≃ₜ A'.E.OneOrbitSpace :=
    { toFun := F
      invFun := Gm ∘ eK.symm
      left_inv := fun z => hinj (hr (F z))
      right_inv := hr
      continuous_toFun := hcF
      continuous_invFun := hcG.comp eK.symm.continuous }
  exact e.isHomeomorph

/-- **The saturation theorem**: a strong bundle functor `Ψ : W'' → W'` covering an equivalence,
injective on the fibres, with `Ψ ∘ G` naturally equivalent to a strong bundle equivalence `K`
for some strong bundle functor `G`, is a strong bundle equivalence (Definition 10.4.1). -/
theorem equivalences_of_natEquiv_comp (Ψ : A ⟶ A') (hψ : (Hom.ϕ Ψ).IsEquivalence)
    (hinj : FibInj Ψ) (G : C ⟶ A) (K : C ⟶ A') (hK : equivalences K)
    (hGK : NatEquiv K (G ≫ Ψ)) : equivalences Ψ := by
  have hloc := exists_isStrongBundleIsoOn Ψ hψ hinj G K hK hGK
  exact
    { isStrongBundleFunctor := Hom.isStrongBundleFunctor Ψ
      isEquivalence_base := hψ
      isEquivalence := isEquivalence_total Ψ hψ hinj hloc
      isHomeomorph_oneOrbitMap :=
        isHomeomorph_oneOrbitMap_of Ψ (full_total Ψ hψ hinj) G K hK hGK
      isLocalStrongBundleIso_obj := hloc
      isLocalStrongBundleIso_mor := isLocalStrongBundleIso_mor_of_obj Ψ hloc }

end SEP

/-! ### Fibrewise injectivity from `[D] ∘ [E] = 1` -/

namespace SBLocalization

open SEP EpStrongBundle

variable {A A' A'' : SEP.{u}}

namespace SDiagram

/-- Over the points `ΠW''(H(c))`, `Ψ` is injective on the fibres as soon as `ΠV'' ∘ H` is: the
point `ΠV''(m)` is the unique `e` with `Φ'(e) = p.φ · Ψ(ΠW''(m))` (`compRight_obj_eq`), and
`ΠW'' ∘ H` is bijective on the fibres. -/
theorem fibInjAt_Ψ (D : SDiagram A A') (E : SDiagram A' A'') {C : SEP.{u}} (H : C ⟶ compMid D E)
    (hH : equivalences H) (hinj : FibInj (H ≫ compRight D E)) (c : C.Obj) :
    FibInjAt D.Ψ ((Hom.ϕ (H ≫ compLeft D E)).obj c) := by
  intro w₁ w₂ h₁ h₂ he
  have hM : equivalences (H ≫ compLeft D E) :=
    SEP.equivalences.comp_mem _ _ hH (equivalences_compLeft D E)
  obtain ⟨v₁, hv₁⟩ := (hM.fiberEquiv c).surjective ⟨w₁, h₁⟩
  obtain ⟨v₂, hv₂⟩ := (hM.fiberEquiv c).surjective ⟨w₂, h₂⟩
  have e₁ : (Hom.Φ (H ≫ compLeft D E)).obj v₁ = w₁ := congrArg Subtype.val hv₁
  have e₂ : (Hom.Φ (H ≫ compLeft D E)).obj v₂ = w₂ := congrArg Subtype.val hv₂
  have hpt : pt D E ((Hom.Φ H).obj v₁) = pt D E ((Hom.Φ H).obj v₂) := by
    change (compMid D E).P _ = (compMid D E).P _
    rw [(Hom.isStrongBundleFunctor H).isStrongBundleMap_obj.covers,
      (Hom.isStrongBundleFunctor H).isStrongBundleMap_obj.covers, v₁.2, v₂.2]
  have hfib : ∀ i : C.P ⁻¹' {c}, fib D E ((Hom.Φ H).obj i) = (Hom.Φ (H ≫ compLeft D E)).obj i :=
    fun _ => rfl
  have hR : (Hom.Φ (compRight D E)).obj ((Hom.Φ H).obj v₁) =
      (Hom.Φ (compRight D E)).obj ((Hom.Φ H).obj v₂) := by
    refine (compRight_obj_eq D E ?_ ?_).symm
    · rw [P_compRight, hpt]
    · rw [obj_compRight, hpt, hfib, hfib, e₁, e₂, he]
  have hv : (v₁ : C.W) = v₂ := hinj (v₁.2.trans v₂.2.symm) hR
  rw [← e₁, ← e₂, hv]

/-- **Fibrewise injectivity of `Ψ` from `[D] ∘ [E] = 1`.** -/
theorem fibInj_Ψ_of_equiv (D : SDiagram A A') (E : SDiagram A' A)
    (h : Equiv (D.comp E) (SDiagram.id A)) : FibInj D.Ψ := by
  obtain ⟨D₀, ⟨H, hH, -, hHΨ⟩, ⟨K, hK, -, hKΨ⟩⟩ := h
  have h1 : NatEquiv K ((H ≫ compRight D E) ≫ E.Ψ) :=
    ((NatEquiv.of_eq (Category.comp_id K).symm).trans hKΨ).trans
      ((NatEquiv.of_eq (Category.assoc _ _ _)).trans hHΨ).symm
  have hinj : FibInj (H ≫ compRight D E) :=
    (FibInj.of_natEquiv h1 (fibInj_of_equivalences hK)).of_comp
  refine (fibInj_iff _).2 fun x => ?_
  have hM : equivalences (H ≫ compLeft D E) :=
    SEP.equivalences.comp_mem _ _ hH (equivalences_compLeft D E)
  obtain ⟨c, γ, hs, ht⟩ := hM.isEquivalence_base.exists_iso x
  exact (fibInjAt_Ψ D E H hH hinj c).of_mor hs ht

/-- **The strong bundle equivalence `K` from `[E] ∘ [D] = 1`**: some strong bundle functor `G`
into `W''` (`ΠW'' ∘ H` for the refinement `H` into the middle of `E ∘ D`) has `Ψ ∘ G`
naturally equivalent to a strong bundle equivalence. -/
theorem exists_natEquiv_of_equiv (D : SDiagram A A') (E : SDiagram A' A)
    (h : Equiv (E.comp D) (SDiagram.id A')) : ∃ (C : SEP.{u}) (G : C ⟶ D.B) (K : C ⟶ A'),
      equivalences K ∧ NatEquiv K (G ≫ D.Ψ) := by
  obtain ⟨D₀, ⟨H, -, -, hHΨ⟩, ⟨K, hK, -, hKΨ⟩⟩ := h
  exact ⟨D₀.B, H ≫ compRight E D, K, hK,
    ((NatEquiv.of_eq (Category.comp_id K).symm).trans hKΨ).trans
      ((NatEquiv.of_eq (Category.assoc _ _ _)).trans hHΨ).symm⟩

end SDiagram

namespace SEPLoc

/-- **The converse of the strong bundle version of 2021 Theorem 10.3.10, p. 489 (2017:
Theorem 10.4, p. 353)** (Remark 10.5.3, p. 506): if `[W ←Φ W'' →Ψ W']` is an isomorphism of
`SEP(F⁻¹)`, then `Ψ` is a strong bundle equivalence.  From the inverse `[E]`: `ψ` is an
equivalence (`isEquivalence_base_of_isIso`), `[D] ∘ [E] = 1` makes `Ψ` injective on the fibres,
and `[E] ∘ [D] = 1` gives the strong bundle equivalence of `equivalences_of_natEquiv_comp`. -/
theorem equivalences_Ψ_of_isIso (D : SDiagram A A') (h : IsIso (homMk D)) :
    SEP.equivalences D.Ψ := by
  obtain ⟨E, hE⟩ := homMk_surjective (CategoryTheory.inv (homMk D))
  have h₁ : homMk (D.comp E) = homMk (SDiagram.id A) := by
    rw [← homMk_comp, hE]; exact IsIso.hom_inv_id _
  have h₂ : homMk (E.comp D) = homMk (SDiagram.id A') := by
    rw [← homMk_comp, hE]; exact IsIso.inv_hom_id _
  obtain ⟨C, G, K, hK, hGK⟩ := SDiagram.exists_natEquiv_of_equiv D E (homMk_eq_homMk_iff.1 h₂)
  exact SEP.equivalences_of_natEquiv_comp D.Ψ (isEquivalence_base_of_isIso D h)
    (SDiagram.fibInj_Ψ_of_equiv D E (homMk_eq_homMk_iff.1 h₁)) G K hK hGK

/-- **The strong bundle version of Theorem 10.3.10 (1)** (Remark 10.5.3): `[W ←Φ W'' →Ψ W']` is
an isomorphism of `SEP(F⁻¹)` iff `Ψ` is a strong bundle equivalence. -/
theorem isIso_homMk_iff (D : SDiagram A A') : IsIso (homMk D) ↔ SEP.equivalences D.Ψ :=
  ⟨equivalences_Ψ_of_isIso D, fun hΨ => (theorem_10_3_10 D hΨ).1⟩

/-- **2021 Remark 10.5.3, p. 506**: the isomorphisms of `SEP(F⁻¹)` are exactly the generalized
strong bundle isomorphisms of Definition 10.5.2 (every representative of an isomorphism has both
legs strong bundle equivalences). -/
theorem isIso_iff_isGeneralizedIso (f : GenSBMap A A') :
    IsIso (show of A ⟶ of A' from f) ↔ f.IsGeneralizedIso := by
  refine ⟨fun h => ?_, isIso_of_isGeneralizedIso⟩
  obtain ⟨D, rfl⟩ := SDiagram.cls_surjective f
  exact ⟨D, rfl, equivalences_Ψ_of_isIso D h⟩

end SEPLoc

end SBLocalization

end Polyfold
