import Polyfold.Chapter10.Equivalence
import Polyfold.Chapter8.NonVacuityBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, "Equivalences and Localization", §10.4 "Strong Bundles and Equivalences"
(pp. 495–503; 2017: pp. 357–364): **Definition 10.4.1, Propositions 10.4.2, 10.4.3, 10.4.4,
Theorem 10.4.5** (2017: Definition 10.10, Propositions 10.7, 10.8, 10.9, Theorem 10.8).  Numbers
and pages are the 2021 text's, the 2017 ones in parentheses.  Remark 10.4.9 and Definitions
10.4.8, 10.4.10, 10.4.11 are in `StrongBundleEquivalenceNat.lean`, the concrete witnesses in
`StrongBundleEquivalenceExamples.lean`.

# Strong bundle equivalences

## The text, paraphrased

(pp. 495–496) A strong bundle `(P : W → X, μ)` over an ep-groupoid (Definition 8.3.1) gives the
category `(W, 𝐖)`, `𝐖 = 𝐗 ₛ×_P W`, with `(φ, w) : w → μ(φ, w)`, and the ep-groupoids `W[i]`,
`i = 0, 1`; a strong bundle functor `Φ` covering `ϕ` satisfies `μ'(ϕ(γ), Φ(w)) = Φ(μ(γ, w))`
(10.14).  (Definition 10.4.1, p. 496 (2017: Definition 10.10)) A strong bundle equivalence is a
linear strong bundle functor with (1) `Φ : W[i] → W'[i]`, `i = 0, 1`, equivalences of
ep-groupoids covering the equivalence `ϕ`, and (2) `Φ` on objects and on morphisms locally strong
bundle isomorphisms.  (pp. 496–497) `w ≅ w'` iff `w' = μ(σ, w)` (10.15); section functors satisfy
`f(t(γ)) = μ(γ, f(s(γ)))` (10.16); the pull-back is `Φ*(f')(x) = Φ_x⁻¹(f'(ϕ(x)))`.

(Proposition 10.4.2, p. 497 (2017: Proposition 10.7)) For strong bundle equivalences `Φ`, `Ψ`
covering `ϕ`, `ψ` with `|Φ| = |Ψ|`, `Φ*(f') = Ψ*(f')` for every sc-smooth section functor `f'`.
(p. 498) The push-forward `(Φ_* f)(x') = μ'(σ, Φ(f(x)))` for a choice of `σ : ϕ(x) → x'`; it is
independent of the choice by (10.22), and its sc-smoothness is called easily verified.
(Proposition 10.4.3, p. 499 (2017: Proposition 10.8)) Under the hypotheses of 10.4.2,
`Φ_* f = Ψ_* f`.  (Proposition 10.4.4, p. 499 (2017: Proposition 10.9)) `(Ψ ∘ Φ)* = Φ* ∘ Ψ*` and
`(Ψ ∘ Φ)_* = Ψ_* ∘ Φ_*`.  (Theorem 10.4.5, p. 500 (2017: Theorem 10.8)) `Φ_*` and `Φ*` are
mutually inverse bijections between `Γ(P, μ)` and `Γ(P', μ')`, they agree for `|Φ| = |Ψ|`, and
they preserve sc⁺-section functors and sc-Fredholm section functors.

## What is formalized

* `EpStrongBundle.IsStrongBundleEquivalence` (**Definition 10.4.1**),
  `isStrongBundleEquivalence_id`, `IsStrongBundleEquivalence.comp`; consequences `covers`,
  `fiberEquiv` (the fibre maps are topological linear isomorphisms), `eq_of_obj_eq`,
  `isLocalScDiffeo_obj`, `isLocalScDiffeo_one`, `exists_mor_eq`; the orbit space
  `OneOrbitSpace` of `W[1]` with `oneOrbitMap`.
* The pull-back `IsStrongBundleEquivalence.pullback` and the push-forward `pushforward`:
  `isFunctorialSection_pullback`, `pushforward_eq` ((10.22)), `isFunctorialSection_pushforward`,
  `pullback_pushforward`, `pushforward_pullback`; sc-smoothness `isScSmoothSection_pullback`,
  `isScSmoothSection_pushforward`, and at level `[1]` `isScPlusSection_pullback`,
  `isScPlusSection_pushforward`.
* `proposition_10_4_2` (**Proposition 10.4.2**), with `pullback_eq_of_orbitMap_eq` for all
  functorial sections; `proposition_10_4_3` (**Proposition 10.4.3**), with
  `pushforward_eq_of_orbitMap_eq`; `proposition_10_4_4` (**Proposition 10.4.4**);
  `theorem_10_4_5` (**Theorem 10.4.5**, without the `Fred` part).
* Helpers: `StrongBundle.IsStrongBundleIsoOn.restrict`, `comp`, `exists_comp`, `P_inv`,
  `P_inv_one`; `EpStrongBundle.IsStrongBundleFunctor.comp`;
  `MPolyfold.isScSmoothOn_of_forall_charts` and `StrongBundle.isScSmoothOn_to_pullback_one`
  (the level-`[1]` universal property of the
  pull-back on an open set); `exists_μ_eq_of_orbitMap_eq` and `orbitMap_eq_of_forall_exists`
  (`|Φ| = |Ψ|` through (10.15)); `μ_injective_snd`, `μ_mk_congr`.

## What the text leaves implicit, and the choices made

* (1) for `i = 0` is `Φ.IsEquivalence` (Definition 10.1.1) for `Φ : (W, 𝐖) → (W', 𝐖')`, the
  repo's `toEpGroupoid` being `W[0]`.  `W[1]` is not built as an ep-groupoid in the repo; (1) for
  `i = 1` is read as `|Φ| : |W[1]| → |W'[1]|` a homeomorphism (`isHomeomorph_oneOrbitMap`, with
  `|W[1]|` the quotient of `W_{0,1}` by the orbit relation of `W`).  The other parts of (1) for
  `i = 1` are then consequences: the local sc-diffeomorphism property of `Φ[1]` follows from (2)
  (`isLocalScDiffeo_one`), and fullness and faithfulness at level `[1]` are those at level `[0]`
  restricted, since `𝐖[1]` consists of the `(φ, w)` with `w ∈ W_{0,1}`.
* (2): every point of the base has open `U`, `U'` with `Φ : W|U → W'|U'` a strong bundle
  isomorphism covering the sc-diffeomorphism `ϕ : U → U'` (Chapter 8's
  `StrongBundle.IsStrongBundleIsoOn`, on `[0]` and `[1]`), and the same on morphisms for the
  pull-back bundles over `𝐗`, `𝐗'`.  "Linear" is part of `IsStrongBundleFunctor`.
* `Φ*` and `Φ_*` are defined on all maps (the zero of the fibre off sections); the morphism
  `σ : ϕ(x) → x'` in `Φ_*` is chosen once for all (`preObj`, `preMor`).
* Proposition 10.4.2 is printed with `f' : W' → X'` for the section functor `X' → W'` (possible
  misprint).  The proof here takes for the text's `τ'` the morphism `Φ(Ψ*f'(x)) → Ψ(Ψ*f'(x))`
  given by `|Φ| = |Ψ|`; Proposition 10.4.3 follows the text.  Neither uses sc-smoothness.
* Proposition 10.4.4: `Ψ ∘ Φ` is a strong bundle equivalence (`IsStrongBundleEquivalence.comp`);
  the push-forward identity is stated for section functors, for which `Φ_*` does not depend on
  the choices.
* Theorem 10.4.5: "mutually inverse bijections" is `MapsTo` both ways with `InvOn` and `BijOn`.
  The second display writes `Φ* : Γ(P', μ') → Γ(P, μ)` where `Γ⁺` is meant (possible misprint);
  both directions are proved for `Γ⁺`.  The sc-smoothness of `Φ_* f`: near `x₀'`, it is
  `μ' ∘ (τ, Φ ∘ f ∘ g₁ ∘ s' ∘ τ)` with `τ` a local inverse of `t'` and `g₁` one of `ϕ`
  (`exists_pushforward_local`).

## Not formalized

* The `Fred` part of Theorem 10.4.5: it needs the invariance of `StrongBundle.IsScFredholmSection`
  (Part I's germ reading) under local strong bundle isomorphisms between strong bundles over
  M-polyfolds, which the repo does not have (Part I gives only chart-level germ statements such as
  `IsStrongBundleIso.pushforward_isFredholm_germ`).
* Proposition 10.4.6 (p. 501, new in the 2021 edition: the local regularity property, Definition
  8.4.2, under strong bundle equivalences) and Proposition 10.4.7 (p. 501, new in the 2021
  edition): strong bundle versions of Propositions 10.1.9 and 10.1.10, which are not formalized
  either (a natural representation transported along an equivalence is not provided by the
  `NaturalRep` API; the text leaves the proof of 10.4.6 to the reader).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Local strong bundle isomorphisms: restriction and composition -/

section IsoOn

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  {X'' : Type*} [TopologicalSpace X''] [T2Space X''] [ParacompactSpace X''] {PX'' : MPolyfold X''}
  {Y'' : Type*} [TopologicalSpace Y''] [T2Space Y''] [ParacompactSpace Y''] {P'' : Y'' → X''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]

namespace StrongBundle

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {B'' : StrongBundle PX'' P''}
  {f : X → X'} {Φ : Y → Y'} {h : B.IsStrongBundleMap B' f Φ} {U : Set X} {U' : Set X'}

include h in
/-- Over a local strong bundle isomorphism `Y|U → Y'|U'` with base inverse `g`, the inverse `Ψ` of
`Φ` covers `g`: `P(Ψ(w')) = g(P'(w'))` for `P'(w') ∈ U'`. -/
theorem IsStrongBundleIsoOn.P_inv {g : X' → X} (hg : PX.IsScDiffeoOn PX' f g U U') {Ψ : Y' → Y}
    (hΨ : B.toMPolyfold0.IsScDiffeoOn B'.toMPolyfold0 Φ Ψ (P ⁻¹' U) (P' ⁻¹' U')) {w' : Y'}
    (hw' : P' w' ∈ U') : P (Ψ w') = g (P' w') := by
  have h1 : Ψ w' ∈ P ⁻¹' U := hΨ.mapsTo_inv hw'
  rw [← hΨ.right_inv w' hw', h.covers, hg.left_inv _ h1, hΨ.right_inv w' hw']

/-- The same at level `[1]`. -/
theorem IsStrongBundleIsoOn.P_inv_one {g : X' → X} (hg : PX.IsScDiffeoOn PX' f g U U')
    {Ψ₁ : B'.One → B.One}
    (hΨ₁ : B.toMPolyfold1.IsScDiffeoOn B'.toMPolyfold1 (oneRestrict B B' Φ h.mapsTo_oneSet) Ψ₁
      ((P ∘ B.oneVal) ⁻¹' U) ((P' ∘ B'.oneVal) ⁻¹' U')) {w' : B'.One}
    (hw' : P' (B'.oneVal w') ∈ U') : P (B.oneVal (Ψ₁ w')) = g (P' (B'.oneVal w')) := by
  have h1 : P (B.oneVal (Ψ₁ w')) ∈ U := hΨ₁.mapsTo_inv hw'
  have h2 := congrArg B'.oneVal (hΨ₁.right_inv w' hw')
  rw [oneVal_oneRestrict] at h2
  rw [← h2, h.covers, hg.left_inv _ h1]

/-- **Restriction of a local strong bundle isomorphism** to an open `U₀ ⊆ U`: it is one
`Y|U₀ → Y'|(U' ∩ g⁻¹(U₀))` for the base inverse `g`. -/
theorem IsStrongBundleIsoOn.restrict (hi : B.IsStrongBundleIsoOn B' h U U') {g : X' → X}
    (hg : PX.IsScDiffeoOn PX' f g U U') {U₀ : Set X} (hU₀ : IsOpen U₀) (hsub : U₀ ⊆ U) :
    B.IsStrongBundleIsoOn B' h U₀ (U' ∩ g ⁻¹' U₀) := by
  obtain ⟨Ψ, hΨ⟩ := hi.isScDiffeoOn_zero
  obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
  refine ⟨⟨g, hg.restrict hU₀ hsub⟩, ⟨Ψ, ?_⟩, ⟨Ψ₁, ?_⟩⟩
  · have e := hΨ.restrict (hU₀.preimage B.continuous) (preimage_mono hsub)
    have hset : P' ⁻¹' U' ∩ Ψ ⁻¹' (P ⁻¹' U₀) = P' ⁻¹' (U' ∩ g ⁻¹' U₀) := by
      ext w'
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [← IsStrongBundleIsoOn.P_inv (h := h) hg hΨ h1]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [IsStrongBundleIsoOn.P_inv (h := h) hg hΨ h1]; exact h2⟩
    rwa [hset] at e
  · have hc : Continuous (P ∘ B.oneVal) := B.continuous.comp B.continuous_oneVal
    have e := hΨ₁.restrict (hU₀.preimage hc) (preimage_mono hsub)
    have hset : (P' ∘ B'.oneVal) ⁻¹' U' ∩ Ψ₁ ⁻¹' ((P ∘ B.oneVal) ⁻¹' U₀) =
        (P' ∘ B'.oneVal) ⁻¹' (U' ∩ g ⁻¹' U₀) := by
      ext w'
      simp only [mem_inter_iff, mem_preimage, Function.comp_apply]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [← IsStrongBundleIsoOn.P_inv_one (h := h) hg hΨ₁ h1]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [IsStrongBundleIsoOn.P_inv_one (h := h) hg hΨ₁ h1]; exact h2⟩
    rwa [hset] at e

/-- **Composition of local strong bundle isomorphisms** `Y|U → Y'|U' → Y''|U''`. -/
theorem IsStrongBundleIsoOn.comp {f' : X' → X''} {Ψ : Y' → Y''}
    {h' : B'.IsStrongBundleMap B'' f' Ψ} {U'' : Set X''}
    (hi' : B'.IsStrongBundleIsoOn B'' h' U' U'') (hi : B.IsStrongBundleIsoOn B' h U U') :
    B.IsStrongBundleIsoOn B'' (h'.comp h) U U'' := by
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨g', hg'⟩ := hi'.isScDiffeoOn_base
  obtain ⟨Φi, hΦi⟩ := hi.isScDiffeoOn_zero
  obtain ⟨Ψi, hΨi⟩ := hi'.isScDiffeoOn_zero
  obtain ⟨Φ₁, hΦ₁⟩ := hi.isScDiffeoOn_one
  obtain ⟨Ψ₁, hΨ₁⟩ := hi'.isScDiffeoOn_one
  exact ⟨⟨_, hg'.comp hg⟩, ⟨_, hΨi.comp hΦi⟩, ⟨_, hΨ₁.comp hΦ₁⟩⟩

/-- **Composition at a point**: if `Φ` is a strong bundle isomorphism over `U ∋ x` and `Ψ` one
over `V' ∋ f(x)`, then `Ψ ∘ Φ` is one over an open neighbourhood of `x`. -/
theorem IsStrongBundleIsoOn.exists_comp {f' : X' → X''} {Ψ : Y' → Y''}
    {h' : B'.IsStrongBundleMap B'' f' Ψ} {V' : Set X'} {V'' : Set X''}
    (hi' : B'.IsStrongBundleIsoOn B'' h' V' V'') (hi : B.IsStrongBundleIsoOn B' h U U') {x : X}
    (hx : x ∈ U) (hfx : f x ∈ V') :
    ∃ (U₀ : Set X) (U₀'' : Set X''), x ∈ U₀ ∧ B.IsStrongBundleIsoOn B'' (h'.comp h) U₀ U₀'' := by
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨g', hg'⟩ := hi'.isScDiffeoOn_base
  have hU₀ : IsOpen (U ∩ f ⁻¹' V') :=
    hg.isScSmoothOn.continuousOn.isOpen_inter_preimage hg.isOpen_source hg'.isOpen_source
  have e₁ := hi.restrict hg hU₀ inter_subset_left
  have hsub : U' ∩ g ⁻¹' (U ∩ f ⁻¹' V') ⊆ V' := fun y hy => by
    have := hy.2.2
    rwa [mem_preimage, hg.right_inv y hy.1] at this
  have hopen : IsOpen (U' ∩ g ⁻¹' (U ∩ f ⁻¹' V')) :=
    (hg.restrict hU₀ inter_subset_left).isOpen_target
  exact ⟨U ∩ f ⁻¹' V', _, ⟨hx, hfx⟩, (hi'.restrict hg' hopen hsub).comp e₁⟩

end StrongBundle

end IsoOn

/-! ### The level-`[1]` universal property of the pull-back on an open set -/

section PullbackOneOn

namespace MPolyfold

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {PY : MPolyfold Y}

/-- The local form of `MPolyfold.isScSmoothMap_of_forall_charts`: `f` is sc-smooth on the open `U`
if every `x ∈ U` lies in a chart domain `dom φ ⊆ U` with `f(dom φ) ⊆ dom ψ` and `ψ ∘ f ∘ φ⁻¹`
sc-smooth (the continuity on `U` follows from the charts). -/
theorem isScSmoothOn_of_forall_charts {f : X → Y} {U : Set X} (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ (φ : MChart X) (ψ : MChart Y), PX.IsChart φ ∧ PY.IsChart ψ ∧ x ∈ φ.source ∧
      φ.source ⊆ U ∧ MapsTo f φ.source ψ.source ∧
      IsScSmoothRetractMap φ.model.E φ.model.C φ.model.O ψ.model.E ψ.model.C ψ.model.O
        (ψ ∘ f ∘ φ.symm)) :
    PX.IsScSmoothOn PY f U := by
  have hloc : ∀ x ∈ U, ∃ φ : MChart X, x ∈ φ.source ∧ ContinuousOn f φ.source := fun x hx => by
    obtain ⟨φ, ψ, -, -, hx, -, hmaps, hsm⟩ := h x hx
    refine ⟨φ, hx, ?_⟩
    have h1 : ContinuousOn (ψ.symm ∘ (ψ ∘ f ∘ φ.symm) ∘ φ) φ.source :=
      (ψ.continuousOn_invFun.comp (hsm.continuousOn φ.model.isScRetract) hsm.mapsTo).comp
        φ.continuousOn_toFun fun z hz => φ.mapsTo_model z hz
    refine h1.congr fun z hz => ?_
    simp only [Function.comp_apply, φ.symm_apply_apply hz, ψ.symm_apply_apply (hmaps hz)]
  have hc : ContinuousOn f U := fun x hx => by
    obtain ⟨φ, hxφ, hcont⟩ := hloc x hx
    exact (hcont.continuousAt (φ.isOpen_source.mem_nhds hxφ)).continuousWithinAt
  refine IsScSmoothOn.of_exists_charts hU hc fun x hx => ?_
  obtain ⟨φ, ψ, hφ, hψ, hxφ, hsub, hmaps, hsm⟩ := h x hx
  refine ⟨φ, ψ, φ.source, hφ, hψ, φ.isOpen_source, hxφ, fun z hz => ⟨hsub hz, hz⟩, hmaps, ?_⟩
  rw [φ.image_source]; exact hsm

end MPolyfold

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {f : Z → X} [ParacompactSpace (pullbackSpace P f)]
  {V : Type*} [TopologicalSpace V] [T2Space V] [ParacompactSpace V] {Q : MPolyfold V}

namespace StrongBundle

variable (B : StrongBundle PX P) (hf : PZ.IsScSmoothMap PX f)

/-- **The universal property of the pull-back at level `[1]`, on an open set** (the local form of
`StrongBundle.isScSmoothMap_to_pullback_one`): `ι : V → f*Y[1]` is sc-smooth on `U` as soon as
`P_f ∘ ι` and `P'[1] ∘ ι` are. -/
theorem isScSmoothOn_to_pullback_one {ι : V → (B.pullback hf).One} {U : Set V}
    (ha : Q.IsScSmoothOn PZ (pullbackProj P f ∘ (B.pullback hf).oneVal ∘ ι) U)
    (hb : Q.IsScSmoothOn B.toMPolyfold1 (B.pullbackProj'One hf ∘ ι) U) :
    Q.IsScSmoothOn (B.pullback hf).toMPolyfold1 ι U := by
  refine MPolyfold.isScSmoothOn_of_forall_charts ha.isOpen fun v hv => ?_
  obtain ⟨d, hd, hq⟩ := PullbackChartData.exists_mem_atlas B hf ((B.pullback hf).oneVal (ι v))
  have hmem := B.toChart_mem_pullback_atlas hf hd ((B.pullback hf).oneVal (ι v))
  obtain ⟨φ, hφ, hvφ⟩ := Q.exists_isChart_mem_source v
  have hso : IsOpen ((U ∩ φ.source) ∩
      (pullbackProj P f ∘ (B.pullback hf).oneVal ∘ ι) ⁻¹' d.ψ.source) :=
    (ha.continuousOn.mono inter_subset_left).isOpen_inter_preimage
      (ha.isOpen.inter φ.isOpen_source) d.ψ.isOpen_source
  have hsub : (U ∩ φ.source) ∩ (pullbackProj P f ∘ (B.pullback hf).oneVal ∘ ι) ⁻¹' d.ψ.source ⊆
      φ.source := fun x hx => hx.1.2
  set φ' := φ.restrict hsub hso with hφ'def
  have hφ' : Q.IsChart φ' := MPolyfold.IsChart.restrict Q hφ hsub hso
  set y' := B.pullbackProj'One hf (ι v)
  refine ⟨φ', oneChart hmem (ι v), hφ', (B.pullback hf).isChart_oneChart hmem (ι v),
    ⟨⟨hv, hvφ⟩, hq⟩, fun x hx => hx.1.1, fun x hx => hx.2, ?_⟩
  have h1 := ha.smooth φ' d.ψ hφ' d.isChart φ'.source φ'.isOpen_source
    (fun x hx => ⟨hx.1.1, hx⟩) fun x hx => hx.2
  have h2 := hb.smooth φ' (oneChart hd y') hφ' (B.isChart_oneChart hd y') φ'.source
    φ'.isOpen_source (fun x hx => ⟨hx.1.1, hx⟩) fun x hx => d.mem_c_source hx.2
  have h3 : IsScSmoothRetractMap (d.c.φ.model.E.prod d.c.F.shift) (d.c.φ.model.C ×ˢ univ)
      (strongShiftOne d.c.K) d.c.F.shift univ univ Prod.snd :=
    (d.c.φ.model.E.prodSndOp d.c.F.shift).isScSmoothRetractMap d.c.isScRetract_one
      (mapsTo_univ _ _)
  have h4 := h3.comp h2 d.c.isScRetract_one
  rw [φ'.image_source] at h1 h4
  refine (IsScSmoothRetractMap.scPair h1 h4 ?_).congr fun _ _ => rfl
  intro z hz
  obtain ⟨x, hx, rfl⟩ : z ∈ φ' '' φ'.source := by rw [φ'.image_source]; exact hz
  change (oneChart hmem (ι v)) (ι (φ'.symm (φ' x))) ∈ strongShiftOne (d.toChart _).K
  rw [φ'.symm_apply_apply hx]
  exact (oneChart hmem (ι v)).toPartialEquiv.map_source
    (show ι x ∈ (oneChart hmem (ι v)).source from hx.2)

end StrongBundle

end PullbackOneOn

/-! ### Strong bundle functors: composition; the orbit space of `W[1]` -/

section Functors

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type u} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]
  {Obj'' Mor'' : Type u} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor''] {X'' : EpGroupoid Obj'' Mor''}
  {W'' : Type u} [TopologicalSpace W''] [T2Space W''] [ParacompactSpace W''] {P'' : W'' → Obj''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]
  {B'' : StrongBundle X''.PObj P''} [ParacompactSpace (pullbackSpace P'' X''.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {E'' : EpStrongBundle X'' B''}

namespace EpStrongBundle

/-- **The composition of strong bundle functors** is a strong bundle functor (covering the
composite `ψ ∘ ϕ`). -/
theorem IsStrongBundleFunctor.comp {ϕ : EpFunctor X X'} {ψ : EpFunctor X' X''}
    {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} {Ψ : EpFunctor E'.toEpGroupoid E''.toEpGroupoid}
    (h₂ : E'.IsStrongBundleFunctor E'' ψ Ψ) (h₁ : E.IsStrongBundleFunctor E' ϕ Φ) :
    E.IsStrongBundleFunctor E'' (ψ.comp ϕ) (Ψ.comp Φ) :=
  ⟨h₂.isStrongBundleMap_obj.comp h₁.isStrongBundleMap_obj,
    h₂.isStrongBundleMap_mor.comp h₁.isStrongBundleMap_mor⟩

variable (E) in
/-- The orbit relation of `(W, 𝐖)` on `W[1] = W_{0,1}`: two points of `W_{0,1}` are isomorphic in
`W[1]` iff they are in `W` (a morphism `(φ, w) ∈ 𝐖` with `w ∈ W_{0,1}` lies in `𝐖[1]`). -/
def oneOrbitSetoid : Setoid B.One := Setoid.comap B.oneVal E.toGroupoidStr.orbitSetoid

variable (E) in
/-- **`|W[1]|`**, the orbit space of `W[1]`, with the quotient topology of `W[1]`. -/
abbrev OneOrbitSpace : Type u := Quotient E.oneOrbitSetoid

variable (E E') in
/-- The map `|Φ| : |W[1]| → |W'[1]|` induced by a functor `Φ : (W, 𝐖) → (W', 𝐖')` which maps
`W_{0,1}` into `W'_{0,1}`. -/
def oneOrbitMap (Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid)
    (hΦ : MapsTo Φ.obj B.oneSet B'.oneSet) : E.OneOrbitSpace → E'.OneOrbitSpace :=
  Quotient.map (StrongBundle.oneRestrict B B' Φ.obj hΦ) fun a b hab => by
    obtain ⟨φ, hs, ht⟩ := hab
    exact ⟨Φ.mor φ, (Φ.src_mor φ).trans (congrArg Φ.obj hs),
      (Φ.tgt_mor φ).trans (congrArg Φ.obj ht)⟩

@[simp] lemma oneOrbitMap_mk (Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid)
    (hΦ : MapsTo Φ.obj B.oneSet B'.oneSet) (w : B.One) :
    E.oneOrbitMap E' Φ hΦ (Quotient.mk _ w) =
      Quotient.mk _ (StrongBundle.oneRestrict B B' Φ.obj hΦ w) := rfl

theorem continuous_oneOrbitMap {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    {hΦ : MapsTo Φ.obj B.oneSet B'.oneSet}
    (hc : Continuous (StrongBundle.oneRestrict B B' Φ.obj hΦ)) :
    Continuous (E.oneOrbitMap E' Φ hΦ) :=
  continuous_quot_lift _ (continuous_quot_mk.comp hc)

theorem oneOrbitMap_id (hΦ : MapsTo (EpFunctor.id E.toEpGroupoid).obj B.oneSet B.oneSet) :
    E.oneOrbitMap E (EpFunctor.id E.toEpGroupoid) hΦ = id := by
  funext q
  induction q using Quotient.inductionOn with | h w => rfl

theorem oneOrbitMap_comp {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    {Ψ : EpFunctor E'.toEpGroupoid E''.toEpGroupoid} (hΦ : MapsTo Φ.obj B.oneSet B'.oneSet)
    (hΨ : MapsTo Ψ.obj B'.oneSet B''.oneSet) (hΨΦ : MapsTo (Ψ.comp Φ).obj B.oneSet B''.oneSet) :
    E.oneOrbitMap E'' (Ψ.comp Φ) hΨΦ = E'.oneOrbitMap E'' Ψ hΨ ∘ E.oneOrbitMap E' Φ hΦ := by
  funext q
  induction q using Quotient.inductionOn with | h w => rfl

/-! ### Definition 10.4.1: strong bundle equivalences -/

variable (E E') in
/-- **2021 Definition 10.4.1, p. 496 (2017: Definition 10.10)**: a **strong bundle equivalence**
`Φ : (P : W → X, μ) → (P' : W' → X', μ')` is a linear strong bundle functor `Φ : (W, 𝐖) →
(W', 𝐖')` covering `ϕ : X → X'` (Definition 8.3.3, `IsStrongBundleFunctor`; linearity on the fibres
is part of it) with (1) `ϕ` an equivalence, `Φ : W[0] → W'[0]` an equivalence of ep-groupoids
(`(W, 𝐖)` is `W[0]`), and, for `W[1]`, `|Φ| : |W[1]| → |W'[1]|` a homeomorphism; (2) the maps
`Φ : W → W'` and `Φ : 𝐖 → 𝐖'` local strong bundle isomorphisms (every point of the base has an
open `U` with `Φ : W|U → W'|U'` a strong bundle isomorphism covering `ϕ : U → U'`).  On (1) for
`W[1]`: its local sc-diffeomorphism property follows from (2) (`isLocalScDiffeo_one`), and
fullness and faithfulness are those of `W[0]` restricted, since `𝐖[1]` consists of the
`(φ, w) ∈ 𝐖` with `w ∈ W_{0,1}`. -/
structure IsStrongBundleEquivalence (ϕ : EpFunctor X X')
    (Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid) : Prop where
  isStrongBundleFunctor : E.IsStrongBundleFunctor E' ϕ Φ
  isEquivalence_base : ϕ.IsEquivalence
  isEquivalence : Φ.IsEquivalence
  isHomeomorph_oneOrbitMap :
    IsHomeomorph (E.oneOrbitMap E' Φ isStrongBundleFunctor.isStrongBundleMap_obj.mapsTo_oneSet)
  isLocalStrongBundleIso_obj : ∀ x : Obj, ∃ (U : Set Obj) (U' : Set Obj'), x ∈ U ∧
    B.IsStrongBundleIsoOn B' isStrongBundleFunctor.isStrongBundleMap_obj U U'
  isLocalStrongBundleIso_mor : ∀ φ : Mor, ∃ (U : Set Mor) (U' : Set Mor'), φ ∈ U ∧
    (B.pullback X.isScSmoothMap_src).IsStrongBundleIsoOn (B'.pullback X'.isScSmoothMap_src)
      isStrongBundleFunctor.isStrongBundleMap_mor U U'

namespace IsStrongBundleEquivalence

variable {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (h : E.IsStrongBundleEquivalence E' ϕ Φ)
include h

/-- `Φ` covers `ϕ`: `P' ∘ Φ = ϕ ∘ P`. -/
theorem covers (w : W) : P' (Φ.obj w) = ϕ.obj (P w) :=
  h.isStrongBundleFunctor.isStrongBundleMap_obj.covers w

/-- **The fibre maps `Φ_x : W_x → W'_{ϕ(x)}` are topological linear isomorphisms** (from (2)). -/
def fiberEquiv (x : Obj) : P ⁻¹' {x} ≃L[ℝ] P' ⁻¹' {ϕ.obj x} :=
  (Classical.choose_spec (Classical.choose_spec (h.isLocalStrongBundleIso_obj x))).2.fiberEquiv
    (Classical.choose_spec (Classical.choose_spec (h.isLocalStrongBundleIso_obj x))).1

@[simp] lemma fiberEquiv_apply (x : Obj) (v : P ⁻¹' {x}) : (h.fiberEquiv x v : W') = Φ.obj v :=
  rfl

/-- `Φ` is injective on the fibres. -/
theorem eq_of_obj_eq {w w₁ : W} (hP : P w = P w₁) (he : Φ.obj w = Φ.obj w₁) : w = w₁ := by
  have := (h.fiberEquiv (P w₁)).injective (a₁ := ⟨w, hP⟩) (a₂ := ⟨w₁, rfl⟩) (Subtype.ext he)
  exact congrArg Subtype.val this

/-- (1) for `W[1]`, the local sc-diffeomorphism part: **`Φ : W[1] → W'[1]` is a local
sc-diffeomorphism**, from (2). -/
theorem isLocalScDiffeo_one :
    B.toMPolyfold1.IsLocalScDiffeo B'.toMPolyfold1 (StrongBundle.oneRestrict B B' Φ.obj
      h.isStrongBundleFunctor.isStrongBundleMap_obj.mapsTo_oneSet) := fun w => by
  obtain ⟨U, U', hx, hi⟩ := h.isLocalStrongBundleIso_obj (P (B.oneVal w))
  obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
  exact ⟨_, _, Ψ₁, hx, hΨ₁⟩

/-- `Φ : W → W'` is a local sc-diffeomorphism (Definition 10.1.1 (3) for `W[0]`). -/
theorem isLocalScDiffeo_obj : B.toMPolyfold0.IsLocalScDiffeo B'.toMPolyfold0 Φ.obj :=
  h.isEquivalence.isLocalScDiffeo_obj

/-- `ϕ` is full, in terms of the structure maps. -/
theorem exists_mor_eq {x y : Obj} {ψ : Mor'} (hs : X'.src ψ = ϕ.obj x) (ht : X'.tgt ψ = ϕ.obj y) :
    ∃ φ, X.src φ = x ∧ X.tgt φ = y ∧ ϕ.mor φ = ψ :=
  h.isEquivalence_base.exists_mor_eq hs ht

end IsStrongBundleEquivalence

/-- **The identity is a strong bundle equivalence.** -/
theorem isStrongBundleEquivalence_id (E : EpStrongBundle X B) :
    E.IsStrongBundleEquivalence E (EpFunctor.id X) (EpFunctor.id E.toEpGroupoid) where
  isStrongBundleFunctor := E.isStrongBundleFunctor_id
  isEquivalence_base := EpFunctor.IsEquivalence.id X
  isEquivalence := EpFunctor.IsEquivalence.id E.toEpGroupoid
  isHomeomorph_oneOrbitMap := by rw [oneOrbitMap_id]; exact IsHomeomorph.id
  isLocalStrongBundleIso_obj x := ⟨univ, univ, mem_univ x, B.isStrongBundleIsoOn_id isOpen_univ⟩
  isLocalStrongBundleIso_mor φ := ⟨univ, univ, mem_univ φ,
    (B.pullback X.isScSmoothMap_src).isStrongBundleIsoOn_id isOpen_univ⟩

/-- **The composition of strong bundle equivalences is a strong bundle equivalence.** -/
theorem IsStrongBundleEquivalence.comp {ϕ : EpFunctor X X'} {ψ : EpFunctor X' X''}
    {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} {Ψ : EpFunctor E'.toEpGroupoid E''.toEpGroupoid}
    (h₂ : E'.IsStrongBundleEquivalence E'' ψ Ψ) (h₁ : E.IsStrongBundleEquivalence E' ϕ Φ) :
    E.IsStrongBundleEquivalence E'' (ψ.comp ϕ) (Ψ.comp Φ) where
  isStrongBundleFunctor := h₂.isStrongBundleFunctor.comp h₁.isStrongBundleFunctor
  isEquivalence_base := h₂.isEquivalence_base.comp h₁.isEquivalence_base
  isEquivalence := h₂.isEquivalence.comp h₁.isEquivalence
  isHomeomorph_oneOrbitMap := by
    rw [oneOrbitMap_comp h₁.isStrongBundleFunctor.isStrongBundleMap_obj.mapsTo_oneSet
      h₂.isStrongBundleFunctor.isStrongBundleMap_obj.mapsTo_oneSet]
    exact h₂.isHomeomorph_oneOrbitMap.comp h₁.isHomeomorph_oneOrbitMap
  isLocalStrongBundleIso_obj x := by
    obtain ⟨U, U', hx, hi⟩ := h₁.isLocalStrongBundleIso_obj x
    obtain ⟨V', V'', hy, hi'⟩ := h₂.isLocalStrongBundleIso_obj (ϕ.obj x)
    exact hi'.exists_comp hi hx hy
  isLocalStrongBundleIso_mor φ := by
    obtain ⟨U, U', hx, hi⟩ := h₁.isLocalStrongBundleIso_mor φ
    obtain ⟨V', V'', hy, hi'⟩ := h₂.isLocalStrongBundleIso_mor (ϕ.mor φ)
    exact hi'.exists_comp hi hx hy

/-! ### Pull-backs and push-forwards of section functors -/

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- `μ(ψ, ·)` is injective. -/
theorem μ_injective_snd (E : EpStrongBundle X B) {ψ : Mor} {a b : W} (ha : P a = X.src ψ)
    (hb : P b = X.src ψ) (he : E.μ ⟨(ψ, a), ha⟩ = E.μ ⟨(ψ, b), hb⟩) : a = b := by
  have h1 := E.μ_inv_μ ⟨(ψ, a), ha⟩ (by rw [E.P_μ]; exact (X.src_inv ψ).symm)
  have h2 := E.μ_inv_μ ⟨(ψ, b), hb⟩ (by rw [E.P_μ]; exact (X.src_inv ψ).symm)
  refine h1.symm.trans (Eq.trans ?_ h2)
  exact E.μ_congr (by simp only [he])

namespace IsStrongBundleEquivalence

variable {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (h : E.IsStrongBundleEquivalence E' ϕ Φ)

open scoped Classical in
/-- **The pull-back `Φ*(f')`** of a section `f'` of `P'` (p. 496):
`Φ*(f')(x) = Φ_x⁻¹(f'(ϕ(x))) ∈ W_x`.  (The zero of `W_x` where `f'(ϕ(x)) ∉ W'_{ϕ(x)}`; this does
not occur for sections.) -/
def pullback (f' : Obj' → W') (x : Obj) : W :=
  if hx : P' (f' (ϕ.obj x)) = ϕ.obj x then ((h.fiberEquiv x).symm ⟨f' (ϕ.obj x), hx⟩ : W)
  else fiberZero P x

theorem P_pullback (f' : Obj' → W') (x : Obj) : P (h.pullback f' x) = x := by
  unfold pullback
  split_ifs
  · exact ((h.fiberEquiv x).symm _).2
  · exact isSection_fiberZero x

theorem isSection_pullback (f' : Obj' → W') : IsSection P (h.pullback f') := h.P_pullback f'

/-- `Φ(Φ*(f')(x)) = f'(ϕ(x))`. -/
theorem obj_pullback {f' : Obj' → W'} (hf' : IsSection P' f') (x : Obj) :
    Φ.obj (h.pullback f' x) = f' (ϕ.obj x) := by
  unfold pullback
  rw [dif_pos (hf' _)]
  exact congrArg Subtype.val ((h.fiberEquiv x).apply_symm_apply ⟨f' (ϕ.obj x), hf' _⟩)

/-- `Φ*(f')(x)` is the only `w ∈ W_x` with `Φ(w) = f'(ϕ(x))`. -/
theorem pullback_eq {f' : Obj' → W'} (hf' : IsSection P' f') {x : Obj} {w : W} (hw : P w = x)
    (he : Φ.obj w = f' (ϕ.obj x)) : h.pullback f' x = w :=
  h.eq_of_obj_eq ((h.P_pullback f' x).trans hw.symm) ((h.obj_pullback hf' x).trans he.symm)

/-- **The pull-back of a section functor is a section functor** (functoriality (10.16)):
`Φ(μ(φ, Φ*f'(s φ))) = μ'(ϕ(φ), f'(ϕ(s φ))) = f'(ϕ(t φ))`. -/
theorem isFunctorialSection_pullback {f' : Obj' → W'} (hf' : IsSection P' f')
    (hfun : E'.IsFunctorialSection hf') : E.IsFunctorialSection (h.isSection_pullback f') := by
  intro φ
  refine h.pullback_eq hf' (E.P_μ _) ?_
  change Φ.obj (E.μ ⟨(φ, h.pullback f' (X.src φ)), _⟩) = _
  rw [h.isStrongBundleFunctor.isMap.map_μ φ _ (h.P_pullback f' (X.src φ)), ← ϕ.tgt_mor φ,
    hfun (ϕ.mor φ)]
  refine E'.μ_congr (Prod.ext rfl ?_)
  change Φ.obj (h.pullback f' (X.src φ)) = f' (X'.src (ϕ.mor φ))
  rw [h.obj_pullback hf', ϕ.src_mor]

/-- A choice of `x ∈ X` for `x' ∈ X'` with a morphism `ϕ(x) → x'` (`ϕ` is essentially
surjective). -/
def preObj (x' : Obj') : Obj := (h.isEquivalence_base.exists_iso x').choose

/-- The chosen morphism `σ : ϕ(x) → x'`. -/
def preMor (x' : Obj') : Mor' := (h.isEquivalence_base.exists_iso x').choose_spec.choose

theorem src_preMor (x' : Obj') : X'.src (h.preMor x') = ϕ.obj (h.preObj x') :=
  (h.isEquivalence_base.exists_iso x').choose_spec.choose_spec.1

theorem tgt_preMor (x' : Obj') : X'.tgt (h.preMor x') = x' :=
  (h.isEquivalence_base.exists_iso x').choose_spec.choose_spec.2

open scoped Classical in
/-- **The push-forward `Φ_*(f)`** of a section `f` of `P` (p. 498): `(Φ_* f)(x') = μ'(σ, Φ(f(x)))`
for the chosen `x ∈ X` and `σ : ϕ(x) → x'`.  (The zero of `W'_{x'}` where `f(x) ∉ W_x`; this does
not occur for sections.) -/
def pushforward (f : Obj → W) (x' : Obj') : W' :=
  if hx : P (f (h.preObj x')) = h.preObj x' then
    E'.μ ⟨(h.preMor x', Φ.obj (f (h.preObj x'))), by
      change P' (Φ.obj _) = X'.src _
      rw [h.covers, hx, h.src_preMor]⟩
  else fiberZero P' x'

theorem pushforward_def {f : Obj → W} (hf : IsSection P f) (x' : Obj') :
    h.pushforward f x' = E'.μ ⟨(h.preMor x', Φ.obj (f (h.preObj x'))),
      (h.covers _).trans ((congrArg ϕ.obj (hf _)).trans (h.src_preMor x').symm)⟩ := by
  unfold pushforward
  rw [dif_pos (hf _)]

theorem P_pushforward (f : Obj → W) (x' : Obj') : P' (h.pushforward f x') = x' := by
  unfold pushforward
  split_ifs
  · rw [E'.P_μ]; exact h.tgt_preMor x'
  · exact isSection_fiberZero x'

theorem isSection_pushforward (f : Obj → W) : IsSection P' (h.pushforward f) := h.P_pushforward f

/-- **The push-forward is well defined (10.22)**: for a section functor `f`, every `y ∈ X` and
every `σ' : ϕ(y) → x'`, `(Φ_* f)(x') = μ'(σ', Φ(f(y)))`.  (With `σ : ϕ(x) → x'` the chosen
morphism, fullness of `ϕ` gives `τ : y → x` with `ϕ(τ) = σ⁻¹ ∘ σ'`.) -/
theorem pushforward_eq {f : Obj → W} (hf : IsSection P f) (hfun : E.IsFunctorialSection hf)
    {x' : Obj'} {y : Obj} {σ' : Mor'} (hs : X'.src σ' = ϕ.obj y) (ht : X'.tgt σ' = x') :
    h.pushforward f x' =
      E'.μ ⟨(σ', Φ.obj (f y)), (h.covers _).trans ((congrArg ϕ.obj (hf y)).trans hs.symm)⟩ := by
  have hc : X'.src (X'.inv (h.preMor x')) = X'.tgt σ' := by rw [X'.src_inv, h.tgt_preMor, ht]
  have hsrc : X'.src (X'.comp (X'.inv (h.preMor x')) σ') = ϕ.obj y := by
    rw [X'.src_comp _ _ hc, hs]
  have htgt : X'.tgt (X'.comp (X'.inv (h.preMor x')) σ') = ϕ.obj (h.preObj x') := by
    rw [X'.tgt_comp _ _ hc, X'.tgt_inv, h.src_preMor]
  obtain ⟨τ, hτs, hτt, hτ⟩ := h.exists_mor_eq hsrc htgt
  have hσ' : X'.comp (h.preMor x') (ϕ.mor τ) = σ' := by
    rw [hτ]
    have := GroupoidStr.inv_comp_cancel_left (G := X'.toGroupoidStr) (φ := X'.inv (h.preMor x'))
      (ψ := σ') hc
    rwa [GroupoidStr.inv_inv] at this
  have hfx : f (h.preObj x') = E.μ ⟨(τ, f y), (hf y).trans hτs.symm⟩ := by
    have h0 := hfun τ
    rw [hτt] at h0
    rw [h0]
    refine E.μ_congr (Prod.ext rfl ?_)
    change f (X.src τ) = f y
    rw [hτs]
  have h₁ : P' (Φ.obj (f y)) = X'.src (ϕ.mor τ) := by rw [h.covers, hf y, ϕ.src_mor, hτs]
  have h₂ : X'.src (h.preMor x') = X'.tgt (ϕ.mor τ) := by rw [ϕ.tgt_mor, hτt, h.src_preMor]
  unfold pushforward
  rw [dif_pos (hf _)]
  refine Eq.trans ?_ ((E'.μ_comp (h.preMor x') (ϕ.mor τ) (Φ.obj (f y)) h₁ h₂).symm.trans
    (E'.μ_congr (Prod.ext hσ' rfl)))
  refine E'.μ_congr (Prod.ext rfl ?_)
  change Φ.obj (f (h.preObj x')) = _
  rw [hfx, h.isStrongBundleFunctor.isMap.map_μ]

/-- **The push-forward of a section functor is a section functor**: for `φ' : x' → y'`,
`(Φ_* f)(y') = μ'(φ' ∘ σ, Φ(f(x))) = μ'(φ', (Φ_* f)(x'))` (by (10.22)). -/
theorem isFunctorialSection_pushforward {f : Obj → W} (hf : IsSection P f)
    (hfun : E.IsFunctorialSection hf) : E'.IsFunctorialSection (h.isSection_pushforward f) := by
  intro φ'
  set σ := h.preMor (X'.src φ')
  have h₂ : X'.src φ' = X'.tgt σ := (h.tgt_preMor _).symm
  have h₁ : P' (Φ.obj (f (h.preObj (X'.src φ')))) = X'.src σ := by
    rw [h.covers, hf, h.src_preMor]
  have hs : X'.src (X'.comp φ' σ) = ϕ.obj (h.preObj (X'.src φ')) := by
    rw [X'.src_comp _ _ h₂, h.src_preMor]
  have ht : X'.tgt (X'.comp φ' σ) = X'.tgt φ' := X'.tgt_comp _ _ h₂
  rw [h.pushforward_eq hf hfun hs ht, E'.μ_comp φ' σ _ h₁ h₂]
  refine E'.μ_congr (Prod.ext rfl ?_)
  change _ = h.pushforward f (X'.src φ')
  unfold pushforward
  rw [dif_pos (hf _)]

/-- **`Φ*(Φ_* f) = f`** for a section functor `f` (p. 500, "`Φ_*` and `Φ*` are mutual
inverses"). -/
theorem pullback_pushforward {f : Obj → W} (hf : IsSection P f) (hfun : E.IsFunctorialSection hf) :
    h.pullback (h.pushforward f) = f := by
  funext x
  refine h.pullback_eq (h.isSection_pushforward f) (hf x) ?_
  rw [h.pushforward_eq hf hfun (y := x) (σ' := X'.unit (ϕ.obj x)) (X'.src_unit _) (X'.tgt_unit _)]
  symm
  have e : X'.unit (ϕ.obj x) = X'.unit (P' (Φ.obj (f x))) := by rw [h.covers, hf x]
  refine Eq.trans ?_ (E'.μ_unit (Φ.obj (f x)))
  exact E'.μ_congr (Prod.ext e rfl)

/-- **`Φ_*(Φ* f') = f'`** for a section functor `f'`. -/
theorem pushforward_pullback {f' : Obj' → W'} (hf' : IsSection P' f')
    (hfun : E'.IsFunctorialSection hf') : h.pushforward (h.pullback f') = f' := by
  funext x'
  unfold pushforward
  rw [dif_pos (h.P_pullback f' _), ← congrArg f' (h.tgt_preMor x'), hfun (h.preMor x')]
  refine E'.μ_congr (Prod.ext rfl ?_)
  change Φ.obj (h.pullback f' (h.preObj x')) = f' (X'.src (h.preMor x'))
  rw [h.obj_pullback hf', h.src_preMor]

end IsStrongBundleEquivalence

/-! ### Propositions 10.4.2 and 10.4.3 -/

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- `μ` evaluated at two pairs with equal components (the membership proofs are irrelevant). -/
theorem μ_mk_congr {σ σ' : Mor} {w w' : W} (hσ : σ = σ') (hw : w = w') (h : P w = X.src σ)
    (h' : P w' = X.src σ') : E.μ ⟨(σ, w), h⟩ = E.μ ⟨(σ', w'), h'⟩ := by
  subst hσ hw; rfl

/-- `|Φ| = |Ψ|` on `|W|` gives, for every `w`, a morphism `Φ(w) → Ψ(w)` of `(W', 𝐖')`, i.e. a pair
`(σ, Φ(w)) ∈ 𝐗' ₛ×_{P'} W'` with `μ'(σ, Φ(w)) = Ψ(w)` ((10.15)). -/
theorem exists_μ_eq_of_orbitMap_eq {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (hΦΨ : Φ.orbitMap = Ψ.orbitMap) (w : W) :
    ∃ q : pullbackSpace P' X'.src, (q : Mor' × W').2 = Φ.obj w ∧ E'.μ q = Ψ.obj w := by
  have h1 := congrFun hΦΨ (E.toEpGroupoid.π w)
  rw [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π] at h1
  obtain ⟨q, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 h1
  exact ⟨q, hs, ht⟩

namespace IsStrongBundleEquivalence

variable {ϕ ψ : EpFunctor X X'} {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}

/-- Proposition 10.4.2 for functorial sections (sc-smoothness is not used). -/
theorem pullback_eq_of_orbitMap_eq (hΦ : E.IsStrongBundleEquivalence E' ϕ Φ)
    (hΨ : E.IsStrongBundleEquivalence E' ψ Ψ) (hΦΨ : Φ.orbitMap = Ψ.orbitMap) {f' : Obj' → W'}
    (hf' : IsSection P' f') (hfun : E'.IsFunctorialSection hf') :
    hΦ.pullback f' = hΨ.pullback f' := by
  funext x
  obtain ⟨⟨⟨σ, w'⟩, hq⟩, hq2, hqμ⟩ := exists_μ_eq_of_orbitMap_eq hΦΨ (hΨ.pullback f' x)
  change w' = _ at hq2
  subst hq2
  have hq' : P' (Φ.obj (hΨ.pullback f' x)) = X'.src σ := hq
  have hsσ : X'.src σ = ϕ.obj x := by rw [← hq', hΦ.covers, hΨ.P_pullback]
  have htσ : X'.tgt σ = ψ.obj x :=
    (E'.P_μ ⟨(σ, Φ.obj (hΨ.pullback f' x)), hq⟩).symm.trans
      (by rw [hqμ, hΨ.covers, hΨ.P_pullback])
  have key : E'.μ ⟨(σ, Φ.obj (hΨ.pullback f' x)), hq⟩ = E'.μ ⟨(σ, Φ.obj (hΦ.pullback f' x)),
      (hΦ.covers _).trans ((congrArg ϕ.obj (hΦ.P_pullback f' x)).trans hsσ.symm)⟩ := by
    rw [hqμ, hΨ.obj_pullback hf', ← htσ, hfun σ]
    refine E'.μ_congr (Prod.ext rfl ?_)
    change f' (X'.src σ) = Φ.obj (hΦ.pullback f' x)
    rw [hΦ.obj_pullback hf', hsσ]
  exact hΦ.eq_of_obj_eq (by rw [hΦ.P_pullback, hΨ.P_pullback])
    (E'.μ_injective_snd _ _ key).symm

/-- Proposition 10.4.3 for functorial sections (sc-smoothness is not used). -/
theorem pushforward_eq_of_orbitMap_eq (hΦ : E.IsStrongBundleEquivalence E' ϕ Φ)
    (hΨ : E.IsStrongBundleEquivalence E' ψ Ψ) (hΦΨ : Φ.orbitMap = Ψ.orbitMap) {f : Obj → W}
    (hf : IsSection P f) (hfun : E.IsFunctorialSection hf) :
    hΦ.pushforward f = hΨ.pushforward f := by
  funext x'
  obtain ⟨⟨⟨τ, w'⟩, hq⟩, hq2, hqμ⟩ := exists_μ_eq_of_orbitMap_eq hΦΨ (f (hΦ.preObj x'))
  change w' = _ at hq2
  subst hq2
  have hq' : P' (Φ.obj (f (hΦ.preObj x'))) = X'.src τ := hq
  have hsτ : X'.src τ = ϕ.obj (hΦ.preObj x') := by rw [← hq', hΦ.covers, hf]
  have htτ : X'.tgt τ = ψ.obj (hΦ.preObj x') :=
    (E'.P_μ ⟨(τ, Φ.obj (f (hΦ.preObj x'))), hq⟩).symm.trans (by rw [hqμ, hΨ.covers, hf])
  have hc : X'.src (hΦ.preMor x') = X'.tgt (X'.inv τ) := by
    rw [X'.tgt_inv, hsτ, hΦ.src_preMor]
  have hc' : X'.src (X'.comp (hΦ.preMor x') (X'.inv τ)) = X'.tgt τ := by
    rw [X'.src_comp _ _ hc, X'.src_inv]
  have hs : X'.src (X'.comp (hΦ.preMor x') (X'.inv τ)) = ψ.obj (hΦ.preObj x') := hc'.trans htτ
  have ht : X'.tgt (X'.comp (hΦ.preMor x') (X'.inv τ)) = x' := by
    rw [X'.tgt_comp _ _ hc, hΦ.tgt_preMor]
  have hρ : X'.comp (X'.comp (hΦ.preMor x') (X'.inv τ)) τ = hΦ.preMor x' := by
    have := GroupoidStr.comp_inv_cancel_right (G := X'.toGroupoidStr) (φ := X'.inv τ)
      (ψ := hΦ.preMor x') hc
    rwa [GroupoidStr.inv_inv] at this
  rw [hΨ.pushforward_eq hf hfun hs ht, hΦ.pushforward_def hf]
  symm
  have e : Ψ.obj (f (hΦ.preObj x')) = E'.μ ⟨(τ, Φ.obj (f (hΦ.preObj x'))), hq⟩ := hqμ.symm
  exact (E'.μ_mk_congr rfl e _ _).trans
    ((E'.μ_comp _ _ _ hq hc').symm.trans (E'.μ_mk_congr hρ rfl _ _))

end IsStrongBundleEquivalence

/-- **2021 Proposition 10.4.2, p. 497 (2017: Proposition 10.7)**: if `Φ` and `Ψ` are strong
bundle equivalences `(P, μ) → (P', μ')` covering `ϕ` and `ψ` with `|Φ| = |Ψ| : |W| → |W'|`, then
`Φ*(f') = Ψ*(f')` for every sc-smooth section functor `f'` of `(P', μ')`. -/
theorem proposition_10_4_2 {ϕ ψ : EpFunctor X X'} {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (hΦ : E.IsStrongBundleEquivalence E' ϕ Φ) (hΨ : E.IsStrongBundleEquivalence E' ψ Ψ)
    (hΦΨ : Φ.orbitMap = Ψ.orbitMap) {f' : Obj' → W'} (hf' : f' ∈ E'.sectionFunctors) :
    hΦ.pullback f' = hΨ.pullback f' := by
  obtain ⟨hs, hfun⟩ := hf'
  exact hΦ.pullback_eq_of_orbitMap_eq hΨ hΦΨ hs.1 hfun

/-- **2021 Proposition 10.4.3, p. 499 (2017: Proposition 10.8)**: under the hypotheses of
Proposition 10.4.2, `Φ_* f = Ψ_* f` for every `f ∈ Γ(P, μ)`. -/
theorem proposition_10_4_3 {ϕ ψ : EpFunctor X X'} {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (hΦ : E.IsStrongBundleEquivalence E' ϕ Φ) (hΨ : E.IsStrongBundleEquivalence E' ψ Ψ)
    (hΦΨ : Φ.orbitMap = Ψ.orbitMap) {f : Obj → W} (hf : f ∈ E.sectionFunctors) :
    hΦ.pushforward f = hΨ.pushforward f := by
  obtain ⟨hs, hfun⟩ := hf
  exact hΦ.pushforward_eq_of_orbitMap_eq hΨ hΦΨ hs.1 hfun

/-! ### Proposition 10.4.4 -/

/-- **2021 Proposition 10.4.4, p. 499 (2017: Proposition 10.9)**: for strong bundle equivalences
`Φ : (P, μ) → (P', μ')` and `Ψ : (P', μ') → (P'', μ'')` (their composite is one,
`IsStrongBundleEquivalence.comp`), `(Ψ ∘ Φ)* = Φ* ∘ Ψ*` on sections of `P''` and
`(Ψ ∘ Φ)_* = Ψ_* ∘ Φ_*` on section functors of `(P, μ)`. -/
theorem proposition_10_4_4 {ϕ : EpFunctor X X'} {ψ : EpFunctor X' X''}
    {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} {Ψ : EpFunctor E'.toEpGroupoid E''.toEpGroupoid}
    (hΦ : E.IsStrongBundleEquivalence E' ϕ Φ) (hΨ : E'.IsStrongBundleEquivalence E'' ψ Ψ) :
    (∀ f'' : Obj'' → W'', IsSection P'' f'' →
      (hΨ.comp hΦ).pullback f'' = hΦ.pullback (hΨ.pullback f'')) ∧
    (∀ (f : Obj → W) (hf : IsSection P f), E.IsFunctorialSection hf →
      (hΨ.comp hΦ).pushforward f = hΨ.pushforward (hΦ.pushforward f)) := by
  refine ⟨fun f'' hf'' => funext fun x => ?_, fun f hf hfun => funext fun x'' => ?_⟩
  · refine (hΨ.comp hΦ).pullback_eq hf'' (hΦ.P_pullback _ x) ?_
    change Ψ.obj (Φ.obj (hΦ.pullback (hΨ.pullback f'') x)) = f'' (ψ.obj (ϕ.obj x))
    rw [hΦ.obj_pullback (hΨ.isSection_pullback f''), hΨ.obj_pullback hf'']
  · have h₂ : X''.src (hΨ.preMor x'') = X''.tgt (ψ.mor (hΦ.preMor (hΨ.preObj x''))) := by
      rw [ψ.tgt_mor, hΦ.tgt_preMor, hΨ.src_preMor]
    have hs : X''.src (X''.comp (hΨ.preMor x'') (ψ.mor (hΦ.preMor (hΨ.preObj x'')))) =
        (ψ.comp ϕ).obj (hΦ.preObj (hΨ.preObj x'')) := by
      rw [X''.src_comp _ _ h₂, ψ.src_mor, hΦ.src_preMor]; rfl
    have ht : X''.tgt (X''.comp (hΨ.preMor x'') (ψ.mor (hΦ.preMor (hΨ.preObj x'')))) = x'' := by
      rw [X''.tgt_comp _ _ h₂, hΨ.tgt_preMor]
    have h₁ : P'' (Ψ.obj (Φ.obj (f (hΦ.preObj (hΨ.preObj x''))))) =
        X''.src (ψ.mor (hΦ.preMor (hΨ.preObj x''))) := by
      rw [hΨ.covers, hΦ.covers, hf, ψ.src_mor, hΦ.src_preMor]
    rw [(hΨ.comp hΦ).pushforward_eq hf hfun hs ht, hΨ.pushforward_def (hΦ.isSection_pushforward f)]
    have hin : Ψ.obj (hΦ.pushforward f (hΨ.preObj x'')) =
        E''.μ ⟨(ψ.mor (hΦ.preMor (hΨ.preObj x'')), Ψ.obj (Φ.obj (f (hΦ.preObj (hΨ.preObj x''))))),
          h₁⟩ := by
      rw [hΦ.pushforward_def hf, hΨ.isStrongBundleFunctor.isMap.map_μ]
    exact (E''.μ_comp _ _ _ h₁ h₂).trans (E''.μ_mk_congr rfl hin.symm _ _)

/-! ### Sc-smoothness of pull-backs and push-forwards -/

namespace IsStrongBundleEquivalence

variable {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (h : E.IsStrongBundleEquivalence E' ϕ Φ)

/-- On the open set `U` of (2), `Φ*(f') = Ψ ∘ f' ∘ ϕ` with `Ψ` the inverse of
`Φ : W|U → W'|U'`. -/
theorem eqOn_pullback {f' : Obj' → W'} (hf' : IsSection P' f') {U : Set Obj} {U' : Set Obj'}
    {g : Obj' → Obj} (hg : X.PObj.IsScDiffeoOn X'.PObj ϕ.obj g U U') {Ψ : W' → W}
    (hΨ : B.toMPolyfold0.IsScDiffeoOn B'.toMPolyfold0 Φ.obj Ψ (P ⁻¹' U) (P' ⁻¹' U')) :
    EqOn (Ψ ∘ f' ∘ ϕ.obj) (h.pullback f') U := fun z hz => by
  have hm : P' (f' (ϕ.obj z)) ∈ U' := by rw [hf' (ϕ.obj z)]; exact hg.mapsTo hz
  refine (h.pullback_eq hf' ?_ (hΨ.right_inv _ hm)).symm
  rw [StrongBundle.IsStrongBundleIsoOn.P_inv (h := h.isStrongBundleFunctor.isStrongBundleMap_obj)
    hg hΨ hm, hf' (ϕ.obj z), hg.left_inv z hz]

/-- **The pull-back of an sc-smooth section is sc-smooth** (the first step of the proof of
Theorem 10.4.5). -/
theorem isScSmoothSection_pullback {f' : Obj' → W'} (hf' : B'.IsScSmoothSection f') :
    B.IsScSmoothSection (h.pullback f') := by
  refine ⟨h.isSection_pullback f', MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x _ => ?_⟩
  obtain ⟨U, U', hxU, hi⟩ := h.isLocalStrongBundleIso_obj x
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨Ψ, hΨ⟩ := hi.isScDiffeoOn_zero
  have hmaps : MapsTo (f' ∘ ϕ.obj) U (P' ⁻¹' U') := fun z hz => by
    change P' (f' (ϕ.obj z)) ∈ U'; rw [hf'.1 (ϕ.obj z)]; exact hg.mapsTo hz
  refine ⟨U, hg.isOpen_source, hxU, subset_univ _, ?_⟩
  exact (MPolyfold.IsScSmoothOn.comp hΨ.isScSmoothOn_inv
    (MPolyfold.IsScSmoothOn.comp hf'.2 hg.isScSmoothOn (mapsTo_univ _ _)) hmaps).congr
    (h.eqOn_pullback hf'.1 hg hΨ)

/-- **The pull-back of an sc⁺-section is an sc⁺-section**: on `U`, `Φ*(f')[1] = Ψ₁ ∘ f'[1] ∘ ϕ`
with `Ψ₁` the level-`[1]` inverse of (2). -/
theorem isScPlusSection_pullback {f' : Obj' → W'} (hf' : B'.IsScPlusSection f') :
    B.IsScPlusSection (h.pullback f') := by
  obtain ⟨hs', g', hg'f, hg'⟩ := (B'.isScPlusSection_iff f').1 hf'
  have key : ∀ x, ∃ U : Set Obj, IsOpen U ∧ x ∈ U ∧ ∃ G : Obj → B.One,
      X.PObj.IsScSmoothOn B.toMPolyfold1 G U ∧ ∀ z ∈ U, B.oneVal (G z) = h.pullback f' z := by
    intro x
    obtain ⟨U, U', hxU, hi⟩ := h.isLocalStrongBundleIso_obj x
    obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
    obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
    have hval : ∀ z, B'.oneVal (g' (ϕ.obj z)) = f' (ϕ.obj z) := fun z => congrFun hg'f _
    have hmaps : MapsTo (g' ∘ ϕ.obj) U ((P' ∘ B'.oneVal) ⁻¹' U') := fun z hz => by
      change P' (B'.oneVal (g' (ϕ.obj z))) ∈ U'
      rw [hval z, hs' (ϕ.obj z)]
      exact hg.mapsTo hz
    refine ⟨U, hg.isOpen_source, hxU, Ψ₁ ∘ g' ∘ ϕ.obj,
      MPolyfold.IsScSmoothOn.comp hΨ₁.isScSmoothOn_inv
        (MPolyfold.IsScSmoothOn.comp hg' hg.isScSmoothOn (mapsTo_univ _ _)) hmaps,
      fun z hz => ?_⟩
    have hm := hmaps hz
    refine (h.pullback_eq hs' ?_ ?_).symm
    · refine (StrongBundle.IsStrongBundleIsoOn.P_inv_one
        (h := h.isStrongBundleFunctor.isStrongBundleMap_obj) hg hΨ₁ hm).trans ?_
      change g (P' (B'.oneVal (g' (ϕ.obj z)))) = z
      rw [hval z, hs' (ϕ.obj z), hg.left_inv z hz]
    · have h2 := congrArg B'.oneVal (hΨ₁.right_inv _ hm)
      rw [StrongBundle.oneVal_oneRestrict] at h2
      exact h2.trans (hval z)
  choose U hU hxU G hG hGeq using key
  have hmem : ∀ z, h.pullback f' z ∈ B.oneSet := fun z =>
    hGeq z z (hxU z) ▸ B.oneVal_mem (G z z)
  refine (B.isScPlusSection_iff _).2 ⟨h.isSection_pullback f', fun z => B.oneMk _ (hmem z),
    funext fun z => B.oneVal_oneMk _ (hmem z), ?_⟩
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x _ =>
    ⟨U x, hU x, hxU x, subset_univ _, (hG x).congr fun z hz => ?_⟩
  apply B.oneVal_injective
  rw [hGeq x z hz, B.oneVal_oneMk]

include h in
/-- The local form of the push-forward (the proof of Theorem 10.4.5): near `x₀ ∈ X'`, with a
local inverse `τ` of `t'` at the chosen `σ₀ : ϕ(y₀) → x₀` and a local inverse `g₁` of `ϕ` at
`y₀`, on an open `N ∋ x₀` one has `Φ_*(f)(x') = μ'(τ(x'), Φ(f(g₁(s'(τ(x'))))))`. -/
theorem exists_pushforward_local (x₀ : Obj') :
    ∃ (T : Set Mor') (V : Set Obj') (τ : Obj' → Mor') (U₁ : Set Obj) (U₁' : Set Obj')
      (g₁ : Obj' → Obj), X'.PMor.IsScDiffeoOn X'.PObj X'.tgt τ T V ∧
      X.PObj.IsScDiffeoOn X'.PObj ϕ.obj g₁ U₁ U₁' ∧ x₀ ∈ V ∩ τ ⁻¹' (X'.src ⁻¹' U₁') ∧
      IsOpen (V ∩ τ ⁻¹' (X'.src ⁻¹' U₁')) := by
  obtain ⟨T, V, τ, hσT, hτ⟩ := X'.isLocalScDiffeo_tgt (h.preMor x₀)
  obtain ⟨U₁, U₁', g₁, hy₀, hg₁⟩ := h.isEquivalence_base.isLocalScDiffeo_obj (h.preObj x₀)
  refine ⟨T, V, τ, U₁, U₁', g₁, hτ, hg₁, ?_, hτ.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage
    hτ.isOpen_target (hg₁.isOpen_target.preimage X'.continuous_src)⟩
  have h1 : X'.tgt (h.preMor x₀) = x₀ := h.tgt_preMor x₀
  have h2 := hτ.left_inv _ hσT
  rw [h1] at h2
  refine ⟨h1 ▸ hτ.mapsTo hσT, ?_⟩
  change X'.src (τ x₀) ∈ U₁'
  rw [h2, h.src_preMor]; exact hg₁.mapsTo hy₀

/-- **The push-forward of an sc-smooth section functor is sc-smooth** (the proof of Theorem
10.4.5): locally `Φ_*(f) = μ' ∘ (τ, Φ ∘ f ∘ g₁ ∘ s' ∘ τ)`. -/
theorem isScSmoothSection_pushforward {f : Obj → W} (hf : B.IsScSmoothSection f)
    (hfun : E.IsFunctorialSection hf.1) : B'.IsScSmoothSection (h.pushforward f) := by
  classical
  refine ⟨h.isSection_pushforward f, MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x₀ _ => ?_⟩
  obtain ⟨T, V, τ, U₁, U₁', g₁, hτ, hg₁, hx₀, hNo⟩ := h.exists_pushforward_local x₀
  set N : Set Obj' := V ∩ τ ⁻¹' (X'.src ⁻¹' U₁') with hN
  let b : Obj' → W' := fun x' => Φ.obj (f (g₁ (X'.src (τ x'))))
  have hb : ∀ x' ∈ N, P' (b x') = X'.src (τ x') := fun x' hx' => by
    change P' (Φ.obj (f (g₁ (X'.src (τ x'))))) = _
    rw [h.covers, hf.1, hg₁.right_inv _ hx'.2]
  let ι : Obj' → pullbackSpace P' X'.src := fun x' =>
    if hx : P' (b x') = X'.src (τ x') then ⟨(τ x', b x'), hx⟩
    else ⟨(X'.unit (P' (b x')), b x'), (X'.src_unit _).symm⟩
  have hι : ∀ x' (hx' : x' ∈ N), ι x' = ⟨(τ x', b x'), hb x' hx'⟩ := fun x' hx' =>
    dif_pos (hb x' hx')
  have heq : EqOn (E'.μ ∘ ι) (h.pushforward f) N := fun x' hx' => by
    have hs : X'.src (τ x') = ϕ.obj (g₁ (X'.src (τ x'))) := (hg₁.right_inv _ hx'.2).symm
    change E'.μ (ι x') = h.pushforward f x'
    rw [hι x' hx', h.pushforward_eq hf.1 hfun hs (hτ.right_inv x' hx'.1)]
  have hτN : X'.PObj.IsScSmoothOn X'.PMor τ N := hτ.isScSmoothOn_inv.mono hNo inter_subset_left
  have hgN : X'.PObj.IsScSmoothOn X.PObj (g₁ ∘ X'.src ∘ τ) N :=
    MPolyfold.IsScSmoothOn.comp hg₁.isScSmoothOn_inv
      (MPolyfold.IsScSmoothOn.comp X'.isScSmoothMap_src hτN (mapsTo_univ _ _)) fun x' hx' => hx'.2
  have hbN : X'.PObj.IsScSmoothOn B'.toMPolyfold0 b N :=
    MPolyfold.IsScSmoothOn.comp h.isStrongBundleFunctor.isStrongBundleMap_obj.isScSmoothMap
      (MPolyfold.IsScSmoothOn.comp hf.2 hgN (mapsTo_univ _ _)) (mapsTo_univ _ _)
  have hιN := B'.isScSmoothOn_to_pullback_of_eqOn X'.isScSmoothMap_src (ι := ι) hτN hbN
    fun v hv => by rw [hι v hv]
  exact ⟨N, hNo, hx₀, subset_univ _,
    (MPolyfold.IsScSmoothOn.comp E'.isStrongBundleMap.isScSmoothMap hιN (mapsTo_univ _ _)).congr
      heq⟩

/-- **The push-forward of an sc⁺-section functor is an sc⁺-section** (the level-`[1]` part of
Theorem 10.4.5): locally `Φ_*(f)[1] = μ'[1] ∘ ι₁` with `ι₁ = (τ, Φ[1] ∘ f[1] ∘ g₁ ∘ s' ∘ τ)`
sc-smooth into the level `[1]` of the pull-back (`StrongBundle.isScSmoothOn_to_pullback_one`). -/
theorem isScPlusSection_pushforward {f : Obj → W} (hf : B.IsScSmoothSection f)
    (hfun : E.IsFunctorialSection hf.1) (hf₁ : B.IsScPlusSection f) :
    B'.IsScPlusSection (h.pushforward f) := by
  classical
  obtain ⟨-, G, hGf, hG⟩ := (B.isScPlusSection_iff f).1 hf₁
  have hfmem : ∀ y, f y ∈ B.oneSet := fun y => (congrFun hGf y) ▸ B.oneVal_mem (G y)
  have hΦmem : ∀ y, Φ.obj (f y) ∈ B'.oneSet := fun y =>
    h.isStrongBundleFunctor.isStrongBundleMap_obj.mapsTo_oneSet (hfmem y)
  have hmem : ∀ x', h.pushforward f x' ∈ B'.oneSet := fun x' => by
    rw [h.pushforward_def hf.1]
    exact E'.isStrongBundleMap.mapsTo_oneSet
      ((B'.mem_oneSet_pullback_iff X'.isScSmoothMap_src _).2 (hΦmem _))
  refine (B'.isScPlusSection_iff _).2 ⟨h.isSection_pushforward f, fun x' => B'.oneMk _ (hmem x'),
    funext fun x' => B'.oneVal_oneMk _ (hmem x'), ?_⟩
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x₀ _ => ?_
  obtain ⟨T, V, τ, U₁, U₁', g₁, hτ, hg₁, hx₀, hNo⟩ := h.exists_pushforward_local x₀
  set N : Set Obj' := V ∩ τ ⁻¹' (X'.src ⁻¹' U₁') with hN
  let b : Obj' → W' := fun x' => Φ.obj (f (g₁ (X'.src (τ x'))))
  have hb : ∀ x' ∈ N, P' (b x') = X'.src (τ x') := fun x' hx' => by
    change P' (Φ.obj (f (g₁ (X'.src (τ x'))))) = _
    rw [h.covers, hf.1, hg₁.right_inv _ hx'.2]
  let ι : Obj' → pullbackSpace P' X'.src := fun x' =>
    if hx : P' (b x') = X'.src (τ x') then ⟨(τ x', b x'), hx⟩
    else ⟨(X'.unit (P' (b x')), b x'), (X'.src_unit _).symm⟩
  have hι : ∀ x' (hx' : x' ∈ N), ι x' = ⟨(τ x', b x'), hb x' hx'⟩ := fun x' hx' =>
    dif_pos (hb x' hx')
  have hι2 : ∀ x', (ι x' : Mor' × W').2 = b x' := fun x' => by
    dsimp only [ι]; split_ifs <;> rfl
  have hι1 : ∀ x', ι x' ∈ (B'.pullback X'.isScSmoothMap_src).oneSet := fun x' =>
    (B'.mem_oneSet_pullback_iff X'.isScSmoothMap_src _).2 (by rw [hι2]; exact hΦmem _)
  let ι₁ : Obj' → (B'.pullback X'.isScSmoothMap_src).One := fun x' =>
    (B'.pullback X'.isScSmoothMap_src).oneMk (ι x') (hι1 x')
  have heq : ∀ x' ∈ N, E'.μ (ι x') = h.pushforward f x' := fun x' hx' => by
    have hs : X'.src (τ x') = ϕ.obj (g₁ (X'.src (τ x'))) := (hg₁.right_inv _ hx'.2).symm
    rw [hι x' hx', h.pushforward_eq hf.1 hfun hs (hτ.right_inv x' hx'.1)]
  have hτN : X'.PObj.IsScSmoothOn X'.PMor τ N := hτ.isScSmoothOn_inv.mono hNo inter_subset_left
  have hgN : X'.PObj.IsScSmoothOn X.PObj (g₁ ∘ X'.src ∘ τ) N :=
    MPolyfold.IsScSmoothOn.comp hg₁.isScSmoothOn_inv
      (MPolyfold.IsScSmoothOn.comp X'.isScSmoothMap_src hτN (mapsTo_univ _ _)) fun x' hx' => hx'.2
  have ha : X'.PObj.IsScSmoothOn X'.PMor
      (pullbackProj P' X'.src ∘ (B'.pullback X'.isScSmoothMap_src).oneVal ∘ ι₁) N :=
    hτN.congr fun x' hx' => by
      change τ x' = (ι x' : Mor' × W').1
      rw [hι x' hx']
  have hb1 : X'.PObj.IsScSmoothOn B'.toMPolyfold1
      (B'.pullbackProj'One X'.isScSmoothMap_src ∘ ι₁) N := by
    refine (MPolyfold.IsScSmoothOn.comp
      h.isStrongBundleFunctor.isStrongBundleMap_obj.isScSmoothMap_one
      (MPolyfold.IsScSmoothOn.comp hG hgN (mapsTo_univ _ _)) (mapsTo_univ _ _)).congr
      fun x' _ => B'.oneVal_injective ?_
    change Φ.obj (B.oneVal (G (g₁ (X'.src (τ x'))))) = (ι x' : Mor' × W').2
    rw [hι2, show B.oneVal (G (g₁ (X'.src (τ x')))) = f (g₁ (X'.src (τ x'))) from congrFun hGf _]
  have hι₁N := B'.isScSmoothOn_to_pullback_one X'.isScSmoothMap_src ha hb1
  refine ⟨N, hNo, hx₀, subset_univ _, (MPolyfold.IsScSmoothOn.comp
    E'.isStrongBundleMap.isScSmoothMap_one hι₁N (mapsTo_univ _ _)).congr fun x' hx' => ?_⟩
  apply B'.oneVal_injective
  change E'.μ (ι x') = B'.oneVal (B'.oneMk _ (hmem x'))
  rw [B'.oneVal_oneMk, heq x' hx']

end IsStrongBundleEquivalence

/-- Conversely to `exists_μ_eq_of_orbitMap_eq`: if every `Φ(w)` is connected to `Ψ(w)` by a
morphism of `(W', 𝐖')`, then `|Φ| = |Ψ|`. -/
theorem orbitMap_eq_of_forall_exists {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (hq : ∀ w : W, ∃ q : pullbackSpace P' X'.src, (q : Mor' × W').2 = Φ.obj w ∧
      E'.μ q = Ψ.obj w) :
    Φ.orbitMap = Ψ.orbitMap := by
  refine funext fun a => Quotient.inductionOn a fun w => ?_
  change Φ.orbitMap (E.toEpGroupoid.π w) = Ψ.orbitMap (E.toEpGroupoid.π w)
  rw [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π]
  obtain ⟨q, hs, ht⟩ := hq w
  exact (GroupoidStr.π_eq_π_iff _).2 ⟨q, hs, ht⟩

/-! ### Theorem 10.4.5 -/

/-- **2021 Theorem 10.4.5, p. 500 (2017: Theorem 10.8)**: for a strong bundle equivalence `Φ`
covering `ϕ`,
* `Φ_* : Γ(P, μ) → Γ(P', μ')` and `Φ* : Γ(P', μ') → Γ(P, μ)` are mutually inverse bijections;
* if `Ψ` is another strong bundle equivalence (covering `ψ`) with `|Φ| = |Ψ|`, then `Φ_* = Ψ_*`
  and `Φ* = Ψ*` (Propositions 10.4.2 and 10.4.3);
* `Φ_*` and `Φ*` preserve sc⁺-section functors.
The preservation of `Fred` is not formalized (see the module docstring). -/
theorem theorem_10_4_5 {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (h : E.IsStrongBundleEquivalence E' ϕ Φ) :
    (MapsTo h.pushforward E.sectionFunctors E'.sectionFunctors ∧
      MapsTo h.pullback E'.sectionFunctors E.sectionFunctors ∧
      InvOn h.pullback h.pushforward E.sectionFunctors E'.sectionFunctors ∧
      BijOn h.pushforward E.sectionFunctors E'.sectionFunctors) ∧
    (∀ (ψ : EpFunctor X X') (Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid)
      (hΨ : E.IsStrongBundleEquivalence E' ψ Ψ), Φ.orbitMap = Ψ.orbitMap →
      EqOn h.pushforward hΨ.pushforward E.sectionFunctors ∧
      EqOn h.pullback hΨ.pullback E'.sectionFunctors) ∧
    MapsTo h.pushforward E.plusSectionFunctors E'.plusSectionFunctors ∧
    MapsTo h.pullback E'.plusSectionFunctors E.plusSectionFunctors := by
  have hpush : MapsTo h.pushforward E.sectionFunctors E'.sectionFunctors := by
    rintro f ⟨hs, hfun⟩
    exact ⟨h.isScSmoothSection_pushforward hs hfun, h.isFunctorialSection_pushforward hs.1 hfun⟩
  have hpull : MapsTo h.pullback E'.sectionFunctors E.sectionFunctors := by
    rintro f' ⟨hs, hfun⟩
    exact ⟨h.isScSmoothSection_pullback hs, h.isFunctorialSection_pullback hs.1 hfun⟩
  have hinv : InvOn h.pullback h.pushforward E.sectionFunctors E'.sectionFunctors :=
    ⟨fun f ⟨hs, hfun⟩ => h.pullback_pushforward hs.1 hfun,
      fun f' ⟨hs, hfun⟩ => h.pushforward_pullback hs.1 hfun⟩
  refine ⟨⟨hpush, hpull, hinv, hinv.bijOn hpush hpull⟩,
    fun ψ Ψ hΨ hΦΨ => ⟨fun f hf => proposition_10_4_3 h hΨ hΦΨ hf,
      fun f' hf' => proposition_10_4_2 h hΨ hΦΨ hf'⟩, ?_, ?_⟩
  · rintro f ⟨⟨hs, hfun⟩, hplus⟩
    exact ⟨hpush ⟨hs, hfun⟩, h.isScPlusSection_pushforward hs hfun hplus⟩
  · rintro f' ⟨⟨hs, hfun⟩, hplus⟩
    exact ⟨hpull ⟨hs, hfun⟩, h.isScPlusSection_pullback hplus⟩

end EpStrongBundle

end Functors

end Polyfold
