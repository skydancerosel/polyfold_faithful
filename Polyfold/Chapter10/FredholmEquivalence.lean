import Polyfold.Chapter10.StrongBundleLocalizationSections
import Polyfold.Chapter3.FredholmPullbackIso

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.4 and §10.5: **the `Fred` parts of Theorem 10.4.5, p. 500 (2017:
Theorem 10.8, p. 362) and of Theorem 10.5.4, p. 508 (2017: Theorem 10.9, p. 367)**: `Φ_*`,
`Φ^*`, `[D]_*` and `[D]^*` map sc-Fredholm section functors to sc-Fredholm section functors.
This closes gaps G.121 and G.125 and completes rows V10.27 and V10.59; the Part I half (the
invariance of sc-Fredholm germs under local strong bundle isomorphisms) is
`Chapter3/FredholmPullbackIso.lean`.  Numbers and pages are the 2021 text's, the 2017 ones in
parentheses.

# sc-Fredholm section functors under strong bundle equivalences

## The text, paraphrased

(p. 500, proof of Theorem 10.4.5) "It is clear that `Φ^*` and `Φ_*` map sc-Fredholm section
functors to sc-Fredholm section functors" (2017 p. 362: the same).  (p. 507) `[D]_* = Ψ_* Φ^*`
preserves `Fred` by Theorem 10.4.5.

## What is formalized

* `StrongBundle.IsStrongBundleIsoOn.toLocalIso`: Chapter 8's local strong bundle isomorphism
  (Definition 10.4.1 (2)) as a `LocalIso` of `FredholmPullbackIso.lean`.
* `EpStrongBundle.sectionAct α`, the map `w ↦ μ(α(P(w)), w)` for a local section `α` of `s`, with its
  sc-smoothness on `[0]` and `[1]` and its linearity on the fibres;
  `EpStrongBundle.exists_localIso_mor σ`: **the action of a morphism `σ` is a local strong bundle
  isomorphism `W|t(T) → W|s(T)`** along which every section functor is its own pull-back
  (functoriality (10.16)).
* `IsStrongBundleEquivalence.isScFredholmSection_pullback` (**`Φ^*` preserves `Fred`**, Part I's
  Definition 3.1.18 (preprint 3.14), germ reading), `isScFredholmSectionTame_pullback` (tame germ
  data, Definition 3.6.5);
* `IsStrongBundleEquivalence.isScFredholmSection_pushforward` (**`Φ_*` preserves `Fred`**): near
  `x' ∈ X'` with `σ : ϕ(y) → x'`, `Φ_* f` is `Φ ∘ f ∘ ϕ⁻¹` near `ϕ(y)` (so sc-Fredholm there by
  the key lemma for the inverse local isomorphism) and its own pull-back along the action of
  `σ`; `isScFredholmSectionTame_pushforward`.
* `theorem_10_4_5_fred` (**Theorem 10.4.5, the `Fred` part**, G.121): `Φ_*` and `Φ^*` restrict to
  mutually inverse bijections `Fred(P, μ) ↔ Fred(P', μ')`.
* `SBLocalization.SDiagram.mapsTo_pushforward_fred`, `mapsTo_pullback_fred`,
  `bijOn_pushforward_fred`, and `SBLocalization.GenSBMap.theorem_10_5_4_fred` (**Theorem 10.5.4,
  the `Fred` part**, G.125): `[D]_*` maps `Fred(P, μ)` bijectively onto `Fred(P', μ')`, with
  inverse `[D]^*`.

## What the text leaves implicit, and the choices made

* "Clear": the push-forward is not a pull-back along a strong bundle isomorphism defined on all
  of `W'`, since `ϕ` is only essentially surjective; the proof here uses the morphisms
  `σ : ϕ(y) → x'` and the functoriality of section functors, as the text's definition of `Φ_*`
  does.
* The sc-Fredholm notion is Part I's germ reading (`StrongBundle.IsScFredholmSection`), the one
  in `EpStrongBundle.IsScFredholmSectionFunctor`; the tame form is carried along.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Chapter 8's local strong bundle isomorphisms as `LocalIso` -/

section IsoOn

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]

namespace StrongBundle

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {f : X → X'} {Φ : Y → Y'}
  {h : B.IsStrongBundleMap B' f Φ} {U : Set X} {U' : Set X'}

/-- **A local strong bundle isomorphism `Y|U → Y'|U'`** in the sense of Chapter 8
(`IsStrongBundleIsoOn`, the (2) of Definition 10.4.1) is one in the sense of
`FredholmPullbackIso.lean`: the inverses are chosen. -/
def IsStrongBundleIsoOn.toLocalIso (hi : B.IsStrongBundleIsoOn B' h U U') : LocalIso B B' U U'
    where
  ϕ := f
  g := Classical.choose hi.isScDiffeoOn_base
  Φ := Φ
  Ψ := Classical.choose hi.isScDiffeoOn_zero
  Φ₁ := StrongBundle.oneRestrict B B' Φ h.mapsTo_oneSet
  Ψ₁ := Classical.choose hi.isScDiffeoOn_one
  base := Classical.choose_spec hi.isScDiffeoOn_base
  zero := Classical.choose_spec hi.isScDiffeoOn_zero
  one := Classical.choose_spec hi.isScDiffeoOn_one
  covers y _ := h.covers y
  oneVal_Φ₁ _ _ := rfl
  fiber_linear x x' _ hx' := by
    subst hx'
    exact h.fiber_linear x

@[simp] lemma IsStrongBundleIsoOn.toLocalIso_ϕ (hi : B.IsStrongBundleIsoOn B' h U U') :
    hi.toLocalIso.ϕ = f := rfl

@[simp] lemma IsStrongBundleIsoOn.toLocalIso_Φ (hi : B.IsStrongBundleIsoOn B' h U U') :
    hi.toLocalIso.Φ = Φ := rfl

end StrongBundle

end IsoOn

/-! ### The action of a morphism as a local strong bundle isomorphism -/

section Act

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

variable (X) in
open scoped Classical in
/-- The point `(α(P(w)), w)` of `𝐗 ₛ×_P W` (with the junk value `(1_{P w}, w)` where
`s(α(P w)) ≠ P(w)`). -/
def EpGroupoid.actPair (P : W → Obj) (α : Obj → Mor) (w : W) : pullbackSpace P X.src :=
  if h : P w = X.src (α (P w)) then ⟨(α (P w), w), h⟩ else X.unitPair w

omit [TopologicalSpace W] [T2Space W] [ParacompactSpace W] in
variable (X) in
lemma EpGroupoid.actPair_of_eq (P : W → Obj) (α : Obj → Mor) {w : W}
    (h : P w = X.src (α (P w))) : X.actPair P α w = ⟨(α (P w), w), h⟩ := dif_pos h

omit [TopologicalSpace W] [T2Space W] [ParacompactSpace W] in
variable (X) in
lemma EpGroupoid.actPair_snd (P : W → Obj) (α : Obj → Mor) (w : W) :
    (X.actPair P α w : Mor × W).2 = w := by
  unfold EpGroupoid.actPair; split_ifs <;> rfl

namespace EpStrongBundle

variable (E : EpStrongBundle X B) (α : Obj → Mor)

/-- **The action of a local section `α` of `s`**: `w ↦ μ(α(P(w)), w)`. -/
def sectionAct (w : W) : W := E.μ (X.actPair P α w)

omit [ParacompactSpace (pullbackSpace P X.src)] in
lemma sectionAct_of_eq {w : W} (h : P w = X.src (α (P w))) :
    E.sectionAct α w = E.μ ⟨(α (P w), w), h⟩ := by
  rw [sectionAct, X.actPair_of_eq P α h]

omit [ParacompactSpace (pullbackSpace P X.src)] in
lemma P_sectionAct_of_eq {w : W} (h : P w = X.src (α (P w))) :
    P (E.sectionAct α w) = X.tgt (α (P w)) := by
  rw [E.sectionAct_of_eq α h, E.P_μ]

/-- The action preserves `W_{0,1}`. -/
lemma mapsTo_oneSet_sectionAct : MapsTo (E.sectionAct α) B.oneSet B.oneSet := fun w hw =>
  E.isStrongBundleMap.mapsTo_oneSet
    ((B.mem_oneSet_pullback_iff X.isScSmoothMap_src _).2 (by rw [X.actPair_snd P α]; exact hw))

variable {α} {S : Set Obj} (hS : IsOpen S) (hα : X.PObj.IsScSmoothOn X.PMor α S)
  (hsrc : ∀ x ∈ S, X.src (α x) = x)

include hS hα hsrc in
/-- The action is sc-smooth on `W|S` (level `[0]`): it is `μ ∘ (α ∘ P, id)`. -/
theorem isScSmoothOn_sectionAct : B.toMPolyfold0.IsScSmoothOn B.toMPolyfold0 (E.sectionAct α) (P ⁻¹' S) := by
  have hSo : IsOpen (P ⁻¹' S) := hS.preimage B.continuous
  have hP : B.toMPolyfold0.IsScSmoothOn X.PObj P (P ⁻¹' S) :=
    B.isScSmoothMap_proj.mono hSo (subset_univ _)
  have ha : B.toMPolyfold0.IsScSmoothOn X.PMor (α ∘ P) (P ⁻¹' S) :=
    MPolyfold.IsScSmoothOn.comp hα hP fun w hw => hw
  have hι := B.isScSmoothOn_to_pullback_of_eqOn X.isScSmoothMap_src (ι := X.actPair P α) ha
    (MPolyfold.isScSmoothMap_id.mono hSo (subset_univ _)) fun w hw => by
      rw [X.actPair_of_eq P α (hsrc _ hw).symm]; rfl
  exact MPolyfold.IsScSmoothOn.comp E.isStrongBundleMap.isScSmoothMap hι (mapsTo_univ _ _)

include hS hα hsrc in
/-- The action is sc-smooth on `W[1]|S`. -/
theorem isScSmoothOn_sectionAct_one :
    B.toMPolyfold1.IsScSmoothOn B.toMPolyfold1 (StrongBundle.oneRestrict B B (E.sectionAct α) (E.mapsTo_oneSet_sectionAct α))
      ((P ∘ B.oneVal) ⁻¹' S) := by
  have hSo : IsOpen ((P ∘ B.oneVal) ⁻¹' S) :=
    hS.preimage (B.continuous.comp B.continuous_oneVal)
  let ι₁ : B.One → (B.pullback X.isScSmoothMap_src).One := fun w =>
    (B.pullback X.isScSmoothMap_src).oneMk (X.actPair P α (B.oneVal w))
      ((B.mem_oneSet_pullback_iff X.isScSmoothMap_src _).2
        (by rw [X.actPair_snd P α]; exact B.oneVal_mem w))
  have hP1 : B.toMPolyfold1.IsScSmoothOn X.PObj (P ∘ B.oneVal) ((P ∘ B.oneVal) ⁻¹' S) :=
    B.isScSmoothMap_proj1.mono hSo (subset_univ _)
  have ha : B.toMPolyfold1.IsScSmoothOn X.PMor
      (pullbackProj P X.src ∘ (B.pullback X.isScSmoothMap_src).oneVal ∘ ι₁)
      ((P ∘ B.oneVal) ⁻¹' S) :=
    (MPolyfold.IsScSmoothOn.comp hα hP1 fun w hw => hw).congr fun w hw => by
      change α (P (B.oneVal w)) = (X.actPair P α (B.oneVal w) : Mor × W).1
      rw [X.actPair_of_eq P α (hsrc _ hw).symm]
  have hb : B.toMPolyfold1.IsScSmoothOn B.toMPolyfold1
      (B.pullbackProj'One X.isScSmoothMap_src ∘ ι₁) ((P ∘ B.oneVal) ⁻¹' S) :=
    (MPolyfold.isScSmoothMap_id.mono hSo (subset_univ _)).congr fun w _ => by
      apply B.oneVal_injective
      change B.oneVal w = (X.actPair P α (B.oneVal w) : Mor × W).2
      rw [X.actPair_snd P α]
  have hι₁ := B.isScSmoothOn_to_pullback_one X.isScSmoothMap_src ha hb
  exact (MPolyfold.IsScSmoothOn.comp E.isStrongBundleMap.isScSmoothMap_one hι₁
    (mapsTo_univ _ _)).congr fun w _ => B.oneVal_injective rfl

omit [ParacompactSpace (pullbackSpace P X.src)] in
include hsrc in
/-- The action is linear on the fibres over `S`: `μ(α(x), ·) : W_x → W_{t(α(x))}`. -/
theorem isLinearMap_sectionAct {x : Obj} (hx : x ∈ S) {x' : Obj} (hx' : X.tgt (α x) = x') :
    IsLinearMap ℝ (fiberMapOf P P (E.sectionAct α) (x := x) (x' := x') fun v => by
      have hv : P v = x := v.2
      rw [E.P_sectionAct_of_eq α (by rw [hv]; exact (hsrc x hx).symm), hv, hx']) := by
  have := B.paracompactSpace_pullback X.PMor X.src
  subst hx'
  let L : P ⁻¹' {x} →ₗ[ℝ] P ⁻¹' {X.tgt (α x)} :=
    ((E.isStrongBundleMap.fiber_linear (α x)).mk' _).comp
      (((pullbackFiberLinearEquiv P X.src (α x)).symm.toLinearMap).comp
        (fiberCast P (hsrc x hx).symm))
  have hL : (fiberMapOf P P (E.sectionAct α) (x := x) (x' := X.tgt (α x)) fun v => by
      have hv : P v = x := v.2
      rw [E.P_sectionAct_of_eq α (by rw [hv]; exact (hsrc x hx).symm), hv]) = L := by
    funext v
    apply Subtype.ext
    have hv : P v = x := v.2
    change E.sectionAct α v = E.μ ((pullbackFiberLinearEquiv P X.src (α x)).symm (fiberCast P _ v))
    rw [E.sectionAct_of_eq α (by rw [hv]; exact (hsrc x hx).symm)]
    refine E.μ_congr ?_
    change (α (P v), (v : W)) = (α x, ((fiberCast P (hsrc x hx).symm v : P ⁻¹' {X.src (α x)}) : W))
    rw [fiberCast_val, hv]
  rw [hL]; exact L.isLinear

/-- **The action of a morphism `σ` is a local strong bundle isomorphism `W|t(T) → W|s(T)`**, for
a neighbourhood `T` of `σ` on which `s` and `t` are sc-diffeomorphisms: `ϕ = s ∘ t⁻¹`,
`Φ(w) = μ((t⁻¹(P w))⁻¹, w)`, with inverse `g = t ∘ s⁻¹`, `Ψ(w) = μ(s⁻¹(P w), w)`.  Every section
functor is its own pull-back along it (functoriality (10.16)). -/
theorem exists_localIso_mor (σ : Mor) :
    ∃ (U U' : Set Obj) (L : StrongBundle.LocalIso B B U U'), X.tgt σ ∈ U ∧
      L.ϕ (X.tgt σ) = X.src σ ∧
      ∀ (f : Obj → W) (hf : IsSection P f), E.IsFunctorialSection hf →
        EqOn f (L.Ψ ∘ f ∘ L.ϕ) U := by
  obtain ⟨T₁, V₁, τ₁, hσ₁, hτ₁⟩ := X.isLocalScDiffeo_src σ
  obtain ⟨T₂, V₂, τ₂, hσ₂, hτ₂⟩ := X.isLocalScDiffeo_tgt σ
  have hT : IsOpen (T₁ ∩ T₂) := hτ₁.isOpen_source.inter hτ₂.isOpen_source
  have hs := hτ₁.restrict hT inter_subset_left
  have ht := hτ₂.restrict hT inter_subset_right
  set T := T₁ ∩ T₂ with hTdef
  set U := V₂ ∩ τ₂ ⁻¹' T with hUdef
  set U' := V₁ ∩ τ₁ ⁻¹' T with hU'def
  have hbase : X.PObj.IsScDiffeoOn X.PObj (X.src ∘ τ₂) (X.tgt ∘ τ₁) U U' := hs.comp ht.symm
  have hU : IsOpen U := hbase.isOpen_source
  have hU' : IsOpen U' := hbase.isOpen_target
  -- the two local sections of `s`
  set α₂ : Obj → Mor := fun x => X.inv (τ₂ x) with hα₂def
  have hα₂ : X.PObj.IsScSmoothOn X.PMor α₂ U :=
    MPolyfold.IsScSmoothOn.comp X.isScSmoothMap_inv ht.isScSmoothOn_inv (mapsTo_univ _ _)
  have hsrc₂ : ∀ x ∈ U, X.src (α₂ x) = x := fun x hx => by
    change X.src (X.inv (τ₂ x)) = x
    rw [X.src_inv, ht.right_inv x hx]
  have hα₁ : X.PObj.IsScSmoothOn X.PMor τ₁ U' := hs.isScSmoothOn_inv
  have hsrc₁ : ∀ x ∈ U', X.src (τ₁ x) = x := fun x hx => hs.right_inv x hx
  -- covering
  have hcov : ∀ y, P y ∈ U → P (E.sectionAct α₂ y) = (X.src ∘ τ₂) (P y) := fun y hy => by
    rw [E.P_sectionAct_of_eq α₂ (hsrc₂ _ hy).symm]; exact X.tgt_inv _
  have hcov' : ∀ y, P y ∈ U' → P (E.sectionAct τ₁ y) = (X.tgt ∘ τ₁) (P y) := fun y hy =>
    E.P_sectionAct_of_eq τ₁ (hsrc₁ _ hy).symm
  have hmaps : MapsTo (E.sectionAct α₂) (P ⁻¹' U) (P ⁻¹' U') := fun y hy => by
    show P (E.sectionAct α₂ y) ∈ U'
    rw [hcov y hy]; exact hbase.mapsTo hy
  have hmaps' : MapsTo (E.sectionAct τ₁) (P ⁻¹' U') (P ⁻¹' U) := fun y hy => by
    show P (E.sectionAct τ₁ y) ∈ U
    rw [hcov' y hy]; exact hbase.mapsTo_inv hy
  -- the two compositions
  have hleft : ∀ y, P y ∈ U → E.sectionAct τ₁ (E.sectionAct α₂ y) = y := fun y hy => by
    have hρ : τ₂ (P y) ∈ T := ht.mapsTo_inv hy
    have hy1 : P y = X.src (α₂ (P y)) := (hsrc₂ _ hy).symm
    have hw1 : P (E.sectionAct α₂ y) = X.src (τ₁ (P (E.sectionAct α₂ y))) := (hsrc₁ _ (hmaps hy)).symm
    have hτρ : τ₁ (P (E.sectionAct α₂ y)) = τ₂ (P y) := by
      rw [hcov y hy]; exact hs.left_inv _ hρ
    have hP' : P (E.μ ⟨(X.inv (τ₂ (P y)), y), hy1⟩) = X.src (τ₂ (P y)) := by
      rw [E.P_μ]; exact X.tgt_inv _
    rw [E.sectionAct_of_eq τ₁ hw1]
    refine (E.μ_congr (q' := ⟨(τ₂ (P y), E.μ ⟨(X.inv (τ₂ (P y)), y), hy1⟩), hP'⟩) ?_).trans
      (E.μ_μ_inv _ y hy1 hP')
    exact Prod.ext hτρ (E.sectionAct_of_eq α₂ hy1)
  have hright : ∀ y', P y' ∈ U' → E.sectionAct α₂ (E.sectionAct τ₁ y') = y' := fun y' hy' => by
    have hρ : τ₁ (P y') ∈ T := hs.mapsTo_inv hy'
    have hy1 : P y' = X.src (τ₁ (P y')) := (hsrc₁ _ hy').symm
    have hw1 : P (E.sectionAct τ₁ y') = X.src (α₂ (P (E.sectionAct τ₁ y'))) := (hsrc₂ _ (hmaps' hy')).symm
    have hτρ : α₂ (P (E.sectionAct τ₁ y')) = X.inv (τ₁ (P y')) := by
      change X.inv (τ₂ (P (E.sectionAct τ₁ y'))) = _
      rw [hcov' y' hy']; exact congrArg X.inv (ht.left_inv _ hρ)
    have hP' : P (E.μ ⟨(τ₁ (P y'), y'), hy1⟩) = X.src (X.inv (τ₁ (P y'))) := by
      rw [E.P_μ, X.src_inv]
    rw [E.sectionAct_of_eq α₂ hw1]
    refine (E.μ_congr (q' := ⟨(X.inv (τ₁ (P y')), E.μ ⟨(τ₁ (P y'), y'), hy1⟩), hP'⟩) ?_).trans
      (E.μ_inv_μ ⟨(τ₁ (P y'), y'), hy1⟩ hP')
    exact Prod.ext hτρ (E.sectionAct_of_eq τ₁ hy1)
  have hzero : B.toMPolyfold0.IsScDiffeoOn B.toMPolyfold0 (E.sectionAct α₂) (E.sectionAct τ₁) (P ⁻¹' U)
      (P ⁻¹' U') :=
    ⟨E.isScSmoothOn_sectionAct hU hα₂ hsrc₂, E.isScSmoothOn_sectionAct hU' hα₁ hsrc₁, hmaps, hmaps', hleft,
      hright⟩
  have hone : B.toMPolyfold1.IsScDiffeoOn B.toMPolyfold1
      (StrongBundle.oneRestrict B B (E.sectionAct α₂) (E.mapsTo_oneSet_sectionAct α₂))
      (StrongBundle.oneRestrict B B (E.sectionAct τ₁) (E.mapsTo_oneSet_sectionAct τ₁))
      ((P ∘ B.oneVal) ⁻¹' U) ((P ∘ B.oneVal) ⁻¹' U') :=
    ⟨E.isScSmoothOn_sectionAct_one hU hα₂ hsrc₂, E.isScSmoothOn_sectionAct_one hU' hα₁ hsrc₁,
      fun w hw => hmaps hw, fun w hw => hmaps' hw,
      fun w hw => B.oneVal_injective (hleft _ hw), fun w hw => B.oneVal_injective (hright _ hw)⟩
  let L : StrongBundle.LocalIso B B U U' :=
    { ϕ := X.src ∘ τ₂
      g := X.tgt ∘ τ₁
      Φ := E.sectionAct α₂
      Ψ := E.sectionAct τ₁
      Φ₁ := StrongBundle.oneRestrict B B (E.sectionAct α₂) (E.mapsTo_oneSet_sectionAct α₂)
      Ψ₁ := StrongBundle.oneRestrict B B (E.sectionAct τ₁) (E.mapsTo_oneSet_sectionAct τ₁)
      base := hbase
      zero := hzero
      one := hone
      covers := hcov
      oneVal_Φ₁ := fun _ _ => rfl
      fiber_linear := fun x x' hx hx' =>
        E.isLinearMap_sectionAct hsrc₂ hx ((X.tgt_inv _).trans hx') }
  have hσT : σ ∈ T := ⟨hσ₁, hσ₂⟩
  have htσ : X.tgt σ ∈ U := ⟨hτ₂.mapsTo hσ₂, by
    show τ₂ (X.tgt σ) ∈ T
    rw [hτ₂.left_inv σ hσ₂]; exact hσT⟩
  refine ⟨U, U', L, htσ, ?_, ?_⟩
  · change X.src (τ₂ (X.tgt σ)) = X.src σ
    rw [hτ₂.left_inv σ hσ₂]
  · intro f hf hfun x'' hx''
    have hρ : τ₂ x'' ∈ T := ht.mapsTo_inv hx''
    have hsρ : X.src (τ₂ x'') ∈ U' := hs.mapsTo hρ
    have h1 : P (f (X.src (τ₂ x''))) = X.src (τ₁ (P (f (X.src (τ₂ x''))))) :=
      (hsrc₁ _ (by rw [hf]; exact hsρ)).symm
    have h2 : τ₁ (P (f (X.src (τ₂ x'')))) = τ₂ x'' := by rw [hf, hs.left_inv _ hρ]
    change f x'' = E.sectionAct τ₁ (f (X.src (τ₂ x'')))
    rw [E.sectionAct_of_eq τ₁ h1]
    exact (congrArg f (ht.right_inv x'' hx'').symm).trans
      ((hfun (τ₂ x'')).trans (E.μ_congr (Prod.ext h2.symm rfl)))

end EpStrongBundle

end Act

/-! ### Theorem 10.4.5, the `Fred` part -/

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
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'}

namespace EpStrongBundle

namespace IsStrongBundleEquivalence

variable {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (h : E.IsStrongBundleEquivalence E' ϕ Φ)

/-- Around every `x ∈ X` the pull-back `Φ^* f'` is `Ψ ∘ f' ∘ ϕ` for the local strong bundle
isomorphism of Definition 10.4.1 (2). -/
theorem exists_localIso_pullback (f' : Obj' → W') (hf' : IsSection P' f') (x : Obj) :
    ∃ (U : Set Obj) (U' : Set Obj') (L : StrongBundle.LocalIso B B' U U'), x ∈ U ∧
      L.ϕ = ϕ.obj ∧ L.Φ = Φ.obj ∧ EqOn (h.pullback f') (L.Ψ ∘ f' ∘ L.ϕ) U := by
  obtain ⟨U, U', hxU, hi⟩ := h.isLocalStrongBundleIso_obj x
  exact ⟨U, U', hi.toLocalIso, hxU, rfl, rfl,
    (h.eqOn_pullback hf' hi.toLocalIso.base hi.toLocalIso.zero).symm⟩

/-- **`Φ^*` maps sc-Fredholm sections to sc-Fredholm sections** (Theorem 10.4.5, `Fred` part,
pull-back): Definition 3.1.18 is local and invariant under local strong bundle isomorphisms. -/
theorem isScFredholmSection_pullback {f' : Obj' → W'} (hf' : B'.IsScFredholmSection f') :
    B.IsScFredholmSection (h.pullback f') :=
  StrongBundle.isScFredholmSection_of_forall (h.isScSmoothSection_pullback hf'.isScSmooth)
    fun x => by
      obtain ⟨U, U', L, hxU, -, -, heq⟩ := h.exists_localIso_pullback f' hf'.isScSmooth.1 x
      exact ⟨U, U', L, f', hxU, heq, hf'⟩

/-- The tame form: `Φ^*` preserves tame germ data (Definition 3.6.5). -/
theorem isScFredholmSectionTame_pullback {f' : Obj' → W'} (hf' : B'.IsScFredholmSectionTame f') :
    B.IsScFredholmSectionTame (h.pullback f') :=
  StrongBundle.isScFredholmSectionTame_of_forall (h.isScSmoothSection_pullback hf'.isScSmooth)
    fun x => by
      obtain ⟨U, U', L, hxU, -, -, heq⟩ := h.exists_localIso_pullback f' hf'.isScSmooth.1 x
      exact ⟨U, U', L, f', hxU, heq, hf'⟩

/-- **Descent**: around every `ϕ(y)`, the push-forward `Φ_* f` of a section functor is
`Φ ∘ f ∘ ϕ⁻¹`, i.e. `f` is its pull-back along the inverse local strong bundle isomorphism. -/
theorem exists_localIso_pushforward {f : Obj → W} (hf : IsSection P f)
    (hfun : E.IsFunctorialSection hf) (y : Obj) :
    ∃ (U : Set Obj') (U' : Set Obj) (L : StrongBundle.LocalIso B' B U U'), ϕ.obj y ∈ U ∧
      L.ϕ (ϕ.obj y) = y ∧ EqOn (h.pushforward f) (L.Ψ ∘ f ∘ L.ϕ) U := by
  have hs' : IsSection P' (h.pushforward f) := h.isSection_pushforward f
  obtain ⟨U₁, U₁', L₁, hyU, hLϕ, -, heq⟩ := h.exists_localIso_pullback (h.pushforward f) hs' y
  refine ⟨U₁', U₁, L₁.symm, by rw [← hLϕ]; exact L₁.base.mapsTo hyU, ?_, fun x'' hx'' => ?_⟩
  · change L₁.g (ϕ.obj y) = y
    rw [← hLϕ]; exact L₁.base.left_inv y hyU
  have hg : L₁.g x'' ∈ U₁ := L₁.base.mapsTo_inv hx''
  have h1 := heq hg
  rw [h.pullback_pushforward hf hfun] at h1
  change h.pushforward f x'' = L₁.Φ (f (L₁.g x''))
  rw [h1]
  change h.pushforward f x'' = L₁.Φ (L₁.Ψ (h.pushforward f (L₁.ϕ (L₁.g x''))))
  rw [L₁.base.right_inv x'' hx'',
    L₁.zero.right_inv _ (show P' (h.pushforward f x'') ∈ U₁' by rw [hs']; exact hx'')]

/-- **`Φ_*` maps sc-Fredholm section functors to sc-Fredholm sections** (Theorem 10.4.5, `Fred`
part, push-forward): near `x' ∈ X'` with `σ : ϕ(y) → x'`, `Φ_* f` is its own pull-back along
the action of `σ` (`exists_localIso_mor`), and near `ϕ(y)` it is `Φ ∘ f ∘ ϕ⁻¹`
(`exists_localIso_pushforward`); the key lemma applies twice. -/
theorem isScFredholmSection_pushforward {f : Obj → W} (hf : E.IsScFredholmSectionFunctor f) :
    B'.IsScFredholmSection (h.pushforward f) := by
  obtain ⟨⟨hs, hfun⟩, hF⟩ := hf
  have hs' : B'.IsScSmoothSection (h.pushforward f) := h.isScSmoothSection_pushforward hs hfun
  have hfun' : E'.IsFunctorialSection hs'.1 := h.isFunctorialSection_pushforward hs.1 hfun
  refine ⟨hs', fun m x' hxm hfx => ?_, fun x' hxs => ?_⟩
  · obtain ⟨U₂, U₂', L₂, hx'U₂, hL₂ϕ, hL₂eq⟩ := E'.exists_localIso_mor (h.preMor x')
    rw [h.tgt_preMor] at hx'U₂ hL₂ϕ
    rw [h.src_preMor] at hL₂ϕ
    obtain ⟨U₁, U₁', L₁, hyU₁, hL₁ϕ, hL₁eq⟩ := h.exists_localIso_pushforward hs.1 hfun (h.preObj x')
    refine L₂.regularizing_at (hL₂eq _ hs'.1 hfun') hs'.1 hs'.1 hx'U₂ m ?_ hxm hfx
    rw [hL₂ϕ]
    intro h1 h2
    refine L₁.regularizing_at hL₁eq hs'.1 hs.1 hyU₁ m ?_ h1 h2
    rw [hL₁ϕ]
    exact hF.regularizing m _
  · obtain ⟨U₂, U₂', L₂, hx'U₂, hL₂ϕ, hL₂eq⟩ := E'.exists_localIso_mor (h.preMor x')
    rw [h.tgt_preMor] at hx'U₂ hL₂ϕ
    rw [h.src_preMor] at hL₂ϕ
    obtain ⟨U₁, U₁', L₁, hyU₁, hL₁ϕ, hL₁eq⟩ := h.exists_localIso_pushforward hs.1 hfun (h.preObj x')
    refine L₂.isScFredholmGerm (hL₂eq _ hs'.1 hfun') hs'.1 hx'U₂ ?_
    rw [hL₂ϕ]
    refine L₁.isScFredholmGerm hL₁eq hs.1 hyU₁ ?_
    rw [hL₁ϕ]
    refine hF.germ _ ?_
    have := (L₂.mem_smoothSet_iff hx'U₂).1 hxs
    rw [hL₂ϕ, L₁.mem_smoothSet_iff hyU₁, hL₁ϕ] at this
    exact this

/-- The tame form: `Φ_*` preserves tame germ data (Definition 3.6.5). -/
theorem isScFredholmSectionTame_pushforward {f : Obj → W} (hf : E.IsScSmoothSectionFunctor f)
    (hF : B.IsScFredholmSectionTame f) : B'.IsScFredholmSectionTame (h.pushforward f) := by
  obtain ⟨hs, hfun⟩ := hf
  have hs' : B'.IsScSmoothSection (h.pushforward f) := h.isScSmoothSection_pushforward hs hfun
  have hfun' : E'.IsFunctorialSection hs'.1 := h.isFunctorialSection_pushforward hs.1 hfun
  refine ⟨h.isScFredholmSection_pushforward ⟨⟨hs, hfun⟩, hF.toIsScFredholmSection⟩,
    fun x' hxs => ?_⟩
  obtain ⟨U₂, U₂', L₂, hx'U₂, hL₂ϕ, hL₂eq⟩ := E'.exists_localIso_mor (h.preMor x')
  rw [h.tgt_preMor] at hx'U₂ hL₂ϕ
  rw [h.src_preMor] at hL₂ϕ
  obtain ⟨U₁, U₁', L₁, hyU₁, hL₁ϕ, hL₁eq⟩ := h.exists_localIso_pushforward hs.1 hfun (h.preObj x')
  refine L₂.isScFredholmGermTame (hL₂eq _ hs'.1 hfun') hs'.1 hx'U₂ ?_
  rw [hL₂ϕ]
  refine L₁.isScFredholmGermTame hL₁eq hs.1 hyU₁ ?_
  rw [hL₁ϕ]
  refine hF.germTame _ ?_
  have := (L₂.mem_smoothSet_iff hx'U₂).1 hxs
  rw [hL₂ϕ, L₁.mem_smoothSet_iff hyU₁, hL₁ϕ] at this
  exact this

end IsStrongBundleEquivalence

/-- **2021 Theorem 10.4.5, p. 500 (2017: Theorem 10.8, p. 362), the `Fred` part** (G.121): for a
strong bundle equivalence `Φ` covering `ϕ`, `Φ_*` and `Φ^*` map sc-Fredholm section functors to
sc-Fredholm section functors, and restrict to mutually inverse bijections
`Fred(P, μ) ↔ Fred(P', μ')`.  The rest of the theorem is `theorem_10_4_5`. -/
theorem theorem_10_4_5_fred {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (h : E.IsStrongBundleEquivalence E' ϕ Φ) :
    MapsTo h.pushforward E.fredholmSectionFunctors E'.fredholmSectionFunctors ∧
    MapsTo h.pullback E'.fredholmSectionFunctors E.fredholmSectionFunctors ∧
    InvOn h.pullback h.pushforward E.fredholmSectionFunctors E'.fredholmSectionFunctors ∧
    BijOn h.pushforward E.fredholmSectionFunctors E'.fredholmSectionFunctors := by
  have hpush : MapsTo h.pushforward E.fredholmSectionFunctors E'.fredholmSectionFunctors :=
    fun f hf => ⟨(theorem_10_4_5 h).1.1 hf.1, h.isScFredholmSection_pushforward hf⟩
  have hpull : MapsTo h.pullback E'.fredholmSectionFunctors E.fredholmSectionFunctors :=
    fun f' hf' => ⟨(theorem_10_4_5 h).1.2.1 hf'.1, h.isScFredholmSection_pullback hf'.2⟩
  have hinv := (theorem_10_4_5 h).1.2.2.1.mono E.fredholmSectionFunctors_subset
    E'.fredholmSectionFunctors_subset
  exact ⟨hpush, hpull, hinv, hinv.bijOn hpush hpull⟩

end EpStrongBundle

end Functors

/-! ### Theorem 10.5.4, the `Fred` part -/

namespace SBLocalization

variable {A A' : SEP.{u}}

namespace SDiagram

variable (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)

theorem mapsTo_pushforward_fred :
    MapsTo (D.pushforward hΨ) A.E.fredholmSectionFunctors A'.E.fredholmSectionFunctors :=
  (EpStrongBundle.theorem_10_4_5_fred (sbe hΨ)).1.comp
    (EpStrongBundle.theorem_10_4_5_fred D.hΦ).2.1

theorem mapsTo_pullback_fred :
    MapsTo (D.pullback hΨ) A'.E.fredholmSectionFunctors A.E.fredholmSectionFunctors :=
  (D.symm hΨ).mapsTo_pushforward_fred D.isEquivalence_Φ

theorem bijOn_pushforward_fred :
    BijOn (D.pushforward hΨ) A.E.fredholmSectionFunctors A'.E.fredholmSectionFunctors :=
  ((D.invOn_pullback_pushforward hΨ).mono A.E.fredholmSectionFunctors_subset
    A'.E.fredholmSectionFunctors_subset).bijOn (D.mapsTo_pushforward_fred hΨ)
    (D.mapsTo_pullback_fred hΨ)

end SDiagram

namespace GenSBMap

/-- **2021 Theorem 10.5.4, p. 508 (2017: Theorem 10.9, p. 367), the `Fred` part** (G.125): for
a generalized strong bundle isomorphism `[D]`, `[D]_*` maps `Fred(P, μ)` bijectively onto
`Fred(P', μ')`, `[D]^*` maps `Fred(P', μ')` into `Fred(P, μ)`, and the inverse of `[D]_*` on
`Fred` is `[D]^*` (the push-forward along the inverse diagram).  The rest of the theorem is
`theorem_10_5_4`. -/
theorem theorem_10_5_4_fred {f : GenSBMap A A'} (hf : f.IsGeneralizedIso) :
    MapsTo (pushforward hf) A.E.fredholmSectionFunctors A'.E.fredholmSectionFunctors ∧
    MapsTo (pullback hf) A'.E.fredholmSectionFunctors A.E.fredholmSectionFunctors ∧
    BijOn (pushforward hf) A.E.fredholmSectionFunctors A'.E.fredholmSectionFunctors ∧
    (∀ (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) (_ : D.cls = f),
      EqOn (pushforward (isGeneralizedIso_symm D hΨ)) (pullback hf)
        A'.E.fredholmSectionFunctors) :=
  ⟨(rep hf).mapsTo_pushforward_fred _, (rep hf).mapsTo_pullback_fred _,
    (rep hf).bijOn_pushforward_fred _, fun D hΨ hD =>
      ((theorem_10_5_4 hf).2.2.1 D hΨ hD).mono A'.E.fredholmSectionFunctors_subset⟩

end GenSBMap

end SBLocalization

end Polyfold
