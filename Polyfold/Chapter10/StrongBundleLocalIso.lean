import Polyfold.Chapter10.LocalizationLRBundleBase

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapters 8 and 10: local strong bundle isomorphisms between two strong bundles, the tool
for **Propositions 10.4.6, 10.4.7 and 10.5.6** (§10.4, pp. 501–502, and §10.5, p. 508, new in the
2021 edition), which are in `StrongBundleLocalRegularity.lean`.

# Local strong bundle isomorphisms `Y|U → Y'|U'`

`StrongBundle.IsLocalIsoOn` (`LocalizationLRBundleBase.lean`) is a strong bundle isomorphism of
`Y|U` onto itself with no condition off `Y|U`.  The proofs of Propositions 10.4.6 and 10.4.7
compose such maps with strong bundle isomorphisms between two different bundles (the restriction
of a strong bundle equivalence, and the transport `w ↦ μ(m(P w), w)` along a family of
morphisms), and invert them.  `StrongBundle.IsLocalIso₂ B B' f g Φ Ψ U U'` records the data:
`f : U → U'` an sc-diffeomorphism with inverse `g`, `Φ` and its inverse `Ψ` linear on the fibres,
mutually inverse sc-diffeomorphisms of `Y|U` and `Y'|U'` at level `[0]` and, through maps
agreeing with them, at level `[1]`.

## What is formalized

* `StrongBundle.IsLocalIso₂`, `covers`, `covers_inv`, `symm`, `comp`, `restrict`,
  `restrict_image`, `restrict_target`, `isLocalIsoOn` (the case `Y' = Y`, `U' = U`), and the
  converse `IsLocalIsoOn.exists_isLocalIso₂` (the inverse of a local isomorphism is linear on the
  fibres: `exists_linear_inv_of`).
* `StrongBundle.IsStrongBundleIsoOn.exists_isLocalIso₂`: a strong bundle map restricting to a
  strong bundle isomorphism `Y|U → Y'|U'` (Chapter 8) gives one.
* `EpStrongBundle.isLocalIso₂_lrAct`: for an sc-smooth family `m(y) : y → τ(y)` of morphisms over
  `U` with `τ : U → U'` an sc-diffeomorphism, `w ↦ μ(m(P w), w)` is a local strong bundle
  isomorphism `W|U → W|U'` covering `τ`, with inverse `w ↦ μ(m(τ⁻¹(P w))⁻¹, w)`.
* `EpStrongBundle.lrAct_comp`: `μ(a ∘ b, w) = μ(a, μ(b, w))` in the total form `lrAct`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

section LocalIso₂

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

/-- **A strong bundle isomorphism `Y|U → Y'|U'`** covering the sc-diffeomorphism `f : U → U'`
(inverse `g`), with inverse `Ψ`, and no condition off `Y|U`: `Φ` and `Ψ` are linear on the
fibres over `U` and `U'`, mutually inverse sc-diffeomorphisms of `Y|U` and `Y'|U'` at level `[0]`,
and, through maps `Φ₁`, `Ψ₁` of `Y[1]`, `Y'[1]` agreeing with them, at level `[1]`. -/
structure IsLocalIso₂ (B : StrongBundle PX P) (B' : StrongBundle PX' P') (f : X → X') (g : X' → X)
    (Φ : Y → Y') (Ψ : Y' → Y) (U : Set X) (U' : Set X') : Prop where
  base : PX.IsScDiffeoOn PX' f g U U'
  fiber_linear : ∀ x ∈ U, ∃ L : P ⁻¹' {x} →ₗ[ℝ] P' ⁻¹' {f x}, ∀ v, (L v : Y') = Φ v
  fiber_linear_inv : ∀ y ∈ U', ∃ L : P' ⁻¹' {y} →ₗ[ℝ] P ⁻¹' {g y}, ∀ v, (L v : Y) = Ψ v
  zero : B.toMPolyfold0.IsScDiffeoOn B'.toMPolyfold0 Φ Ψ (P ⁻¹' U) (P' ⁻¹' U')
  one : ∃ (Φ₁ : B.One → B'.One) (Ψ₁ : B'.One → B.One),
    (∀ y, P (B.oneVal y) ∈ U → B'.oneVal (Φ₁ y) = Φ (B.oneVal y)) ∧
    (∀ y, P' (B'.oneVal y) ∈ U' → B.oneVal (Ψ₁ y) = Ψ (B'.oneVal y)) ∧
    B.toMPolyfold1.IsScDiffeoOn B'.toMPolyfold1 Φ₁ Ψ₁ ((P ∘ B.oneVal) ⁻¹' U)
      ((P' ∘ B'.oneVal) ⁻¹' U')

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {B'' : StrongBundle PX'' P''}
  {f : X → X'} {g : X' → X} {Φ : Y → Y'} {Ψ : Y' → Y} {U : Set X} {U' : Set X'}

namespace IsLocalIso₂

theorem covers (h : B.IsLocalIso₂ B' f g Φ Ψ U U') {w : Y} (hw : P w ∈ U) :
    P' (Φ w) = f (P w) := by
  obtain ⟨L, hL⟩ := h.fiber_linear (P w) hw
  rw [← hL ⟨w, rfl⟩]
  exact (L ⟨w, rfl⟩).2

theorem covers_inv (h : B.IsLocalIso₂ B' f g Φ Ψ U U') {w : Y'} (hw : P' w ∈ U') :
    P (Ψ w) = g (P' w) := by
  obtain ⟨L, hL⟩ := h.fiber_linear_inv (P' w) hw
  rw [← hL ⟨w, rfl⟩]
  exact (L ⟨w, rfl⟩).2

theorem mapsTo (h : B.IsLocalIso₂ B' f g Φ Ψ U U') {w : Y} (hw : P w ∈ U) : P' (Φ w) ∈ U' :=
  h.zero.mapsTo hw

theorem mapsTo_inv (h : B.IsLocalIso₂ B' f g Φ Ψ U U') {w : Y'} (hw : P' w ∈ U') : P (Ψ w) ∈ U :=
  h.zero.mapsTo_inv hw

theorem left_inv (h : B.IsLocalIso₂ B' f g Φ Ψ U U') {w : Y} (hw : P w ∈ U) : Ψ (Φ w) = w :=
  h.zero.left_inv w hw

theorem right_inv (h : B.IsLocalIso₂ B' f g Φ Ψ U U') {w : Y'} (hw : P' w ∈ U') : Φ (Ψ w) = w :=
  h.zero.right_inv w hw

/-- The inverse. -/
theorem symm (h : B.IsLocalIso₂ B' f g Φ Ψ U U') : B'.IsLocalIso₂ B g f Ψ Φ U' U where
  base := h.base.symm
  fiber_linear := h.fiber_linear_inv
  fiber_linear_inv := h.fiber_linear
  zero := h.zero.symm
  one := let ⟨Φ₁, Ψ₁, h₁, h₂, h₃⟩ := h.one; ⟨Ψ₁, Φ₁, h₂, h₁, h₃.symm⟩

/-- **Composition** `Y|U → Y'|U' → Y''|U''`. -/
theorem comp {f₂ : X' → X''} {g₂ : X'' → X'} {Φ₂ : Y' → Y''} {Ψ₂ : Y'' → Y'} {U'' : Set X''}
    (h₂ : B'.IsLocalIso₂ B'' f₂ g₂ Φ₂ Ψ₂ U' U'') (h₁ : B.IsLocalIso₂ B' f g Φ Ψ U U') :
    B.IsLocalIso₂ B'' (f₂ ∘ f) (g ∘ g₂) (Φ₂ ∘ Φ) (Ψ ∘ Ψ₂) U U'' where
  base := h₂.base.comp h₁.base
  fiber_linear x hx := by
    obtain ⟨L₁, hL₁⟩ := h₁.fiber_linear x hx
    obtain ⟨L₂, hL₂⟩ := h₂.fiber_linear (f x) (h₁.base.mapsTo hx)
    exact ⟨L₂.comp L₁, fun v => by
      simp only [LinearMap.coe_comp, Function.comp_apply, hL₂, hL₁]⟩
  fiber_linear_inv y hy := by
    obtain ⟨L₂, hL₂⟩ := h₂.fiber_linear_inv y hy
    obtain ⟨L₁, hL₁⟩ := h₁.fiber_linear_inv (g₂ y) (h₂.base.mapsTo_inv hy)
    exact ⟨L₁.comp L₂, fun v => by
      simp only [LinearMap.coe_comp, Function.comp_apply, hL₂, hL₁]⟩
  zero := h₂.zero.comp h₁.zero
  one := by
    obtain ⟨Φ₁, Ψ₁, a₁, b₁, c₁⟩ := h₁.one
    obtain ⟨Φ₂₁, Ψ₂₁, a₂, b₂, c₂⟩ := h₂.one
    refine ⟨Φ₂₁ ∘ Φ₁, Ψ₁ ∘ Ψ₂₁, fun y hy => ?_, fun y hy => ?_, c₂.comp c₁⟩
    · have h' : P' (B'.oneVal (Φ₁ y)) ∈ U' := c₁.mapsTo hy
      simp only [Function.comp_apply, a₂ _ h', a₁ y hy]
    · have h' : P' (B'.oneVal (Ψ₂₁ y)) ∈ U' := c₂.mapsTo_inv hy
      simp only [Function.comp_apply, b₁ _ h', b₂ y hy]

/-- **Restriction** to an open `U₀ ⊆ U`: a local isomorphism `Y|U₀ → Y'|(U' ∩ g⁻¹(U₀))`. -/
theorem restrict (h : B.IsLocalIso₂ B' f g Φ Ψ U U') {U₀ : Set X} (hU₀ : IsOpen U₀)
    (hsub : U₀ ⊆ U) : B.IsLocalIso₂ B' f g Φ Ψ U₀ (U' ∩ g ⁻¹' U₀) where
  base := h.base.restrict hU₀ hsub
  fiber_linear x hx := h.fiber_linear x (hsub hx)
  fiber_linear_inv y hy := h.fiber_linear_inv y hy.1
  zero := by
    have e := h.zero.restrict (hU₀.preimage B.continuous) (preimage_mono hsub)
    have hset : P' ⁻¹' U' ∩ Ψ ⁻¹' (P ⁻¹' U₀) = P' ⁻¹' (U' ∩ g ⁻¹' U₀) := by
      ext w'
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [← h.covers_inv h1]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [h.covers_inv h1]; exact h2⟩
    rwa [hset] at e
  one := by
    obtain ⟨Φ₁, Ψ₁, a₁, b₁, c₁⟩ := h.one
    have hc : Continuous (P ∘ B.oneVal) := B.continuous.comp B.continuous_oneVal
    have e := c₁.restrict (hU₀.preimage hc) (preimage_mono hsub)
    have hset : (P' ∘ B'.oneVal) ⁻¹' U' ∩ Ψ₁ ⁻¹' ((P ∘ B.oneVal) ⁻¹' U₀) =
        (P' ∘ B'.oneVal) ⁻¹' (U' ∩ g ⁻¹' U₀) := by
      ext w'
      simp only [mem_inter_iff, mem_preimage, Function.comp_apply]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [← h.covers_inv h1, ← b₁ w' h1]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [b₁ w' h1, h.covers_inv h1]; exact h2⟩
    rw [hset] at e
    exact ⟨Φ₁, Ψ₁, fun y hy => a₁ y (hsub hy), fun y hy => b₁ y hy.1, e⟩

/-- Restriction to an open `U₀ ⊆ U`, with target `f(U₀)`. -/
theorem restrict_image (h : B.IsLocalIso₂ B' f g Φ Ψ U U') {U₀ : Set X} (hU₀ : IsOpen U₀)
    (hsub : U₀ ⊆ U) : B.IsLocalIso₂ B' f g Φ Ψ U₀ (f '' U₀) := by
  have e := h.restrict hU₀ hsub
  rwa [← e.base.image_eq] at e

/-- Restriction to an open `U₀' ⊆ U'` of the target: `Y|(U ∩ f⁻¹(U₀')) → Y'|U₀'`. -/
theorem restrict_target (h : B.IsLocalIso₂ B' f g Φ Ψ U U') {U₀' : Set X'} (hU₀' : IsOpen U₀')
    (hsub : U₀' ⊆ U') : B.IsLocalIso₂ B' f g Φ Ψ (U ∩ f ⁻¹' U₀') U₀' :=
  (h.symm.restrict hU₀' hsub).symm

/-- **A local isomorphism `Y|U → Y|U` is one in the sense of `IsLocalIsoOn`.** -/
theorem isLocalIsoOn {β β' : X → X} {Φ Ψ : Y → Y} (h : B.IsLocalIso₂ B β β' Φ Ψ U U) :
    B.IsLocalIsoOn β Φ U where
  fiber_linear := h.fiber_linear
  isScDiffeoOn_base := ⟨β', h.base⟩
  isScDiffeoOn_zero := ⟨Ψ, h.zero⟩
  isScDiffeoOn_one := let ⟨Φ₁, Ψ₁, h₁, _, h₃⟩ := h.one; ⟨Φ₁, Ψ₁, h₁, h₃⟩

/-- Changing `Φ` and `Ψ` on the complements of `Y|U` and `Y'|U'`. -/
theorem congr (h : B.IsLocalIso₂ B' f g Φ Ψ U U') {Φ' : Y → Y'} {Ψ' : Y' → Y}
    (hΦ : ∀ w, P w ∈ U → Φ' w = Φ w) (hΨ : ∀ w, P' w ∈ U' → Ψ' w = Ψ w) :
    B.IsLocalIso₂ B' f g Φ' Ψ' U U' where
  base := h.base
  fiber_linear x hx := let ⟨L, hL⟩ := h.fiber_linear x hx
    ⟨L, fun v => by rw [hL, hΦ _ (by rw [show P v = x from v.2]; exact hx)]⟩
  fiber_linear_inv y hy := let ⟨L, hL⟩ := h.fiber_linear_inv y hy
    ⟨L, fun v => by rw [hL, hΨ _ (by rw [show P' v = y from v.2]; exact hy)]⟩
  zero := by
    have z := h.zero
    exact ⟨z.isScSmoothOn.congr fun w hw => (hΦ w hw).symm,
      z.isScSmoothOn_inv.congr fun w hw => (hΨ w hw).symm,
      fun w hw => by rw [mem_preimage, hΦ w hw]; exact z.mapsTo hw,
      fun w hw => by rw [mem_preimage, hΨ w hw]; exact z.mapsTo_inv hw,
      fun w hw => by rw [hΦ w hw, hΨ _ (z.mapsTo hw)]; exact z.left_inv w hw,
      fun w hw => by rw [hΨ w hw, hΦ _ (z.mapsTo_inv hw)]; exact z.right_inv w hw⟩
  one := let ⟨Φ₁, Ψ₁, h₁, h₂, h₃⟩ := h.one
    ⟨Φ₁, Ψ₁, fun y hy => by rw [h₁ y hy, hΦ _ hy], fun y hy => by rw [h₂ y hy, hΨ _ hy], h₃⟩

end IsLocalIso₂

/-- **The inverse of a fibrewise linear local sc-diffeomorphism is linear on the fibres**: if
`f : U → U'` is an sc-diffeomorphism with inverse `g`, `Φ` is linear from `Y_x` to `Y'_{f(x)}`
for `x ∈ U` and `Ψ` is its inverse on `Y|U`, `Y'|U'`, then `Ψ` is linear from `Y'_y` to
`Y_{g(y)}` for `y ∈ U'`. -/
theorem exists_linear_inv_of (hb : PX.IsScDiffeoOn PX' f g U U')
    (hl : ∀ x ∈ U, ∃ L : P ⁻¹' {x} →ₗ[ℝ] P' ⁻¹' {f x}, ∀ v, (L v : Y') = Φ v)
    (hz : B.toMPolyfold0.IsScDiffeoOn B'.toMPolyfold0 Φ Ψ (P ⁻¹' U) (P' ⁻¹' U')) {y : X'}
    (hy : y ∈ U') : ∃ L : P' ⁻¹' {y} →ₗ[ℝ] P ⁻¹' {g y}, ∀ v, (L v : Y) = Ψ v := by
  have hx : g y ∈ U := hb.mapsTo_inv hy
  obtain ⟨L₀, hL₀⟩ := hl (g y) hx
  have hfy : f (g y) = y := hb.right_inv y hy
  have hcov : ∀ w, P w ∈ U → P' (Φ w) = f (P w) := fun w hw => by
    obtain ⟨L, hL⟩ := hl (P w) hw
    rw [← hL ⟨w, rfl⟩]
    exact (L ⟨w, rfl⟩).2
  have hmem : ∀ u : P' ⁻¹' {f (g y)}, P' (u : Y') ∈ U' := fun u => by
    rw [show P' (u : Y') = f (g y) from u.2, hfy]; exact hy
  have hPΨ : ∀ u : P' ⁻¹' {f (g y)}, P (Ψ u) = g y := fun u => by
    have h1 := hz.mapsTo_inv (hmem u)
    have h2 : f (P (Ψ u)) = f (g y) := by
      rw [← hcov _ h1, hz.right_inv _ (hmem u)]; exact u.2
    exact hb.injOn h1 hx h2
  have hinj : Injective L₀ := fun a b hab => by
    have ha : P (a : Y) ∈ U := by rw [show P (a : Y) = g y from a.2]; exact hx
    have hb' : P (b : Y) ∈ U := by rw [show P (b : Y) = g y from b.2]; exact hx
    have h1 := congrArg Subtype.val hab
    rw [hL₀, hL₀] at h1
    exact Subtype.ext (by rw [← hz.left_inv _ ha, h1, hz.left_inv _ hb'])
  have hsurj : Surjective L₀ := fun u => ⟨⟨Ψ u, hPΨ u⟩, Subtype.ext (by
    rw [hL₀]; exact hz.right_inv _ (hmem u))⟩
  set e := LinearEquiv.ofBijective L₀ ⟨hinj, hsurj⟩
  refine ⟨(e.symm : P' ⁻¹' {f (g y)} →ₗ[ℝ] P ⁻¹' {g y}).comp (fiberCast P' hfy.symm),
    fun v => ?_⟩
  set u := fiberCast P' hfy.symm v
  have hu : (u : Y') = v := fiberCast_val _ _
  have h1 : Φ (e.symm u : Y) = (u : Y') := by
    have h0 : L₀ (e.symm u) = u := e.apply_symm_apply u
    have := congrArg Subtype.val h0
    rwa [hL₀] at this
  have h2 : (e.symm u : Y) ∈ P ⁻¹' U := by
    change P (e.symm u : Y) ∈ U; rw [(e.symm u).2]; exact hx
  change (e.symm u : Y) = Ψ v
  rw [← hz.left_inv _ h2, h1, hu]

/-- **A local isomorphism in the sense of `IsLocalIsoOn` gives an `IsLocalIso₂`.** -/
theorem IsLocalIsoOn.exists_isLocalIso₂ {β : X → X} {Φ : Y → Y} (h : B.IsLocalIsoOn β Φ U) :
    ∃ (β' : X → X) (Ψ : Y → Y), B.IsLocalIso₂ B β β' Φ Ψ U U := by
  obtain ⟨β', hβ⟩ := h.isScDiffeoOn_base
  obtain ⟨Ψ, hΨ⟩ := h.isScDiffeoOn_zero
  obtain ⟨Φ₁, Ψ₁, h₁, h₂⟩ := h.isScDiffeoOn_one
  refine ⟨β', Ψ, ⟨hβ, h.fiber_linear, fun y hy => exists_linear_inv_of hβ h.fiber_linear hΨ hy,
    hΨ, Φ₁, Ψ₁, h₁, fun y hy => ?_, h₂⟩⟩
  have hm : P (B.oneVal (Ψ₁ y)) ∈ U := h₂.mapsTo_inv hy
  have e := congrArg B.oneVal (h₂.right_inv y hy)
  rw [h₁ _ hm] at e
  rw [← e, hΨ.left_inv _ hm]

/-- **A strong bundle isomorphism `Y|U → Y'|U'` (Chapter 8) gives an `IsLocalIso₂`.** -/
theorem IsStrongBundleIsoOn.exists_isLocalIso₂ {h : B.IsStrongBundleMap B' f Φ}
    (hi : B.IsStrongBundleIsoOn B' h U U') :
    ∃ (g : X' → X) (Ψ : Y' → Y), B.IsLocalIso₂ B' f g Φ Ψ U U' := by
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨Ψ, hΨ⟩ := hi.isScDiffeoOn_zero
  obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
  exact ⟨g, Ψ, hg, fun x _ => ⟨h.fiberLinearMap x, fun _ => rfl⟩,
    fun y hy => hi.exists_linear_inv hg hΨ hy, hΨ, _, Ψ₁, fun _ _ => rfl,
    fun y hy => IsStrongBundleIsoOn.oneVal_inv (h := h) hΨ hΨ₁ hy, hΨ₁⟩

end StrongBundle

end LocalIso₂

/-! ### The transport `w ↦ μ(m(P w), w)` along a family of morphisms -/

section Transport

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  {E : EpStrongBundle X B}

namespace EpStrongBundle

/-- `μ(a ∘ b, w) = μ(a, μ(b, w))`, in the total form `lrAct`. -/
theorem lrAct_comp {a b : Mor} {w : W} (hw : P w = X.src b) (hab : X.src a = X.tgt b) :
    E.lrAct (X.comp a b) w = E.lrAct a (E.lrAct b w) := by
  have h₁ : P w = X.src (X.comp a b) := hw.trans (X.src_comp a b hab).symm
  have h₂ : P (E.lrAct b w) = X.src a := by rw [P_lrAct hw, hab]
  rw [lrAct_eq h₁, lrAct_eq h₂, E.μ_comp a b w hw hab]
  exact E.μ_congr (Prod.ext rfl (lrAct_eq hw).symm)

/-- `natLift` in the total form `lrAct`. -/
theorem natLift_eq_lrAct {x : Obj} (R : X.NaturalRep x) (g : X.Isotropy x) (w : W)
    (hw : P w ∈ R.U) : E.natLift R g w hw = E.lrAct (R.Γ g (P w)) w :=
  (lrAct_eq (R.src_Γ g (P w) hw).symm).symm

/-- **The transport along a family of morphisms is a local strong bundle isomorphism**: if
`m : U → 𝐗` is sc-smooth with `m(y) : y → τ(y)` and `τ : U → U'` is an sc-diffeomorphism with
inverse `τ'`, then `w ↦ μ(m(P w), w)` is a strong bundle isomorphism `W|U → W|U'` covering `τ`,
with inverse `w ↦ μ(m(τ'(P w))⁻¹, w)`. -/
theorem isLocalIso₂_lrAct {m : Obj → Mor} {τ τ' : Obj → Obj} {U U' : Set Obj}
    (hm : X.PObj.IsScSmoothOn X.PMor m U) (hs : ∀ y ∈ U, X.src (m y) = y)
    (ht : ∀ y ∈ U, X.tgt (m y) = τ y) (hτ : X.PObj.IsScDiffeoOn X.PObj τ τ' U U') :
    B.IsLocalIso₂ B τ τ' (fun w => E.lrAct (m (P w)) w)
      (fun w => E.lrAct (X.inv (m (τ' (P w)))) w) U U' := by
  have hUo : IsOpen (P ⁻¹' U) := hτ.isOpen_source.preimage B.continuous
  have hU'o : IsOpen (P ⁻¹' U') := hτ.isOpen_target.preimage B.continuous
  have hab : ∀ w, P w ∈ U → P w = X.src (m (P w)) := fun w hw => (hs _ hw).symm
  have hab' : ∀ w, P w ∈ U' → P w = X.src (X.inv (m (τ' (P w)))) := fun w hw => by
    rw [X.src_inv, ht _ (hτ.mapsTo_inv hw), hτ.right_inv _ hw]
  have hP1 : ∀ w, P w ∈ U → P (E.lrAct (m (P w)) w) = τ (P w) := fun w hw => by
    rw [P_lrAct (hab w hw), ht _ hw]
  have hP2 : ∀ w, P w ∈ U' → P (E.lrAct (X.inv (m (τ' (P w)))) w) = τ' (P w) := fun w hw => by
    rw [P_lrAct (hab' w hw), X.tgt_inv, hs _ (hτ.mapsTo_inv hw)]
  have hPs : B.toMPolyfold0.IsScSmoothOn X.PObj P (P ⁻¹' U) :=
    B.isScSmoothMap_proj.mono hUo (subset_univ _)
  have hPs' : B.toMPolyfold0.IsScSmoothOn X.PObj P (P ⁻¹' U') :=
    B.isScSmoothMap_proj.mono hU'o (subset_univ _)
  have ha : B.toMPolyfold0.IsScSmoothOn X.PMor (fun w => m (P w)) (P ⁻¹' U) :=
    MPolyfold.IsScSmoothOn.comp hm hPs fun _ hw => hw
  have ha' : B.toMPolyfold0.IsScSmoothOn X.PMor (fun w => X.inv (m (τ' (P w)))) (P ⁻¹' U') :=
    MPolyfold.IsScSmoothOn.comp X.isScSmoothMap_inv
      (MPolyfold.IsScSmoothOn.comp hm (MPolyfold.IsScSmoothOn.comp hτ.isScSmoothOn_inv hPs'
        fun _ hw => hw) fun _ hw => hτ.mapsTo_inv hw) (mapsTo_univ _ _)
  have hid : B.toMPolyfold0.IsScSmoothOn B.toMPolyfold0 id (P ⁻¹' U) :=
    MPolyfold.isScSmoothMap_id.mono hUo (subset_univ _)
  have hid' : B.toMPolyfold0.IsScSmoothOn B.toMPolyfold0 id (P ⁻¹' U') :=
    MPolyfold.isScSmoothMap_id.mono hU'o (subset_univ _)
  have hli : ∀ w, P w ∈ U →
      E.lrAct (X.inv (m (τ' (P (E.lrAct (m (P w)) w))))) (E.lrAct (m (P w)) w) = w :=
    fun w hw => by
      rw [hP1 w hw, hτ.left_inv _ hw]; exact lrAct_inv_lrAct (hab w hw)
  have hri : ∀ w, P w ∈ U' →
      E.lrAct (m (P (E.lrAct (X.inv (m (τ' (P w)))) w))) (E.lrAct (X.inv (m (τ' (P w)))) w) =
        w := fun w hw => by
    rw [hP2 w hw]; exact lrAct_lrAct_inv (hab' w hw)
  have h0 : B.toMPolyfold0.IsScDiffeoOn B.toMPolyfold0 (fun w => E.lrAct (m (P w)) w)
      (fun w => E.lrAct (X.inv (m (τ' (P w)))) w) (P ⁻¹' U) (P ⁻¹' U') :=
    ⟨isScSmoothOn_lrAct ha hid hab, isScSmoothOn_lrAct ha' hid' hab',
      fun w hw => by change P _ ∈ U'; rw [hP1 w hw]; exact hτ.mapsTo hw,
      fun w hw => by change P _ ∈ U; rw [hP2 w hw]; exact hτ.mapsTo_inv hw, hli, hri⟩
  refine ⟨hτ, fun x hx => ?_, fun y hy => ?_, h0, ?_⟩
  · refine ⟨(fiberCast P (ht x hx)).comp ((E.fiberMor (m x)).toLinearMap.comp
      (fiberCast P (hs x hx).symm)), fun v => ?_⟩
    have hv : P (v : W) = x := v.2
    simp only [LinearMap.coe_comp, Function.comp_apply, fiberCast_val,
      ContinuousLinearMap.coe_coe, fiberMor_apply]
    rw [lrAct_eq (show P (v : W) = X.src (m (P v)) from hab v (by rw [hv]; exact hx))]
    exact E.μ_congr (Prod.ext (congrArg m hv.symm) rfl)
  · have hs' : y = X.src (X.inv (m (τ' y))) := by
      rw [X.src_inv, ht _ (hτ.mapsTo_inv hy), hτ.right_inv _ hy]
    have ht' : X.tgt (X.inv (m (τ' y))) = τ' y := by
      rw [X.tgt_inv, hs _ (hτ.mapsTo_inv hy)]
    refine ⟨(fiberCast P ht').comp ((E.fiberMor (X.inv (m (τ' y)))).toLinearMap.comp
      (fiberCast P hs')), fun v => ?_⟩
    have hv : P (v : W) = y := v.2
    simp only [LinearMap.coe_comp, Function.comp_apply, fiberCast_val,
      ContinuousLinearMap.coe_coe, fiberMor_apply]
    rw [lrAct_eq (show P (v : W) = X.src (X.inv (m (τ' (P v)))) from
      hab' v (by rw [hv]; exact hy))]
    exact E.μ_congr (Prod.ext (congrArg (fun z => X.inv (m (τ' z))) hv.symm) rfl)
  · -- level `[1]`
    have hU1o : IsOpen ((P ∘ B.oneVal) ⁻¹' U) :=
      hτ.isOpen_source.preimage (B.continuous.comp B.continuous_oneVal)
    have hU1o' : IsOpen ((P ∘ B.oneVal) ⁻¹' U') :=
      hτ.isOpen_target.preimage (B.continuous.comp B.continuous_oneVal)
    have hov : B.toMPolyfold1.IsScSmoothOn B.toMPolyfold0 B.oneVal ((P ∘ B.oneVal) ⁻¹' U) :=
      B.isScSmoothMap_oneVal.mono hU1o (subset_univ _)
    have hov' : B.toMPolyfold1.IsScSmoothOn B.toMPolyfold0 B.oneVal ((P ∘ B.oneVal) ⁻¹' U') :=
      B.isScSmoothMap_oneVal.mono hU1o' (subset_univ _)
    have s₁ : B.toMPolyfold1.IsScSmoothOn B.toMPolyfold1
        (fun y => E.lrActOne ((fun w => m (P w)) (B.oneVal y)) (id y)) ((P ∘ B.oneVal) ⁻¹' U) :=
      isScSmoothOn_lrActOne (MPolyfold.IsScSmoothOn.comp (f := B.oneVal) ha hov fun _ hy => hy)
        (MPolyfold.isScSmoothMap_id.mono hU1o (subset_univ _)) fun y hy => hab _ hy
    have s₂ : B.toMPolyfold1.IsScSmoothOn B.toMPolyfold1
        (fun y => E.lrActOne ((fun w => X.inv (m (τ' (P w)))) (B.oneVal y)) (id y))
        ((P ∘ B.oneVal) ⁻¹' U') :=
      isScSmoothOn_lrActOne (MPolyfold.IsScSmoothOn.comp (f := B.oneVal) ha' hov' fun _ hy => hy)
        (MPolyfold.isScSmoothMap_id.mono hU1o' (subset_univ _)) fun y hy => hab' _ hy
    refine ⟨_, _, fun y _ => rfl, fun y _ => rfl, ⟨s₁, s₂, fun y hy => ?_, fun y hy => ?_,
      fun y hy => B.oneVal_injective ?_, fun y hy => B.oneVal_injective ?_⟩⟩
    · change P (E.lrAct _ (B.oneVal y)) ∈ U'
      rw [hP1 _ hy]; exact hτ.mapsTo hy
    · change P (E.lrAct _ (B.oneVal y)) ∈ U
      rw [hP2 _ hy]; exact hτ.mapsTo_inv hy
    · exact hli _ hy
    · exact hri _ hy

end EpStrongBundle

end Transport

end Polyfold
