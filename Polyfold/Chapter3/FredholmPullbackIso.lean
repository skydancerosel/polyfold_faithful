import Polyfold.Chapter3.TameGermsG
import Polyfold.Chapter3.RestrictOpenGerms
import Polyfold.Chapter5.AuxNorm
import Polyfold.Chapter8.StrongBundleMap
import Polyfold.Chapter2.TangentMap

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part I, §3.1 and §3.6, Definitions 3.1.16, 3.1.18, 3.6.4 and 3.6.5, pp. 86–88 and 115–116
(2014 preprint: Definitions 3.11, 3.14, 3.50, 3.51), **the invariance of sc-Fredholm germs and
sections under local strong bundle isomorphisms**, the step the proof of Part II's Theorem 10.4.5
(p. 500; 2017: Theorem 10.8) calls "clear": `Φ_*` and `Φ^*` map sc-Fredholm section functors to
sc-Fredholm section functors.  This file is the Part I half of gap G.121 (and, through it, of
G.125); the Part II half is `Chapter10/FredholmEquivalence.lean`.

# sc-Fredholm germs under local strong bundle isomorphisms

## The text, paraphrased

(Definition 3.1.16, p. 86) `(f, x)` is an sc-Fredholm germ if in a strong bundle chart centred at
`x` the principal part has a filling `g` with `g − s` conjugated to a basic germ for a local
sc⁺-section `s`.  (Definition 3.1.18) An sc-Fredholm section is sc-smooth, regularizing, and an
sc-Fredholm germ at every smooth point.  (Definitions 3.6.4, 3.6.5) For a tame strong bundle the
chart is taken tame.  (p. 500, proof of Theorem 10.4.5) "It is clear that `Φ^*` and `Φ_*` map
sc-Fredholm section functors to sc-Fredholm section functors", since the notions are local and
invariant under strong bundle isomorphisms.

## What is formalized

* `StrongBundle.LocalIso B B' U U'`: a **local strong bundle isomorphism** `Y|U → Y'|U'`
  covering an sc-diffeomorphism `ϕ : U → U'`, given by its data: the base maps `ϕ`, `g`, the
  total maps `Φ`, `Ψ` (sc-diffeomorphism `Y[0]|U → Y'[0]|U'`), the level-`[1]` maps `Φ₁`, `Ψ₁`
  (sc-diffeomorphism `Y[1]|U → Y'[1]|U'`), covering `P' ∘ Φ = ϕ ∘ P` on `U`, and linear on the
  fibres; `LocalIso.symm` (the inverse of a fibrewise linear bijection is linear),
  `LocalIso.refl`.
* `LocalIso.transportChart c' hsub`: **the strong bundle chart `Ψ' ∘ Φ` of `P`** obtained from a
  strong bundle chart `Ψ'` of `P'` with base domain inside `U'`: same model `E ◁ F`, same
  domain `U ◁ F`, same strong bundle retraction `R`, base chart `φ' ∘ ϕ`
  (`MPolyfold.transportChart`).  `LocalIso.isChart_transportChart`: **it is compatible with the
  atlas of `P`** (its transition maps with the charts of `P` are local representatives of `Φ`,
  `Ψ` on `[0]` and of `Φ₁`, `Ψ₁` on `[1]`), `isTameChart_transportChart` (tameness is
  preserved: same base retraction), `principal_transportChart` (**the local representative of
  `Ψ ∘ f' ∘ ϕ` in `Ψ' ∘ Φ` is that of `f'` in `Ψ'`**).
* **The key lemma** `LocalIso.isScFredholmGerm` (G.121, Part I half): if `f = Ψ ∘ f' ∘ ϕ` on `U`
  and `f'` is an sc-Fredholm germ at `ϕ(x)`, `x ∈ U`, then `f` is an sc-Fredholm germ at `x`,
  with the same germ data (`g`, `s`, the conjugation) in the transported chart; the tame form
  `isScFredholmGermTame`, and the point-wise regularizing transfer `regularizing_at`
  (`Φ₁` preserves `Y_{m,m+1}`), `mem_smoothSet_iff`.
* `StrongBundle.isScFredholmSection_of_forall`, `isScFredholmSectionTame_of_forall`: an sc-smooth
  section locally of the form `Ψ ∘ f' ∘ ϕ` for sc-Fredholm sections `f'` of a fixed bundle `P'`
  is sc-Fredholm (Definition 3.1.18 is local).

## What the text leaves implicit, and the choices made

* The text's "strong bundle isomorphism `W|U → W'|U'`" is read as `LocalIso`: an
  sc-diffeomorphism on `[0]` and on `[1]` over an sc-diffeomorphism of the bases, linear on the
  fibres.  Part II's `StrongBundle.IsStrongBundleIsoOn` (Chapter 8) gives one
  (`FredholmEquivalence.lean`), and so does the action `μ(σ, ·)` of a morphism (ibid.).
* The transported chart needs the base domain of `Ψ'` inside `U'`; a chart centred at `ϕ(x)` is
  first restricted to `dom φ' ∩ U'` (`StrongBundleChart.restrictInter`), which keeps the germ data
  (`RestrictOpenGerms.lean`).
* The filling, the sc⁺-section and the conjugation live on `U ◁ F` and are untouched; only the
  principal part changes, and it agrees with the old one on the retract `O` (which is all the
  germ conditions see).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

section Fiber

variable {X Y X' Y' : Type*} (P : Y → X) (P' : Y' → X')

/-- The fibre map `P⁻¹(x) → P'⁻¹(x')` of a map `Φ : Y → Y'` sending the fibre over `x` into the
fibre over `x'`. -/
def fiberMapOf (Φ : Y → Y') {x : X} {x' : X'} (hΦ : ∀ v : P ⁻¹' {x}, P' (Φ v) = x') :
    P ⁻¹' {x} → P' ⁻¹' {x'} :=
  fun v => ⟨Φ v, hΦ v⟩

variable {P P'}

@[simp] lemma fiberMapOf_val {Φ : Y → Y'} {x : X} {x' : X'} (hΦ : ∀ v : P ⁻¹' {x}, P' (Φ v) = x')
    (v : P ⁻¹' {x}) : (fiberMapOf P P' Φ hΦ v : Y') = Φ v := rfl

/-- The inverse of a linear bijection between modules is linear. -/
theorem IsLinearMap.of_inverse {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] {f : M → N} {g : N → M} (hf : IsLinearMap ℝ f) (hl : ∀ m, g (f m) = m)
    (hr : ∀ n, f (g n) = n) : IsLinearMap ℝ g where
  map_add a b := by
    have : f (g a + g b) = a + b := by rw [hf.map_add, hr, hr]
    rw [← this, hl]
  map_smul c a := by
    have : f (c • g a) = c • a := by rw [hf.map_smul, hr]
    rw [← this, hl]

end Fiber

section LocalIsoDefs

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]

namespace StrongBundle

/-- **A local strong bundle isomorphism `Y|U → Y'|U'`** between strong bundles over M-polyfolds
(the "strong bundle isomorphism `W|U → W'|U'`" of Part II, Definitions 8.3.5 and 10.4.1), given
by its data: an sc-diffeomorphism `ϕ : U → U'` of the bases with inverse `g`, an
sc-diffeomorphism `Φ : Y[0]|U → Y'[0]|U'` with inverse `Ψ`, an sc-diffeomorphism
`Φ₁ : Y[1]|U → Y'[1]|U'` with inverse `Ψ₁` lifting `Φ`, with `P' ∘ Φ = ϕ ∘ P` on `U` and `Φ`
linear on the fibres over `U`. -/
structure LocalIso (B : StrongBundle PX P) (B' : StrongBundle PX' P') (U : Set X) (U' : Set X')
    where
  /-- The base map `ϕ : U → U'`. -/
  ϕ : X → X'
  /-- The inverse `g : U' → U` of the base map. -/
  g : X' → X
  /-- The map `Φ : Y|U → Y'|U'`. -/
  Φ : Y → Y'
  /-- The inverse `Ψ : Y'|U' → Y|U`. -/
  Ψ : Y' → Y
  /-- The map `Φ[1] : Y[1]|U → Y'[1]|U'`. -/
  Φ₁ : B.One → B'.One
  /-- The inverse `Ψ[1]`. -/
  Ψ₁ : B'.One → B.One
  base : PX.IsScDiffeoOn PX' ϕ g U U'
  zero : B.toMPolyfold0.IsScDiffeoOn B'.toMPolyfold0 Φ Ψ (P ⁻¹' U) (P' ⁻¹' U')
  one : B.toMPolyfold1.IsScDiffeoOn B'.toMPolyfold1 Φ₁ Ψ₁ ((P ∘ B.oneVal) ⁻¹' U)
    ((P' ∘ B'.oneVal) ⁻¹' U')
  covers : ∀ y, P y ∈ U → P' (Φ y) = ϕ (P y)
  oneVal_Φ₁ : ∀ w, P (B.oneVal w) ∈ U → B'.oneVal (Φ₁ w) = Φ (B.oneVal w)
  fiber_linear : ∀ (x : X) (x' : X') (hx : x ∈ U) (hx' : ϕ x = x'),
    IsLinearMap ℝ (fiberMapOf P P' Φ (x := x) (x' := x') fun v =>
      ((covers v (by rw [show P v = x from v.2]; exact hx)).trans
        (by rw [show P v = x from v.2]; exact hx')))

namespace LocalIso

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {U : Set X} {U' : Set X'}
  (L : LocalIso B B' U U')

include L in
lemma isOpen_U : IsOpen U := L.base.isScSmoothOn.isOpen

include L in
lemma isOpen_U' : IsOpen U' := L.base.isScSmoothOn_inv.isOpen

/-- The inverse covers `g`: `P ∘ Ψ = g ∘ P'` on `U'`. -/
lemma covers_inv (y' : Y') (hy' : P' y' ∈ U') : P (L.Ψ y') = L.g (P' y') := by
  have h1 : L.Ψ y' ∈ P ⁻¹' U := L.zero.mapsTo_inv hy'
  rw [← L.zero.right_inv y' hy', L.covers _ h1, L.base.left_inv _ h1, L.zero.right_inv y' hy']

/-- `Ψ[1]` lifts `Ψ`. -/
lemma oneVal_Ψ₁ (w' : B'.One) (hw' : P' (B'.oneVal w') ∈ U') :
    B.oneVal (L.Ψ₁ w') = L.Ψ (B'.oneVal w') := by
  have h1 : L.Ψ₁ w' ∈ (P ∘ B.oneVal) ⁻¹' U := L.one.mapsTo_inv hw'
  have h2 := L.oneVal_Φ₁ (L.Ψ₁ w') h1
  rw [L.one.right_inv w' hw'] at h2
  rw [h2, L.zero.left_inv _ h1]

/-- The inverse is linear on the fibres. -/
lemma fiber_linear_inv (x' : X') (x : X) (hx' : x' ∈ U') (hx : L.g x' = x) :
    IsLinearMap ℝ (fiberMapOf P' P L.Ψ (x := x') (x' := x) fun v =>
      ((L.covers_inv v (by rw [show P' v = x' from v.2]; exact hx')).trans
        (by rw [show P' v = x' from v.2]; exact hx))) := by
  subst hx
  have hgx : L.g x' ∈ U := L.base.mapsTo_inv hx'
  refine IsLinearMap.of_inverse (L.fiber_linear (L.g x') x' hgx (L.base.right_inv x' hx'))
    (fun v => Subtype.ext ?_) (fun v => Subtype.ext ?_)
  · exact L.zero.left_inv _ (by rw [mem_preimage, show P v = L.g x' from v.2]; exact hgx)
  · exact L.zero.right_inv _ (by rw [mem_preimage, show P' v = x' from v.2]; exact hx')

/-- **The inverse local strong bundle isomorphism** `Y'|U' → Y|U`. -/
def symm : LocalIso B' B U' U where
  ϕ := L.g
  g := L.ϕ
  Φ := L.Ψ
  Ψ := L.Φ
  Φ₁ := L.Ψ₁
  Ψ₁ := L.Φ₁
  base := L.base.symm
  zero := L.zero.symm
  one := L.one.symm
  covers := L.covers_inv
  oneVal_Φ₁ := L.oneVal_Ψ₁
  fiber_linear := L.fiber_linear_inv

/-- `Φ` maps `Y_{0,1}` over `U` into `Y'_{0,1}`. -/
lemma mem_oneSet_Φ {y : Y} (hy : P y ∈ U) (h1 : y ∈ B.oneSet) : L.Φ y ∈ B'.oneSet := by
  have := L.oneVal_Φ₁ (B.oneMk y h1) hy
  rw [B.oneVal_oneMk] at this
  rw [← this]; exact B'.oneVal_mem _

/-- `Ψ` maps `Y'_{0,1}` over `U'` into `Y_{0,1}`. -/
lemma mem_oneSet_Ψ {y' : Y'} (hy' : P' y' ∈ U') (h1 : y' ∈ B'.oneSet) : L.Ψ y' ∈ B.oneSet :=
  L.symm.mem_oneSet_Φ hy' h1

end LocalIso

variable (B : StrongBundle PX P)

/-- **The identity** as a local strong bundle isomorphism `Y|univ → Y|univ`. -/
def LocalIso.refl : LocalIso B B univ univ where
  ϕ := id
  g := id
  Φ := id
  Ψ := id
  Φ₁ := id
  Ψ₁ := id
  base := ⟨MPolyfold.isScSmoothMap_id, MPolyfold.isScSmoothMap_id, mapsTo_univ _ _,
    mapsTo_univ _ _, fun _ _ => rfl, fun _ _ => rfl⟩
  zero := by
    rw [preimage_univ]
    exact ⟨MPolyfold.isScSmoothMap_id, MPolyfold.isScSmoothMap_id, mapsTo_univ _ _,
      mapsTo_univ _ _, fun _ _ => rfl, fun _ _ => rfl⟩
  one := by
    rw [preimage_univ]
    exact ⟨MPolyfold.isScSmoothMap_id, MPolyfold.isScSmoothMap_id, mapsTo_univ _ _,
      mapsTo_univ _ _, fun _ _ => rfl, fun _ _ => rfl⟩
  covers _ _ := rfl
  oneVal_Φ₁ _ _ := rfl
  fiber_linear x x' _ hx' := by
    subst hx'
    exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-! ### The transported strong bundle chart `Ψ' ∘ Φ` -/

namespace LocalIso

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {U : Set X} {U' : Set X'}
  (L : LocalIso B B' U U') (c' : StrongBundleChart PX' P') (hsub : c'.φ.source ⊆ U')

omit [T2Space Y'] [ParacompactSpace Y'] in
include hsub in
lemma mem_U'_of_mem_source {y' : Y'} (hy' : y' ∈ c'.toPartialEquiv.source) : P' y' ∈ U' :=
  hsub (c'.mem_base_of_mem_source hy')

lemma mem_source_Φ {y : Y} (hy : y ∈ P ⁻¹' (U ∩ L.ϕ ⁻¹' c'.φ.source)) :
    L.Φ y ∈ c'.toPartialEquiv.source := by
  rw [c'.source_eq, mem_preimage, L.covers y hy.1]; exact hy.2

include hsub in
lemma mem_source_Ψ {y' : Y'} (hy' : y' ∈ c'.toPartialEquiv.source) :
    L.Ψ y' ∈ P ⁻¹' (U ∩ L.ϕ ⁻¹' c'.φ.source) := by
  have h1 : P' y' ∈ U' := mem_U'_of_mem_source c' hsub hy'
  have h2 : P (L.Ψ y') = L.g (P' y') := L.covers_inv y' h1
  refine ⟨?_, ?_⟩
  · show P (L.Ψ y') ∈ U
    rw [h2]; exact L.base.mapsTo_inv h1
  · show L.ϕ (P (L.Ψ y')) ∈ c'.φ.source
    rw [h2, L.base.right_inv _ h1]
    exact c'.mem_base_of_mem_source hy'

/-- **The strong bundle chart `Ψ' ∘ Φ` of `P`** obtained from a strong bundle chart `Ψ'` of `P'`
whose base domain lies in `U'`, through the local strong bundle isomorphism `Φ : Y|U → Y'|U'`:
the base chart is `φ' ∘ ϕ` (`MPolyfold.transportChart`), and the model `(K, U ◁ F, R)` is that
of `Ψ'`. -/
def transportChart : StrongBundleChart PX P where
  φ := MPolyfold.transportChart L.base c'.φ
  isChart := MPolyfold.transportChart_isChart L.base c'.isChart
  F := c'.F
  U := c'.U
  R := c'.R
  relOpen := c'.relOpen
  isRetraction := c'.isRetraction
  base_retract := c'.base_retract.trans (by
    change c'.φ.model.O = c'.φ '' (U' ∩ c'.φ.source)
    rw [inter_eq_right.2 hsub, c'.φ.image_source])
  toPartialEquiv :=
    { toFun := fun y => c' (L.Φ y)
      invFun := fun k => L.Ψ (c'.toPartialEquiv.symm k)
      source := P ⁻¹' (U ∩ L.ϕ ⁻¹' c'.φ.source)
      target := c'.R '' (c'.U ×ˢ univ)
      map_source' := fun y hy => by
        have := c'.toPartialEquiv.map_source (L.mem_source_Φ c' hy)
        rwa [c'.target_eq] at this
      map_target' := fun k hk =>
        L.mem_source_Ψ c' hsub (c'.toPartialEquiv.map_target (c'.target_eq ▸ hk))
      left_inv' := fun y hy => by
        rw [c'.toPartialEquiv.left_inv (L.mem_source_Φ c' hy)]
        exact L.zero.left_inv y hy.1
      right_inv' := fun k hk => by
        have hk' : k ∈ c'.toPartialEquiv.target := c'.target_eq ▸ hk
        have hs := c'.toPartialEquiv.map_target hk'
        change c' (L.Φ (L.Ψ (c'.toPartialEquiv.symm k))) = k
        rw [L.zero.right_inv _ (mem_U'_of_mem_source c' hsub hs), c'.toPartialEquiv.right_inv hk'] }
  source_eq := rfl
  target_eq := rfl
  continuousOn_toFun :=
    c'.continuousOn_toFun.comp (L.zero.isScSmoothOn.continuousOn.mono fun y hy => hy.1)
      fun y hy => L.mem_source_Φ c' hy
  continuousOn_invFun := by
    have h1 : ContinuousOn c'.toPartialEquiv.symm (c'.R '' (c'.U ×ˢ univ)) := by
      have := c'.continuousOn_invFun; rwa [c'.target_eq] at this
    refine L.zero.isScSmoothOn_inv.continuousOn.comp h1 fun k hk => ?_
    exact mem_U'_of_mem_source c' hsub (c'.toPartialEquiv.map_target (c'.target_eq ▸ hk))
  covers y hy := by
    change (c' (L.Φ y)).1 = c'.φ (L.ϕ (P y))
    rw [c'.covers _ (L.mem_source_Φ c' hy), L.covers y hy.1]
  fiber_linear x hx := by
    have h1 := c'.fiber_linear (L.ϕ x) hx.2
    have h2 := L.fiber_linear x (L.ϕ x) hx.1 rfl
    exact ((h1.mk' _).comp (h2.mk' _)).isLinear

lemma transportChart_apply (y : Y) : L.transportChart c' hsub y = c' (L.Φ y) := rfl

lemma transportChart_symm_apply (k : c'.φ.model.E 0 × c'.F 0) :
    (L.transportChart c' hsub).toPartialEquiv.symm k = L.Ψ (c'.toPartialEquiv.symm k) := rfl

lemma transportChart_φ_apply (x : X) : (L.transportChart c' hsub).φ x = c'.φ (L.ϕ x) := rfl

lemma transportChart_φ_symm_apply (z : c'.φ.model.E 0) :
    (L.transportChart c' hsub).φ.symm z = L.g (c'.φ.symm z) := rfl

lemma transportChart_source :
    (L.transportChart c' hsub).toPartialEquiv.source = P ⁻¹' (U ∩ L.ϕ ⁻¹' c'.φ.source) := rfl

lemma transportChart_φ_source :
    (L.transportChart c' hsub).φ.source = U ∩ L.ϕ ⁻¹' c'.φ.source := rfl

lemma transportChart_K : (L.transportChart c' hsub).K = c'.K := rfl

lemma transportChart_U : (L.transportChart c' hsub).U = c'.U := rfl

lemma transportChart_model_O : (L.transportChart c' hsub).φ.model.O = c'.φ.model.O := by
  change c'.φ '' (U' ∩ c'.φ.source) = c'.φ.model.O
  rw [inter_eq_right.2 hsub, c'.φ.image_source]

lemma mem_transportChart_source {y : Y} :
    y ∈ (L.transportChart c' hsub).toPartialEquiv.source ↔
      P y ∈ U ∧ L.Φ y ∈ c'.toPartialEquiv.source := by
  rw [transportChart_source, c'.source_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, show P' (L.Φ y) ∈ c'.φ.source by rw [L.covers y h1]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, show L.ϕ (P y) ∈ c'.φ.source by rw [← L.covers y h1]; exact h2⟩

/-- `Φ(P⁻¹(dom)) = P'⁻¹(dom')` for the transported chart. -/
lemma image_Φ_source :
    L.Φ '' (L.transportChart c' hsub).toPartialEquiv.source = c'.toPartialEquiv.source := by
  ext y'
  constructor
  · rintro ⟨y, hy, rfl⟩; exact L.mem_source_Φ c' hy
  · intro hy'
    refine ⟨L.Ψ y', L.mem_source_Ψ c' hsub hy', L.zero.right_inv y' ?_⟩
    exact mem_U'_of_mem_source c' hsub hy'

/-- **The principal part of `Ψ ∘ f' ∘ ϕ` in `Ψ' ∘ Φ` is the principal part of `f'` in `Ψ'`**, on
the retract `O`. -/
lemma principal_transportChart {f : X → Y} {f' : X' → Y'} (hf : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U)
    (hf' : IsSection P' f') {z : c'.φ.model.E 0} (hz : z ∈ c'.φ.model.O) :
    (L.transportChart c' hsub).principal f z = c'.principal f' z := by
  have hw : c'.φ.symm z ∈ c'.φ.source := c'.φ.symm_mapsTo hz
  have hwU' : c'.φ.symm z ∈ U' := hsub hw
  have hgU : L.g (c'.φ.symm z) ∈ U := L.base.mapsTo_inv hwU'
  change (c' (L.Φ (f (L.g (c'.φ.symm z))))).2 = (c' (f' (c'.φ.symm z))).2
  rw [hf hgU]
  change (c' (L.Φ (L.Ψ (f' (L.ϕ (L.g (c'.φ.symm z))))))).2 = _
  rw [L.base.right_inv _ hwU', L.zero.right_inv _ (show P' (f' _) ∈ U' by rw [hf']; exact hwU')]

/-! ### The transported chart is a chart of `P` -/

lemma _root_.Polyfold.ScBanach.lvlSet_empty (E : ScBanach) (m : ℕ) : E.lvlSet ∅ m = ∅ :=
  preimage_empty

lemma _root_.Polyfold.ScBanach.tangentSet_empty (E : ScBanach) : E.tangentSet ∅ = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro p hp
  have := (ScBanach.mem_tangentSet E).1 hp
  rw [ScBanach.lvlSet_empty] at this
  exact this

theorem _root_.Polyfold.isSc0_empty {E F : ScBanach} (f : E 0 → F 0) : IsSc0 E F ∅ f where
  mem_range m x hx := by rw [ScBanach.lvlSet_empty] at hx; exact hx.elim
  continuousOn m := by rw [ScBanach.lvlSet_empty]; exact continuousOn_empty _

theorem _root_.Polyfold.isSck_empty : ∀ (k : ℕ) {E F : ScBanach} (f : E 0 → F 0), IsSck k E F ∅ f
  | 0, _, _, f => isSc0_empty f
  | k + 1, E, _, f =>
    ⟨⟨fun _ => 0, isSc0_empty f, fun x hx => by rw [ScBanach.lvlSet_empty] at hx; exact hx.elim,
      by rw [ScBanach.tangentSet_empty]; exact isSc0_empty _⟩,
      by rw [ScBanach.tangentSet_empty]; exact isSck_empty k _⟩

/-- Every map is sc-smooth on the empty set. -/
theorem _root_.Polyfold.isScSmooth_empty {E F : ScBanach} (f : E 0 → F 0) : IsScSmooth ∅ f :=
  fun k => isSck_empty k f

/-- A map on the empty retract is sc-smooth. -/
theorem _root_.Polyfold.isScSmoothRetractMap_of_empty {E E' : ScBanach} {C : Set (E 0)}
    {C' O' : Set (E' 0)} {f : E 0 → E' 0} : IsScSmoothRetractMap E C ∅ E' C' O' f where
  mapsTo := fun _ h => h.elim
  comp_isScSmooth R hR := by
    have hU : R.U = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x hx
      have : R x ∈ R.retract := ⟨x, hx, rfl⟩
      rw [hR] at this; exact this
    rw [hU]
    exact isScSmooth_empty _

/-- `K[1]` of the empty set is empty. -/
lemma _root_.Polyfold.strongShiftOne_empty {E F : ScBanach} :
    strongShiftOne (E := E) (F := F) ∅ = ∅ := by
  rw [eq_empty_iff_forall_notMem]; intro p hp; exact hp

/-- **The transported chart `Ψ' ∘ Φ` is a strong bundle chart of `P`**: its transition maps with
the charts `Φ_c` of the atlas of `P` are `Φ_c ∘ Ψ ∘ Ψ'⁻¹` and `Ψ' ∘ Φ ∘ Φ_c⁻¹`, local
representatives of the sc-smooth maps `Ψ`, `Φ` on `[0]` and of `Ψ[1]`, `Φ[1]` on `[1]`, and
`Φ`, `Ψ` preserve `Y_{0,1}`. -/
theorem isChart_transportChart (hc' : B'.IsChart c') : B.IsChart (L.transportChart c' hsub) := by
  intro c hc
  have hcB : B.IsChart c := B.isChart_of_mem hc
  set c'' := L.transportChart c' hsub with hc''
  have hc''src : c''.toPartialEquiv.source ⊆ P ⁻¹' U := fun y hy => hy.1
  have hc'src : c'.toPartialEquiv.source ⊆ P' ⁻¹' U' := fun _ hy' =>
    mem_U'_of_mem_source c' hsub hy'
  -- the overlaps, upstairs and downstairs
  have hov2 : c.overlap c'' = c '' (c.toPartialEquiv.source ∩ c''.toPartialEquiv.source) := rfl
  rw [inter_comm] at hov2
  set S := c''.toPartialEquiv.source ∩ c.toPartialEquiv.source with hS
  set S' := c'.toPartialEquiv.source ∩ L.Ψ ⁻¹' c.toPartialEquiv.source with hS'
  have hSo : IsOpen S := (c''.isOpen_source B.continuous).inter (c.isOpen_source B.continuous)
  have hS'o : IsOpen S' :=
    (L.zero.isScSmoothOn_inv.continuousOn.mono hc'src).isOpen_inter_preimage
      (c'.isOpen_source B'.continuous) (c.isOpen_source B.continuous)
  have hΦS : L.Φ '' S = S' := by
    ext y'
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      refine ⟨L.mem_source_Φ c' hy1, ?_⟩
      show L.Ψ (L.Φ y) ∈ c.toPartialEquiv.source
      rw [L.zero.left_inv y hy1.1]; exact hy2
    · rintro ⟨hy1, hy2⟩
      exact ⟨L.Ψ y', ⟨L.mem_source_Ψ c' hsub hy1, hy2⟩, L.zero.right_inv y' (hc'src hy1)⟩
  have hΨS' : ∀ y' ∈ S', L.Ψ y' ∈ S := fun y' hy' => ⟨L.mem_source_Ψ c' hsub hy'.1, hy'.2⟩
  have hov1 : c''.overlap c = c' '' S' := by
    show (fun y => c' (L.Φ y)) '' S = c' '' S'
    rw [← hΦS, image_image]
  -- level `[0]`
  have h1 := L.zero.isScSmoothOn_inv.smooth (c'.toMChart B'.continuous) (c.toMChart B.continuous)
    hc'.toMChart hcB.toMChart S' hS'o
    (fun y' hy' => ⟨hc'src hy'.1, hy'.1⟩) (fun y' hy' => hy'.2)
  have hm1 : MapsTo ((c.toMChart B.continuous) ∘ L.Ψ ∘ (c'.toMChart B'.continuous).symm)
      ((c'.toMChart B'.continuous) '' S') (c.overlap c'') := by
    rintro _ ⟨y', hy', rfl⟩
    change c (L.Ψ (c'.toPartialEquiv.symm (c' y'))) ∈ c.overlap c''
    rw [c'.toPartialEquiv.left_inv hy'.1]
    exact ⟨L.Ψ y', ⟨(hΨS' y' hy').2, (hΨS' y' hy').1⟩, rfl⟩
  have h2 := L.zero.isScSmoothOn.smooth (c.toMChart B.continuous) (c'.toMChart B'.continuous)
    hcB.toMChart hc'.toMChart S hSo
    (fun y hy => ⟨hc''src hy.1, hy.2⟩) (fun y hy => L.mem_source_Φ c' hy.1)
  have hm2 : MapsTo ((c'.toMChart B'.continuous) ∘ L.Φ ∘ (c.toMChart B.continuous).symm)
      ((c.toMChart B.continuous) '' S) (c''.overlap c) := by
    rintro _ ⟨y, hy, rfl⟩
    change c' (L.Φ (c.toPartialEquiv.symm (c y))) ∈ c''.overlap c
    rw [c.toPartialEquiv.left_inv hy.2]
    exact ⟨y, hy, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hov1]; exact h1.mono_target hm1
  · rw [hov2]; exact h2.mono_target hm2
  -- level `[1]`
  · rcases S.eq_empty_or_nonempty with hSe | ⟨y₀Y, hy₀⟩
    · have hov1e : c''.overlap c = ∅ := by rw [hov1, ← hΦS, hSe, image_empty, image_empty]; rfl
      rw [hov1e, strongShiftOne_empty]
      exact isScSmoothRetractMap_of_empty
    set y₀ : B.One := B.oneMk (fiberZero P (P y₀Y)) (B.fiberZero_mem_oneSet _)
    set y₀' : B'.One := B'.oneMk (fiberZero P' (L.ϕ (P y₀Y))) (B'.fiberZero_mem_oneSet _)
    set V₁ : Set B'.One := B'.oneVal ⁻¹' S' with hV₁
    have hV₁o : IsOpen V₁ := hS'o.preimage B'.continuous_oneVal
    have hV₁U' : ∀ w ∈ V₁, P' (B'.oneVal w) ∈ U' := fun w hw => hc'src hw.1
    have h3 := L.one.isScSmoothOn_inv.smooth (oneChartOf hc' y₀') (oneChartOf hcB y₀)
      (isChart_oneChartOf hc' y₀')
      (isChart_oneChartOf hcB y₀) V₁ hV₁o (fun w hw => ⟨hV₁U' w hw, hw.1⟩) (fun w hw => by
        show B.oneVal (L.Ψ₁ w) ∈ c.toPartialEquiv.source
        rw [L.oneVal_Ψ₁ w (hV₁U' w hw)]; exact hw.2)
    have hV₁img : (oneChartOf hc' y₀') '' V₁ = strongShiftOne (c''.overlap c) := by
      rw [hov1]
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        have h2 : (c' (B'.oneVal w)).2 ∈ range (c'.F.toBase 1) :=
          (mem_oneSet_iff_of_isChart hc' hw.1).1 (B'.oneVal_mem w)
        change ((c'.liftOne (B'.oneVal w)).1, c'.F.toBase 1 (c'.liftOne (B'.oneVal w)).2) ∈
          c' '' S'
        rw [c'.toBase_liftOne h2]
        exact ⟨_, hw, rfl⟩
      · rintro ⟨y', hy', hyz⟩
        have h1' : y' ∈ B'.oneSet :=
          (mem_oneSet_iff_of_isChart hc' hy'.1).2 (by rw [hyz]; exact ⟨z.2, rfl⟩)
        refine ⟨B'.oneMk y' h1', hy', ?_⟩
        change c'.liftOne y' = z
        unfold StrongBundleChart.liftOne
        rw [hyz]
        exact Prod.ext rfl (c'.F.toBase_injective 1 (Function.invFun_eq ⟨z.2, rfl⟩))
    have hm3 : MapsTo ((oneChartOf hcB y₀) ∘ L.Ψ₁ ∘ (oneChartOf hc' y₀').symm)
        ((oneChartOf hc' y₀') '' V₁) (strongShiftOne (c.overlap c'')) := by
      rintro _ ⟨w, hw, rfl⟩
      change (oneChartOf hcB y₀) (L.Ψ₁ ((oneChartOf hc' y₀').symm ((oneChartOf hc' y₀') w))) ∈ _
      rw [(oneChartOf hc' y₀').symm_apply_apply (show w ∈ (oneChartOf hc' y₀').source from hw.1)]
      change c.liftOne (B.oneVal (L.Ψ₁ w)) ∈ _
      have hmem := B.oneVal_mem (L.Ψ₁ w)
      rw [L.oneVal_Ψ₁ w (hV₁U' w hw)] at hmem ⊢
      exact liftOne_mem_overlap hcB hw.2 (L.mem_source_Ψ c' hsub hw.1) hmem
    rw [← hV₁img]
    refine (h3.mono_target hm3).congr fun z hz => ?_
    rw [hV₁img] at hz
    have hzK : z ∈ strongShiftOne c'.K := strongShiftOne_mono (c''.overlap_subset_K c) hz
    have hzt : (z.1, c'.F.toBase 1 z.2) ∈ c'.toPartialEquiv.target := by
      rw [c'.target_eq]; exact hzK
    have hw' : B'.oneVal ((oneChartOf hc' y₀').symm z) ∈ c'.toPartialEquiv.source := by
      rw [oneChartOf_symm_apply hc' y₀' hzK]; exact c'.toPartialEquiv.map_target hzt
    change c.liftOne (B.oneVal (L.Ψ₁ ((oneChartOf hc' y₀').symm z))) =
      c.liftOne (L.Ψ (c'.toPartialEquiv.symm _))
    rw [L.oneVal_Ψ₁ _ (hc'src hw'), oneChartOf_symm_apply hc' y₀' hzK]
    rfl
  · rcases S.eq_empty_or_nonempty with hSe | ⟨y₀Y, hy₀⟩
    · have hov2e : c.overlap c'' = ∅ := by rw [hov2, hSe, image_empty]
      rw [hov2e, strongShiftOne_empty]
      exact isScSmoothRetractMap_of_empty
    set y₀ : B.One := B.oneMk (fiberZero P (P y₀Y)) (B.fiberZero_mem_oneSet _)
    set y₀' : B'.One := B'.oneMk (fiberZero P' (L.ϕ (P y₀Y))) (B'.fiberZero_mem_oneSet _)
    set V₂ : Set B.One := B.oneVal ⁻¹' S with hV₂
    have hV₂o : IsOpen V₂ := hSo.preimage B.continuous_oneVal
    have hV₂U : ∀ w ∈ V₂, P (B.oneVal w) ∈ U := fun w hw => hc''src hw.1
    have h4 := L.one.isScSmoothOn.smooth (oneChartOf hcB y₀) (oneChartOf hc' y₀')
      (isChart_oneChartOf hcB y₀)
      (isChart_oneChartOf hc' y₀') V₂ hV₂o (fun w hw => ⟨hV₂U w hw, hw.2⟩) (fun w hw => by
        show B'.oneVal (L.Φ₁ w) ∈ c'.toPartialEquiv.source
        rw [L.oneVal_Φ₁ w (hV₂U w hw)]; exact L.mem_source_Φ c' hw.1)
    have hV₂img : (oneChartOf hcB y₀) '' V₂ = strongShiftOne (c.overlap c'') := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact liftOne_mem_overlap hcB hw.2 hw.1 (B.oneVal_mem w)
      · rintro ⟨y, hy, hyz⟩
        have h1' : y ∈ B.oneSet :=
          (mem_oneSet_iff_of_isChart hcB hy.1).2 (by rw [hyz]; exact ⟨z.2, rfl⟩)
        refine ⟨B.oneMk y h1', ⟨hy.2, hy.1⟩, ?_⟩
        change c.liftOne y = z
        unfold StrongBundleChart.liftOne
        rw [hyz]
        exact Prod.ext rfl (c.F.toBase_injective 1 (Function.invFun_eq ⟨z.2, rfl⟩))
    have hm4 : MapsTo ((oneChartOf hc' y₀') ∘ L.Φ₁ ∘ (oneChartOf hcB y₀).symm)
        ((oneChartOf hcB y₀) '' V₂) (strongShiftOne (c''.overlap c)) := by
      rintro _ ⟨w, hw, rfl⟩
      change (oneChartOf hc' y₀') (L.Φ₁ ((oneChartOf hcB y₀).symm ((oneChartOf hcB y₀) w))) ∈ _
      rw [(oneChartOf hcB y₀).symm_apply_apply (show w ∈ (oneChartOf hcB y₀).source from hw.2)]
      change c'.liftOne (B'.oneVal (L.Φ₁ w)) ∈ _
      rw [L.oneVal_Φ₁ w (hV₂U w hw)]
      have h2 : (c'' (B.oneVal w)).2 ∈ range (c''.F.toBase 1) :=
        (mem_oneSet_iff_of_isChart hc' (L.mem_source_Φ c' hw.1)).1
          (L.mem_oneSet_Φ (hV₂U w hw) (B.oneVal_mem w))
      change ((c''.liftOne (B.oneVal w)).1, c''.F.toBase 1 (c''.liftOne (B.oneVal w)).2) ∈
        c''.overlap c
      rw [c''.toBase_liftOne h2]
      exact ⟨_, hw, rfl⟩
    rw [← hV₂img]
    refine (h4.mono_target hm4).congr fun z hz => ?_
    rw [hV₂img] at hz
    have hzK : z ∈ strongShiftOne c.K := strongShiftOne_mono (c.overlap_subset_K c'') hz
    obtain ⟨y, hy, hyz⟩ := hz
    have hsymm : c.toPartialEquiv.symm (z.1, c.F.toBase 1 z.2) = y := by
      rw [← hyz]; exact c.toPartialEquiv.left_inv hy.1
    change c'.liftOne (B'.oneVal (L.Φ₁ ((oneChartOf hcB y₀).symm z))) =
      c'.liftOne (L.Φ (c.toPartialEquiv.symm _))
    rw [L.oneVal_Φ₁ _ (by rw [oneChartOf_symm_apply hcB y₀ hzK, hsymm]; exact hy.2.1),
      oneChartOf_symm_apply hcB y₀ hzK]
  -- `Y_{0,1}` is preserved
  · rintro _ ⟨y, hy, rfl⟩ h2
    have h3 : L.Φ y ∈ B'.oneSet :=
      (mem_oneSet_iff_of_isChart hc' (L.mem_source_Φ c' hy.1)).2 h2
    have h4 : y ∈ B.oneSet := by
      have := L.mem_oneSet_Ψ (by rw [L.covers y hy.1.1]; exact L.base.mapsTo hy.1.1) h3
      rwa [L.zero.left_inv y hy.1.1] at this
    rw [c''.transition_apply c hy.1]
    exact (B.mem_oneSet_iff hc hy.2).1 h4
  · rintro _ ⟨y, hy, rfl⟩ h2
    have h3 : y ∈ B.oneSet := (B.mem_oneSet_iff hc hy.1).2 h2
    rw [c.transition_apply c'' hy.1]
    exact (mem_oneSet_iff_of_isChart hc' (L.mem_source_Φ c' hy.2)).1
      (L.mem_oneSet_Φ hy.2.1 h3)

/-- **Tameness is preserved**: the transported chart has the base retraction of `Ψ'`. -/
theorem isTameChart_transportChart (hc' : B'.IsTameChart c') :
    B.IsTameChart (L.transportChart c' hsub) :=
  ⟨L.isChart_transportChart c' hsub hc'.1, hc'.2⟩

/-! ### The key lemma: sc-Fredholm germs pull back -/

variable {f : X → Y} {f' : X' → Y'}

/-- A point `x ∈ U` is on level `m` iff `ϕ(x)` is. -/
lemma mem_levelSet_iff {x : X} (hx : x ∈ U) (m : ℕ) :
    x ∈ PX.levelSet m ↔ L.ϕ x ∈ PX'.levelSet m := by
  constructor
  · intro h; exact L.base.isScSmoothOn.mapsTo_levelSet m ⟨hx, h⟩
  · intro h
    have := L.base.isScSmoothOn_inv.mapsTo_levelSet m ⟨L.base.mapsTo hx, h⟩
    rwa [L.base.left_inv x hx] at this

/-- A point `x ∈ U` is smooth iff `ϕ(x)` is. -/
lemma mem_smoothSet_iff {x : X} (hx : x ∈ U) : x ∈ PX.smoothSet ↔ L.ϕ x ∈ PX'.smoothSet := by
  simp only [MPolyfold.smoothSet, mem_iInter]
  exact forall_congr' fun m => L.mem_levelSet_iff hx m

/-- **The key lemma (G.121, Part I half)**: if `f = Ψ ∘ f' ∘ ϕ` on `U` and `f'` is an
sc-Fredholm germ at `ϕ(x)` (Definition 3.1.16), `x ∈ U`, then `f` is an sc-Fredholm germ at `x`,
with the same filling `g`, sc⁺-germ `s` and conjugation, read in the transported chart
`Ψ' ∘ Φ` of the chart `Ψ'` at `ϕ(x)` (restricted to `U'`). -/
theorem isScFredholmGerm (hf : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hf' : IsSection P' f') {x : X}
    (hx : x ∈ U) (h : B'.IsScFredholmGerm f' (L.ϕ x)) : B.IsScFredholmGerm f x := by
  obtain ⟨hs, c', hc', hxc', hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩ := h
  have hU' := L.isOpen_U'
  have hsub : (c'.restrictInter hU').φ.source ⊆ U' := c'.restrictInter_source_subset hU'
  have hxU' : L.ϕ x ∈ U' := L.base.mapsTo hx
  have h0₁ := c'.zero_mem_restrictInter_U hU' hxc' hφ0 hxU'
  obtain ⟨hfill₁, hsm₁, hconj₁⟩ :=
    c'.germData_restrictInter hU' hxc' hφ0 hxU' h0 hfill hsm hconj
  refine ⟨(L.mem_smoothSet_iff hx).2 hs, L.transportChart (c'.restrictInter hU') hsub,
    L.isChart_transportChart _ hsub (hc'.restrictInter hU'),
    ⟨hx, c'.mem_restrictInter_source hU' hxc' hxU'⟩, hφ0, h0₁, g, s, ?_, hsm₁, hs0, hconj₁⟩
  refine { hfill₁ with eq_on := ?_ }
  filter_upwards [hfill₁.eq_on] with z hz hzO
  rw [← hz hzO]
  exact L.principal_transportChart _ hsub hf hf' ((c'.restrictInter hU').r_image ▸ hzO)

/-- **The key lemma, tame form** (Definition 3.6.4): the transported chart of a tame chart is
tame. -/
theorem isScFredholmGermTame (hf : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hf' : IsSection P' f') {x : X}
    (hx : x ∈ U) (h : B'.IsScFredholmGermTame f' (L.ϕ x)) : B.IsScFredholmGermTame f x := by
  obtain ⟨hs, c', hc', hxc', hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩ := h
  have hU' := L.isOpen_U'
  have hsub : (c'.restrictInter hU').φ.source ⊆ U' := c'.restrictInter_source_subset hU'
  have hxU' : L.ϕ x ∈ U' := L.base.mapsTo hx
  have h0₁ := c'.zero_mem_restrictInter_U hU' hxc' hφ0 hxU'
  obtain ⟨hfill₁, hsm₁, hconj₁⟩ :=
    c'.germData_restrictInter hU' hxc' hφ0 hxU' h0 hfill hsm hconj
  refine ⟨(L.mem_smoothSet_iff hx).2 hs, L.transportChart (c'.restrictInter hU') hsub,
    L.isTameChart_transportChart _ hsub (hc'.restrictInter hU'),
    ⟨hx, c'.mem_restrictInter_source hU' hxc' hxU'⟩, hφ0, h0₁, g, s, ?_, hsm₁, hs0, hconj₁⟩
  refine { hfill₁ with eq_on := ?_ }
  filter_upwards [hfill₁.eq_on] with z hz hzO
  rw [← hz hzO]
  exact L.principal_transportChart _ hsub hf hf' ((c'.restrictInter hU').r_image ▸ hzO)

/-- **The regularizing property transfers point-wise**: `Φ[1]` maps `Y_{m,m+1}` into
`Y'_{m,m+1}`, and `ϕ` preserves the levels; so if `f'` is regularizing at `ϕ(x)` (for the level
`m`), `f = Ψ ∘ f' ∘ ϕ` is regularizing at `x`. -/
theorem regularizing_at (hf : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hfs : IsSection P f)
    (hf' : IsSection P' f') {x : X} (hx : x ∈ U) (m : ℕ)
    (hreg : L.ϕ x ∈ PX'.levelSet m → f' (L.ϕ x) ∈ B'.doubleLevel m (m + 1) →
      L.ϕ x ∈ PX'.levelSet (m + 1))
    (hxm : x ∈ PX.levelSet m) (hfx : f x ∈ B.doubleLevel m (m + 1)) :
    x ∈ PX.levelSet (m + 1) := by
  rw [L.mem_levelSet_iff hx] at hxm ⊢
  refine hreg hxm ?_
  have hfx' : f' (L.ϕ x) = L.Φ (f x) := by
    rw [hf hx]
    exact (L.zero.right_inv _ (show P' (f' (L.ϕ x)) ∈ U' by rw [hf']; exact L.base.mapsTo hx)).symm
  rw [hfx']
  have h1 : f x ∈ B.oneSet := fun c hc hyc =>
    range_toBase_mono c.F (Nat.le_add_left 1 m) (hfx c hc hyc).2
  have h2 : B.oneMk (f x) h1 ∈ B.toMPolyfold1.levelSet m :=
    (B.mem_levelSet1_iff_mem_doubleLevel _ m).2 hfx
  have hPx : P (B.oneVal (B.oneMk (f x) h1)) ∈ U := by rw [B.oneVal_oneMk, hfs]; exact hx
  have h3 := L.one.isScSmoothOn.mapsTo_levelSet m ⟨hPx, h2⟩
  rw [B'.mem_levelSet1_iff_mem_doubleLevel, L.oneVal_Φ₁ _ hPx, B.oneVal_oneMk] at h3
  exact h3

end LocalIso

/-- **Definition 3.1.18 is local**: an sc-smooth section `f` of `P` which, near every point, is
`Ψ ∘ f' ∘ ϕ` for a local strong bundle isomorphism `(ϕ, Φ, Ψ) : Y|U → Y'|U'` and an sc-Fredholm
section `f'` of `P'` is an sc-Fredholm section. -/
theorem isScFredholmSection_of_forall {B : StrongBundle PX P} {B' : StrongBundle PX' P'}
    {f : X → Y} (hf : B.IsScSmoothSection f)
    (h : ∀ x : X, ∃ (U : Set X) (U' : Set X') (L : LocalIso B B' U U') (f' : X' → Y'),
      x ∈ U ∧ EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U ∧ B'.IsScFredholmSection f') :
    B.IsScFredholmSection f where
  isScSmooth := hf
  regularizing m x hxm hfx := by
    obtain ⟨U, U', L, f', hxU, heq, hf'⟩ := h x
    exact L.regularizing_at heq hf.1 hf'.isScSmooth.1 hxU m (hf'.regularizing m _) hxm hfx
  germ x hxs := by
    obtain ⟨U, U', L, f', hxU, heq, hf'⟩ := h x
    exact L.isScFredholmGerm heq hf'.isScSmooth.1 hxU
      (hf'.germ _ ((L.mem_smoothSet_iff hxU).1 hxs))

/-- **Definition 3.6.5 is local**: the tame form of `isScFredholmSection_of_forall`. -/
theorem isScFredholmSectionTame_of_forall {B : StrongBundle PX P} {B' : StrongBundle PX' P'}
    {f : X → Y} (hf : B.IsScSmoothSection f)
    (h : ∀ x : X, ∃ (U : Set X) (U' : Set X') (L : LocalIso B B' U U') (f' : X' → Y'),
      x ∈ U ∧ EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U ∧ B'.IsScFredholmSectionTame f') :
    B.IsScFredholmSectionTame f where
  toIsScFredholmSection := isScFredholmSection_of_forall hf fun x => by
    obtain ⟨U, U', L, f', hxU, heq, hf'⟩ := h x
    exact ⟨U, U', L, f', hxU, heq, hf'.toIsScFredholmSection⟩
  germTame x hxs := by
    obtain ⟨U, U', L, f', hxU, heq, hf'⟩ := h x
    exact L.isScFredholmGermTame heq hf'.isScSmooth.1 hxU
      (hf'.germTame _ ((L.mem_smoothSet_iff hxU).1 hxs))

end StrongBundle

end LocalIsoDefs

end Polyfold
