import Polyfold.Chapter10.StrongBundleWeakFibredProductPullback
import Polyfold.Chapter10.StrongBundleEquivalenceExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.5 "Localization in the Strong Bundle Case" (pp. 504–508; 2017:
pp. 364–368): the weak fibred product of strong bundles over ep-groupoids and the strong bundle
version of **Theorem 10.2.2** (2021 p. 477; 2017: Theorem 10.2, p. 343), which the text uses
without stating it (2021 p. 504: refinements and equivalence of strong bundle diagrams are
introduced "following our earlier construction", and Definition 10.5.1 calls the resulting
classes the morphisms of a category).  The tools (pull-backs along functors, transport along
natural transformations, fibrewise inverse lifts) are in
`StrongBundleWeakFibredProductPullback.lean`; the category `SEP(F⁻¹)` is in
`StrongBundleLocalizationCategory.lean`.

# The weak fibred product of strong bundles

## The construction

For a strong bundle equivalence `Φ : W → W'` covering `ϕ : X → X'` (Definition 10.4.1) and a
strong bundle functor `Ψ : W'' → W'` covering `ψ : X'' → X'`, the weak fibred product
`X ×_{X'} X''` of `ϕ` and `ψ` is an ep-groupoid with an equivalence `πZ` (Theorem 10.2.2).  We set
`W ×_{W'} W'' = πZ*W''` (`SBWeakFibredProduct.wfpSEP`, a strong bundle over `X ×_{X'} X''`), with

* `ΠZ : πZ*W'' → W''`, `((x, φ, z), w'') ↦ w''`, covering `πZ` (`projZ`), and
* `ΠX : πZ*W'' → W`, `((x, φ, z), w'') ↦ Φ_x⁻¹(μ'(φ⁻¹, Ψ(w'')))`, covering `πX` (`projX`),
  where `Φ_x : W_x → W'_{ϕ(x)}` is the fibrewise isomorphism of Proposition 10.4.4.

## What is formalized

* `SEP.pullbackAlong`, `SEP.pullbackHom`, `SEP.pullbackLiftHom`, `SEP.equivalences_pullbackHom`:
  pull-backs along functors in `SEP`; `SEP.coneHom`, `SEP.natEquiv_cone`, `SEP.coneHom_obj_eq`:
  for `π : Y → X''`, `κ : Y → X` and `τ : ψ ∘ π → ϕ ∘ κ`, the strong bundle functor
  `π*W'' → W` covering `κ` and the natural equivalence of the square.
* `SBWeakFibredProduct.theorem_10_2_2`: **`ΠZ` is a strong bundle equivalence and
  `Φ ∘ ΠX ≃ Ψ ∘ ΠZ`** (Definition 10.4.8); `theorem_10_2_2_right`: **if `Ψ` is a strong bundle
  equivalence, so is `ΠX`**; `nonempty_wfpSEP`.
* `SEP.NatEquiv.comp_right` (with `StrongBundleNatTrans.whiskerRight`), `SEP.Hom.ext_obj`,
  `IsStrongBundleFunctor.ext_obj`.
* Satisfiability: `StrongBundleWeakFibredProductExamples.theorem_10_2_2_negSEPHom`.

## Our reading

The text gives no construction of the weak fibred product of strong bundles.  We take the
pull-back of `W''` along `πZ`; the claims of Theorem 10.2.2 on degeneracy indices, tameness and
paracompact orbit spaces concern the bases and are `WeakFibredProduct.theorem_10_2_2`.  The
symmetric construction (the pull-back of `W` along `πX`) is isomorphic to ours when both `Φ` and
`Ψ` are equivalences (`swapHom`, `equivalences_swapHom`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Whiskering on the right; strong bundle functors are determined by their object maps -/

section Whisker

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

/-- Two strong bundle functors covering the same functor agree if their object maps agree
(p. 274, "from the strong bundle map we can recover the functor completely"). -/
theorem IsStrongBundleFunctor.ext_obj {ϕ : EpFunctor X X'}
    {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (hΦ : E.IsStrongBundleFunctor E' ϕ Φ)
    (hΨ : E.IsStrongBundleFunctor E' ϕ Ψ) (h : Φ.obj = Ψ.obj) : Φ = Ψ :=
  EpFunctor.ext h (funext fun q => Subtype.ext ((hΦ.mor_val q).trans (by rw [hΨ.mor_val q, h])))

@[simp] theorem transportPair_val {ψ ϕ : EpFunctor X X'}
    {Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (hΨ : E.IsStrongBundleFunctor E' ψ Ψ)
    (τ : EpNatTrans ψ ϕ) (w : W) :
    (transportPair hΨ τ w : Mor' × W') = (τ.app (P w), Ψ.obj w) := rfl

/-- `μ(ψ, v) = w` if `v = μ(ψ⁻¹, w)`. -/
theorem μ_eq_of_eq_μ_inv {ψ : Mor} {w v : W} (hv : P v = X.src ψ)
    (hw : P w = X.src (X.inv ψ)) (h : v = E.μ ⟨(X.inv ψ, w), hw⟩) : E.μ ⟨(ψ, v), hv⟩ = w := by
  subst h
  exact E.μ_μ_inv ψ w hw hv

/-- `μ(ψ⁻¹, v) = w` if `v = μ(ψ, w)`. -/
theorem μ_inv_eq_of_eq_μ {ψ : Mor} {w v : W} (hv : P v = X.src (X.inv ψ))
    (hw : P w = X.src ψ) (h : v = E.μ ⟨(ψ, w), hw⟩) : E.μ ⟨(X.inv ψ, v), hv⟩ = w := by
  subst h
  exact E.μ_inv_μ ⟨(ψ, w), hw⟩ hv

namespace StrongBundleNatTrans

variable {ϕ ψ : EpFunctor X X'} {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}

/-- Whiskering by a strong bundle functor `K` covering `κ` on the left: `K ∘ Φ → K ∘ Ψ`,
`w ↦ K(T(w))`, covering `κ ∘ τ`. -/
def whiskerRight (θ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ) (hΦ : E.IsStrongBundleFunctor E' ϕ Φ)
    {κ : EpFunctor X' X''} {K : EpFunctor E'.toEpGroupoid E''.toEpGroupoid}
    (hK : E'.IsStrongBundleFunctor E'' κ K) :
    E.StrongBundleNatTrans E'' (κ.comp ϕ) (κ.comp ψ) (K.comp Φ) (K.comp Ψ) :=
  ofEpNatTrans ((θ.toEpNatTrans hΦ).whiskerRight K) (θ.τ.whiskerRight κ) fun w => by
    change κ.mor (θ.τ.app (P w)) = (K.mor (θ.T w) : Mor'' × W'').1
    rw [hK.mor_val, θ.app_P]

end StrongBundleNatTrans

end EpStrongBundle

end Whisker

/-! ### Pull-backs along functors in `SEP`; the cone of a strong bundle equivalence -/

namespace SEP

open EpStrongBundle

variable {A A' A'' : SEP.{u}}

/-- Morphisms of `SEP` covering the same functor agree if their object maps agree. -/
theorem Hom.ext_obj {F G : A ⟶ A'} (hϕ : Hom.ϕ F = Hom.ϕ G) (h : (Hom.Φ F).obj = (Hom.Φ G).obj) :
    F = G := by
  refine Hom.ext' hϕ ?_
  have hG := Hom.isStrongBundleFunctor G
  rw [← hϕ] at hG
  exact (Hom.isStrongBundleFunctor F).ext_obj hG h

/-- Natural equivalence is compatible with composition on the right. -/
theorem NatEquiv.comp_right {F G : A ⟶ A'} (h : NatEquiv F G) (K : A' ⟶ A'') :
    NatEquiv (F ≫ K) (G ≫ K) :=
  let ⟨θ⟩ := h
  ⟨θ.whiskerRight (Hom.isStrongBundleFunctor F) (Hom.isStrongBundleFunctor K)⟩

theorem NatEquiv.of_eq {F G : A ⟶ A'} (h : F = G) : NatEquiv F G := h ▸ NatEquiv.refl F

/-- **The pull-back `π*W` of `A` along a functor `π : Y → X`**, an object of `SEP`
(`EpStrongBundle.pullbackAlong`). -/
def pullbackAlong (A : SEP.{u}) (Y : EP.{u}) (π : EpFunctor Y.X A.X) : SEP.{u} :=
  haveI := A.B.paracompactSpace_pullback Y.X.PObj π.obj
  haveI := (A.B.pullback π.isScSmoothMap_obj).paracompactSpace_pullback Y.X.PMor Y.X.src
  { Obj := Y.Obj, Mor := Y.Mor, X := Y.X, W := pullbackSpace A.P π.obj
    P := pullbackProj A.P π.obj, B := A.B.pullback π.isScSmoothMap_obj
    E := A.E.pullbackAlong π }

/-- The projection `π*W → W`, a morphism of `SEP` covering `π`. -/
def pullbackHom (A : SEP.{u}) (Y : EP.{u}) (π : EpFunctor Y.X A.X) : A.pullbackAlong Y π ⟶ A :=
  haveI := A.B.paracompactSpace_pullback Y.X.PObj π.obj
  haveI := (A.B.pullback π.isScSmoothMap_obj).paracompactSpace_pullback Y.X.PMor Y.X.src
  ⟨π, A.E.pullbackProjFunctor π, A.E.isStrongBundleFunctor_pullbackProjFunctor π⟩

theorem pullbackHom_ϕ (A : SEP.{u}) (Y : EP.{u}) (π : EpFunctor Y.X A.X) :
    Hom.ϕ (A.pullbackHom Y π) = π := rfl

/-- **The projection along an equivalence is a strong bundle equivalence**
(`isStrongBundleEquivalence_pullbackProjFunctor`). -/
theorem equivalences_pullbackHom (A : SEP.{u}) (Y : EP.{u}) {π : EpFunctor Y.X A.X}
    (hπ : π.IsEquivalence) : equivalences (A.pullbackHom Y π) := by
  have := A.B.paracompactSpace_pullback Y.X.PObj π.obj
  have := (A.B.pullback π.isScSmoothMap_obj).paracompactSpace_pullback Y.X.PMor Y.X.src
  have h := A.E.isStrongBundleEquivalence_pullbackProjFunctor hπ
  exact h

/-- The lift `C → π*W` of a morphism `Θ : C → A` covering `π ∘ κ`, covering `κ`. -/
def pullbackLiftHom (A : SEP.{u}) (Y : EP.{u}) (π : EpFunctor Y.X A.X) {C : SEP.{u}}
    (κ : EpFunctor C.X Y.X) (Θ : C ⟶ A) (h : Hom.ϕ Θ = π.comp κ) : C ⟶ A.pullbackAlong Y π :=
  haveI := A.B.paracompactSpace_pullback Y.X.PObj π.obj
  haveI := (A.B.pullback π.isScSmoothMap_obj).paracompactSpace_pullback Y.X.PMor Y.X.src
  ⟨κ, A.E.pullbackLiftFunctor π (h ▸ (Hom.isStrongBundleFunctor Θ).isMap),
    A.E.isStrongBundleFunctor_pullbackLiftFunctor π _⟩

theorem pullbackLiftHom_ϕ (A : SEP.{u}) (Y : EP.{u}) (π : EpFunctor Y.X A.X) {C : SEP.{u}}
    (κ : EpFunctor C.X Y.X) (Θ : C ⟶ A) (h : Hom.ϕ Θ = π.comp κ) :
    Hom.ϕ (A.pullbackLiftHom Y π κ Θ h) = κ := rfl

/-- `(π*W → W) ∘ (C → π*W) = Θ`. -/
theorem pullbackLiftHom_comp (A : SEP.{u}) (Y : EP.{u}) (π : EpFunctor Y.X A.X) {C : SEP.{u}}
    (κ : EpFunctor C.X Y.X) (Θ : C ⟶ A) (h : Hom.ϕ Θ = π.comp κ) :
    A.pullbackLiftHom Y π κ Θ h ≫ A.pullbackHom Y π = Θ :=
  Hom.ext_obj h.symm rfl

section Cone

variable {Φ : A ⟶ A'} (hΦ : equivalences Φ) (Ψ : A'' ⟶ A') {Y : EP.{u}}
  (π : EpFunctor Y.X A''.X) (κ : EpFunctor (A''.pullbackAlong Y π).X A.X)
  (τ : EpNatTrans (Hom.ϕ (A''.pullbackHom Y π ≫ Ψ)) ((Hom.ϕ Φ).comp κ))

/-- The strong bundle functor `Θ : π*W'' → W'`, `Θ(y, w'') = μ'(τ(y), Ψ(w''))`, covering
`ϕ ∘ κ` (`transportFunctor`). -/
def coneTransport : A''.pullbackAlong Y π ⟶ A' :=
  ⟨(Hom.ϕ Φ).comp κ, transportFunctor (Hom.isStrongBundleFunctor (A''.pullbackHom Y π ≫ Ψ)) τ,
    isStrongBundleFunctor_transportFunctor _ τ⟩

include hΦ in
theorem isMap_coneTransport : (A''.pullbackAlong Y π).E.IsMap A'.E ((Hom.ϕ Φ).comp κ)
    (Hom.Φ (coneTransport (Φ := Φ) Ψ π κ τ)).obj :=
  isMap_transportMap _ τ

/-- **The leg `π*W'' → W` of the cone**: the fibrewise inverse lift of `Θ` through `Φ`,
covering `κ` (`invLiftFunctor`). -/
def coneHom : A''.pullbackAlong Y π ⟶ A :=
  ⟨κ, invLiftFunctor hΦ (isMap_coneTransport hΦ Ψ π κ τ),
    isStrongBundleFunctor_invLiftFunctor hΦ (isMap_coneTransport hΦ Ψ π κ τ)⟩

theorem coneHom_ϕ : Hom.ϕ (coneHom hΦ Ψ π κ τ) = κ := rfl

/-- `Φ ∘ Π = Θ`. -/
theorem coneHom_comp : coneHom hΦ Ψ π κ τ ≫ Φ = coneTransport Ψ π κ τ :=
  Hom.ext' rfl (comp_invLiftFunctor hΦ (isMap_coneTransport hΦ Ψ π κ τ))

/-- **The square commutes up to natural equivalence**: `Ψ ∘ π_{W''} ≃ Φ ∘ Π` (Definition
10.4.8), by `transportNatTrans`. -/
theorem natEquiv_cone : NatEquiv (A''.pullbackHom Y π ≫ Ψ) (coneHom hΦ Ψ π κ τ ≫ Φ) := by
  rw [coneHom_comp]
  exact ⟨transportNatTrans _ τ⟩

theorem P_coneHom (m : (A''.pullbackAlong Y π).W) :
    A.P ((Hom.Φ (coneHom hΦ Ψ π κ τ)).obj m) = κ.obj ((A''.pullbackAlong Y π).P m) :=
  P_invLiftMap hΦ (isMap_coneTransport hΦ Ψ π κ τ) m

theorem obj_coneHom (m : (A''.pullbackAlong Y π).W) :
    (Hom.Φ Φ).obj ((Hom.Φ (coneHom hΦ Ψ π κ τ)).obj m) =
      (Hom.Φ (coneTransport Ψ π κ τ)).obj m :=
  obj_invLiftMap hΦ (isMap_coneTransport hΦ Ψ π κ τ) m

/-- `Π(m)` is the unique `w` over `κ(P m)` with `Φ(w) = μ'(τ(P m), Ψ(m))`. -/
theorem coneHom_obj_eq {m : (A''.pullbackAlong Y π).W} {w : A.W}
    (hw : A.P w = κ.obj ((A''.pullbackAlong Y π).P m))
    (he : (Hom.Φ Φ).obj w = (Hom.Φ (coneTransport Ψ π κ τ)).obj m) :
    (Hom.Φ (coneHom hΦ Ψ π κ τ)).obj m = w :=
  invLiftMap_eq hΦ (isMap_coneTransport hΦ Ψ π κ τ) hw he

end Cone

end SEP

/-! ### The weak fibred product of strong bundles and Theorem 10.2.2 -/

namespace SBWeakFibredProduct

open SEP WeakFibredProduct EPLocalization

variable {A A' A'' : SEP.{u}} {Φ : A ⟶ A'} (hΦ : SEP.equivalences Φ) (Ψ : A'' ⟶ A')

include hΦ in
theorem admissible : Admissible (Hom.ϕ Φ) (Hom.ϕ Ψ) :=
  .of_isEquivalence_left hΦ.isEquivalence_base

/-- The weak fibred product `X ×_{X'} X''` of the bases. -/
abbrev baseEP : EP.{u} :=
  wfp (A := A.baseEP) (B := A''.baseEP) (C := A'.baseEP) (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ)

/-- **The weak fibred product `W ×_{W'} W''` of strong bundles**: the pull-back of `W''` along
`πZ : X ×_{X'} X'' → X''`, a strong bundle over the ep-groupoid `X ×_{X'} X''`. -/
abbrev wfpSEP : SEP.{u} :=
  A''.pullbackAlong (baseEP hΦ Ψ) (projRight (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ))

/-- The projection `W ×_{W'} W'' → W''`, covering `πZ`. -/
def projZ : wfpSEP hΦ Ψ ⟶ A'' :=
  A''.pullbackHom (baseEP hΦ Ψ) (projRight (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ))

/-- The projection `W ×_{W'} W'' → W`, covering `πX`: `((x, φ, z), w'') ↦ Φ_x⁻¹(μ'(φ⁻¹, Ψ(w'')))`.
-/
def projX : wfpSEP hΦ Ψ ⟶ A :=
  coneHom hΦ Ψ (Y := baseEP hΦ Ψ) (projRight (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ))
    (projLeft (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ))
    (natTrans (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ)).symm

theorem projX_ϕ : Hom.ϕ (projX hΦ Ψ) = projLeft (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ) := rfl

theorem projZ_ϕ : Hom.ϕ (projZ hΦ Ψ) = projRight (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ) := rfl

/-- **The strong bundle version of 2021 Theorem 10.2.2, p. 477 (2017: Theorem 10.2, p. 343)**
(used in §10.5, 2021 p. 504): for a strong bundle equivalence `Φ : W → W'` covering `ϕ` and a
strong bundle functor `Ψ : W'' → W'` covering `ψ`, the strong bundle `W ×_{W'} W''` over
`X ×_{X'} X''` has projections `ΠX` covering `πX` and `ΠZ` covering `πZ`; `ΠZ` is a strong bundle
equivalence, and `Φ ∘ ΠX ≃ Ψ ∘ ΠZ` as strong bundle functors (Definition 10.4.8). -/
theorem theorem_10_2_2 :
    SEP.equivalences (projZ hΦ Ψ) ∧ SEP.NatEquiv (projX hΦ Ψ ≫ Φ) (projZ hΦ Ψ ≫ Ψ) ∧
      Hom.ϕ (projX hΦ Ψ) = projLeft (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ) ∧
      Hom.ϕ (projZ hΦ Ψ) = projRight (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ) :=
  ⟨A''.equivalences_pullbackHom _ (isEquivalence_projRight hΦ.isEquivalence_base _),
    (natEquiv_cone hΦ Ψ _ _ _).symm, rfl, rfl⟩

/-! ### The case of two equivalences -/

section Right

variable (hΨ : SEP.equivalences Ψ)

/-- The pull-back of `W` along `πX : X ×_{X'} X'' → X`. -/
abbrev wfpSEPLeft : SEP.{u} :=
  A.pullbackAlong (baseEP hΦ Ψ) (projLeft (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ))

/-- The leg `πX*W → W''` (the cone of `Ψ` over `Φ`). -/
def projZLeft : wfpSEPLeft hΦ Ψ ⟶ A'' :=
  coneHom hΨ Φ (Y := baseEP hΦ Ψ) (projLeft (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ))
    (projRight (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ)) (natTrans (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ
        Ψ))

/-- `πZ*W'' → πX*W`, `(p, w'') ↦ (p, ΠX(p, w''))`. -/
def swapHom : wfpSEP hΦ Ψ ⟶ wfpSEPLeft hΦ Ψ :=
  A.pullbackLiftHom (baseEP hΦ Ψ) (projLeft (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ))
    (EpFunctor.id _) (projX hΦ Ψ) (EpFunctor.ext rfl rfl)

/-- `πX*W → πZ*W''`, `(p, w) ↦ (p, Π'Z(p, w))`. -/
def swapHomInv : wfpSEPLeft hΦ Ψ ⟶ wfpSEP hΦ Ψ :=
  A''.pullbackLiftHom (baseEP hΦ Ψ) (projRight (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ))
    (EpFunctor.id _) (projZLeft hΦ Ψ hΨ) (EpFunctor.ext rfl rfl)

theorem swapHomInv_swapHom (m : (wfpSEP hΦ Ψ).W) :
    (Hom.Φ (swapHomInv hΦ Ψ hΨ)).obj ((Hom.Φ (swapHom hΦ Ψ)).obj m) = m := by
  have hm : A''.P m.1.2 = m.1.1.z := m.2
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change (Hom.Φ (projZLeft hΦ Ψ hΨ)).obj ((Hom.Φ (swapHom hΦ Ψ)).obj m) = m.1.2
  refine coneHom_obj_eq hΨ Φ _ _ _ hm ?_
  have hw : A'.P ((Hom.Φ Ψ).obj m.1.2) = A'.X.src (A'.X.inv m.1.1.φ) := by
    rw [A'.X.src_inv, m.1.1.tgt_φ, (Hom.isStrongBundleFunctor Ψ).isStrongBundleMap_obj.covers, hm]
  have e : (Hom.Φ Φ).obj ((Hom.Φ (projX hΦ Ψ)).obj m) =
      A'.E.μ ⟨(A'.X.inv m.1.1.φ, (Hom.Φ Ψ).obj m.1.2), hw⟩ :=
    obj_coneHom hΦ Ψ _ _ _ m
  exact (A'.E.μ_eq_of_eq_μ_inv _ hw e).symm

theorem swapHom_swapHomInv (n : (wfpSEPLeft hΦ Ψ).W) :
    (Hom.Φ (swapHom hΦ Ψ)).obj ((Hom.Φ (swapHomInv hΦ Ψ hΨ)).obj n) = n := by
  have hn : A.P n.1.2 = n.1.1.x := n.2
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change (Hom.Φ (projX hΦ Ψ)).obj ((Hom.Φ (swapHomInv hΦ Ψ hΨ)).obj n) = n.1.2
  refine coneHom_obj_eq hΦ Ψ _ _ _ hn ?_
  have ha : A'.P ((Hom.Φ Φ).obj n.1.2) = A'.X.src n.1.1.φ := by
    rw [n.1.1.src_φ, (Hom.isStrongBundleFunctor Φ).isStrongBundleMap_obj.covers, hn]
  have e : (Hom.Φ Ψ).obj ((Hom.Φ (projZLeft hΦ Ψ hΨ)).obj n) =
      A'.E.μ ⟨(n.1.1.φ, (Hom.Φ Φ).obj n.1.2), ha⟩ :=
    obj_coneHom hΨ Φ _ _ _ n
  have hv : A'.P ((Hom.Φ Ψ).obj ((Hom.Φ (projZLeft hΦ Ψ hΨ)).obj n)) =
      A'.X.src (A'.X.inv n.1.1.φ) := by
    rw [e, A'.E.P_μ, A'.X.src_inv]
  exact (A'.E.μ_inv_eq_of_eq_μ hv ha e).symm

include hΨ in
theorem equivalences_swapHom : SEP.equivalences (swapHom hΦ Ψ) := by
  have h := EpStrongBundle.isStrongBundleEquivalence_of_inverse
    (Hom.isStrongBundleFunctor (swapHom hΦ Ψ)).isMap
    (Hom.isStrongBundleFunctor (swapHomInv hΦ Ψ hΨ)).isMap (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (swapHomInv_swapHom hΦ Ψ hΨ) (swapHom_swapHomInv hΦ Ψ hΨ)
  rwa [← (Hom.isStrongBundleFunctor (swapHom hΦ Ψ)).eq_liftFunctor] at h

include hΨ in
/-- **The strong bundle version of 2021 Theorem 10.2.2, p. 478, the case `Ψ` an equivalence**:
then also `ΠX` is a strong bundle equivalence (`ΠX = π_W ∘ S` for the isomorphism
`S : πZ*W'' → πX*W` and the projection `π_W : πX*W → W`, an equivalence since `πX` is one). -/
theorem theorem_10_2_2_right : SEP.equivalences (projX hΦ Ψ) := by
  rw [← A.pullbackLiftHom_comp (baseEP hΦ Ψ) (projLeft (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ))
    (EpFunctor.id _) (projX hΦ Ψ) (EpFunctor.ext rfl rfl)]
  exact SEP.equivalences.comp_mem _ _ (equivalences_swapHom hΦ Ψ hΨ)
    (A.equivalences_pullbackHom _ (isEquivalence_projLeft hΨ.isEquivalence_base _))

end Right

/-- The weak fibred product of strong bundles is nonempty if `W''` is (`ΠZ` is an equivalence,
hence surjective on orbit spaces). -/
theorem nonempty_wfpSEP (w : A''.W) : Nonempty (wfpSEP hΦ Ψ).W := by
  obtain ⟨q, -⟩ := (theorem_10_2_2 hΦ Ψ).1.isEquivalence.isHomeomorph_orbitMap.surjective
    (Quotient.mk _ w)
  obtain ⟨m, -⟩ := Quot.exists_rep q
  exact ⟨m⟩

end SBWeakFibredProduct

/-! ### Satisfiability -/

namespace StrongBundleWeakFibredProductExamples

open StrongBundleEquivalenceExamples SBWeakFibredProduct

variable (n k : ℕ)

/-- **The strong bundle version of Theorem 10.2.2 is not vacuous**: for the strong bundle
equivalence `Φ = (-id)* : (-id)*W' → W'` (`negSEPHom`) and `Ψ = 1_{W'}`, `W ×_{W'} W'` is a
nonempty strong bundle over `X ×_{X'} X'`, both projections are strong bundle equivalences and
`Φ ∘ ΠX ≃ ΠZ`. -/
theorem theorem_10_2_2_negSEPHom :
    Nonempty (wfpSEP (negSEPHom_mem_equivalences n k) (𝟙 (epSEP n k))).W ∧
    SEP.equivalences (projZ (negSEPHom_mem_equivalences n k) (𝟙 (epSEP n k))) ∧
    SEP.equivalences (projX (negSEPHom_mem_equivalences n k) (𝟙 (epSEP n k))) ∧
    SEP.NatEquiv (projX (negSEPHom_mem_equivalences n k) (𝟙 (epSEP n k)) ≫ negSEPHom n k)
      (projZ (negSEPHom_mem_equivalences n k) (𝟙 (epSEP n k)) ≫ 𝟙 (epSEP n k)) := by
  obtain ⟨w, -⟩ := (epSEP n k).B.surjective ((0 : Fin n → ℝ) : (epSEP n k).Obj)
  exact ⟨nonempty_wfpSEP _ _ w, (theorem_10_2_2 _ _).1,
    theorem_10_2_2_right _ _ (SEP.equivalences.id_mem _), (theorem_10_2_2 _ _).2.1⟩

end StrongBundleWeakFibredProductExamples

end Polyfold
