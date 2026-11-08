import Polyfold.Chapter8.EpStrongBundle
import Polyfold.Chapter3.NonVacuityG

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 8: **witnesses** for the definitions of §8.3, "Strong Bundles over Ep-Groupoids"
(**Definitions 8.4, 8.5, 8.6, 8.7**, pp. 270–275), for **Definition 8.8** (proper covering
functors, p. 275) and for **Definition 8.10** (proper strong bundle covering functors, p. 285; the
structure studied in §8.5.2, pp. 288–289).

# Non-vacuity: strong bundles over ep-groupoids and their coverings

## The text, paraphrased

(Definition 8.4) A strong bundle over an ep-groupoid `X` is a strong bundle `P : W → X` over the
object M-polyfold with a structure map `μ : 𝐗 ₛ×_P W → W`, a surjective local sc-diffeomorphism
and strong bundle map covering `t`, with `μ(1_x, w) = w` and `μ(ψ ∘ γ, w) = μ(ψ, μ(γ, w))`.
(Definitions 8.5, 8.6) Strong bundle maps `Φ` covering an sc-smooth functor `ϕ`, with
`Φ(μ(γ, w)) = μ'(ϕ(γ), Φ(w))`; equivalently strong bundle functors `(W, 𝐖) → (W', 𝐖')`.
(Definition 8.7) `Γ(P, μ)`, `Γ⁺(P, μ)`, `Fred(P, μ)`: the sc-smooth, sc⁺- and sc-Fredholm sections
`f` with `f(t φ) = μ(φ, f(s φ))`.  (Definition 8.8) `F : Y → X` is a proper covering functor:
`F` a surjective local sc-diffeomorphism on objects, finite and evenly covered fibres, and
`φ ↦ (F(φ), s(φ))` an sc-diffeomorphism `𝐘 → 𝐗 ₛ×_F Y`.  (Definition 8.10) A proper strong bundle
covering functor `A` covering a proper covering functor `F`: surjective, a local strong bundle
isomorphism, a strong bundle isomorphism over the sets `U(y) → U(x)` of an even covering, and
`(ψ, w) ↦ ((F(ψ), A(w)), w)` a strong bundle isomorphism `𝐖 → 𝐕 ₛ×_A W`.

## What is formalized

* `pullbackMap`, `StrongBundle.isStrongBundleMap_pullbackMap`: **a map of pull-backs**
  `f*Y → f'*Y'`, `(z, y) ↦ (g(z), Φ(y))`, for a strong bundle map `Φ` covering `h` and an
  sc-smooth `g` with `f' ∘ g = h ∘ f`, is a strong bundle map covering `g` (the argument of
  `EpStrongBundle.IsMap.isStrongBundleFunctor_liftFunctor`, for a general second pull-back).
* `StrongBundle.isStrongBundleIsoOn_id`: the identity is a strong bundle isomorphism `Y|U → Y|U`
  for open `U`.
* **Definition 8.4**: `EpStrongBundle.trivial B : EpStrongBundle (EpGroupoid.trivial PZ) B`, the
  strong bundle `B` over the trivial ep-groupoid of `Z` (Chapter 7, `s = t = id`) with
  `μ(z, w) = w` (the pull-back projection along `id`); `trivial_μ`.
* **Definitions 8.5, 8.6**: `EpStrongBundle.isMap_id` (the identity, covering `EpFunctor.id`),
  `EpStrongBundle.isStrongBundleFunctor_id`.
* **Definition 8.7**: `EpStrongBundle.isFunctorialSection_trivial` (over the trivial ep-groupoid
  every section is functorial), `mem_sectionFunctors_trivial`, `mem_plusSectionFunctors_trivial`,
  `mem_fredholmSectionFunctors_trivial` (`Γ`, `Γ⁺`, `Fred` are Part I's sc-smooth, sc⁺- and
  sc-Fredholm sections).
* **Definition 8.8**: `EpFunctor.isScDiffeoOn_fibredMap_id` (`φ ↦ (φ, s(φ))` with inverse
  `(φ, x) ↦ φ`) and **`EpFunctor.isProperCovering_id`**: the identity functor of any ep-groupoid
  is a proper covering functor.
* **Definition 8.10**: `EpStrongBundle.isStrongBundleIso_fibredLift_id` (condition (3) for the
  identity, with inverse `((φ, x), w) ↦ (φ, w)`) and
  **`EpStrongBundle.isProperStrongBundleCovering_id`**: the identity of any strong bundle over an
  ep-groupoid is a proper strong bundle covering functor covering the identity.
* **The concrete instance** on Part I's trivial strong bundle `ℝⁿ × ℝᵏ → ℝⁿ`
  (`TrivialBundle.bundle n k`, Chapter 3 `NonVacuity.lean`), over the trivial ep-groupoid of `ℝⁿ`:
  `TrivialBundle.epBundle n k`, its ep-groupoid `epBundleEpGroupoid n k` (the functorial picture,
  `toEpGroupoid`), `epBundle_isProperStrongBundleCovering`, `epBundle_isMap_id`;
  `fiberZero_mem_plusSectionFunctors_epBundle` (`0 ∈ Γ⁺`), and for a `C^∞` map
  `φ : ℝⁿ → ℝᵏ` the graph section `x ↦ (x, φ(x))`: `graphSection_mem_sectionFunctors_epBundle`,
  `graphSection_mem_fredholmSectionFunctors_epBundle` (`∈ Γ`, `∈ Fred`, from Part I's
  `isScSmoothSection_graphSection` and `isScFredholmSection_graphSection`, germ reading).

## Witnesses and the hypotheses they make non-vacuous

* `EpStrongBundle.trivial`: Definition 8.4 for every strong bundle over an M-polyfold; with
  `TrivialBundle.epBundle`, a concrete one in `Type`, for which the functorial picture
  (`toEpGroupoid`, an `EpGroupoid` of Chapter 7) is available.
* `isMap_id`, `isStrongBundleFunctor_id`: Definitions 8.5 and 8.6.
* `graphSection_mem_fredholmSectionFunctors_epBundle`: `Fred(P, μ) ≠ ∅` (Definition 8.7 (3)), with
  nonzero members; `fiberZero_mem_plusSectionFunctors_epBundle`: `Γ⁺(P, μ) ≠ ∅`.
* `isProperCovering_id`: Definition 8.8, all of (1)–(3).
* `isProperStrongBundleCovering_id`, `epBundle_isProperStrongBundleCovering`: Definition 8.10, all
  of (1)–(3), on the reading of (3) recorded in `EpStrongBundle.lean`; hence the hypothesis of
  `EpStrongBundle.section_8_5_2` can hold.

## What the witnesses do not exercise

* All of them have trivial isotropy (the trivial ep-groupoid, or the identity functor): the fibres
  `F⁻¹(x)` are singletons, so the even covering and the finiteness in Definitions 8.8 (2), 8.10 (2)
  are met with one sheet.  No covering with `|F⁻¹(x)| > 1` is constructed here.
* `Γ⁺` is witnessed by the zero section only.
-/

open Set Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### A map into a sub-M-polyfold -/

section Helpers

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- **A map into a sub-M-polyfold** `A ⊆ Y` is sc-smooth into `A` as soon as it is sc-smooth into
`Y` (the private lemma of the same name in `ProperCovering.lean` and `SubGroupoid.lean`): near
`x`, `f = (i⁻¹ ∘ r) ∘ i ∘ f` for a retraction `r` onto `A` near `f(x)` (Proposition 2.21 (2)). -/
private theorem isScSmoothOn_subPolyfold_of_val {A : Set Y} (hA : Q.IsSubMPolyfold A)
    [ParacompactSpace A] {f : X → A} {U : Set X}
    (hf : P.IsScSmoothOn Q (fun x => (f x : Y)) U) :
    P.IsScSmoothOn (MPolyfold.subPolyfold hA) f U := by
  refine MPolyfold.IsScSmoothOn.of_locally hf.isOpen fun x hx => ?_
  set d := hA.data (f x).2
  have hU' : IsOpen (U ∩ (fun x => (f x : Y)) ⁻¹' d.V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen d.isOpen
  refine ⟨_, hU', ⟨hx, hA.mem_data_V (f x).2⟩, inter_subset_left, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp (MPolyfold.subPolyfold_retraction_isScSmooth hA d (f x))
    (hf.mono hU' inter_subset_left) fun y hy => hy.2).congr fun y hy => Subtype.ext ?_
  simp only [Function.comp_apply]
  rw [d.retractInto_val (f x) hy.2]
  exact d.apply_eq_self ⟨(f y).2, hy.2⟩

end Helpers

/-! ### Maps of pull-backs -/

section PullbackMap

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {f : Z → X} [ParacompactSpace (pullbackSpace P f)]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  {Z' : Type*} [TopologicalSpace Z'] [T2Space Z'] [ParacompactSpace Z'] {PZ' : MPolyfold Z'}
  {f' : Z' → X'} [ParacompactSpace (pullbackSpace P' f')]
  {h : X → X'} {Φ : Y → Y'} {g : Z → Z'}

variable (P P' f f') in
/-- The map of pull-backs `f*Y → f'*Y'`, `(z, y) ↦ (g(z), Φ(y))`, for `P' ∘ Φ = h ∘ P` and
`f' ∘ g = h ∘ f`. -/
def pullbackMap (hΦ : ∀ y, P' (Φ y) = h (P y)) (hg : ∀ z, f' (g z) = h (f z))
    (q : pullbackSpace P f) : pullbackSpace P' f' :=
  ⟨(g (q : Z × Y).1, Φ (q : Z × Y).2),
    (hΦ _).trans ((congrArg h (q.2 : P (q : Z × Y).2 = f (q : Z × Y).1)).trans (hg _).symm)⟩

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] [ParacompactSpace (pullbackSpace P f)]
  [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] [TopologicalSpace Y'] [T2Space Y']
  [ParacompactSpace Y'] [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  [TopologicalSpace Z'] [T2Space Z'] [ParacompactSpace Z'] [ParacompactSpace (pullbackSpace P' f')]
  in
@[simp] lemma pullbackMap_val (hΦ : ∀ y, P' (Φ y) = h (P y)) (hg : ∀ z, f' (g z) = h (f z))
    (q : pullbackSpace P f) :
    (pullbackMap P f P' f' hΦ hg q : Z' × Y') = (g (q : Z × Y).1, Φ (q : Z × Y).2) := rfl

namespace StrongBundle

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'} (hf : PZ.IsScSmoothMap PX f)
  (hf' : PZ'.IsScSmoothMap PX' f')

/-- **A map of pull-backs is a strong bundle map**: for a strong bundle map `Φ : Y → Y'` covering
`h` and an sc-smooth `g : Z → Z'` with `f' ∘ g = h ∘ f`, `(z, y) ↦ (g(z), Φ(y))` is a strong bundle
map `f*Y → f'*Y'` covering `g` (linear on the fibres, those of `Φ`; sc-smooth on `[0]` and `[1]`
by the universal properties of `f'*Y'[0]`, `f'*Y'[1]`). -/
theorem isStrongBundleMap_pullbackMap (hΦ : B.IsStrongBundleMap B' h Φ)
    (hgs : PZ.IsScSmoothMap PZ' g) (hg : ∀ z, f' (g z) = h (f z)) :
    (B.pullback hf).IsStrongBundleMap (B'.pullback hf') g
      (pullbackMap P f P' f' hΦ.covers hg) where
  covers _ := rfl
  fiber_linear z := isLinearMap_fiberRestrict_pullbackMap hΦ.covers hΦ.fiber_linear hg _
    (fun _ => rfl) _ z
  isScSmoothMap :=
    B'.isScSmoothMap_pullbackPair hf' (a := g ∘ pullbackProj P f) (b := Φ ∘ pullbackProj' P f)
      (hgs.comp (B.isScSmoothMap_pullbackProj hf))
      (hΦ.isScSmoothMap.comp (B.isScSmoothMap_pullbackProj' hf))
      fun q => (pullbackMap P f P' f' hΦ.covers hg q).2
  mapsTo_oneSet q hq := by
    rw [B'.mem_oneSet_pullback_iff]
    exact hΦ.mapsTo_oneSet ((B.mem_oneSet_pullback_iff hf q).1 hq)
  isScSmoothMap_one := by
    refine B'.isScSmoothMap_to_pullback_one hf' ?_ ?_
    · exact hgs.comp (B.pullback hf).isScSmoothMap_proj1
    · exact hΦ.isScSmoothMap_one.comp (B.isScSmoothMap_one_pullbackProj' hf)

end StrongBundle

end PullbackMap

/-! ### The identity as a strong bundle isomorphism over an open set -/

section IsoOnId

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

namespace StrongBundle

/-- The identity is a strong bundle isomorphism `Y|U → Y|U` for open `U`. -/
theorem isStrongBundleIsoOn_id {U : Set X} (hU : IsOpen U) :
    B.IsStrongBundleIsoOn B (IsStrongBundleMap.id B) U U where
  isScDiffeoOn_base := ⟨id, MPolyfold.isScDiffeoOn_id hU⟩
  isScDiffeoOn_zero := ⟨id, MPolyfold.isScDiffeoOn_id (hU.preimage B.continuous)⟩
  isScDiffeoOn_one :=
    ⟨id, MPolyfold.isScDiffeoOn_id (hU.preimage (continuousOn_univ.1
      B.isScSmoothMap_proj1.continuousOn))⟩

end StrongBundle

end IsoOnId

/-! ### Definition 8.4: strong bundles over the trivial ep-groupoid -/

section Trivial

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Z}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace EpStrongBundle

/-- **A strong bundle over the trivial ep-groupoid** (Definition 8.4): a strong bundle `B` over
the M-polyfold `Z`, over `EpGroupoid.trivial PZ` (`𝐗 = X = Z`, `s = t = id`), with
`μ(z, w) = w`, the pull-back projection `P' : id*W → W` (a strong bundle map covering `id = t` and
a local sc-diffeomorphism by `StrongBundleMap.lean`). -/
def trivial (B : StrongBundle PZ P) : EpStrongBundle (EpGroupoid.trivial PZ) B where
  μ := pullbackProj' P (EpGroupoid.trivial PZ).src
  isStrongBundleMap := by
    have := B.paracompactSpace_pullback PZ (EpGroupoid.trivial PZ).src
    exact B.isStrongBundleMap_pullbackProj' (EpGroupoid.trivial PZ).isScSmoothMap_src
  surjective w := ⟨⟨(P w, w), rfl⟩, rfl⟩
  isLocalScDiffeo := by
    have := B.paracompactSpace_pullback PZ (EpGroupoid.trivial PZ).src
    exact B.isLocalScDiffeo_pullbackProj' (EpGroupoid.trivial PZ).isScSmoothMap_src
      (EpGroupoid.trivial PZ).isLocalScDiffeo_src
  μ_unit _ := rfl
  μ_comp _ _ _ _ _ := rfl

variable {B : StrongBundle PZ P}

@[simp] lemma trivial_μ (q : pullbackSpace P (EpGroupoid.trivial PZ).src) :
    (trivial B).μ q = (q : Z × W).2 := rfl

/-- Over the trivial ep-groupoid every section is functorial (`f(t φ) = f(φ) = μ(φ, f(s φ))`). -/
theorem isFunctorialSection_trivial {f : Z → W} (hf : IsSection P f) :
    (trivial B).IsFunctorialSection hf := fun _ => rfl

/-- `Γ(P, μ)` over the trivial ep-groupoid is the set of Part I's sc-smooth sections. -/
theorem mem_sectionFunctors_trivial {f : Z → W} :
    f ∈ (trivial B).sectionFunctors ↔ B.IsScSmoothSection f :=
  ⟨fun h => h.1, fun h => ⟨h, isFunctorialSection_trivial h.1⟩⟩

/-- `Γ⁺(P, μ)` over the trivial ep-groupoid. -/
theorem mem_plusSectionFunctors_trivial {f : Z → W} :
    f ∈ (trivial B).plusSectionFunctors ↔ B.IsScSmoothSection f ∧ B.IsScPlusSection f :=
  ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨mem_sectionFunctors_trivial.2 h.1, h.2⟩⟩

/-- `Fred(P, μ)` over the trivial ep-groupoid. -/
theorem mem_fredholmSectionFunctors_trivial {f : Z → W} :
    f ∈ (trivial B).fredholmSectionFunctors ↔
      B.IsScSmoothSection f ∧ B.IsScFredholmSection f :=
  ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨mem_sectionFunctors_trivial.2 h.1, h.2⟩⟩

end EpStrongBundle

end Trivial

/-! ### Definition 8.5: the identity -/

section MapId

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

/-- **Definition 8.5 for the identity**: `id : W → W` is a strong bundle map covering the identity
functor. -/
theorem isMap_id (E : EpStrongBundle X B) : E.IsMap E (EpFunctor.id X) id where
  isStrongBundleMap := StrongBundle.IsStrongBundleMap.id B
  map_μ _ _ _ := rfl

end EpStrongBundle

end MapId

/-! ### Definition 8.8: the identity functor is a proper covering functor -/

section ProperCoveringId

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

namespace EpFunctor

theorem preimage_obj_id (x : Obj) : (EpFunctor.id X).obj ⁻¹' {x} = {x} := rfl

/-- Definition 8.8 (3) for the identity: `φ ↦ (φ, s(φ))` is an sc-diffeomorphism `𝐗 → 𝐗 ₛ×_id X`
onto Part I's fibred-product sub-M-polyfold, with inverse `(φ, x) ↦ φ`. -/
theorem isScDiffeoOn_fibredMap_id [ParacompactSpace (Mor × Obj)]
    [ParacompactSpace (MPolyfold.fibredProduct X.src (EpFunctor.id X).obj)] :
    X.PMor.IsScDiffeoOn (MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_fibredProduct
      X.isLocalScDiffeo_src (EpFunctor.id X).isScSmoothMap_obj)) (EpFunctor.id X).fibredMap
      (fun p => (p : Mor × Obj).1) univ univ where
  isScSmoothOn := isScSmoothOn_subPolyfold_of_val _
    (MPolyfold.IsScSmoothOn.prodMk MPolyfold.isScSmoothMap_id X.isScSmoothMap_src)
  isScSmoothOn_inv :=
    (MPolyfold.isScSmoothMap_fst X.PMor X.PObj).comp (MPolyfold.subPolyfold_inclusion_isScSmooth _)
  mapsTo := mapsTo_univ _ _
  mapsTo_inv := mapsTo_univ _ _
  left_inv _ _ := rfl
  right_inv p _ := Subtype.ext (Prod.ext rfl p.2)

/-- **Definition 8.8 for the identity**: the identity functor of an ep-groupoid is a proper
covering functor (one sheet `U(x) = U(y) = X` over every `x`, `F⁻¹(x) = {x}`). -/
theorem isProperCovering_id : (EpFunctor.id X).IsProperCovering where
  surjective := surjective_id
  isLocalScDiffeo x := ⟨univ, univ, fun y => y, mem_univ x, MPolyfold.isScDiffeoOn_id isOpen_univ⟩
  finite_fiber x := by
    rw [preimage_obj_id]
    exact finite_singleton x
  evenlyCovered x := by
    refine ⟨univ, fun _ => univ, fun _ y => y, isOpen_univ, mem_univ x, ?_,
      fun _ _ => ⟨mem_univ _, MPolyfold.isScDiffeoOn_id isOpen_univ⟩, ?_⟩
    · rw [preimage_obj_id]
      exact pairwiseDisjoint_singleton _ _
    · rw [preimage_obj_id, biUnion_singleton, preimage_univ]
  isScDiffeo_fibredMap := by
    have := MPolyfold.paracompactSpace_prod X.PMor X.PObj
    have := (X.PMor.prod X.PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct X.src (EpFunctor.id X).obj)
    exact ⟨_, isScDiffeoOn_fibredMap_id⟩

end EpFunctor

end ProperCoveringId

/-! ### Definitions 8.6 and 8.10: the identity is a proper strong bundle covering functor -/

section CoveringId

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

namespace EpStrongBundle

/-- **Definition 8.6 for the identity**: the identity functor of `(W, 𝐖)` is a strong bundle
functor covering the identity functor of `X`. -/
theorem isStrongBundleFunctor_id (E : EpStrongBundle X B) :
    E.IsStrongBundleFunctor E (EpFunctor.id X) (EpFunctor.id E.toEpGroupoid) :=
  ⟨StrongBundle.IsStrongBundleMap.id B, StrongBundle.IsStrongBundleMap.id _⟩

variable (B) in
/-- **Definition 8.10 (3) for the identity**: `(ψ, w) ↦ ((ψ, s(ψ)), w)` is a strong bundle
isomorphism `𝐖 → (𝐗 ₛ×_id X) ×_{pr₂} W` covering `ψ ↦ (ψ, s(ψ))`, with inverse
`((φ, x), w) ↦ (φ, w)` covering `(φ, x) ↦ φ` (both maps of pull-backs, `pullbackMap`). -/
theorem isStrongBundleIso_fibredLift_id [ParacompactSpace (Mor × Obj)]
    [ParacompactSpace (MPolyfold.fibredProduct X.src (EpFunctor.id X).obj)]
    [ParacompactSpace (pullbackSpace P (EpFunctor.id X).fibredSnd)] :
    (B.pullback X.isScSmoothMap_src).IsStrongBundleIso
      (B.pullback (EpFunctor.id X).isScSmoothMap_fibredSnd) (EpFunctor.id X).fibredMap
      (fibredLift P (EpFunctor.id X)) (fun p => (p : Mor × Obj).1)
      (pullbackMap P (EpFunctor.id X).fibredSnd P X.src (StrongBundle.IsStrongBundleMap.id B).covers
        (g := fun p => (p : Mor × Obj).1) fun p => p.2) where
  toMap := StrongBundle.isStrongBundleMap_pullbackMap X.isScSmoothMap_src
    (EpFunctor.id X).isScSmoothMap_fibredSnd (StrongBundle.IsStrongBundleMap.id B)
    EpFunctor.isScDiffeoOn_fibredMap_id.isScSmoothOn fun _ => rfl
  invMap := StrongBundle.isStrongBundleMap_pullbackMap (EpFunctor.id X).isScSmoothMap_fibredSnd
    X.isScSmoothMap_src (StrongBundle.IsStrongBundleMap.id B)
    EpFunctor.isScDiffeoOn_fibredMap_id.isScSmoothOn_inv fun p => p.2
  left_inv _ := rfl
  right_inv r := by
    have hr : X.src ((r : MPolyfold.fibredProduct X.src (EpFunctor.id X).obj × W).1 :
        Mor × Obj).1 = ((r : MPolyfold.fibredProduct X.src (EpFunctor.id X).obj × W).1 :
        Mor × Obj).2 := (r : MPolyfold.fibredProduct X.src (EpFunctor.id X).obj × W).1.2
    exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl hr)) rfl)

/-- **Definition 8.10 for the identity**: the identity of a strong bundle `(P, μ)` over an
ep-groupoid is a proper strong bundle covering functor covering the identity functor. -/
theorem isProperStrongBundleCovering_id (E : EpStrongBundle X B) :
    E.IsProperStrongBundleCovering E (EpFunctor.id X) (EpFunctor.id E.toEpGroupoid) where
  isStrongBundleFunctor := E.isStrongBundleFunctor_id
  surjective := surjective_id
  isProperCovering := EpFunctor.isProperCovering_id
  isLocalStrongBundleIso y :=
    ⟨univ, univ, mem_univ y, StrongBundle.isStrongBundleIsoOn_id isOpen_univ⟩
  evenlyCovered x := by
    refine ⟨univ, fun _ => univ, isOpen_univ, mem_univ x, ?_,
      fun _ _ => ⟨mem_univ _, StrongBundle.isStrongBundleIsoOn_id isOpen_univ⟩, ?_⟩
    · rw [EpFunctor.preimage_obj_id]
      exact pairwiseDisjoint_singleton _ _
    · rw [EpFunctor.preimage_obj_id, biUnion_singleton, preimage_univ]
  isStrongBundleIso_fibredLift := by
    have := MPolyfold.paracompactSpace_prod X.PMor X.PObj
    have := (X.PMor.prod X.PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct X.src (EpFunctor.id X).obj)
    have := B.paracompactSpace_pullback (MPolyfold.subPolyfold
      (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src
        (EpFunctor.id X).isScSmoothMap_obj)) (EpFunctor.id X).fibredSnd
    exact ⟨_, _, isStrongBundleIso_fibredLift_id B⟩

end EpStrongBundle

end CoveringId

/-! ### The concrete instance: `ℝⁿ × ℝᵏ → ℝⁿ` over the trivial ep-groupoid of `ℝⁿ` -/

namespace TrivialBundle

variable (n k : ℕ)

/-- `𝐗 ₛ×_P W` for the trivial bundle over the trivial ep-groupoid of `ℝⁿ` is paracompact
(`StrongBundle.paracompactSpace_pullback`). -/
instance : ParacompactSpace
    (pullbackSpace (proj n k) (EpGroupoid.trivial (rnPolyfold n)).src) :=
  (bundle n k).paracompactSpace_pullback (rnPolyfold n) _

/-- **Part I's trivial strong bundle `ℝⁿ × ℝᵏ → ℝⁿ` as a strong bundle over the trivial
ep-groupoid of `ℝⁿ`** (Definition 8.4). -/
def epBundle : EpStrongBundle (EpGroupoid.trivial (rnPolyfold n)) (bundle n k) :=
  EpStrongBundle.trivial (bundle n k)

/-- Its ep-groupoid `(W, 𝐖)` of the functorial picture (p. 271). -/
def epBundleEpGroupoid :
    EpGroupoid ((Fin n → ℝ) × (Fin k → ℝ))
      (pullbackSpace (proj n k) (EpGroupoid.trivial (rnPolyfold n)).src) :=
  (epBundle n k).toEpGroupoid

/-- Definition 8.5 for the concrete instance. -/
theorem epBundle_isMap_id :
    (epBundle n k).IsMap (epBundle n k) (EpFunctor.id (EpGroupoid.trivial (rnPolyfold n))) id :=
  (epBundle n k).isMap_id

/-- **Definition 8.10 is satisfiable**: the identity of `ℝⁿ × ℝᵏ → ℝⁿ` over the trivial
ep-groupoid of `ℝⁿ` is a proper strong bundle covering functor. -/
theorem epBundle_isProperStrongBundleCovering :
    (epBundle n k).IsProperStrongBundleCovering (epBundle n k)
      (EpFunctor.id (EpGroupoid.trivial (rnPolyfold n))) (EpFunctor.id (epBundleEpGroupoid n k)) :=
  (epBundle n k).isProperStrongBundleCovering_id

/-- `0 ∈ Γ⁺(P, μ)` (Definition 8.7 (2)) for the concrete instance. -/
theorem fiberZero_mem_plusSectionFunctors_epBundle :
    fiberZero (proj n k) ∈ (epBundle n k).plusSectionFunctors :=
  (epBundle n k).fiberZero_mem_plusSectionFunctors

variable {n k} {φ : (Fin n → ℝ) → (Fin k → ℝ)}

/-- The graph section `x ↦ (x, φ(x))` of a `C^∞` map is in `Γ(P, μ)` (Definition 8.7 (1)). -/
theorem graphSection_mem_sectionFunctors_epBundle (hφ : ContDiff ℝ ∞ φ) :
    graphSection φ ∈ (epBundle n k).sectionFunctors :=
  EpStrongBundle.mem_sectionFunctors_trivial.2 (isScSmoothSection_graphSection hφ)

/-- **`Fred(P, μ) ≠ ∅`** (Definition 8.7 (3)): the graph section of a `C^∞` map is an sc-Fredholm
section functor (Part I's `isScFredholmSection_graphSection`, germ reading). -/
theorem graphSection_mem_fredholmSectionFunctors_epBundle (hφ : ContDiff ℝ ∞ φ) :
    graphSection φ ∈ (epBundle n k).fredholmSectionFunctors :=
  EpStrongBundle.mem_fredholmSectionFunctors_trivial.2
    ⟨isScSmoothSection_graphSection hφ, isScFredholmSection_graphSection hφ⟩

end TrivialBundle

end Polyfold
