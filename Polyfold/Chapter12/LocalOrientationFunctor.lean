import Polyfold.Chapter12.LocalOrientationSpace
import Polyfold.Chapter6.TransportFunctor
import Polyfold.Chapter6.ChartOrientationFunctor

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6,
**Theorem 6.6.13** (pp. 273–274) and **Definitions 6.6.14–6.6.16** (p. 274), with
Definition 6.2.1 (p. 239) for the linearizations.

# The functor `Γ_f`, orientability and orientations for the local orientation sets

## The text, paraphrased

Theorem 6.6.13: for an sc-Fredholm section `f` of a strong bundle over a tame M-polyfold there
is a uniquely determined functor `Γ_f`, from the category of smooth points and classes of
sc-smooth paths to the two-element sets `Or_x^f`, which on the paths in the neighbourhoods of
Theorem 6.6.11 is the local propagation (property (∗)).  Definition 6.6.14: `f` is orientable
if `Γ_f([φ])` depends only on the end points.  Definition 6.6.15 (an equivalent version): there
is a map `y ↦ o_y ∈ Or_y^f` which near every smooth point is a continuous orientation.
Definition 6.6.16: such a map is an orientation of `f`.

## What is formalized

The statements for the local orientation sets `OrxLoc hf x hs`
(`LocalOrientationDomains.lean`), with the hypotheses "`X` is tame" and "`f` has tame germ data"
only; the linearizations are made with sc⁺-sections over a *domain* (an open subset of the base
domain of a chart).

* `orFunctorMapLoc`, `orFunctorLoc`: the functor `Γ_f` (`LocalTransport.functorMap` for
  `orLocalTransportLoc`).
* `Dom.transportLoc_eq_of_isPush`: along a path in an open subset `U` of a domain `W` with the
  local propagation property for `f|W` in a chart `c` of `P|W`, the propagation is every
  push-forward `e` along the path in `c`, read through `toChartOr` and `Dom.toLoc`.
* Property (∗): `IsStarPropertyDom` (on the class of a path with all values in a domain `W` the
  map is the transport of `f|W`) and `IsStarPropertyLoc` (the text's form, with a chart of
  `P|W`, a set with the local propagation property and a push-forward `e`);
  `IsStarPropertyDom.isStarPropertyLoc`, `orFunctorMapLoc_isStarPropertyDom`,
  `orFunctorMapLoc_isStarPropertyLoc`, `orFunctorMapLoc_unique`.
* `theorem_6_6_13_loc`: **Theorem 6.6.13**; `theorem_6_6_13_loc_dom` with (∗) in the first
  form.
* `IsOrientableSectionLoc` (Definition 6.6.14), `IsSectionOrientationLoc` (Definition 6.6.16:
  near every smooth point the map is carried along by the propagation), the equivalences
  `isSectionOrientationLoc_iff` (with `Γ_f`), `isSectionOrientationLoc_iff_forall_dom`,
  `isSectionOrientationLoc_iff_forall_dom_isSectionOrientation` (read in every domain `W` the
  map is an orientation of `f|W` in the sense of Definition 6.6.16),
  `isOrientableSectionLoc_iff` (Definitions 6.6.14 and 6.6.15 are equivalent),
  `IsSectionOrientationLoc.apply_eq_iff`, `IsSectionOrientationLoc.exists_two`,
  `isOrientableSectionLoc_of_hom_eq`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### The propagation in a domain and push-forwards in a chart -/

/-- **The propagation along a path in a domain is every push-forward in a chart** (property (∗)
in a domain): for a domain `W`, a chart `c` of `P|W`, an open `U ⊆ W` with the local
propagation property for `f|W` in `c`, an sc-smooth path `γ` with all values in `W` and
`γ([0, 1]) ⊆ U`, and a push-forward `e` along `γ` in `c`, the propagation
`Or_{x₀}^f ≃ Or_{x₁}^f` is `e` read through `toChartOr` and the identifications
`Or_x^f ≃ Or_x^{f|W}`. -/
theorem StrongBundle.Dom.transportLoc_eq_of_isPush (D : B.Dom) (hX : PX.IsTame)
    (hf : B.IsScFredholmSectionTame f)
    {c : StrongBundleChart (PX.restrictOpen D.isOpen)
      (pullbackProj P (Subtype.val : D.carrier → X))} {hc : D.bundle.IsChart c}
    {U : Set D.carrier}
    (hU : HasLocalPropagation (D.sec f hf.isScSmooth.1)
      (D.isFredholm hf).toIsScFredholmSection c hc U) (hUo : IsOpen U)
    {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγD : ∀ q, γ q ∈ D.carrier)
    (hγU : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, D.liftPath γ hγD q ∈ U) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet)
    (hx₀ : (⟨x₀, h₀ ▸ hγD _⟩ : D.carrier) ∈ c.φ.source)
    (hx₁ : (⟨x₁, h₁ ▸ hγD _⟩ : D.carrier) ∈ c.φ.source)
    {e : (chartPtOf c hc hx₀ (StrongBundle.Dom.mem_smoothSet _ hs₀)).Or
        (D.sec f hf.isScSmooth.1) (D.isFredholm hf).toIsScFredholmSection ≃
      (chartPtOf c hc hx₁ (StrongBundle.Dom.mem_smoothSet _ hs₁)).Or
        (D.sec f hf.isScSmooth.1) (D.isFredholm hf).toIsScFredholmSection}
    (he : IsPush (D.sec f hf.isScSmooth.1) (D.isFredholm hf).toIsScFredholmSection c hc
      (D.liftPath γ hγD) (fun q hq => hU.subset (hγU q hq))
      (show D.liftPath γ hγD (pt1 0) = (⟨x₀, h₀ ▸ hγD _⟩ : D.carrier) from Subtype.ext h₀)
      (show D.liftPath γ hγD (pt1 1) = (⟨x₁, h₁ ▸ hγD _⟩ : D.carrier) from Subtype.ext h₁)
      hx₀ hx₁ (StrongBundle.Dom.mem_smoothSet _ hs₀) (StrongBundle.Dom.mem_smoothSet _ hs₁)
      e) :
    D.transportLoc hX hf γ hγ hγD h₀ h₁ hs₀ hs₁ =
      (D.toLoc hf x₀ (h₀ ▸ hγD _) hs₀).trans
        (((toChartOr (D.isFredholm hf).toIsScFredholmSection
            (StrongBundle.Dom.mem_smoothSet _ hs₀) c hc hx₀).trans
          (e.trans (toChartOr (D.isFredholm hf).toIsScFredholmSection
            (StrongBundle.Dom.mem_smoothSet _ hs₁) c hc hx₁).symm)).trans
          (D.toLoc hf x₁ (h₁ ▸ hγD _) hs₁).symm) := by
  have key := orLocalTransportOfChart_transport_eq (D.isTame hX) D.exists_chart_univ
    (D.isFredholm hf) D.hasSections hU hUo (D.isScSmoothMap_liftPath hγ hγD) hγU
    (show D.liftPath γ hγD (pt1 0) = (⟨x₀, h₀ ▸ hγD _⟩ : D.carrier) from Subtype.ext h₀)
    (show D.liftPath γ hγD (pt1 1) = (⟨x₁, h₁ ▸ hγD _⟩ : D.carrier) from Subtype.ext h₁)
    (StrongBundle.Dom.mem_smoothSet _ hs₀) (StrongBundle.Dom.mem_smoothSet _ hs₁) hx₀ hx₁ he
  exact congrArg (fun T => (D.toLoc hf x₀ (h₀ ▸ hγD _) hs₀).trans
    (T.trans (D.toLoc hf x₁ (h₁ ▸ hγD _) hs₁).symm)) key

section Functor

variable (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)

/-! ### The functor `Γ_f` -/

/-- **The functor `Γ_f` on morphisms** (Theorem 6.6.13) for the local orientation sets:
`Γ_f([φ]) : Or_x^f ≃ Or_y^f` is the transport along `φ`. -/
def orFunctorMapLoc {x y : PathCat PX} (a : x ⟶ y) :
    OrxLoc hf x.pt x.smooth ≃ OrxLoc hf y.pt y.smooth :=
  (orLocalTransportLoc hX hf).functorMap a

/-- `Γ_f([φ])` is the transport along `φ`. -/
theorem orFunctorMapLoc_mk {x y : PathCat PX} (φ : ScPath PX x.pt y.pt) :
    orFunctorMapLoc hX hf (PathCat.homMk φ) =
      (orLocalTransportLoc hX hf).transport φ.toFun φ.isScSmoothMap φ.source φ.target x.smooth
        y.smooth :=
  rfl

/-- **`Γ_f` takes identities to identities.** -/
theorem orFunctorMapLoc_id (x : PathCat PX) : orFunctorMapLoc hX hf (𝟙 x) = Equiv.refl _ :=
  (orLocalTransportLoc hX hf).functorMap_id x

/-- **`Γ_f` takes compositions to composites.** -/
theorem orFunctorMapLoc_comp {x y z : PathCat PX} (a : x ⟶ y) (b : y ⟶ z) :
    orFunctorMapLoc hX hf (a ≫ b) =
      (orFunctorMapLoc hX hf a).trans (orFunctorMapLoc hX hf b) :=
  (orLocalTransportLoc hX hf).functorMap_comp a b

/-- **The functor `Γ_f : PX → O_f`** (Theorem 6.6.13) for the local orientation sets:
`x ↦ Or_x^f`, `[φ] ↦ Γ_f([φ])`. -/
def orFunctorLoc : PathCat PX ⥤ Type _ := (orLocalTransportLoc hX hf).functor

theorem orFunctorLoc_obj (x : PathCat PX) :
    (orFunctorLoc hX hf).obj x = OrxLoc hf x.pt x.smooth :=
  rfl

theorem orFunctorLoc_map_apply {x y : PathCat PX} (a : x ⟶ y) (o : OrxLoc hf x.pt x.smooth) :
    (orFunctorLoc hX hf).map a o = orFunctorMapLoc hX hf a o :=
  rfl

/-! ### Property (∗) -/

/-- **Property (∗), read in domains**: on the class of an sc-smooth path with all values in a
domain `W`, the map is the propagation in `W`, the transport of `f|W` read through the
identifications `Or_x^f ≃ Or_x^{f|W}`. -/
def IsStarPropertyDom
    (G : ∀ x y : PathCat PX, (x ⟶ y) → (OrxLoc hf x.pt x.smooth ≃ OrxLoc hf y.pt y.smooth)) :
    Prop :=
  ∀ (D : B.Dom) (x y : PathCat PX) (φ : ScPath PX x.pt y.pt) (hφD : ∀ q, φ.toFun q ∈ D.carrier),
    G x y (PathCat.homMk φ) =
      D.transportLoc hX hf φ.toFun φ.isScSmoothMap hφD φ.source φ.target x.smooth y.smooth

/-- **Property (∗) of Theorem 6.6.13** for the local orientation sets: for every domain `W`,
every chart `c` of `P|W`, every open `U ⊆ W` with the local propagation property for `f|W` in
`c`, every sc-smooth path `φ` between smooth points `x`, `y` with all values in `W` and
`φ([0, 1]) ⊆ U`, and every push-forward `e` along `φ` in `c`, the map `G([φ])` is `e` read
through `toChartOr` and the identifications `Or^f ≃ Or^{f|W}`. -/
def IsStarPropertyLoc
    (G : ∀ x y : PathCat PX, (x ⟶ y) → (OrxLoc hf x.pt x.smooth ≃ OrxLoc hf y.pt y.smooth)) :
    Prop :=
  ∀ (D : B.Dom) (c : StrongBundleChart (PX.restrictOpen D.isOpen)
      (pullbackProj P (Subtype.val : D.carrier → X))) (hc : D.bundle.IsChart c)
    (U : Set D.carrier), IsOpen U →
    ∀ (hU : HasLocalPropagation (D.sec f hf.isScSmooth.1)
        (D.isFredholm hf).toIsScFredholmSection c hc U)
      (x y : PathCat PX) (φ : ScPath PX x.pt y.pt) (hφD : ∀ q, φ.toFun q ∈ D.carrier)
      (hφU : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, D.liftPath φ.toFun hφD q ∈ U)
      (hx : (⟨x.pt, φ.source ▸ hφD _⟩ : D.carrier) ∈ c.φ.source)
      (hy : (⟨y.pt, φ.target ▸ hφD _⟩ : D.carrier) ∈ c.φ.source)
      (e : (chartPtOf c hc hx (StrongBundle.Dom.mem_smoothSet _ x.smooth)).Or
          (D.sec f hf.isScSmooth.1) (D.isFredholm hf).toIsScFredholmSection ≃
        (chartPtOf c hc hy (StrongBundle.Dom.mem_smoothSet _ y.smooth)).Or
          (D.sec f hf.isScSmooth.1) (D.isFredholm hf).toIsScFredholmSection),
      IsPush (D.sec f hf.isScSmooth.1) (D.isFredholm hf).toIsScFredholmSection c hc
        (D.liftPath φ.toFun hφD) (fun q hq => hU.subset (hφU q hq))
        (show D.liftPath φ.toFun hφD (pt1 0) = (⟨x.pt, φ.source ▸ hφD _⟩ : D.carrier) from
          Subtype.ext φ.source)
        (show D.liftPath φ.toFun hφD (pt1 1) = (⟨y.pt, φ.target ▸ hφD _⟩ : D.carrier) from
          Subtype.ext φ.target) hx hy (StrongBundle.Dom.mem_smoothSet _ x.smooth)
        (StrongBundle.Dom.mem_smoothSet _ y.smooth) e →
      G x y (PathCat.homMk φ) =
        (D.toLoc hf x.pt (φ.source ▸ hφD _) x.smooth).trans
          (((toChartOr (D.isFredholm hf).toIsScFredholmSection
              (StrongBundle.Dom.mem_smoothSet _ x.smooth) c hc hx).trans
            (e.trans (toChartOr (D.isFredholm hf).toIsScFredholmSection
              (StrongBundle.Dom.mem_smoothSet _ y.smooth) c hc hy).symm)).trans
            (D.toLoc hf y.pt (φ.target ▸ hφD _) y.smooth).symm)

variable {hX hf} in
/-- Property (∗) read in domains gives the text's form. -/
theorem IsStarPropertyDom.isStarPropertyLoc
    {G : ∀ x y : PathCat PX, (x ⟶ y) → (OrxLoc hf x.pt x.smooth ≃ OrxLoc hf y.pt y.smooth)}
    (hG : IsStarPropertyDom hX hf G) : IsStarPropertyLoc hf G :=
  fun D _ _ _ hUo hU x y φ hφD hφU hx hy _ he =>
    (hG D x y φ hφD).trans
      (D.transportLoc_eq_of_isPush hX hf hU hUo φ.isScSmoothMap hφD hφU φ.source φ.target
        x.smooth y.smooth hx hy he)

/-- **`Γ_f` has property (∗), read in domains** (`orLocalTransportLoc_transport_eq`). -/
theorem orFunctorMapLoc_isStarPropertyDom :
    IsStarPropertyDom hX hf fun _ _ a => orFunctorMapLoc hX hf a :=
  fun D x y φ hφD =>
    orLocalTransportLoc_transport_eq hX hf D φ.isScSmoothMap hφD φ.source φ.target x.smooth
      y.smooth

/-- **`Γ_f` has property (∗).** -/
theorem orFunctorMapLoc_isStarPropertyLoc :
    IsStarPropertyLoc hf fun _ _ a => orFunctorMapLoc hX hf a :=
  (orFunctorMapLoc_isStarPropertyDom hX hf).isStarPropertyLoc

/-- **Uniqueness of `Γ_f`** ("it is obvious that `Γ_f` is unique"): a family of bijections on
the morphisms of `PX` which takes compositions to composites and has property (∗) is `Γ_f`.
A path with `[0, 1]` in a good set is replaced by its reparametrization by the smooth
transition function, in the same class, which takes all its values in the good set. -/
theorem orFunctorMapLoc_unique
    (G : ∀ x y : PathCat PX, (x ⟶ y) → (OrxLoc hf x.pt x.smooth ≃ OrxLoc hf y.pt y.smooth))
    (hG_comp : ∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
      G x z (a ≫ b) = (G x y a).trans (G y z b))
    (hG : IsStarPropertyLoc hf G) : G = fun _ _ a => orFunctorMapLoc hX hf a := by
  refine (orLocalTransportLoc hX hf).functorMap_unique G hG_comp ?_
  intro U hU x y φ hφU
  obtain ⟨hUo, D, hUD, c, hc, hVo, hLP⟩ := id hU
  -- the reparametrized path
  have h₀' : smoothTransPath_or φ.toFun (pt1 0) = x.pt :=
    (congrArg (fun t => φ.toFun (pt1 t)) Real.smoothTransition.zero).trans φ.source
  have h₁' : smoothTransPath_or φ.toFun (pt1 1) = y.pt :=
    (congrArg (fun t => φ.toFun (pt1 t)) Real.smoothTransition.one).trans φ.target
  let ψ : ScPath PX x.pt y.pt :=
    ⟨smoothTransPath_or φ.toFun, isScSmoothMap_smoothTransPath_or φ.isScSmoothMap, h₀', h₁'⟩
  have hψφ : PathCat.homMk ψ = PathCat.homMk φ :=
    PathCat.mk_eq_mk_iff.2 ⟨_, isScHomotopyRel_reparam φ.isScSmoothMap
      Real.smoothTransition.contDiff Real.smoothTransition.zero Real.smoothTransition.one⟩
  have hψU : ∀ q, ψ.toFun q ∈ U := smoothTransPath_or_mem hφU
  have hψD : ∀ q, ψ.toFun q ∈ D.carrier := fun q => hUD (hψU q)
  have hψV : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1,
      D.liftPath ψ.toFun hψD q ∈ (Subtype.val ⁻¹' U : Set D.carrier) := fun q _ => hψU q
  have hx : (⟨x.pt, ψ.source ▸ hψD _⟩ : D.carrier) ∈ c.φ.source :=
    hLP.subset (show x.pt ∈ U from ψ.source ▸ hψU _)
  have hy : (⟨y.pt, ψ.target ▸ hψD _⟩ : D.carrier) ∈ c.φ.source :=
    hLP.subset (show y.pt ∈ U from ψ.target ▸ hψU _)
  obtain ⟨e, he⟩ := hLP.exists_isPush (D.liftPath ψ.toFun hψD)
    (D.isScSmoothMap_liftPath ψ.isScSmoothMap hψD) hψV
    (show D.liftPath ψ.toFun hψD (pt1 0) = (⟨x.pt, ψ.source ▸ hψD _⟩ : D.carrier) from
      Subtype.ext ψ.source)
    (show D.liftPath ψ.toFun hψD (pt1 1) = (⟨y.pt, ψ.target ▸ hψD _⟩ : D.carrier) from
      Subtype.ext ψ.target) hx hy (StrongBundle.Dom.mem_smoothSet _ x.smooth)
    (StrongBundle.Dom.mem_smoothSet _ y.smooth)
  rw [← hψφ, hG D c hc _ hVo hLP x y ψ hψD hψV hx hy e he,
    orLocalTransportLoc_push_eq hX hf hU D φ.isScSmoothMap hφU hψD φ.source φ.target x.smooth
      y.smooth]
  exact (D.transportLoc_eq_of_isPush hX hf hLP hVo ψ.isScSmoothMap hψD hψV ψ.source ψ.target
    x.smooth y.smooth hx hy he).symm

include hX in
/-- **2021 Theorem 6.6.13**, pp. 273–274, for the local orientation sets, for a tame M-polyfold
and a section with tame germ data: there is exactly one family of maps
`Γ_f([φ]) : Or_x^f ≃ Or_y^f` on the morphisms `[φ] : x ⟶ y` of `PX` which is a functor
(identities to identities, compositions to composites) and has property (∗); it is
`orFunctorMapLoc` (packaged as `orFunctorLoc`). -/
theorem theorem_6_6_13_loc :
    ∃! G : ∀ x y : PathCat PX, (x ⟶ y) →
        (OrxLoc hf x.pt x.smooth ≃ OrxLoc hf y.pt y.smooth),
      (∀ x, G x x (𝟙 x) = Equiv.refl _) ∧
      (∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
        G x z (a ≫ b) = (G x y a).trans (G y z b)) ∧
      IsStarPropertyLoc hf G :=
  ⟨fun _ _ a => orFunctorMapLoc hX hf a,
    ⟨orFunctorMapLoc_id hX hf, fun _ _ _ => orFunctorMapLoc_comp hX hf,
      orFunctorMapLoc_isStarPropertyLoc hX hf⟩,
    fun G ⟨_, hG_comp, hG⟩ => orFunctorMapLoc_unique hX hf G hG_comp hG⟩

/-- **Theorem 6.6.13 with property (∗) read in domains**: exactly one functorial family of
maps is the transport of `f|W` on the paths in every domain `W`. -/
theorem theorem_6_6_13_loc_dom :
    ∃! G : ∀ x y : PathCat PX, (x ⟶ y) →
        (OrxLoc hf x.pt x.smooth ≃ OrxLoc hf y.pt y.smooth),
      (∀ x, G x x (𝟙 x) = Equiv.refl _) ∧
      (∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
        G x z (a ≫ b) = (G x y a).trans (G y z b)) ∧
      IsStarPropertyDom hX hf G :=
  ⟨fun _ _ a => orFunctorMapLoc hX hf a,
    ⟨orFunctorMapLoc_id hX hf, fun _ _ _ => orFunctorMapLoc_comp hX hf,
      orFunctorMapLoc_isStarPropertyDom hX hf⟩,
    fun G ⟨_, hG_comp, hG⟩ => orFunctorMapLoc_unique hX hf G hG_comp hG.isStarPropertyLoc⟩

/-! ### Orientability (Definitions 6.6.14 and 6.6.15) and orientations (Definition 6.6.16) -/

/-- **Definition 6.6.14, orientability**, for the local orientation sets: for every pair of
smooth points `x`, `y` and any two classes `[φ], [ψ]` of sc-smooth paths from `x` to `y`,
`Γ_f([φ]) = Γ_f([ψ])`. -/
def IsOrientableSectionLoc : Prop :=
  ∀ (x y : PathCat PX) (a b : x ⟶ y), orFunctorMapLoc hX hf a = orFunctorMapLoc hX hf b

/-- **Definition 6.6.16, an orientation of `f`**, for the local orientation sets: a map
`y ↦ o_y ∈ Or_y^f` on the smooth points which near every smooth point is a continuous
orientation: every smooth point has an open neighbourhood `V` such that the propagation along
the sc-smooth paths in `V` carries `o` along. -/
def IsSectionOrientationLoc (o : ∀ y (hy : y ∈ PX.smoothSet), OrxLoc hf y hy) : Prop :=
  ∀ x ∈ PX.smoothSet, ∃ V : Set X, x ∈ V ∧ (orLocalTransportLoc hX hf).IsContOn V o

/-- **Definition 6.6.16 in terms of `Γ_f`**: `y ↦ o_y` is an orientation of `f` iff
`Γ_f([φ]) o_x = o_y` for every morphism `[φ] : x ⟶ y` of `PX`. -/
theorem isSectionOrientationLoc_iff (o : ∀ y (hy : y ∈ PX.smoothSet), OrxLoc hf y hy) :
    IsSectionOrientationLoc hX hf o ↔
      ∀ (x y : PathCat PX) (a : x ⟶ y),
        orFunctorMapLoc hX hf a (o x.pt x.smooth) = o y.pt y.smooth :=
  (LocalTransport.isOrientation_iff_forall_exists_isContOn o).symm

/-- An orientation is a map carried along by the transport along every sc-smooth path. -/
theorem isSectionOrientationLoc_iff_isContOn_univ
    (o : ∀ y (hy : y ∈ PX.smoothSet), OrxLoc hf y hy) :
    IsSectionOrientationLoc hX hf o ↔ (orLocalTransportLoc hX hf).IsContOn univ o :=
  (LocalTransport.isOrientation_iff_forall_exists_isContOn o).symm.trans
    (LocalTransport.isOrientation_iff_isContOn_univ o)

/-- **An orientation is a map which is a continuous orientation in every domain**: `y ↦ o_y` is
an orientation of `f` iff for every domain `W` the family read in `W` is carried along by the
transport of `f|W` along all sc-smooth paths in `W`. -/
theorem isSectionOrientationLoc_iff_forall_dom
    (o : ∀ y (hy : y ∈ PX.smoothSet), OrxLoc hf y hy) :
    IsSectionOrientationLoc hX hf o ↔
      ∀ D : B.Dom, IsContOrOn (D.transport hX hf) univ (D.pushLoc hf o) :=
  (isSectionOrientationLoc_iff_isContOn_univ hX hf o).trans
    (isContOn_univ_iff_forall_dom hX hf o)

/-- **An orientation is a map which in every domain is an orientation in the sense of
Definition 6.6.16**: `y ↦ o_y` is an orientation of `f` iff for every domain `W` the family
read in `W` is a continuous orientation of `f|W` over every orientable neighbourhood in `W`
(`IsSectionOrientation` for the restriction of `f` to `W`). -/
theorem isSectionOrientationLoc_iff_forall_dom_isSectionOrientation
    (o : ∀ y (hy : y ∈ PX.smoothSet), OrxLoc hf y hy) :
    IsSectionOrientationLoc hX hf o ↔
      ∀ D : B.Dom, IsSectionOrientation (D.sec f hf.isScSmooth.1)
        (D.isFredholm hf).toIsScFredholmSection (D.pushLoc hf o) := by
  refine (isSectionOrientationLoc_iff_forall_dom hX hf o).trans (forall_congr' fun D => ?_)
  refine Iff.trans ?_ (isSectionOrientation_iff_of_chart (D.isTame hX) D.exists_chart_univ
    (D.isFredholm hf) D.hasSections (D.pushLoc hf o)).symm
  exact (LocalTransport.isOrientation_iff_isContOn_univ (L := D.transport hX hf)
    (D.pushLoc hf o)).symm

/-- **Definitions 6.6.14 and 6.6.15 are equivalent** for the local orientation sets: `f` is
orientable iff there is a map `y ↦ o_y ∈ Or_y^f` which near every smooth point is a continuous
orientation. -/
theorem isOrientableSectionLoc_iff :
    IsOrientableSectionLoc hX hf ↔
      ∃ o : ∀ y (hy : y ∈ PX.smoothSet), OrxLoc hf y hy, IsSectionOrientationLoc hX hf o :=
  (LocalTransport.isOrientable_iff_exists_isOrientation
    (L := orLocalTransportLoc hX hf) fun _ hy => exists_two_orxLoc hf hy).trans
    (exists_congr fun o => (isSectionOrientationLoc_iff hX hf o).symm)

/-- **`f` has an orientation (Definition 6.6.16) iff it is orientable (Definition 6.6.14).** -/
theorem exists_isSectionOrientationLoc_iff :
    (∃ o, IsSectionOrientationLoc hX hf o) ↔ IsOrientableSectionLoc hX hf :=
  (isOrientableSectionLoc_iff hX hf).symm

/-- **If any two sc-smooth paths of `X` with the same end points are sc-smoothly homotopic with
end points fixed, every sc-Fredholm section with tame germ data over `X` is orientable.** -/
theorem isOrientableSectionLoc_of_hom_eq (hP : ∀ {x y : PathCat PX} (a b : x ⟶ y), a = b) :
    IsOrientableSectionLoc hX hf := fun _ _ a b =>
  congrArg (fun c => orFunctorMapLoc hX hf c) (hP a b)

variable {hX hf}

/-- **Two orientations which agree at a point agree on its path component.** -/
theorem IsSectionOrientationLoc.apply_eq_iff
    {o o' : ∀ y (hy : y ∈ PX.smoothSet), OrxLoc hf y hy}
    (ho : IsSectionOrientationLoc hX hf o) (ho' : IsSectionOrientationLoc hX hf o')
    {x y : PathCat PX} (a : x ⟶ y) :
    o x.pt x.smooth = o' x.pt x.smooth ↔ o y.pt y.smooth = o' y.pt y.smooth :=
  LocalTransport.IsOrientation.apply_eq_iff
    ((LocalTransport.isOrientation_iff_forall_exists_isContOn o).2 ho)
    ((LocalTransport.isOrientation_iff_forall_exists_isContOn o').2 ho') a

/-- **On the path component of a point there are exactly two orientations**: for an orientation
`o` and a smooth point `x` there is an orientation `o'` which differs from `o` at every point
joined to `x` by an sc-smooth path and agrees with `o` at the other points, and on the path
component of `x` every orientation agrees with `o` or with `o'`. -/
theorem IsSectionOrientationLoc.exists_two
    {o : ∀ y (hy : y ∈ PX.smoothSet), OrxLoc hf y hy}
    (ho : IsSectionOrientationLoc hX hf o) (x : PathCat PX) :
    ∃ o' : ∀ y (hy : y ∈ PX.smoothSet), OrxLoc hf y hy,
      IsSectionOrientationLoc hX hf o' ∧
      (∀ y : PathCat PX, Nonempty (x ⟶ y) → o' y.pt y.smooth ≠ o y.pt y.smooth) ∧
      (∀ y : PathCat PX, IsEmpty (x ⟶ y) → o' y.pt y.smooth = o y.pt y.smooth) ∧
      ∀ o'' : ∀ y (hy : y ∈ PX.smoothSet), OrxLoc hf y hy,
        IsSectionOrientationLoc hX hf o'' →
        (∀ y : PathCat PX, Nonempty (x ⟶ y) → o'' y.pt y.smooth = o y.pt y.smooth) ∨
        (∀ y : PathCat PX, Nonempty (x ⟶ y) → o'' y.pt y.smooth = o' y.pt y.smooth) := by
  obtain ⟨o', ho', h1, h2, h3⟩ := LocalTransport.IsOrientation.exists_two
    ((LocalTransport.isOrientation_iff_forall_exists_isContOn o).2 ho)
    (fun _ hy => exists_two_orxLoc hf hy) x
  exact ⟨o', (LocalTransport.isOrientation_iff_forall_exists_isContOn o').1 ho', h1, h2,
    fun o'' ho'' => h3 o'' ((LocalTransport.isOrientation_iff_forall_exists_isContOn o'').2 ho'')⟩

end Functor

end Polyfold
