import Polyfold
/-! Blind formalization of V8_37 (the 2017 book, arXiv 1707.08941, Part II, §8.4, Definition 8.10,
p. 285; 2021: Definition 8.5.9, p. 394).

Text: let `(W, μ)` and `(V, τ)` be strong bundles over the ep-groupoids `Y` and `X`, `P : W → Y`,
`Q : V → X`.  A proper strong bundle covering functor is a strong bundle map `A` (in particular
fibrewise linear) with `Q ∘ A = F ∘ P` and (1) `A` is surjective and a local strong bundle
isomorphism covering an sc-smooth proper covering functor `F : Y → X`; (2) `F⁻¹(x)` is finite for
every `x`, and there are open `U(x)` and mutually disjoint `U(y)`, `y ∈ F⁻¹(x)`, with
`A : W|U(y) → V|U(x)` a strong bundle isomorphism for every `y ∈ F⁻¹(x)` and
`F⁻¹(U(x)) = ⋃ U(y)`; (3) `𝐖 → 𝐕 ₛ×_A W`, `(ψ, w) ↦ ((F(ψ), A(w)), w)`, is a strong bundle
isomorphism covering the sc-diffeomorphism `𝐘 → 𝐗 ₛ×_F Y`, `ψ ↦ (F(ψ), s(ψ))`, where the
projection `𝐕 ₛ×_A W → 𝐗 ₛ×_F Y` is `((φ, v), w) ↦ (φ, P(w))`.

Choices:
- This item is a definition; B states that my transcription `IsPSBCoveringB` of it is the project's
  `EpStrongBundle.IsProperStrongBundleCovering`.  Setting: all spaces in `Type` (the project's
  definition has them in one universe), Hausdorff paracompact; `BW : StrongBundle Y.PObj P`,
  `BV : StrongBundle X.PObj Q` the project's strong bundles over M-polyfolds (Part I), fibres with
  their vector space structures as instances; `EW : EpStrongBundle Y BW`, `EV : EpStrongBundle X BV`
  the project's Definition 8.3.1 (`#print`ed: `μ : 𝐘 ₛ×_P W → W` a strong bundle map covering `t`,
  surjective local sc-diffeomorphism, unit and composition laws); the paracompactness of
  `𝐘 ₛ×_P W`, `𝐗 ₛ×_Q V` is an instance argument, as for the project's `toEpGroupoid`.
- "A strong bundle map `A` with `Q ∘ A = F ∘ P`", between strong bundles over ep-groupoids: read as
  Definition 8.3.2 (V8.23), the project's `EpStrongBundle.IsMap EW EV F A` (`#print`ed: a Part I
  strong bundle map `A : W → V` covering `F` — `Q ∘ A = F ∘ P`, linear on fibres, sc-smooth on
  `W[0]` and on `W[1]` — with `A(μ(γ, w)) = τ(F(γ), A(w))`).  (Alternative reading: only a Part I
  strong bundle map, without the equivariance, which the 2021 edition adds as condition (0),
  V8.50.)  The project's definition takes `A` as an `EpFunctor` of the functorial picture with the
  strong bundle functor property (Definition 8.3.3); by V8.25 these are the same data, so B
  compares `IsPSBCoveringB A` with the existence of such a functor with object map `A`.
- `F`: an `EpFunctor` with the project's `IsProperCovering` (= Definition 8.5.1, see V8_29).
- "Strong bundle isomorphism `A : W|U → V|U'`" (in "local strong bundle isomorphism" and in (2)):
  the project's `StrongBundle.IsStrongBundleIsoOn` (`#print`ed: `F : U → U'` an sc-diffeomorphism,
  and `A : P⁻¹(U) → Q⁻¹(U')` an sc-diffeomorphism on level `[0]` and on level `[1]`; with `A`
  fibrewise linear its inverse is then a strong bundle map).  "Local": every `y ∈ Y` has an open
  `U ∋ y` and `U'` with `A : W|U → V|U'` a strong bundle isomorphism.
- (3): `𝐖` is the pull-back strong bundle `𝐘 ₛ×_P W → 𝐘` of `BW` along `s` (the project's
  `StrongBundle.pullback`, Part I Proposition 2.54).  `𝐕 ₛ×_A W = {((φ, v), w) | s(φ) = Q(v),
  v = A(w)}`: its strong bundle structure over `𝐗 ₛ×_F Y` is not described; I take the only natural
  one, `((φ, v), w) ↦ ((φ, P(w)), w)` identifying it with the pull-back of `BW` along
  `pr₂ : 𝐗 ₛ×_F Y → Y` (fibre `W_y` over `(φ, y)`; the text's projection becomes the pull-back
  projection, and the map becomes `(ψ, w) ↦ ((F(ψ), s(ψ)), w)`).  `𝐗 ₛ×_F Y` carries its
  sub-M-polyfold structure in `𝐗 × Y` (as in Definition 8.5.1).  The smoothness proofs and
  paracompactness instances these constructions need are existentially quantified (true;
  irrelevant as proofs).  "Strong bundle isomorphism covering `L_F`": the project's
  `StrongBundle.IsStrongBundleIso` (`#print`ed: strong bundle maps both ways, covering `L_F` and
  some `g`, mutually inverse).
- Nothing looks false to me.
-/
namespace RoundTrip.V8_37
open Polyfold

section
variable {ObjY MorY ObjX MorX : Type}
  [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → ObjY}
  [∀ y : ObjY, AddCommGroup (P ⁻¹' {y})] [∀ y : ObjY, Module ℝ (P ⁻¹' {y})]
  {BW : StrongBundle Y.PObj P} [ParacompactSpace (pullbackSpace P Y.src)]
  {V : Type} [TopologicalSpace V] [T2Space V] [ParacompactSpace V] {Q : V → ObjX}
  [∀ x : ObjX, AddCommGroup (Q ⁻¹' {x})] [∀ x : ObjX, Module ℝ (Q ⁻¹' {x})]
  {BV : StrongBundle X.PObj Q} [ParacompactSpace (pullbackSpace Q X.src)]

/-- The map `𝐖 → 𝐕 ₛ×_A W`, `(ψ, w) ↦ ((F(ψ), A(w)), w)`, read on the pull-back of `P` along
`pr₂ : 𝐗 ₛ×_F Y → Y` as `(ψ, w) ↦ ((F(ψ), s(ψ)), w)`. -/
def liftB (F : EpFunctor Y X) (q : pullbackSpace P Y.src) : pullbackSpace P F.fibredSnd :=
  ⟨(F.fibredMap q.1.1, q.1.2), q.2⟩

/-- **Definition 8.5.9 (2017: 8.10)**: `A : W → V` is a proper strong bundle covering functor over
`F : Y → X`. -/
def IsPSBCoveringB (EW : EpStrongBundle Y BW) (EV : EpStrongBundle X BV) (F : EpFunctor Y X)
    (A : W → V) : Prop :=
  ∃ hA : EW.IsMap EV F A,
    -- `Q ∘ A = F ∘ P`
    (∀ w : W, Q (A w) = F.obj (P w)) ∧
    -- (1)
    Function.Surjective A ∧ F.IsProperCovering ∧
    (∀ y : ObjY, ∃ (U : Set ObjY) (U' : Set ObjX), IsOpen U ∧ y ∈ U ∧
      BW.IsStrongBundleIsoOn BV hA.isStrongBundleMap U U') ∧
    -- (2)
    (∀ x : ObjX, (F.obj ⁻¹' {x}).Finite ∧
      ∃ (U : Set ObjX) (Uy : ObjY → Set ObjY), IsOpen U ∧ x ∈ U ∧
        (F.obj ⁻¹' {x}).PairwiseDisjoint Uy ∧
        (∀ y ∈ F.obj ⁻¹' {x}, IsOpen (Uy y) ∧ y ∈ Uy y ∧
          BW.IsStrongBundleIsoOn BV hA.isStrongBundleMap (Uy y) U) ∧
        F.obj ⁻¹' U = ⋃ y ∈ F.obj ⁻¹' {x}, Uy y) ∧
    -- (3)
    ∃ (hsY : Y.PMor.IsScSmoothMap Y.PObj Y.src) (_ : ParacompactSpace (MorX × ObjY))
      (hS : (X.PMor.prod Y.PObj).IsSubMPolyfold (MPolyfold.fibredProduct X.src F.obj))
      (_ : ParacompactSpace (MPolyfold.fibredProduct X.src F.obj))
      (hpr : ((X.PMor.prod Y.PObj).subPolyfold hS).IsScSmoothMap Y.PObj F.fibredSnd)
      (_ : ParacompactSpace (pullbackSpace P F.fibredSnd))
      (g : MPolyfold.fibredProduct X.src F.obj → MorY)
      (Ψ : pullbackSpace P F.fibredSnd → pullbackSpace P Y.src),
      (BW.pullback hsY).IsStrongBundleIso (BW.pullback hpr) F.fibredMap (liftB F) g Ψ

end

/-- Definition 8.5.9: `A : W → V` is a proper strong bundle covering functor over `F` (my
transcription) iff it is the object map of a project `IsProperStrongBundleCovering` functor. -/
def B : Prop :=
  ∀ (ObjY MorY ObjX MorX : Type)
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → ObjY)
    [∀ y : ObjY, AddCommGroup (P ⁻¹' {y})] [∀ y : ObjY, Module ℝ (P ⁻¹' {y})]
    (BW : StrongBundle Y.PObj P) [ParacompactSpace (pullbackSpace P Y.src)]
    (V : Type) [TopologicalSpace V] [T2Space V] [ParacompactSpace V] (Q : V → ObjX)
    [∀ x : ObjX, AddCommGroup (Q ⁻¹' {x})] [∀ x : ObjX, Module ℝ (Q ⁻¹' {x})]
    (BV : StrongBundle X.PObj Q) [ParacompactSpace (pullbackSpace Q X.src)]
    (EW : EpStrongBundle Y BW) (EV : EpStrongBundle X BV) (F : EpFunctor Y X) (A : W → V),
    IsPSBCoveringB EW EV F A ↔
      ∃ A' : EpFunctor EW.toEpGroupoid EV.toEpGroupoid,
        A'.obj = A ∧ EW.IsProperStrongBundleCovering EV F A'

end RoundTrip.V8_37
