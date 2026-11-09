import Polyfold
/-! Blind formalization of V8_27 (the text's Part II, §8.5 = 2017 §8.4, Definition 8.5.1 = 2017
Definition 8.8, p. 383 / 2017 p. 275).

Text: an sc-smooth functor `F : Y → X` between ep-groupoids is a proper covering functor if
(1) `F : Y → X` on objects is a surjective local sc-diffeomorphism; (2) for every `x ∈ X` the
preimage `F⁻¹(x)` is finite and there are an open `U(x)` and mutually disjoint open `U(y)`,
`y ∈ F⁻¹(x)`, with `F : U(y) → U(x)` sc-diffeomorphisms and `F⁻¹(U(x)) = ⋃_{y ∈ F⁻¹(x)} U(y)`;
(3) `𝐘 → 𝐗 ₛ×_F Y`, `φ ↦ (F(φ), s(φ))`, is an sc-diffeomorphism.

Choices:
- This item is a definition.  Setting: ep-groupoids `Y : EpGroupoid ObjY MorY`,
  `X : EpGroupoid ObjX MorX` (all spaces in `Type`, universe 0), `F` a project `EpFunctor Y X`
  (V7_9: the text's sc-smooth functor).
- (1): `Function.Surjective` and the project's `MPolyfold.IsLocalScDiffeo` (V7_3).
- (2): `U(x) ∋ x` open; `U(y)` given as a family `V : ObjY → Set ObjY` (only its values on
  `F⁻¹(x)` matter), each open and containing `y`; "mutually disjoint" = pairwise disjoint on
  `F⁻¹(x)`; "`F : U(y) → U(x)` is an sc-diffeomorphism" = some `g` with the project's
  `MPolyfold.IsScDiffeoOn F g (U y) (U x)` (fields read with `#print`: sc-smooth on `U(y)`, `g`
  sc-smooth on `U(x)`, mapping into each other, mutually inverse — a bijection `U(y) ≅ U(x)`).
- (3): `𝐗 ₛ×_F Y = {(φ, y) | s(φ) = F(y)}` (`MPolyfold.fibredProduct X.src F.obj`) with its natural
  M-polyfold structure, read (as in `RoundTrip/Blind/V7_3.lean` for `𝐗 ₛ×ₜ 𝐗`) as a
  sub-M-polyfold of the product `𝐗 × Y` (`MPolyfold.prod`, `MPolyfold.subPolyfold`; the
  paracompactness instances they take are existentially quantified, true as M-polyfolds are
  metrizable); `φ ↦ (F(φ), s(φ))` lands there by `s(F φ) = F(s φ)`.  "sc-diffeomorphism":
  `IsScDiffeoOn` on `univ`, `univ` with some inverse `g`.
- B: the project's `EpFunctor.IsProperCovering F` (fields read with `#print`) iff my
  `IsProperCoveringB F`.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_27
open Polyfold

section
variable {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}

/-- The map `𝐘 → 𝐗 ₛ×_F Y`, `φ ↦ (F(φ), s(φ))`. -/
def LB (F : EpFunctor Y X) (φ : MorY) : MPolyfold.fibredProduct X.src F.obj :=
  ⟨(F.mor φ, Y.src φ), F.src_mor φ⟩

/-- **Definition 8.5.1**: `F` is a proper covering functor. -/
def IsProperCoveringB (F : EpFunctor Y X) : Prop :=
  -- (1) a surjective local sc-diffeomorphism on objects
  Function.Surjective F.obj ∧ Y.PObj.IsLocalScDiffeo X.PObj F.obj ∧
  -- (2) finite, evenly covered fibres
  (∀ x : ObjX, (F.obj ⁻¹' {x}).Finite ∧
    ∃ (U : Set ObjX) (V : ObjY → Set ObjY), IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ F.obj ⁻¹' {x}, IsOpen (V y) ∧ y ∈ V y ∧
        ∃ g : ObjX → ObjY, Y.PObj.IsScDiffeoOn X.PObj F.obj g (V y) U) ∧
      (F.obj ⁻¹' {x}).PairwiseDisjoint V ∧
      F.obj ⁻¹' U = ⋃ y ∈ F.obj ⁻¹' {x}, V y) ∧
  -- (3) `φ ↦ (F(φ), s(φ))` is an sc-diffeomorphism `𝐘 → 𝐗 ₛ×_F Y`
  (∃ (_ : ParacompactSpace (MorX × ObjY))
      (hA : (X.PMor.prod Y.PObj).IsSubMPolyfold (MPolyfold.fibredProduct X.src F.obj))
      (_ : ParacompactSpace (MPolyfold.fibredProduct X.src F.obj))
      (g : MPolyfold.fibredProduct X.src F.obj → MorY),
    Y.PMor.IsScDiffeoOn ((X.PMor.prod Y.PObj).subPolyfold hA) (LB F) g Set.univ Set.univ)

end

/-- Definition 8.5.1: the project's proper covering functors are the text's. -/
def B : Prop :=
  ∀ (ObjY MorY : Type) [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    (ObjX MorX : Type) [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX) (F : EpFunctor Y X),
    F.IsProperCovering ↔ IsProperCoveringB F

end RoundTrip.V8_27
