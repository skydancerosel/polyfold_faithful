import Polyfold
/-! Blind formalization of V8_28 (the text's Part II, §8.5 = 2017 §8.4, after Definition 8.5.1 =
2017 Definition 8.8, pp. 383 ff. / 2017 pp. 275–276).

Text: the sc-diffeomorphism `L : 𝐘 → 𝐗 ₛ×_F Y`, `φ ↦ (F(φ), s(φ))`, preserves the degeneracy
index, `d_𝐘(φ) = d_{𝐗 ₛ×_F Y}(F(φ), s(φ))`.  The fibred product is a sub-M-polyfold of `𝐗 × Y`,
which has `d_{𝐗×Y}(φ, y) = d_𝐗(φ) + d_Y(y)`.  Since `F` and `s` are local sc-diffeomorphisms,
`d_{𝐗×Y}(F(φ), s(φ)) = d_𝐗(F(φ)) + d_Y(s(φ)) = 2 d_𝐘(φ)`, hence
`d_{𝐗 ₛ×_F Y}(F(φ), s(φ)) = ½ d_{𝐗×Y}(F(φ), s(φ))`.

Choices:
- Setting as in my `RoundTrip/Blind/V8_27.lean`: `F : EpFunctor Y X` between ep-groupoids, all
  spaces in `Type`; the passage follows Definition 8.5.1 and speaks of "the sc-diffeomorphism"
  of its condition (3), so the hypothesis is that `F` is a proper covering functor (the
  project's `EpFunctor.IsProperCovering`, characterized in V8_27).
- `𝐗 ₛ×_F Y` with its M-polyfold structure as a sub-M-polyfold of `𝐗 × Y` (`MPolyfold.prod`,
  `MPolyfold.subPolyfold`, as in V8_27 and V7_3; the paracompactness instances and the
  sub-M-polyfold property are existentially quantified — "the fibred product is a
  sub-M-polyfold of `𝐗 × Y`" is thereby asserted; the structure does not depend on the
  witnesses).  `L` is my `LB` (copied from V8_27).
- Degeneracy indices: the project's `MPolyfold.degIndex` (Definition 2.22 of Part I: the
  minimum over the charts around the point), for `𝐘`, `𝐗`, `Y`, `𝐗 × Y` and `𝐗 ₛ×_F Y`; values in
  `ℕ`, so "`= ½ d_{𝐗×Y}`" is written `2 · d_{𝐗 ₛ×_F Y} = d_{𝐗×Y}`.
- B is the conjunction of all displayed claims: (a) `d_𝐘(φ) = d_{𝐗 ₛ×_F Y}(L φ)`; (b) the product
  formula for every `(φ, y) ∈ 𝐗 × Y`; (c) `d_𝐗(F(φ)) = d_𝐘(φ)` and `d_Y(s(φ)) = d_𝐘(φ)` (the text's
  "since `F` and `s` are local sc-diffeomorphisms", `F` on morphisms); (d)
  `d_{𝐗×Y}(F(φ), s(φ)) = 2 d_𝐘(φ)`; (e) `2 d_{𝐗 ₛ×_F Y}(L φ) = d_{𝐗×Y}(F(φ), s(φ))`.
- Doubtful: the product formula (b) for arbitrary M-polyfolds with the chart-minimum
  degeneracy index (non-product charts of `𝐗 × Y` might in principle give smaller values); I
  formalize it literally as stated.
-/
namespace RoundTrip.V8_28
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

end

/-- The degeneracy index of `𝐗 ₛ×_F Y` for a proper covering functor `F`: `L` preserves it, and it
is half the degeneracy index of `𝐗 × Y` at the points `(F(φ), s(φ))`. -/
def B : Prop :=
  ∀ (ObjY MorY : Type) [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    (ObjX MorX : Type) [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX) (F : EpFunctor Y X),
    F.IsProperCovering →
    ∃ (_ : ParacompactSpace (MorX × ObjY))
      (hA : (X.PMor.prod Y.PObj).IsSubMPolyfold (MPolyfold.fibredProduct X.src F.obj))
      (_ : ParacompactSpace (MPolyfold.fibredProduct X.src F.obj)),
      -- (a) `L` preserves the degeneracy index
      (∀ φ : MorY, Y.PMor.degIndex φ = ((X.PMor.prod Y.PObj).subPolyfold hA).degIndex (LB F φ)) ∧
      -- (b) the degeneracy index of the product `𝐗 × Y`
      (∀ p : MorX × ObjY,
        (X.PMor.prod Y.PObj).degIndex p = X.PMor.degIndex p.1 + Y.PObj.degIndex p.2) ∧
      -- (c) `F` (on morphisms) and `s` preserve the degeneracy index
      (∀ φ : MorY, X.PMor.degIndex (F.mor φ) = Y.PMor.degIndex φ ∧
        Y.PObj.degIndex (Y.src φ) = Y.PMor.degIndex φ) ∧
      -- (d) `d_{𝐗×Y}(F(φ), s(φ)) = 2 d_𝐘(φ)`
      (∀ φ : MorY, (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) = 2 * Y.PMor.degIndex φ) ∧
      -- (e) `d_{𝐗 ₛ×_F Y}(F(φ), s(φ)) = ½ d_{𝐗×Y}(F(φ), s(φ))`
      (∀ φ : MorY, 2 * ((X.PMor.prod Y.PObj).subPolyfold hA).degIndex (LB F φ) =
        (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ))

end RoundTrip.V8_28
