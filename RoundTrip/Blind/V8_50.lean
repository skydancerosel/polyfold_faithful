import Polyfold
/-! Blind formalization of V8_50 (the 2021 book, Part II, §8.5, Definition 8.5.9, p. 394; 2017:
Definition 8.10, p. 285; condition (0) new in 2021).

Text: for strong bundles `(W, μ)` over `Y` and `(V, τ)` over `X` and an ep-functor `F : Y → X`, a
strong bundle map `A : W → V` with `Q ∘ A = F ∘ P` is a proper strong bundle covering functor
if (0) `τ(F(ψ), A(w)) = A(μ(ψ, w))`, and (1)–(3) of the 2017 definition hold.

Choices:
- This item is a definition.  B says that the project's
  `EpStrongBundle.IsProperStrongBundleCovering2021 EW EV F A` (for a map `A : W → V`) is the
  text's notion, written out on the right of the `↔`.
- Setting: universe 0; `Y : EpGroupoid ObjY MorY`, `X : EpGroupoid ObjX MorX`, `W`, `V : Type`
  with their topologies, `P : W → ObjY`, `Q : V → ObjX` with the linear structures on the
  fibres, Part I strong bundles `BW`, `BV` over the object M-polyfolds, `EW`, `EV` the strong
  bundles over the ep-groupoids (`μ = EW.μ`, `τ = EV.μ`, 2017 Definition 8.4), `F` an
  `EpFunctor` (sc-smooth functor, Definition 7.7).  The instances
  `ParacompactSpace (𝐘 ₛ×_P W)` and `ParacompactSpace (𝐗 ₛ×_Q V)` are hypotheses: the project
  needs them to form the ep-groupoids `(W, 𝐖)`, `(V, 𝐕)` of the 2017 definition (in the text
  these are M-polyfolds, paracompact by definition).
- "strong bundle map `A : W → V`": Part I's `BW.IsStrongBundleMap BV F.obj A` (fibrewise linear,
  sc-smooth on `W[0]` and `W[1]`, covering `F` on objects); "`Q ∘ A = F ∘ P`" stated separately
  (it is also part of the covering property).
- (0): for every morphism `ψ` of `Y` and `w` with `P(w) = s(ψ)`,
  `τ(F(ψ), A(w)) = A(μ(ψ, w))`; the proof that `(F(ψ), A(w))` lies in `𝐗 ₛ×_Q V` is taken as a
  hypothesis `hv` (it always holds).
- "(1)–(3) of the 2017 definition hold": the text of 2017 Definition 8.10 is not quoted.  In 2017
  `A` is a functor `(W, 𝐖) → (V, 𝐕)`; by (0) the map `A` defines the functor
  `Â(ψ, w) = (F(ψ), A(w))` (this is what makes `A` "a proper strong bundle covering functor").
  I read "(1)–(3) hold" as: there is a functor `Â : (W, 𝐖) → (V, 𝐕)` (an `EpFunctor`) with
  `Â = A` on objects and `Â(ψ, w) = (F(ψ), A(w))` on morphisms which satisfies 2017 Definition
  8.10, the project's `EpStrongBundle.IsProperStrongBundleCovering` (I use the project's
  formalization of the 2017 definition for the referenced conditions).  That structure also
  contains its preamble (`Â` a strong bundle functor, i.e. a strong bundle map on objects and on
  morphisms covering `F`); for the functor induced by a strong bundle map this should be
  automatic, but it is an extra requirement on the right-hand side, flagged here.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_50
open Polyfold

/-- Definition 8.5.9 (2021): a strong bundle map `A` with `Q ∘ A = F ∘ P` is a proper strong
bundle covering functor iff (0) holds and the induced functor satisfies 2017 Definition 8.10. -/
def B : Prop :=
  ∀ (ObjY MorY : Type) [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY] (Y : EpGroupoid ObjY MorY)
    (ObjX MorX : Type) [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX] (X : EpGroupoid ObjX MorX)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → ObjY)
    [∀ y, AddCommGroup (P ⁻¹' {y})] [∀ y, Module ℝ (P ⁻¹' {y})] (BW : StrongBundle Y.PObj P)
    [ParacompactSpace (pullbackSpace P Y.src)]
    (V : Type) [TopologicalSpace V] [T2Space V] [ParacompactSpace V] (Q : V → ObjX)
    [∀ x, AddCommGroup (Q ⁻¹' {x})] [∀ x, Module ℝ (Q ⁻¹' {x})] (BV : StrongBundle X.PObj Q)
    [ParacompactSpace (pullbackSpace Q X.src)]
    (EW : EpStrongBundle Y BW) (EV : EpStrongBundle X BV) (F : EpFunctor Y X) (A : W → V),
    EW.IsProperStrongBundleCovering2021 EV F A ↔
      (BW.IsStrongBundleMap BV F.obj A ∧
        (∀ w : W, Q (A w) = F.obj (P w)) ∧
        -- (0) `τ(F(ψ), A(w)) = A(μ(ψ, w))`
        (∀ (ψ : MorY) (w : W) (hw : P w = Y.src ψ) (hv : Q (A w) = X.src (F.mor ψ)),
          EV.μ ⟨(F.mor ψ, A w), hv⟩ = A (EW.μ ⟨(ψ, w), hw⟩)) ∧
        -- (1)–(3) of 2017 Definition 8.10, for the induced functor `Â(ψ, w) = (F(ψ), A(w))`
        ∃ Â : EpFunctor EW.toEpGroupoid EV.toEpGroupoid,
          Â.obj = A ∧
          (∀ m : pullbackSpace P Y.src, (Â.mor m).1 = (F.mor m.1.1, A m.1.2)) ∧
          EW.IsProperStrongBundleCovering EV F Â)

end RoundTrip.V8_50
