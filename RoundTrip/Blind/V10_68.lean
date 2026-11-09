import Polyfold
/-! Blind formalization of V10_68 (the Springer 2021 book, Part II, §10.5, the strong bundle case,
p. 504 (2017 p. 364), of Theorem 10.2.2, p. 477 (2017: Theorem 10.2, p. 343)): the weak fibred
product `W ×_{W'} W''` of strong bundles.

Text: refinements and the equivalence of diagrams of strong bundles are introduced "following our
earlier construction" of generalized maps, which rests on the weak fibred product of Theorem
10.2.2; the strong bundle version is not stated.  Theorem 10.2.2 (the ep-groupoid case, items
V10_18–V10_20): for an equivalence `F : X → Y` and an sc-smooth `G : Z → Y`, `X ×_Y Z` is an
ep-groupoid, `πZ` is an equivalence and `F ∘ πX ≃ G ∘ πZ`; if `G` is an equivalence too, so is
`πX` (and degeneracy, tameness statements, not transcribed here).

Choices:
- The strong bundle version I formalize: for strong bundles `W → X`, `W' → X'`, `W'' → X''` over
  ep-groupoids, a strong bundle equivalence `Φ : W → W'` (covering `ϕ`) and a strong bundle
  functor `Ψ : W'' → W'` (covering `ψ`), there is a strong bundle `C` (the text's `W ×_{W'} W''`)
  over an ep-groupoid identified with the weak fibred product `X ×_{X'} X''` of `ϕ` and `ψ`, with
  strong bundle functors `ΠX : C → W`, `ΠZ : C → W''` (`πW`, `πW₂` in B) covering the projections
  `πX`, `πZ`, such that `ΠZ` is a strong bundle equivalence, `Φ ∘ ΠX ≃ Ψ ∘ ΠZ`, and `ΠX` is a
  strong bundle equivalence when `Ψ` is one.  The case where only `Ψ` is an equivalence
  (Theorem 10.2.2 has it for ep-groupoids) is the mirror image and is not included; nor is the
  identification of the total space of `C` with the weak fibred product of the total-space
  ep-groupoids (only the base is pinned down), nor the degeneracy/tameness parts.  B is an
  existence statement (the text gives no construction for strong bundles to pin down).
- Setting: universe 0, strong bundles over ep-groupoids are objects of the project's `SEP.{0}`,
  strong bundle functors its morphisms `⟶` (read with `#print`: `ϕ` on the bases, `Φ` on the
  total-space ep-groupoids, `IsStrongBundleFunctor`; 2021 Definition 8.3.3), `≫` their
  composition (diagrammatic order).  Strong bundle equivalences: `SEP.equivalences` (2021
  Definition 10.4.1, trusted); `≃`: the project's `SEP.NatEquiv` (2021 Definition 10.4.8, read with
  `#print`: a natural transformation of strong bundle functors covering an sc-smooth natural
  transformation of the base functors).
- The weak fibred product of the bases: the project's `EPLocalization.wfp ϕ ψ h` (Definition
  10.2.1 with the M-polyfold structures of Theorem 10.2.2, read with `#print`), for every proof
  `h` of the project's `Admissible ϕ ψ` (read with `#print`: `ϕ` or `ψ` is a local
  sc-diffeomorphism on objects; true here as `ϕ` is an equivalence, Definition 10.1.1 (3)), with
  its projections `projLeft`, `projRight` (`(x, φ, z) ↦ x`, `↦ z`).  "The base of `C` is
  `X ×_{X'} X''`": an isomorphism `e` of the category `EP` between `C.baseEP` and `wfp ϕ ψ h`
  (sc-smooth functors inverse to each other), with `ΠX` covering `πX ∘ e` and `ΠZ` covering
  `πZ ∘ e`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_68
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- **Theorem 10.2.2, strong bundle case**: the weak fibred product of a strong bundle
equivalence `Φ : W → W'` and a strong bundle functor `Ψ : W'' → W'`. -/
def B : Prop :=
  ∀ (A A' A'' : SEP.{0}) (Φ : A ⟶ A') (Ψ : A'' ⟶ A'), SEP.equivalences Φ →
    ∀ h : WeakFibredProduct.Admissible Φ.ϕ Ψ.ϕ,
    ∃ (C : SEP.{0}) (πW : C ⟶ A) (πW₂ : C ⟶ A'')
      (e : C.baseEP ≅ wfp (A := A.baseEP) (B := A''.baseEP) (C := A'.baseEP) Φ.ϕ Ψ.ϕ h),
      πW.ϕ = (WeakFibredProduct.projLeft Φ.ϕ Ψ.ϕ h).comp e.hom ∧
      πW₂.ϕ = (WeakFibredProduct.projRight Φ.ϕ Ψ.ϕ h).comp e.hom ∧
      SEP.equivalences πW₂ ∧
      SEP.NatEquiv (πW ≫ Φ) (πW₂ ≫ Ψ) ∧
      (SEP.equivalences Ψ → SEP.equivalences πW)

end RoundTrip.V10_68
