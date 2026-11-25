import Polyfold
/-! Blind formalization of V14_33 (the Springer 2021 book, Part II, §14.4, Proposition 14.4.14,
pp. 667–671; 2017: Proposition 14.7).

Text: for fixed `a ∈ A` there is a local sc⁺-smooth symmetric section structure `(ŝᵃᵢ)_{i ∈ I_a}`
on `V̂_a` with (1) `ŝᵃᵢ = s⁰ᵃᵢ` on `V_a = V̂_a ∩ ∂X` and (2) `ŝᵃᵢ(z) = ŝᵃ_{i'}(z)` if `i ∼_z i'`,
`z ∈ V̂_a`.

Choices:
- Setting: universe 0; a strong bundle over an ep-groupoid is the project's `SEP.{0}`.  The
  standing hypotheses of Chapter 14 (those of the ∂-Extension Theorem 14.1.9, inside whose proof
  §14.4 lives) are made explicit: `X` tame (`EpGroupoid.IsTame`), with paracompact orbit space
  (`HasParacompactOrbitSpace`), and admitting sc-smooth partitions of unity
  (`MPolyfold.AdmitsScPartitionsOfUnity`; the proof uses a `G_a`-invariant partition of unity).
- The objects `A`, `Ũ(a)`, `V̂_a`, `I_a`, `τ̂`, `s⁰ᵃᵢ` are those of the running construction of
  §§14.2–14.4, so I quantify over every choice of that construction, read through the project's
  structures (all `#print`ed): a structured tuple `(Λ, U⁰, S⁰, τ⁰)` over `∂X`
  (`BoundaryStructuredTuple`), the neighbourhoods `Ũ'(x)` of (P5) (`P5Nbhds`), the extension of
  the correspondences of Lemma 14.3.1 (`CorrExtension`), the neighbourhoods `Ũ(x)` of (P6)
  (`P5Nbhds.P6Nbhds`) and the data of Proposition 14.3.8 (`ZConcrete`: `A ⊆ ∂X`, `V̂_a`).  The
  setting of §14.4 is `C.toZData` (`A`, `Ũ(a)` with its natural `G_a`-action, `V̂_a`, `I_a`,
  `τ̂`), the boundary sections `s⁰ᵃᵢ` are `C.toZSections.s a i` (the sections of the tuple at
  `a`), and `i ∼_z i'` (Definition 14.4.4) is the project's `ZSetup.ZRel a z i i'`.  I did not
  use the project's `LocalExtensionBase` (it takes `∼` and `≈` as free data).
- "local sc⁺-smooth symmetric section structure on `V̂_a`": every `ŝᵃᵢ` is an sc⁺-section on
  `V̂_a` (`IsScPlusSectionOn`: `P ∘ ŝ = id` there and `ŝ : V̂_a → W[1]` sc-smooth) and the family is
  `G_a`-equivariant, `ŝ_{g(i)}(g ∗ y) = μ(Γ(g, y), ŝᵢ(y))` for `y ∈ V̂_a` (the action of the
  natural representation of `Ũ(a)`; `fibAct` is `μ`).  Values off `V̂_a` are junk.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V14_33
open Polyfold Polyfold.SBLocalization

/-- The conclusion of Proposition 14.4.14 at `a` for the data `C`: `ŝ` is a local sc⁺-smooth
symmetric section structure on `V̂_a` extending `s⁰ᵃ` and constant on `∼_z`-classes. -/
def IsLocalExtension {A : SEP.{0}} {T : BoundaryStructuredTuple A} {P : P5Nbhds T}
    {E : CorrExtension T P} {Q : P.P6Nbhds} (C : ZConcrete E Q) (a : A.Obj)
    (sh : C.toZData.I a → A.Obj → A.W) : Prop :=
  -- sc⁺ on `V̂_a`
  (∀ i, IsScPlusSectionOn A (sh i) (C.toZData.V a)) ∧
  -- symmetric: `G_a`-equivariant
  (∀ (g : A.X.Isotropy a) (i : C.toZData.I a), ∀ y ∈ C.toZData.V a,
    sh (g • i) ((C.toZData.nbhd a).rep.Φ g y) = fibAct ((C.toZData.nbhd a).rep.Γ g y) (sh i y)) ∧
  -- (1) `ŝᵃᵢ = s⁰ᵃᵢ` on `V_a = V̂_a ∩ ∂X`
  (∀ i, ∀ y ∈ C.toZData.V a ∩ A.X.PObj.boundary, sh i y = C.toZSections.s a i y) ∧
  -- (2) `ŝᵃᵢ(z) = ŝᵃ_{i'}(z)` if `i ∼_z i'`, `z ∈ V̂_a`
  (∀ z ∈ C.toZData.V a, ∀ i i' : C.toZData.I a, C.toZData.ZRel a z i i' → sh i z = sh i' z)

/-- Proposition 14.4.14: the local extensions `ŝᵃ` exist for every `a ∈ A`. -/
def B : Prop :=
  ∀ (A : SEP.{0}), A.X.IsTame → A.X.HasParacompactOrbitSpace →
    A.X.PObj.AdmitsScPartitionsOfUnity →
    ∀ (T : BoundaryStructuredTuple A) (P : P5Nbhds T) (E : CorrExtension T P) (Q : P.P6Nbhds)
      (C : ZConcrete E Q), ∀ a ∈ C.toZData.A,
        ∃ sh : C.toZData.I a → A.Obj → A.W, IsLocalExtension C a sh

end RoundTrip.V14_33
