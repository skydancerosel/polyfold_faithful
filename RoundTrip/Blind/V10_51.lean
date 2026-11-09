import Polyfold
/-! Blind formalization of V10_51 (the text's Part II, §10.5, the diagrams of strong bundles,
p. 504 of the Springer 2021 book; 2017 p. 364).

Text: diagrams `W ←Φ W'' →Ψ W'` with `Φ` a strong bundle equivalence and `Ψ` a strong bundle
functor; refinements and equivalence (having a common refinement) as for ep-groupoids; the class
`[D]` is a generalized strong bundle map.

Choices:
- This item is a definition.  Setting: universe 0; strong bundles over ep-groupoids are the
  project's bundled `SEP.{0}` (an ep-groupoid `X`, a Part I strong bundle `P : W → X` and the
  structure map `μ`, 2021 Definition 8.3.1); a strong bundle functor `W'' → W` is a morphism of
  the project's category `SEP` (a pair `(ϕ, Φ)` of sc-smooth functors `ϕ : X'' → X`,
  `Φ : (W'', 𝐖'') → (W, 𝐖)` with the project's `IsStrongBundleFunctor`, 2021 Definition 8.3.3);
  a strong bundle equivalence is the project's `IsStrongBundleEquivalence` (2021 Definition
  10.4.1), natural equivalence `≃` of strong bundle functors the project's `StrongBundleNatEquiv`
  (2021 Definition 10.4.8).  A diagram is the project's `SDiagram A A'` (fields `B`, `Φ`,
  `isEquivalence_Φ`, `Ψ`, read with `#print`); conjunct (a) checks it is the text's notion.
- "refinement as for ep-groupoids" (2021 Definition 10.3.1 transposed, `IsRefB`): `D'` is a
  refinement of `D` if there is a strong bundle equivalence `H : W''' → W''` with `Φ ∘ H ≃ Φ'` and
  `Ψ ∘ H ≃ Ψ'`; composites of strong bundle functors written as the composites of the two
  underlying functors (`EpFunctor.comp F G = F ∘ G`).  "equivalence" (`EquivB`): a common
  refinement, a diagram refining both.
- "the class `[D]`": I read it as the equivalence class of `D` for "having a common refinement";
  this presupposes, as for ep-groupoids (the text's result following Definition 10.3.5), that
  this relation is an equivalence relation.  Conjunct (d): `[D] = [D']` (the project's
  `SDiagram.cls`) iff `D`, `D'` have a common refinement; (e): every generalized strong bundle
  map (the project's `GenSBMap`) is some `[D]`.  (d) is the claim that the project's classes
  are those of the relation itself, not of the equivalence relation it generates.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_51
open Polyfold CategoryTheory

/-- `D'` is a refinement of `D`: a strong bundle equivalence `H : W''' → W''` with
`Φ ∘ H ≃ Φ'` and `Ψ ∘ H ≃ Ψ'`. -/
def IsRefB {A A' : SEP.{0}} (D' D : SBLocalization.SDiagram A A') : Prop :=
  ∃ H : D'.B ⟶ D.B,
    D'.B.E.IsStrongBundleEquivalence D.B.E H.ϕ H.Φ ∧
    D'.B.E.StrongBundleNatEquiv A.E (D.Φ.ϕ.comp H.ϕ) D'.Φ.ϕ (D.Φ.Φ.comp H.Φ) D'.Φ.Φ ∧
    D'.B.E.StrongBundleNatEquiv A'.E (D.Ψ.ϕ.comp H.ϕ) D'.Ψ.ϕ (D.Ψ.Φ.comp H.Φ) D'.Ψ.Φ

/-- `D` and `D'` are equivalent: they have a common refinement. -/
def EquivB {A A' : SEP.{0}} (D D' : SBLocalization.SDiagram A A') : Prop :=
  ∃ D'' : SBLocalization.SDiagram A A', IsRefB D'' D ∧ IsRefB D'' D'

/-- The diagrams of strong bundles, their refinements and equivalence, and the classes `[D]`
(generalized strong bundle maps) are the text's. -/
def B : Prop :=
  ∀ A A' : SEP.{0},
    -- (a) a diagram `W ←Φ W'' →Ψ W'`: `Φ` a strong bundle equivalence, `Ψ` a strong bundle
    -- functor, and every such triple is a diagram
    (∀ D : SBLocalization.SDiagram A A',
      D.B.E.IsStrongBundleEquivalence A.E D.Φ.ϕ D.Φ.Φ ∧
      D.B.E.IsStrongBundleFunctor A'.E D.Ψ.ϕ D.Ψ.Φ) ∧
    (∀ (C : SEP.{0}) (Φ : C ⟶ A) (Ψ : C ⟶ A'),
      C.E.IsStrongBundleEquivalence A.E Φ.ϕ Φ.Φ →
      ∃ D : SBLocalization.SDiagram A A', D.B = C ∧ HEq D.Φ Φ ∧ HEq D.Ψ Ψ) ∧
    -- (b) refinements
    (∀ D D' : SBLocalization.SDiagram A A', D'.IsRefinement D ↔ IsRefB D' D) ∧
    -- (c) equivalence: a common refinement
    (∀ D D' : SBLocalization.SDiagram A A', D.Equiv D' ↔ EquivB D D') ∧
    -- (d) `[D]` is the equivalence class of `D`
    (∀ D D' : SBLocalization.SDiagram A A', D.cls = D'.cls ↔ EquivB D D') ∧
    -- (e) the generalized strong bundle maps are the classes `[D]`
    (∀ f : SBLocalization.GenSBMap A A', ∃ D : SBLocalization.SDiagram A A', D.cls = f)

end RoundTrip.V10_51
