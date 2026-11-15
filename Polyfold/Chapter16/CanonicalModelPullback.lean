import Polyfold.Chapter15.CanonicalOrientationPullback
import Polyfold.Chapter16.CanonicalModelIndependence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739, with
**Definition 16.4.4** (pp. 730–731), **Definition 16.6.5** and **Theorem 16.6.6** (p. 739),
**Theorem 15.4.1** and **Definition 15.4.2** (pp. 701–702).

# The oriented perturbed solution set does not depend on the model of the orientation

## The text, paraphrased

(p. 739) For a generic `λ` the perturbed solution set `θ = λ ∘ f` has the orientation inherited
from `(f, o)` (Theorem 15.4.1, Definition 15.4.2), read in a representative `(W, F)` carrying
`o`.  Two representatives are related by a diagram `W₁ ←Φ W'' →Ψ W₂` of strong bundle
equivalences along which the orientations correspond (Definition 16.6.5, Theorem 12.5.7).

## What is formalized (namespace `Polyfold.StrongPolyfoldBundle.ModelPerturbation`)

For model perturbations `M₁`, `M₂` in representatives `a₁`, `a₂` related by a diagram `D` with
`Ψ` an equivalence, `Γ₂ ∘ |D| = Γ₁`, `Φ^* F₁ = Ψ^* F₂`, `Λ₁ ∘ Φ = Λ₂ ∘ Ψ`, `Φ^* o₁ = Ψ^* o₂`, each
with the canonical orientation of `(Fᵢ, oᵢ)`:

* **`orientedRep_rel_of_diagram_pullSection`**: the two representatives of oriented branched
  suborbifolds are related (Definition 16.4.4) by the base generalized isomorphism of `D`;
* **`toCompact_eq_of_diagram_pullSection`**, **`integral_eq_of_diagram_pullSection`**: the
  compact oriented branched suborbifolds of `Z` are equal, so `∫_θ̂ τ` and `∮_θ̂ τ` agree in both
  models.

No canonical orientation on the middle bundle `W''` is assumed: it is the pull-back `ϕ^* T̂₁` of
the canonical orientation of the first model (`IsCanonicalFor.pullSection`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

open EPLocalization EpGroupoid SBLocalization PolyfoldClass

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

namespace ModelPerturbation

variable {a₁ a₂ : SectionRep c} {m : ℕ}

/-- **The oriented representatives of two models with corresponding canonical orientations are
related** (Definition 16.4.4, §16.6 p. 739).  Let `D : W₁ ←Φ W'' →Ψ W₂` be a diagram of strong
bundle equivalences with `Γ₂ ∘ |D| = Γ₁` and `Φ^* F₁ = Ψ^* F₂`, let the orientations correspond
over `W''` (`Φ^* o₁ = Ψ^* o₂`), and let `M₁`, `M₂` be model perturbations with
`Λ₁ ∘ Φ = Λ₂ ∘ Ψ`, each with the canonical orientation of `(Fᵢ, oᵢ)`.  Then
`((Λ₁ ∘ F₁, T̂₁), (X₁, γ₁))` and `((Λ₂ ∘ F₂, T̂₂), (X₂, γ₂))` are related by the base generalized
isomorphism `[d]` of `D`. -/
theorem orientedRep_rel_of_diagram_pullSection (M₁ : ModelPerturbation a₁ m)
    (M₂ : ModelPerturbation a₂ m)
    (D : SBLocalization.SDiagram a₁.S.A a₂.S.A) (hΨ : SEP.equivalences D.Ψ)
    (hΓ : ⇑a₂.S.Γ ∘ D.orbitMap = ⇑a₁.S.Γ)
    (hF₁ : a₁.S.A.E.IsScFredholmSectionFunctor a₁.F)
    (hF₂ : a₂.S.A.E.IsScFredholmSectionFunctor a₂.F)
    (hF'' : D.B.E.IsScFredholmSectionFunctor (D.hΦ.pullback a₁.F))
    (hpb : D.hΦ.pullback a₁.F = (SBLocalization.sbe hΨ).pullback a₂.F)
    (hsec₁ : a₁.S.A.B.HasScPlusSectionsThrough) (hsec₂ : a₂.S.A.B.HasScPlusSectionsThrough)
    (hsec'' : D.B.B.HasScPlusSectionsThrough)
    (hΛ : ∀ w, M₁.Λ ((SEP.Hom.Φ D.Φ).obj w) = M₂.Λ ((SEP.Hom.Φ D.Ψ).obj w))
    {o₁ : ∀ x (hs : x ∈ a₁.S.A.X.PObj.smoothSet), Orx a₁.F hF₁.2 x hs}
    {o₂ : ∀ x (hs : x ∈ a₂.S.A.X.PObj.smoothSet), Orx a₂.F hF₂.2 x hs}
    (ho : D.hΦ.pullOr hF'' hF₁ rfl hsec'' hsec₁ o₁ =
      (SBLocalization.sbe hΨ).pullOr hF'' hF₂ hpb hsec'' hsec₂ o₂)
    (hC₁ : IsCanonicalPerturbation hF₁.2 hsec₁ o₁ M₁.toOrientedRegularPerturbation)
    (hC₂ : IsCanonicalPerturbation hF₂.2 hsec₂ o₂ M₂.toOrientedRegularPerturbation) :
    OrientedRep.Rel M₁.orientedRep M₂.orientedRep :=
  orientedRep_rel_of_diagram M₁ M₂ D hΨ hΓ hF₁ hF₂ hF'' hpb hsec₁ hsec₂ hsec'' hΛ ho hC₁ hC₂
    (IsCanonicalFor.pullSection D.hΦ hF'' hF₁ rfl hsec'' hsec₁ hC₁)

/-- **The compact oriented branched suborbifold `θ̂ = λ ∘ f` does not depend on the model of the
orientation** (§16.6, p. 739), under the hypotheses of
`orientedRep_rel_of_diagram_pullSection`. -/
theorem toCompact_eq_of_diagram_pullSection (M₁ : ModelPerturbation a₁ m)
    (M₂ : ModelPerturbation a₂ m)
    (D : SBLocalization.SDiagram a₁.S.A a₂.S.A) (hΨ : SEP.equivalences D.Ψ)
    (hΓ : ⇑a₂.S.Γ ∘ D.orbitMap = ⇑a₁.S.Γ)
    (hF₁ : a₁.S.A.E.IsScFredholmSectionFunctor a₁.F)
    (hF₂ : a₂.S.A.E.IsScFredholmSectionFunctor a₂.F)
    (hF'' : D.B.E.IsScFredholmSectionFunctor (D.hΦ.pullback a₁.F))
    (hpb : D.hΦ.pullback a₁.F = (SBLocalization.sbe hΨ).pullback a₂.F)
    (hsec₁ : a₁.S.A.B.HasScPlusSectionsThrough) (hsec₂ : a₂.S.A.B.HasScPlusSectionsThrough)
    (hsec'' : D.B.B.HasScPlusSectionsThrough)
    (hΛ : ∀ w, M₁.Λ ((SEP.Hom.Φ D.Φ).obj w) = M₂.Λ ((SEP.Hom.Φ D.Ψ).obj w))
    {o₁ : ∀ x (hs : x ∈ a₁.S.A.X.PObj.smoothSet), Orx a₁.F hF₁.2 x hs}
    {o₂ : ∀ x (hs : x ∈ a₂.S.A.X.PObj.smoothSet), Orx a₂.F hF₂.2 x hs}
    (ho : D.hΦ.pullOr hF'' hF₁ rfl hsec'' hsec₁ o₁ =
      (SBLocalization.sbe hΨ).pullOr hF'' hF₂ hpb hsec'' hsec₂ o₂)
    (hC₁ : IsCanonicalPerturbation hF₁.2 hsec₁ o₁ M₁.toOrientedRegularPerturbation)
    (hC₂ : IsCanonicalPerturbation hF₂.2 hsec₂ o₂ M₂.toOrientedRegularPerturbation) :
    M₁.toCompact = M₂.toCompact :=
  toCompact_eq_of_diagram M₁ M₂ D hΨ hΓ hF₁ hF₂ hF'' hpb hsec₁ hsec₂ hsec'' hΛ ho hC₁ hC₂
    (IsCanonicalFor.pullSection D.hΦ hF'' hF₁ rfl hsec'' hsec₁ hC₁)

/-- **2021 §16.6, p. 739: `∫_θ̂ τ` and `∮_θ̂ τ` do not depend on the model of the orientation**,
for two model perturbations with corresponding canonical orientations over a diagram, under the
hypotheses of `orientedRep_rel_of_diagram_pullSection`. -/
theorem integral_eq_of_diagram_pullSection (M₁ : ModelPerturbation a₁ m)
    (M₂ : ModelPerturbation a₂ m)
    (D : SBLocalization.SDiagram a₁.S.A a₂.S.A) (hΨ : SEP.equivalences D.Ψ)
    (hΓ : ⇑a₂.S.Γ ∘ D.orbitMap = ⇑a₁.S.Γ)
    (hF₁ : a₁.S.A.E.IsScFredholmSectionFunctor a₁.F)
    (hF₂ : a₂.S.A.E.IsScFredholmSectionFunctor a₂.F)
    (hF'' : D.B.E.IsScFredholmSectionFunctor (D.hΦ.pullback a₁.F))
    (hpb : D.hΦ.pullback a₁.F = (SBLocalization.sbe hΨ).pullback a₂.F)
    (hsec₁ : a₁.S.A.B.HasScPlusSectionsThrough) (hsec₂ : a₂.S.A.B.HasScPlusSectionsThrough)
    (hsec'' : D.B.B.HasScPlusSectionsThrough)
    (hΛ : ∀ w, M₁.Λ ((SEP.Hom.Φ D.Φ).obj w) = M₂.Λ ((SEP.Hom.Φ D.Ψ).obj w))
    {o₁ : ∀ x (hs : x ∈ a₁.S.A.X.PObj.smoothSet), Orx a₁.F hF₁.2 x hs}
    {o₂ : ∀ x (hs : x ∈ a₂.S.A.X.PObj.smoothSet), Orx a₂.F hF₂.2 x hs}
    (ho : D.hΦ.pullOr hF'' hF₁ rfl hsec'' hsec₁ o₁ =
      (SBLocalization.sbe hΨ).pullOr hF'' hF₂ hpb hsec'' hsec₂ o₂)
    (hC₁ : IsCanonicalPerturbation hF₁.2 hsec₁ o₁ M₁.toOrientedRegularPerturbation)
    (hC₂ : IsCanonicalPerturbation hF₂.2 hsec₂ o₂ M₂.toOrientedRegularPerturbation)
    (τ : ScForm c.polyfold (m + 1)) :
    M₁.toCompact.integral τ = M₂.toCompact.integral τ ∧
      M₁.toCompact.integralEff τ = M₂.toCompact.integralEff τ :=
  integral_eq_of_diagram M₁ M₂ D hΨ hΓ hF₁ hF₂ hF'' hpb hsec₁ hsec₂ hsec'' hΛ ho hC₁ hC₂
    (IsCanonicalFor.pullSection D.hΦ hF'' hF₁ rfl hsec'' hsec₁ hC₁) τ

end ModelPerturbation

end StrongPolyfoldBundle

end Polyfold
