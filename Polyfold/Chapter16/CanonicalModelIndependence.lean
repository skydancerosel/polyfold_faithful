import Polyfold.Chapter15.CanonicalOrientationEquivalence
import Polyfold.Chapter16.ModelPerturbations

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739, with
**Definition 16.4.4** (pp. 730–731), **Definition 16.6.5** and **Theorem 16.6.6** (p. 739),
**Theorem 15.4.1** and **Definition 15.4.2** (pp. 701–702).

# The oriented perturbed solution set does not depend on the model of the orientation

## The text, paraphrased

(p. 739) For a generic `λ` the perturbed solution set `θ = λ ∘ f` is a branched suborbifold of
`Z`, and if `f` is oriented, `θ` has the orientation inherited from `(f, o)` (Theorem 15.4.1,
Definition 15.4.2), read in a representative `(W, F)` carrying `o`.  Two representatives are
related by a generalized strong bundle isomorphism `𝔄`, represented by a diagram
`W ←Φ W'' →Ψ W'` of strong bundle equivalences; the orientations of the two representatives
correspond over `W''` (Definition 16.6.5, Theorem 12.5.7).

## What is formalized (namespace `Polyfold.StrongPolyfoldBundle.ModelPerturbation`)

For representatives `a₁`, `a₂` of `s`, a diagram `D : W₁ ←Φ W'' →Ψ W₂` with `Ψ` an equivalence
and `Γ₂ ∘ |D| = Γ₁`, with `Φ^* F₁ = Ψ^* F₂`, orientations `o₁`, `o₂` with `Φ^* o₁ = Ψ^* o₂`, and
model perturbations `M₁`, `M₂` with `Λ₁ ∘ Φ = Λ₂ ∘ Ψ`, each with the canonical orientation:

* **`orientedRep_rel_of_diagram`**: if `Λ₁ ∘ Φ ∘ F''` has a canonical orientation on `W''` for
  the common family, the two representatives `((Λᵢ ∘ Fᵢ, T̂ᵢ), (Xᵢ, γᵢ))` of oriented branched
  suborbifolds are related (Definition 16.4.4) by the base generalized isomorphism `[d]` of `D`
  (`IsCanonicalFor.pullSection_eq_pullSection`, Theorem 11.3.5's push/pull).
* **`toCompact_eq_of_diagram`**, **`integral_eq_of_diagram`**, `integralEff_eq_of_diagram`: hence
  the two compact oriented branched suborbifolds of `Z` are equal, and `∫_θ̂ τ`, `∮_θ̂ τ` are the
  same in both models.

## Reading

The canonical orientation on the middle bundle `W''` is a hypothesis (`hT''`).  It holds under
the hypotheses of Theorem 15.4.1 on `W''` (`theorem_15_4_1`), among them that `Φ^* o₁` is an
orientation of `Φ^* F₁` in the sense of Definition 6.6.16; its transport from `W₁` along `Φ` is
not part of this file.
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
`Λ₁ ∘ Φ = Λ₂ ∘ Ψ`, each with the canonical orientation of `(Fᵢ, oᵢ)`.  If `Λ₁ ∘ Φ ∘ F''` has a
canonical orientation on `W''` (`hT''`), then `((Λ₁ ∘ F₁, T̂₁), (X₁, γ₁))` and
`((Λ₂ ∘ F₂, T̂₂), (X₂, γ₂))` are related by the base generalized isomorphism `[d]` of `D`. -/
theorem orientedRep_rel_of_diagram (M₁ : ModelPerturbation a₁ m) (M₂ : ModelPerturbation a₂ m)
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
    {n : ℕ} {T'' : D.B.Obj → D.B.X.PObj.OrTangent →₀ ℚ}
    (hT'' : IsCanonicalFor (fun w => M₁.Λ ((SEP.Hom.Φ D.Φ).obj w)) hF''.2 hsec''
      (D.hΦ.pullOr hF'' hF₁ rfl hsec'' hsec₁ o₁) n T'') :
    OrientedRep.Rel M₁.orientedRep M₂.orientedRep := by
  set h₁ := D.hΦ with hh₁
  set h₂ := SBLocalization.sbe hΨ with hh₂
  have hf : EPLoc.IsGeneralizedIso (EPLoc.homMk D.base) :=
    (SBLocalization.GenSBMap.remark_10_5_3 ⟨D, rfl, hΨ⟩).1
  refine ⟨EPLoc.homMk D.base, hf, (Γ_base (F := D.cls) hΓ).symm, ?_⟩
  refine OrientedBranched.ext' ?_ ?_
  · change EPLoc.pullTheta (EPLoc.homMk D.base) (fun z => ((M₂.Λ (a₂.F z) : ℚ≥0) : ℚ)) =
      fun z => ((M₁.Λ (a₁.F z) : ℚ≥0) : ℚ)
    rw [EPLoc.pullTheta_homMk D.base M₂.isBranched.isFunctorial]
    change (SEP.Hom.ϕ D.Φ).pushforwardTheta ((SEP.Hom.ϕ D.Ψ).pullbackTheta
      (fun z => ((M₂.Λ (a₂.F z) : ℚ≥0) : ℚ))) = _
    rw [← pullbackTheta_eq h₂ hF₂ hpb (Λ := fun w => M₂.Λ ((SEP.Hom.Φ D.Ψ).obj w)) rfl]
    have e1 : (fun z => ((M₂.Λ ((SEP.Hom.Φ D.Ψ).obj (h₁.pullback a₁.F z)) : ℚ≥0) : ℚ)) =
        fun z => ((M₁.Λ ((SEP.Hom.Φ D.Φ).obj (h₁.pullback a₁.F z)) : ℚ≥0) : ℚ) :=
      funext fun z => by rw [hΛ]
    rw [e1, pullbackTheta_eq h₁ hF₁ rfl (Λ := fun w => M₁.Λ ((SEP.Hom.Φ D.Φ).obj w))
      (Λ' := M₁.Λ) rfl]
    exact EpFunctor.pushforwardTheta_pullbackTheta h₁.isEquivalence_base.essSurj
      M₁.isBranched.isFunctorial
  · change EPLoc.pullSection (EPLoc.homMk D.base) M₂.T = M₁.T
    rw [EPLoc.pullSection_homMk D.base h₂.isEquivalence_base M₂.isOrientation.isGrHatSection]
    change (SEP.Hom.ϕ D.Φ).pushSection ((SEP.Hom.ϕ D.Ψ).pullSection M₂.T) = M₁.T
    have e : (SEP.Hom.ϕ D.Ψ).pullSection M₂.T = (SEP.Hom.ϕ D.Φ).pullSection M₁.T := by
      funext y
      by_cases hys : y ∈ D.B.X.PObj.smoothSet
      · exact (IsCanonicalFor.pullSection_eq_pullSection h₁ h₂ hF₁ hF₂ hF'' rfl hpb hsec₁ hsec₂
          hsec'' hΛ ho hC₁ hC₂ hT'' hys).symm
      · rw [EpFunctor.pullSection_of_not_mem hys, EpFunctor.pullSection_of_not_mem hys]
    rw [e]
    exact EpFunctor.pushSection_pullSection h₁.isEquivalence_base
      ⟨M₁.isOrientation.isGrHatSection, M₁.smooth⟩

/-- **The compact oriented branched suborbifold `θ̂ = λ ∘ f` does not depend on the model of the
orientation** (§16.6, p. 739), under the hypotheses of `orientedRep_rel_of_diagram`. -/
theorem toCompact_eq_of_diagram (M₁ : ModelPerturbation a₁ m) (M₂ : ModelPerturbation a₂ m)
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
    {n : ℕ} {T'' : D.B.Obj → D.B.X.PObj.OrTangent →₀ ℚ}
    (hT'' : IsCanonicalFor (fun w => M₁.Λ ((SEP.Hom.Φ D.Φ).obj w)) hF''.2 hsec''
      (D.hΦ.pullOr hF'' hF₁ rfl hsec'' hsec₁ o₁) n T'') :
    M₁.toCompact = M₂.toCompact := by
  have h := Quotient.sound (s := OrientedRep.setoid c.polyfold)
    (orientedRep_rel_of_diagram M₁ M₂ D hΨ hΓ hF₁ hF₂ hF'' hpb hsec₁ hsec₂ hsec'' hΛ ho hC₁ hC₂
      hT'')
  unfold toCompact
  congr 1

/-- **2021 §16.6, p. 739: `∫_θ̂ τ` and `∮_θ̂ τ` do not depend on the model of the orientation**,
for two model perturbations with corresponding canonical orientations over a diagram, under the
hypotheses of `orientedRep_rel_of_diagram`. -/
theorem integral_eq_of_diagram (M₁ : ModelPerturbation a₁ m) (M₂ : ModelPerturbation a₂ m)
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
    {n : ℕ} {T'' : D.B.Obj → D.B.X.PObj.OrTangent →₀ ℚ}
    (hT'' : IsCanonicalFor (fun w => M₁.Λ ((SEP.Hom.Φ D.Φ).obj w)) hF''.2 hsec''
      (D.hΦ.pullOr hF'' hF₁ rfl hsec'' hsec₁ o₁) n T'') (τ : ScForm c.polyfold (m + 1)) :
    M₁.toCompact.integral τ = M₂.toCompact.integral τ ∧
      M₁.toCompact.integralEff τ = M₂.toCompact.integralEff τ := by
  rw [toCompact_eq_of_diagram M₁ M₂ D hΨ hΓ hF₁ hF₂ hF'' hpb hsec₁ hsec₂ hsec'' hΛ ho hC₁ hC₂
    hT'']
  exact ⟨rfl, rfl⟩

end ModelPerturbation

end StrongPolyfoldBundle

end Polyfold
