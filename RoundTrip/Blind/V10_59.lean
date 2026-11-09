import Polyfold
/-! Blind formalization of V10_59 (the text's Part II, §10.5, Theorem 10.5.4, pp. 507–508 of the
Springer 2021 book; 2017: Theorem 10.9, p. 367), without the `Fred` part.

Text: for a generalized strong bundle isomorphism `[D]`, `[D]_* : Γ(P, μ) → Γ(P', μ')` is a
well-defined isomorphism whose inverse, given by the inverse diagram, is `[D]^*`; the same for
`Γ⁺` and `Fred`; `|[D]| = |[D']|` implies `[D]_* = [D']_*` and `[D]^* = [D']^*`.

Choices:
- Scope: the item's title excludes the `Fred` part, so the claim for `Fred(P, μ)` is not
  formalized.
- Setting: universe 0; the project's `SEP.{0}`, `SDiagram`, `GenSBMap`,
  `GenSBMap.IsGeneralizedIso` (V10_51, V10_56).  `[D]_*`, `[D]^*` are the project's
  `GenSBMap.pushforward`, `.pullback` (defined with a chosen representative); `Ψ_* Φ^*` on a
  representative is written with the project's `IsStrongBundleEquivalence.pushforward`,
  `.pullback` (2021 §10.4; my `pullB`, `pushB`, as in V10_58).  `Γ(P, μ)`, `Γ⁺(P, μ)` are the
  project's `sectionFunctors`, `plusSectionFunctors` (2017 Definition 8.7 (1), (2)).
- (a) "well-defined": `[D]_* f = Ψ_* Φ^* f` for every representative with both legs strong bundle
  equivalences.  (b) "`[D]_* : Γ(P, μ) → Γ(P', μ')`" and its inverse `[D]^* : Γ(P', μ') → Γ(P, μ)`
  map sections to sections; (c) they are mutually inverse there.  "isomorphism" is read as this
  bijection; I do not add linearity (the statement does not say "linear", and the same word is
  used for `Fred`, which is not a vector space).
- (d) "the inverse, given by the inverse diagram, is `[D]^*`": for a representative `D` with both
  legs equivalences, the inverse diagram `D⁻¹ = W' ←Ψ W'' →Φ W` (`invDiagB`, mine) defines a
  generalized strong bundle isomorphism `[D⁻¹]`, and `[D⁻¹]_* = [D]^*` on `Γ(P', μ')`.
- (e) "the same for `Γ⁺`": both maps send sc⁺-section functors to sc⁺-section functors, mutually
  inverse there.
- (f) `[D'] : P → P'` is another generalized strong bundle isomorphism (needed for `[D']_*`);
  `|[D]|` is the project's `GenSBMap.orbitMap` (V10_52); equality of the maps `|W| → |W'|`.  The
  conclusions are on `Γ(P, μ)` and `Γ(P', μ')` (off sections the project's maps carry junk).
- Nothing looks false to me ((f) is plausible: both values at `x'` lie in one `G_{x'}`-orbit of
  the fibre, and values of section functors are `G_{x'}`-fixed).
-/
namespace RoundTrip.V10_59
open Polyfold CategoryTheory

/-- `Φ^*` for a strong bundle equivalence `Φ : C → A`. -/
noncomputable def pullB {C A : SEP.{0}} (Φ : C ⟶ A) (h : SEP.equivalences Φ) :
    (A.Obj → A.W) → C.Obj → C.W :=
  EpStrongBundle.IsStrongBundleEquivalence.pullback h

/-- `Φ_*` for a strong bundle equivalence `Φ : C → A`. -/
noncomputable def pushB {C A : SEP.{0}} (Φ : C ⟶ A) (h : SEP.equivalences Φ) :
    (C.Obj → C.W) → A.Obj → A.W :=
  EpStrongBundle.IsStrongBundleEquivalence.pushforward h

/-- The inverse diagram `W' ←Ψ W'' →Φ W` of a diagram whose `Ψ` is a strong bundle
equivalence. -/
def invDiagB {A A' : SEP.{0}} (D : SBLocalization.SDiagram A A') (hΨ : SEP.equivalences D.Ψ) :
    SBLocalization.SDiagram A' A :=
  ⟨D.B, D.Ψ, hΨ, D.Φ⟩

/-- Theorem 10.5.4 (without `Fred`): `[D]_*` is a well-defined bijection `Γ(P, μ) → Γ(P', μ')`
and `Γ⁺(P, μ) → Γ⁺(P', μ')` with inverse `[D]^* = [D⁻¹]_*`, depending only on `|[D]|`. -/
def B : Prop :=
  ∀ (A A' : SEP.{0}) (f : SBLocalization.GenSBMap A A') (hf : f.IsGeneralizedIso),
    -- (a) well defined: `[D]_* = Ψ_* Φ^*` for every representative
    (∀ (D : SBLocalization.SDiagram A A') (hΨ : SEP.equivalences D.Ψ), D.cls = f →
      ∀ s ∈ A.E.sectionFunctors,
        SBLocalization.GenSBMap.pushforward hf s = pushB D.Ψ hΨ (pullB D.Φ D.isEquivalence_Φ s)) ∧
    -- (b) `[D]_* : Γ(P, μ) → Γ(P', μ')`, `[D]^* : Γ(P', μ') → Γ(P, μ)`
    (∀ s ∈ A.E.sectionFunctors, SBLocalization.GenSBMap.pushforward hf s ∈ A'.E.sectionFunctors) ∧
    (∀ t ∈ A'.E.sectionFunctors, SBLocalization.GenSBMap.pullback hf t ∈ A.E.sectionFunctors) ∧
    -- (c) mutually inverse
    (∀ s ∈ A.E.sectionFunctors,
      SBLocalization.GenSBMap.pullback hf (SBLocalization.GenSBMap.pushforward hf s) = s) ∧
    (∀ t ∈ A'.E.sectionFunctors,
      SBLocalization.GenSBMap.pushforward hf (SBLocalization.GenSBMap.pullback hf t) = t) ∧
    -- (d) the inverse is the push-forward along the inverse diagram
    (∀ (D : SBLocalization.SDiagram A A') (hΨ : SEP.equivalences D.Ψ), D.cls = f →
      (invDiagB D hΨ).cls.IsGeneralizedIso ∧
      ∀ (h : (invDiagB D hΨ).cls.IsGeneralizedIso), ∀ t ∈ A'.E.sectionFunctors,
        SBLocalization.GenSBMap.pushforward h t = SBLocalization.GenSBMap.pullback hf t) ∧
    -- (e) the same for `Γ⁺`
    (∀ s ∈ A.E.plusSectionFunctors,
      SBLocalization.GenSBMap.pushforward hf s ∈ A'.E.plusSectionFunctors) ∧
    (∀ t ∈ A'.E.plusSectionFunctors,
      SBLocalization.GenSBMap.pullback hf t ∈ A.E.plusSectionFunctors) ∧
    (∀ s ∈ A.E.plusSectionFunctors,
      SBLocalization.GenSBMap.pullback hf (SBLocalization.GenSBMap.pushforward hf s) = s) ∧
    (∀ t ∈ A'.E.plusSectionFunctors,
      SBLocalization.GenSBMap.pushforward hf (SBLocalization.GenSBMap.pullback hf t) = t) ∧
    -- (f) `|[D]| = |[D']|` implies `[D]_* = [D']_*`, `[D]^* = [D']^*`
    (∀ (f' : SBLocalization.GenSBMap A A') (hf' : f'.IsGeneralizedIso),
      f.orbitMap = f'.orbitMap →
      (∀ s ∈ A.E.sectionFunctors,
        SBLocalization.GenSBMap.pushforward hf s = SBLocalization.GenSBMap.pushforward hf' s) ∧
      (∀ t ∈ A'.E.sectionFunctors,
        SBLocalization.GenSBMap.pullback hf t = SBLocalization.GenSBMap.pullback hf' t))

end RoundTrip.V10_59
