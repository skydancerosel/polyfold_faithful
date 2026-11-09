import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_68

/-! Round trip for V10_68 (the strong bundle case of 2021 Theorem 10.2.2, used without statement
in §10.5, p. 504: the weak fibred product `W ×_{W'} W''`).

The item lists the definitions `wfpSEP`, `projX`, `projZ`, `EpStrongBundle.pullbackAlong`,
`transportFunctor`, `invLiftFunctor`, `SEP.pullbackAlong`, `SEP.coneHom` (vocabulary) and six
theorems; `A` is the conjunction of their types, all universes at `0`:
`SBWeakFibredProduct.theorem_10_2_2` (for the project's construction `wfpSEP hΦ Ψ = πZ*W''`:
`ΠZ = projZ` is a strong bundle equivalence, `Φ ∘ ΠX ≃ Ψ ∘ ΠZ`, `ΠX`, `ΠZ` cover `πX`, `πZ`),
`theorem_10_2_2_right` (`Ψ` an equivalence ⇒ `ΠX` one), `nonempty_wfpSEP`, the general pull-back
lemma `EpStrongBundle.isStrongBundleEquivalence_pullbackProjFunctor` (the pull-back along an
equivalence projects by a strong bundle equivalence), the general cone lemma `SEP.natEquiv_cone`,
and the example `theorem_10_2_2_negSEPHom`.

`B`: for a strong bundle equivalence `Φ : W → W'`, a strong bundle functor `Ψ : W'' → W'` and
every proof `h` of `Admissible Φ.ϕ Ψ.ϕ`, there EXIST a strong bundle `C`, functors
`πW : C → W`, `πW₂ : C → W''` and an isomorphism `e : C.baseEP ≅ wfp Φ.ϕ Ψ.ϕ h` in `EP` with
`πW`, `πW₂` covering `πX ∘ e`, `πZ ∘ e`, `πW₂` an equivalence, `πW ≫ Φ ≃ πW₂ ≫ Ψ`, and `πW` an
equivalence when `Ψ` is one.

* `A_to_B`: `C = wfpSEP hΦ Ψ`, `πW = projX`, `πW₂ = projZ`, `e = Iso.refl` (the base of `wfpSEP`
  is `wfp … (admissible hΦ Ψ)` up to structure eta, and `h = admissible hΦ Ψ` by proof
  irrelevance, `Admissible` being a `Prop`); the covering equations by `rfl`; the rest is
  `theorem_10_2_2` and `theorem_10_2_2_right`.
* `B_to_A`: not proved.  `B` is an existence statement about SOME `C`; `A` is about the
  project's specific construction `wfpSEP`, `projX`, `projZ` (e.g. that this `projZ` is a strong
  bundle equivalence), plus two general lemmas on pull-backs and cones and an example.  `B` pins
  down only the base of its `C` (up to isomorphism), not its total space, so no property of `B`'s
  `C` transfers to `wfpSEP`.  Proving `A`'s conjuncts would mean re-proving the construction's
  properties outright (`isStrongBundleEquivalence_pullbackProjFunctor` is the substance of
  `ΠZ` being an equivalence). -/

namespace RoundTrip.V10_68
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBWeakFibredProduct.theorem_10_2_2.{0}) ∧
  (type_of% @Polyfold.SBWeakFibredProduct.theorem_10_2_2_right.{0}) ∧
  (type_of% @Polyfold.SBWeakFibredProduct.nonempty_wfpSEP.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isStrongBundleEquivalence_pullbackProjFunctor.{0}) ∧
  (type_of% @Polyfold.SEP.natEquiv_cone.{0}) ∧
  (type_of% @Polyfold.StrongBundleWeakFibredProductExamples.theorem_10_2_2_negSEPHom)

theorem A_holds : A :=
  ⟨@Polyfold.SBWeakFibredProduct.theorem_10_2_2.{0},
    @Polyfold.SBWeakFibredProduct.theorem_10_2_2_right.{0},
    @Polyfold.SBWeakFibredProduct.nonempty_wfpSEP.{0},
    @Polyfold.EpStrongBundle.isStrongBundleEquivalence_pullbackProjFunctor.{0},
    @Polyfold.SEP.natEquiv_cone.{0},
    @Polyfold.StrongBundleWeakFibredProductExamples.theorem_10_2_2_negSEPHom⟩

theorem A_to_B : A → B := by
  rintro ⟨h22, h22r, -, -, -, -⟩
  intro A A' A'' Φ Ψ hΦ h
  obtain ⟨hZ, hnat, -, -⟩ := h22 hΦ Ψ
  exact ⟨SBWeakFibredProduct.wfpSEP hΦ Ψ, SBWeakFibredProduct.projX hΦ Ψ,
    SBWeakFibredProduct.projZ hΦ Ψ, Iso.refl _, rfl, rfl, hZ, hnat, fun hΨ => h22r hΦ Ψ hΨ⟩

#rt_check RoundTrip.V10_68.A_to_B [Polyfold.SBWeakFibredProduct.theorem_10_2_2,
  Polyfold.SBWeakFibredProduct.theorem_10_2_2_right,
  Polyfold.SBWeakFibredProduct.nonempty_wfpSEP,
  Polyfold.EpStrongBundle.isStrongBundleEquivalence_pullbackProjFunctor,
  Polyfold.SEP.natEquiv_cone,
  Polyfold.StrongBundleWeakFibredProductExamples.theorem_10_2_2_negSEPHom]

end RoundTrip.V10_68
