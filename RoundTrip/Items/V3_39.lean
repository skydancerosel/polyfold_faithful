import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_39

/-!
Round trip for V3_39 (Lemma 3.44: the kernel of `Dg(0)` is a graph).

`A` is the conjunction of the types of `Polyfold.ShiftedBasicData.Deriv.ker_Dg_eq`,
`Polyfold.ShiftedBasicData.Deriv.snd_Dg_inr` and `Polyfold.ShiftedBasicData.Deriv.DH₀_surjective`
(no universe parameters).  They are stated for the project's data `𝒟 : ShiftedBasicData` (an
sc-smooth germ `g` on a germ `G₀` whose index raise `g¹` is a basic germ on exactly the shifted
germ `G₁ = (G₀)_{·+1}`, `δ` the project's solution germ `𝒞.sol`) and `𝒱 : 𝒟.Deriv` (a neighbourhood
on which `H` and `δ` are `C¹`; `L = ι Dδ(0)`, `DH₀ = (1 − P)Dg(0)(α, Lα)`).

Neither direction is proved.
* `kerEquiv_of_A`: in A's own setting, A (`ker_Dg_eq`) gives exactly B's conclusion: a linear
  equivalence `ker DH(0) ≃ ker Dg(0)`, `α ↦ (α, Lα)`.
* `A → B` fails on the setting: to use A one must build a `ShiftedBasicData` from B's data.  That
  needs `g = Φ_*(h + s)` to be an sc-smooth germ on a germ `G₀` whose shift is (a shrinking of)
  B's `G₁` (a chain rule for germs: B only gives `g` sc¹ on some `G'`; the level-`0` tangent
  regularity is not determined by `g¹`), the basic germ `g₁` restricted to the shrunken germ, and
  then the identification of B's arbitrary `δ` (any representative of the solution germ) with
  `𝒞.sol` near `0` (uniqueness of the fixed point), of B's `L`, `M` with `Dδ₀`, `DH₀` and of
  `D' 0` with `scDerivGerm G₀ g 0` (uniqueness of derivatives on partial quadrants).  All of this
  is believed true but is substantial (the germ chain rule is proved in the project only for its
  own coordinate change, `StabilityData.pushMap₀_isScSmoothGerm`).
* `B → A` fails genuinely: A holds for every `ShiftedBasicData` (arbitrary finite-dimensional
  `P`, `Q`, any sc-smooth `g` with `g¹` basic), which need not be a push-forward `Φ_*(h + s)` of a
  germ `h` basic on level `0`; and A's conjuncts `snd_Dg_inr` (`(Dg(0)(0, ζ))_W = ζ`, via density
  of `W₁`) and `DH₀_surjective` are not stated in B.
-/

namespace RoundTrip.V3_39
open Polyfold

/-- The project's statement: Lemma 3.44 and its two companions. -/
def A : Prop :=
  type_of% @Polyfold.ShiftedBasicData.Deriv.ker_Dg_eq ∧
    type_of% @Polyfold.ShiftedBasicData.Deriv.snd_Dg_inr ∧
    type_of% @Polyfold.ShiftedBasicData.Deriv.DH₀_surjective

theorem A_holds : A :=
  ⟨@Polyfold.ShiftedBasicData.Deriv.ker_Dg_eq, @Polyfold.ShiftedBasicData.Deriv.snd_Dg_inr,
    @Polyfold.ShiftedBasicData.Deriv.DH₀_surjective⟩

/-- In A's setting, A yields B's conclusion: `α ↦ (α, Lα)` is a linear isomorphism
`ker DH(0) ≃ ker Dg(0)`. -/
theorem kerEquiv_of_A (hA : A) {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    {W : ScBanach} {Ct : Set P} (hC : IsQuadrantLike (ScBanach.const P) Ct)
    {𝒟 : ShiftedBasicData Ct W Q} (𝒱 : 𝒟.Deriv) :
    ∃ e : LinearMap.ker (𝒱.DH₀ : P →ₗ[ℝ] Q) ≃ₗ[ℝ]
        LinearMap.ker (𝒟.Dg : P × W.lvl 0 →ₗ[ℝ] Q × W.lvl 0),
      ∀ α, (e α : P × W.lvl 0) = ((α : P), 𝒱.L α) := by
  have hker := hA.1 hC 𝒱
  refine ⟨(Submodule.equivMapOfInjective (graphMap 𝒱.L) (graphMap_injective _) _).trans
    (LinearEquiv.ofEq _ _ hker.symm), fun α => rfl⟩

#rt_check RoundTrip.V3_39.kerEquiv_of_A [Polyfold.ShiftedBasicData.Deriv.ker_Dg_eq,
  Polyfold.ShiftedBasicData.Deriv.snd_Dg_inr, Polyfold.ShiftedBasicData.Deriv.DH₀_surjective]

end RoundTrip.V3_39
