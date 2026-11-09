import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_20

/-! Round trip for V8_20 (Definition 8.3.1 = 2017 Definition 8.4: strong bundles over
ep-groupoids).

The item lists the definitions `EpStrongBundle` (the structure), `EpGroupoid.unitPair` and
`EpStrongBundle.trivial` (a non-vacuity example), and the theorems `EpStrongBundle.P_μ`
(`P ∘ μ = t ∘ π₁`) and `EpStrongBundle.continuous_μ`.  `A` is the conjunction of the types of the
two theorems, universes at `0` (B lives in `Type`).

`B`: (a) the `μ` of every project `EpStrongBundle X B` satisfies B's reading `IsEpStrongBundleB`
of Definition 8.3.1, and (b) every `μ` satisfying it is the `μ` of a project `EpStrongBundle`.
`IsEpStrongBundleB` takes the paracompactness of `𝐗 ₛ×_P W` and the sc-smoothness `hs` of `s`
as arguments, while the project uses `B.paracompactSpace_pullback X.PMor X.src` and
`X.isScSmoothMap_src`; both are `Prop`s, so the pull-back strong bundles agree definitionally.

* `B` is proved outright (`B_holds`): the fields `isStrongBundleMap`, `surjective`,
  `isLocalScDiffeo` are B's first three clauses; B's literal fibre linearity
  (`μ(ψ, ·) : W_{s ψ} → W_{t ψ}` linear for the fibre structures of `W`) is the project's fibre map
  `EpStrongBundle.fiberMor ψ` (the fibre map of the strong bundle map `μ`, composed with Part I's
  identification `pullbackFiberCLE` of the fibre of `𝐗 ₛ×_P W` over `ψ` with `W_{s ψ}`); (2) is
  `μ_unit` (B's extra hypothesis `P w = x` substituted); (3) is `μ_comp` (B's extra hypothesis
  `s ψ = P(μ(γ, w))` is not needed for the project's form, and for (b) it is supplied by the
  covering property of the strong bundle map).  So the project's definition is the text's (in
  B's reading): the literal fibre-linearity clause is implied by `IsStrongBundleMap`.
* `A ⇒ B` is `B_holds` (vacuous use of `A`).
* `B ⇒ A`: (a) applied to a project `E` gives B's strong-bundle-map clause, whose covering field
  is `P_μ` and whose `[0]`-sc-smoothness gives `continuous_μ`.
-/

namespace RoundTrip.V8_20
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.P_μ.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.continuous_μ.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.P_μ.{0, 0}, @Polyfold.EpStrongBundle.continuous_μ.{0, 0}⟩

section Glue
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

theorem proj_to_B (hs : X.PMor.IsScSmoothMap X.PObj X.src) (E : EpStrongBundle X B) :
    IsEpStrongBundleB X B hs E.μ := by
  refine ⟨E.isStrongBundleMap, E.surjective, E.isLocalScDiffeo, fun ψ =>
    ⟨(E.fiberMor ψ).toLinearMap, fun w => rfl⟩, ?_, ?_⟩
  · rintro x w rfl h
    exact E.μ_unit w
  · intro ψ γ w h₁ h₂ _
    exact E.μ_comp ψ γ w h₁ h₂.symm

/-- The project strong bundle over `X` with structure map `μ`, built from B's conditions. -/
def ofB (hs : X.PMor.IsScSmoothMap X.PObj X.src) (μ : pullbackSpace P X.src → W)
    (h : IsEpStrongBundleB X B hs μ) : EpStrongBundle X B where
  μ := μ
  isStrongBundleMap := h.1
  surjective := h.2.1
  isLocalScDiffeo := h.2.2.1
  μ_unit w := h.2.2.2.2.1 (P w) w rfl _
  μ_comp ψ γ w h₁ h₂ := h.2.2.2.2.2 ψ γ w h₁ h₂.symm ((h.1.covers ⟨(γ, w), h₁⟩).trans h₂.symm).symm

end Glue

theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ hs
  exact ⟨fun E => proj_to_B hs E, fun μ h => ⟨ofB hs μ h, rfl⟩⟩

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E q
    have := B.paracompactSpace_pullback X.PMor X.src
    exact ((hB Obj Mor X W P B X.isScSmoothMap_src).1 E).1.covers q
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E
    have := B.paracompactSpace_pullback X.PMor X.src
    exact ((hB Obj Mor X W P B X.isScSmoothMap_src).1 E).1.continuous

#rt_check RoundTrip.V8_20.A_to_B [Polyfold.EpStrongBundle.P_μ, Polyfold.EpStrongBundle.continuous_μ]
#rt_check RoundTrip.V8_20.B_to_A [Polyfold.EpStrongBundle.P_μ, Polyfold.EpStrongBundle.continuous_μ]
#rt_overlap RoundTrip.V8_20.B_to_A [Polyfold.EpStrongBundle.P_μ,
  Polyfold.EpStrongBundle.continuous_μ]
#rt_check RoundTrip.V8_20.B_holds [Polyfold.EpStrongBundle.P_μ,
  Polyfold.EpStrongBundle.continuous_μ]

end RoundTrip.V8_20
