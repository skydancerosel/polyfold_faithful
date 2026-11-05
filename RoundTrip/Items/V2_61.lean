import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_61

/-! Round trip for V2_61 (Proposition 2.54: the pull-back of a strong bundle is a strong bundle).

`A` is the conjunction of the types of the theorems `Polyfold.proposition_2_54`,
`Polyfold.PullbackChartData.transition_eqOn`, `PullbackChartData.transition_isScSmooth`,
`PullbackChartData.transitionOne_isScSmooth`, `PullbackChartData.compatible_toChart`,
`Polyfold.paracompactSpace_pullbackSpace`, `Polyfold.pullback_image`,
`Polyfold.isStrongBundleRetraction_pullback` and `Polyfold.isStrongBundleRetract_pullback`, at
universe `0`.  `pullbackAtlas`, `PullbackChartData`, `PullbackChartData.toChart`,
`pullbackFiberCLE` and `pullbackRetraction` are definitions (vocabulary).

Neither direction is proved.

`A → B` fails because B's "naturality" is not in `A`: B asks that `P' : f*Y → Y`, `(z, y) ↦ y`, be
sc-smooth from `f*Y[0]` to `Y[0]` and from `f*Y[1]` to `Y[1]` for the strong bundle structure on
`f*Y`.  `A` only says that the pulled-back charts `Φ_f(z, y) = (ψ(z), pr_F Φ(y))` form a strong
bundle atlas (`proposition_2_54`: `∃ B'`, `B'.atlas.charts = (pullbackAtlas B hf).charts`); no
project statement mentions the sc-smoothness of `P'`.  It is believed true (in the charts `Φ_f`,
`Φ` the map `P'` is `(w, h) ↦ (g(w), h)` on `K_g`, `g = φ ∘ f ∘ ψ⁻¹` sc-smooth), but proving it is
new work on the chart API (`IsScSmoothOn.of_exists_charts` on both `toMPolyfold0` and
`toMPolyfold1`), not glue.  The rest of B does follow: `A_to_struct` (B without naturality; the
fibre-linearity conjunct comes from the project lemmas `pullbackFiberEquiv_add/smul`).

`B → A` fails: `A` is about the specific pulled-back charts (transition formulas, compatibility,
the retraction `R_g` and its image `K_g`, and that exactly these charts form the atlas), while B
only asserts that SOME strong bundle structure exists with `P'` sc-smooth.  `A` also asserts
paracompactness of `f*Y` for an arbitrary map `f` (not only sc-smooth ones).  B does give the
existence part of `proposition_2_54` (`B_to_exists`).

Harness note: the statement of `proposition_2_54` itself contains the banned
`paracompactSpace_pullbackSpace` (the instance on `f*Y` used by `StrongBundle`), so any proof that
mentions `A` fails `#rt_check`.  The partial results are therefore routed through `Exists254`
(the existence part of Proposition 2.54, with the instance existentially quantified): `A → Exists254`
is a one-line projection, and `#rt_check` is run on `Exists254 → Bstruct`. -/

namespace RoundTrip.V2_61
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.proposition_2_54.{0, 0, 0}) ∧
    (type_of% @Polyfold.PullbackChartData.transition_eqOn.{0, 0, 0}) ∧
    (type_of% @Polyfold.PullbackChartData.transition_isScSmooth.{0, 0, 0}) ∧
    (type_of% @Polyfold.PullbackChartData.transitionOne_isScSmooth.{0, 0, 0}) ∧
    (type_of% @Polyfold.PullbackChartData.compatible_toChart.{0, 0, 0}) ∧
    (type_of% @Polyfold.paracompactSpace_pullbackSpace.{0, 0, 0}) ∧
    (type_of% @Polyfold.pullback_image) ∧ (type_of% @Polyfold.isStrongBundleRetraction_pullback) ∧
    (type_of% @Polyfold.isStrongBundleRetract_pullback)

theorem A_holds : A :=
  ⟨@Polyfold.proposition_2_54.{0, 0, 0}, @Polyfold.PullbackChartData.transition_eqOn.{0, 0, 0},
    @Polyfold.PullbackChartData.transition_isScSmooth.{0, 0, 0},
    @Polyfold.PullbackChartData.transitionOne_isScSmooth.{0, 0, 0},
    @Polyfold.PullbackChartData.compatible_toChart.{0, 0, 0},
    @Polyfold.paracompactSpace_pullbackSpace.{0, 0, 0}, @Polyfold.pullback_image,
    @Polyfold.isStrongBundleRetraction_pullback, @Polyfold.isStrongBundleRetract_pullback⟩

/-- The existence part of Proposition 2.54: for a strong bundle `P : Y → X` and an sc-smooth
`f : Z → X`, `f*Y` is paracompact and `P_f : f*Y → Z` carries some strong bundle structure. -/
def Exists254 : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
    {Y : Type} [TopologicalSpace Y] {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})]
    [∀ x, Module ℝ (P ⁻¹' {x})] {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    {PZ : MPolyfold Z} {f : Z → X} [T2Space Y] [ParacompactSpace Y] (_ : StrongBundle PX P),
    PZ.IsScSmoothMap PX f →
      ∃ (_ : ParacompactSpace (pullbackSpace P f)), Nonempty (StrongBundle PZ (pullbackProj P f))

/-- B without its naturality clause. -/
def Bstruct : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (PZ : MPolyfold Z)
    (_ : StrongBundle PX P) (f : Z → X),
    PZ.IsScSmoothMap PX f →
      (∀ (z : Z) (a b : pullbackProj P f ⁻¹' {z}) (c : ℝ),
        pullbackFiberEquiv P f z (a + b) = pullbackFiberEquiv P f z a + pullbackFiberEquiv P f z b ∧
        pullbackFiberEquiv P f z (c • a) = c • pullbackFiberEquiv P f z a) ∧
      ∃ (_ : ParacompactSpace (pullbackSpace P f)), Nonempty (StrongBundle PZ (pullbackProj P f))

/-- `A` gives the existence part (projection of `proposition_2_54`). -/
theorem A_to_exists : A → Exists254 := by
  intro hA X _ _ _ PX Y _ P _ _ Z _ _ _ PZ f _ _ Bd hf
  obtain ⟨B', -⟩ := hA.1 Bd hf
  exact ⟨_, ⟨B'⟩⟩

/-- The existence part, with the project's fibre lemmas, gives B without naturality. -/
theorem exists_to_struct : Exists254 → Bstruct := by
  intro h X _ _ _ PX Y _ _ _ P _ _ Z _ _ _ PZ Bd f hf
  exact ⟨fun z a b c => ⟨pullbackFiberEquiv_add P f z a b, pullbackFiberEquiv_smul P f z c a⟩,
    h Bd hf⟩

theorem A_to_struct : A → Bstruct := fun hA => exists_to_struct (A_to_exists hA)

/-- `B` gives the existence part of Proposition 2.54 (not the identification of the atlas). -/
theorem B_to_exists : B → Exists254 := by
  intro hB X _ _ _ PX Y _ P _ _ Z _ _ _ PZ f _ _ Bd hf
  obtain ⟨-, hpc, Bf, -⟩ := hB PX P PZ Bd f hf
  exact ⟨hpc, ⟨Bf⟩⟩

#rt_check RoundTrip.V2_61.exists_to_struct [Polyfold.proposition_2_54,
  Polyfold.PullbackChartData.transition_eqOn, Polyfold.PullbackChartData.transition_isScSmooth,
  Polyfold.PullbackChartData.transitionOne_isScSmooth, Polyfold.PullbackChartData.compatible_toChart,
  Polyfold.paracompactSpace_pullbackSpace, Polyfold.pullback_image,
  Polyfold.isStrongBundleRetraction_pullback, Polyfold.isStrongBundleRetract_pullback]
#rt_check RoundTrip.V2_61.B_to_exists [Polyfold.proposition_2_54,
  Polyfold.PullbackChartData.transition_eqOn, Polyfold.PullbackChartData.transition_isScSmooth,
  Polyfold.PullbackChartData.transitionOne_isScSmooth, Polyfold.PullbackChartData.compatible_toChart,
  Polyfold.paracompactSpace_pullbackSpace, Polyfold.pullback_image,
  Polyfold.isStrongBundleRetraction_pullback, Polyfold.isStrongBundleRetract_pullback]

end RoundTrip.V2_61
