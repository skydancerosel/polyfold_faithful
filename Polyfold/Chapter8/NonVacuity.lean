import Polyfold.Chapter8.GeometricLift
import Polyfold.Chapter7.NonVacuity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 8: **witnesses** for the hypotheses of §8.6 (Definitions 8.8–8.9, Proposition 8.3,
pp. 275–281).  There is no 2014 preprint of Part II; numbers and pages are the 2017 text's.

# Non-vacuity: covering functors and geometric lifts

## The text, paraphrased

(Definition 8.9, p. 279) A functor `f : D → C` between finite groupoids is a covering functor
if `D → C ₛ×_f D`, `ψ ↦ (f(ψ), s(ψ))`, is a bijection; a geometric lift of `f` is a pair of
functors `L_D : D → Diff_sc`, `L_C : C → Diff_sc` with a natural transformation
`τ : L_D → L_C ∘ f`.  (Proposition 8.3, p. 281) A geometric lift of a covering functor gives a
proper covering functor (Definition 8.8).

## What is formalized (namespace `Polyfold.CoveringExamples`)

* `isCoveringFunctor_id`: the identity of `SingleObj G` is a covering functor, for every group
  `G`; `not_isCoveringFunctor_one`: for `G` nontrivial the functor sending every morphism to `1`
  is not (so Definition 8.9 is not vacuous in the other direction either).
* `rCat` (`ℝ = rnPolyfold 1` in `Diff_sc`), `reflectionDiffeo` (`y ↦ ±y`), `reflectionHom`
  (`ℤˣ →* End ℝ`), `reflectionLift`: a geometric lift of `𝟭 : SingleObj ℤˣ → SingleObj ℤˣ`, with
  `L_C(⋆) = ℝ` and `ℤ/2 = ℤˣ` acting by reflection, `L_D = L_C`, `τ = 1`.
* `isProperCovering_reflectionLift`: Proposition 8.3 applied to it, a proper covering functor
  (Definition 8.8) onto the translation groupoid `ℤ/2 ⋉ ℝ`.

## Elsewhere

* The other Chapter 8 witnesses sit next to their statements:
  `EpGroupoid.isTame_tangentEpGroupoid_trivial_rn` (Lemma 8.8, `TangentTame.lean`),
  `EpGroupoid.hasParacompactOrbitSpace_tangent_trivial` (Theorem 8.4, `TangentOrbit.lean`),
  `isCoveringFunctor_of_isEmpty` (`GeometricLift.lean`), and the strong bundle witnesses of
  §8.3–§8.5 in `NonVacuityBundle.lean`.
* Theorem 8.6 quantifies over all `ProperCoveringChart`s at `x`; Theorem 8.5 (part (b) of
  `theorem_8_6`) shows such charts exist below every open neighbourhood of `x`.
-/

open CategoryTheory Set Function

namespace Polyfold.CoveringExamples

open EpGroupoid.Examples

/-! ### Definition 8.9: covering functors -/

section Covering

variable (G : Type) [Group G]

/-- **The identity `SingleObj G → SingleObj G` is a covering functor** (Definition 8.9):
`ψ ↦ (ψ, ⋆)` is a bijection from the morphisms of `D = SingleObj G` onto `G × D`. -/
theorem isCoveringFunctor_id : IsCoveringFunctor (𝟭 (SingleObj G)) := by
  constructor
  · rintro ⟨a, b, g⟩ ⟨a', b', g'⟩ h
    simp only [coveringMap, Functor.id_map, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    cases a; cases b; cases a'; cases b'
    cases h1
    rfl
  · rintro ⟨g, a⟩
    exact ⟨⟨a, SingleObj.star G, g⟩, rfl⟩

/-- **A functor that is not a covering functor**: the functor `SingleObj G → SingleObj G` sending
every morphism to `1`, for `G` nontrivial (`(g, ⋆)` with `g ≠ 1` is not hit). -/
theorem not_isCoveringFunctor_one [Nontrivial G] :
    ¬ IsCoveringFunctor (SingleObj.mapHom G G (1 : G →* G)) := by
  intro h
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  obtain ⟨ψ, hψ⟩ := h.2 (g, SingleObj.star G)
  simp only [coveringMap, Prod.mk.injEq] at hψ
  exact hg (hψ.1.symm.trans rfl)

end Covering

/-! ### Definition 8.9: a geometric lift, `ℤ/2` acting on `ℝ` by reflection -/

section Reflection

/-- `ℝ = rnPolyfold 1` as an object of `Diff_sc`. -/
abbrev rCat : MPolyfoldCat.{0} := ⟨Fin 1 → ℝ, rnPolyfold 1⟩

/-- `y ↦ k y`, `k ∈ ℤˣ = {±1}`, as an sc-diffeomorphism of `ℝ`. -/
def reflectionDiffeo (k : ℤˣ) : ScDiffeo rCat rCat :=
  ⟨fun y : Fin 1 → ℝ => k • y, fun y : Fin 1 → ℝ => k⁻¹ • y,
    { isScSmoothOn := isScSmoothMap_units_smul k
      isScSmoothOn_inv := isScSmoothMap_units_smul k⁻¹
      mapsTo := mapsTo_univ _ _
      mapsTo_inv := mapsTo_univ _ _
      left_inv := fun (y : Fin 1 → ℝ) _ => inv_smul_smul k y
      right_inv := fun (y : Fin 1 → ℝ) _ => smul_inv_smul k y }⟩

/-- The action `ℤˣ →* End(ℝ)` in `Diff_sc`. -/
def reflectionHom : ℤˣ →* End rCat where
  toFun := reflectionDiffeo
  map_one' := ScDiffeo.ext (funext fun y : Fin 1 → ℝ => one_smul ℤˣ y)
  map_mul' k l := ScDiffeo.ext (funext fun y : Fin 1 → ℝ => mul_smul k l y)

/-- **A geometric lift** (Definition 8.9) of the covering functor `𝟭 : SingleObj ℤˣ → SingleObj ℤˣ`:
`L_C(⋆) = ℝ` with `ℤ/2` acting by reflection, `L_D = L_C`, `τ = 1`. -/
def reflectionLift : GeometricLift.{0} (𝟭 (SingleObj ℤˣ)) where
  LC := SingleObj.functor reflectionHom
  LD := 𝟭 _ ⋙ SingleObj.functor reflectionHom
  τ := 𝟙 _


/-- **Proposition 8.3, a proper covering functor** built from `reflectionLift`: `𝟭` is a
covering functor and `reflectionLift` a geometric lift of it, so the lifted functor
`F : ℤ/2 ⋉ ℝ → ℤ/2 ⋉ ℝ` is a proper covering (Definition 8.8). -/
theorem isProperCovering_reflectionLift :
    (geometricLiftFunctor reflectionLift).IsProperCovering :=
  proposition_8_3 (isCoveringFunctor_id ℤˣ) reflectionLift

end Reflection

end Polyfold.CoveringExamples
