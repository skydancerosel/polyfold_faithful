import Polyfold.Chapter8.GeometricLift
import Polyfold.Chapter8.NonVacuityBundle
import Polyfold.Chapter7.NonVacuity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 8: **witnesses** for the hypotheses of §8.4 (Definitions 8.8–8.9, Proposition 8.3,
pp. 275–281) and a counterexample to Theorem 8.5 (5) as printed (p. 277).  There is no 2014
preprint of Part II; numbers and pages are the 2017 text's.

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

* **Theorem 8.5 (5) as printed** (p. 277, right arrow `t`): `theorem_8_5_five_as_printed`, for
  the identity functor of `ℤ/2 ⋉ ℝ` (`reflectionEpGroupoid`, a proper covering functor by
  `EpFunctor.isProperCovering_id`) and every chart of Theorem 8.5 at `x = 0`, the sheet `𝐔(ψ₀)` of
  `ψ₀ = (−1, 0)` contains `ψ = (−1, y)` with `F(s(ψ)) = y ≠ −y = t(F(ψ))`; such charts exist
  (`theorem_8_5_five_as_printed_nonvacuous`).  So (5) with `t` does not hold as we read it; the
  formalized (5) has `s` on both arrows (`ProperCoveringChart.comm_src`), a possible misprint.

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

/-! ### Theorem 8.5 (5) as printed -/

section Theorem85

/-- The morphism `ψ₀ = (−1, 0) : 0 → 0` of `ℤ/2 ⋉ ℝ`. -/
def reflectionψ₀ : ℤˣ × (Fin 1 → ℝ) := (-1, 0)

theorem reflectionψ₀_mem_morOn :
    reflectionψ₀ ∈
      reflectionEpGroupoid.morOn ((EpFunctor.id reflectionEpGroupoid).obj ⁻¹' {0}) := by
  refine ⟨?_, ?_⟩
  · rfl
  · change ((-1 : ℤˣ) • (0 : Fin 1 → ℝ)) = 0
    exact smul_zero _

/-- **Theorem 8.5 (5) as printed (right arrow `t`) does not hold as we read it**: for the
identity functor of `ℤ/2 ⋉ ℝ` (a proper covering functor) and every chart of Theorem 8.5 at
`x = 0`, the sheet `𝐔(ψ₀)` of `ψ₀ = (−1, 0)` contains a `ψ` with `F(s(ψ)) ≠ t(F(ψ))`. -/
theorem theorem_8_5_five_as_printed
    (C : (EpFunctor.id reflectionEpGroupoid).ProperCoveringChart 0) :
    ∃ ψ ∈ C.sheet reflectionψ₀,
      (EpFunctor.id reflectionEpGroupoid).obj (reflectionEpGroupoid.src ψ) ≠
        reflectionEpGroupoid.tgt ((EpFunctor.id reflectionEpGroupoid).mor ψ) := by
  have hm := reflectionψ₀_mem_morOn
  have ho : IsOpen ((fun y : Fin 1 → ℝ => ((-1 : ℤˣ), y)) ⁻¹' C.sheet reflectionψ₀) :=
    (C.isOpen_sheet _ hm).preimage (continuous_const.prodMk continuous_id)
  have h0 : (0 : Fin 1 → ℝ) ∈ (fun y : Fin 1 → ℝ => ((-1 : ℤˣ), y)) ⁻¹' C.sheet reflectionψ₀ :=
    C.mem_sheet _ hm
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho 0 h0
  set y : Fin 1 → ℝ := fun _ => ε / 2 with hy
  have hyb : y ∈ Metric.ball (0 : Fin 1 → ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, pi_norm_const, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  refine ⟨((-1 : ℤˣ), y), hball hyb, ?_⟩
  change y ≠ (-1 : ℤˣ) • y
  rw [units_smul_rn_neg_one]
  intro h
  have h1 := congrFun h 0
  simp only [hy, Pi.neg_apply] at h1
  linarith

/-- The charts of `theorem_8_5_five_as_printed` exist (Theorem 8.5 applied to the proper
covering functor `𝟭`), so the statement is not vacuous. -/
theorem theorem_8_5_five_as_printed_nonvacuous :
    Nonempty ((EpFunctor.id reflectionEpGroupoid).ProperCoveringChart 0) :=
  let ⟨C, _⟩ := EpFunctor.theorem_8_5
    (EpFunctor.isProperCovering_id (X := reflectionEpGroupoid)) 0 isOpen_univ (mem_univ _)
  ⟨C⟩

end Theorem85

section Universe

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **Theorem 8.6 in every universe** (2021 Theorem 8.5.8, p. 392): the identity functor of any
ep-groupoid, in any universe `u`, is a proper covering functor, and the theorem applies to it
(its restriction to the fibre over `x` is a covering functor). -/
theorem theorem_8_6_id (X : EpGroupoid Obj Mor) (x : Obj) :
    (EpFunctor.id X).IsProperCovering ∧
      IsCoveringFunctor ((EpFunctor.id X).restrictFiber x) :=
  ⟨EpFunctor.isProperCovering_id, (EpFunctor.theorem_8_6 EpFunctor.isProperCovering_id x).1⟩

end Universe

end Polyfold.CoveringExamples
