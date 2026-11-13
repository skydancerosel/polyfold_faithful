import Polyfold.Chapter9.GapP2_C2Remark9110Etale

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 9,
§9.1, **Proposition 9.1.9** and **Remark 9.1.10** (p. 404–405; 2017: Proposition 9.1, Remark 9.2):
satisfiability of the hypotheses of `proposition_9_1_9_two_text` and `remark_9_1_10_*`.

# The x-axis of ℝ² as a witness

`proposition_9_1_9_two_text` takes `[Nonempty (supp Θ)]` (the text's groupoid `⊔ M_x` is built
from a point of the support), and `remark_9_1_10_manifold`, `remark_9_1_10_manifold_proj`,
`remark_9_1_10_orbifold_etale` take `IsNDimensional Θ n` and `d_{|X|} = 0` on `|supp Θ|`
(Remark 9.1.10 is about an `n`-dimensional `Θ` without boundary). All of these hold for
`Θ = 1_L`, `L` the x-axis of `ℝ²`, in the trivial ep-groupoid of `ℝ²` (`n = 1`):

* `axis_isManifoldType`: `1_L` is of manifold-type (Definition 9.1.8 (1));
* `axis_degIndexOrbit_eq_zero`: `d = 0` on `|supp 1_L|`;
* `nonempty_supp_axis`: `0 ∈ supp 1_L`;
* **`remark_9_1_10_hypotheses_axis`**: the conjunction of all hypotheses (branched
  ep⁺-subgroupoid, manifold-type, `1`-dimensional, `d = 0`, nonempty support);
* the `example`s at the end apply `remark_9_1_10_manifold`, `remark_9_1_10_manifold_proj`,
  `remark_9_1_10_orbifold_etale` and `proposition_9_1_9_two_text` to this `Θ`.

(Moved into the library on 2026-11-13 from the check file of agent C2.)
-/

open Polyfold Polyfold.EpGroupoid

namespace Polyfold.EpGroupoid

/-- `1_L` (`L` the x-axis of `ℝ²`) is of manifold-type in the trivial ep-groupoid of `ℝ²`
(Definition 9.1.8 (1)). -/
theorem axis_isManifoldType :
    (trivial (rnPolyfold 2)).IsManifoldType (axis2.indicator 1) := by
  refine ⟨fun y => ?_, fun φ ψ _ _ h _ => h⟩
  by_cases hy : y ∈ axis2
  · simp [hy]
  · simp [hy]

/-- `d_{|X|} = 0` on `|supp 1_L|` (`ℝ²` has no boundary). -/
theorem axis_degIndexOrbit_eq_zero :
    ∀ z ∈ (trivial (rnPolyfold 2)).orbitSupp (axis2.indicator 1),
      (trivial (rnPolyfold 2)).degIndexOrbit z = 0 := by
  rintro _ ⟨a, -, rfl⟩
  exact MPolyfold.degIndex_rn a

/-- `0 ∈ supp 1_L`: the support is nonempty (the instance argument of
`proposition_9_1_9_two_text` and `remark_9_1_10_orbifold_etale`). -/
instance nonempty_supp_axis : Nonempty (supp (axis2.indicator (1 : (Fin 2 → ℝ) → ℚ))) :=
  ⟨⟨0, by simp [supp, zero_mem_axis2]⟩⟩

/-- All hypotheses of `proposition_9_1_9_two_text` and of Remark 9.1.10's Lean forms hold together
for `Θ = 1_L` in the trivial ep-groupoid of `ℝ²`, with `n = 1`. -/
theorem remark_9_1_10_hypotheses_axis :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid (axis2.indicator 1) ∧
      (trivial (rnPolyfold 2)).IsManifoldType (axis2.indicator 1) ∧
      (trivial (rnPolyfold 2)).IsNDimensional (axis2.indicator 1) 1 ∧
      (∀ z ∈ (trivial (rnPolyfold 2)).orbitSupp (axis2.indicator 1),
        (trivial (rnPolyfold 2)).degIndexOrbit z = 0) ∧
      Nonempty (supp (axis2.indicator (1 : (Fin 2 → ℝ) → ℚ))) :=
  ⟨indicator_axis2_branched.1, axis_isManifoldType, indicator_axis2_branched.2,
    axis_degIndexOrbit_eq_zero, nonempty_supp_axis⟩

example := remark_9_1_10_manifold indicator_axis2_branched.1 axis_isManifoldType
  indicator_axis2_branched.2 axis_degIndexOrbit_eq_zero

example := remark_9_1_10_manifold_proj indicator_axis2_branched.1 axis_isManifoldType
  indicator_axis2_branched.2 axis_degIndexOrbit_eq_zero

example := remark_9_1_10_orbifold_etale indicator_axis2_branched.1 axis_isManifoldType.1
  indicator_axis2_branched.2 axis_degIndexOrbit_eq_zero
  (nonempty_sheetChoice indicator_axis2_branched.1).some

example := proposition_9_1_9_two_text indicator_axis2_branched.1 axis_isManifoldType.1
  (nonempty_sheetChoice indicator_axis2_branched.1).some

end Polyfold.EpGroupoid
