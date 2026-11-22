import Polyfold.Chapter17.LevelStructures
import Polyfold.Chapter17.ModelPropertiesExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (p. 766): witnesses for **Theorem 17.1.28** (the polyfold structure `(F¹, M_{F¹})`),
**Corollary 17.1.29** and the levels `C^{i+1} := (C^i)¹`.  Numbers and pages are the 2021 text's.

# Witnesses for the levels `C^i`

The GCT `ℤ/3 ⋉ ℝ` (trivial action) with its tautological polyfold structure
(`z3TautConstruction`) has `F(x) ≠ ∅` for every `x` and satisfies (ZHOU), (SLUC), (SLR).  So the
hypotheses `HasCoveringUniformizers`, `HasUniformizers` of `LevelStructures.lean` hold, and the
conclusions are not vacuous:

* `z3Uniformized`: `ℤ/3 ⋉ ℝ` as a `GCT.UniformizedPolyfold`.
* `z3Taut_regSet`: every object has every regularity, `C_i = C`.
* `z3Uniformized_level`: for every `i`, `C^i` has objects (all of `C`: the image of `C^i → C` is
  everything), every object of `C^i` has a uniformizer of `F^i`, `C^i` has a covering family, and
  `C^i` satisfies (ZHOU), (SLUC) and (SLR) (Corollary 17.1.29 iterated).
* `z3Taut_levelOneModel`: for the covering family `L` of `F¹`, the comparison functor
  `X_L → X_Ψ¹` of Corollary 17.1.29 is an equivalence and `X_L` satisfies (ZHOU).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

namespace GCT.PolyfoldConstruction

open EpGroupoid.Examples LocalizationLRCounterexample

/-- **`ℤ/3 ⋉ ℝ` as a GCT with a polyfold structure and `F(x) ≠ ∅`.** -/
def z3Uniformized : GCT.UniformizedPolyfold.{0} :=
  ⟨_, z3TautConstruction, twistConstruction_hasUniformizers _ _⟩

/-- **Every object of `ℤ/3 ⋉ ℝ` has every regularity** (`ℝ` is finite-dimensional). -/
theorem z3Taut_regSet (i : ℕ) : z3TautConstruction.regSet i = univ :=
  eq_univ_of_forall fun x =>
    ⟨tautUnif _ _ x, x, GroupoidStr.isomorphic_refl _ _, by
      change x ∈ (rnPolyfold 1).levelSet i
      rw [rnPolyfold_levelSet]
      exact mem_univ x⟩

/-- **Witness for Theorem 17.1.28, Corollary 17.1.29 and `C^{i+1} := (C^i)¹`**: for `ℤ/3 ⋉ ℝ`
and every `i`, the objects of `C^i` are all objects of `C`, every object of `C^i` has a uniformizer
of `F^i`, `F^i` has a covering family, and `C^i` satisfies (ZHOU), (SLUC) and (SLR). -/
theorem z3Uniformized_level (i : ℕ) :
    range (z3Uniformized.levelIncl i).obj = univ ∧ Nonempty (z3Uniformized.level i).cat.Obj ∧
      (z3Uniformized.level i).str.HasUniformizers ∧
      Nonempty (z3Uniformized.level i).str.CoveringFamily ∧
      (z3Uniformized.level i).str.IsZhou ∧ (z3Uniformized.level i).str.IsSLUC ∧
      (z3Uniformized.level i).str.IsSLR := by
  have hr : range (z3Uniformized.levelIncl i).obj = univ :=
    (z3Uniformized.range_levelIncl_obj i).trans (z3Taut_regSet i)
  obtain ⟨hZ, -, hSLUC, -, hSLR⟩ := z3Taut_properties
  obtain ⟨h1, h2, h3⟩ := z3Uniformized.level_properties i
  have hx : (0 : Fin 1 → ℝ) ∈ range (z3Uniformized.levelIncl i).obj := hr ▸ mem_univ _
  exact ⟨hr, ⟨hx.choose⟩, (z3Uniformized.level i).hasUniformizers,
    (z3Uniformized.level i).str.exists_coveringFamily_iff.2
      (z3Uniformized.level i).hasCoveringUniformizers, h1 hZ, h2 hSLUC, h3 hSLR⟩

/-- **Witness for the comparison functor of Corollary 17.1.29**: for `ℤ/3 ⋉ ℝ` and a covering
family `L` of `F¹`, `X_L → X_Ψ¹` is an equivalence of ep-groupoids and `X_L` satisfies (ZHOU). -/
theorem z3Taut_levelOneModel :
    ∃ L : (z3TautConstruction.levelOneConstruction
        z3Uniformized.hasCoveringUniformizers).CoveringFamily,
      (z3TautConstruction.levelOneModelFunctor z3Uniformized.hasCoveringUniformizers L
        z3Family).IsEquivalence ∧
      ((z3TautConstruction.levelOneConstruction
        z3Uniformized.hasCoveringUniformizers).modelEP L.Ψ).X.IsZhou := by
  obtain ⟨L⟩ := (z3Uniformized.level 1).str.exists_coveringFamily_iff.2
    (z3Uniformized.level 1).hasCoveringUniformizers
  exact ⟨L, z3TautConstruction.isEquivalence_levelOneModelFunctor _ L z3Family,
    (z3TautConstruction.corollary_17_1_29_of_coveringFamily _ L).1 z3Taut_properties.1⟩

end GCT.PolyfoldConstruction

end Polyfold
