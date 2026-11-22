import Polyfold.Chapter17.CategoryStokes
import Polyfold.Chapter17.ModelPropertiesExamples
import Polyfold.Chapter7.HilbertPartitionsOfUnityEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.6 (pp. 823–824): witnesses for the hypotheses of **Theorems 17.6.7 and 17.6.10** in
`CategoryStokes.lean`.  Numbers and pages are the 2021 text's.

# Witnesses for the Stokes theorems on polyfolds

The extra hypothesis of `theorem_17_6_7_hyp`, `theorem_17_6_10_hyp` and their `n = 1` forms is
that the sc-smooth model `X_Ψ` of the covering family admits sc-smooth partitions of unity
(Definition 7.5.5); the hypothesis of the `_of_epStokes` forms is the ep-level assertion
`EP.StokesWithoutPartitions` for `X_Ψ`.  For `C = ℤ/3 ⋉ ℝ` with its tautological polyfold
structure and the covering family `{Ψ₀}` (`z3TautConstruction`, `z3Family`, every object with
isotropy `ℤ/3`):

* `z3Model_hasScPartitionsOfUnity`: `X_Ψ` (non-empty) admits sc-smooth partitions of unity
  (Corollary 7.6.6: `|X_Ψ|` is metrizable and the charts of `ℝ` have the Hilbert space `ℝ`);
* `z3Model_stokesWithoutPartitions`: hence the ep-level Stokes assertion holds for `X_Ψ`;
* `z3Taut_hypotheses_17_6_10`: `C` satisfies (LUC) (the hypothesis of Theorems 17.6.8–17.6.10),
  together with the two facts above.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

namespace GCT.PolyfoldConstruction

/-- **Witness for the `_hyp` forms of Theorems 17.6.7 and 17.6.10**: the model of `ℤ/3 ⋉ ℝ` for
the covering family `{Ψ₀}` is non-empty and admits sc-smooth partitions of unity. -/
theorem z3Model_hasScPartitionsOfUnity :
    (z3TautConstruction.modelEP z3Family.Ψ).X.HasScPartitionsOfUnity ∧
      Nonempty (z3TautConstruction.modelEP z3Family.Ψ).Obj := by
  refine ⟨EpGroupoid.corollary_7_6_6_unconditional _ ?_ fun x => ?_,
    ⟨⟨PUnit.unit, (0 : Fin 1 → ℝ)⟩⟩⟩
  · have := metrizableSpace_modelOrbitSpace_of_family (S := z3TautConstruction) (Ψ := z3Family.Ψ)
    let _ := TopologicalSpace.metrizableSpaceMetric
      (z3TautConstruction.modelEP z3Family.Ψ).X.OrbitSpace
    exact (inferInstance : ParacompactSpace (z3TautConstruction.modelEP z3Family.Ψ).X.OrbitSpace)
  · obtain ⟨i, y⟩ := x
    obtain ⟨φ, hφ, hy, hb, -⟩ := rnPolyfold_one_hilbert_hypothesis y
    exact ⟨MPolyfold.sigmaChart i φ, MPolyfold.IsChart.sigmaChart hφ, ⟨y, hy, rfl⟩, hb⟩

/-- **Witness for the `_of_epStokes` forms of Theorems 17.6.7 and 17.6.10**: Stokes on the
ep-groupoid level holds for the model of `ℤ/3 ⋉ ℝ`. -/
theorem z3Model_stokesWithoutPartitions :
    (z3TautConstruction.modelEP z3Family.Ψ).StokesWithoutPartitions :=
  EP.stokesWithoutPartitions_of_hasScPartitionsOfUnity _ z3Model_hasScPartitionsOfUnity.1

/-- **The hypotheses of Theorem 17.6.10 on `C` and its model are satisfiable**: `ℤ/3 ⋉ ℝ` has
(LUC), and its model admits sc-smooth partitions of unity and the ep-level Stokes assertion. -/
theorem z3Taut_hypotheses_17_6_10 :
    z3TautConstruction.IsLUC ∧
      (z3TautConstruction.modelEP z3Family.Ψ).X.HasScPartitionsOfUnity ∧
      (z3TautConstruction.modelEP z3Family.Ψ).StokesWithoutPartitions :=
  ⟨z3Taut_properties.2.1, z3Model_hasScPartitionsOfUnity.1, z3Model_stokesWithoutPartitions⟩

end GCT.PolyfoldConstruction

end Polyfold
