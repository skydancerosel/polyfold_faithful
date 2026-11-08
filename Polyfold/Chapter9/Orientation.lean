import Polyfold.Chapter9.OrientationBoundary

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.3 "Orientations" (2021 pp. 422–429; 2017 pp. 310–315), the items not in
Chapter9/BoundaryPosition.lean (Definition 9.3.6, Lemma 9.3.7).

# Orientations (index)

* Chapter9/OrientationTangent.lean: `Gr̂(X)` (2021 p. 422), Remark 9.3.1.
* Chapter9/OrientationBasic.lean: Definition 9.3.2 (`EpGroupoid.IsOrientation`,
  `EpGroupoid.IsOrientable`), Remark 9.3.3 (`remark_9_3_3`).
* Chapter9/OrientationExample.lean: Example 9.3.5 (`example_9_3_5`, `example_9_3_5_eq_of_neg`,
  `exampleT2_ne_orientedLift1`).
* Chapter9/OrientationUniqueness.lean: Lemma 9.3.4 (`lemma_9_3_4`, `lemma_9_3_4_mixed_dim`).
* Chapter9/OrientationBoundary.lean: Definition 9.3.8 (`MPolyfold.boundaryFrames`), (9.11)
  (`eq_9_11`), Proposition 9.3.9 (`proposition_9_3_9`), Definition 9.3.10
  (`EpGroupoid.boundaryLift`), Remark 9.3.11.

## Overlap with existing files

The chart lemmas `chartVec_injOn`, `exists_clm_chartVec`, `chartVec_image_submanifoldTangent`,
`exists_submodule_chartVec_image` and `chartVec_image_graph2'` restate, for the chart vector
`chartVec`, lemmas of Chapter9/TangentSlicesBasic.lean and Chapter9/TangentSlicesRn.lean
(`injOn_tangentChartMap_snd`, `exists_clm_tangentChartMap_snd`, `chartTangent_eq`,
`exists_submodule_chartTangent`, `rn_exists_retraction`), which these files do not import.  The
independence hypotheses `hind` of the witnesses are discharged there
(`hasIndependentTangentSums_of_isOfDim_rn`, `hasIndependentTangentSums_of_proposition_9_1_12_rn`).
-/
