# Handoff: the Polyfold project (HWZ, *Polyfold and Fredholm Theory*, Parts I–IV)

A Lean 4 / Mathlib formalization of Hofer, Wysocki and Zehnder, *Polyfold and Fredholm Theory*
(Springer 2021), with its reports. `README.md` is the public overview; this file is for whoever works on
the repository. The Springer edition is the authoritative text: statement numbers and pages are its own,
followed in parentheses by those of the 2014 preprint (arXiv 1407.3185, Part I) or of the book's arXiv
version (1707.08941, "2017", Parts II–IV); the correspondence is `Exposition/BookConcordance.md`.

## 1. Setup

```bash
cd ~/polyfold_faithful && git pull
lake exe cache get      # Mathlib, once
lake build              # minutes, not hours
```

Sources (not in git, folder `Exposition/sources/`, gitignored): the Springer PDF and its `pdftotext -layout` text
`HWZ-Book-2021.txt`, the 2017 arXiv text `HWZ-Book-2017.txt` and the 2014 preprint `HWZ-PartI-2014.txt`
(`curl -sSL https://arxiv.org/pdf/1407.3185 -o a.pdf && pdftotext -layout a.pdf Exposition/sources/HWZ-PartI-2014.txt`,
the same for 1707.08941). The "2010 paper" of the Findings is arXiv 1002.3381.

**On this Mac:** `/usr/local/bin/git` is a stale x86 binary ("Bad CPU type"); Lean's process spawn finds it first
on the PATH, so every `lake` call (also inside `check_names.py`) fails and then **deletes
`.lake/packages/mathlib`**. Put a directory containing `git -> /usr/bin/git` first on the PATH for every lake or
check-script call. If Mathlib is missing, copy it from the Morse project (same Mathlib revision, already built):
`cp -c -R ~/math_faithful/Morse/.lake/packages .lake/packages`. Elaborate a single file with
`lake env lean -DmaxSynthPendingDepth=3 <file>` (the project option is not applied by plain `lake env lean`).
At most two full `lake build` runs at a time on this machine.

Checks that must stay green:

```bash
lake build
lake env lean -DmaxSynthPendingDepth=3 Polyfold/Test.lean | grep -v "propext, Classical.choice, Quot.sound\]"   # nothing but continuation lines
python3 Exposition/check_names.py                       # every cited name exists
python3 Exposition/check_trace.py Exposition/ProofByProof.md   # 0 unresolved
```

Rules: no `sorry`; `#print axioms` in `Polyfold/Test.lean` for every theorem; temporary files only as gitignored
`WIP_*.lean`; never renumber V-items, G-items or Findings items (as long as no sign-off is recorded in the repository,
V-items may be edited in place). Every hypothesis that quantifies over all charts is checked for
satisfiability (Findings, Chapter 3, item 190), and every added hypothesis has a witness in the non-degenerate
case (a witness only for $\partial X = \emptyset$ or zero fibres does not count). Lean names carry the 2021 numbers
(`theorem_14_1_9`, `lemma_14_1_4`) with descriptive suffixes only (`_hyp` for a form with a hypothesis not in the
text, `_book`/`_text` for the printed form when a restated form is the main one); file names are topic names in
UpperCamelCase.

Wording about the text: in everything the authors may read (the reports, the README, `RoundTrip/REPORT.md`), a
counterexample refutes *our reading* of a statement, not the statement. Say "does not hold as we read it",
"presumably …", "we read … as …"; never call the text wrong or attribute a defect to it.
The public documents describe the final state only.

## 2. Layout

Top level: `Polyfold.lean` (imports every module), `Polyfold/Test.lean` (`#print axioms` per theorem, one block
per chapter), `Polyfold/Basic.lean`, `Polyfold/Vendor/MilnorSard/` (Sard's theorem, from the Milnor project),
`Polyfold/Chapter1/` … `Polyfold/Chapter19/` (one folder per chapter of the book, files named by topic),
`Polyfold/Examples/` (the worked example, below),
`RoundTrip/` (the round-trip audit: `REPORT.md`, `Items/`, `Blind/`, `harness/`, `Check.lean`),
`Exposition/` (§3). A file's folder is its place in the dependency order: a file in `Polyfold/ChapterN/` imports
only chapters ≤ N, so a statement of one chapter that needs the machinery of a later chapter lives in the later
chapter's folder, and a file that needs nothing beyond an earlier chapter sits in that earlier folder. "From other
chapters" below names the files that serve statements of another chapter of the book; "pieces" are parts split off
larger files for import order.

**Chapter 1** (sc-calculus): `ScBanach`, `ScFredholm`, `ScFredholmCriterion`, `FredholmIndex`,
`FredholmPerturbation`, `ScSmooth`, `Levels`, `Properties`, `ChainRule`, `Degeneracy`, `PartialCones`,
`ScOneNotNormContinuous`, `ExpositionLemmas`, `Book`; the weighted Sobolev spaces of Example 1.1.3 on the
cylinder in `CylinderSobolevSpaces`, `CylinderScBanach`, `CylinderSobolevComplete`, `CylinderWeakDerivatives`,
`CylinderLeibniz`, `CylinderIntegrationByParts`, `CylinderMultipliers`, `CylinderCutoff`, `CylinderTestDensity`,
`CylinderTrigPolynomials`, `CylinderFourier`, `CylinderRellich`, `CylinderCompactInclusions`.

**Chapter 2** (retracts and M-polyfolds): `Retracts`, `TameRetracts`, `MPolyfold`, `LocalTopology`,
`LocalTopologyExample`, `Metrizable`, `MichaelRefinement`, `DegeneracyIndex`, `Boundary`, `PartialCone`,
`PartialConeQuadrant`, `CornerGerms`, `Tame`, `TameFaces`, `TameInvariance`, `ExtendedFaces`,
`SubMPolyfold`, `SubMPolyfoldTangent`, `SubMPolyfoldTangentSc`, `FibredProduct`, `LevelPolyfold`,
`SmoothRetractImage`; the tangent bundle and tangent spaces in `TangentBundle`, `TangentMap`, `TangentMapLinear`,
`TangentLift`, `TangentLiftAll`, `TangentSpaceLinear` (Definition 2.3.14), `TangentSpaceChartIndependent`,
`TangentProjOpen`, `TangentConeQuadrant`, `ReducedTangentIntrinsic`; strong bundles in
`StrongBundle`, `StrongBundleOne`, `StrongBundlePullback`, `StrongBundleRestrict`; the tame boundary of §2.7 in
`TameBoundary`, `TameBoundaryStructure`, `TameBoundaryTopology`, `TameBoundaryExample`, `TameBoundaryNonCentred`;
the 2021 statements in `Book`, `BookFormLocalCompleteness`, `BookFormTameBoundary`.
Face-structured M-polyfolds recognised by labels and face counts, with products: `FaceLabels`, `FaceFamilies`.
From other chapters: `LevelsWeak` (Chapter 1), `VectorFields`, `VectorFieldsGlobal` (Chapter 4), `LocConnected`
(Chapter 7); pieces: `ScOperatorProdMap`, `StrongBundleLevelOne`, `StrongBundleSectionOps`, `TangentMapLocal`.

**Chapter 3** (sc-Fredholm theory): germs and the contraction germ in `Germ`, `GermLevels`, `GermCalculus`,
`GermCalculusParam`, `ContractionGerm`, `GermIFT`, `GermIFTSmooth`, `SolutionGermRegularity`,
`SolutionGermQuantitative`, `SolutionGermRecentre`; fillers and basic germs in `Filler`, `GermFilling`,
`GermFillingChart`, `BasicClass` and the `BasicGermCriterion*`, `BasicGermLinearization*`, `BasicGermShrink*`
files; sc-Fredholm sections and their tame germ data in `TameGerms`, `TameGermsG`, `TameGermData`,
`TameGermDataStabilization`, `TameGermTransfer`, `FredholmSectionsG` and the `FredholmGerm*` files; the implicit
function theorem in the `GlobalIFT*` files (`GlobalIFTTheorems`, `GlobalIFTTheoremsG`, `GlobalIFTFull`; the
surjectivity at nearby zeros in the `GlobalIFTNearby*` files); good position in the `GoodPosition*` and
`GoodComplement*` files; linearizations in the `Linearization*` files; local solvability, compactness and quadrants in `LocalSolvability`,
`LocalSolvabilityClosed`, `SectionCompactness`, `SectionCompactnessG`, `LocalCompactness`, `QuadrantIFT`,
`QuadrantInverse`, `QuadrantInverseSmooth`, `QuadrantClassCk`; the all-charts tameness hypothesis that no strong
bundle satisfies, and the non-vacuity witnesses, in `TameVacuity`, `TameVacuityChart`, `NonVacuity`,
`NonVacuityCorner`; untamed bundles in the `Untamed*` files; the interval $[0,1]$ as an M-polyfold
in `UnitIntervalPolyfold`; the 2021 statements and counterexamples to our readings in `BookGerms`,
`BookItems`, `Counterexamples`, `RecentreCounterexample`.
Files with the suffix `G` hold the germ-reading forms of the statements of the file of the same stem. The index
along paths and its local constancy, the printed forms of the main theorems and the restriction to open subsets
need the bump functions of Chapter 5 and are there.

**Chapter 4** (manifolds with boundary with corners, sc⁺, forms): `LocalStructure`, `LocalFaces`,
`Characterization`, `Recentre`, `Submanifolds`, `SubmanifoldNearInterior`, `ScPlus`,
`ScPlusGraph`, `Families`, `FamiliesLocal`, `GeneralPositionLocalFaces`,
`StratifiedRegularValues`, `LocalStrongBundle`, `RetractionSectionFredholm`, `RetractionSectionSplitting`,
`RemarkLocalForm`, `RemarkFourThreeExample`, `RemarkFourThreeFamily`; the Lie bracket in
`BracketLevel`, `LieBracketBundle`, `BookFormLieBracket` (vector fields in Chapter 2); sc-differential forms and Stokes in the `ScForms*` files, `ScExteriorDerivative`,
`BoundaryForms`, `BoundaryFormsAgreementGeneral`, `BoundaryFormsAgreement`,
`BoundaryWedge`, `RelativeWedge`, `EuclideanForms`, `EuclideanStokes`, `ManifoldForms`,
`ManifoldFaceForms`, `ManifoldBoundary`, `ManifoldIntegral`, `ManifoldStokes`, the `StokesFace*`
files, `Poincare448Shift`, `ParametricIntegrals`; `Book`.
The faces of a submanifold in general position: `GeneralPositionFaceStructure`. The boundary integral of a manifold
with ends, without faces (level sets and cut-offs): `BoundaryIntegralEnds`.
From other chapters: `TameSub`, `BookFormTameSub` (Chapter 2), `NonVacuityG`, `UntamedBundleFrame`,
`UntamedBundleTheorem` (Chapter 3), `ManifoldOrientation` (Chapter 6); pieces: `NonVacuityHalfSpace`,
`SmoothSubmanifoldBasics`.

**Chapter 5** (the Fredholm package): `Compactness`, `SolutionSetClosed`, `AuxNorm`, `AuxNormLiteral`,
`AllowableSectionsMetric`, `BumpFunctions`, `BumpWeakPointwise`, `BumpPointsResearch`, `ShiftTameResearch`,
`PartitionsOfUnity`, `HilbertPartitionsOfUnity`, `SeparablePartitionsOfUnity`, `WCGPartitionsOfUnity`,
`AmirLindenstrauss`, `BonicFrampton`, `Torunczyk`, `ProjectionalResolution`, `LocallyFiniteBases`,
`ReflexiveCompactness`, `ReflexiveFibres`, `WeakSequentialCompactness`, `StrongBundleShift`,
`ShiftFamily` (the family `P^i` of Corollary 5.2.5), `SmoothLevelContinuity`; transversality and general position in
`Transversality`, `GeneralPosition`, `DenseGoodPosition`, `Corollary58`,
`FredholmArcPerturbation`, `CylinderPerturbation`; homotopy in `Homotopy`, `CompactHomotopyIso`; Theorem 5.3.15
in the `Theorem5315_*` files; the Sobolev spaces on cubes in the `SobolevCube*`, `SobolevRemark*` and
`LpWeightedProduct` files; the printed forms in `MainTheoremsBookForm`, `MainTheoremsBookFormTextDefs`, `Book`,
`ApproxPropertyEveryChart`. The allowable sections of trivial bundles: `AllowableSectionsIncomplete`; a non-zero
1-form `df` (§4.4): `ExteriorDerivativeWitness`.
From other chapters: `SmoothPaths`, `TangentConePaths` (Chapter 2); the index along paths and its local constancy
in the `IndexAlongPaths*` and `IndexLocallyConstant*` files, `BookFormIFT`, `MainTheorems`, `RestrictOpen`,
`SolutionTangentKernel`, `FredholmPullbackIso`, `GermReadingAliases` (Chapter 3); `OpenForms`, `Poincare448`,
`Poincare` (Chapter 4); `ScPaths`, `OrientableNbhd`, `Lemma629` (Chapter 6); `StrongBundleMap` (Chapter 8); pieces:
`RestrictOpenGermData`, `ChartSegmentPaths`, `SmoothSetMaps`, `DenseSmoothPoints`, `DenseSmooth`, `SubtypeValSmooth`.

**Chapter 6** (determinants, orientations, invariants): determinant lines and bundles in `DetLine`, `DetBundle`,
`DetConventions`, `DirectSumDet`, `ExactSequence`, `FredholmDet`, `LocalDetBundle`, `ClassicalDetBundle`,
`DetVectorBundles`, the `DetNonOrientable*` files, `LineBundleOrientation`, `OrientationBundle`,
`OrientationSpace`; linearizations and orientations in `LinSet`, `LinSetFredholm`, `LinOrientation`, `Stabilization`,
`StabilizationContinuity`, `StabKernelsExist`, `SmoothKernelFrames`, `SmoothSubspaceFamilies`, `SubspaceBundle`,
`GoodProjections`, `ProjectionSequence`, `SectionOrientation`, `SolutionOrientation`, `SolutionOrientationCharts`,
`SolutionSetOrientation`, `SolutionSetOpen`, `SolutionManifoldFamily`, `ProductOrientation`, the
`ProductSectionOrientation*` files, `OrientationConvention`, `OrientationFunctor`, `OrientationMainClean`,
`ContinuousOrientation`, `PerturbedOrientation`; paths, homotopies and
transport in `PathsInterval`, `PathCategory`, `PathCategoryInterval`, `PathTransport`, `Propagation`,
`PropagationWellDefined`, `Continuation`, `ScHomotopy`, `IntervalHomotopy`, `ScContractible`,
`SmoothPathComponents`, `PushData`, `PushTransfer`, `ChartTransfer`, `AddSections`, `FamilySections`,
`KernelFamily`, `KernelBundleInterval`, `ParamKernel`, `UnitIntervalSections`, `SmoothFiniteDimRanges`,
`SubmersionNearFamily`; the invariants and cobordisms of §§6.6–6.7 in the `Cube*` files (the cube
$[0,1]^n$ and its boundary slices), `SlicePropertyP`, `CobordismOrientation`, the `EndProductOrientation*`
and `EndPullbackForms*` files, `InvariantSingle`, `InvariantCobordism`, `InvariantProductEnds`,
`InvariantProductEndCharts`, `ProperHomotopy`, `Theorem671`, `Theorem671Assembly`, `Theorem671Final`
(Theorem 6.7.1); `Book`, `BookContinuity`. Families on `[0,1]ⁿ` and the cylinder `[0,1] × X` in
`CubeManifold`, `CubeReparam`, `CubeStabKernels`, `KernelBundleCube`, `SliceGeneralPosition`, the `IntervalProduct*`,
`IntervalSlice*`, `IntervalEnd*` files, `IntervalCobordismExistence`, `IntervalHomotopyInvariance`,
`KernelPathOrientation`, `TangentOrientationFamily`; orientations without bump functions in `ChartSections`,
`ChartPropagation`, `ChartOrientationSpace`, `ChartOrientationFunctor`, `TransportOrientationSpace`,
`TransportFunctor`, `TransportSpaceEquiv`; the literal 2021 germ data in `UntamedIndexJump`, `UntamedOrientation`,
`UntamedOrientationFunctor`.
The cobordism over `[0, 1] × X` (Remark 6.6.19, proof of Theorem 6.7.1): its ends in `IntervalEndGeneralPosition`,
`IntervalEndManifolds`, `IntervalCobordismDegeneracy`, `IntervalEndInclusion`, `IntervalCobordismStokes`,
`IntervalConstantCobordism`, `CornerSmoothMaps`, `InducedOrientationFrames`, `IntervalSliceSignedFrames`; its
boundary integral, which uses the face-sum form of Stokes, in Chapter 9.
From other chapters: `BoundaryFormsPullback`, `StokesFaceCharts` (Chapter 4), `CubePartitions` (Chapter 5), `Discrete`
(Chapter 7), `MathlibFormsBridge`, `MathlibSolutionSets`, `SolutionFaces`, `SolutionFaceForms` (Chapter 9); pieces:
`CylinderInterpolation`, `TangentMapCongr`, `TangentSpaceSingleton`, `DegIndexLevelZero`, `CornerCoordinates`,
`SubmanifoldDimension`, `RetractTangentShift`.

**Chapter 7** (ep-groupoids): `Groupoid`, `EpGroupoid`, `Basic`, `BookBasic`, `Effective`,
`Reduced`, `ReducedCriterion`, `ReducedNaturalCharts`, `ReducedNotHausdorff`, `OrbitTopology`, `ProperMaps`,
`ProperSubsets`, `LocalDiffeo`, `NaturalAction`, `NaturalRep`, `NaturalRepFinite`, `Uniformizer`,
`SubGroupoid`, `SubGroupoidTangent`, `SubGroupoidTangentSc`, `Lift`,
`SmoothPointsDense`, `FlatGluing`, `Michael`,
`PartitionsOfUnity`, `HilbertPartitionsOfUnityEp`, `PropertyFiveResearch`, `NonVacuity`; Zhou's retract and
(ZHOU) in the `Zhou*` files, `LineSobolevScale`, `LineTranslates`; the tame boundary in `TameBoundaryEp`,
`TameBoundaryEpStructure`, `TameBoundaryFull`, `BookFormTameBoundaryEp`. From Chapter 5: `DegeneracyZeroTame`.

**Chapter 8** (bundles and covering functors): `Basic`, `EpStrongBundle`, `NatTrans`,
`GeometricLift`, `GeometricLiftEmpty`,
`BundleOrbitParacompact`, `BundleOrbitParacompactOne`, `ProperCovering`, `ProperCoveringLocal`,
`SigmaPolyfold`, `NonVacuity`, `NonVacuityBundle`; the tangent ep-groupoid in `TangentEp`, `TangentEpNotInjective`,
`TangentFibred`, `TangentLocal`, `TangentOrbit`, `TangentOrbitLinear`, `TangentPairs`, `TangentTame`, `TangentVertical`,
`TangentWhitneyLocal` and the `TangentZhou*` files; condition (3) of a proper covering functor in
`ProperCoveringFibredMap`; the degeneracy index of `X ×_F Y` in `DegIndexProduct`, `DegIndexProductGeneral`, `DegIndexProductSmooth`, `DegIndexProductLevelOne`; `Book`.
From other chapters: `LieBracketOpenSubsets` (Chapter 4); `SmoothConnectedReps`, `SmoothRegularAssembly`, `ZhouFacts`,
`ZhouGroupoid`, `ZhouLevels`, `ZhouSigma` and, for the tangent maps of §7.4, `ZhouTangent` (Chapter 7).

**Chapter 9** (branched ep⁺-subgroupoids, integration, Stokes): the definitions in `Basic`, `Symmetric`,
`Propositions`, `Appendix`, `AppendixSlices`, `Tangent`, the `TangentSlices*` files, `TangentSubmanifoldSmooth`,
`OrientationBasic`, `Orientation`, `OrientationAnyDim`, `OrientationBoundary`, `OrientationRn`, `OrientationTangent`,
`OrientationUniqueness` and the `OrientationExample*` files; sheets, measures and the branched integral in the
`Sheet*` files, `Measure`, `MeasureEffective`, `MeasureGlue`, `MeasureWholeSheets`, `LocalMeasure`, `FamilyMeasure`,
`PointIntegration`, `FinitePointIntegration`, `BranchedIntegral`,
`SignedMeasureIntegrals`, `DensityLocal`, `DensitySignedMeasure`, `FunctionTimesForm`, `ZeroFormValues`; the integral
through graph charts in `GraphChart`, `GraphChartExists`, `GraphChartTransition`, `GraphCoord`, `GraphDiffeo`,
`ChartIntegral`, `ChartAbsIntegral`, `ChartVectors`, `IntegralCovering`, `FormEvalEp`, `FormEvalInfty`, `FrameSign`,
`ManifoldBridge`, `ManifoldIntegralBridge`, `MathlibManifoldBridge`,
`TameOpen`, `MultiChart`, `MultiChartCompact`, `MultiChartIntegration`, `MultiChartTheorem`; the boundary, its faces
and their measure in the `Boundary*` files, `CornerFinite`, `FaceChange`, `FaceFrame`, `FaceIntegrand`,
`FaceOrientation`, `FaceIntegralDimOne`, `GeneralBoundaryPoints`, `StratumRetraction`, `StratumTangent`; dimension
decompositions in `DimDecompositionExists`, `DimDecompositionUnique`, `DimensionJumpPolyfold`, `DimensionJumpRetract`,
`LocallyEquidimensional`; Stokes in the `Stokes*` files, `FiniteTheorem`, `FiniteTheoremText`, `FiniteDominated`,
`GeneralCorollaries`, `GeneralLevelZero`, `AllStructures`, `AllStructuresDimOne`, `EffectiveDimOneLUC`; witnesses in
`CircleOneSheet`, `CircleWitness`, `HalfCircleSheet`, `HalfCircleWitness`, the `Hemisphere*` files,
`SphereRadialRetraction`, `CyclicGroupoidIsotropy`; the support of a branched subgroupoid in the `Support*` files;
`CoveringFromText`, `DescentPolyfold`, `GoodPoints`, `LevelRestrict`, `OrbitSubsetMetrizable`,
`PropertyTShrinking`. Remark 9.5.20 in `DimensionJumpSheet`,
`DimensionJumpBranched`, `DimensionJumpIntegral`, `DimensionZeroIntegral` (the boundary integral in Chapter 11,
`DimensionJumpBoundaryIntegral`).
Theorems 9.5.17 and 9.5.18 without partitions of unity (Remark 9.5.19, point G.153): functions summing to $1$ near
`supp Θ` in `LocalPartitions`, `LocalPartitionsBump`, `LocalPartitionsExtension`, `LocalPartitionsConstruction`; the
forms `β_k ω` in `LocalFormsPush`, `LocalFormsSub`, `LocalFormsSheets`, `LocalFormsStokes`, `LocalFormsSystem`,
`LocalFormSystem`, and in dimension 1 `LocalFormsDimOneSub`, `LocalFormsDimOneSheets`, `LocalFormsDimOneSystem`,
`LocalFormSystemDimOne`; the proof of p. 451 with them in `StokesLocalForms`, `StokesLocalFormsCompare`,
`StokesLocalFormsStructures`, `StokesLocalFormsDimOne`; the theorems in `StokesLocalPartitions`,
`StokesLocalPartitionsDimOne`. Finitely many bump functions near a compact part of `|X|`: `BumpsNearCompact`.
The boundary integral of the cobordism `S_F ⊆ [0, 1] × X` of Chapter 6 (ends, signs, lateral faces):
`BoundaryEndFaces`, `IntervalBoundaryDecomposition`, `IntervalEndSigns`, `IntervalCobordismFaceStructure` (on
`StokesFaceSum`); without faces, the lateral term as a limit of cut-off integrals: `EndFaceChartPairs`,
`IntervalLateralBoundary`.
From other chapters: `SubmanifoldNearBoundary`, `ScPlusRetractQuestion` (Chapter 4), `TangentMorphism`,
`TangentMorphismLinear` (Chapter 7), forms on ep-groupoids in `EpForms`, `EpFormsObj`, `EpPoincare` (Chapter 8); pieces:
`TangentMapBoundaryOps`, `SubmanifoldTangentImage`.

**Chapter 10** (equivalences and localization): `Equivalence`, `EquivalenceExamples`, `EquivalenceLR`,
`EquivalenceLREffective`, `EquivalenceReduced`, `EquivalenceRefinement`, `EquivalenceZhou`, `ZhouExample`,
`ZhouExampleRealScale`, `WeakFibredProduct`, `WeakFibredProductTheorem`, `WeakFibredProductTriple`, `Localization`,
`LocalizationCategory`, `LocalizationLR`, `LocalizationLRBundleBase`, `LocalizationLRCounterexample`,
`LocalizationLREffectiveBundle`, `LocalizationProperties`, `LocalizationUniversal`, `LocalRegularitySubcategory`;
strong bundles up to equivalence in the `StrongBundle*` files; `FredholmEquivalence`, `SectionFunctorLinear`.
Local regularity in germ form in `LocalRegularityGerm`, `StrongBundleCutOff`; tame bundle charts in
`TameBundleCharts`.
Proposition 8.4.3 for Definition 8.4.2 as printed: `BundleLocalRegularityPrinted`.
From other chapters: `RaisedEpGroupoid` (Chapter 7), `PullbackStrongBundle`, `BundleLocalRegularity`, `EpFormsFunctor`
(Chapter 8), `ReducedIntegral`, `ReducedRep`, `ReducedCircle`, `XAxisWitness`, `SupportClassicalStructures`,
`SupportGroupoidEtale`, `SupportGroupoidNaturality` (Chapter 9).

**Chapter 11** (geometry up to equivalences): `EpEquivalenceGeometry`, `EpEquivalenceGeometryFaces`,
`FaceEpGroupoids`, `FaceGeneralizedIso`, `FaceIntersectionUnion`, `FaceIntersectionCounterexample`,
`SubGroupoidModel`, `MultisectionLocalStructure`, `AuxiliaryNormTransport`; coverings in
`CoveringEquivalence`, `CoveringEquivalenceDiagram`, `CoveringEquivalenceTheorem`, `ProperCoveringLocalization`,
`ProperStrongBundleCoverings`, the `StrongBundleCovering*` files, `StrongBundleUpToEquivalence`; branched subgroupoids
and their integrals up to equivalence in the `BranchedEquivalence*` files, `MeasureEquivalence`,
`MeasureGeneralizedIso`, `EffectiveMeasureEquivalence`, `EffectiveMeasureGeneralizedIso`, the `BoundaryMeasure*`
files, `BoundaryOrientationEquiv`, `BoundarySheetsDiffeo`, `GraphChartsDiffeo`, `MultiChartSheetsEquivalence`,
`OrientedStructureDiffeo`, `OrientedStructurePairs`; forms in `GeneralizedForms`, `EquivalenceForms`,
`EquivalenceFormsInfty`, `EpFormsWedge`, `EpPoincareLemma`, `FormAveraging`, `FormDescent`, `FormEvalPullback`,
`FormEvalPullbackEquivalence`, `OrbitForms`, `TranslationAverage`. `ChartDomainOrientation` (orientations on chart
domains), `DimensionJumpBoundaryIntegral` (Remark 9.5.20 on `∂X`), `OrientedBoundaryPair` (Theorem 11.3.9 for
oriented pairs).

**Chapter 12** (Fredholm theory in ep-groupoids): auxiliary norms and extensions in `AuxNormEp`, `AuxNormExtension`,
`AuxNormLocalExtension`, `ReflexiveAuxNormEp`, `ReflexiveAuxNormExtension`, `ReflexiveLocalExtension`,
`LocalBoundaryExtension`, `ScPlusExtension`, `ScPlusSectionFunctor`, `BumpEp`, `GoodNeighborhood`, `CompactnessEp`,
`ReflexiveCompactnessEp`; pulls along morphisms in `ChartPull`, `ChartPullTwoBundles`, `SectionPull`, `PushDataPull`,
`StabilizedKernelPull`, `MorphismIso`; orientations (§12.5) in `OrientationBundleEp`, `OrientationGerm`,
`OrientationFromSection`, `ContinuousOrientationSection`, `OrientationOrbit`, `OrientationOrbitHomeo`,
`OrientationMorphismContinuity`, `OrientationLocalCommute`, `OrientationNaturality`, `OrientationRepresentativeIndep`,
`OrientationTransferTheorem`, the `OrientationEquivalence*` files and `DyadicPathInduction`. §12.5 on chart-domain
restrictions (tame germ data) in `RestrictionLocalIso`, `ChartTransportCommute`, `ChartBumpTransportCommute`,
`OrientationGermSquare` and the `LocalOrientation*` files; generalized isomorphisms in the
`OrientationGeneralizedIso*` files, `OrientationEqualOrbitMaps`, `OrientationEqualOrbitMapsGerm`,
`OrientationNonEffectiveExample`; the literal germ data in `UntamedOrientationEp`.
The orientation objects with and without local sc⁺-sections compared under bump functions:
`LocalOrientationComparisonOrbit`, `LocalOrientationDiagramComparison`; local isomorphisms of `[0, 1] × X`:
`IntervalProductLocalIso`. From Chapter 5: `BoundaryExtension`.

**Chapter 13** (sc⁺-multisections): `Correspondence`, `PiCorrespondence`, `BiAction`, `GoodSystem`,
`GoodSystemExistence`, `GoodSystemRelative`, `ScPlusSectionOn`, `StrongBundlePullMap`, `SymmetricOn`,
`SymmetricStructurePush`, `StructurableMultisection`, `StructuredExtension`, `StructuredExtensionData`,
`DecoratedMultisection`, `TightMultisection`, `TightOn`, `Commensurable`, the `Atomic*` and `Multisection*` files,
`LocallyFiniteStructurable`, `LocallyFiniteSupports`.

**Chapter 14** (extension from the boundary): boundary neighbourhoods and structures in `GoodBoundary`,
`BoundaryCover`, `CoverVHat`, `BoundaryMultisection` (Definition 14.1.3, `BoundarySymmetricStructure`),
`BoundaryStructured`, `GoodStructured`, `StructurabilityCriterion`, `FiniteRepresentation`, `BoundaryPull`,
`BoundaryPush`, `FacePush`, `FaceTransport` (Proposition 14.1.8); the local extension of §§14.3–14.4 in
`LocalExtension`, `OpenExtension`, `ExtendCorrespondences`, `ZDataLocalExtension`, `ZRelationClosure`, the `ZLoop*`
files, `CoherentExtension`, `NormControl`; the transport of §14.5 in `TransportStatement`, `TransportProof`,
`TransportedSum`; the assembly and Theorem 14.1.9 in `ExtensionAssembly`, `AssemblyInputInstance`, `EmptyIndex`,
`BoundaryExtensionTheorem`, with the witness on the half-space in `HalfSpaceBundle`, `HalfSpaceConstSection`; faces
(§14.6) in `FaceGerm`, `FaceStructured`, `FaceTame`, `FaceAssembly`, `FaceGoodSystem`, `CornerScPlus`. Lemma 14.5.2 in
`BoundaryCommensurableSum`, `HalfSpaceCommensurableSum`; Theorem 14.6.3 with section-compatible face data in
`FaceSectionCompatible`, `FaceNaturalRep`, with the quadrant example in `QuadrantBundle`, `FaceAssemblyCorner`;
half-space witnesses for §12.5 in `ChartOrientationHalfSpace` and the `LocalOrientation*HalfSpace` files.
Index families per face: `FaceIndexFamilies`; the extension on the corner example: `CornerExtensionWitness`.
From Chapter 15: `Linearization`, `LinearizationModel`, `LocalScPlus`, `SeparationLemmas`.

**Chapter 15** (transversality and invariants): linearizations in `LinearizationFunctor`,
`LinearizationIntrinsic`, `OrientedLinearizations`, `CanonicalLift`; local families and general
position in `LocalFamilies`, `LocalSeeds`, `LocalSlice`, `LocalIFT`, `ParamFamily`, `ParamOntoBridge`,
`ParamOntoTransport`, `ParametricGeneralPosition`, the `GeneralPosition*` files, `GoodPositionBranches`,
`GoodPositionWitness`, `Transversality`, `TransversalExtension`, `RegularPerturbations`,
`InteriorPerturbationWitness`, `BoundaryPerturbation`, `ControllingPairs`, `FredholmSummands`; the
relative case (Theorem 15.3.9) in `RelativeFamilies`, `RelativeParametric`, `RelativeReduction`, `RelativeBranch`,
`ChargedExtensionFibres`, `ChargedExtensionCylinder`; branched objects in `BranchChart`, `TameBranched`,
`TameWitness`, `RestrictedEp`; the cylinder $[0,1] \times X$ in `Cylinder`, `CylinderEnds`, `CylinderGlue`,
`CylinderPartitions`, `CylinderCobordism`, `CubeEp`, `CubeLift`, `CubeAuxNorm`, `CutoffFunctor`, `GlueStructurable`;
products in the `Product*` files; the invariants in `PerturbedStokesInvariants`. The relative step in `RelativeSeeds`,
`RelativeSeedFamilies`, `RelativeLocalFamilies`, `RelativeStepBump`, `RelativeStepSeeds`, `BumpsNearControlledSet`,
`BoundaryExtensionIndependence`, `BoundaryFrameCriterion`, `TransversalExtensionCorollaries`, `TransversalExtensionWitness`,
`FaceOntoCorollaries`; the
canonical orientation (Theorem 15.4.1, Definition 15.4.2) in `KernelBranching`, `KernelBranchingIndex`,
`BranchKernelTangent`, `KernelChartChange`, `KernelFramesPerturbed`, `CanonicalOrientation`,
`CanonicalOrientationStokes`, the `CanonicalLift*` files, `LinearizationLocalIso`, `EmbeddedSubmanifolds`,
`FaceSliceSubmanifolds`; the cylinder and Corollary 15.4.4 in `CubeLUC`, `CubeLiftScPlus`, the `CylinderEnd*`,
`CylinderFace*` files, `CylinderSliceKernels`, `CylinderProductOrientation`, `CylinderCanonicalOrientation`,
`CylinderCobordismReduced`, `CylinderCollarNorm`, `CylinderPullStructurable`, `CylinderExtensionBump`,
`CylinderMatchedBranchingWitness`, `GeneralPositionBoundaryWeight`, `HalfSpaceBoundaryWeightWitness`; general position
along equivalences in `GeneralPositionEquivalence`.
Corollary 15.4.4 with the cylinder orientation: `CylinderOrientationInvariance`, `CollarCobordismCorollary`, and for
index 0 `CylinderPointFrames`, `CylinderPointEnds`; the canonical orientation under strong bundle equivalences:
`CanonicalOrientationEquivalence`, `CanonicalOrientationPullback`, `TransversalityEquivalence`; local orientations:
`CanonicalOrientationLocal`, `CanonicalOrientationOrientedSection`; witnesses: `SingleSectionMultisection`,
`TransversalExtensionBoundaryDatum`. The category `GrF(X)` of §15.1: `GrFCategory`; canonically oriented regular
perturbations exist: `CanonicalPerturbationExists`. Theorem 15.4.3 and Corollary 15.4.4 without partitions of unity:
`CanonicalOrientationUnconditional`, `CollarCobordismUnconditional`; over all transversal perturbations, the cylinder
over arbitrary ends: `AdmissibleRelativeStep`, `AdmissibleCylinderExtension`, `AdmissibleCylinderEnds`,
`AdmissibleCobordism`. Without bump functions on $X$: the orientation chain in `CanonicalLiftContinuityLocal`,
`CanonicalLiftContinuityLocalFrames`, `CanonicalLiftContinuityLocalKer`, `CylinderOrientationLocal`,
`CylinderOrientationLocalConj`, `CylinderOrientationLocalIso`, `CylinderFrameConventionLocal`,
`CylinderFrameConventionLocalOps`, `CylinderFrameConventionLocalPt`, `CylinderFrameConventionLocalRestr`,
`CylinderFrameConventionLocalSlice`, `CubeSectionsThrough`; the relative step and Corollary 15.4.4 from local families
in `RelativeStepFamilies`, `AdmissibleCobordismLocal`; the restriction to a saturated open set in `RestrictedBundle`,
`RestrictedBundleCompactness`, `RestrictedBundleGeneralPosition`, `RestrictedOrientation`,
`RestrictedOrientationCanonical`, `RestrictedOrientationCanonSum`, `RestrictedIntegral`, `RestrictedIntegralCore`,
`RestrictedIntegralSolution`, `RestrictedCobordism`; the local families on the restricted cylinder:
`RestrictedSeedsAtomic`, `RestrictedSeedsBump`, `RestrictedSeedsCone`, `RestrictedSeedsCut`, `RestrictedSeedsPre`,
`RestrictedSeedsTransfer`, `RestrictedSeedsCompare`, `RestrictedSeedsCompare2`, `RestrictedSeedsNatRep`,
`RestrictedSeedsLocal`, `RestrictedSeedsInclusion`, `RestrictedSeedsAssembly` (a second proof in `RestrictedSeedsCentre`,
`RestrictedSeedsLift`, `RestrictedSeedsFinal0`, `RestrictedSeedsFinal`); for index 0 `IndexZeroNoBumpsFrames`,
`IndexZeroNoBumpsEnds`.

**Chapter 16** (polyfolds): `PolyfoldStructure`, `PolyfoldExamples`, `PolyfoldMaps`, `RaisedPolyfold`,
`TangentPolyfold`, `TangentFunctor`, `TangentLemma`, `TangentEffective`, `CompositionCounterexample`,
`StrongPolyfoldBundle`, the `PolyfoldBundle*` files, `ZeroSection`, `FibreZero`, `ReflexivePull`, `ReflexivePush`,
`MixedTransfer`, `PolyfoldAuxNorm`, `NormLamContinuous`, `PolyfoldBump`, `PolyfoldPartitions`, `PolyfoldSections`,
`PolyfoldFredholmSections`, `PolyfoldMultisections`, `StructurablePullback`, `PolyfoldBoundaryExtension`,
`BranchedSuborbifold`, `BranchedTame`, `PerturbedSuborbifold`, `OrientationTransport`, `PolyfoldForms`,
`FormsPullback`, `FormsIndependence`, `PerturbedIntegralIndependence`, `StokesWithoutPartitions`, `SuppNaturality`,
`SuppNaturalityStatement`, `RepresentativeChecks`, `ZhouUniquenessCheck`. Orientation transport in
`OrientationRepresentatives`, `OrientationClassIndependence`, `OrientationOrbitMapIndependence`,
`OrientationTransportRegularity`, `OrientationNonEffectiveWitness`; witnesses for Chapter 15 in
`HalfSpaceOrientedSection`, `CanonicalOrientationWitness`, `CylinderOrientationWitness`; Theorem 16.6.6 in
`GeneralPositionModels`, `ModelPerturbations`, and for index 0 in `IndexZeroInvariant`, `IndexZeroPolyfoldTheorem`,
`IndexZeroTwoModels`, `PointCountEquivalence`, `PointTameShrinking`, `PointMeasureGeneralizedIso`.
Theorem 16.6.6 from the cylinder: `CanonicalIntegralInvariance`, `IndexZeroCylinder`; its independence of the model:
`CanonicalModelIndependence`, `CanonicalModelPullback`, `CanonicalModelTransfer`, `CorrespondenceMiddleCanonical`,
`InheritedOrientationGeneralPosition`, for index 0 `IndexZeroInheritedCorrespondence`; `OrientationRepLocal`, `CanonicalPerturbationIntegral`,
`FibreNegationStructure`; witnesses: `CircleSectionCobordism`, `CircleSectionCollarCobordism`,
`CircleSectionPolyfold`, `CylinderInvarianceNonEffective`, `IsotropyCircleCobordism`, `TrivialIsotropyBundle`,
`IndexZeroCylinderWitness`, `IndexZeroIsotropyWitness`, `IndexZeroShiftedPerturbation`,
`HalfSpaceIsotropyOrientedSection`, `HalfSpaceLocalOrientation`, `CanonicalModelTransferWitness`,
`CanonicalOrientationPullbackWitness`, `InheritedOrientationGeneralPositionWitness`,
`IndexZeroInheritedCorrespondenceWitness`, and Remark 6.6.19 on the half-disc in `HalfDiscIntervalCobordism`,
`HalfDiscCobordismFaces`, `HalfDiscBoundaryIntegral`, `HalfDiscFaceStructureInstance`, `HalfDiscLateralBoundary`;
the zero section: `ZeroSectionWitness`.
Without partitions of unity: Theorem 16.4.6 as printed, and Theorems 17.6.7 and 17.6.10 as printed, in
`StokesUnconditional`; the boundary integrals and Theorem 16.6.6 in `InvariantUnconditional`, for index 0 in
`IndexZeroUnconditional`, its independence of the model in `CorrespondenceUnconditional`. Existence for every
admissible perturbation: `InheritedPerturbationExists`. Theorem 16.6.6 over all admissible perturbations:
`InvariantAllAdmissible`, for index 0 `IndexZeroAllAdmissible`; witnesses `InvariantAllAdmissibleWitness`,
`IndexZeroNormOneWitness`. Theorem 16.6.6 without bump functions in the model of the orientation: `InvariantNoBumps`,
`InvariantNoBumpsUnconditional`, for index 0 `IndexZeroNoBumpsPointPull`, `IndexZeroNoBumpsCobordism`,
`IndexZeroNoBumpsRestr`, `IndexZeroNoBumpsUnconditional`; the orientation of Definition 16.6.5 made with local
sc⁺-sections: `OrientationRepLocalNoBumps`, `OrientationRepLocalNoBumpsCover`.

**Chapter 17** (polyfold theory for groupoidal categories): §17.1 in `GroupoidalCategory`, `TransitionSet`,
`LocalUniformizer`, `PolyfoldConstruction`, `FunctorialUniformizers`, `TransitionProperness`,
`PolyfoldConstructionExamples`, `OverlappingUniformizers`, the models in `ModelEpGroupoid`, `ModelEquivalence`,
`ModelComparison`, `ModelExamples`, `ModelProperties`, `ModelPropertiesExamples`, the levels in `PolyfoldLevels`,
`AdmissibleTripleBasic`, `LevelOneCategory`, `LevelStructures`, `LevelStructuresExamples`, `LevelOrbitSpaces`; §17.2
in `TangentVectors`, `TangentCategory`, `TangentTransition`, `TangentTransitionStructure`, `TangentModel`,
`TangentConstruction`, `TangentUnifExamples`, `TangentModelEquivalence`; §17.3 in `Subpolyfold`, `SubpolyfoldStructure`,
`SubpolyfoldLevels` (and `Chapter18/SubpolyfoldLocalFaces`, which uses an open subcategory of §18.1); §17.4 in `PolyfoldFaces`, `TameBoundaryGerms`, `TameBoundaryCategory`, `TameBoundaryUniformizer`,
`TameBoundaryTransition`, `TameBoundaryTransitionStructure`, `TameBoundaryTopology`, `TameBoundaryPolyfold`,
`TameBoundaryTame`, `TameBoundaryDiagram`, `TameBoundaryFaceGroupoid`, and strong bundles in `SigmaStrongBundle`,
`VectorBundleGCT`, `StrongBundleStructures`, `StrongBundleStructuresExamples`, `BundleModel`, `BundleModelComparison`,
`BundleModelMultiplication`, `BundleModelStructure`; §17.5 in `BranchedSubcategory`, `BranchedSupport`,
`BranchedTangent`, `BranchedSubcategoryExamples`, `BranchedOrientation`, `BranchedOrientationExamples`,
`GrassmannianFunctor`; §17.6 in `CategoryForms`, `WhitneySumStructure`, `WhitneySumCategory`, `WhitneySumPolyfold`, `CategoryStokes` (as printed in `Chapter16/StokesUnconditional`),
`CategoryStokesExamples`, `TameOrientedTransfer`, `TameOrientedExamples`; §17.8 in `ProperCoveringStructure`,
`ProperCoveringModel`, `ProperCoveringModelRestrict`, `ProperCoveringLift`, `ProperCoveringModelIso`,
`ProperCoveringUniformizer`, `ProperCoveringPolyfold`, `ProperCoveringBranched`, `ProperCoveringSheetUniformizer`,
`ProperCoveringSheetCounterexample`, `ProperCoveringSheetEffective`, `ProperCoveringTame`, `ProperCoveringGlobalModel`,
`ProperCoveringGlobalFunctor`, `ProperCoveringMorita`, `ProperCoveringReflection`. From other chapters:
`Chapter4/TangentWhitneySum`, `Chapter8/TangentWhitneyLocal`, `Chapter8/ProperCoveringFibredMap`.

**Chapter 18** (Fredholm theory in polyfolds): §18.1 in `SectionFunctors`, `FredholmSectionFunctors`, `ModelTransfer`,
`FredholmSectionFunctorsExamples`, `LinearizationTransport`, `Linearization`, `LinearizationSet`,
`LinearizationSetExamples`, `LinearizationSetLocal`, `LinearizationSetLocalExamples`, `ImplicitFunctionTheorem`,
`ImplicitFunctionTheoremExamples`, `ImplicitFunctionSubcategory`, `OpenSubcategory`, `OpenSubcategoryExamples`,
`ModelSectionPushforward`, `TangentPartialCone`, `TangentPartialConeExamples`, `GoodPositionIntrinsic`,
`GoodPositionIntrinsicExamples`, `AuxiliaryNormsBookForm`, `AuxiliaryNormsDirectExamples`, `ReflexivePieces`; §18.2 in
`AuxiliaryNorms`, `AuxiliaryNormsDirect`, `Compactness`, `CompactnessExamples`, `SolutionRegularity`; §§18.3–18.4 in `MultisectionFunctors`,
`MultisectionFunctorsExamples`, `MultisectionConstructions`; §18.5 in `Orientations`, `OrientationsExamples`,
`OrientationCategory`, `OrientationWitness`; §18.6 in `Perturbation`, `PerturbationExamples`, `PerturbationModelIndependence`,
`PerturbationModelIndependenceExamples`, `PerturbationOrientedSupport`, `PerturbationOrientedWitness`; the half-space
witness bundles in `HalfSpaceBundleConstruction`, `HalfSpaceWitnesses`, `HalfSpaceBoundaryData`.

**Chapter 19** (the basic construction): §§19.1–19.2 in `BasicConstruction`, `NaturalTopology`,
`BasicConstructionExamples`; §§19.3–19.4 in `TopologyLemmas`, `Metrizability`, `MetrizabilityExamples`; §19.5 in
`PolyfoldStructure`, `PolyfoldStructureGCT`, `PolyfoldStructureExamples`, `BasicRegularity`, `BasicRegularityPointwise`,
`TopologyLemmasTwo`, `CompactNeighbourhoods`; §19.6 in `StrongBundleUniformizer`, `StrongBundleTransition`,
`StrongBundleTopology`, `StrongBundleExamples`, `StrongBundleAlternative`, `StrongBundleTransport`,
`StrongBundleCoherence`, `StrongBundleTheorem`, `StrongBundleComparison`, `StrongBundleMultiplication`; §19.7 in
`ProperCoveringModelExample`, `CoveringConstruction`, `CoveringTopology`, `CoveringOrbitTopology`,
`CoveringOrbitCounterexample`, `CoveringCounterexamples`, `CoveringLocalStructure`, `CoveringMetrizability`,
`CoveringLocalExamples`, `CoveringPolyfold`, `CoveringPolyfoldExamples`; §19.8 in `CoveringPullbackDiagram`,
`CoveringPullbackTheorem`, `CoveringPullbackExamples`, `CoveringPullbackCoherence`, `CoveringSquare`,
`CoveringSquareTheorem`, `CoveringSquareExamples`, `CoveringSquareTopology`, `CoveringSquareTopologyExamples`,
`CoveringSquareMultiplication`, `CoveringSquareMultiplicationExamples`, `FibredProductCovering`,
`CoveringSquareFibredProper`, `CoveringSquareFibredProperExamples`, `CompatibilityExamples`.

**Examples** (the worked example, imported after Chapter 16; page `Exposition/WorkedExample.md`): the orbifold
ℤ/5 ⋉ ℂ with the strong bundle of weight 2 and the section z ↦ z², index 0, in `OrbifoldSquareAlgebra`,
`OrbifoldSquareBundle`, `OrbifoldSquareStructure`, `OrbifoldSquareOrientation`, `OrbifoldSquarePerturbation`,
`OrbifoldSquare`, `OrbifoldSquareCount`, `OrbifoldSquareSign` (namespace Polyfold.Examples.OrbifoldSquare).
No equivariant single-valued sc⁺-perturbation is transversal (`not_isTransversalAt_sectionMulti`); every hypothesis
of Theorem 16.6.6 for index 0 holds (`theorem_16_6_6_hypotheses`); the five-branch multisection with weights 1/5 is
admissible (`exists_canonical_t5`); and the count is 2/5 for every admissible perturbation with the canonical
orientation, for the orientation positive at the complex-linear isomorphisms (`count_eq_two_fifths`,
`count_eq_two_fifths_all`). General lemmas in the same folder, in the library's namespaces: counts over finitely
many orbits in `PointCountFiniteSupport` (`EP.pointBranchedIntegral_eq_sum`, `PointSolution.count_eq_sum`); d of a
constant 0-form in `ConstantFormClosed` (`MPolyfold.extD_constForm`); the sign of the canonical orientation of
Theorem 15.4.1 in dimension 0 in `SignDimZeroLinear`, `SignDimZeroPush`, `SignDimZeroFrames`
(`isPosOr_iff_of_path`, `KernelBranching.frameSign_orTangent_eq_one_iff`, `IsCanonicalFor.signedWeight_eq`).
The infinite-dimensional version (namespace Polyfold.Examples.OrbifoldSquareInf): the weighted ℓ² sc-Hilbert space
in `WeightedEllTwo`; the product (ℤ/5 ⋉ ℂ) × H with the section (z, e) ↦ (z², e) in `OrbifoldSquareInfBundle`,
`OrbifoldSquareInfFredholm`, `OrbifoldSquareInfNorm`, `OrbifoldSquareInfStructure`, `OrbifoldSquareInfPaths`,
`OrbifoldSquareInfSection`, `OrbifoldSquareInfPerturbation`, `OrbifoldSquareInfPositive`,
`OrbifoldSquareInfOrientation`, `OrbifoldSquareInf`; every hypothesis of Theorem 16.6.6 for index 0 holds
(`theorem_16_6_6_hypotheses_inf`) and the count is 2/5 (`count_eq_two_fifths_inf`); the general lemma
`EpStrongBundle.isOrInvariantAt_iff_of_continuous` in `OrInvariantSmooth`.
Limits: the non-transversality of single-valued perturbations is stated for the finite-dimensional example;
`sqOrientationPos` is not proved equal to `sqOrientation`. The Chapter 15 and 16 reports cite the
example as a witness for the index-0 statements (V15.37, V15.51, V16.82; Findings, Chapter 16, items 25 and 26).

## 3. The reports (`Exposition/`)

- `Chapter1.md` – `Chapter11.md`: the exposition of Parts I–II.
- `cmp/chNN.json` → `build_comparison.py` → `Comparison.json`, `Comparison.md`, `polyfold-beside-lean.html`: every
  numbered statement of the book beside the Lean statement, with a verdict (V-rows), and the points (G-numbers):
  entries of the text that no row covers, each formalized or marked "nothing to formalize".
- `verification/chNN.md` → `build_verification.py` → `Verification.md` (and `.pdf`): the verified edition, V-items
  and the numbered sign-off items; `build_signoff.py` → `polyfold-signoff.html`, the sign-off page.
- `pbp/partNN.md` → `assemble_pbp.py`, `build_proofbyproof.py` → `ProofByProof.md`, `.pdf`,
  `polyfold-proof-by-proof.html`: the proofs retold step by step, with trace tags checked by `check_trace.py`.
- `Findings.md`: reading points, hidden hypotheses and counterexamples to our readings, numbered per chapter.
- `BookConcordance.md`: numbers and pages of the 2014, 2017 and 2021 texts side by side.
- `WorkedExample.md`: the worked example ℂ/ℤ₅ with z ↦ z² (`Polyfold/Examples/`), written by hand.
- `checklist/` (`TrustedBase.lean`, `graph.tsv`, `mains.json`, `mains.tsv`, `build_checklist.py`) →
  `ReviewerChecklist.md`: the definitions and main statements a reviewer must read, in tiers.
  `build_path.py` → `Path-16.6.6.md`: the same for Theorem 16.6.6 alone, the definition rows in levels,
  leaves first; run it after `build_checklist.py`.
- `STYLE.md`, `REVIEW.md`, `VERIFY.md`, `PBP.md`: conventions of the reports, from the Milnor project.
- `RoundTrip/` (outside `Exposition/`): the round-trip audit of the statements of Chapters 1–11; method and how to
  rerun it in `RoundTrip/README.md`, results in `RoundTrip/REPORT.md`.

Run the scripts from the project folder with the git shim of §1 on the PATH (`check_names.py` calls lake, and
`check_trace.py` reads Mathlib's sources in `.lake/packages/mathlib`).

## 4. Status

Of the 275 points, 264 are formalized and 11 have nothing to formalize (G.34, the question after
Proposition 4.2.3; Remark 5.3.6; preprint Theorem 5.27; in Part IV
G.213, G.228, G.244, G.247, G.249, G.255, G.272, G.274: remarks, comments, invitations and exercises). G.222 (the
Whitney sum $\oplus^k TC$ of Proposition 17.6.1) is formalized with $\hat\Psi$ continuous, the hypothesis of
Theorem 17.2.17. G.153 (Remark 9.5.19, Stokes on ep-groupoids without partitions of unity) is formalized along the
route the remark sketches, so Theorems 16.4.6, 17.6.7 and 17.6.10 hold as printed, and Theorem 16.6.6 holds over all
admissible perturbations, with no bump functions and no partitions of unity. The 79
rows with the verdict "narrower" prove less than the text states; `Exposition/Findings.md` gives the reason for each,
and `README.md` lists the points that need the authors' reading. Added hypotheses (`_hyp` forms) are listed with
their witnesses in the rows that cite them.
