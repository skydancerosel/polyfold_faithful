# Handoff: the Polyfold project (HWZ, *Polyfold and Fredholm Theory*, Parts I–III)

A Lean 4 / Mathlib formalization of Hofer, Wysocki and Zehnder, *Polyfold and Fredholm Theory*
(Springer 2021), with its reports. `README.md` is the public overview; this file is for whoever works on
the repository. The Springer edition is the authoritative text: statement numbers and pages are its own,
followed in parentheses by those of the 2014 preprint (arXiv 1407.3185, Part I) or of the book's arXiv
version (1707.08941, "2017", Parts II–III); the correspondence is `Exposition/BookConcordance.md`.

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
`WIP_*.lean`; never renumber V-items, G-items or Findings items (no sign-off is recorded in the repository yet,
so V-items may still be edited in place). Every hypothesis that quantifies over all charts is checked for
satisfiability (Findings, Chapter 3, item 190), and every added hypothesis has a witness in the non-degenerate
case (a witness only for $\partial X = \emptyset$ or zero fibres does not count). Lean names carry the 2021 numbers
(`theorem_14_1_9`, `lemma_14_1_4`) with descriptive suffixes only (`_hyp` for a form with a hypothesis not in the
text, `_book`/`_text` for the printed form when a restated form is the main one); file names are topic names in
UpperCamelCase.

Wording about the text: in everything the authors may read (the reports, the README, `RoundTrip/REPORT.md`), a
counterexample refutes *our reading* of a statement, not the statement. Say "does not hold as we read it",
"presumably …", "we read … as …"; never call the text wrong or speak of its errors, mistakes or misprints.
The public documents describe the final state only.

## 2. Layout

Top level: `Polyfold.lean` (imports every module), `Polyfold/Test.lean` (`#print axioms` per theorem, one block
per chapter), `Polyfold/Basic.lean`, `Polyfold/Vendor/MilnorSard/` (Sard's theorem, from the Milnor project),
`Polyfold/Chapter1/` … `Polyfold/Chapter16/` (one folder per chapter of the book, files named by topic),
`RoundTrip/` (the round-trip audit: `REPORT.md`, `Items/`, `Blind/`, `harness/`, `Check.lean`), `PLAN.md`,
`Exposition/` (§3). A statement of one chapter that needs the machinery of a later chapter lives in the later
chapter's folder.

**Chapter 1** (sc-calculus): `ScBanach`, `ScFredholm`, `ScFredholmCriterion`, `FredholmIndex`,
`FredholmPerturbation`, `ScSmooth`, `Levels`, `LevelsWeak`, `Properties`, `ChainRule`, `Degeneracy`, `PartialCones`,
`ScOneNotNormContinuous`, `ExpositionLemmas`, `Book2021`; the weighted Sobolev spaces of Example 1.1.3 on the
cylinder in `CylinderSobolevSpaces`, `CylinderScBanach`, `CylinderSobolevComplete`, `CylinderWeakDerivatives`,
`CylinderLeibniz`, `CylinderIntegrationByParts`, `CylinderMultipliers`, `CylinderCutoff`, `CylinderTestDensity`,
`CylinderTrigPolynomials`, `CylinderFourier`, `CylinderRellich`, `CylinderCompactInclusions`.

**Chapter 2** (retracts and M-polyfolds): `Retracts`, `TameRetracts`, `MPolyfold`, `LocalTopology`,
`LocalTopologyExample`, `Metrizable`, `MichaelRefinement`, `DegeneracyIndex`, `Boundary`, `PartialCone`,
`PartialConeQuadrant`, `CornerGerms`, `Tame`, `TameFaces`, `TameInvariance`, `TameSub`, `ExtendedFaces`,
`SubMPolyfold`, `SubMPolyfoldTangent`, `SubMPolyfoldTangentSc`, `FibredProduct`, `LevelPolyfold`, `SmoothPaths`,
`SmoothRetractImage`; the tangent bundle and tangent spaces in `TangentBundle`, `TangentMap`, `TangentMapLinear`,
`TangentLift`, `TangentLiftAll`, `TangentSpaceLinear` (Definition 2.3.14), `TangentSpaceChartIndependent`,
`TangentProjOpen`, `TangentConePaths`, `TangentConeQuadrant`, `ReducedTangentIntrinsic`; strong bundles in
`StrongBundle`, `StrongBundleOne`, `StrongBundlePullback`, `StrongBundleRestrict`; the tame boundary of §2.7 in
`TameBoundary`, `TameBoundaryStructure`, `TameBoundaryTopology`, `TameBoundaryExample`, `TameBoundaryNonCentred`;
the 2021 statements in `Book2021`, `BookFormLocalCompleteness2021`, `BookFormTameBoundary2021`,
`BookFormTameSub2021`.
Face-structured M-polyfolds recognised by labels and face counts, with products: `FaceLabels`, `FaceFamilies`.

**Chapter 3** (sc-Fredholm theory): germs and the contraction germ in `Germ`, `GermLevels`, `GermCalculus`,
`GermCalculusParam`, `ContractionGerm`, `GermIFT`, `GermIFTSmooth`, `SolutionGermRegularity`,
`SolutionGermQuantitative`, `SolutionGermRecentre`; fillers and basic germs in `Filler`, `GermFilling`,
`GermFillingChart`, `BasicClass` and the `BasicGermCriterion*`, `BasicGermLinearization*`, `BasicGermShrink*`
files; sc-Fredholm sections and their tame germ data in `TameGerms`, `TameGermsG`, `TameGermData`,
`TameGermDataStabilization`, `TameGermTransfer`, `FredholmSectionsG` and the `FredholmGerm*` files; the implicit
function theorem in the `GlobalIFT*` files (`GlobalIFTTheorems`, `GlobalIFTTheoremsG`, `GlobalIFTFull`; the
surjectivity at nearby zeros in the `GlobalIFTNearby*` files); good position in the `GoodPosition*` and
`GoodComplement*` files; linearizations in the `Linearization*` files; the index in the `IndexLocallyConstant*`
and `IndexAlongPaths*` files; local solvability, compactness and quadrants in `LocalSolvability`,
`LocalSolvabilityClosed`, `SectionCompactness`, `SectionCompactnessG`, `LocalCompactness`, `QuadrantIFT`,
`QuadrantInverse`, `QuadrantInverseSmooth`, `QuadrantClassCk`; the all-charts tameness hypothesis that no strong
bundle satisfies, and the non-vacuity witnesses, in `TameVacuity`, `TameVacuityChart`, `NonVacuity`,
`NonVacuityCorner`, `NonVacuityG`; untamed bundles in the `Untamed*` files; the interval $[0,1]$ as an M-polyfold
in `UnitIntervalPolyfold`; the 2021 statements and counterexamples to our readings in `Book2021Germs`,
`Book2021Items`, `BookFormIFT2021`, `MainTheorems2021`, `Counterexamples2021`, `RecentreCounterexample2021`.
Files with the suffix `G` hold the germ-reading forms of the statements of the file of the same stem.

**Chapter 4** (manifolds with boundary with corners, sc⁺, forms): `LocalStructure`, `LocalFaces`,
`Characterization`, `Recentre`, `Submanifolds`, `SubmanifoldNearBoundary`, `SubmanifoldNearInterior`, `ScPlus`,
`ScPlusGraph`, `ScPlusRetractQuestion`, `Families`, `FamiliesLocal`, `GeneralPositionLocalFaces`,
`StratifiedRegularValues`, `LocalStrongBundle`, `RetractionSectionFredholm`, `RetractionSectionSplitting`,
`RemarkLocalForm`, `RemarkFourThreeExample`, `RemarkFourThreeFamily`; vector fields and the Lie bracket in
`VectorFields`, `VectorFieldsGlobal`, `BracketLevel`, `LieBracketBundle`, `LieBracketOpenSubsets`,
`BookFormLieBracket2021`; sc-differential forms and Stokes in the `ScForms*2021` files, `ScExteriorDerivative2021`,
`OpenForms`, `BoundaryForms2021`, `BoundaryFormsPullback2021`, `A3BoundaryForms2021`, `A3BoundaryForms2021b`,
`BoundaryWedge`, `RelativeWedge`, `EuclideanForms2021`, `EuclideanStokes2021`, `ManifoldForms2021`,
`ManifoldFaceForms2021`, `ManifoldBoundary2021`, `ManifoldIntegral2021`, `ManifoldStokes2021`, the `StokesFace*`
files, `Poincare448`, `Poincare448Shift`, `Poincare2021`, `Poincare2021b`; `Book2021`.
The faces of a submanifold in general position: `GeneralPositionFaceStructure`.

**Chapter 5** (the Fredholm package): `Compactness`, `SolutionSetClosed`, `AuxNorm`, `AuxNormLiteral`,
`AllowableSectionsMetric`, `BumpFunctions`, `BumpWeakPointwise`, `BumpPointsResearch`, `ShiftTameResearch`,
`PartitionsOfUnity`, `HilbertPartitionsOfUnity`, `SeparablePartitionsOfUnity`, `WCGPartitionsOfUnity`,
`AmirLindenstrauss`, `BonicFrampton`, `Torunczyk`, `ProjectionalResolution`, `LocallyFiniteBases`,
`ReflexiveCompactness`, `ReflexiveFibres`, `WeakSequentialCompactness`, `StrongBundleShift`,
`SmoothLevelContinuity`, `DegeneracyZeroTame`, `CubePartitions`; transversality and general position in
`Transversality`, `GeneralPosition`, `DenseGoodPosition`, `Corollary58`, `BoundaryExtension`,
`FredholmArcPerturbation`, `CylinderPerturbation2021`; homotopy in `Homotopy`, `CompactHomotopyIso`; Theorem 5.3.15
in the `Theorem5315_*` files; the Sobolev spaces on cubes in the `SobolevCube*`, `SobolevRemark*` and
`LpWeightedProduct` files; the printed forms in `MainTheoremsBookForm`, `MainTheoremsBookForm2021`, `Book2021`,
`ApproxPropertyEveryChart`.

**Chapter 6** (determinants, orientations, invariants): determinant lines and bundles in `DetLine`, `DetBundle`,
`DetConventions`, `DirectSumDet`, `ExactSequence`, `FredholmDet`, `LocalDetBundle`, `ClassicalDetBundle`,
`DetVectorBundles2021`, the `DetNonOrientable*` files, `LineBundleOrientation`, `OrientationBundle`,
`OrientationSpace`; linearizations and orientations in `LinSet`, `LinSetFredholm`, `LinOrientation`, `Stabilization`,
`StabilizationContinuity`, `StabKernelsExist`, `SmoothKernelFrames`, `SmoothSubspaceFamilies`, `SubspaceBundle`,
`GoodProjections`, `ProjectionSequence`, `SectionOrientation`, `SolutionOrientation`, `SolutionOrientationCharts`,
`SolutionSetOrientation`, `SolutionSetOpen2021`, `SolutionManifoldFamily2021`, `ProductOrientation`, the
`ProductSectionOrientation2021*` files, `OrientationConvention2021`, `OrientationFunctor`, `OrientationMainClean`,
`ManifoldOrientation`, `ContinuousOrientation`, `PerturbedOrientation`, `OrientableNbhd`; paths, homotopies and
transport in `ScPaths`, `PathsInterval`, `PathCategory`, `PathCategoryInterval`, `PathTransport`, `Propagation`,
`PropagationWellDefined`, `Continuation`, `ScHomotopy`, `IntervalHomotopy`, `ScContractible`,
`SmoothPathComponents2021`, `PushData`, `PushTransfer`, `ChartTransfer`, `AddSections`, `FamilySections`,
`KernelFamily`, `KernelBundleInterval`, `ParamKernel`, `UnitIntervalSections`, `SmoothFiniteDimRanges`,
`SubmersionNearFamily`, `Lemma629`; the invariants and cobordisms of §§6.6–6.7 in the `Cube*` files (the cube
$[0,1]^n$ and its boundary slices), `SlicePropertyP`, `CobordismOrientation2021`, the `CobordismOrientationEnds2021*`
and `CobordismRelativeForms2021*` files, `InvariantSingle2021`, `InvariantCobordism2021`, `InvariantProductEnds2021`,
`InvariantProductEnds2021b`, `ProperHomotopy2021`, `Theorem671_2021`, `Theorem671Assembly2021`, `Theorem671Final2021`
(Theorem 6.7.1); `Book2021`, `Book2021Continuity`. Families on `[0,1]ⁿ` and the cylinder `[0,1] × X` in
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

**Chapter 7** (ep-groupoids): `Groupoid`, `EpGroupoid`, `Basic`, `Book2021Basic`, `Discrete`, `Effective`,
`Reduced`, `ReducedCriterion`, `ReducedNaturalCharts`, `ReducedNotHausdorff`, `OrbitTopology`, `ProperMaps`,
`ProperSubsets`, `LocalDiffeo`, `LocConnected`, `NaturalAction`, `NaturalRep`, `NaturalRepFinite`, `Uniformizer`,
`SubGroupoid`, `SubGroupoidTangent`, `SubGroupoidTangentSc`, `TangentMorphism`, `TangentMorphismLinear`, `Lift`,
`RaisedEpGroupoid`, `SmoothPointsDense`, `SmoothConnectedReps`, `SmoothRegularAssembly`, `FlatGluing`, `Michael`,
`PartitionsOfUnity`, `HilbertPartitionsOfUnityEp`, `PropertyFiveResearch`, `NonVacuity`; Zhou's retract and
(ZHOU) in the `Zhou*` files, `LineSobolevScale`, `LineTranslates`; the tame boundary in `TameBoundaryEp`,
`TameBoundaryEpStructure`, `TameBoundaryFull`, `BookFormTameBoundaryEp2021`.

**Chapter 8** (bundles and covering functors): `Basic`, `EpStrongBundle`, `StrongBundleMap`, `NatTrans`,
`GeometricLift`, `GeometricLiftEmpty2021`, `PullbackStrongBundle2021`, `BundleLocalRegularity2021`,
`BundleOrbitParacompact2021`, `BundleOrbitParacompactOne`, `ProperCovering`, `ProperCoveringLocal`,
`SigmaPolyfold`, `NonVacuity`, `NonVacuityBundle`; the tangent ep-groupoid in `TangentEp`, `TangentEpNotInjective`,
`TangentFibred`, `TangentLocal`, `TangentOrbit`, `TangentPairs`, `TangentTame`, `TangentVertical2021` and the
`TangentZhou*` files; forms on ep-groupoids in `EpForms`, `EpFormsFunctor`, `EpFormsObj`, `EpPoincare`; `Book2021`.

**Chapter 9** (branched ep⁺-subgroupoids, integration, Stokes): the definitions in `Basic`, `Symmetric`,
`Propositions`, `Appendix`, `AppendixSlices`, `Tangent`, the `TangentSlices*` files, `TangentSubmanifoldSmooth`,
`OrientationBasic`, `Orientation`, `OrientationAnyDim`, `OrientationBoundary`, `OrientationRn`, `OrientationTangent`,
`OrientationUniqueness` and the `OrientationExample*` files; sheets, measures and the branched integral in the
`Sheet*` files, `Measure`, `MeasureEffective`, `MeasureGlue`, `MeasureWholeSheets`, `LocalMeasure`, `FamilyMeasure`,
`PointIntegration`, `FinitePointIntegration`, `BranchedIntegral`, `ReducedIntegral`, `ReducedRep`, `ReducedCircle`,
`SignedMeasureIntegrals`, `DensityLocal`, `DensitySignedMeasure`, `FunctionTimesForm`, `ZeroFormValues`; the integral
through graph charts in `GraphChart`, `GraphChartExists`, `GraphChartTransition`, `GraphCoord`, `GraphDiffeo`,
`ChartIntegral`, `ChartAbsIntegral`, `ChartVectors`, `IntegralCovering`, `FormEvalEp`, `FormEvalInfty`, `FrameSign`,
`ManifoldBridge`, `ManifoldIntegralBridge`, `MathlibFormsBridge2021`, `MathlibManifoldBridge`, `MathlibSolutionSets`,
`TameOpen`, `MultiChart`, `MultiChartCompact`, `MultiChartIntegration`, `MultiChartTheorem`; the boundary, its faces
and their measure in the `Boundary*` files, `CornerFinite`, `FaceChange`, `FaceFrame`, `FaceIntegrand`,
`FaceOrientation`, `FaceIntegralDimOne`, `GeneralBoundaryPoints`, `StratumRetraction`, `StratumTangent`; dimension
decompositions in `DimDecompositionExists`, `DimDecompositionUnique`, `DimensionJumpPolyfold`, `DimensionJumpRetract`,
`LocallyEquidimensional2021`; Stokes in the `Stokes*` files, `FiniteTheorem`, `FiniteTheoremText`, `FiniteDominated`,
`GeneralCorollaries`, `GeneralLevelZero`, `AllStructures`, `AllStructuresDimOne`, `EffectiveDimOneLUC`; witnesses in
`CircleOneSheet`, `CircleWitness`, `HalfCircleSheet`, `HalfCircleWitness`, the `Hemisphere*` files, `XAxisWitness`,
`SphereRadialRetraction`, `CyclicGroupoidIsotropy`; the support of a branched subgroupoid in the `Support*` files;
`CoveringFromText`, `DescentPolyfold`, `GoodPoints`, `LevelRestrict`, `OrbitSubsetMetrizable`,
`PropertyTShrinking2021`, `SolutionFaces2021`, `SolutionFaceForms2021`. Remark 9.5.20 in `DimensionJumpSheet`,
`DimensionJumpBranched`, `DimensionJumpIntegral`, `DimensionZeroIntegral` (the boundary integral in Chapter 11,
`DimensionJumpBoundaryIntegral`).
The boundary integral of the cobordism `S_F ⊆ [0, 1] × X` of Chapter 6 (ends, signs, lateral faces):
`BoundaryEndFaces`, `IntervalBoundaryDecomposition`, `IntervalEndSigns`, `IntervalCobordismFaceStructure` (on
`StokesFaceSum`).

**Chapter 10** (equivalences and localization): `Equivalence`, `EquivalenceExamples`, `EquivalenceLR`,
`EquivalenceLREffective`, `EquivalenceReduced`, `EquivalenceRefinement`, `EquivalenceZhou`, `ZhouExample`,
`ZhouExampleRealScale`, `WeakFibredProduct`, `WeakFibredProductTheorem`, `WeakFibredProductTriple`, `Localization`,
`LocalizationCategory`, `LocalizationLR`, `LocalizationLRBundleBase`, `LocalizationLRCounterexample`,
`LocalizationLREffectiveBundle`, `LocalizationProperties`, `LocalizationUniversal`, `LocalRegularitySubcategory`;
strong bundles up to equivalence in the `StrongBundle*` files; `FredholmEquivalence`, `SectionFunctorLinear2021`.
Local regularity in germ form in `LocalRegularityGerm`, `StrongBundleCutOff`; tame bundle charts in
`TameBundleCharts`.
Proposition 8.4.3 for Definition 8.4.2 as printed: `BundleLocalRegularityPrinted`.

**Chapter 11** (geometry up to equivalences): `EpEquivalenceGeometry`, `EpEquivalenceGeometryFaces`,
`FaceEpGroupoids`, `FaceGeneralizedIso`, `FaceIntersectionUnion`, `FaceIntersectionCounterexample`,
`SubGroupoidModel`, `MultisectionLocalStructure2021`, `AuxiliaryNormTransport2021`; coverings in
`CoveringEquivalence`, `CoveringEquivalenceDiagram`, `CoveringEquivalenceTheorem`, `ProperCoveringLocalization`,
`ProperStrongBundleCoverings`, the `StrongBundleCovering*` files, `StrongBundleUpToEquivalence`; branched subgroupoids
and their integrals up to equivalence in the `BranchedEquivalence*` files, `MeasureEquivalence`,
`MeasureGeneralizedIso`, `EffectiveMeasureEquivalence`, `EffectiveMeasureGeneralizedIso`, the `BoundaryMeasure*`
files, `BoundaryOrientationEquiv`, `BoundarySheetsDiffeo`, `GraphChartsDiffeo`, `MultiChartSheetsEquivalence`,
`OrientedStructureDiffeo`, `OrientedStructurePairs`; forms in `GeneralizedForms`, `EquivalenceForms`,
`EquivalenceFormsInfty`, `EpFormsWedge`, `EpPoincareLemma`, `FormAveraging`, `FormDescent`, `FormEvalPullback`,
`FormEvalPullbackEquivalence`, `OrbitForms`, `TranslationAverage`. `ChartDomainOrientation` (orientations on chart
domains), `DimensionJumpBoundaryIntegral` (Remark 9.5.20 on `∂X`).

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
`IntervalProductLocalIso`.

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

**Chapter 15** (transversality and invariants): linearizations in `Linearization`, `LinearizationFunctor`,
`LinearizationIntrinsic`, `LinearizationModel`, `OrientedLinearizations`, `CanonicalLift`; local families and general
position in `LocalFamilies`, `LocalSeeds`, `LocalSlice`, `LocalIFT`, `LocalScPlus`, `ParamFamily`, `ParamOntoBridge`,
`ParamOntoTransport`, `ParametricGeneralPosition`, the `GeneralPosition*` files, `GoodPositionBranches`,
`GoodPositionWitness`, `Transversality`, `TransversalExtension`, `RegularPerturbations`,
`InteriorPerturbationWitness`, `BoundaryPerturbation`, `ControllingPairs`, `SeparationLemmas`, `FredholmSummands`; the
relative case (Theorem 15.3.9) in `RelativeFamilies`, `RelativeParametric`, `RelativeReduction`, `RelativeBranch`,
`ChargedExtensionFibres`, `ChargedExtensionCylinder`; branched objects in `BranchChart`, `TameBranched`,
`TameWitness`, `RestrictedEp`; the cylinder $[0,1] \times X$ in `Cylinder`, `CylinderEnds`, `CylinderGlue`,
`CylinderPartitions`, `CylinderCobordism`, `CubeEp`, `CubeLift`, `CubeAuxNorm`, `CutoffFunctor`, `GlueStructurable`;
products in the `Product*` files; the invariants in `PerturbedStokesInvariants`. The relative step in `RelativeSeeds`,
`RelativeSeedFamilies`, `RelativeLocalFamilies`, `RelativeStepBump`, `BoundaryExtensionIndependence`,
`BoundaryFrameCriterion`, `TransversalExtensionCorollaries`, `TransversalExtensionWitness`, `FaceOntoCorollaries`; the
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
`TransversalExtensionBoundaryDatum`.

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
`InheritedOrientationGeneralPosition`; `OrientationRepLocal`, `CanonicalPerturbationIntegral`,
`FibreNegationStructure`; witnesses: `CircleSectionCobordism`, `CircleSectionCollarCobordism`,
`CircleSectionPolyfold`, `CylinderInvarianceNonEffective`, `IsotropyCircleCobordism`, `TrivialIsotropyBundle`,
`IndexZeroCylinderWitness`, `IndexZeroIsotropyWitness`, `IndexZeroShiftedPerturbation`,
`HalfSpaceIsotropyOrientedSection`, `HalfSpaceLocalOrientation`, `CanonicalModelTransferWitness`,
`CanonicalOrientationPullbackWitness`, `InheritedOrientationGeneralPositionWitness`, and Remark 6.6.19 on the
half-disc in `HalfDiscIntervalCobordism`, `HalfDiscCobordismFaces`, `HalfDiscBoundaryIntegral`,
`HalfDiscFaceStructureInstance`.

## 3. The reports (`Exposition/`)

- `Chapter1.md` – `Chapter11.md`: the exposition of Parts I–II.
- `cmp/chNN.json` → `build_comparison.py` → `Comparison.json`, `Comparison.md`, `polyfold-beside-lean.html`: every
  numbered statement of the book beside the Lean statement, with a verdict (V-rows), and the entries not
  formalized or formalized only in part (G-numbers).
- `verification/chNN.md` → `build_verification.py` → `Verification.md` (and `.pdf`): the verified edition, V-items
  and the numbered sign-off items; `build_signoff.py` → `polyfold-signoff.html`, the sign-off page.
- `pbp/partNN.md` → `assemble_pbp.py`, `build_proofbyproof.py` → `ProofByProof.md`, `.pdf`,
  `polyfold-proof-by-proof.html`: the proofs retold step by step, with trace tags checked by `check_trace.py`.
- `Findings.md`: reading points, hidden hypotheses and counterexamples to our readings, numbered per chapter.
- `BookConcordance.md`: numbers and pages of the 2014, 2017 and 2021 texts side by side.
- `checklist/` (`TrustedBase.lean`, `graph.tsv`, `mains.json`, `mains.tsv`, `build_checklist.py`) →
  `ReviewerChecklist.md`: the definitions and main statements a reviewer must read, in tiers.
- `STYLE.md`, `REVIEW.md`, `VERIFY.md`, `PBP.md`: conventions of the reports, from the Milnor project.

Run the scripts from the project folder with the git shim of §1 on the PATH (`check_names.py` calls lake, and
`check_trace.py` reads Mathlib's sources in `.lake/packages/mathlib`).

## 4. What is open

The open items are the G-entries of `Exposition/Comparison.md` that are not marked formalized, and the rows with
the verdict "narrower"; `Exposition/Findings.md` gives the reasons, and `Exposition/Verification.md` lists per
chapter what is not verified. Added hypotheses (`_hyp` forms) are listed with their witnesses in the rows that
cite them.
